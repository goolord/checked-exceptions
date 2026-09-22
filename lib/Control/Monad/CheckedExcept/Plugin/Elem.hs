{-# LANGUAGE CPP #-}

-- | Solve 'Control.Monad.CheckedExcept.Elem' constraints that instance
-- resolution leaves stuck.
module Control.Monad.CheckedExcept.Plugin.Elem
  ( mkElemPlugin
  ) where

import GHC.Plugins hiding ((<>), TcPlugin)
import GHC.Tc.Types (TcPlugin (..), TcPluginSolveResult (..))
import GHC.Tc.Types.Constraint (Ct, ctPred, ctLoc, mkNonCanonical)
import GHC.Tc.Types.Evidence (EvTerm, evDFunApp)
import qualified GHC.Tc.Plugin as TC
import GHC.Tc.Utils.TcType (eqType, isMetaTyVar)
import GHC.Core.Class (Class, classTyCon)
import GHC.Types.Unique (hasKey)
import GHC.Core.Unify (tcUnifyTys, tcMatchTy, BindFlag (..))
#if __GLASGOW_HASKELL__ >= 914
import GHC.Core.Predicate (getClassPredTys_maybe, mkNomEqPred)
#else
import GHC.Core.Predicate (getClassPredTys_maybe)
#endif
import Control.Monad (when)
import Data.Either (partitionEithers)
import Data.IORef (IORef, newIORef, readIORef, modifyIORef')
import Data.Maybe (isJust, catMaybes)
import Control.Monad.CheckedExcept.Plugin.Util

data Environment = Environment
  { elemClass :: Class
  , elemInClass :: Class
  , hereDataCon :: DataCon
  , thereDataCon :: DataCon
  , emitted :: IORef [(Type, Type)]
    -- ^ Equalities already emitted, so a constraint that stays stuck doesn't
    -- re-emit them on every solver iteration.
  , verbose :: Bool
  }

-- | @Elem e es@ (and its helper @ElemIn e es declared@) is stuck when @e@
-- might still equal an element of @es@ without being syntactically equal to
-- it: @E a@ against @E Int@, or @Int@ against a type variable @x@.
--
-- * If @e@ is syntactically equal to an element of the known prefix of @es@,
--   solve it with that index.
-- * Otherwise, if @es@ is fully known and exactly one element unifies with
--   @e@, @e@ must be that element: emit the equality.
--
-- Anything else is left to the instances, which report a custom type error
-- when @e@ is not a member.
mkElemPlugin :: [CommandLineOption] -> TcPlugin
mkElemPlugin opts = TcPlugin
  { tcPluginInit = do
      checkedExceptMod <- lookupModule "Control.Monad.CheckedExcept"
      elemClass <- lookupClass checkedExceptMod "Elem"
      -- Not exported, so looked up by original name.
      elemInClass <- lookupClass checkedExceptMod "ElemIn"
      hereDataCon <- lookupDataCon checkedExceptMod "Here"
      thereDataCon <- lookupDataCon checkedExceptMod "There"
      emitted <- TC.tcPluginIO (newIORef [])
      pure Environment
        { elemClass, elemInClass, hereDataCon, thereDataCon, emitted
        , verbose = "verbose" `elem` opts
        }
  , tcPluginSolve = \env _ _ wanteds -> do
      results <- catMaybes <$> mapM (solveElem env) wanteds
      let (solved, newCts) = partitionEithers results
      pure (TcPluginSolveResult [] solved (concat newCts))
  , tcPluginRewrite = const emptyUFM
  , tcPluginStop = const (pure ())
  }

solveElem :: Environment -> Ct -> TC.TcPluginM (Maybe (Either (EvTerm, Ct) [Ct]))
solveElem env@Environment {elemClass, elemInClass, emitted, verbose} ct =
  case getClassPredTys_maybe (ctPred ct) of
    Just (cls, tys@(e : es : _))
      | cls == elemClass || cls == elemInClass -> do
          let (elems, rest) = splitPromotedList es
          case any (eqType e) elems of
            True ->
              pure (Just (Left (evDFunApp (classConId cls) tys [elemIxExpr env e es], ct)))
            False
              | isNil rest
              , [y] <- filter (unifies e) elems -> do
                  seen <- TC.tcPluginIO (readIORef emitted)
                  if any (\(x', y') -> eqType e x' && eqType y y') seen
                    then pure Nothing
                    else do
                      when verbose $ tcTrace "unify" (e, y)
                      TC.tcPluginIO (modifyIORef' emitted ((e, y) :))
                      eq <- TC.newWanted (ctLoc ct) (nomEqPred e y)
                      pure (Just (Right [mkNonCanonical eq]))
              | otherwise -> pure Nothing
    _ -> pure Nothing
  where
    bindMetas tv _ = if isMetaTyVar tv then BindMe else DontBindMe
    unifies x y = isJust (tcUnifyTys bindMetas [x] [y])
    isNil ty = maybe False ((`hasKey` nilDataConKey) . fst) (splitTyConApp_maybe ty)
    -- A single-method class dictionary is built by its (newtype) constructor.
    classConId = dataConWrapId . tyConSingleDataCon . classTyCon

-- | @ElemIx e es@ pointing at the first element of @es@ equal to @e@.
elemIxExpr :: Environment -> Type -> Type -> CoreExpr
elemIxExpr Environment {hereDataCon, thereDataCon} e = go
  where
    elemIxTy = mkTyConApp (dataConTyCon hereDataCon) . (\es -> [e, es])
    go es = case splitTyConApp_maybe es of
      Just (_, [_, x, rest])
        | eqType e x -> conApp hereDataCon (elemIxTy es) []
        | otherwise -> conApp thereDataCon (elemIxTy es) [go rest]
      _ -> panic "checked-exceptions: elemIxExpr: element not in list"

-- | Apply a data constructor's wrapper at the instantiation giving @resTy@.
conApp :: DataCon -> Type -> [CoreExpr] -> CoreExpr
conApp dc resTy args =
  let wrapId = dataConWrapId dc
      (tvs, body) = splitForAllTyCoVars (idType wrapId)
      (_, wrapRes) = splitFunTys body
  in case tcMatchTy wrapRes resTy of
      Just subst -> mkCoreApps (Var wrapId) (map (Type . substTyVar subst) tvs ++ args)
      Nothing -> panic "checked-exceptions: conApp: result type mismatch"

nomEqPred :: Type -> Type -> PredType
#if __GLASGOW_HASKELL__ >= 914
nomEqPred = mkNomEqPred
#else
nomEqPred = mkPrimEqPred
#endif
