-- | Helpers shared by the checked-exceptions type-checker plugins.
module Control.Monad.CheckedExcept.Plugin.Util
  ( lookupModule
  , lookupClass
  , lookupTyFam
  , lookupDataCon
  , splitPromotedList
  , extractMPromotedList
  , tcTrace
  ) where

import GHC.Plugins hiding ((<>))
import GHC.Core.Class (Class)
import GHC.Types.Unique (hasKey)
import GHC.Builtin.Names (consDataConKey)
import qualified GHC.Tc.Plugin as TC
import GHC.Tc.Plugin (tcPluginTrace)

lookupModule :: String -> TC.TcPluginM Module
lookupModule modName = do
  findResult <- TC.findImportedModule (mkModuleName modName) NoPkgQual
  case findResult of
    TC.Found _ md -> pure md
    _ -> fail ("checked-exceptions: could not find " <> modName)

lookupClass :: Module -> String -> TC.TcPluginM Class
lookupClass md name = do
  name' <- TC.lookupOrig md (mkClsOcc name)
  TC.tcLookupClass name'

lookupTyFam :: Module -> String -> TC.TcPluginM TyCon
lookupTyFam md name = do
  name' <- TC.lookupOrig md (mkTcOcc name)
  TC.tcLookupTyCon name'

lookupDataCon :: Module -> String -> TC.TcPluginM DataCon
lookupDataCon md name = do
  name' <- TC.lookupOrig md (mkDataOcc name)
  TC.tcLookupDataCon name'

-- | Leading elements of a promoted list, and the remaining tail (@'[]@ when
-- the list is fully known, otherwise e.g. a metavariable or a stuck family).
splitPromotedList :: Type -> ([Type], Type)
splitPromotedList ty =
  case splitTyConApp_maybe ty of
    Just (tc, [_, t, ts]) | tc `hasKey` consDataConKey ->
      let (elems, rest) = splitPromotedList ts in (t : elems, rest)
    _ -> ([], ty)

-- | Elements of a fully known promoted list.
extractMPromotedList :: Type -> Maybe [Type]
extractMPromotedList ty =
  case splitPromotedList ty of
    (elems, rest)
      | Just (tc, _) <- splitTyConApp_maybe rest
      , tc `hasKey` nilDataConKey -> Just elems
    _ -> Nothing

tcTrace :: Outputable a => String -> a -> TC.TcPluginM ()
tcTrace label x =
  tcPluginTrace ("[checked-exceptions] " <> label) (ppr x)
