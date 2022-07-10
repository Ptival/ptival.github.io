{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

module BlogPost.Renaming where

import BlogPost.Var (Bdr (B), Var (V), varOfBdr)
import Control.Lens (Getter, Lens', makeLenses, over, view)
import Control.Monad.Reader (ReaderT)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)

data Renaming = Renaming
  { _renameBdr :: Map.Map Bdr Bdr,
    _renameVar :: Map.Map Var Var
  }

makeLenses ''Renaming

newtype RenameT m a = RenameT {unRenameT :: ReaderT Renaming m a}

class Renamable a where
  rename :: Renaming -> a -> a

instance Renamable Bdr where
  rename r b = fromMaybe b (Map.lookup b (view renameBdr r))

instance Renamable Var where
  rename r v = fromMaybe v (Map.lookup v (view renameVar r))

removeBdr :: Bdr -> Renaming -> Renaming
removeBdr b@(B s) =
  over renameBdr (Map.delete b)
    . over renameVar (Map.delete (V s))

emptyRenaming :: Renaming
emptyRenaming = Renaming Map.empty Map.empty

addRenaming :: (Bdr, Bdr) -> Renaming -> Renaming
addRenaming (from, to) =
  over renameBdr (Map.union (Map.singleton from to))
  . over renameVar (Map.union (Map.singleton (varOfBdr from) (varOfBdr to)))

renaming :: (Bdr, Bdr) -> Renaming
renaming = (`addRenaming` emptyRenaming)
