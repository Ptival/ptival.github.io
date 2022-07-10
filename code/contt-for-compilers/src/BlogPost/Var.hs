{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module BlogPost.Var where

import Data.Maybe (fromMaybe)
import Data.String (IsString)
import Prettyprinter (Pretty (pretty))

newtype Bdr = B {getBdr :: String} deriving (Eq, IsString, Ord, Show)

instance Pretty Bdr where
  pretty = pretty . getBdr

newtype Var = V {getVar :: String} deriving (Eq, IsString, Ord, Show)

instance Pretty Var where
  pretty = pretty . getVar

bdrOfVar :: Var -> Bdr
bdrOfVar = B . getVar

varOfBdr :: Bdr -> Var
varOfBdr = V . getBdr
