{-# LANGUAGE OverloadedStrings #-}

module Source
  ( Exp (..),
    prettyApp,
    prettyLet,
  )
where

import Prettyprinter (Doc, Pretty (pretty), hang, hsep, vcat)
import Var (Bdr, Var)

data Exp
  = App Exp Exp
  | Int Int
  | Let Bdr Exp Exp
  | Var Var
  deriving (Show)

prettyApp :: Pretty a => Pretty b => a -> b -> Doc d
prettyApp e1 e2 = hsep [pretty e1, pretty e2]

prettyLet :: Pretty a => Pretty b => Pretty c => a -> b -> c -> Doc d
prettyLet b e1 e2 =
  vcat
    [ hsep ["let", pretty b, "=", hang 0 (pretty e1), "in"],
      hsep [pretty e2]
    ]

instance Pretty Exp where
  pretty (App e1 e2) = prettyApp e1 e2
  pretty (Int i) = pretty i
  pretty (Let b e1 e2) = prettyLet b e1 e2
  pretty (Var v) = pretty v
