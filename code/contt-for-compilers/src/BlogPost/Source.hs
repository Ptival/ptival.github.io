{-# LANGUAGE OverloadedStrings #-}

module BlogPost.Source where

import BlogPost.Var (Bdr, Var)
import Control.Lens (Field1 (_1), over)
import Data.String (IsString (fromString))
import Prettyprinter (Doc, Pretty (pretty), hang, hsep, vcat)

data Exp
  = App Exp Exp
  | Int Int
  | Lam Bdr Exp
  | Let Bdr Exp Exp
  | Var Var
  deriving (Show)

instance IsString Exp where
  fromString = Var . fromString

prettyApp :: Doc d -> Doc d -> Doc d
prettyApp e1 e2 = hsep [e1, e2]

prettyLam :: Doc d -> Doc d -> Doc d
prettyLam b e =
  vcat
    [ hsep ["\\", b, "->"],
      hang 0 e
    ]

prettyLet :: Doc d -> Doc d -> Doc d -> Doc d
prettyLet b e1 e2 =
  vcat
    [ hsep ["let", b, "=", hang 0 e1, "in"],
      hang 0 e2
    ]

instance Pretty Exp where
  pretty (App e1 e2) = prettyApp (pretty e1) (pretty e2)
  pretty (Int i) = pretty i
  pretty e@(Lam {}) =
    let (bs, e') = gatherLams e
     in prettyLam (hsep $ pretty <$> bs) (pretty e')
    where
      gatherLams :: Exp -> ([Bdr], Exp)
      gatherLams (Lam b e) = over _1 (b :) $ gatherLams e
      gatherLams e = ([], e)
  pretty (Let b e1 e2) = prettyLet (pretty b) (pretty e1) (pretty e2)
  pretty (Var v) = pretty v

apps :: [Exp] -> Exp
apps (h : r) = foldl App h r
apps [] = error "apps: empty list"

lams :: [Bdr] -> Exp -> Exp
lams = flip (foldr Lam)

lets :: [(Bdr, Exp)] -> Exp -> Exp
lets = flip (foldr (uncurry Let))
