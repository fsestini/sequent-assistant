{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

module TeX (texTree) where

import Formula
import Proof
import Text.PrettyPrint
import Tree

texTree :: _ => ProofTree a -> String
texTree = render . ppTree

ppTree :: _ => ProofTree a -> Doc
ppTree (Node concl prems) =
  if null prems
    then ppConcl
    else vcat
           [ text "\\inferrule*{"
           , nest 2 ppPrems
           , text "}{"
           , nest 2 ppConcl
           , text "}"
           ]
  where
    ppPrems = vcat $ punctuate (text "\\\\ \\quad") $ map ppTree prems
    ppConcl = text . show $ concl

