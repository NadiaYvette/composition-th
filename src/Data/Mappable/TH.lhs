\documentclass{article}
%include polycode.fmt
\begin{document}
\begin{code}
module Data.Mappable.TH where
import           "base"              Data.Char as
  Char (intToDigit, isLetter)
import           "base"              Data.Function (on)
import qualified "base"              Data.List as
  List (splitAt)
import           "base"              Numeric.Natural (Natural)

import qualified "template-haskell"  Language.Haskell.TH as
  TH ( Body (NormalB), Clause (..), Dec (FunD, InfixD, SigD)
     , Exp (AppE, InfixE, LamE, VarE) , Fixity (..)
     , FixityDirection (InfixL, InfixR)
     , NamespaceSpecifier (NoNamespaceSpecifier), Pat (VarP), Q
     , Specificity (SpecifiedSpec)
     , Type (AppT, ArrowT, ConT, ForallT, VarT)
     , TyVarBndr (PlainTV), mkName)
import qualified "template-haskell"  Language.Haskell.TH.CodeDo as
  TH ()
import qualified "template-haskell"  Language.Haskell.TH.LanguageExtensions as
  TH ()
import qualified "template-haskell"  Language.Haskell.TH.Lib as
  TH ()
import qualified "template-haskell"  Language.Haskell.TH.Ppr as
  TH (Ppr (..))
import qualified "template-haskell"  Language.Haskell.TH.PprLib as
  TH (Doc)
import qualified "template-haskell"  Language.Haskell.TH.Quote as
  TH ()
import qualified "template-haskell"  Language.Haskell.TH.Syntax as
  TH (Name (..))

import qualified "unicode-tricks"    Data.Char.Small as
  Unicode (toSub)
\end{code}

Find a decent Unicode symbol for this.
\begin{code}
infixr 1 ↪
(↪) :: TH.Type → TH.Type → TH.Type
v ↪ v' = (TH.ArrowT `TH.AppT` v) `TH.AppT` v'

infix 4 ≤
(≤) :: Ord t ⇒ t → t → Bool
(≤) = (<=)
\end{code}

\begin{code}
mkStrList :: Char -> Natural → [String]
mkStrList c n
  | Char.isLetter c && n ≤ 9
  , n' <- fromIntegral n
  = [[c,k] | Just k <- Unicode.toSub . Char.intToDigit <$> [1..n']]
  | otherwise
  = error "non-letter character or integer too large for digit"

mkNameList :: Char -> Natural → [TH.Name]
mkNameList c n = TH.mkName <$> mkStrList c n

mkFmap :: Natural → TH.Q [TH.Dec]
mkFmap = pure . mkFmap'

pprFmap :: Natural → TH.Doc
pprFmap = TH.ppr . mkFmap'

mkFmap' :: Natural → [TH.Dec]
mkFmap' n = dollarDecls <> ampersandDecls where
  dollarDecls = [infixD, sigD, name `TH.FunD` [clause]]
  ampersandDecls = [infixD', sigD', name' `TH.FunD` [clause']]
  n' = fromIntegral n
  name  = TH.mkName $ "<" <> replicate n' '$' <> ">"
  name' = TH.mkName $ "<" <> replicate n' '&' <> ">"
  fmapVarE = TH.VarE $ TH.mkName "fmap"
  flipVarE = TH.VarE $ TH.mkName "flip"
  dotVarE = TH.VarE $ TH.mkName "."
  infixE x y = TH.InfixE x dotVarE y
  fixity  = (n' + 3) `TH.Fixity` TH.InfixL
  fixity' = (n' - 1) `TH.Fixity` TH.InfixL
  infixD  = TH.InfixD fixity  TH.NoNamespaceSpecifier name
  infixD' = TH.InfixD fixity' TH.NoNamespaceSpecifier name'
  tyVars = mkNameList 'φ' n
  tyVars' = TH.mkName <$> ["t", "t'"]
  t = TH.VarT $ tyVars' !! 0
  t' = TH.VarT $ tyVars' !! 1
  ctx     = [TH.ConT (TH.mkName "Functor") `TH.AppT` TH.VarT tv | tv <- tyVars]
  specs   = [TH.PlainTV tv TH.SpecifiedSpec | tv <- tyVars' <> tyVars]
  argTy   = foldr TH.AppT t $ TH.VarT <$> tyVars
  retTy   = foldr TH.AppT t' $ TH.VarT <$> tyVars
  sigD    = TH.SigD name  typeE
  sigD'   = TH.SigD name' typeE'
  typeE   = TH.ForallT specs ctx $ (t ↪ t') ↪ argTy ↪ retTy
  typeE'  = TH.ForallT specs ctx $ argTy ↪ (t ↪ t') ↪ retTy
  body    = TH.NormalB . foldr1 (infixE `on` Just) $ replicate n' fmapVarE
  body'   = TH.NormalB $ flipVarE `TH.AppE` TH.VarE name
  clause  = TH.Clause [{- no pat -}] body  [{- no decls -}]
  clause' = TH.Clause [{- no pat -}] body' [{- no decls -}]
\end{code}

\begin{code}
mkMapM :: Natural → TH.Q [TH.Dec]
mkMapM = pure . mkMapM'

pprMapM :: Natural → TH.Doc
pprMapM = TH.ppr . mkMapM'

mkMapM' :: Natural → [TH.Dec]
mkMapM' n = dollarDecls <> ampersandDecls where
  dollarDecls = [infixD, sigD, name `TH.FunD` [clause]]
  ampersandDecls = [infixD', sigD', name' `TH.FunD` [clause']]
  n' = fromIntegral n
  name  = TH.mkName $ replicate n' '$' <> "=<<"
  name' = TH.mkName $ ">>=" <> replicate n' '$'
  mapMVarE = TH.VarE $ TH.mkName "mapM"
  flipVarE = TH.VarE $ TH.mkName "flip"
  dotVarE = TH.VarE $ TH.mkName "."
  infixE x y = TH.InfixE x dotVarE y
  fixity  = n' `TH.Fixity` TH.InfixR
  fixity' = n' `TH.Fixity` TH.InfixL
  infixD  = TH.InfixD fixity  TH.NoNamespaceSpecifier name
  infixD' = TH.InfixD fixity' TH.NoNamespaceSpecifier name'
  tyVars = mkNameList 'τ' n
  tyVars' = TH.mkName <$> ["µ", "t", "t'"]
  m = TH.VarT $ tyVars' !! 0
  t = TH.VarT $ tyVars' !! 1
  t' = TH.VarT $ tyVars' !! 2
  ctx     = (TH.ConT (TH.mkName "Monad") `TH.AppT` m)
          : [TH.ConT (TH.mkName "Traversable") `TH.AppT` TH.VarT tv | tv <- tyVars]
  specs   = [TH.PlainTV tv TH.SpecifiedSpec | tv <- tyVars' <> tyVars]
  argTy   = foldr TH.AppT t $ TH.VarT <$> tyVars
  retTy   = m `TH.AppT` foldr TH.AppT t' (TH.VarT <$> tyVars)
  sigD    = TH.SigD name  typeE
  sigD'   = TH.SigD name' typeE'
  typeE   = TH.ForallT specs ctx $ (t ↪ (m `TH.AppT` t')) ↪ argTy ↪ retTy
  typeE'  = TH.ForallT specs ctx $ argTy ↪ (t ↪ (m `TH.AppT` t')) ↪ retTy
  body    = TH.NormalB . foldr1 (infixE `on` Just) $ replicate n' mapMVarE
  body'   = TH.NormalB $ flipVarE `TH.AppE` TH.VarE name
  clause  = TH.Clause [{- no pat -}] body  [{- no decls -}]
  clause' = TH.Clause [{- no pat -}] body' [{- no decls -}]

mkPassN :: Natural → TH.Q [TH.Dec]
mkPassN = pure . mkPassN'

pprPassN :: Natural → TH.Doc
pprPassN = TH.ppr . mkPassN'

replace :: Int -> t -> [t] -> [t]
replace k x xs = case List.splitAt k xs of
  (ys, _ : zs) -> ys <> (x : zs)
  (ys, []) -> ys <> [x]

mkPassN' :: Natural → [TH.Dec]
mkPassN' n = [infixD, sigD, name `TH.FunD` [clause]] where
  n' = fromIntegral n
  -- name  = TH.mkName $ "passArg" <> show n
  name  = TH.mkName $ replicate n' '$'
  tyStrs  = mkStrList 'τ' $ n + 1
  tyNames = TH.mkName <$> tyStrs
  pats    = TH.VarP . TH.mkName . replace 0 'x' <$> init (init tyStrs)
  tyVars  = TH.VarT <$> tyNames
  argTy   = tyVars !! (n' - 1)
  argPat  = TH.VarP . TH.mkName . replace 0 'x' $ tyStrs !! (n' - 1)
  allExps = TH.VarE . TH.mkName . replace 0 'x' <$> init tyStrs
  funTy   = foldr1 (↪) tyVars
  funPat  = TH.VarP $ TH.mkName "f"
  funExp  = TH.VarE $ TH.mkName "f"
  retTy   = foldr1 (↪) $ take (n' - 1) tyVars <> [tyVars !! n']
  ctx     = []
  specs   = [TH.PlainTV tn TH.SpecifiedSpec | tn <- tyNames]
  sigD    = TH.SigD name typeE
  fixity  = (n' - 1) `TH.Fixity` TH.InfixR
  infixD  = TH.InfixD fixity  TH.NoNamespaceSpecifier name
  typeE   = TH.ForallT specs ctx $ funTy ↪ argTy ↪ retTy
  body    = TH.NormalB . TH.LamE pats $ foldl TH.AppE funExp allExps
  clause  = TH.Clause [funPat, argPat] body  [{- no decls -}]
\end{code}

\begin{spec}
mkOnN' :: Natural → [TH.Dec]
mkOnN' n = [infixD, sigD, name `TH.FunD` [clause]] where
  n'       = fromIntegral n
  str      = "on" <> show n
  name     = TH.mkName str
  pat      = TH.VarP name
  tyStrs   = mkStrList 't' $ n' + 2
  tyNames  = TH.mkName <$> tyStrs
  tyTypes  = TH.VarT <$> tyNames
  varStrs  = mkStrList 'x' n'
  varNames = TH.mkName <$> varStrs
  varPats  = TH.VarP <$> varNames
  varExps  = TH.VarE <$> varNames
  fStr     = "f"
  fName    = TH.mkName fStr
  fType    = foldr1 (↪) $ take (n' + 1) tyVars
  fExp     = TH.VarE <$> fName
  fPat     = TH.VarP <$> fName
  gStr     = "g"
  gName    = TH.mkName gStr
  gExp     = TH.VarE <$> gName
  gPat     = TH.VarP <$> gName
  tyVars   = TH.VarT <$> tyNames
  argTy    = TH.mkName $ tyStrs !! (n' + 1) 
  argPat   = TH.VarP . TH.mkName . replace 0 'x' $ tyStrs !! (n' - 1)
  allExps  = TH.VarE . TH.mkName . replace 0 'x' <$> init tyStrs
  retTy    = foldr1 (↪) . replace (n' - 1) (tyVars !! (n' + 1))
             $ take (n' - 1) tyVars
  ctx      = []
  specs    = [TH.PlainTV tn TH.SpecifiedSpec | tn <- tyNames]
  sigD     = TH.SigD name typeE
  fixity   = 1 `TH.Fixity` TH.InfixL
  infixName = TH.mkName $ "`on" <> show n <> "`"
  infixD   = TH.InfixD fixity TH.NoNamespaceSpecifier infixName
  typeE    = TH.ForallT specs ctx $ funTy ↪ argTy ↪ retTy
  body     = TH.NormalB . TH.LamE varPats
             $ foldl TH.AppE fExp (init varExps)
                 `TH.AppE` (gExp `TH.AppE` (varExps !! (n' - 1)))
  clause   = TH.Clause [fPat, gPat] body  [{- no decls -}]
\end{spec}
\end{document}
