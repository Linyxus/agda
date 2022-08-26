{-# LANGUAGE NondecreasingIndentation #-}
module Agda.TypeChecking.IApplyConfluence where

import Prelude hiding (null, (!!))  -- do not use partial functions like !!

import Control.Monad
import Control.Arrow (first,second)

import qualified Data.List as List
import qualified Data.Map as Map

import Agda.Syntax.Common
import Agda.Syntax.Position
import Agda.Syntax.Internal.Generic
import Agda.Syntax.Internal
import Agda.Syntax.Internal.Pattern

import Agda.Interaction.Options

import Agda.TypeChecking.Primitive hiding (Nat)
import Agda.TypeChecking.Monad
import Agda.TypeChecking.Pretty
import Agda.TypeChecking.Records
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Telescope.Path
import Agda.TypeChecking.Telescope
import Agda.TypeChecking.Conversion
import Agda.TypeChecking.Substitute

import qualified Agda.Utils.BiMap as BiMap
import Agda.Utils.Monad
import Agda.Utils.Null
import Agda.Utils.Maybe
import Agda.Utils.Size
import Agda.Utils.Impossible
import Agda.Utils.Functor
import Agda.TypeChecking.Monad.Boundary


checkIApplyConfluence_ :: QName -> TCM ()
checkIApplyConfluence_ f = whenM (isJust . optCubical <$> pragmaOptions) $ do
  -- Andreas, 2019-03-27, iapply confluence should only be checked
  -- when --cubical or --erased-cubical is active. See
  -- test/Succeed/CheckIApplyConfluence.agda.
  -- We cannot reach the following crash point unless
  -- --cubical/--erased-cubical is active.
  __CRASH_WHEN__ "tc.cover.iapply.confluence.crash" 666
  reportSDoc "tc.cover.iapply" 10 $ text "Checking IApply confluence of" <+> pretty f
  inConcreteOrAbstractMode f $ \ d -> do
  case theDef d of
    Function{funClauses = cls', funCovering = cls} -> do
      reportSDoc "tc.cover.iapply" 10 $ text "length cls =" <+> pretty (length cls)
      when (null cls && any (not . null . iApplyVars . namedClausePats) cls') $
        __IMPOSSIBLE__
      modifySignature $ updateDefinition f $ updateTheDef $ updateCovering (const [])
      forM_ cls $ checkIApplyConfluence f
    _ -> return ()

-- | 'checkIApplyConfluence' checks that the given clause reduces in a
-- way that is confluent with IApply reductions. The way this works is
-- as follows: Since IApply reductions happen under the function, it
-- suffices to check that the clause LHS (turned into an expression) is
-- equal to the clause RHS at every interval substitution.
checkIApplyConfluence :: QName -> Clause -> TCM ()
checkIApplyConfluence f cl = case cl of
  Clause {clauseBody = Nothing} -> return ()
  Clause {clauseType = Nothing} -> __IMPOSSIBLE__
  cl@Clause { clauseTel = clTel
            , namedClausePats = ps
            , clauseType = Just t
            , clauseBody = Just body
            , clauseFullRange = range
            } -> setCurrentRange range $ do
    -- For reporting, use the range associated with the clause (rather
    -- than with the function's name). That way, if there's any yellow,
    -- it might get hidden by the clause (e.g. if the RHS is an
    -- interaction point).

    let trhs = unArg t
        check b = b { boundaryCheck = True }
    reportSDoc "tc.cover.iapply" 40 $ "tel =" <+> prettyTCM clTel
    reportSDoc "tc.cover.iapply" 40 $ "ps =" <+> pretty ps

    addContext clTel $ do
      ps <- normaliseProjP ps
      withLHSBoundary f ps trhs $ do
        -- 'withLHSBoundary' adds the boundary *as hints*, so we have to
        -- make them checkable here. Additionally, we normalise the
        -- boundary (only to compute display forms. Normalising too far
        -- causes a failure in checking an hcomp clause in
        -- Cubical.Homotopy.Hopf)
        b' <- normaliseBoundary' True =<< fmap (Boundary . map check . boundaryFaces) (asksTC envBoundary)
        localTC (\e -> e { envBoundary = b' }) $
          -- Using 'discardBoundary' for checking the equalities means
          -- that we get the proper boundary condition error messages.
          discardBoundary $ \check -> check CmpEq trhs body

-- | If there are any 'IApply' co/patterns in the list of patterns,
-- invert it into a boundary, and add that to the environment as a list
-- of hints.
withLHSBoundary :: QName -> [NamedArg DeBruijnPattern] -> Type -> TCM a -> TCM a
withLHSBoundary f pat rhst k | not (null (iApplyVars pat)) = do
  ineg <- primINeg
  let
    es = patternsToElims pat
    want = Def f es
    boundary = [ [(var k, want), (ineg `apply` [argN (var k)], want)] | k <- iApplyVars pat ]
  withBoundaryHint (concat boundary) k
withLHSBoundary _ _ _ k = k


-- | current context is of the form Γ.Δ
unifyElims :: Args
              -- ^ variables to keep   Γ ⊢ x_n .. x_0 : Γ
           -> Args
              -- ^ variables to solve  Γ.Δ ⊢ ts : Γ
           -> (Substitution -> [(Term,Term)] -> TCM a)
              -- Γ.Δ' ⊢ σ : Γ.Δ
              -- Γ.Δ' new current context.
              -- Γ.Δ' ⊢ [(x = u)]
              -- Γ.Δ', [(x = u)] ⊢ id_g = ts[σ] : Γ
           -> TCM a
unifyElims vs ts k = do
                      dom <- getContext
                      let (binds' , eqs' ) = candidate (map unArg vs) (map unArg ts)
                          (binds'', eqss') =
                            unzip $ map (\ (j,t:ts) -> ((j,t),map (,var j) ts)) $ Map.toList $ Map.fromListWith (++) (map (second (:[])) binds')
                          cod   = codomain s (map fst binds) dom
                          binds = map (second (raise (size cod - size vs))) binds''
                          eqs   = map (first  (raise $ size dom - size vs)) $ eqs' ++ concat eqss'
                          s     = bindS binds
                      updateContext s (codomain s (map fst binds)) $ do
                      k s (s `applySubst` eqs)
  where
    candidate :: [Term] -> [Term] -> ([(Nat,Term)],[(Term,Term)])
    candidate (i:is) (Var j []:ts) = first ((j,i):) (candidate is ts)
    candidate (i:is) (t:ts)        = second ((i,t):) (candidate is ts)
    candidate [] [] = ([],[])
    candidate _ _ = __IMPOSSIBLE__


    bindS binds = parallelS (for [0..maximum (-1:map fst binds)] $ (\ i -> fromMaybe (deBruijnVar i) (List.lookup i binds)))

    codomain :: Substitution
             -> [Nat]  -- support
             -> Context -> Context
    codomain s vs cxt = map snd $ filter (\ (i,c) -> i `List.notElem` vs) $ zip [0..] cxt'
     where
      cxt' = zipWith (\ n d -> dropS n s `applySubst` d) [1..] cxt


-- | Like @unifyElims@ but @Γ@ is from the the meta's @MetaInfo@ and
-- the context extension @Δ@ is taken from the @Closure@.
unifyElimsMeta :: MetaId -> Args -> Closure Constraint -> ([(Term,Term)] -> Constraint -> TCM a) -> TCM a
unifyElimsMeta m es_m cl k = ifM (isNothing . optCubical <$> pragmaOptions) (enterClosure cl $ k []) $ do
                  mv <- lookupLocalMeta m
                  enterClosure (getMetaInfo mv) $ \ _ -> do -- mTel ⊢
                  ty <- metaType m
                  mTel0 <- getContextTelescope
                  unless (size mTel0 == size es_m) $ reportSDoc "tc.iapply.ip.meta" 20 $ "funny number of elims" <+> text (show (size mTel0, size es_m))
                  unless (size mTel0 <= size es_m) $ __IMPOSSIBLE__ -- meta has at least enough arguments to fill its creation context.
                  reportSDoc "tc.iapply.ip.meta" 20 $ "ty: " <+> prettyTCM ty

                  -- if we have more arguments we extend the telescope accordingly.
                  TelV mTel1 _ <- telViewUpToPath (size es_m) ty
                  addContext (mTel1 `apply` teleArgs mTel0) $ do
                  mTel <- getContextTelescope
                  reportSDoc "tc.iapply.ip.meta" 20 $ "mTel: " <+> prettyTCM mTel

                  es_m <- return $ take (size mTel) es_m
                  -- invariant: size mTel == size es_m

                  (c,cxt) <- enterClosure cl $ \ c -> (c,) <$> getContextTelescope
                  reportSDoc "tc.iapply.ip.meta" 20 $ prettyTCM cxt

                  addContext cxt $ do

                  reportSDoc "tc.iapply.ip.meta" 20 $ "es_m" <+> prettyTCM es_m

                  reportSDoc "tc.iapply.ip.meta" 20 $ "trying unifyElims"

                  unifyElims (teleArgs mTel) es_m $ \ sigma eqs -> do

                  reportSDoc "tc.iapply.ip.meta" 20 $ "gotten a substitution"

                  reportSDoc "tc.iapply.ip.meta" 20 $ "sigma:" <+> prettyTCM sigma
                  reportSDoc "tc.iapply.ip.meta" 20 $ "sigma:" <+> pretty sigma

                  k eqs (sigma `applySubst` c)
