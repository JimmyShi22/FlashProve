-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/TwinTiePure.lean.
Run/TwinTiePure.lean: THE TWIN'S SIX FUNCTIONS WITHOUT A QUERY (Run/TwinDefs.lean) ARE THE LIBRARY'S
(Compile/Batch/Verifier.lean) AT THE SHAPE OF THE SKELETON. Statements (Run.Twin.Spec.*); the proofs
are in Run/TwinTiePureProofs.lean. Generic. Bookkeeping on our own terms.
For every list S of skeleton rounds, with up S its shape:
   Spec.effPlainT_eq      the plain part of a round that counts effPlainT r a rt pl = effPlain (r :=
                          r.up) a rt pl
   Spec.effPlainsT_eq     the same for all rounds effPlainsT S A rts pls = effPlains (up S) A rts
                          pls
   Spec.mkTrT_eq          the transcript that the verifier builds mkTrT S A W rts pls ρ f = mkTr (up
                          S) A W rts pls ρ f
   Spec.countT_eq         how many roots the chain has taken countT S rts = RootsOfChain.count (up S) rts
   Spec.strictST_eq       the strict format of the openings strictST sMT S A W rts isRead f =
                          strictSB sMT (up S) A W rts isRead f
   Spec.forestsT_eq       the checks, tree by tree forestsT S A W emb rts isRead f = forestsB (up S)
                          A W emb rts isRead f
 USE. Run/TwinTie.lean: that the twin of the whole verifier is the library's verifier, as a tree of
 queries.
WHAT IS NOT SAID. Nothing on what an evaluator builds or does not build. The twin's functions that
ask the oracle (the chain, what follows it, the whole verifier) are not treated here:
Run/TwinTie.lean.

Terms: lean/GLOSSARY.md.

-/
import Run.TwinTiePure
import OnBytes.TypedOracleCompiler.Run.TwinDefs

set_option autoImplicit false

namespace TypedOracleCompiler.Run.Twin
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.Twin

namespace Spec

def effPlainT_eq : Prop :=
  ∀ (lam : ℕ) (r : RS) (a : RAnn r.up) (rt : RtC lam × RtC lam) (pl : r.Plain),
    effPlainT r a rt pl = effPlain (r := r.up) a rt pl

def effPlainsT_eq : Prop :=
  ∀ (lam : ℕ) (S : List RS) (A : RoundSplits (up S)) (rts : RootsOfChain lam (up S)) (pls : Plains (up S)),
    effPlainsT S A rts pls = effPlains (up S) A rts pls

def mkTrT_eq : Prop :=
  ∀ (lam K : ℕ) (S : List RS) (A : RoundSplits (up S)) (W : RoundsQueryLayout lam K (up S) A) (rts : RootsOfChain lam (up S))
      (pls : Plains (up S)) (ρ : Rho (up S))
      (f : (p : OPos (up S)) → Option (Opening lam (OSym (up S) p))),
    mkTrT S A W rts pls ρ f = mkTr (up S) A W rts pls ρ f

def countT_eq : Prop :=
  ∀ (lam : ℕ) (S : List RS) (rts : RootsOfChain lam (up S)), countT S rts = RootsOfChain.count (up S) rts

def strictST_eq : Prop :=
  ∀ (lam K sMT : ℕ) (S : List RS) (A : RoundSplits (up S)) (W : RoundsQueryLayout lam K (up S) A)
      (rts : RootsOfChain lam (up S)) (isRead : OPos (up S) → Bool)
      (f : (p : OPos (up S)) → Option (Opening lam (OSym (up S) p))),
    strictST sMT S A W rts isRead f = strictSB sMT (up S) A W rts isRead f

def forestsT_eq : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocolWithLeafBody I X) (S : List RS) (A : RoundSplits (up S))
      (W : RoundsQueryLayout lam K (up S) A) (emb : (p : OPos (up S)) → OSym (up S) p → Body L)
      (rts : RootsOfChain lam (up S)) (isRead : OPos (up S) → Bool)
      (f : (p : OPos (up S)) → Option (Opening lam (OSym (up S) p))),
    forestsT S A W emb rts isRead f = forestsB (up S) A W emb rts isRead f

end Spec
end TypedOracleCompiler.Run.Twin
