-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/TwinTiePure.lean: six functions of Run/TwinDefs.lean that ask no query equal the library's
functions (Compile/Batch/Verifier.lean) at the shape of the skeleton.

Statements (each a `Prop` in `Run.Twin.Spec`); the proofs are in Run/TwinTiePureProofs.lean.
Generic. Bookkeeping on this library's own terms.
Run/TwinDefs.lean writes the compiled verifier of one slot (`Compile.Batch.verifyOneProtocol`, a tree of
oracle queries) again as `verifyT`, whose helpers recurse on a list S of skeletons of rounds in the
place of the shape `up S`. The skeleton of a round (`RS`) has the round's fields with the instance
`Fintype Chal` behind a function of `Unit`.

Main names. For every list S of skeleton rounds, with `up S` its shape:
  `Spec.effPlainT_eq`: (for one skeleton r, at `r.up`) the plain part of a round that counts.
  `Spec.effPlainsT_eq`: the same for all rounds.
  `Spec.mkTrT_eq`: the transcript that the verifier builds.
  `Spec.countT_eq`: how many roots the chain has taken.
  `Spec.strictST_eq`: the strict format of the openings.
  `Spec.forestsT_eq`: the checks, tree by tree.

All but the first are used in Run/TwinTie.lean: that `verifyT`, at the interface's `early` and
`late`, is the library's verifier, as a tree of queries.

Limits: this file says nothing on what an evaluator builds or does not build. The functions of
Run/TwinDefs.lean that ask the oracle (the chain, what follows it, the whole verifier) are not
treated here, nor are `lateT`, `forestsOfT`, `strictBT`: Run/TwinTie.lean.

Terms: lean/GLOSSARY.md.
-/
import Run.TwinDefs

set_option autoImplicit false

namespace Run.Twin
open Iop Rom Compile Compile.Batch

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
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocol I X) (S : List RS) (A : RoundSplits (up S))
      (W : RoundsQueryLayout lam K (up S) A) (emb : (p : OPos (up S)) → OSym (up S) p → Body L)
      (rts : RootsOfChain lam (up S)) (isRead : OPos (up S) → Bool)
      (f : (p : OPos (up S)) → Option (Opening lam (OSym (up S) p))),
    forestsT S A W emb rts isRead f = forestsB (up S) A W emb rts isRead f

end Spec
end Run.Twin
