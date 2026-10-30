-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SpecLate.lean: the two statements that relate the committer and the prover of the
compiled scheme (Compile/Batch/Star.lean: `Cp`, `Pp`) to their forms in `LStep`
(Compile/Batch/Mirror.lean: `CpL`, `PpL`) by `Rom.Late`. Definitions and statements, and one small
lemma with its proof (`IskK.ext`); the proofs of the two statements are in Compile/Batch/Late4.lean.
(Words of this library: lean/GLOSSARY.md.)

`LStep` (Rom/DeferLate.lean): "One step of a challenger that supplies points at the release. As
Step, but for marked and reveal." `Rom.Late post n Γ P Q` (the same file), for a `Step` program P
and an `LStep` program Q: "P and Q have the same constructors; Q has no closures at its marked
evaluations (and draws their answers from all of the range), and at each reveal of ts it supplies,
for every token of ts and every oracle at which P has charged it, the closure that P gave." "post
relates the results, with the bound and the context at the end."

A closure (`Clo`, Rom/DeferLate.lean) is the function that makes the input of a marked query from
the values of its tokens; the context Γ (`Ctx`; here `Cx`, Compile/Batch/Mirror.lean) records, by
charged token and oracle, the one that the `Step` program gave.
-/
import Compile.Batch.Late3
import Compile.Batch.SpecFit

noncomputable section

namespace Compile.Batch
open Iop Rom

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- the body of leaf j of the tree over the encoding of i with the randomness r -/
def encBody (i : I) (r : L.EncodingRandomness) (j : ℕ) : Body L :=
  if h : j < L.wordLength then some (.inl (L.encodeIndex i r ⟨j, h⟩)) else none

/-- What the context Γ records of a key, at most: for every salted leaf of the tree of every copy:
its two tokens are older than n; for the salt Γ records no closure that holds data but, at most, the
one with the true symbol; for the digest none that holds data. -/
def IskK {K : ℕ} (Γ : Cx lam K L) (n : ℕ) (k : IskH lam L) : Prop :=
  ∀ lf ∈ k.leaves, ExtK Γ n (encBody k.i lf.node.r) lf.node.tree.salts

/-- `IskK` is preserved by everything that adds only closures without data below n, also at a larger
bound n' ≥ n -/
theorem IskK.ext {K : ℕ} {Γ Γ' : Cx lam K L} {n n' : ℕ} {k : IskH lam L} (h : IskK Γ n k)
    (hE : Ext n Γ Γ') (hn : n ≤ n') : IskK Γ' n' k :=
  fun lf hlf j s d hs => by
    obtain ⟨h1, h2, h3, h4⟩ := h lf hlf j s d hs
    exact ⟨h1.ext hE h3, h2.ext hE h4, by omega, by omega⟩

/-- The committer (hypotheses below). Of `GrFitPB` only `readsPut` is used: the prover opens the
positions that the verifier reads at the plain parts with the nonces; the form in `LStep` takes the
symbols from the view of the interactive protocol, which holds those read at the plain parts as the
interactive prover sends them. -/
def Spec.lateCpB : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I)
      (n : ℕ) (Γ : Cx lam W.K L),
    L.Wired → W.OKG → GrFitPB W → Fut n Γ →
    Late (fun n' Γ' a b => a = b ∧ n ≤ n' ∧ Fut n' Γ' ∧ Ext n Γ Γ' ∧ IskK Γ' n' a.2) n Γ
      (Cp W WP p i) (CpL W WP p i)

def Spec.latePpB : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) (n : ℕ) (Γ : Cx lam W.K L),
    L.Wired → W.OKG → GrFitPB W → L.onlineBatch.ann.Coherent → Fut n Γ → IskK Γ n k →
    Late (fun n' Γ' a b => a = b ∧ n ≤ n' ∧ Fut n' Γ' ∧ Ext n Γ Γ') n Γ
      (Pp W WP p k fr xs) (PpL W WP p k fr xs)

end Compile.Batch
