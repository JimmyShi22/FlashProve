-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/Chain.lean: sequential composition of interactive oracle reductions (IORs): rules for chains.

Definitions and statements; the proofs are in Ior/ChainProofs.lean.
An IOR (`IOR`, Ior/Ior.lean) is an interactive oracle reduction: a protocol after whose rounds the
verifier rejects or outputs a new statement.

Main names:
 1. The probability of the withheld set of a composition (`Spec.hid_seq_le`,
    `Spec.withheld_seq_le`). The hidden part of the withheld set of "R₁; then R₂" unites, over the
    coins of the first prover, the hidden sets of the second on what the first hands on. A bound for
    every single witness of the second says nothing about that union. The rule: if, for every first
    part ρ₁ that the first does not withhold, all these sets lie in one set G ρ₁ of probability at
    most z₂, the probabilities add.
 2. Extractors that read oracles only. An extractor here reads the implicit part of the input
    statement, the oracles that the prover sent and a witness of the output statement; by type no
    verifier message, no plain part, no explicit part. The form is kept by composition (`extSeqO`)
    if the middle implicit instance is itself a function of the input's implicit part and of the
    oracles sent (`ImpBy`), or if the first extractor looks neither at the oracles sent nor at the
    middle witness (`Spec.good_seq_dec`). There is no branch "the first verifier rejected" and no
    default value: knowledge soundness reads an extractor only where the verifier outputs a
    statement.
 3. One bundle, one rule. `Rels`: what a chain says about the statements at one of its joints (the
    honest relation, its relaxation `relR`, a condition on statements, and the core of a witness:
    the part that no prover's coins touch (by type any map `W → K`; among the clauses on it:
    `Good.keeps`, `GoodT.keeps`, `Good.cover`)). `Nums`: the numbers of an IOR.
    `Good R H A B ext P`: R with the honest side H leads from A to B: strings only, local, complete,
    knowledge sound with the extractor ext, honest-verifier exactly zero knowledge (`Good.exact`:
    `Honest.Exact`, Ior/Honest.lean), with the two probabilities. Under `R₁.ImpBy io`,
    `Spec.good_seq` composes all of it, with no side condition on withheld sets: the honest prover
    hands the core on unchanged (`keeps`), and the hidden withheld set lies in a set that reads the
    core only (`cover`).

Limits: this file says nothing on numbers of queries; nothing on running times. `keeps` and `cover`
are demanded at every ρ and for every witness, valid or not, and the bound `prCov` for every core:
they are meant to hold by construction. Where a bound needs a condition on the core, put the
condition into the set: cov k = {ρ | k is well formed and the event happens}. A bound under the
premise "the statement is in the relation" would not compose: if the first withholds every ρ₁, no
valid middle statement is at hand.
`keeps` is asked of every IOR, the last of a chain too, so the core of the input witness is a
function of the output witness. An IOR whose output witness forgets what its hidden event reads is
`Good` only with pHid ≥ the probability of the union of the events (Ior/ChainTest.lean). The way
out: what later events read rides along as a further part of the witness (Ior/Frame.lean:
`Honest.carry`, `Spec.good_frame`) and is dropped after the last joint (Ior/ChainZ.lean:
`Honest.dropZ`, `Spec.end_of_good`).
Terms: lean/GLOSSARY.md: bundle, chain, core, cover, honest side, IOR, joint, numbers (of a
reduction), plain part, preamble, relaxation, rides along, statement, string, withheld,
zero knowledge.
-/
import Ior.Batch
import Ior.Honest
import Ior.Know
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-- Two shapes of strings in a row are a shape of strings. -/
def Shape.IsPoint.append : {s t : Shape} → s.IsPoint → t.IsPoint → Shape.IsPoint (s ++ t)
  | [], _, _, b => b
  | _ :: _, _, (h, a), b => (h, Shape.IsPoint.append a b)

namespace IOR
variable {K X₁ X₂ X₃ Xi Xo X : Type} {E₁ E₂ E₃ Ei Eo E : ExtSpec} {W₁ W₂ W₃ Wi Wo W : Type}

/-! ## Extractors that read oracles only -/

/-- The new implicit instance is a function of the old one and of the oracles sent: it reads no
verifier message and no plain part. -/
def ImpBy (R : IOR Xi Ei Xo Eo) (io : Ei.Str → Orcs R.shape → Eo.Str) : Prop :=
  ∀ y τ, R.imp y τ = io y τ.read

/-- The same for a composition. -/
def ioSeq {s t : Shape} (io₁ : E₁.Str → Orcs s → E₂.Str) (io₂ : E₂.Str → Orcs t → E₃.Str) :
    E₁.Str → Orcs (s ++ t) → E₃.Str :=
  fun y o => io₂ (io₁ y o.fst) o.snd

/-- The extractor of a composition: that of the second, on the middle implicit instance and the
oracles of the second part; then that of the first. -/
def extSeqO {s t : Shape} (e₁ : E₁.Str → Orcs s → W₂ → W₁)
    (e₂ : E₂.Str → Orcs t → W₃ → W₂) (io : E₁.Str → Orcs s → E₂.Str) :
    E₁.Str → Orcs (s ++ t) → W₃ → W₁ :=
  fun y o w => e₁ y o.fst (e₂ (io y o.fst) o.snd w)

/-! ## The bundle -/

/-- What a chain says about the statements at a joint. -/
structure Rels (K X : Type) (E : ExtSpec) (W : Type) where
  /-- the relation of the honest side -/
  rel  : X → E.Str → W → Prop
  /-- its relaxation: what knowledge soundness speaks of (by type any relation
  `X × E.Str → W → Prop`; no clause of `Good` compares it with `rel`) -/
  relR : X × E.Str → W → Prop
  /-- the statements of which knowledge soundness speaks -/
  on   : X × E.Str → Prop
  /-- the part of a witness that no prover's coins touch (by type any map `W → K`; among the clauses
  on it: `Good.keeps`, `GoodT.keeps`, `Good.cover`) -/
  core : W → K

/-- The numbers of an IOR: errors (counts), bounds on the probabilities of the public and of the
hidden withheld set, the budget of further reads, and a cover of the hidden withheld set that reads
the core only. (`Good.prBad`, `Good.cover`, `Good.prCov`) -/
structure Nums (K : Type) (R : IOR Xi Ei Xo Eo) where
  err  : Err R.shape
  pBad : ℝ≥0∞
  pHid : ℝ≥0∞
  bud  : Rho R.shape → Finset (OPos R.shape) → Prop
  cov  : K → Set (Rho R.shape)

/-- R, with the honest side H, leads from A to B. -/
structure Good (R : IOR Xi Ei Xo Eo) (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi)
    (B : Rels K Xo Eo Wo) (ext : Ei.Str → Orcs R.shape → Wo → Wi) (P : Nums K R) : Prop where
  point   : Nonempty R.shape.IsPoint
  isLocal : R.IsLocal
  acc     : H.Acc A.rel B.rel
  onOut   : ∀ a τ b, A.on a → R.red.out a τ = some b → B.on b
  keeps   : ∀ w x c ρ, B.core ((H.strat w x c).run ρ).2.2 = A.core w
  prBad   : prRho H.Bad ≤ P.pBad
  cover   : ∀ w x, H.Hid w x ⊆ P.cov (A.core w)
  prCov   : ∀ k, prRho (P.cov k) ≤ P.pHid
  know    : R.red.Know A.on A.relR B.relR (fun a τ w => ext a.2 τ.read w) P.err
  exact   : H.Exact A.rel P.bud

/-- The numbers of a composition: errors in a row, probabilities added, the composed budget, the two
covers side by side. -/
def Nums.seq {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃}
    (P₁ : Nums K R₁) (P₂ : Nums K R₂) : Nums K (R₁.seq R₂) where
  err  := Err.app P₁.err P₂.err
  pBad := P₁.pBad + P₂.pBad
  pHid := P₁.pHid + P₂.pHid
  bud  := budSeq R₁ R₂ P₁.bud P₂.bud
  cov  := fun k => Rho.cylFst R₂.shape (P₁.cov k) ∪ Rho.cylSnd R₁.shape (P₂.cov k)

/-- P' is weaker than P. -/
structure Nums.Le {R : IOR Xi Ei Xo Eo} (P P' : Nums K R) : Prop where
  err  : Err.le P.err P'.err
  pBad : P.pBad ≤ P'.pBad
  pHid : P.pHid ≤ P'.pHid
  bud  : ∀ ρ T, P'.bud ρ T → P.bud ρ T
  cov  : ∀ k, P'.cov k = P.cov k

end IOR

namespace Spec
open IOR

/-- The hidden withheld set of a composition. G ρ₁ holds, for every coin of the first prover, the
hidden withheld set of the second on what the first hands on at ρ₁. -/
def hid_seq_le : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (w : W₁) (x : X₁)
      (G : Rho R₁.shape → Set (Rho R₂.shape)) (z₁ z₂ : ℝ≥0∞),
    prRho (H₁.Hid w x) ≤ z₁ →
    (∀ ρ₁, ρ₁ ∉ H₁.withheld w x →
      ∀ c, H₂.Hid ((H₁.strat w x c).run ρ₁).2.2 ((H₁.strat w x c).run ρ₁).2.1 ⊆ G ρ₁) →
    (∀ ρ₁, ρ₁ ∉ H₁.withheld w x → prRho (G ρ₁) ≤ z₂) → prRho ((H₁.seq H₂).Hid w x) ≤ z₁ + z₂

/-- The public bad set of a composition. -/
def bad_seq_le : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (b₁ b₂ : ℝ≥0∞),
    prRho H₁.Bad ≤ b₁ → prRho H₂.Bad ≤ b₂ → prRho (H₁.seq H₂).Bad ≤ b₁ + b₂

/-- The whole withheld set of a composition (the completeness error). -/
def withheld_seq_le : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (w : W₁) (x : X₁)
      (G : Rho R₁.shape → Set (Rho R₂.shape)) (p₁ b₂ z₂ : ℝ≥0∞),
    prRho (H₁.withheld w x) ≤ p₁ → prRho H₂.Bad ≤ b₂ →
    (∀ ρ₁, ρ₁ ∉ H₁.withheld w x →
      ∀ c, H₂.Hid ((H₁.strat w x c).run ρ₁).2.2 ((H₁.strat w x c).run ρ₁).2.1 ⊆ G ρ₁) →
    (∀ ρ₁, ρ₁ ∉ H₁.withheld w x → prRho (G ρ₁) ≤ z₂) →
    prRho ((H₁.seq H₂).withheld w x) ≤ p₁ + (b₂ + z₂)

/-- "A function of the old implicit instance and of the oracles sent" is kept by composition. -/
def impBy_seq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (io₁ : E₁.Str → Orcs R₁.shape → E₂.Str) (io₂ : E₂.Str → Orcs R₂.shape → E₃.Str),
    R₁.ImpBy io₁ → R₂.ImpBy io₂ → (R₁.seq R₂).ImpBy (ioSeq io₁ io₂)

/-- States: under `R₁.ImpBy io`, the composed extractor is the one of Ior/Know.lean wherever the
first verifier does not reject. -/
def extSeqO_eq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (e₁ : E₁.Str → Orcs R₁.shape → W₂ → W₁)
      (e₂ : E₂.Str → Orcs R₂.shape → W₃ → W₂) (io : E₁.Str → Orcs R₁.shape → E₂.Str) (d : W₁),
    R₁.ImpBy io →
    ∀ (a : X₁ × E₁.Str) (τ : Tr (R₁.shape ++ R₂.shape)) (w : W₃),
      (R₁.out a.1 a.2 (Tr.fst τ)).isSome = true →
      Reduction.extSeq R₁.red R₂.red (fun a τ w => e₁ a.2 τ.read w)
          (fun b τ w => e₂ b.2 τ.read w) d a τ w =
        extSeqO e₁ e₂ io a.2 τ.read w

/-- Knowledge soundness of a composition, extractors that read oracles only, general form: ext is
any function that agrees with "the second's, then the first's". (not all hypotheses are named here:
see the statement below) -/
def know_seq_ext : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (on₁ : X₁ × E₁.Str → Prop) (on₂ : X₂ × E₂.Str → Prop)
      (RA : X₁ × E₁.Str → W₁ → Prop) (RB : X₂ × E₂.Str → W₂ → Prop) (RC : X₃ × E₃.Str → W₃ → Prop)
      (e₁ : E₁.Str → Orcs R₁.shape → W₂ → W₁) (e₂ : E₂.Str → Orcs R₂.shape → W₃ → W₂)
      (ext : E₁.Str → Orcs (R₁.shape ++ R₂.shape) → W₃ → W₁) (ε₁ : Err R₁.shape)
      (ε₂ : Err R₂.shape),
    R₁.red.Know on₁ RA RB (fun a τ w => e₁ a.2 τ.read w) ε₁ →
    R₂.red.Know on₂ RB RC (fun a τ w => e₂ a.2 τ.read w) ε₂ →
    (∀ a τ b, on₁ a → R₁.red.out a τ = some b → on₂ b) →
    (∀ y (τ₁ : Tr R₁.shape) (τ₂ : Tr R₂.shape) w,
      ext y (Tr.app τ₁ τ₂).read w = e₁ y τ₁.read (e₂ (R₁.imp y τ₁) τ₂.read w)) →
    (R₁.seq R₂).red.Know on₁ RA RC (fun a τ w => ext a.2 τ.read w) (Err.app ε₁ ε₂)

/-- The rule for chains, general form: as `good_seq`, with any extractor that agrees with "the
second's, then the first's". -/
def good_seq_ext : Prop :=
  ∀ (K X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (A : Rels K X₁ E₁ W₁)
      (B : Rels K X₂ E₂ W₂) (C : Rels K X₃ E₃ W₃) (e₁ : E₁.Str → Orcs R₁.shape → W₂ → W₁)
      (e₂ : E₂.Str → Orcs R₂.shape → W₃ → W₂) (ext : E₁.Str → Orcs (R₁.shape ++ R₂.shape) → W₃ → W₁)
      (P₁ : Nums K R₁) (P₂ : Nums K R₂),
    Good R₁ H₁ A B e₁ P₁ → Good R₂ H₂ B C e₂ P₂ →
    (∀ y (τ₁ : Tr R₁.shape) (τ₂ : Tr R₂.shape) w,
      ext y (Tr.app τ₁ τ₂).read w = e₁ y τ₁.read (e₂ (R₁.imp y τ₁) τ₂.read w)) →
    Good (R₁.seq R₂) (H₁.seq H₂) A C ext (P₁.seq P₂)

/-- The rule for chains. Under `R₁.ImpBy io`, from A to B, then from B to C, is from A to C: errors
in a row, probabilities added, the composed budget, the composed extractor. -/
def good_seq : Prop :=
  ∀ (K X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (A : Rels K X₁ E₁ W₁)
      (B : Rels K X₂ E₂ W₂) (C : Rels K X₃ E₃ W₃) (e₁ : E₁.Str → Orcs R₁.shape → W₂ → W₁)
      (e₂ : E₂.Str → Orcs R₂.shape → W₃ → W₂) (io : E₁.Str → Orcs R₁.shape → E₂.Str)
      (P₁ : Nums K R₁) (P₂ : Nums K R₂),
    Good R₁ H₁ A B e₁ P₁ → Good R₂ H₂ B C e₂ P₂ → R₁.ImpBy io →
    Good (R₁.seq R₂) (H₁.seq H₂) A C (extSeqO e₁ e₂ io) (P₁.seq P₂)

/-- The rule for chains when the first extractor decodes the input statement (it looks neither at
the oracles sent nor at the middle witness): so does the composed one. No premise of its own is
asked of the middle implicit instance (no `R₁.ImpBy io`, which `Spec.good_seq` asks), which may read
verifier messages (a fold). -/
def good_seq_dec : Prop :=
  ∀ (K X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (A : Rels K X₁ E₁ W₁)
      (B : Rels K X₂ E₂ W₂) (C : Rels K X₃ E₃ W₃) (d : E₁.Str → W₁)
      (e₂ : E₂.Str → Orcs R₂.shape → W₃ → W₂) (P₁ : Nums K R₁) (P₂ : Nums K R₂),
    Good R₁ H₁ A B (fun y _ _ => d y) P₁ → Good R₂ H₂ B C e₂ P₂ →
    Good (R₁.seq R₂) (H₁.seq H₂) A C (fun y _ _ => d y) (P₁.seq P₂)

/-- Consequence: a smaller honest input relation, a larger honest output relation; fewer statements
at the input, more at the output; a larger relaxed input relation, a smaller relaxed output
relation; the same cores; weaker numbers. -/
def good_conseq : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type)
      (H : R.Honest Wi Wo) (A A' : Rels K Xi Ei Wi) (B B' : Rels K Xo Eo Wo)
      (ext : Ei.Str → Orcs R.shape → Wo → Wi) (P P' : Nums K R),
    Good R H A B ext P → (∀ x y w, A'.rel x y w → A.rel x y w) →
    (∀ x y w, B.rel x y w → B'.rel x y w) → (∀ a, A'.on a → A.on a) → (∀ b, B.on b → B'.on b) →
    (∀ a w, A'.on a → A.relR a w → A'.relR a w) → (∀ b w, B'.relR b w → B.relR b w) →
    (∀ w, A'.core w = A.core w) → (∀ w, B'.core w = B.core w) → P.Le P' → Good R H A' B' ext P'

/-- What the bundle gives for the two probabilities, in the form of the parameter lists. -/
def good_prHid : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type)
      (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext : Ei.Str → Orcs R.shape → Wo → Wi) (P : Nums K R),
    Good R H A B ext P →
    ∀ x y w, A.rel x y w → prRho (H.Hid w x) ≤ P.pHid ∧ prRho (H.withheld w x) ≤ P.pBad + P.pHid

end Spec
end Iop
