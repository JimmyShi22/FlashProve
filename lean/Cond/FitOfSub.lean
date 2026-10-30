-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cond/FitOfSub.lean: what the compiler needs of one sub-protocol, as a bundle that composes.

This is book-keeping for the compiler, which turns an interactive oracle protocol into a
non-interactive argument: no security property is stated here.
Definitions, statements and proofs. Generic: no protocol occurs.
The compiler (Compile/Batch, through the generic wires of Iop/BatchWireDraw.lean) needs, beside the
security properties of an IOP, data on its format and side conditions on these data. The IOPs of the
protocols under Cb/ are long chains of IORs. Here each link of a
chain brings its own data and conditions, and they compose.

Main names:
  `IOR.SubData R H lam`: for an IOR R with the honest side H: the oracles are strings (`pt`); a
    numbering of the positions of each round (`pos`); a block sampler for each verifier message
    (`dr`); a numbering of the prover's coins (`coin`); decision procedures for the public and for
    the hidden withheld set (`decBad`, `decHid`); the four numbers of openings (`ob`:
    Cond/FitOfOpens.lean).
  `IOR.SubData.seq`: the hidden withheld set of a composition asks "for some coins of the first
    prover": it is decided by going through the coins.
  `IOR.SubFit D κ₀`: the conditions: every sampler obeys its law with κ₀^(number of its blocks); the
    numbers of openings are upper bounds (`R.OpensLe D.ob`).
  `subFit_seq`: the rule. `blocks_seq`: the blocks of all rounds add up, the largest number of
    blocks of a round is the larger one.
  `BIOP.SubData`, `BIOP.SubFit`: the same, without `decHid`, for a batch IOP whose slots have
    external oracles of their own (Ior/Batch.lean): positions of the shared component and of a
    slot's component numbered apart, two kinds of coins; and the format of its rounds (`fmt`).
  `RoundSplits.phaseAfter`, `fmtFrom_app`: the format of two annotated shapes in a row, from the formats of
    the two. `fmt_online`: local rounds, at least one, in which only the slots speak, and then
    rounds that have the format from the phase `.loc` (`FPhase`, Iop/BatchFmt.lean) on, have the
    format (`RoundSplits.Fmt`).

Why: these bundles stand beside the bundle of security properties (`IOR.Good`, Ior/Chain.lean), not
in it: that one is a proposition, `SubData` is data.

Num.prod and SubData.seq are ordinary definitions, which Lean COMPILES (it refuses to compile a
definition whose value, after types and proofs are erased, depends on a noncomputable constant,
unless the definition is marked noncomputable). (#print axioms cannot show anything here: it also
counts the proofs inside these constructions and the types, and IOR.seq itself forms unions of
finite sets with classical equality tests.)

Limits: this file says nothing on security. For a batch IOP that is a chain of links:
Cond/FitOfBatch.lean.

Terms: lean/GLOSSARY.md.

-/
import Cond.FitOfOpens
import Blocks.Numbering
import Blocks.Batch.Numbering
import Blocks.Batch.Fmt
import Blocks.Draws
import Blocks.DrawsSum

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-- A numbering of pairs: (a, b) has the number  number of b + (number of values of b) · number of a
(Mathlib's finProdFinEquiv). -/
def Num.prod {α β : Type} [Fintype α] [Fintype β] (a : Num α) (b : Num β) : Num (α × β) :=
  ((Equiv.prodCongr a b).trans finProdFinEquiv).trans (finCongr (Fintype.card_prod α β).symm)

/-! ## 1. An IOR with its honest side -/

namespace IOR
variable {X₁ X₂ X₃ Xi Xo : Type} {E₁ E₂ E₃ Ei Eo : ExtSpec} {W₁ W₂ W₃ Wi Wo : Type} {lam : ℕ}

/-- The data of an IOR with its honest side. -/
structure SubData (R : IOR Xi Ei Xo Eo) (H : R.Honest Wi Wo) (lam : ℕ) where
  pt     : R.shape.IsPoint
  pos    : R.shape.NumPos pt
  dr     : R.shape.Draws lam
  coin   : Num H.Coin
  decBad : ∀ ρ, Decidable (ρ ∈ H.Bad)
  decHid : ∀ w x ρ, Decidable (ρ ∈ H.Hid w x)
  ob     : OpenB

/-- The blocks of all rounds; `maxB`: the largest number of blocks of a round. -/
def SubData.tot {R : IOR Xi Ei Xo Eo} {H : R.Honest Wi Wo} (D : R.SubData H lam) : ℕ :=
  Shape.Draws.totB _ D.dr
def SubData.maxB {R : IOR Xi Ei Xo Eo} {H : R.Honest Wi Wo} (D : R.SubData H lam) : ℕ :=
  Shape.Draws.maxB _ D.dr

/-- The data of a composition. -/
def SubData.seq {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃} {H₁ : R₁.Honest W₁ W₂}
    {H₂ : R₂.Honest W₂ W₃} (D₁ : R₁.SubData H₁ lam) (D₂ : R₂.SubData H₂ lam) :
    (R₁.seq R₂).SubData (H₁.seq H₂) lam where
  pt := Blocks.pointApp D₁.pt D₂.pt
  pos := Blocks.numPosApp D₁.pos D₂.pos
  dr := Shape.Draws.app D₁.dr D₂.dr
  coin := Num.prod D₁.coin D₂.coin
  decBad := fun ρ =>
    letI := D₁.decBad (Rho.fst ρ)
    letI := D₂.decBad (Rho.snd (s := R₁.shape) ρ)
    inferInstanceAs (Decidable (Rho.fst ρ ∈ H₁.Bad ∨ Rho.snd (s := R₁.shape) ρ ∈ H₂.Bad))
  decHid := fun w x ρ =>
    letI := D₁.decHid w x (Rho.fst ρ)
    letI := D₁.decBad (Rho.fst ρ)
    letI : DecidablePred fun c : H₁.Coin =>
        Rho.snd (s := R₁.shape) ρ ∈
            H₂.Hid ((H₁.strat w x c).run (Rho.fst ρ)).2.2 ((H₁.strat w x c).run (Rho.fst ρ)).2.1 :=
      fun _ => D₂.decHid _ _ _
    inferInstanceAs (Decidable
      (Rho.fst ρ ∈ H₁.Hid w x ∨
        (Rho.fst ρ ∉ H₁.Bad ∧
          ∃ c : H₁.Coin, Rho.snd (s := R₁.shape) ρ ∈
            H₂.Hid ((H₁.strat w x c).run (Rho.fst ρ)).2.2 ((H₁.strat w x c).run (Rho.fst ρ)).2.1)))
  ob := D₁.ob.seq D₂.ob

/-- The conditions. -/
structure SubFit {R : IOR Xi Ei Xo Eo} {H : R.Honest Wi Wo} (D : R.SubData H lam) (κ₀ : ℝ≥0∞) :
    Prop where
  good  : Shape.Draws.Good κ₀ _ D.dr
  opens : R.OpensLe D.ob

end IOR

/-! ## 2. A batch IOP whose slots have external oracles of their own -/

namespace BIOP
variable {X : Type} {E0 Ej : ExtSpec} {W0 Wj : Type} {lam : ℕ}

/-- The data of a batch IOP with its honest side. -/
structure SubData (Q : BIOP X (E0.prod Ej)) (H : Q.Honest W0 Wj) (lam : ℕ) where
  pt     : Q.ior.shape.IsPoint
  pos    : Q.ior.shape.NumPosB Q.ann pt
  dr     : Q.ior.shape.Draws lam
  coin0  : Num H.Coin0
  coin   : Num H.Coin
  decBad : ∀ l, Decidable (l ∈ H.Bad)
  ob     : OpenB

def SubData.tot {Q : BIOP X (E0.prod Ej)} {H : Q.Honest W0 Wj} (D : Q.SubData H lam) : ℕ :=
  Shape.Draws.totB _ D.dr
def SubData.maxB {Q : BIOP X (E0.prod Ej)} {H : Q.Honest W0 Wj} (D : Q.SubData H lam) : ℕ :=
  Shape.Draws.maxB _ D.dr

/-- The conditions. The format is asked from the phase "after a local round" (`.loc`) on: the batch
IOP comes after the local rounds of a preamble. -/
structure SubFit {Q : BIOP X (E0.prod Ej)} {H : Q.Honest W0 Wj} (D : Q.SubData H lam) (κ₀ : ℝ≥0∞) :
    Prop where
  good  : Shape.Draws.Good κ₀ _ D.dr
  opens : Q.ior.OpensLe D.ob
  fmt   : RoundSplits.FmtFrom Q.ior.shape Q.ann .loc

end BIOP

/-! ## 3. The format of two annotated shapes in a row -/

/-- The phase after the rounds of s, begun in the phase ph. -/
def RoundSplits.phaseAfter : (s : Shape) → RoundSplits s → FPhase → FPhase
  | [], _, ph => ph
  | _ :: s, (a, A), ph => RoundSplits.phaseAfter s A (match a.kind with
             | .lo => ph.afterLo
             | .sh => .shr)

namespace Spec
open IOR

/-- States the rule: from `SubFit D₁ κ₀` and `SubFit D₂ κ₀`, `SubFit (D₁.seq D₂) κ₀`. -/
def subFit_seq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (W₁ W₂ W₃ : Type) (lam : ℕ) (R₁ : IOR X₁ E₁ X₂ E₂)
      (R₂ : IOR X₂ E₂ X₃ E₃) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (D₁ : R₁.SubData H₁ lam)
      (D₂ : R₂.SubData H₂ lam) (κ₀ : ℝ≥0∞),
    SubFit D₁ κ₀ → SubFit D₂ κ₀ → SubFit (D₁.seq D₂) κ₀

/-- States the blocks of a composition: `tot` adds up, `maxB` is the larger one. -/
def blocks_seq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (W₁ W₂ W₃ : Type) (lam : ℕ) (R₁ : IOR X₁ E₁ X₂ E₂)
      (R₂ : IOR X₂ E₂ X₃ E₃) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃)
      (D₁ : R₁.SubData H₁ lam) (D₂ : R₂.SubData H₂ lam),
    (D₁.seq D₂).tot = D₁.tot + D₂.tot ∧ (D₁.seq D₂).maxB = max D₁.maxB D₂.maxB

/-- States the format of two annotated shapes in a row, from the formats of the two: the first from
the phase ph on, the second from the phase after the first's rounds on. -/
def fmtFrom_app : Prop :=
  ∀ (s t : Shape) (A : RoundSplits s) (B : RoundSplits t) (ph : FPhase), RoundSplits.FmtFrom s A ph →
    RoundSplits.FmtFrom t B (RoundSplits.phaseAfter s A ph) → RoundSplits.FmtFrom (s ++ t) (RoundSplits.app A B) ph

/-- States that these have the format: local rounds in which only the slots speak, at least one, and
then rounds that have the format from the phase "after a local round" (`.loc`) on. -/
def fmt_online : Prop :=
  ∀ (s t : Shape) (B : RoundSplits t), s ≠ [] → RoundSplits.FmtFrom t B .loc → (RoundSplits.app (RoundSplits.allLocal s) B).Fmt

end Spec

theorem subFit_seq : Spec.subFit_seq := by
  intro X₁ X₂ X₃ E₁ E₂ E₃ W₁ W₂ W₃ lam R₁ R₂ H₁ H₂ D₁ D₂ κ₀ h₁ h₂
  exact ⟨Blocks.good_app D₁.dr D₂.dr h₁.good h₂.good,
    opensLe_seq _ _ _ _ _ _ R₁ R₂ D₁.ob D₂.ob h₁.opens h₂.opens⟩

theorem blocks_seq : Spec.blocks_seq := by
  intro X₁ X₂ X₃ E₁ E₂ E₃ W₁ W₂ W₃ lam R₁ R₂ H₁ H₂ D₁ D₂
  exact ⟨Shape.Draws.totB_app D₁.dr D₂.dr, Shape.Draws.maxB_app D₁.dr D₂.dr⟩

theorem fmtFrom_app : Spec.fmtFrom_app := by
  intro s
  induction s with
  | nil => exact fun t A B ph _ h => h
  | cons r s ih =>
    rintro t ⟨a, A⟩ B ph h h'
    obtain ⟨k, M0, Mj, sp, P0, Pj, pl0, plj, pl, own⟩ := a
    cases k
    · cases ph
      · exact h.elim
      · exact ih t A B _ h h'
      · exact ⟨h.1, ih t A B _ h.2 h'⟩
      · exact h.elim
    · exact ⟨h.1, ih t A B _ h.2 h'⟩

theorem fmt_online : Spec.fmt_online := by
  intro s t B hs h
  cases s with
  | nil => exact absurd rfl hs
  | cons r s => exact RoundSplits.fmtFrom_app_lo r s .first h

end Iop
