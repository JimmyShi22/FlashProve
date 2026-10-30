-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cond/FitOfBatch.lean: the compiler's data and side conditions of a batch IOP that is a chain of
links.

This is book-keeping for the compiler, as in Cond/FitOfSub.lean, for batch IOPs (`BIOP`,
Ior/Batch.lean): no security property is stated here.
Definitions, statements and proofs. Generic: no protocol occurs.
Cond/FitOfSub.lean has the bundle of a whole batch IOP (`BIOP.SubData`, `BIOP.SubFit`).
Ior/BatchSeqZk.lean builds batch IOPs as chains: a link (an IOR with an annotation of its shape),
then a batch IOP (`seqB`); at the end an IOP in every slot (`localB`, `localH`); in between IORs
that the shared part of the prover runs alone (`sharedH`). Here each link brings its own bundle, and
they compose.

Main names:
  `IOR.LinkData R A H lam`: the data of a link R with the annotation A and the honest side H: the
    oracles are strings (`pt`); numberings of the positions of the shared and of a slot's component
    of each round; a sampler for each verifier message; numberings of the two kinds of coins; a
    decision procedure for the public bad set (`H.Bad`); the four numbers of openings.
  The format goes by phases (`FPhase`, Iop/BatchFmt.lean). The compiled scheme carries rounds of the
  kinds local+ shared* local*, and what is asked of a round depends on the phase in which it is. So
  the conditions have the phase as a parameter:
  `IOR.LinkFit D κ₀ ph`, `BIOP.SubFitAt D κ₀ ph`: the samplers obey their law (`Shape.Draws.Good`);
    the numbers of openings are upper bounds; the rounds have the format from the phase ph on.
  `subFitAt_seqB`: the rule.
  `blocks_seqB`: the blocks of all rounds add up; the largest number of blocks of a round is the
    larger one.

`Iop.IOR.LinkData.seqB`, `Iop.IOR.SubData.localB`, `Iop.IOR.SubData.sharedL` are ordinary
definitions, which Lean COMPILES.

Limits: this file says nothing on security. In `IOR.SubData.sharedL` the decision procedure
`D.decBad` of the IOR's own bundle is not used: `sharedH` of Ior/BatchSeqZk.lean has an empty local
bad set (decided here: "no") and puts the IOR's public bad set into its shared stop, a Boolean
function that it forms itself with a classical test of membership.

Terms: lean/GLOSSARY.md.
-/
import Cond.FitOfSub
import Ior.BatchSeqZk

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR
variable {X X' : Type} {E0 Ej Eo : ExtSpec} {W0 Wj W0' Wj' : Type} {lam : ℕ}

/-- The data of a link. -/
structure LinkData (R : IOR X (E0.prod Ej) X' Eo) (A : RoundSplits R.shape)
    (H : R.HonestB A W0 Wj W0' Wj') (lam : ℕ) where
  pt     : R.shape.IsPoint
  pos    : R.shape.NumPosB A pt
  dr     : R.shape.Draws lam
  coin0  : Num H.Coin0
  coin   : Num H.Coin
  decBad : ∀ l, Decidable (l ∈ H.Bad)
  ob     : OpenB

def LinkData.tot {R : IOR X (E0.prod Ej) X' Eo} {A : RoundSplits R.shape}
    {H : R.HonestB A W0 Wj W0' Wj'} (D : R.LinkData A H lam) : ℕ :=
  Shape.Draws.totB _ D.dr
def LinkData.maxB {R : IOR X (E0.prod Ej) X' Eo} {A : RoundSplits R.shape}
    {H : R.HonestB A W0 Wj W0' Wj'} (D : R.LinkData A H lam) : ℕ :=
  Shape.Draws.maxB _ D.dr

/-- The conditions on a link, from the phase ph on. -/
structure LinkFit {R : IOR X (E0.prod Ej) X' Eo} {A : RoundSplits R.shape} {H : R.HonestB A W0 Wj W0' Wj'}
    (D : R.LinkData A H lam) (κ₀ : ℝ≥0∞) (ph : FPhase) : Prop where
  good  : Shape.Draws.Good κ₀ _ D.dr
  opens : R.OpensLe D.ob
  fmt   : RoundSplits.FmtFrom R.shape A ph

end IOR

namespace BIOP
variable {X : Type} {E0 Ej : ExtSpec} {W0 Wj : Type} {lam : ℕ}

/-- The conditions on a batch IOP, from the phase ph on. -/
structure SubFitAt {Q : BIOP X (E0.prod Ej)} {H : Q.Honest W0 Wj} (D : Q.SubData H lam)
    (κ₀ : ℝ≥0∞) (ph : FPhase) : Prop where
  good  : Shape.Draws.Good κ₀ _ D.dr
  opens : Q.ior.OpensLe D.ob
  fmt   : RoundSplits.FmtFrom Q.ior.shape Q.ann ph

end BIOP

section Seq
variable {X X' : Type} {E0 Ej E0' Ej' : ExtSpec} {W0 Wj W0' Wj' : Type} {lam : ℕ}

/-- The data of "a link, then a batch IOP". -/
def IOR.LinkData.seqB {R : IOR X (E0.prod Ej) X' (E0'.prod Ej')} {A : RoundSplits R.shape}
    {Q : BIOP X' (E0'.prod Ej')} {HR : R.HonestB A W0 Wj W0' Wj'} {HQ : Q.Honest W0' Wj'}
    (DR : R.LinkData A HR lam) (DQ : Q.SubData HQ lam) :
    (seqB R A Q).SubData (HR.seqB HQ) lam where
  pt := Blocks.pointApp DR.pt DQ.pt
  pos := Blocks.numPosBApp DR.pos DQ.pos
  dr := Shape.Draws.app DR.dr DQ.dr
  coin0 := Num.prod DR.coin0 DQ.coin0
  coin := Num.prod DR.coin DQ.coin
  decBad := fun l =>
    letI := DR.decBad (RhoLo.fstA A Q.ann l)
    letI := DQ.decBad (RhoLo.sndA A Q.ann l)
    inferInstanceAs (Decidable (RhoLo.fstA A Q.ann l ∈ HR.Bad ∨ RhoLo.sndA A Q.ann l ∈ HQ.Bad))
  ob := DR.ob.seq DQ.ob

end Seq

section Local
variable {X : Type} {E0 Ej : ExtSpec} {Wi W0 Wj : Type} {lam : ℕ}

/-- The data of an IOP in every slot. -/
def IOR.SubData.localB {B : IOR X (E0.prod Ej) Unit extNone} {H : B.Honest Wi Unit}
    (D : B.SubData H lam) (mk : W0 → Wj → Wi) :
    (localB B).SubData (localH H mk) lam where
  pt := D.pt
  pos := Shape.NumPosB.ofLocal B.shape D.pt D.pos
  dr := D.dr
  coin0 := Num.ofFinEnum Unit
  coin := D.coin
  decBad := fun l => D.decBad (RhoLo.all B.shape l)
  ob := D.ob

end Local

section Shared
variable {X X' : Type} {E0 Ej Eo : ExtSpec} {Wi Wo W0 Wj W0' Wj' : Type} {lam : ℕ}

/-- The data of an IOR run by the shared part alone, as a link. -/
def IOR.SubData.sharedL {R : IOR X (E0.prod Ej) X' Eo} {H : R.Honest Wi Wo} (D : R.SubData H lam)
    (s0 : W0 → H.Coin → Strat R.shape W0') (nx : X → Wj → X' × Wj') :
    R.LinkData (RoundSplits.const (RAnn.ofShared .sh) R.shape) (sharedH R H.Coin s0 nx H.Bad) lam where
  pt := D.pt
  pos := Blocks.numPosBShared .sh R.shape D.pt D.pos
  dr := D.dr
  coin0 := D.coin
  coin := Num.ofFinEnum Unit
  decBad := fun _ => isFalse fun h => h
  ob := D.ob

end Shared

namespace Spec
open IOR

/-- States that the conditions of Cond/FitOfSub.lean are those from the phase "after a local round"
(`.loc`) on. -/
def subFit_iff : Prop :=
  ∀ (X : Type) (E0 Ej : ExtSpec) (W0 Wj : Type) (lam : ℕ) (Q : BIOP X (E0.prod Ej))
      (H : Q.Honest W0 Wj) (D : Q.SubData H lam) (κ₀ : ℝ≥0∞),
    BIOP.SubFit D κ₀ ↔ BIOP.SubFitAt D κ₀ .loc

/-- States the rule: the link from ph on and the batch IOP from the phase after the link's rounds on
give `DR.seqB DQ` from ph on. -/
def subFitAt_seqB : Prop :=
  ∀ (X X' : Type) (E0 Ej E0' Ej' : ExtSpec) (W0 Wj W0' Wj' : Type) (lam : ℕ)
      (R : IOR X (E0.prod Ej) X' (E0'.prod Ej')) (A : RoundSplits R.shape) (Q : BIOP X' (E0'.prod Ej'))
      (HR : R.HonestB A W0 Wj W0' Wj') (HQ : Q.Honest W0' Wj') (DR : R.LinkData A HR lam)
      (DQ : Q.SubData HQ lam) (κ₀ : ℝ≥0∞) (ph : FPhase),
    LinkFit DR κ₀ ph → BIOP.SubFitAt DQ κ₀ (RoundSplits.phaseAfter R.shape A ph) →
    BIOP.SubFitAt (DR.seqB DQ) κ₀ ph

def blocks_seqB : Prop :=
  ∀ (X X' : Type) (E0 Ej E0' Ej' : ExtSpec) (W0 Wj W0' Wj' : Type) (lam : ℕ)
      (R : IOR X (E0.prod Ej) X' (E0'.prod Ej')) (A : RoundSplits R.shape)
      (Q : BIOP X' (E0'.prod Ej')) (HR : R.HonestB A W0 Wj W0' Wj') (HQ : Q.Honest W0' Wj')
      (DR : R.LinkData A HR lam) (DQ : Q.SubData HQ lam),
    (DR.seqB DQ).tot = DR.tot + DQ.tot ∧ (DR.seqB DQ).maxB = max DR.maxB DQ.maxB

/-- States the conditions of an IOP in every slot, from every phase on, from `SubFit` of the IOP. -/
def subFitAt_localB : Prop :=
  ∀ (X : Type) (E0 Ej : ExtSpec) (Wi W0 Wj : Type) (lam : ℕ) (B : IOR X (E0.prod Ej) Unit extNone)
      (H : B.Honest Wi Unit) (D : B.SubData H lam) (mk : W0 → Wj → Wi) (κ₀ : ℝ≥0∞) (ph : FPhase),
    SubFit D κ₀ → BIOP.SubFitAt (D.localB mk) κ₀ ph

/-- States the conditions of rounds of the shared part alone, from the phases "after a local round"
(`.loc`: before any shared round) and "after a shared round" (`.shr`) on, from `SubFit` of the IOR.
-/
def linkFit_sharedL : Prop :=
  ∀ (X X' : Type) (E0 Ej Eo : ExtSpec) (Wi Wo W0 Wj W0' Wj' : Type) (lam : ℕ)
      (R : IOR X (E0.prod Ej) X' Eo) (H : R.Honest Wi Wo) (D : R.SubData H lam)
      (s0 : W0 → H.Coin → Strat R.shape W0') (nx : X → Wj → X' × Wj') (κ₀ : ℝ≥0∞) (ph : FPhase),
    ph = .loc ∨ ph = .shr → SubFit D κ₀ → LinkFit (D.sharedL s0 nx) κ₀ ph

/-- States that after shared rounds the phase is "after a shared round"; without a round it is what
it was. -/
def phaseAfter_shared : Prop :=
  ∀ (f : ∀ r : Round, RAnn r), (∀ r, (f r).kind = .sh) →
    ∀ (s : Shape) (ph : FPhase), RoundSplits.phaseAfter s (RoundSplits.const f s) ph = if s = [] then ph else .shr

end Spec

theorem subFit_iff : Spec.subFit_iff := fun _ _ _ _ _ _ _ _ _ _ =>
  ⟨fun h => ⟨h.good, h.opens, h.fmt⟩, fun h => ⟨h.good, h.opens, h.fmt⟩⟩

theorem subFitAt_seqB : Spec.subFitAt_seqB := by
  intro X X' E0 Ej E0' Ej' W0 Wj W0' Wj' lam R A Q HR HQ DR DQ κ₀ ph h₁ h₂
  exact ⟨Blocks.good_app DR.dr DQ.dr h₁.good h₂.good,
    opensLe_seq _ _ _ _ _ _ R Q.ior DR.ob DQ.ob h₁.opens h₂.opens,
    fmtFrom_app R.shape Q.ior.shape A Q.ann ph h₁.fmt h₂.fmt⟩

theorem blocks_seqB : Spec.blocks_seqB := by
  intro X X' E0 Ej E0' Ej' W0 Wj W0' Wj' lam R A Q HR HQ DR DQ
  exact ⟨Shape.Draws.totB_app DR.dr DQ.dr, Shape.Draws.maxB_app DR.dr DQ.dr⟩

theorem subFitAt_localB : Spec.subFitAt_localB := by
  intro X E0 Ej Wi W0 Wj lam B H D mk κ₀ ph h
  exact ⟨h.good, h.opens, RoundSplits.fmtFrom_allLocal B.shape ph⟩

/-- Shared rounds in which only the shared part speaks have the format from the phase "after a
shared round" on. -/
theorem fmtFrom_shared_shr : ∀ s : Shape, RoundSplits.FmtFrom s (RoundSplits.const (RAnn.ofShared .sh) s) .shr
  | [] => trivial
  | r :: s => ⟨RAnn.noSlot_ofShared .sh r, fmtFrom_shared_shr s⟩

theorem fmtFrom_shared_loc : ∀ s : Shape, RoundSplits.FmtFrom s (RoundSplits.const (RAnn.ofShared .sh) s) .loc
  | [] => trivial
  | _ :: s => fmtFrom_shared_shr s

theorem linkFit_sharedL : Spec.linkFit_sharedL := by
  intro X X' E0 Ej Eo Wi Wo W0 Wj W0' Wj' lam R H D s0 nx κ₀ ph hph h
  refine ⟨h.good, h.opens, ?_⟩
  rcases hph with rfl | rfl
  · exact fmtFrom_shared_loc R.shape
  · exact fmtFrom_shared_shr R.shape

theorem phaseAfter_shared : Spec.phaseAfter_shared := by
  intro f hf s
  induction s with
  | nil => exact fun ph => rfl
  | cons r s ih =>
    intro ph
    have e : RoundSplits.phaseAfter (r :: s) (RoundSplits.const f (r :: s)) ph = RoundSplits.phaseAfter s (RoundSplits.const f s) (match (f r).kind with
                                  | .lo => ph.afterLo
                                  | .sh => .shr) := rfl
    rw [e, hf r, ih, if_neg (List.cons_ne_nil r s)]
    split <;> rfl

end Iop
