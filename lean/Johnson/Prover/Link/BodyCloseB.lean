-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BodyCloseB.lean: THE INDUCTION's BASE PREMISE IS MET BY THE ONE INVARIANT.
Statements and proofs: at the last stage BodyInv (Johnson/Prover/Link/BodyInv.lean), over the plan's
letter PlanAll, yields the base case's accept on what bodyAll shows there. "Nothing is left
untested" is no part of the invariant: it stands beside it, as a premise by name.

  PlanAll      the public facts that go along: PlanFrom (FormStepPlan.lean) and SortsFrom
               (BodySorts.lean)
  hbase_both   the accept; and: if nothing is left untested in front, nothing is behind it
  hbase_at     THE ACCEPT ALONE: hbase of body_yes_of (BodyYes.lean) at no further clause
  hbase_left   the accept, with "nothing is left untested" in front and behind

By: base_at (BodyBase.lean) · fitB_at (BodySorts.lean) · the library's roundsFit_iff |
inRange_of_fit | inRange_noDigest · left_spent (TestEnd.lean).
Not shown here. That BodyInv is met anywhere. Nothing on soundness or any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Prover.Link.BodyInv
import Johnson.Prover.Link.BodySorts
import Johnson.Prover.Link.FormStepPlan
import Johnson.Prover.Link.TestEnd
import Johnson.Desc.K12.Law.RangeOfFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)

/-- The public facts that ride beside the invariant. -/
def PlanAll (p : P12) (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid)
    (K : Codes) : Prop :=
  PlanFrom p rest j cur l K ∧ SortsFrom l cur rest

/-- The accept; and what it keeps. -/
theorem hbase_both (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) (j : ℕ) (cur : Fmt.M1.Stage)
    (l : Laid) (o : ℕ) (t : T12) (P : PS) (col : ℕ → List UInt64)
    (h : BodyInv p K (PlanAll p) D [] j cur l o t P col) :
    ∃ t', (guardedProximityTestParts.base p j cur (l.map (·.1))).decide t
        ((lastOut p j cur o t P col (rowOf t) D).rs.map noDigest)
        (lastOut p j cur o t P col (rowOf t) D).gs = .ok t' ∧
      (ChainEnd.NothingLeft t.st → ChainEnd.NothingLeft t'.st) := by
  obtain ⟨⟨hP, hS⟩, hF, row, L, c, cl, m, star, a, I⟩ := h
  obtain ⟨⟨c', d₁, d₂, Lp⟩, -⟩ := hP
  have hfit := fitB_at p j cur l o t P col (rowOf t) D hF hS
  rw [Lp.cut] at hfit ⊢
  have hz : inRange [d₁, d₂] ((lastOut p j cur o t P col (rowOf t) D).rs.map noDigest) = true := by
    rw [H2K.First.inRange_noDigest]
    exact H2K.First.inRange_of_fit _ _ hfit
  have hR := (roundsFit_iff _ _).1 hfit
  obtain ⟨f1, f2⟩ : RoundFits d₁ ((lastOut p j cur o t P col (rowOf t) D).rs.getD 0 ⟨[], D o⟩) ∧
      RoundFits d₂ ((lastOut p j cur o t P col (rowOf t) D).rs.getD 1 ⟨[], D o⟩) := by
    cases hR with
    | cons a1 b1 =>
      cases b1 with
      | cons a2 _ => exact ⟨a1, a2⟩
  have hlen : (D o).elems.length = 1 := f1.elems.trans Lp.drawE
  obtain ⟨lam, hlam⟩ : ∃ lam, (D o).elems = [lam] := List.length_eq_one_iff.1 hlen
  have hx : ∀ x ∈ (D (o + 1)).poss, x < 2 ^ (sgOf cur).C.a := fun x hx' => by
    have := f2.below x hx'
    rw [Lp.logN] at this
    exact this
  have hcI := I.colIs
  subst hcI
  refine ⟨_, base_at p j cur d₁ d₂ o t P D row L c cl m star a lam I.form.st I.form.front I.form.h0
    I.form.g0 I.form.pow I.form.dSize I.form.fix I.holds hlam hx hz, ?_⟩
  exact left_spent t.st star

/-- **The premise hbase of body_yes_of (BodyYes.lean): the accept alone.** -/
theorem hbase_at (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) (j : ℕ) (cur : Fmt.M1.Stage)
    (l : Laid) (o : ℕ) (t : T12) (P : PS) (col : ℕ → List UInt64)
    (h : BodyInv p K (PlanAll p) D [] j cur l o t P col) :
    ∃ t', (guardedProximityTestParts.base p j cur (l.map (·.1))).decide t
        ((lastOut p j cur o t P col (rowOf t) D).rs.map noDigest)
        (lastOut p j cur o t P col (rowOf t) D).gs = .ok t' :=
  let ⟨t', a, _⟩ := hbase_both p K D j cur l o t P col h
  ⟨t', a⟩

/-- **The premise hbase of body_yes_of, with "nothing is left untested" in front and behind.** -/
theorem hbase_left (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) (j : ℕ) (cur : Fmt.M1.Stage)
    (l : Laid) (o : ℕ) (t : T12) (P : PS) (col : ℕ → List UInt64)
    (h : BodyInv p K (PlanAll p) D [] j cur l o t P col) (hl : ChainEnd.NothingLeft t.st) :
    ∃ t', (guardedProximityTestParts.base p j cur (l.map (·.1))).decide t
        ((lastOut p j cur o t P col (rowOf t) D).rs.map noDigest)
        (lastOut p j cur o t P col (rowOf t) D).gs = .ok t' ∧ ChainEnd.NothingLeft t'.st :=
  let ⟨t', a, b⟩ := hbase_both p K D j cur l o t P col h
  ⟨t', a, b hl⟩

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.hbase_both
#print axioms Johnson.Prover.Link.hbase_at
#print axioms Johnson.Prover.Link.hbase_left
