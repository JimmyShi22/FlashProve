-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3PlanOfOk.lean: the kind "lookup" (K3): WHAT THE STATED BLOCK's OWN TEST ON
THE PLAN GIVES AT THE PLACE's PARAMETERS: where the value of K3.theStated at an address passes its
test on the plan, the parameters that placeAt makes there pass the kind's public test P.planOk: SO
THE PLANNER RETURNS THERE (entries) AND THE PLANES' PACKING FITS (planesOk, and with it
Forest.planeCols). Statements and proofs. Ties of texts: no error term. NO SOUNDNESS IS CLAIMED.

Why. A list of public tests on the plan under the kind's laws asks, at each link, "the planner
returns" and "planeCols says yes". Neither wants a run or the goals' scope: both are conjuncts of
the test on the plan that the description's own planOk asks of every block.

OBJECT: the value B of K3.theStated claim readers X codes shape a (Johnson/Desc/First/Look/
  K3Stated.lean) and its field planOk.
Used by PlanZeroInScope.lean (Johnson/Desc/AtSeats/) · HeadAtOfPlan.lean
  (Johnson/Desc/First/Link/Law/) · K03LeftQ.lean (Johnson/Desc/First/Look/) and others.
LETTERS: claim, readers, X, codes, shape, a, B, i, d free.
Compiled with the whole library.


Main names:
  `pieceAt_inj`: a link's two lookups stand at two pieces.
  `stated_planOk`: B.planOk = true gives P.planOk at placeAt's value, at the address's own link and
    sort: through the equations of texts theStated_is, theWhole_is, theOwn_is (K3OwnIs.lean) and
    blockVia_planOk (Johnson/Top/H/K3Via/Blocks.lean).
  `planOk_parts`: what P.planOk says of the shape, the planner and the packing.
  `planeCols_of_planesOk`: planesOk h lm = true gives (Forest.planeCols h lm).toBool = true.
  `stated_entries`: SO: at every p with placeAt X i d = some p: p.entries.isSome = true, and there
    is the shape h that p makes with (Forest.planeCols h p.lm).toBool = true.

Limits. h and hOk are premises: that the description's test on the plan reaches this block is
another file's. The shape is the one that the kind's own parameters make.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3OwnIs
import Johnson.Top.H.K3Via.Blocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3
open OnBytes OnBytes.Model

/-- A link's two lookups stand at two pieces. -/
theorem pieceAt_inj (X : Verify.Public) (i : ℕ) {d d' : Bool}
    (h : pieceAt X i d = pieceAt X i d') : d = d' := by
  unfold pieceAt at h
  cases d <;> cases d' <;> first | rfl | (split at h <;> simp at h)

/-- **The stated block's test on the plan gives the kind's public test at placeAt's value.** -/
theorem stated_planOk {Cl : Type} (claim : Aff → Cl) (readers : Nat → Option (Readers First.S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place)
    (B : Block First.S Cl) (h : theStated claim readers X codes shape a = some B)
    (hOk : B.planOk = true) :
    ∃ i d p laid, a.link = some i ∧ a.piece = pieceAt X i d ∧
      First.Look.placeAt X i d = some p ∧
      p.planOk laid ([] : List (First.Look.Guest First.S Cl)) = true := by
  obtain ⟨B₁, hB₁, -, -, -, e4⟩ := theStated_is claim readers X codes shape a B h
  obtain ⟨b, hb, hW⟩ := theWhole_is claim true X codes shape a B₁ hB₁
  obtain ⟨i, d, p, sent, laid, hi, hpc, hP, -, -, -, -, -, r4⟩ :=
    theOwn_is claim true X codes shape a b hb
  have hbk : b.planOk = true := by
    rcases hW with ⟨-, rfl⟩ | ⟨f, -, rfl⟩
    · exact e4.symm.trans hOk
    · have h6 : (b.planOk &&
          (roundlessBlock (b.name ++ ": behind it") 1 a.link a.piece f).planOk) = true :=
        e4.symm.trans hOk
      exact (Eq.mp (Bool.and_eq_true _ _) h6).1
  have h1 : planOk p laid ([] : List (First.Look.Guest First.S Cl)) = true :=
    (Law.blockVia_planOk (r4 hbk)).1
  unfold planOk at h1
  exact ⟨i, d, p, laid, hi, hpc, hP, (Eq.mp (Bool.and_eq_true _ _) h1).1⟩

/-- What the kind's public test says of the shape, the planner and the packing. -/
theorem planOk_parts {S Cl : Type} {p : First.Look.P} {laid : Array Nat}
    {guests : List (First.Look.Guest S Cl)} (h : p.planOk laid guests = true) :
    ∃ hs, p.shape = some hs ∧ p.entries.isSome = true ∧ First.Look.planesOk hs p.lm = true := by
  unfold First.Look.P.planOk at h
  cases e : p.shape with
  | none =>
    rw [e] at h
    cases h
  | some hs =>
    rw [e] at h
    simp only [Bool.and_eq_true] at h
    exact ⟨hs, rfl, h.1.1.1.1.1, h.1.1.1.1.2⟩

/-- The packing's test gives the yes of Forest.planeCols. -/
theorem planeCols_of_planesOk {hs : Forest.Shape} {lm : ℕ}
    (h : First.Look.planesOk hs lm = true) : (Forest.planeCols hs lm).toBool = true := by
  unfold First.Look.planesOk at h
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  have hc : (decide (lm < 5) || decide (lm > hs.kT + 5)) = false := by
    rw [Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
    exact ⟨by omega, by omega⟩
  unfold Forest.planeCols
  rw [hc]
  rfl

/-- **SO THE PLANNER RETURNS AND THE PACKING FITS AT THE PLACE's PARAMETERS.** -/
theorem stated_entries {Cl : Type} (claim : Aff → Cl) (readers : Nat → Option (Readers First.S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place)
    (B : Block First.S Cl) (h : theStated claim readers X codes shape a = some B)
    (hOk : B.planOk = true) (i : ℕ) (d : Bool) (hl : a.link = some i)
    (hpc : a.piece = pieceAt X i d) (p : First.Look.P) (hp : First.Look.placeAt X i d = some p) :
    p.entries.isSome = true ∧
      ∃ hs, p.shape = some hs ∧ (Forest.planeCols hs p.lm).toBool = true := by
  obtain ⟨j, d', p', laid, hj, hpj, hP, hk⟩ := stated_planOk claim readers X codes shape a B h hOk
  obtain rfl : i = j := Option.some.inj (hl.symm.trans hj)
  obtain rfl : d = d' := pieceAt_inj X i (hpc.symm.trans hpj)
  obtain rfl : p = p' := Option.some.inj (hp.symm.trans hP)
  obtain ⟨hs, e1, e2, e3⟩ := planOk_parts hk
  exact ⟨e2, hs, e1, planeCols_of_planesOk e3⟩

end VerifiableInference.Desc.K3

#print axioms VerifiableInference.Desc.K3.stated_planOk
#print axioms VerifiableInference.Desc.K3.planeCols_of_planesOk
#print axioms VerifiableInference.Desc.K3.stated_entries
