-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05PlanOfPublic.lean: KIND K5: THE SEVEN FACTS ON THE PLAN THAT THE KIND's LAW AT THE TABLE OF JOINTS ASKS (K5Plan, Johnson/Desc/First/Att/K05T2.lean) AT THE PUBLIC RECORD's OWN NUMBERS, from
PlanIs Wv (every stored attention plan is the planner's return but for one field), "attention is covered" and the two lookups of the record.
  `place_calls`: what lookAt hands at an attention link for the lookup on the calls: its ledger starts at the plan's base's next slot; its number of slots is the plan's; its link is the link.
  `place_digits`: for the lookup on the digits: where the digits' scalars fit, THERE IS a place; its first slot is the plan's number of slots less these scalars; its shape's record is the plan's f9.
  `planIs_tiles`, `planIs_next0`: plan_tiles (Johnson/Desc/First/Att/K05PlanTiles.lean) and the library's planA_next0 at a stored plan.
  `k5Plan_of_public`: **K5Plan at own := a.own (which is (parO W m a before).own by the make) · pC | pD := the two places' parameters · hS := a.seam.tl.f9 · first := Forest.elems a.fs · kr := the kind's slots and the digits' scalars · nsPlan := a.ns.**
    ONE PREMISE IS LEFT: hsh: the digits' parameters fix the plan's record f9 as their shape (P.shape: other files' to show: the twin, at the digits, of guard_theorems' first clause).
Limits: facts on public data. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.K05PlanTiles
import Johnson.Desc.First.Att.K05T2
import Johnson.Desc.First.Att.GuardPublic
import OnBytes.Tie.Pv.Lookup.Ends.FoNext0

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look (lookAt digitsNext)

section
variable {W : Verify.Public} {g : ℕ} {a : Attention.Plan}

theorem odd_facts (h4 : W.p4 = true) : 2 * g + 1 ≠ (if W.p4 then 2 else 1) * W.NGr ∧ (2 * g + 1) % (if W.p4 then 2 else 1) ≠ 0 ∧
    (2 * g + 1) / (if W.p4 then 2 else 1) = g := by
  rw [h4]
  simp only [if_true]
  omega

theorem place_calls (h4 : W.p4 = true) (ha : W.A[g]? = some a) {x : Look.Place} (hx : lookAt W (2 * g + 1) false = some x) :
    x.F.next = a.seam.Fp.next ∧ x.ns = a.ns ∧ x.link = 2 * g + 1 ∧ x.fs = a.fs := by
  obtain ⟨hn, h0, eg⟩ := odd_facts (W := W) (g := g) h4
  unfold lookAt at hx
  dsimp only at hx
  rw [if_neg (by simpa using hn), if_neg (by simpa using h0), eg, ha] at hx
  simp at hx
  subst hx
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem place_digits (h4 : W.p4 = true) (ha : W.A[g]? = some a) (hfit : Forest.elems a.seam.tl.f9 ≤ a.ns) :
    ∃ xd : Look.Place, lookAt W (2 * g + 1) true = some xd ∧ xd.F.next = a.ns - Forest.elems a.seam.tl.f9 ∧ xd.link = 2 * g + 1 ∧
      xd.fs = a.seam.tl.f9 ∧ xd.ns = a.ns := by
  obtain ⟨hn, h0, eg⟩ := odd_facts (W := W) (g := g) h4
  unfold lookAt
  dsimp only
  rw [if_neg (by simpa using hn), if_neg (by simpa using h0), eg, ha]
  have hd : digitsNext a.ns 0 (Forest.elems a.seam.tl.f9) = some (a.ns - 0 - Forest.elems a.seam.tl.f9) := by
    unfold digitsNext
    rw [if_pos (by omega)]
  simp only [Option.bind_some, if_true, hd, Option.map_some]
  exact ⟨_, rfl, by simp, rfl, rfl, rfl⟩

theorem planIs_tiles (hP : PlanIs W) (ha : W.A[g]? = some a) :
    a.ns = Forest.elems a.fs + slotsOf (script a.own) + Forest.elems a.seam.tl.f9 := by
  obtain ⟨A0, pf, h0, e⟩ := hP g a ha
  subst e
  exact plan_tiles (A := A0) h0

theorem planIs_next0 (hP : PlanIs W) (ha : W.A[g]? = some a) : a.seam.Fp.next = 0 := by
  obtain ⟨A0, pf, h0, e⟩ := hP g a ha
  subst e
  exact Fo.Next0.planA_next0 _ _ _ A0 h0

/-- **K5Plan at the public record's own numbers.** -/
theorem k5Plan_of_public (hP : PlanIs W) (h4 : W.p4 = true) (ha : W.A[g]? = some a) {x : Look.Place}
    (hx : lookAt W (2 * g + 1) false = some x) (set : Params.Setting) :
    ∃ xd : Look.Place, lookAt W (2 * g + 1) true = some xd ∧ x.ns = a.ns ∧ x.F.next + Forest.elems x.fs = Forest.elems a.fs ∧
      ((Look.P.ofPlace set true xd).shape = some a.seam.tl.f9 →
        K5Plan a.own (2 * g + 1) (Look.P.ofPlace set false x) (Look.P.ofPlace set true xd) a.seam.tl.f9
          (Forest.elems a.fs) (slotsOf (script a.own) + Forest.elems a.seam.tl.f9) a.ns) := by
  have ht := planIs_tiles hP ha
  have hz := planIs_next0 hP ha
  obtain ⟨c1, c2, _, c4⟩ := place_calls h4 ha hx
  obtain ⟨xd, hxd, d1, d2, _, _⟩ := place_digits (W := W) (g := g) h4 ha (by omega)
  refine ⟨xd, hxd, c2, by rw [c1, hz, c4]; omega, fun hsh => ⟨rfl, rfl, hsh, d2, rfl, ?_, ?_⟩⟩
  · show Forest.elems a.fs + (slotsOf (script a.own) + Forest.elems a.seam.tl.f9) ≤ a.ns
    omega
  · show xd.F.next = Forest.elems a.fs + slotsOf (script a.own)
    rw [d1]
    omega

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.place_calls
#print axioms VerifiableInference.Desc.First.Att.P.place_digits
#print axioms VerifiableInference.Desc.First.Att.P.planIs_tiles
#print axioms VerifiableInference.Desc.First.Att.P.k5Plan_of_public
