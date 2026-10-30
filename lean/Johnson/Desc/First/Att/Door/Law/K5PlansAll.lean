-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5PlansAll.lean: kind K5: **THE TWO TESTS ON THE PLAN's SEATS AND SHAPES, ASKED AT EVERY MEMBER OF THE CALLER's LIST, GIVE THEM AT ANY LIST OF NUMBERS**: so at the members that the law reads.
Why. The law's two fields seatsPlan | shapesPlan (seatsPlanB | shapesPlanB, Johnson/Desc/First/Att/K05OwnersSent.lean) are asked at the pairs of the members that are read (readMsgs, Johnson/Desc/First/Att/K05ReadMsgs.lean), and which these
are hangs on the map from trees to arrays' names in what the planner sends. The forms "at every member" read no such map.

Main names:
  ps_sub | qs_sub: every pair of psOf l seat ks | qsOf l ks is a pair at List.range l.length (numbers from l.length on are dropped by both).
  **seatsPlan_of_all | shapesPlan_of_all**: the test at List.range l.length gives the test at every ks.
IS IT EMPTY HERE? Rules over letters.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05OwnersSent
import Johnson.Desc.First.Att.K05ReadMsgs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open OnBytes
open VerifiableInference.Desc.First.Att.P (psOf qsOf ps_mem seatsPlanB shapesPlanB)
open VerifiableInference.Desc.First.FillSent (SentData)
open VerifiableInference.Desc.K12.Door (Laid)

/-- Every pair (number, seat) at some list of numbers is a pair at all the list's numbers. -/
theorem ps_sub (l : List (OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ) (ks : List ℕ) (p : ℕ × (ℕ × ℕ)) (hp : p ∈ psOf l seat ks) :
    p ∈ psOf l seat (List.range l.length) := by
  obtain ⟨k, _, e⟩ := List.mem_filterMap.1 hp
  by_cases h : k < l.length
  · rw [dif_pos h] at e
    obtain rfl := Option.some.inj e
    exact ps_mem l seat ⟨k, h⟩ (List.mem_range.2 h)
  · rw [dif_neg h] at e
    cases e

/-- Every pair (number, shape) at some list of numbers is a pair at all the list's numbers. -/
theorem qs_sub (l : List (OracleShape × ℕ)) (ks : List ℕ) (p : ℕ × OracleShape) (hp : p ∈ qsOf l ks) : p ∈ qsOf l (List.range l.length) := by
  obtain ⟨k, _, e⟩ := List.mem_filterMap.1 hp
  obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 e
  exact List.mem_filterMap.2 ⟨k, List.mem_range.2 (List.getElem?_eq_some_iff.1 ho).1, by rw [ho]; rfl⟩

/-- **The test on the seats at every member gives it at any numbers.** -/
theorem seatsPlan_of_all {d : SentData} {m kept : ℕ} {Ld : Laid} {l : List (OracleShape × ℕ)} {seat : Fin l.length → ℕ × ℕ}
    {own : List (ℕ × ℕ)} {n : ℕ} (h : seatsPlanB d m kept Ld (psOf l seat (List.range l.length)) own n = true) (ks : List ℕ) :
    seatsPlanB d m kept Ld (psOf l seat ks) own n = true := by
  unfold seatsPlanB at h ⊢
  exact List.all_eq_true.2 fun p hp => List.all_eq_true.1 h p (ps_sub l seat ks p hp)

/-- **The test on the shapes at every member gives it at any numbers.** -/
theorem shapesPlan_of_all {d : SentData} {m kept : ℕ} {M : List OracleShape} {l : List (OracleShape × ℕ)} {n : ℕ}
    (h : shapesPlanB d m kept M (qsOf l (List.range l.length)) n = true) (ks : List ℕ) :
    shapesPlanB d m kept M (qsOf l ks) n = true := by
  unfold shapesPlanB at h ⊢
  exact List.all_eq_true.2 fun p hp => List.all_eq_true.1 h p (qs_sub l ks p hp)

end H2K5.Door

#print axioms H2K5.Door.ps_sub
#print axioms H2K5.Door.qs_sub
#print axioms H2K5.Door.seatsPlan_of_all
#print axioms H2K5.Door.shapesPlan_of_all
