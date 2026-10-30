-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Key/KeyRowAgree.lean: THE KEY FILE's TABLES: «THE LAST INCH» OF THE MAP THAT LAYS: A ROW READS THE WORDS AT ITS OWN NAMES ALONE. RowHolds and Means.Says sum over EVERY message of the statement, each entry times a coefficient: so a row that rides past a laying
reads the laid message too: that it does not count is a fact: off the row's names the coefficient reads 0 (the last chain's files' coefficient_off_names, Johnson/Desc/Third/Law/Renamed.lean).
  names_of_rowIn             PROVED: a row that has passed the tests of the adding at a group names that group's members alone
  coeff_off_members          PROVED: so off the group's members its coefficient reads 0: THE PREMISE hz OF row_rides_layAt (KeyCloseBack.lean: not in this library), FROM THE FENCE
(«two families of words alike where the coefficient does not read 0: the row says the same of both» IS says_congr, by report (three theorems of that name stand in the library: Johnson/Desc/Third/Law/Row0Words.lean, Johnson/Desc/K12/Law/TupleWords.lean, Johnson/Desc/First/Close/Law/FillRow.lean: each asks the two families alike at every message, whatever the coefficient reads; the last two inside the tables' sizes alone): what doubles it here is private and serves the last lemma alone.)
  rowHolds_agree             PROVED: THE TABLE's SENTENCE: at same := «ρ x = ρ y», under RowIn: val and val' read alike at the group's members ⟹ RowHolds … val r ↔ RowHolds … val' r
WHO CALLS IT: the riders of a row that closes a pin (1.15 · 2.9 · 2.10 · 3.2): the items that are RowHolds over rows of the statement (srow k · «Eval» · «FoldO» …) ride from w to layAt … w where no laid message is a member of the row's group; RowIn from the promise's fence (SampleIn | OpenIn | InOrder).
Imports RowHoldsSays.lean and Third/Law/Renamed.lean. Nothing on soundness.
-/
import Johnson.Desc.Key.RowHoldsSays
import Johnson.Desc.Third.Law.Renamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes

variable {K : Type} [CommRing K] (ρ : Model.Reading K)

private theorem onTable_agree (S : Statement) (r : OnBytes.Row) (m m' : Means.Words K) (h : ∀ o ∈ r.oracles, m o = m' o) (o : Nat) (pt : Part) :
    Means.onTable ρ S r m o pt = Means.onTable ρ S r m' o pt := by
  unfold Means.onTable
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases ho : o ∈ r.oracles
  · rw [h o ho]
  · rw [Third.Law.coefficient_off_names ρ r o ho pt i, zero_mul, zero_mul]

private theorem value_agree (S : Statement) (r : OnBytes.Row) (m m' : Means.Words K) (h : ∀ o ∈ r.oracles, m o = m' o) : Means.value ρ S r m = Means.value ρ S r m' := by
  unfold Means.value
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [onTable_agree ρ S r m m' h o .main, onTable_agree ρ S r m m' h o .mask]

private theorem says_agree (S : Statement) (r : OnBytes.Row) (m m' : Means.Words K) (h : ∀ o ∈ r.oracles, m o = m' o) : Means.Says ρ S r m ↔ Means.Says ρ S r m' := by
  unfold Means.Says
  rw [value_agree ρ S r m m' h]

/-- A row that has passed the tests of the adding names the group's members alone. -/
theorem names_of_rowIn {S : Statement} {G : OnBytes.Group} {r : OnBytes.Row} (h : Means.RowIn S G r) : ∀ o ∈ r.oracles, o ∈ G.members.toList := by
  intro o ho
  simp only [Row.oracles, List.mem_append, Array.toList_map, List.mem_map] at ho
  rcases ho with ((⟨t, ht, rfl⟩ | ⟨u, hu, rfl⟩) | ⟨w, hw, rfl⟩) | ⟨f, hf, rfl⟩
  · exact ((Means.placeOk_iff _ _ _ _ _ _).1 (h.terms t ht)).1
  · exact ((Means.placeOk_iff _ _ _ _ _ _).1 (h.units u hu)).1
  · exact ((Means.placeOk_iff _ _ _ _ _ _).1 (h.runs w hw).2.2).1
  · exact ((Means.placeOk_iff _ _ _ _ _ _).1 (h.forms f hf).1).1

/-- **Off the group's members a fenced row's coefficient reads 0**: what row_rides_layAt (not in this library) asks (its hz), from the fence: where no laid message is a member of the row's group. -/
theorem coeff_off_members {S : Statement} {G : OnBytes.Group} {r : OnBytes.Row} (hr : Means.RowIn S G r) (o : Nat) (ho : o ∉ G.members.toList) (pt : Part) (i : Nat) :
    ρ.val (r.coefficient o pt i) = 0 :=
  Third.Law.coefficient_off_names ρ r o (fun h => ho (names_of_rowIn hr o h)) pt i

private theorem says_agree_in {S : Statement} {G : OnBytes.Group} {r : OnBytes.Row} (hr : Means.RowIn S G r) (m m' : Means.Words K) (h : ∀ o ∈ G.members.toList, m o = m' o) :
    Means.Says ρ S r m ↔ Means.Says ρ S r m' := says_agree ρ S r m m' fun o ho => h o (names_of_rowIn hr o ho)

/-- **The table's sentence: a row reads the entries of its group's members alone.** -/
theorem rowHolds_agree {S : Statement} {G : OnBytes.Group} {r : OnBytes.Row} (hr : Means.RowIn S G r) (val val' : Nat → Part → Nat → E)
    (h : ∀ o ∈ G.members.toList, ∀ pt i, ρ.val (val o pt i) = ρ.val (val' o pt i)) :
    RowHolds (fun a b => ρ.val a = ρ.val b) S val r ↔ RowHolds (fun a b => ρ.val a = ρ.val b) S val' r := by
  rw [rowHolds_iff_says_of_rowIn ρ S G val r hr, rowHolds_iff_says_of_rowIn ρ S G val' r hr]
  exact says_agree_in ρ hr _ _ fun o ho => funext fun pt => funext fun i => h o ho pt i

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.coeff_off_members
#print axioms VerifiableInference.Desc.Key.names_of_rowIn
#print axioms VerifiableInference.Desc.Key.rowHolds_agree
