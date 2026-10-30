-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- Johnson/Desc/First/Att/Door/Law/ReadsThereTie.lean: A YES OF THE ITEM «K5.readsThere»'s Bool GIVES THE LEMMAS' Bool AND U3There, BY LEAN. (The item's first clause bears the equation T.K = nW: the item's Bool gives the lemmas'.)
import Johnson.Desc.First.Att.Door.ReadsThereB
import Johnson.Desc.First.Att.K05U3B

set_option autoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att.P

/-- **A yes of readsAtB gives u3AtB's.** -/
theorem readsAtB_gives (own : List (Nat × Nat)) (c : ParC) (s : VerifiableInference.Desc.First.S)
    (a : VerifiableInference.Desc.First.AttOwn) (h : readsAtB own c.iU3 c.nW a.L a.F s.book = true) :
    u3AtB own c s a = true := by
  unfold readsAtB at h
  unfold u3AtB
  simp only [Bool.and_eq_true] at h ⊢
  refine ⟨⟨?_, h.1.2⟩, h.2⟩
  cases hT : a.F.trees[c.iU3]? with
  | none => rw [hT] at h; simp at h
  | some T =>
    rw [hT] at h
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h ⊢
    exact ⟨h.1.1.1, Nat.le_of_eq h.1.1.2.symm⟩

/-- So a yes of the item's Bool at an open attention segment gives U3There at the plan of the segment's group. -/
theorem u3There_of_sheet (W : Verify.Public) (own : List (Nat × Nat)) (s : VerifiableInference.Desc.First.S)
    (a : VerifiableInference.Desc.First.AttOwn) (e : s.here = .att a) (p : Attention.Plan)
    (hp : W.A[a.L.link / 2]? = some p) (h : readsThereB W own s = true) : U3There own s a (parCOf p) := by
  unfold readsThereB at h
  rw [e] at h
  simp only [hp, Option.any_some] at h
  refine u3There_of_B e ?_
  unfold u3ThereB
  rw [e]
  exact readsAtB_gives own (parCOf p) s a h

/-- **And the width**: the ledger's array of the reads has one row and just the plan's number of columns. -/
theorem width_of_sheet (W : Verify.Public) (own : List (Nat × Nat)) (s : VerifiableInference.Desc.First.S)
    (a : VerifiableInference.Desc.First.AttOwn) (e : s.here = .att a) (p : Attention.Plan)
    (hp : W.A[a.L.link / 2]? = some p) (h : readsThereB W own s = true) :
    ∃ T, a.F.trees[p.iU3]? = some T ∧ T.R = 1 ∧ T.K = p.nW := by
  unfold readsThereB at h
  rw [e] at h
  simp only [hp, Option.any_some] at h
  unfold readsAtB at h
  simp only [Bool.and_eq_true] at h
  cases hT : a.F.trees[p.iU3]? with
  | none => rw [hT] at h; simp at h
  | some T =>
    rw [hT] at h
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨T, rfl, h.1.1.1, h.1.1.2⟩

#print axioms readsAtB_gives
#print axioms u3There_of_sheet
#print axioms width_of_sheet

end H2K5.Door
