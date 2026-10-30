-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.FirstCut
import Johnson.Desc.K12.Law.PlacesSmall
import Johnson.Desc.K12.Law.PlacesFull
import Johnson.Desc.BlockSlot
/-
Johnson/Desc/K12/Law/LabelsClash.lean: AT THE LAST CHAIN's OWN PROXIMITY TEST NO NUMBERING OF THE TREES THROUGH THE FILE IS A FUNCTION OF THE LABEL: two of the first switch's declared openings bear ONE label and have TWO sources, «taken 0 1» and «taken 1 1». ON THE PLAN ALONE. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  clash_WFull | clash_W    among opensOf π k (k the first stage's) stand (a shape with the label 1, taken 0 1) and (a shape with the label 1, taken 1 1): at the full and at the smaller size
  k_WFull | k_W            5 | 3 ARE the first stage's k at the two places
  no_label_number          whatever num and nl: if num o.2 = nl o.1.tree at every declared opening of the first switch of piWFull, then num (.taken 0 1) = num (.taken 1 1)
  no_label_numAt           at num := numAt t₁ t₂ c (Johnson/Desc/BlockSlot.lean): then t₁ = 0: so where the first chain sends a tree at all, «each declared opening's source's number through the file is nl of its label» FAILS AT THIS PLACE FOR EVERY nl · _W: the like at the smaller size
WHY: a form of the kind's law that numbers the book's places by their trees' labels asks that sentence of the plan. At the places whose openings are the chain's own it can hold; at this place it cannot.
THE PLACES ARE CLOSED TERMS: A RUN's PRINT MADE INTO TERMS. By «decide».
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.First
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- The sources under the label n among a list of openings. -/
def srcsUnder (n : Nat) (os : List (Fmt.Shape × Fmt.TreeSource)) : List Fmt.TreeSource :=
  (os.filter fun o => o.1.tree == n).map (·.2)

theorem clash_WFull : srcsUnder 1 (opensOf H2K.Member.piWFull 5) = [.taken 0 1, .taken 1 1] := by
  decide
theorem clash_W : srcsUnder 1 (opensOf H2K.Member.piW 3) = [.taken 0 1, .taken 1 1] := by decide

/-- 5 and 3 are the first stages' numbers of row variables at the two places. -/
theorem k_WFull : H2K.Member.piWFull.nums.stages.head?.map (·.k) = some 5 := by decide
theorem k_W : H2K.Member.piW.nums.stages.head?.map (·.k) = some 3 := by decide

theorem under_mem (n : Nat) (os : List (Fmt.Shape × Fmt.TreeSource)) (s : Fmt.TreeSource)
    (h : s ∈ srcsUnder n os) : ∃ o ∈ os, o.1.tree = n ∧ o.2 = s := by
  unfold srcsUnder at h
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 h
  obtain ⟨h1, h2⟩ := List.mem_filter.1 ho
  exact ⟨o, h1, by simpa using h2, rfl⟩

theorem no_label_of (os : List (Fmt.Shape × Fmt.TreeSource)) (n : Nat) (s s' : Fmt.TreeSource)
    (hs : s ∈ srcsUnder n os) (hs' : s' ∈ srcsUnder n os) (num : Fmt.TreeSource → Nat)
    (nl : Nat → Nat) (h : ∀ o ∈ os, num o.2 = nl o.1.tree) : num s = num s' := by
  obtain ⟨o, ho, e1, rfl⟩ := under_mem n os s hs
  obtain ⟨o', ho', e1', rfl⟩ := under_mem n os s' hs'
  rw [h o ho, h o' ho', e1, e1']

theorem no_label_number (num : Fmt.TreeSource → Nat) (nl : Nat → Nat)
    (h : ∀ o ∈ opensOf H2K.Member.piWFull 5, num o.2 = nl o.1.tree) :
    num (.taken 0 1) = num (.taken 1 1) :=
  no_label_of _ 1 _ _ (by rw [clash_WFull]; simp) (by rw [clash_WFull]; simp) num nl h


theorem no_label_numAt (t₁ t₂ c : Nat) (nl : Nat → Nat)
    (h : ∀ o ∈ opensOf H2K.Member.piWFull 5,
      VerifiableInference.Desc.numAt t₁ t₂ c o.2 = nl o.1.tree) : t₁ = 0 := by
  have e := no_label_number (VerifiableInference.Desc.numAt t₁ t₂ c) nl h
  simp only [VerifiableInference.Desc.numAt] at e
  simp at e
  omega

theorem no_label_numAt_W (t₁ t₂ c : Nat) (nl : Nat → Nat)
    (h : ∀ o ∈ opensOf H2K.Member.piW 3, VerifiableInference.Desc.numAt t₁ t₂ c o.2 = nl o.1.tree) :
    t₁ = 0 := by
  have e := no_label_of _ 1 (.taken 0 1) (.taken 1 1) (by rw [clash_W]; simp) (by rw [clash_W]; simp)
    (VerifiableInference.Desc.numAt t₁ t₂ c) nl h
  simp only [VerifiableInference.Desc.numAt] at e
  simp at e
  omega

end H2K.First

#print axioms H2K.First.clash_WFull
#print axioms H2K.First.clash_W
#print axioms H2K.First.no_label_numAt
#print axioms H2K.First.no_label_numAt_W
