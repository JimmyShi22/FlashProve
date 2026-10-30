-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/FallAlg.lean: THE WEIGHT OF ONE ENTRY, READ OFF A LEDGER's VALUE IN TWO WORLDS;
AND THE SUM OF PLAIN CLAIMS AS TERMS IN THE BATCHING ELEMENT. Statements and proofs, for the count of
Johnson/Desc/K8/Honest/FallCount.lean. No block, no state of the chain, no prover.

  `sumFrom_above`, `sumFrom_only`   a numbered sum in which only the term of one number counts
  `row_off`, `row_oneAt`, `tree_off`, `tree_oneAt`, `trees_oneAt`, `trees_allZero`, `slots_none`
  **`total_oneAt`**   a ledger's value where one entry is 1 and all else 0, less its value where all
      is 0, is the weight on that entry, if the entry's virtual row begins at column 0;
      `total_below`: it is 0 if the entry lies in front of the row's first column
  `fromOn a m c`   the terms (c, a c), .., (c + m - 1, a (c + m - 1)); `fromOn_mem`, `fromOn_nodup`
  **`claimsSum_plain`**   for plain claims whose coefficients on the entry are a's: the claims' sum
      under their weights, taken in the two worlds, parts by the terms `fromOn a` at the element
Limits: identities. Nothing on any run of claims.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.FallCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc

/-! ## A numbered sum with one term that counts -/

section
variable {K : Type} [CommRing K]

theorem sumFrom_above {α : Type} (g : Nat → α → K) (k : Nat) (h : ∀ j x, j ≠ k → g j x = 0) :
    ∀ (l : List α) (s : Nat), k < s → sumFrom g s l = 0
  | [], _, _ => rfl
  | x :: l, s, hs => by
    simp only [sumFrom]
    rw [h s x (by omega), sumFrom_above g k h l (s + 1) (by omega), add_zero]

theorem sumFrom_only {α : Type} (g : Nat → α → K) (k : Nat) (h : ∀ j x, j ≠ k → g j x = 0) :
    ∀ (l : List α) (s : Nat), s ≤ k → sumFrom g s l = ((l[k - s]?).map (g k)).getD 0
  | [], _, _ => by simp [sumFrom]
  | x :: l, s, hs => by
    simp only [sumFrom]
    by_cases e : s = k
    · subst e
      rw [sumFrom_above g s h l (s + 1) (by omega)]
      simp
    · rw [h s x e, sumFrom_only g k h l (s + 1) (by omega), zero_add,
        show k - s = (k - (s + 1)) + 1 by omega, List.getElem?_cons_succ]

end

theorem getD_toList {α : Type} (A : Array α) (k : Nat) (d : α) :
    A.getD k d = (A.toList[k]?).getD d := by
  simp [Array.getD_eq_getD_getElem?]

/-! ## A ledger's value in the two worlds -/

section
variable (ρ : Reading Cb.Gl.E)

theorem row_off (t r i t' r' : Nat) (R : HRow) (h : ¬ (t' = t ∧ r' = r)) :
    HRow.value ρ (oneAt t r i) t' r' R = 0 := by
  unfold HRow.value
  refine sumFrom_eq_zero _ _ _ (fun j v _ => ?_)
  have hn : ¬ (t' = t ∧ r' = r ∧ j = i) := fun e => h ⟨e.1, e.2.1⟩
  simp [oneAt, hn]

theorem row_oneAt (t r i : Nat) (R : HRow) (h0 : R.L0 = 0) :
    HRow.value ρ (oneAt t r i) t r R = ρ.val (R.L.getD i zeroE) := by
  have hz : ∀ (j : Nat) (v : E), j ≠ i → ρ.val v * (oneAt t r i).entry t r j = 0 := by
    intro j v hj
    simp [oneAt, hj]
  unfold HRow.value
  rw [h0, sumFrom_only (fun j v => ρ.val v * (oneAt t r i).entry t r j) i hz R.L.toList 0
    (Nat.zero_le i), Nat.sub_zero, getD_toList]
  cases R.L.toList[i]? with
  | none => simp [ρ.zero]
  | some v => simp [oneAt]

theorem tree_off (t r i t' : Nat) (X : HTree) (h : t' ≠ t) :
    HTree.value ρ (oneAt t r i) t' X = 0 := by
  unfold HTree.value
  exact sumFrom_eq_zero _ _ _ (fun r' R _ => row_off ρ t r i t' r' R (fun e => h e.1))

theorem tree_oneAt (t r i : Nat) (X : HTree) (h0 : (X.rows.getD r {}).L0 = 0) :
    HTree.value ρ (oneAt t r i) t X = ρ.val ((X.rows.getD r {}).L.getD i zeroE) := by
  unfold HTree.value
  rw [sumFrom_only (fun r' R => HRow.value ρ (oneAt t r i) t r' R) r
    (fun r' R hr => row_off ρ t r i t r' R (fun e => hr e.2)) X.rows.toList 0 (Nat.zero_le r),
    Nat.sub_zero]
  rw [getD_toList X.rows] at h0 ⊢
  cases hR : X.rows.toList[r]? with
  | none => simp [ρ.zero, Array.getD_eq_getD_getElem?]
  | some R =>
    rw [hR] at h0
    simpa using row_oneAt ρ t r i R (by simpa using h0)

theorem trees_oneAt (t r i : Nat) (trees : Array HTree)
    (h0 : ((trees.getD t {}).rows.getD r {}).L0 = 0) :
    treesValue ρ (oneAt t r i) trees =
      ρ.val (((trees.getD t {}).rows.getD r {}).L.getD i zeroE) := by
  unfold treesValue
  rw [sumFrom_only (fun t' X => HTree.value ρ (oneAt t r i) t' X) t
    (fun t' X ht => tree_off ρ t r i t' X ht) trees.toList 0 (Nat.zero_le t), Nat.sub_zero]
  rw [getD_toList trees] at h0 ⊢
  cases hX : trees.toList[t]? with
  | none => simp [ρ.zero, Array.getD_eq_getD_getElem?]
  | some X =>
    rw [hX] at h0
    simpa using tree_oneAt ρ t r i X (by simpa using h0)

theorem trees_allZero (trees : Array HTree) : treesValue ρ allZero trees = 0 := by
  unfold treesValue
  refine sumFrom_eq_zero _ _ _ (fun t X _ => ?_)
  unfold HTree.value
  refine sumFrom_eq_zero _ _ _ (fun r R _ => ?_)
  unfold HRow.value
  exact sumFrom_eq_zero _ _ _ (fun i v _ => by simp [allZero])

theorem slots_none (W : World Cb.Gl.E) (hW : ∀ j, W.slot j = 0) (LS : Array E) :
    slotsValue ρ W LS = 0 := by
  unfold slotsValue
  exact sumFrom_eq_zero _ _ _ (fun j v _ => by rw [hW, mul_zero])

/-! An entry in front of the first column that a virtual row's weights hold counts for nothing. -/

theorem row_below (t r i : Nat) (R : HRow) (h : i < R.L0) :
    HRow.value ρ (oneAt t r i) t r R = 0 := by
  have hz : ∀ (j : Nat) (v : E), j ≠ i → ρ.val v * (oneAt t r i).entry t r j = 0 := by
    intro j v hj
    simp [oneAt, hj]
  unfold HRow.value
  exact sumFrom_above (fun j v => ρ.val v * (oneAt t r i).entry t r j) i hz R.L.toList R.L0 h

theorem tree_below (t r i : Nat) (X : HTree) (h : i < (X.rows.getD r {}).L0) :
    HTree.value ρ (oneAt t r i) t X = 0 := by
  unfold HTree.value
  rw [sumFrom_only (fun r' R => HRow.value ρ (oneAt t r i) t r' R) r
    (fun r' R hr => row_off ρ t r i t r' R (fun e => hr e.2)) X.rows.toList 0 (Nat.zero_le r),
    Nat.sub_zero]
  rw [getD_toList X.rows] at h
  cases hR : X.rows.toList[r]? with
  | none => rfl
  | some R =>
    rw [hR] at h
    simpa using row_below ρ t r i R (by simpa using h)

theorem trees_below (t r i : Nat) (trees : Array HTree)
    (h : i < ((trees.getD t {}).rows.getD r {}).L0) : treesValue ρ (oneAt t r i) trees = 0 := by
  unfold treesValue
  rw [sumFrom_only (fun t' X => HTree.value ρ (oneAt t r i) t' X) t
    (fun t' X ht => tree_off ρ t r i t' X ht) trees.toList 0 (Nat.zero_le t), Nat.sub_zero]
  rw [getD_toList trees] at h
  cases hX : trees.toList[t]? with
  | none => rfl
  | some X =>
    rw [hX] at h
    simpa using tree_below ρ t r i X (by simpa using h)

/-- **The weight on an entry, off the ledger's value in two worlds.** -/
theorem total_oneAt (F : Fork) (t r i : Nat)
    (h0 : ((F.trees.getD t {}).rows.getD r {}).L0 = 0) :
    F.total ρ (oneAt t r i) - F.total ρ allZero = ρ.val ((weightsOf F t r).getD i zeroE) := by
  unfold Fork.total weightsOf
  rw [trees_oneAt ρ t r i F.trees h0, trees_allZero, slots_none ρ (oneAt t r i) (fun _ => rfl),
    slots_none ρ allZero (fun _ => rfl)]
  ring

/-- Where the entry lies in front of the row's first column, the two values are one. -/
theorem total_below (F : Fork) (t r i : Nat)
    (h : i < ((F.trees.getD t {}).rows.getD r {}).L0) :
    F.total ρ (oneAt t r i) - F.total ρ allZero = 0 := by
  unfold Fork.total
  rw [trees_below ρ t r i F.trees h, trees_allZero, slots_none ρ (oneAt t r i) (fun _ => rfl),
    slots_none ρ allZero (fun _ => rfl)]
  ring

end

/-! ## Plain claims as terms -/

/-- The terms (c, a c), (c + 1, a (c + 1)), .., m of them. -/
def fromOn (a : Nat → Cb.Gl.E) : (m c : Nat) → List (ℕ × Cb.Gl.E)
  | 0, _ => []
  | m + 1, c => (c, a c) :: fromOn a m (c + 1)

theorem fromOn_mem (a : Nat → Cb.Gl.E) : ∀ (m c : Nat) (y : ℕ × Cb.Gl.E), y ∈ fromOn a m c →
    c ≤ y.1 ∧ y.1 < c + m
  | 0, _, _, h => nomatch h
  | m + 1, c, y, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨Nat.le_refl _, by simp⟩
    · have := fromOn_mem a m (c + 1) y h
      omega

theorem fromOn_nodup (a : Nat → Cb.Gl.E) : ∀ (m c : Nat), ((fromOn a m c).map (·.1)).Nodup
  | 0, _ => List.nodup_nil
  | m + 1, c => by
    simp only [fromOn, List.map_cons, List.nodup_cons]
    refine ⟨fun h => ?_, fromOn_nodup a m (c + 1)⟩
    obtain ⟨y, hy, e⟩ := List.mem_map.1 h
    have := (fromOn_mem a m (c + 1) y hy).1
    omega

/-- **Plain claims whose coefficients on an entry are a's.** x: the batching element, read in the
field. n: the plan's number of claims. c: the first claim's number. -/
theorem claimsSum_plain (x : Cb.Gl.E) (n t r i : Nat) (a : Nat → Cb.Gl.E) :
    ∀ (l : List Claim) (c : Nat),
      (∀ j cl, l[j]? = some cl → cl.eqFirst = none ∧ coefOn cl t r i = a (c + j)) →
      K9L.claimsSum Reading.gl (oneAt t r i) x n c l - K9L.claimsSum Reading.gl allZero x n c l =
        K9L.termsSum (fromOn a l.length c) x
  | [], c, _ => by simp [K9L.claimsSum, sumFrom, K9L.termsSum, fromOn]
  | cl :: l, c, h => by
    obtain ⟨h0, h1⟩ := h 0 cl (by simp)
    have ih := claimsSum_plain x n t r i a l (c + 1) (fun j y hy => by
      have h2 := h (j + 1) y (by simpa using hy)
      rwa [show c + (j + 1) = c + 1 + j by omega] at h2)
    have he : K9L.expo n c cl = c := by simp [K9L.expo, h0]
    have h1' : K9L.claimValue Reading.gl (oneAt t r i) cl - K9L.claimValue Reading.gl allZero cl =
        a c := by simpa [coefOn] using h1
    simp only [K9L.claimsSum, sumFrom, List.length_cons, fromOn, K9L.termsSum, List.map_cons,
      List.sum_cons] at ih ⊢
    rw [he]
    linear_combination ih + x ^ c * h1'

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.total_oneAt
#print axioms VerifiableInference.Desc.First.K8.Honest.total_below
#print axioms VerifiableInference.Desc.First.K8.Honest.claimsSum_plain
#print axioms VerifiableInference.Desc.First.K8.Honest.fromOn_nodup
