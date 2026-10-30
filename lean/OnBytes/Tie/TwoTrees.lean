-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/TwoTrees.lean: the pruned walk over two trees of one depth is the two trees' walks.

The library's pruned walk (Hash/Octopus.lean) goes up from a list of numbered nodes, level by level.
Where a node's sibling is not in the list, the walk takes the sibling's digest from a second list,
which the library calls the message. Lay the nodes of a second tree of depth d behind those of a
first one, with 2 ^ d added to their numbers. Then no node of the first tree is the sibling of a
node of the second, at any level. So the walk over both lists is the first tree's walk followed by
the second tree's.

Main theorems: `octF_two` (the digests), `upN_two` (the numbers).
Proof: four functions of one level (`up`, `stepF`, `reads1`, `upP`) split over two lists if no node
of the first is a sibling of a node of the second, and commute with adding an even number. Then by
induction on the depth.
It claims nothing on what a chain proves.
-/
import Hash.OctopusFacts

namespace OnBytes.Tie

open Octopus

/-! ## Numbers -/

/-- Adding an even number to both keeps siblings siblings. -/
theorem sib_shift (c i j : ℕ) : sib (2 * c + i) (2 * c + j) ↔ sib i j := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, by omega⟩

/-- A number below 2 c is no left sibling of a number from 2 c on. -/
theorem not_sib_of_lt (c i y : ℕ) (h : i < 2 * c) : ¬ sib i (2 * c + y) := by
  rintro ⟨h1, h2⟩
  omega

/-- Adding 2 c to the children's numbers adds c to the parents'. -/
theorem up_shift (c : ℕ) : ∀ l : List ℕ, up (l.map (2 * c + ·)) = (up l).map (c + ·)
  | [] => rfl
  | [i] => by
    show [(2 * c + i) / 2] = [c + i / 2]
    rw [show (2 * c + i) / 2 = c + i / 2 by omega]
  | i :: j :: l => by
    have ih1 := up_shift c l
    have ih2 := up_shift c (j :: l)
    have hd : (2 * c + i) / 2 = c + i / 2 := by omega
    simp only [List.map_cons] at ih2 ⊢
    by_cases h : sib i j
    · simp only [up, if_pos h, if_pos ((sib_shift c i j).mpr h), ih1, hd, List.map_cons]
    · simp only [up, if_neg h, if_neg (mt (sib_shift c i j).mp h), ih2, hd, List.map_cons]

/-- Adding an even number does not change the number of digests that a level takes. -/
theorem need1_shift (c : ℕ) : ∀ l : List ℕ, need1 (l.map (2 * c + ·)) = need1 l
  | [] => rfl
  | [_] => rfl
  | i :: j :: l => by
    have ih1 := need1_shift c l
    have ih2 := need1_shift c (j :: l)
    simp only [List.map_cons] at ih2 ⊢
    by_cases h : sib i j
    · simp only [need1, if_pos h, if_pos ((sib_shift c i j).mpr h), ih1]
    · simp only [need1, if_neg h, if_neg (mt (sib_shift c i j).mp h), ih2]

/-- The parents' numbers split over two lists with no siblings across them. -/
theorem up_append : ∀ (X Y : List ℕ), (∀ i ∈ X, ∀ j ∈ Y, ¬ sib i j) →
    up (X ++ Y) = up X ++ up Y
  | [], _, _ => rfl
  | [_], [], _ => rfl
  | [i], j :: Y, h => by
    have hn : ¬ sib i j := h i (by simp) j (by simp)
    show up (i :: j :: Y) = [i / 2] ++ up (j :: Y)
    rw [up, if_neg hn]
    rfl
  | i :: k :: X, Y, h => by
    have h1 : ∀ a ∈ X, ∀ j ∈ Y, ¬ sib a j := fun a ha => h a (by simp [ha])
    have h2 : ∀ a ∈ k :: X, ∀ j ∈ Y, ¬ sib a j := fun a ha => h a (List.mem_cons_of_mem _ ha)
    have ih1 := up_append X Y h1
    have ih2 := up_append (k :: X) Y h2
    rw [List.cons_append] at ih2
    show up (i :: k :: (X ++ Y)) = up (i :: k :: X) ++ up Y
    by_cases hs : sib i k
    · simp only [up, if_pos hs, ih1, List.cons_append]
    · simp only [up, if_neg hs, ih2, List.cons_append]

/-- The numbers after d levels: the second tree's come out with 1 added. -/
theorem upN_append : ∀ (d : ℕ) (X Y : List ℕ), (∀ i ∈ X, i < 2 ^ d) →
    upN d (X ++ Y.map (2 ^ d + ·)) = upN d X ++ (upN d Y).map (1 + ·)
  | 0, _, _, _ => rfl
  | d + 1, X, Y, h => by
    have hp : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hp] at h ⊢
    have hn : ∀ i ∈ X, ∀ j ∈ Y.map (2 * 2 ^ d + ·), ¬ sib i j := by
      intro i hi j hj
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hj
      exact not_sib_of_lt (2 ^ d) i y (h i hi)
    show upN d (up (X ++ Y.map (2 * 2 ^ d + ·))) = upN d (up X) ++ (upN d (up Y)).map (1 + ·)
    rw [up_append _ _ hn, up_shift]
    refine upN_append d (up X) (up Y) ?_
    intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_up X x hx
    have := h k hk
    omega

/-! ## One level of the walk -/

section Step
variable {D : Type} [Inhabited D] (hN : D → D → D)

/-- One level at two siblings: they are joined, and no digest of the message is taken. -/
theorem stepF_sib {i j : ℕ} (h : sib i j) (l : List ℕ) (v s : List D) :
    stepF hN (i :: j :: l) v s =
      hN (v.headD default) (v.tail.headD default) :: stepF hN l v.tail.tail s := by
  simp only [stepF, stepC, if_pos h]
  rfl

/-- One level at a node without its sibling: the next digest of the message is taken. -/
theorem stepF_lone {i j : ℕ} (h : ¬ sib i j) (l : List ℕ) (v s : List D) :
    stepF hN (i :: j :: l) v s =
      loneF hN i (v.headD default) (s.headD default) :: stepF hN (j :: l) v.tail s.tail := by
  simp only [stepF, stepC, if_neg h]
  rfl

omit [Inhabited D] in
/-- Which side a lone node's digest is on depends on its number's parity. -/
theorem loneF_shift (c i : ℕ) (a s : D) : loneF hN (2 * c + i) a s = loneF hN i a s := by
  unfold loneF
  rw [show (2 * c + i) % 2 = i % 2 by omega]

/-- One level gives as many digests as there are parents. -/
theorem length_stepF : ∀ (js : List ℕ) (v s : List D),
    (stepF hN js v s).length = (up js).length
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | i :: j :: l, v, s => by
    by_cases h : sib i j
    · rw [stepF_sib hN h, List.length_cons, length_stepF l]
      simp only [up, if_pos h, List.length_cons]
    · rw [stepF_lone hN h, List.length_cons, length_stepF (j :: l)]
      simp only [up, if_neg h, List.length_cons]

/-- One level reads only the first `need1` digests of the message. -/
theorem stepF_take : ∀ (js : List ℕ) (v s e : List D), s.length = need1 js →
    stepF hN js v (s ++ e) = stepF hN js v s
  | [], _, _, _, _ => rfl
  | [_], _, [], _, h => by simp [need1] at h
  | [_], _, _ :: _, _, _ => rfl
  | i :: j :: l, v, s, e, h => by
    by_cases hs : sib i j
    · have h' : s.length = need1 l := by simpa only [need1, if_pos hs] using h
      rw [stepF_sib hN hs, stepF_sib hN hs, stepF_take l _ s e h']
    · rcases s with _ | ⟨x, s⟩
      · simp only [need1, if_neg hs, List.length_nil] at h
        omega
      · have h' : s.length = need1 (j :: l) := by
          simp only [need1, if_neg hs, List.length_cons] at h
          omega
        rw [List.cons_append, stepF_lone hN hs, stepF_lone hN hs]
        simp only [List.headD_cons, List.tail_cons, stepF_take (j :: l) _ s e h']

/-- Adding an even number to the nodes' numbers does not change one level. -/
theorem stepF_shift (c : ℕ) : ∀ (js : List ℕ) (v s : List D),
    stepF hN (js.map (2 * c + ·)) v s = stepF hN js v s
  | [], _, _ => rfl
  | [i], v, s => by
    show [loneF hN (2 * c + i) _ _] = [loneF hN i _ _]
    rw [loneF_shift]
  | i :: j :: l, v, s => by
    have ih1 := stepF_shift c l v.tail.tail s
    have ih2 := stepF_shift c (j :: l) v.tail s.tail
    simp only [List.map_cons] at ih2 ⊢
    by_cases h : sib i j
    · rw [stepF_sib hN ((sib_shift c i j).mpr h), stepF_sib hN h, ih1]
    · rw [stepF_lone hN (mt (sib_shift c i j).mp h), stepF_lone hN h, loneF_shift, ih2]

/-- One level splits over two lists with no siblings across them. -/
theorem stepF_append : ∀ (X Y : List ℕ) (vX vY sX t : List D), vX.length = X.length →
    sX.length = need1 X → (∀ i ∈ X, ∀ j ∈ Y, ¬ sib i j) →
    stepF hN (X ++ Y) (vX ++ vY) (sX ++ t) = stepF hN X vX sX ++ stepF hN Y vY t
  | [], Y, vX, vY, sX, t, hv, hs, _ => by
    rw [List.eq_nil_of_length_eq_zero hv, List.eq_nil_of_length_eq_zero hs]
    rfl
  | [i], Y, vX, vY, sX, t, hv, hs, h => by
    rcases vX with _ | ⟨a, vX⟩
    · simp at hv
    rcases sX with _ | ⟨x, sX⟩
    · simp [need1] at hs
    have hv' : vX = [] := List.eq_nil_of_length_eq_zero (by simpa using hv)
    have hs' : sX = [] := List.eq_nil_of_length_eq_zero (by simpa [need1] using hs)
    subst hv' hs'
    rcases Y with _ | ⟨j, Y⟩
    · rfl
    · have hn : ¬ sib i j := h i (by simp) j (by simp)
      show stepF hN (i :: j :: Y) (a :: vY) (x :: t) = _
      rw [stepF_lone hN hn]
      rfl
  | i :: k :: X, Y, vX, vY, sX, t, hv, hs, h => by
    have h1 : ∀ a ∈ X, ∀ j ∈ Y, ¬ sib a j := fun a ha => h a (by simp [ha])
    have h2 : ∀ a ∈ k :: X, ∀ j ∈ Y, ¬ sib a j := fun a ha => h a (List.mem_cons_of_mem _ ha)
    rcases vX with _ | ⟨a, vX⟩
    · simp at hv
    by_cases hk : sib i k
    · rcases vX with _ | ⟨a', vX⟩
      · simp at hv
      have hv' : vX.length = X.length := by simpa using hv
      have hs' : sX.length = need1 X := by simpa only [need1, if_pos hk] using hs
      have ih := stepF_append X Y vX vY sX t hv' hs' h1
      show stepF hN (i :: k :: (X ++ Y)) (a :: a' :: (vX ++ vY)) (sX ++ t) = _
      rw [stepF_sib hN hk, stepF_sib hN hk]
      simp only [List.headD_cons, List.tail_cons, ih, List.cons_append]
    · rcases sX with _ | ⟨x, sX⟩
      · simp only [need1, if_neg hk, List.length_nil] at hs
        omega
      have hv' : vX.length = (k :: X).length := by simpa using hv
      have hs' : sX.length = need1 (k :: X) := by
        simp only [need1, if_neg hk, List.length_cons] at hs
        omega
      have ih := stepF_append (k :: X) Y vX vY sX t hv' hs' h2
      rw [List.cons_append] at ih
      show stepF hN (i :: k :: (X ++ Y)) (a :: (vX ++ vY)) (x :: (sX ++ t)) = _
      rw [stepF_lone hN hk, stepF_lone hN hk]
      simp only [List.headD_cons, List.tail_cons, ih, List.cons_append]

end Step

/-! ## Whole paths -/

section Paths
variable {D : Type} [Inhabited D]

/-- Adding an even number to the numbers does not change the digests that a level reads off the
paths. -/
theorem reads1_shift (c : ℕ) : ∀ l : List (ℕ × List D),
    reads1 (l.map fun x => (2 * c + x.1, x.2)) = reads1 l
  | [] => rfl
  | [_] => rfl
  | x :: y :: l => by
    have ih1 := reads1_shift c l
    have ih2 := reads1_shift c (y :: l)
    simp only [List.map_cons] at ih2 ⊢
    by_cases h : sib x.1 y.1
    · simp only [reads1, if_pos h, if_pos ((sib_shift c x.1 y.1).mpr h), ih1]
    · simp only [reads1, if_neg h, if_neg (mt (sib_shift c x.1 y.1).mp h), ih2]

omit [Inhabited D] in
/-- Adding 2 c to the children's numbers adds c to the parents' and leaves the parents' paths. -/
theorem upP_shift (c : ℕ) : ∀ l : List (ℕ × List D),
    upP (l.map fun x => (2 * c + x.1, x.2)) = (upP l).map fun x => (c + x.1, x.2)
  | [] => rfl
  | [x] => by
    show [((2 * c + x.1) / 2, x.2.tail)] = [(c + x.1 / 2, x.2.tail)]
    rw [show (2 * c + x.1) / 2 = c + x.1 / 2 by omega]
  | x :: y :: l => by
    have ih1 := upP_shift c l
    have ih2 := upP_shift c (y :: l)
    have hd : (2 * c + x.1) / 2 = c + x.1 / 2 := by omega
    simp only [List.map_cons] at ih2 ⊢
    by_cases h : sib x.1 y.1
    · simp only [upP, if_pos h, if_pos ((sib_shift c x.1 y.1).mpr h), ih1, hd, List.map_cons]
    · simp only [upP, if_neg h, if_neg (mt (sib_shift c x.1 y.1).mp h), ih2, hd, List.map_cons]

/-- The digests that a level reads off the paths split over two lists with no siblings across
them. -/
theorem reads1_append : ∀ (X Y : List (ℕ × List D)), (∀ a ∈ X, ∀ b ∈ Y, ¬ sib a.1 b.1) →
    reads1 (X ++ Y) = reads1 X ++ reads1 Y
  | [], _, _ => rfl
  | [_], [], _ => rfl
  | [x], y :: Y, h => by
    have hn : ¬ sib x.1 y.1 := h x (by simp) y (by simp)
    show reads1 (x :: y :: Y) = [x.2.headD default] ++ reads1 (y :: Y)
    rw [reads1, if_neg hn]
    rfl
  | x :: z :: X, Y, h => by
    have h1 : ∀ a ∈ X, ∀ b ∈ Y, ¬ sib a.1 b.1 := fun a ha => h a (by simp [ha])
    have h2 : ∀ a ∈ z :: X, ∀ b ∈ Y, ¬ sib a.1 b.1 :=
      fun a ha => h a (List.mem_cons_of_mem _ ha)
    have ih1 := reads1_append X Y h1
    have ih2 := reads1_append (z :: X) Y h2
    rw [List.cons_append] at ih2
    show reads1 (x :: z :: (X ++ Y)) = reads1 (x :: z :: X) ++ reads1 Y
    by_cases hs : sib x.1 z.1
    · simp only [reads1, if_pos hs, ih1]
    · simp only [reads1, if_neg hs, ih2, List.cons_append]

omit [Inhabited D] in
/-- The parents with their paths split over two lists with no siblings across them. -/
theorem upP_append : ∀ (X Y : List (ℕ × List D)), (∀ a ∈ X, ∀ b ∈ Y, ¬ sib a.1 b.1) →
    upP (X ++ Y) = upP X ++ upP Y
  | [], _, _ => rfl
  | [_], [], _ => rfl
  | [x], y :: Y, h => by
    have hn : ¬ sib x.1 y.1 := h x (by simp) y (by simp)
    show upP (x :: y :: Y) = [(x.1 / 2, x.2.tail)] ++ upP (y :: Y)
    rw [upP, if_neg hn]
    rfl
  | x :: z :: X, Y, h => by
    have h1 : ∀ a ∈ X, ∀ b ∈ Y, ¬ sib a.1 b.1 := fun a ha => h a (by simp [ha])
    have h2 : ∀ a ∈ z :: X, ∀ b ∈ Y, ¬ sib a.1 b.1 :=
      fun a ha => h a (List.mem_cons_of_mem _ ha)
    have ih1 := upP_append X Y h1
    have ih2 := upP_append (z :: X) Y h2
    rw [List.cons_append] at ih2
    show upP (x :: z :: (X ++ Y)) = upP (x :: z :: X) ++ upP Y
    by_cases hs : sib x.1 z.1
    · simp only [upP, if_pos hs, ih1, List.cons_append]
    · simp only [upP, if_neg hs, ih2, List.cons_append]

omit [Inhabited D] in
/-- There are no siblings across nodes below 2 c and nodes from 2 c on. -/
theorem not_sib_two (c : ℕ) (A B : List (ℕ × List D)) (h : ∀ x ∈ A, x.1 < 2 * c) :
    ∀ a ∈ A, ∀ b ∈ B.map (fun x => (2 * c + x.1, x.2)), ¬ sib a.1 b.1 := by
  intro a ha b hb
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hb
  exact not_sib_of_lt c a.1 y.1 (h a ha)

omit [Inhabited D] in
/-- The numbers of two lists laid one behind the other: the first's, then the second's with c
added. -/
theorem map_fst_two (c : ℕ) (A B : List (ℕ × List D)) :
    (A ++ B.map fun x => (c + x.1, x.2)).map (·.1) = A.map (·.1) ++ B.map (c + ·.1) := by
  rw [List.map_append, List.map_map]
  rfl

omit [Inhabited D] in
/-- The parents of nodes below 2 c lie below c. -/
theorem lt_upP (c : ℕ) (A : List (ℕ × List D)) (h : ∀ x ∈ A, x.1 < 2 * c) :
    ∀ x ∈ upP A, x.1 < c := by
  intro x hx
  have hm : x.1 ∈ up (A.map Prod.fst) := by
    rw [← map_fst_upP]
    exact List.mem_map_of_mem hx
  obtain ⟨k, hk, hk2⟩ := mem_up _ _ hm
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hk
  have := h a ha
  omega

variable (hN : D → D → D)

/-- One level over both trees is the two trees' levels side by side. -/
theorem stepF_two (c : ℕ) (A B : List (ℕ × List D)) (v0 v1 : List D)
    (h : ∀ x ∈ A, x.1 < 2 * c) (hv : v0.length = A.length) :
    stepF hN ((A ++ B.map fun x => (2 * c + x.1, x.2)).map (·.1)) (v0 ++ v1)
        (reads1 A ++ reads1 B) =
      stepF hN (A.map (·.1)) v0 (reads1 A) ++ stepF hN (B.map (·.1)) v1 (reads1 B) := by
  have e : (A ++ B.map fun x => (2 * c + x.1, x.2)).map (·.1) =
      A.map (·.1) ++ (B.map (·.1)).map (2 * c + ·) := by
    rw [List.map_append, List.map_map, List.map_map]
    rfl
  have hn : ∀ i ∈ A.map (·.1), ∀ j ∈ (B.map (·.1)).map (2 * c + ·), ¬ sib i j := by
    intro i hi j hj
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hj
    exact not_sib_of_lt c a.1 y (h a ha)
  rw [e, stepF_append hN _ _ _ _ _ _ (by rw [hv, List.length_map]) (length_reads1 A) hn,
    stepF_shift]

/-- The walk of depth d + 1 on the digests read off whole paths is one level,
then the walk of depth d. -/
theorem octF_succ_reads (d : ℕ) (l : List (ℕ × List D)) (v : List D) :
    octF hN (d + 1) (l.map (·.1)) v (reads (d + 1) l) =
      octF hN d ((upP l).map (·.1)) (stepF hN (l.map (·.1)) v (reads1 l)) (reads d (upP l)) := by
  have e : octF hN (d + 1) (l.map (·.1)) v (reads (d + 1) l) =
      octF hN d (up (l.map (·.1))) (stepF hN (l.map (·.1)) v (reads (d + 1) l))
        ((reads (d + 1) l).drop (need1 (l.map (·.1)))) := rfl
  rw [e, reads, stepF_take hN _ _ _ _ (length_reads1 l), List.drop_left' (length_reads1 l)]
  exact congrArg (fun js => octF hN d js _ _) (map_fst_upP l).symm

/-- The same as `octF_two` below, with the numbers read off the list of paths. -/
theorem octF_two_paths : ∀ (d : ℕ) (l0 l1 : List (ℕ × List D)) (v0 v1 : List D),
    (∀ x ∈ l0, x.1 < 2 ^ d) → v0.length = l0.length →
    octF hN d ((l0 ++ l1.map fun (x : ℕ × List D) => (2 ^ d + x.1, x.2)).map (·.1)) (v0 ++ v1)
        (reads d (l0 ++ l1.map fun x => (2 ^ d + x.1, x.2))) =
      octF hN d (l0.map (·.1)) v0 (reads d l0) ++ octF hN d (l1.map (·.1)) v1 (reads d l1)
  | 0, _, _, _, _, _, _ => rfl
  | d + 1, l0, l1, v0, v1, h0, hv => by
    have hp : 2 ^ (d + 1) = 2 * 2 ^ d := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hp] at h0 ⊢
    rw [octF_succ_reads, octF_succ_reads, octF_succ_reads,
      upP_append _ _ (not_sib_two _ l0 l1 h0), upP_shift,
      reads1_append _ _ (not_sib_two _ l0 l1 h0), reads1_shift, stepF_two hN _ _ _ _ _ h0 hv]
    refine octF_two_paths d (upP l0) (upP l1) _ _ (lt_upP _ l0 h0) ?_
    rw [length_stepF, ← List.length_map (f := Prod.fst) (as := upP l0), map_fst_upP]

/-- The walk over a forest of two trees of one depth, on the digests read off whole paths, is the
two trees' walks side by side. l0 and l1 hold the nodes of the two trees with their paths; v0 and v1
hold the nodes' digests. The first tree's nodes are below 2^d, and v0 is as long as l0. -/
theorem octF_two (d : ℕ) (l0 l1 : List (ℕ × List D)) (v0 v1 : List D)
    (h0 : ∀ x ∈ l0, x.1 < 2 ^ d) (hv : v0.length = l0.length) :
    octF hN d (l0.map (·.1) ++ l1.map (2 ^ d + ·.1)) (v0 ++ v1)
        (reads d (l0 ++ l1.map fun x => (2 ^ d + x.1, x.2))) =
      octF hN d (l0.map (·.1)) v0 (reads d l0) ++ octF hN d (l1.map (·.1)) v1 (reads d l1) := by
  rw [← map_fst_two]
  exact octF_two_paths hN d l0 l1 v0 v1 h0 hv

omit [Inhabited D] in
/-- The numbers in which the walk over both trees ends are the first tree's, then the second tree's
with 1 added, if the first tree's nodes are below 2^d. -/
theorem upN_two (d : ℕ) (l0 l1 : List (ℕ × List D)) (h0 : ∀ x ∈ l0, x.1 < 2 ^ d) :
    upN d (l0.map (·.1) ++ l1.map (2 ^ d + ·.1)) =
      upN d (l0.map (·.1)) ++ (upN d (l1.map (·.1))).map (1 + ·) := by
  have e : l1.map (2 ^ d + ·.1) = (l1.map (·.1)).map (2 ^ d + ·) := by
    rw [List.map_map]
    rfl
  rw [e]
  refine upN_append d _ _ ?_
  intro i hi
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
  exact h0 a ha

end Paths

end OnBytes.Tie

#print axioms OnBytes.Tie.octF_two
#print axioms OnBytes.Tie.upN_two
