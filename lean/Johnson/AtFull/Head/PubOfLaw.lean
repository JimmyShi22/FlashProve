-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Head/PubOfLaw.lean: the counts of padding keys of the output head's lookup
(Head.pubOf, OnBytes/Model/HeadLayout.lean): where its one test on each call passes, and no segment
has an entry behind the vocabulary, it returns; what it returns is a fold of folds; and the counts
lie under a bound made of a few numbers a call. General laws: nothing is evaluated. No sub-protocol
imports this file.
  forIn_ok          a loop in Except whose body always goes on is a fold
  addCols           what one call adds: T at the tree of each of its columns that no segment takes
  pubOf_eq          pubOf = .ok (the fold of addCols over the calls), under H1 (the test on each
                    call) and H2 (each of the five segments with one entry a vocabulary entry has
                    none behind the vocabulary: the second inner loop is empty)
  fold_adds · calls_add   such folds keep the size and add sums
  colsAt            what one call adds at one tree, as a sum · colsAt_out | colsAt_le | colsAt_lt
  bdH               the bound on it: a whole tree's keys at each of the call's trees, less one
                    column's at tree number t · bd_le: where column p is taken, at t := p / M
  choices bs        all lists of numbers below the members of bs
  vH                the bound on a tree's count, at one list of such t
  pub_le            the fold's size, and: some list of choices bounds all its counts
Called, not typed: block_le | block_lt | sum_zero (the law file
Johnson/Unfolds/Count.lean) · pub_step (Johnson/Road/FormsKeysPub.lean).
Limits. Which tree holds a taken column is not said: hence the choices. No soundness is claimed. On
hiding nothing.
-/
import OnBytes.Model.HeadLayout
import Johnson.Unfolds.Count

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.Head
open OnBytes OnBytes.Model OnBytes.Model.Head
open Johnson.Unfolds (sum_zero block_le block_lt)

/-- A loop whose body always goes on is a fold. -/
theorem forIn_ok {α β : Type} (body : α → β → Except String (ForInStep β)) (g : α → β → β) :
    ∀ (l : List α) (init : β), (∀ a ∈ l, ∀ b, body a b = .ok (.yield (g a b))) →
      forIn l init body = .ok (l.foldl (fun b a => g a b) init)
  | [], _, _ => rfl
  | a :: l, init, h => by
    rw [List.forIn_cons, h a (List.mem_cons_self ..)]
    exact forIn_ok body g l _ fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- What one call adds. -/
def addCols (T cs base : Nat) (cd : CallD) (pub : Array Nat) : Array Nat :=
  (List.range cd.J).foldl
    (fun r j => if (cd.used.getD j 0 == 0) = true then r.modify (base + j / 2 ^ cs) (· + T) else r)
    pub

theorem foldl_id {α β : Type} : ∀ (l : List α) (b : β), l.foldl (fun b _ => b) b = b
  | [], _ => rfl
  | _ :: l, b => foldl_id l b

/-- **pubOf is a fold of folds.** -/
theorem pubOf_eq (h : Shape) (L : HL) (fs : Forest.Shape) (calls : List CallD)
    (H1 : ∀ x ∈ calls.zipIdx, (x.1.J / 2 ^ (fs.dT - h.lt) == 2 ^ fs.iota.getD x.2 0) = true)
    (H2 : ∀ x ∈ calls.zipIdx, ∀ g ∈ x.1.segs, perEntry g.name = true →
      g.n - (h.V - firstEntry L g.name) = 0) :
    pubOf h L fs calls = .ok (calls.zipIdx.foldl
      (fun pub x => addCols h.T (fs.dT - h.lt) (fs.first.getD x.2 0) x.1 pub)
      (Array.replicate fs.NT 0)) := by
  unfold pubOf
  dsimp only
  rw [forIn_ok _ (fun x pub => addCols h.T (fs.dT - h.lt) (fs.first.getD x.2 0) x.1 pub)]
  · rfl
  · rintro ⟨cd, q⟩ hx r
    dsimp only
    have n1 : needed (cd.J / 2 ^ (fs.dT - h.lt) == 2 ^ fs.iota.getD q 0) "internal-forest-place" =
        .ok () := by
      unfold needed
      rw [if_pos (H1 _ hx)]
    rw [n1]
    show ((forIn (List.range cd.J) r _ : Except String (Array Nat)) >>= _) = _
    rw [forIn_ok _ (fun j r => if (cd.used.getD j 0 == 0) = true then
      r.modify (fs.first.getD q 0 + j / 2 ^ (fs.dT - h.lt)) (· + h.T) else r) (List.range cd.J)]
    · show ((forIn cd.segs _ _ : Except String (Array Nat)) >>= _) = _
      rw [forIn_ok _ (fun _ r => r) cd.segs]
      · rw [foldl_id]
        rfl
      · intro g hg b
        by_cases hp : perEntry g.name = true
        · rw [if_pos hp, H2 _ hx g hg hp]
          rfl
        · rw [if_neg hp]
          rfl
    · intro j _ b
      split <;> rfl

/-- Such a fold keeps the size and adds a sum. -/
theorem fold_adds (P : Nat → Bool) (ix : Nat → Nat) (T n : Nat) :
    ∀ (l : List Nat) (pub : Array Nat), pub.size = n →
      (l.foldl (fun r j => if P j = true then r.modify (ix j) (· + T) else r) pub).size = n ∧
      ∀ θ, θ < n →
        (l.foldl (fun r j => if P j = true then r.modify (ix j) (· + T) else r) pub).getD θ 0 =
          pub.getD θ 0 + (l.map fun j => if P j = true ∧ ix j = θ then T else 0).sum
  | [], pub, hs => ⟨hs, fun θ _ => by simp⟩
  | j :: l, pub, hs => by
    rw [List.foldl_cons]
    obtain ⟨s1, a1⟩ := OnBytes.Road.pub_step (P j) false (ix j) T n "" pub
      (if P j = true then pub.modify (ix j) (· + T) else pub) hs (by
        by_cases hP : P j = true
        · rw [if_pos hP, if_pos hP]
          rfl
        · rw [if_neg hP, if_neg hP]
          rfl)
    obtain ⟨s2, a2⟩ := fold_adds P ix T n l _ s1
    refine ⟨s2, fun θ hθ => ?_⟩
    rw [a2 θ hθ, a1 θ hθ, List.map_cons, List.sum_cons]
    omega

/-- What one call adds at one tree. -/
def colsAt (T cs base : Nat) (cd : CallD) (θ : Nat) : Nat :=
  ((List.range cd.J).map fun j =>
    if (cd.used.getD j 0 == 0) = true ∧ base + j / 2 ^ cs = θ then T else 0).sum

theorem addCols_adds (T cs base n : Nat) (cd : CallD) (pub : Array Nat) (hs : pub.size = n) :
    (addCols T cs base cd pub).size = n ∧ ∀ θ, θ < n →
      (addCols T cs base cd pub).getD θ 0 = pub.getD θ 0 + colsAt T cs base cd θ :=
  fold_adds (fun j => cd.used.getD j 0 == 0) (fun j => base + j / 2 ^ cs) T n _ pub hs

/-- The outer fold. -/
theorem calls_add {α : Type} (F : α → Array Nat → Array Nat) (A : α → Nat → Nat) (n : Nat)
    (hF : ∀ x pub, pub.size = n → (F x pub).size = n ∧
      ∀ θ, θ < n → (F x pub).getD θ 0 = pub.getD θ 0 + A x θ) :
    ∀ (l : List α) (pub : Array Nat), pub.size = n →
      (l.foldl (fun pub x => F x pub) pub).size = n ∧ ∀ θ, θ < n →
        (l.foldl (fun pub x => F x pub) pub).getD θ 0 = pub.getD θ 0 + (l.map fun x => A x θ).sum
  | [], pub, hs => ⟨hs, fun θ _ => by simp⟩
  | x :: l, pub, hs => by
    rw [List.foldl_cons]
    obtain ⟨s1, a1⟩ := hF x pub hs
    obtain ⟨s2, a2⟩ := calls_add F A n hF l _ s1
    refine ⟨s2, fun θ hθ => ?_⟩
    rw [a2 θ hθ, a1 θ hθ, List.map_cons, List.sum_cons]
    omega

theorem colsAt_in (T cs base : Nat) (cd : CallD) (t : Nat) : colsAt T cs base cd (base + t) =
    ((List.range cd.J).map fun j =>
      if (cd.used.getD j 0 == 0) = true ∧ j / 2 ^ cs = t then T else 0).sum := by
  unfold colsAt
  congr 1
  refine List.map_congr_left fun x _ => ?_
  simp only [Nat.add_left_cancel_iff]

theorem colsAt_out (T cs base : Nat) (cd : CallD) {A θ : Nat} (hfit : cd.J ≤ 2 ^ cs * A)
    (hθ : θ < base ∨ base + A ≤ θ) : colsAt T cs base cd θ = 0 := by
  unfold colsAt
  refine sum_zero _ _ fun x hx => ?_
  have hd : x / 2 ^ cs < A :=
    Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_le (List.mem_range.1 hx) hfit)
  rw [if_neg]
  rintro ⟨_, e⟩
  generalize x / 2 ^ cs = d at hd e
  omega

theorem colsAt_le (T cs base : Nat) (cd : CallD) (t : Nat) :
    colsAt T cs base cd (base + t) ≤ 2 ^ cs * T := by
  rw [colsAt_in]
  refine Nat.le_trans (block_le (fun j => cd.used.getD j 0 == 0) T (2 ^ cs) t
    (Nat.two_pow_pos _) _) (Nat.mul_le_mul_right _ ?_)
  generalize 2 ^ cs = M
  generalize t * M = a
  omega

theorem colsAt_lt (T cs base : Nat) (cd : CallD) {p : Nat} (hp : p < cd.J)
    (h0 : (cd.used.getD p 0 == 0) = false) :
    colsAt T cs base cd (base + p / 2 ^ cs) + T ≤ 2 ^ cs * T := by
  rw [colsAt_in]
  have k := block_lt (fun j => cd.used.getD j 0 == 0) T (2 ^ cs) (p / 2 ^ cs) p
    (Nat.two_pow_pos _) h0 rfl cd.J
  rw [if_pos hp] at k
  refine Nat.le_trans k (Nat.mul_le_mul_right _ ?_)
  generalize 2 ^ cs = M
  generalize p / M * M = a
  omega

/-- The bound on what one call adds at one tree; t: the number, among the call's trees, of one that
holds a taken column. -/
def bdH (T cs : Nat) (fs : Forest.Shape) (q t θ : Nat) : Nat :=
  if fs.first.getD q 0 ≤ θ ∧ θ < fs.first.getD q 0 + 2 ^ fs.iota.getD q 0 then
    (if θ = fs.first.getD q 0 + t then 2 ^ cs * T - T else 2 ^ cs * T)
  else 0

theorem bd_le (T cs : Nat) (fs : Forest.Shape) (cd : CallD) (q : Nat)
    (hJ : cd.J ≤ 2 ^ cs * 2 ^ fs.iota.getD q 0) {p : Nat} (hp : p < cd.J)
    (h0 : (cd.used.getD p 0 == 0) = false) (θ : Nat) :
    colsAt T cs (fs.first.getD q 0) cd θ ≤ bdH T cs fs q (p / 2 ^ cs) θ := by
  unfold bdH
  by_cases hin : fs.first.getD q 0 ≤ θ ∧ θ < fs.first.getD q 0 + 2 ^ fs.iota.getD q 0
  · rw [if_pos hin]
    obtain ⟨t, rfl⟩ : ∃ t, θ = fs.first.getD q 0 + t := ⟨θ - fs.first.getD q 0, by omega⟩
    by_cases ht : fs.first.getD q 0 + t = fs.first.getD q 0 + p / 2 ^ cs
    · rw [if_pos ht, ht]
      exact Nat.le_sub_of_add_le (colsAt_lt T cs _ cd hp h0)
    · rw [if_neg ht]
      exact colsAt_le T cs _ cd t
  · rw [if_neg hin, colsAt_out T cs _ cd hJ (by omega)]

/-- All lists of numbers below the members of bs. -/
def choices : List Nat → List (List Nat)
  | [] => [[]]
  | b :: bs => (List.range b).flatMap fun t => (choices bs).map (t :: ·)

/-- The bound on a tree's count, at one list of choices; k: the number of the first call. -/
def vH (T cs : Nat) (fs : Forest.Shape) : Nat → List Nat → Nat → Nat
  | _, [], _ => 0
  | k, t :: ts, θ => bdH T cs fs k t θ + vH T cs fs (k + 1) ts θ

/-- Some list of choices bounds the sums. -/
theorem sums_le (T cs : Nat) (fs : Forest.Shape) : ∀ (l : List CallD) (k : Nat),
    (∀ x ∈ l.zipIdx k, x.1.J ≤ 2 ^ cs * 2 ^ fs.iota.getD x.2 0 ∧
      ∃ p, p < x.1.J ∧ (x.1.used.getD p 0 == 0) = false) →
    ∃ ts ∈ choices ((l.zipIdx k).map fun x => 2 ^ fs.iota.getD x.2 0), ∀ θ,
      ((l.zipIdx k).map fun x => colsAt T cs (fs.first.getD x.2 0) x.1 θ).sum ≤ vH T cs fs k ts θ
  | [], _, _ => ⟨[], List.mem_singleton.2 rfl, fun _ => Nat.le_refl _⟩
  | cd :: l, k, h => by
    rw [List.zipIdx_cons] at h ⊢
    obtain ⟨hJ, p, hp, h0⟩ := h (cd, k) (List.mem_cons_self ..)
    obtain ⟨ts, hts, hb⟩ := sums_le T cs fs l (k + 1) fun x hx => h x (List.mem_cons_of_mem _ hx)
    refine ⟨p / 2 ^ cs :: ts, ?_, fun θ => ?_⟩
    · rw [List.map_cons]
      refine List.mem_flatMap.2 ⟨p / 2 ^ cs, List.mem_range.2 ?_, List.mem_map.2 ⟨ts, hts, rfl⟩⟩
      exact Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_le hp hJ)
    · rw [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (bd_le T cs fs cd k hJ hp h0 θ) (hb θ)

theorem getD_out {a : Array Nat} {θ n : Nat} (hs : a.size = n) (h : ¬ θ < n) : a.getD θ 0 = 0 := by
  simp [Array.getD, hs, h]

/-- **The counts lie under a bound.** -/
theorem pub_le (T cs : Nat) (fs : Forest.Shape) (calls : List CallD)
    (h : ∀ x ∈ calls.zipIdx, x.1.J ≤ 2 ^ cs * 2 ^ fs.iota.getD x.2 0 ∧
      ∃ p, p < x.1.J ∧ (x.1.used.getD p 0 == 0) = false) :
    (calls.zipIdx.foldl (fun pub x => addCols T cs (fs.first.getD x.2 0) x.1 pub)
      (Array.replicate fs.NT 0)).size = fs.NT ∧
    ∃ ts ∈ choices (calls.zipIdx.map fun x => 2 ^ fs.iota.getD x.2 0), ∀ θ,
      (calls.zipIdx.foldl (fun pub x => addCols T cs (fs.first.getD x.2 0) x.1 pub)
        (Array.replicate fs.NT 0)).getD θ 0 ≤ vH T cs fs 0 ts θ := by
  obtain ⟨s, f⟩ := calls_add
    (fun (x : CallD × Nat) pub => addCols T cs (fs.first.getD x.2 0) x.1 pub)
    (fun x θ => colsAt T cs (fs.first.getD x.2 0) x.1 θ) fs.NT
    (fun x pub hs => addCols_adds T cs _ fs.NT x.1 pub hs) calls.zipIdx
    (Array.replicate fs.NT 0) (by simp)
  obtain ⟨ts, hts, hb⟩ := sums_le T cs fs calls 0 h
  refine ⟨s, ts, hts, fun θ => ?_⟩
  by_cases hθ : θ < fs.NT
  · have z : (Array.replicate fs.NT 0).getD θ 0 = 0 := by simp [Array.getD]
    rw [f θ hθ, z, Nat.zero_add]
    exact hb θ
  · rw [getD_out s hθ]
    exact Nat.zero_le _

end AtFull.Head

#print axioms AtFull.Head.forIn_ok
#print axioms AtFull.Head.pubOf_eq
#print axioms AtFull.Head.fold_adds
#print axioms AtFull.Head.addCols_adds
#print axioms AtFull.Head.calls_add
#print axioms AtFull.Head.colsAt_out
#print axioms AtFull.Head.colsAt_le
#print axioms AtFull.Head.colsAt_lt
#print axioms AtFull.Head.bd_le
#print axioms AtFull.Head.sums_le
#print axioms AtFull.Head.pub_le
#print axioms AtFull.Head.foldl_id
#print axioms AtFull.Head.colsAt_in
#print axioms AtFull.Head.getD_out
