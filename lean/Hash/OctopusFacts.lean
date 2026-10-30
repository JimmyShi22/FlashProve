-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hash/OctopusFacts.lean: lemmas on pruned Merkle paths (Hash/Octopus.lean), without oracles: lengths,
pruning against filling, honest trees, and the count.

  Part 1  `length_reads`: the pruned paths have exactly need d js digests, whatever the paths are (a
          path that is too short is read as if padded).
  Part 2  `length_fill`, `length_of_mem_fill`, `reads_fill`: filling gives one path of d digests for
          each node, and pruning these paths gives back the first need d js digests of the message,
          if it has that many.
  Part 3  `complete`: honest trees pass. A tree is given by the function g from leaf numbers to leaf
          digests. On any list js of leaves, with their digests and the pruned form of their honest
          paths, the verification ends in the digests of level d at the numbers upN d js. No order
          and no bound is asked of js.
  Part 4  The count, for q leaves in strictly ascending order, all below n * 2^d (n trees of depth
          d). Full paths have q * d digests.
          `need1_add_length`, `countSharp`: need1 js + js.length = 2 * (up js).length, and the sum
          over the levels telescopes.
          `octMax d n Q`, `need_le_octMax`: the bound for at most Q leaves. It grows with Q (the
          number for exactly q leaves does not: with all leaves opened nothing is sent). At n = 1
          and 1 ≤ Q ≤ 2^(d - 1) it is Q (d - k) + 2^k - Q with k = ceil (log2 Q), the largest size
          of the pruned paths of Q leaves (both computed by hand, not proved here). 319 leaves at
          depth 24: 4,978 (`octMax_319_24`); full paths: 7,656.

Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).
Here:
`length_reads`, `reads_fill`, `complete`, `countSharp`, `need_le_octMax`.

Notation: `upG hN g`: the next level of the tree whose present level is g; `topG hN d g`: level d
above g; `hpath hN d g i`: the d siblings on the way up from node i of the level g; `stepF`, `octF`:
the joint verification for a pure hash function `hN`.

Limits: the count is an upper bound for the worst placement of the leaves, not the number for a
given set (that is need d js itself). Soundness of the verification needs a notion of a run:
Compile/OctopusRom.lean.
Against VCV-io's source (https://github.com/Verified-zkEVM/VCV-io) at commit afa6593f:
"VCV-io,
VCVio/CryptoFoundations/MerkleTree/Addressed/NatIndexed.lean, an identical one-line sibling index
and the same standard heap numbering of a perfect Merkle tree."
lean/CREDITS.md has VCV-io's entry.
-/
import Hash.Octopus
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.Range
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Octopus

/-! ## Part 1. Lengths -/

section Lengths
variable {D : Type} [Inhabited D]

theorem length_reads1 : ∀ l : List (ℕ × List D), (reads1 l).length = need1 (l.map Prod.fst)
  | [] => rfl
  | [_] => rfl
  | x :: y :: l => by
      simp only [reads1, List.map_cons, need1]
      split_ifs
      · exact length_reads1 l
      · rw [List.length_cons, length_reads1 (y :: l), List.map_cons, Nat.add_comm]

omit [Inhabited D] in
theorem map_fst_upP : ∀ l : List (ℕ × List D), (upP l).map Prod.fst = up (l.map Prod.fst)
  | [] => rfl
  | [_] => rfl
  | x :: y :: l => by
      simp only [upP, List.map_cons, up]
      split_ifs
      · rw [List.map_cons, map_fst_upP l]
      · rw [List.map_cons, map_fst_upP (y :: l), List.map_cons]

def Spec.length_reads : Prop :=
  ∀ (D : Type) [Inhabited D] (d : ℕ) (l : List (ℕ × List D)),
    (reads d l).length = need d (l.map Prod.fst)

/-- The pruned paths have exactly need d js digests. -/
theorem length_reads : Spec.length_reads := by
  intro D _ d
  induction d with
  | zero => exact fun _ => rfl
  | succ d ih =>
    intro l
    rw [reads, need, List.length_append, length_reads1, ih, map_fst_upP]

end Lengths

/-! ## Part 2. Filling -/

section Fill
variable {D : Type} [Inhabited D]

theorem length_fill1 (d : ℕ) :
    ∀ (js : List ℕ) (s : List D) (r : List (List D)), (fill1 d js s r).length = js.length
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | i :: j :: l, s, r => by
      simp only [fill1]
      split_ifs
      · simp only [List.length_cons, length_fill1 d l]
      · simp only [List.length_cons, length_fill1 d (j :: l)]

theorem length_fill : ∀ (d : ℕ) (js : List ℕ) (s : List D), (fill d js s).length = js.length
  | 0, js, _ => by simp [fill]
  | d + 1, js, s => length_fill1 d js s _

theorem length_of_mem_fill1 (d : ℕ) :
    ∀ (js : List ℕ) (s : List D) (r : List (List D)),
      r.length = (up js).length → (∀ q ∈ r, q.length = d) → ∀ q ∈ fill1 d js s r, q.length = d + 1
  | [], _, _, _, _, q, hq => by cases hq
  | [_], s, r, hl, hr, q, hq => by
      match r, hl with
      | [a], _ =>
        simp only [fill1, List.mem_singleton] at hq
        subst hq
        simp [hr a (by simp)]
  | i :: j :: l, s, r, hl, hr, q, hq => by
      simp only [fill1] at hq
      simp only [up] at hl
      split_ifs at hq hl with h
      · match r, hl with
        | a :: r', hl =>
          simp only [List.mem_cons, List.headD_cons, List.tail_cons] at hq
          rcases hq with rfl | rfl | hq
          · simp [hr a (by simp)]
          · simp
          · exact length_of_mem_fill1 d l s r' (by simpa using hl)
              (fun q hq => hr q (List.mem_cons_of_mem _ hq)) q hq
      · match r, hl with
        | a :: r', hl =>
          simp only [List.mem_cons, List.headD_cons, List.tail_cons] at hq
          rcases hq with rfl | hq
          · simp [hr a (by simp)]
          · exact length_of_mem_fill1 d (j :: l) s.tail r' (by simpa using hl)
              (fun q hq => hr q (List.mem_cons_of_mem _ hq)) q hq

/-- every path that filling makes has d digests -/
theorem length_of_mem_fill : ∀ (d : ℕ) (js : List ℕ) (s : List D), ∀ q ∈ fill d js s, q.length = d
  | 0, js, _, q, hq => by
      simp only [fill, List.mem_map] at hq
      obtain ⟨_, _, rfl⟩ := hq
      rfl
  | d + 1, js, s, q, hq =>
    length_of_mem_fill1 d js s _ (length_fill d _ _) (length_of_mem_fill d _ _) q hq

theorem reads1_fill1 (d : ℕ) :
    ∀ (js : List ℕ) (s : List D) (r : List (List D)),
      need1 js ≤ s.length → reads1 (js.zip (fill1 d js s r)) = s.take (need1 js)
  | [], _, _, _ => by simp [reads1, need1]
  | [_], s, r, h => by
      match s, h with
      | [], h => simp [need1] at h
      | a :: s', _ => simp [reads1, need1, fill1]
  | i :: j :: l, s, r, h => by
      simp only [need1] at h ⊢
      simp only [fill1]
      split_ifs at h ⊢ with hs
      · simp only [List.zip_cons_cons, reads1, if_pos hs]
        exact reads1_fill1 d l s r.tail h
      · match s, h with
        | [], h => simp only [List.length_nil] at h; omega
        | a :: s', h =>
          have h' : need1 (j :: l) ≤ s'.length := by simp only [List.length_cons] at h; omega
          obtain ⟨q, t, hq⟩ : ∃ q t, fill1 d (j :: l) s' r.tail = q :: t := by
            have := length_fill1 d (j :: l) s' r.tail
            match hf : fill1 d (j :: l) s' r.tail, this with
            | q :: t, _ => exact ⟨q, t, rfl⟩
          have ih := reads1_fill1 d (j :: l) s' r.tail h'
          simp only [List.tail_cons, List.headD_cons]
          rw [hq] at ih ⊢
          simp only [List.zip_cons_cons] at ih ⊢
          simp only [reads1, if_neg hs, List.headD_cons]
          rw [ih, Nat.add_comm 1, List.take_succ_cons]

theorem upP_fill1 (d : ℕ) :
    ∀ (js : List ℕ) (s : List D) (r : List (List D)),
      r.length = (up js).length → upP (js.zip (fill1 d js s r)) = (up js).zip r
  | [], _, r, _ => by simp [upP, up]
  | [_], s, r, hl => by
      match r, hl with
      | [a], _ => simp [upP, up, fill1]
  | i :: j :: l, s, r, hl => by
      simp only [up] at hl ⊢
      simp only [fill1]
      split_ifs at hl ⊢ with hs
      · match r, hl with
        | a :: r', hl =>
          simp only [List.zip_cons_cons, upP, if_pos hs, List.headD_cons, List.tail_cons]
          rw [upP_fill1 d l s r' (by simpa using hl)]
      · match r, hl with
        | a :: r', hl =>
          obtain ⟨q, t, hq⟩ : ∃ q t, fill1 d (j :: l) s.tail r' = q :: t := by
            have := length_fill1 d (j :: l) s.tail r'
            match hf : fill1 d (j :: l) s.tail r', this with
            | q :: t, _ => exact ⟨q, t, rfl⟩
          have ih := upP_fill1 d (j :: l) s.tail r' (by simpa using hl)
          simp only [List.tail_cons, List.headD_cons]
          rw [hq] at ih ⊢
          simp only [List.zip_cons_cons] at ih ⊢
          simp only [upP, if_neg hs, List.tail_cons]
          rw [ih]

def Spec.reads_fill : Prop :=
  ∀ (D : Type) [Inhabited D] (d : ℕ) (js : List ℕ) (s : List D),
    need d js ≤ s.length → reads d (js.zip (fill d js s)) = s.take (need d js)

/-- Pruning the filled paths gives back the first need d js digests of the message, if it has that
many. -/
theorem reads_fill : Spec.reads_fill := by
  intro D _ d
  induction d with
  | zero => intro js s _; simp [reads, need]
  | succ d ih =>
    intro js s h
    rw [need] at h ⊢
    rw [reads, fill, reads1_fill1 d js s _ (by omega), upP_fill1 d js s _ (length_fill d _ _),
      ih (up js) (s.drop (need1 js)) (by rw [List.length_drop]; omega), List.take_add]

end Fill

/-! ## Part 3. Honest trees pass -/

section Honest
variable {D : Type} [Inhabited D] (hN : D → D → D)

/-- the next level of the tree whose present level is g -/
def upG (g : ℕ → D) : ℕ → D := fun i => hN (g (2 * i)) (g (2 * i + 1))

/-- level d above g -/
def topG : ℕ → (ℕ → D) → ℕ → D
  | 0, g => g
  | d + 1, g => topG d (upG hN g)

/-- the number of the sibling -/
def sibOf (i : ℕ) : ℕ := if i % 2 = 0 then i + 1 else i - 1

/-- the d siblings on the way up from node i of the level g -/
def hpath : ℕ → (ℕ → D) → ℕ → List D
  | 0, _, _ => []
  | d + 1, g, i => g (sibOf i) :: hpath d (upG hN g) (i / 2)

/-- the joint verification for a pure hash function `hN` -/
def stepF : List ℕ → List D → List D → List D := stepC (M := Id) hN
@[inherit_doc stepF] def octF : ℕ → List ℕ → List D → List D → List D := octC (M := Id) hN

/-- `lone` for a pure hash function -/
def loneF (i : ℕ) (a s : D) : D := if i % 2 = 0 then hN a s else hN s a

omit [Inhabited D] in
theorem lone_honest (g : ℕ → D) (i : ℕ) : loneF hN i (g i) (g (sibOf i)) = upG hN g (i / 2) := by
  unfold loneF sibOf upG
  by_cases h : i % 2 = 0
  · have e : 2 * (i / 2) = i := by omega
    rw [if_pos h, if_pos h, e]
  · have e : 2 * (i / 2) + 1 = i := by omega
    have e' : 2 * (i / 2) = i - 1 := by omega
    rw [if_neg h, if_neg h, e, e']

theorem stepF_honest (d : ℕ) (g : ℕ → D) :
    ∀ (js : List ℕ) (e : List D),
      stepF hN js (js.map g) (reads1 (js.map fun j => (j, hpath hN (d + 1) g j)) ++ e) =
        (up js).map (upG hN g)
  | [], _ => rfl
  | [i], e => by
      show [loneF hN i (g i) (g (sibOf i))] = _
      rw [lone_honest]; rfl
  | i :: j :: l, e => by
      by_cases hs : sib i j
      · have ih := stepF_honest d g l e
        have e1 : stepF hN (i :: j :: l) ((i :: j :: l).map g)
              (reads1 ((i :: j :: l).map fun j => (j, hpath hN (d + 1) g j)) ++ e) =
            hN (g i) (g j) ::
              stepF hN l (l.map g) (reads1 (l.map fun j => (j, hpath hN (d + 1) g j)) ++ e) := by
          simp only [stepF, stepC, List.map_cons, reads1, if_pos hs]
          rfl
        rw [e1, ih]
        simp only [up, if_pos hs, List.map_cons]
        congr 1
        obtain ⟨h1, rfl⟩ := hs
        have e2 : 2 * (i / 2) = i := by omega
        unfold upG
        rw [e2]
      · have ih := stepF_honest d g (j :: l) e
        have e1 : stepF hN (i :: j :: l) ((i :: j :: l).map g)
              (reads1 ((i :: j :: l).map fun j => (j, hpath hN (d + 1) g j)) ++ e) =
            loneF hN i (g i) (g (sibOf i)) ::
              stepF hN (j :: l) ((j :: l).map g)
                (reads1 ((j :: l).map fun j => (j, hpath hN (d + 1) g j)) ++ e) := by
          simp only [stepF, stepC, List.map_cons, reads1, if_neg hs]
          rfl
        rw [e1, ih, lone_honest]
        simp only [up, if_neg hs, List.map_cons]

omit [Inhabited D] in
theorem upP_honest (d : ℕ) (g : ℕ → D) :
    ∀ js : List ℕ, upP (js.map fun j => (j, hpath hN (d + 1) g j)) =
      (up js).map fun j => (j, hpath hN d (upG hN g) j)
  | [] => rfl
  | [_] => rfl
  | i :: j :: l => by
      by_cases hs : sib i j
      · simp only [List.map_cons, upP, up, if_pos hs, upP_honest d g l]
        rfl
      · have ih := upP_honest d g (j :: l)
        simp only [List.map_cons] at ih
        simp only [List.map_cons, upP, up, if_neg hs, ih]
        rfl

def Spec.complete : Prop :=
  ∀ (D : Type) [Inhabited D] (hN : D → D → D) (d : ℕ) (g : ℕ → D) (js : List ℕ),
    octF hN d js (js.map g) (reads d (js.map fun j => (j, hpath hN d g j))) =
      (upN d js).map (topG hN d g)

/-- Honest trees pass: with the pruned form of the honest paths the verification ends in the digests
of level d. -/
theorem complete : Spec.complete := by
  intro D _ hN d
  induction d with
  | zero => exact fun _ _ => rfl
  | succ d ih =>
    intro g js
    have e : octF hN (d + 1) js (js.map g)
          (reads (d + 1) (js.map fun j => (j, hpath hN (d + 1) g j))) =
        octF hN d (up js)
          (stepF hN js (js.map g) (reads (d + 1) (js.map fun j => (j, hpath hN (d + 1) g j))))
          ((reads (d + 1) (js.map fun j => (j, hpath hN (d + 1) g j))).drop (need1 js)) := rfl
    have hl : (reads1 (js.map fun j => (j, hpath hN (d + 1) g j))).length = need1 js := by
      rw [length_reads1, List.map_map]
      congr 1
      exact List.map_id' js
    rw [e, reads, stepF_honest, ← hl, List.drop_left, upP_honest, ih]
    rfl

end Honest

/-! ## Part 4. The count -/

theorem mem_up : ∀ (js : List ℕ) (x : ℕ), x ∈ up js → ∃ k ∈ js, x = k / 2
  | [], _, h => by cases h
  | [i], x, h => ⟨i, by simp, by simpa [up] using h⟩
  | i :: j :: l, x, h => by
      simp only [up] at h
      split_ifs at h
      · rcases List.mem_cons.1 h with rfl | h
        · exact ⟨i, by simp, rfl⟩
        · obtain ⟨k, hk, rfl⟩ := mem_up l x h
          exact ⟨k, by simp [hk], rfl⟩
      · rcases List.mem_cons.1 h with rfl | h
        · exact ⟨i, by simp, rfl⟩
        · obtain ⟨k, hk, rfl⟩ := mem_up (j :: l) x h
          exact ⟨k, List.mem_cons_of_mem _ hk, rfl⟩

theorem length_up_le : ∀ js : List ℕ, (up js).length ≤ js.length
  | [] => le_rfl
  | [_] => le_rfl
  | i :: j :: l => by
      simp only [up]
      split_ifs
      · have := length_up_le l
        simp only [List.length_cons]; omega
      · have := length_up_le (j :: l)
        simp only [List.length_cons] at this ⊢; omega

theorem need1_le : ∀ js : List ℕ, need1 js ≤ (up js).length
  | [] => le_rfl
  | [_] => le_rfl
  | i :: j :: l => by
      simp only [up, need1]
      split_ifs
      · have := need1_le l
        simp only [List.length_cons]; omega
      · have := need1_le (j :: l)
        simp only [List.length_cons]; omega

/-- the parents of a strictly ascending list are strictly ascending -/
theorem pairwise_up : ∀ js : List ℕ, js.Pairwise (· < ·) → (up js).Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | i :: j :: l, h => by
      obtain ⟨h1, h2⟩ := List.pairwise_cons.1 h
      obtain ⟨h3, h4⟩ := List.pairwise_cons.1 h2
      simp only [up]
      split_ifs with hs
      · refine List.pairwise_cons.2 ⟨fun x hx => ?_, pairwise_up l h4⟩
        obtain ⟨k, hk, rfl⟩ := mem_up l x hx
        have := h3 k hk
        obtain ⟨_, rfl⟩ := hs
        omega
      · refine List.pairwise_cons.2 ⟨fun x hx => ?_, pairwise_up (j :: l) h2⟩
        obtain ⟨k, hk, rfl⟩ := mem_up (j :: l) x hx
        have hij := h1 j (by simp)
        have hik := h1 k hk
        have hjk : j ≤ k := by
          rcases List.mem_cons.1 hk with rfl | hk
          · exact le_rfl
          · exact (h3 k hk).le
        unfold sib at hs
        omega

theorem length_le_of_pairwise
    {js : List ℕ} (h : js.Pairwise (· < ·)) {m : ℕ} (hm : ∀ j ∈ js, j < m) : js.length ≤ m := by
  have hn : js.Nodup := h.imp fun hab => Nat.ne_of_lt hab
  rw [← List.toFinset_card_of_nodup hn, ← Finset.card_range m]
  exact Finset.card_le_card fun j hj => Finset.mem_range.2 (hm j (List.mem_toFinset.1 hj))


/-- each parent has one child in the list and takes a digest, or two and takes none -/
theorem need1_add_length : ∀ js : List ℕ, need1 js + js.length = 2 * (up js).length
  | [] => rfl
  | [_] => rfl
  | i :: j :: l => by
      simp only [up, need1]
      split_ifs
      · have := need1_add_length l
        simp only [List.length_cons]; omega
      · have := need1_add_length (j :: l)
        simp only [List.length_cons] at this ⊢; omega

def Spec.countSharp : Prop :=
  ∀ (d n : ℕ) (js : List ℕ), js.Pairwise (· < ·) → (∀ j ∈ js, j < n * 2 ^ d) →
    need d js + js.length ≤
      (∑ l ∈ Finset.range d, min js.length (n * 2 ^ (d - l - 1))) + min js.length n

/-- The count. For js strictly ascending with all numbers below n * 2^d: need d js + q ≤ (sum over
l < d of min (q, n * 2^(d - l - 1))) + min (q, n), where q = js.length. -/
theorem countSharp : Spec.countSharp := by
  intro d n
  induction d with
  | zero =>
    intro js hp hb
    have : js.length ≤ n := length_le_of_pairwise hp (by simpa using hb)
    simp [need, this]
  | succ d ih =>
    intro js hp hb
    have hb' : ∀ j ∈ up js, j < n * 2 ^ d := by
      intro x hx
      obtain ⟨k, hk, rfl⟩ := mem_up js x hx
      have := hb k hk
      rw [pow_succ, ← Nat.mul_assoc] at this
      exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at this)
    have h0 := need1_add_length js
    have h1 : (up js).length ≤ min js.length (n * 2 ^ d) :=
      le_min (length_up_le js) (length_le_of_pairwise (pairwise_up js hp) hb')
    have h2 := ih (up js) (pairwise_up js hp) hb'
    have h3 : ∑ l ∈ Finset.range d, min (up js).length (n * 2 ^ (d - l - 1)) ≤
        ∑ l ∈ Finset.range d, min js.length (n * 2 ^ (d + 1 - (l + 1) - 1)) := by
      refine Finset.sum_le_sum fun l _ => ?_
      have e : d + 1 - (l + 1) - 1 = d - l - 1 := by omega
      rw [e]
      exact min_le_min_right _ (length_up_le js)
    have h4 : min (up js).length n ≤ min js.length n := min_le_min_right _ (length_up_le js)
    rw [need, Finset.sum_range_succ']
    have e0 : d + 1 - 0 - 1 = d := by omega
    rw [e0]
    omega

/-- The bound on the digests that a verification from at most Q leaves, in strictly ascending order,
of n trees of depth d takes (`need_le_octMax`). -/
def octMax (d n Q : ℕ) : ℕ := (∑ k ∈ Finset.range (d - 1), min Q (n * 2 ^ k)) + min Q n

theorem octMax_mono (d n : ℕ) {Q Q' : ℕ} (h : Q ≤ Q') : octMax d n Q ≤ octMax d n Q' :=
  Nat.add_le_add (Finset.sum_le_sum fun _ _ => min_le_min_right _ h) (min_le_min_right _ h)

theorem octMax_mono_depth {d d' : ℕ} (n Q : ℕ) (h : d ≤ d') : octMax d n Q ≤ octMax d' n Q :=
  Nat.add_le_add_right (Finset.sum_le_sum_of_subset
    (Finset.range_mono (Nat.sub_le_sub_right h 1))) _

/-- The bounds for two trees verified separately (depths d0, dJ; at most a, b leaves) add up to at
most the bound for a forest of two trees of the larger depth (at most a + b leaves). -/
theorem octMax_add_le (d0 dJ a b : ℕ) :
    octMax d0 1 a + octMax dJ 1 b ≤ octMax (max d0 dJ) 2 (a + b) := by
  refine le_trans
    (Nat.add_le_add (octMax_mono_depth 1 a (le_max_left d0 dJ))
      (octMax_mono_depth 1 b (le_max_right d0 dJ))) ?_
  have key : ∀ c : ℕ, min a (1 * c) + min b (1 * c) ≤ min (a + b) (2 * c) := by
    intro c
    have h1 := min_le_left a (1 * c)
    have h2 := min_le_left b (1 * c)
    have h3 := min_le_right a (1 * c)
    have h4 := min_le_right b (1 * c)
    exact le_min (by omega) (by omega)
  unfold octMax
  have hs : ∑ k ∈ Finset.range (max d0 dJ - 1), min a (1 * 2 ^ k) +
        ∑ k ∈ Finset.range (max d0 dJ - 1), min b (1 * 2 ^ k) ≤
      ∑ k ∈ Finset.range (max d0 dJ - 1), min (a + b) (2 * 2 ^ k) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun k _ => key (2 ^ k)
  have h1 := key 1
  simp only [Nat.mul_one] at h1
  omega

def Spec.need_le_octMax : Prop :=
  ∀ (d n Q : ℕ) (js : List ℕ),
    js.Pairwise (· < ·) → (∀ j ∈ js, j < n * 2 ^ d) → js.length ≤ Q → need d js ≤ octMax d n Q

theorem need_le_octMax : Spec.need_le_octMax := by
  intro d n Q js hp hb hQ
  refine le_trans ?_ (octMax_mono d n hQ)
  have h := countSharp d n js hp hb
  unfold octMax
  cases d with
  | zero => simp [need]
  | succ d =>
    rw [Finset.sum_range_succ'] at h
    have e0 : d + 1 - 0 - 1 = d := by omega
    rw [e0] at h
    have e1 : ∑ l ∈ Finset.range d, min js.length (n * 2 ^ (d + 1 - (l + 1) - 1)) =
        ∑ k ∈ Finset.range d, min js.length (n * 2 ^ k) := by
      rw [← Finset.sum_range_reflect (fun k => min js.length (n * 2 ^ k)) d]
      refine Finset.sum_congr rfl fun l hl => ?_
      have := Finset.mem_range.1 hl
      have e : d + 1 - (l + 1) - 1 = d - 1 - l := by omega
      rw [e]
    rw [e1] at h
    have h2 : min js.length (n * 2 ^ d) ≤ js.length := min_le_left _ _
    show need (d + 1) js ≤
      (∑ k ∈ Finset.range (d + 1 - 1), min js.length (n * 2 ^ k)) + min js.length n
    rw [Nat.add_sub_cancel]
    omega

/-- one leaf: a whole path -/
theorem need_singleton : ∀ (d j : ℕ), need d [j] = d
  | 0, _ => rfl
  | d + 1, j => by
      show 1 + need d [j / 2] = d + 1
      rw [need_singleton d, Nat.add_comm]

theorem octMax_319_24 : octMax 24 1 319 = 4978 := by decide +kernel

end Octopus
