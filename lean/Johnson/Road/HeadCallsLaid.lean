-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadCallsLaid.lean: what Johnson/Road/HeadSumMet.lean asks of the verifier's record of
the output head's lookup calls, shown of every layout that the verifier's function returns.

The verifier places the segments of a call in the call's columns by one rule (place in
OnBytes/Model/Calls.lean). When it forms a call's key vector it marks the columns that the segments
list, and refuses if a column is listed twice or lies outside the call (markColumns in
OnBytes/Model/HeadForms.lean). This file shows that the marking never refuses on the rule's own
placing, and two facts on names, lengths and kinds.

How the first is shown. The rule cuts the segments into pieces and lays the pieces one after the
other. So the pieces' ranges of columns rise without overlap (Ranged). A segment's list of columns
is made of the ranges of its own pieces in that order, so it rises strictly (Rising), and two
segments share no column, since their pieces are different ones (inPiece_apart). A marking of
columns that are all different, unmarked and inside the call goes through (fold_returns,
marks_returns).

Main definitions: NoShare, Ranged, Rising, InPiece, segAt.
Main theorems:
 - place_marks: for segments of lengths below 2^41 the marking of a placed call's columns returns.
 - marks_of_layout: so it returns for every call number of a layout that Head.layout returns.
 - segsFit_of_layout, hasAll_of_layout: at 2^10 positions, width 5,120, 202,048 tokens and five
   limbs such a layout has SegsFit and HasAll.
 - met_of_layout: so the hypotheses of next_token_of_calls (Johnson/Road/HeadSum.lean) are met
   together at every record whose layout Head.layout has returned for such a shape; the statement
   names the record.

What is not claimed. That Head.layout returns a layout for some shape is not shown here: a run holds
it at two examples (Johnson/Road/HeadRunK.lean). Nothing on what a verifier's
acceptance shows. The program does not import this file.
-/
import Johnson.Road.HeadSumMet
import Johnson.Road.HeadLaid
import Johnson.Road.FormsKeysPlace

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open OnBytes.Model (SegAsk topBit piecesOfSize piecesBelow columnsOf place)

/-! ## 1. A marking of columns that are apart goes through -/

/-- Marking the columns pos 0, ..., pos (n - 1), which lie within the array, bear no mark and are
all different: no step refuses. -/
theorem fold_returns (pos mk : ℕ → ℕ) :
    ∀ (n : ℕ) (w : Array ℕ), (∀ x, x < n → pos x < w.size) →
      (∀ x, x < n → w.getD (pos x) 0 = 0) → (∀ x x', x < x' → x' < n → pos x ≠ pos x') →
      ∃ w', (List.range n).foldlM (fun w x =>
        if pos x < w.size && w.getD (pos x) 1 == 0 then some (w.set! (pos x) (mk x)) else none)
        w = some w' ∧ w'.size = w.size
  | 0, w, _, _, _ => ⟨w, by simp, rfl⟩
  | n + 1, w, hs, hf, hi => by
    obtain ⟨w1, h1, s1⟩ := fold_returns pos mk n w (fun x hx => hs x (Nat.lt_succ_of_lt hx))
      (fun x hx => hf x (Nat.lt_succ_of_lt hx)) (fun x x' h h' => hi x x' h (Nat.lt_succ_of_lt h'))
    have c1 : pos n < w1.size := by
      rw [s1]
      exact hs n (Nat.lt_succ_self n)
    have c0 : w1.getD (pos n) 0 = 0 := by
      by_contra hne
      rcases fold_listed pos mk n w w1 h1 (pos n) hne with h5 | ⟨x, hx, hxj⟩
      · exact h5 (hf n (Nat.lt_succ_self n))
      · exact hi x n hx (Nat.lt_succ_self n) hxj.symm
    have c2 : w1[pos n] = 0 := by simpa [Array.getD, c1] using c0
    refine ⟨w1.set! (pos n) (mk n), ?_, ?_⟩
    · rw [List.range_succ, List.foldlM_append, h1]
      simp [c1, c2]
    · rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, s1]

/-- Two segments share no column. -/
def NoShare (g g' : Model.Seg) : Prop :=
  ∀ x, x < g.n → ∀ x', x' < g'.n → g.pos.getD x 0 ≠ g'.pos.getD x' 0

/-- The marking of the columns of a list of segments returns, if all listed columns lie within the
array and bear no mark, no segment lists a column twice, and no two segments share one. -/
theorem marks_returns {R : Model.Head.Run} :
    ∀ (l : List Model.Seg) (w : Array ℕ),
      (∀ g ∈ l, ∀ x, x < g.n → g.pos.getD x 0 < w.size) →
      (∀ g ∈ l, ∀ x, x < g.n → w.getD (g.pos.getD x 0) 0 = 0) →
      (∀ g ∈ l, ∀ x x', x < x' → x' < g.n → g.pos.getD x 0 ≠ g.pos.getD x' 0) →
      l.Pairwise NoShare →
      ∃ w', l.foldlM (fun w g => Model.Head.markColumns R w g) w = some w'
  | [], w, _, _, _, _ => ⟨w, by simp⟩
  | g :: l, w, hs, hf, hi, hp => by
    have hg : g ∈ g :: l := List.mem_cons.mpr (Or.inl rfl)
    obtain ⟨w1, h1, s1⟩ := fold_returns (fun x => g.pos.getD x 0)
      (fun x => if Model.Head.perEntry g.name && Model.Head.firstEntry R.L g.name + x ≥ R.h.V
        then 2 else 1) g.n w (hs g hg) (hf g hg) (hi g hg)
    have hm : Model.Head.markColumns R w g = some w1 := h1
    obtain ⟨hpg, hpl⟩ := List.pairwise_cons.mp hp
    obtain ⟨w', h2⟩ := marks_returns l w1
      (fun g' hg' x hx => by
        rw [s1]
        exact hs g' (List.mem_cons.mpr (Or.inr hg')) x hx)
      (fun g' hg' x hx => by
        by_contra hne
        rcases fold_listed _ _ g.n w w1 h1 _ hne with h5 | ⟨y, hy, hyj⟩
        · exact h5 (hf g' (List.mem_cons.mpr (Or.inr hg')) x hx)
        · exact hpg g' hg' y hy x hx hyj.symm)
      (fun g' hg' => hi g' (List.mem_cons.mpr (Or.inr hg'))) hpl
    refine ⟨w', ?_⟩
    rw [List.foldlM_cons, hm]
    exact h2

/-! ## 2. The pieces' ranges of columns rise -/

/-- The ranges of columns of a list of pieces (segment, exponent, first column) rise without overlap
from lo on and end at or before hi. -/
def Ranged : List (ℕ × ℕ × ℕ) → ℕ → ℕ → Prop
  | [], lo, hi => lo ≤ hi
  | p :: P, lo, hi => lo ≤ p.2.2 ∧ Ranged P (p.2.2 + 2 ^ p.2.1) hi

/-- The range of a list of pieces may begin earlier. -/
theorem ranged_lower : ∀ (P : List (ℕ × ℕ × ℕ)) (lo lo' hi : ℕ), Ranged P lo hi → lo' ≤ lo →
    Ranged P lo' hi
  | [], lo, lo', hi, h, h' => by
    simp only [Ranged] at h ⊢
    omega
  | p :: P, lo, lo', hi, h, h' => by
    simp only [Ranged] at h ⊢
    exact ⟨by omega, h.2⟩

/-- In a ranged list of pieces lo is at most hi. -/
theorem ranged_le : ∀ (P : List (ℕ × ℕ × ℕ)) (lo hi : ℕ), Ranged P lo hi → lo ≤ hi
  | [], lo, hi, h => by
    simp only [Ranged] at h
    exact h
  | p :: P, lo, hi, h => by
    simp only [Ranged] at h
    have k := ranged_le P _ hi h.2
    have hpos : 0 < 2 ^ p.2.1 := Nat.two_pow_pos _
    omega

/-- Two ranged lists, the second from where the first ends, make one. -/
theorem ranged_append : ∀ (P Q : List (ℕ × ℕ × ℕ)) (lo mid hi : ℕ), Ranged P lo mid →
    Ranged Q mid hi → Ranged (P ++ Q) lo hi
  | [], Q, lo, mid, hi, h1, h2 => by
    simp only [Ranged] at h1
    rw [List.nil_append]
    exact ranged_lower Q mid lo hi h2 h1
  | p :: P, Q, lo, mid, hi, h1, h2 => by
    simp only [Ranged] at h1
    rw [List.cons_append]
    simp only [Ranged]
    exact ⟨h1.1, ranged_append P Q _ mid hi h1.2 h2⟩

/-- A part of a ranged list is ranged between the same bounds. -/
theorem ranged_filter (f : ℕ × ℕ × ℕ → Bool) : ∀ (P : List (ℕ × ℕ × ℕ)) (lo hi : ℕ),
    Ranged P lo hi → Ranged (P.filter f) lo hi
  | [], lo, hi, h => by
    rw [List.filter_nil]
    exact h
  | p :: P, lo, hi, h => by
    simp only [Ranged] at h
    have ih := ranged_filter f P _ hi h.2
    have hpos : 0 < 2 ^ p.2.1 := Nat.two_pow_pos _
    by_cases hp : f p = true
    · rw [List.filter_cons_of_pos hp]
      simp only [Ranged]
      exact ⟨h.1, ih⟩
    · rw [List.filter_cons_of_neg hp]
      exact ranged_lower _ _ lo hi ih (by omega)

/-- Every piece's range lies between lo and hi. -/
theorem ranged_mem : ∀ (P : List (ℕ × ℕ × ℕ)) (lo hi : ℕ), Ranged P lo hi →
    ∀ q ∈ P, lo ≤ q.2.2 ∧ q.2.2 + 2 ^ q.2.1 ≤ hi
  | [], _, _, _, q, hq => by cases hq
  | p :: P, lo, hi, h, q, hq => by
    simp only [Ranged] at h
    rcases List.mem_cons.mp hq with e | hq'
    · subst e
      exact ⟨h.1, ranged_le P _ hi h.2⟩
    · have k := ranged_mem P _ hi h.2 q hq'
      have hpos : 0 < 2 ^ p.2.1 := Nat.two_pow_pos _
      exact ⟨by omega, k.2⟩

/-- Of two different pieces one ends before the other begins. -/
theorem ranged_apart : ∀ (P : List (ℕ × ℕ × ℕ)) (lo hi : ℕ), Ranged P lo hi →
    ∀ p ∈ P, ∀ q ∈ P, p ≠ q → p.2.2 + 2 ^ p.2.1 ≤ q.2.2 ∨ q.2.2 + 2 ^ q.2.1 ≤ p.2.2
  | [], _, _, _, p, hp, _, _, _ => by cases hp
  | a :: P, lo, hi, h, p, hp, q, hq, hne => by
    simp only [Ranged] at h
    rcases List.mem_cons.mp hp with e | hp'
    · rcases List.mem_cons.mp hq with e' | hq'
      · exact absurd (e.trans e'.symm) hne
      · subst e
        exact Or.inl (ranged_mem P _ hi h.2 q hq').1
    · rcases List.mem_cons.mp hq with e' | hq'
      · subst e'
        exact Or.inr (ranged_mem P _ hi h.2 p hp').1
      · exact ranged_apart P _ hi h.2 p hp' q hq' hne

/-- The pieces of one size are ranged from the offset at which they begin to the offset that the
function returns. -/
theorem ranged_piecesOfSize (b : ℕ) : ∀ (ns : List ℕ) (s off : ℕ),
    Ranged (piecesOfSize b ns s off).1 off (piecesOfSize b ns s off).2
  | [], s, off => by simp [piecesOfSize, Ranged]
  | n :: ns, s, off => by
    cases hb : n.testBit b with
    | true =>
      rw [piecesOfSize_cons_true hb]
      show Ranged ((s, b, off) :: (piecesOfSize b ns (s + 1) (off + 2 ^ b)).1) off
        (piecesOfSize b ns (s + 1) (off + 2 ^ b)).2
      simp only [Ranged]
      exact ⟨Nat.le_refl _, ranged_piecesOfSize b ns (s + 1) (off + 2 ^ b)⟩
    | false =>
      rw [piecesOfSize_cons_false hb]
      exact ranged_piecesOfSize b ns (s + 1) off

/-- The pieces of all sizes below k are ranged in the same way. -/
theorem ranged_piecesBelow (ns : List ℕ) : ∀ (k off : ℕ),
    Ranged (piecesBelow ns k off).1 off (piecesBelow ns k off).2
  | 0, off => by simp [piecesBelow, Ranged]
  | k + 1, off => by
    rw [piecesBelow_succ]
    exact ranged_append _ _ off _ _ (ranged_piecesOfSize k ns 0 off) (ranged_piecesBelow ns k _)

/-! ## 3. A segment's columns rise -/

/-- An array of columns that rises strictly, with every column below top and with the property
Q. -/
structure Rising (a : Array ℕ) (Q : ℕ → Prop) (top : ℕ) : Prop where
  lt : ∀ x, x < a.size → a.getD x 0 < top
  mono : ∀ x x', x < x' → x' < a.size → a.getD x 0 < a.getD x' 0
  inQ : ∀ x, x < a.size → Q (a.getD x 0)

/-- The empty array rises. -/
theorem rising_empty (Q : ℕ → Prop) (top : ℕ) : Rising #[] Q top :=
  ⟨fun x h => by simp at h, fun x x' _ h => by simp at h, fun x h => by simp at h⟩

/-- A run that begins at or above top is appended. -/
theorem Rising.append {a : Array ℕ} {Q : ℕ → Prop} {top : ℕ} (A : Rising a Q top) {b off : ℕ}
    (ht : top ≤ off) (hQ : ∀ y, y < 2 ^ b → Q (y + off)) :
    Rising (a ++ run b off) Q (off + 2 ^ b) := by
  have hsz := size_append_run a b off
  have hpos : 0 < 2 ^ b := Nat.two_pow_pos b
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [hsz] at hx
    by_cases h : x < a.size
    · rw [getD_run_left a b off h]
      have k := A.lt x h
      omega
    · obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt h)
      have hy : y < 2 ^ b := by omega
      rw [getD_run_right a b off hy]
      omega
  · intro x x' hxx hx'
    rw [hsz] at hx'
    by_cases h' : x' < a.size
    · rw [getD_run_left a b off (by omega), getD_run_left a b off h']
      exact A.mono x x' hxx h'
    · obtain ⟨y', rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt h')
      have hy' : y' < 2 ^ b := by omega
      rw [getD_run_right a b off hy']
      by_cases h : x < a.size
      · rw [getD_run_left a b off h]
        have k := A.lt x h
        omega
      · obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt h)
        have hy : y < 2 ^ b := by omega
        rw [getD_run_right a b off hy]
        omega
  · intro x hx
    rw [hsz] at hx
    by_cases h : x < a.size
    · rw [getD_run_left a b off h]
      exact A.inQ x h
    · obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt h)
      have hy : y < 2 ^ b := by omega
      rw [getD_run_right a b off hy]
      exact hQ y hy

/-- Laying pieces whose ranges rise from top on keeps an array rising. -/
theorem rising_fold (Q : ℕ → Prop) : ∀ (F : List (ℕ × ℕ × ℕ)) (a : Array ℕ) (top hi : ℕ),
    Ranged F top hi → Rising a Q top → (∀ p ∈ F, ∀ y, y < 2 ^ p.2.1 → Q (y + p.2.2)) →
    Rising (F.foldl layStep a) Q hi
  | [], a, top, hi, h, A, _ => by
    simp only [Ranged] at h
    exact ⟨fun x hx => Nat.lt_of_lt_of_le (A.lt x hx) h, A.mono, A.inQ⟩
  | p :: F, a, top, hi, h, A, hQ => by
    simp only [Ranged] at h
    rw [List.foldl_cons]
    exact rising_fold Q F (layStep a p) _ hi h.2
      (A.append h.1 (hQ p (List.mem_cons.mpr (Or.inl rfl))))
      (fun q hq => hQ q (List.mem_cons.mpr (Or.inr hq)))

/-- The column c lies in the range of a piece of segment number i. -/
def InPiece (P : List (ℕ × ℕ × ℕ)) (i c : ℕ) : Prop :=
  ∃ p ∈ P, p.1 = i ∧ p.2.2 ≤ c ∧ c < p.2.2 + 2 ^ p.2.1

/-- No column lies in pieces of two segments. -/
theorem inPiece_apart {P : List (ℕ × ℕ × ℕ)} {lo hi : ℕ} (hT : Ranged P lo hi) {i i' c : ℕ}
    (hne : i ≠ i') (h : InPiece P i c) (h' : InPiece P i' c) : False := by
  obtain ⟨p, hp, e, l1, u1⟩ := h
  obtain ⟨q, hq, e', l2, u2⟩ := h'
  have hpq : p ≠ q := fun e0 => hne (by rw [← e, ← e', e0])
  rcases ranged_apart P lo hi hT p hp q hq hpq with k | k <;> omega

/-- The columns of segment number i, whose length is below 2^k: one for each entry, rising strictly,
each in a piece of that segment, all below the first free column. -/
theorem columns_rising (ns : List ℕ) (i k : ℕ) (hlt : ns.getD i 0 < 2 ^ k) :
    (columnsOf (piecesBelow ns k 0).1 i (ns.getD i 0)).size = ns.getD i 0 ∧
      Rising (columnsOf (piecesBelow ns k 0).1 i (ns.getD i 0))
        (InPiece (piecesBelow ns k 0).1 i) (piecesBelow ns k 0).2 := by
  obtain ⟨_, hsp⟩ := piecesBelow_spec ns k 0 (Nat.dvd_zero _)
  have hex := exps_piecesBelow ns i k 0
  have hgood : ∀ p ∈ (piecesBelow ns k 0).1.filter (fun p => p.1 == i),
      0 ≤ p.2.1 ∧ 2 ^ 0 ∣ p.2.2 ∧ p.2.2 + 2 ^ p.2.1 ≤ (piecesBelow ns k 0).2 :=
    fun p hp => ⟨Nat.zero_le _, by simp, (hsp p (List.mem_of_mem_filter hp)).2⟩
  obtain ⟨_, hs⟩ := onBlocks_fold 0 _ _ #[] (onBlocks_empty 0 _) hgood
  rw [hex, bitsBelow_sum, Nat.mod_eq_of_lt hlt] at hs
  have hs' : (((piecesBelow ns k 0).1.filter fun p => p.1 == i).foldl layStep #[]).size =
      ns.getD i 0 := by simpa using hs
  have hT := ranged_filter (fun p => p.1 == i) _ 0 _ (ranged_piecesBelow ns k 0)
  have hR := rising_fold (InPiece (piecesBelow ns k 0).1 i) _ #[] 0 _ hT (rising_empty _ _)
    (fun p hp y hy => ⟨p, List.mem_of_mem_filter hp, by simpa using (List.mem_filter.mp hp).2,
      by omega, by omega⟩)
  rw [columnsOf_eq, fill_none hs']
  exact ⟨hs', hR⟩

/-! ## 4. The marking of a placed call -/

/-- The segment that the placing rule makes of member x of the numbered list of segments. -/
def segAt (asks : List SegAsk) (x : SegAsk × ℕ) : Model.Seg :=
  { name := x.1.1, n := x.1.2.1,
    pos := columnsOf (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).1 x.2 x.1.2.1,
    moe := x.1.2.2 }

/-- The segments of a placed call are the asks, numbered, each through segAt. -/
theorem place_segs_eq (name kind : String) (asks : List SegAsk) (fl : ℕ) :
    (place name kind asks fl).segs = asks.zipIdx.map (segAt asks) := rfl

/-- The numbers in a numbered list rise. -/
theorem zipIdx_rising {α : Type} : ∀ (l : List α) (k : ℕ),
    (l.zipIdx k).Pairwise fun x y => x.2 < y.2
  | [], k => by simp
  | a :: l, k => by
    rw [List.zipIdx_cons]
    refine List.pairwise_cons.mpr ⟨fun y hy => ?_, zipIdx_rising l (k + 1)⟩
    obtain ⟨_, h2, _⟩ := mem_zipIdx_getD (fun _ => 0) l (k + 1) y.1 y.2 hy
    show k < y.2
    omega

/-- The columns of a placed segment. -/
theorem segAt_rising (asks : List SegAsk) (hlen : ∀ a ∈ asks, a.2.1 < 2 ^ (topBit + 1))
    (x : SegAsk × ℕ) (hx : x ∈ asks.zipIdx) :
    (segAt asks x).pos.size = (segAt asks x).n ∧
      Rising (segAt asks x).pos
        (InPiece (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).1 x.2)
        (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).2 := by
  obtain ⟨ha, _, hn⟩ := mem_zipIdx_getD (fun a : SegAsk => a.2.1) asks 0 x.1 x.2 hx
  rw [Nat.sub_zero] at hn
  have hlt : (asks.map (·.2.1)).getD x.2 0 < 2 ^ (topBit + 1) := by
    rw [hn]
    exact hlen x.1 ha
  have k := columns_rising (asks.map (·.2.1)) x.2 (topBit + 1) hlt
  rw [hn] at k
  exact k

/-- **The marking never refuses on the rule's own placing**, for segments of lengths below 2^41. -/
theorem place_marks {R : Model.Head.Run} (name kind : String) (asks : List SegAsk) (fl : ℕ)
    (hlen : ∀ a ∈ asks, a.2.1 < 2 ^ (topBit + 1)) :
    ∃ w, (place name kind asks fl).segs.foldlM (fun w g => Model.Head.markColumns R w g)
      (Array.replicate (place name kind asks fl).J 0) = some w := by
  have hJ : (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).2 ≤ (place name kind asks fl).J := by
    show (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).2 ≤
      2 ^ max (ceilLog2 (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).2) fl
    exact Nat.le_trans (le_two_pow_ceilLog2 _)
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_max_left _ _))
  have hT := ranged_piecesBelow (asks.map (·.2.1)) (topBit + 1) 0
  rw [place_segs_eq]
  refine marks_returns _ _ ?_ ?_ ?_ ?_
  · intro g hg x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hg
    obtain ⟨s1, r1⟩ := segAt_rising asks hlen z hz
    rw [Array.size_replicate]
    exact Nat.lt_of_lt_of_le (r1.lt x (by rw [s1]; exact hx)) hJ
  · intro g _ x _
    exact getD_replicate_zero _ _
  · intro g hg x x' hxx hx'
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hg
    obtain ⟨s1, r1⟩ := segAt_rising asks hlen z hz
    exact Nat.ne_of_lt (r1.mono x x' hxx (by rw [s1]; exact hx'))
  · rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ (zipIdx_rising asks 0)
    intro z z' hz hz' hlt x hx x' hx' he
    obtain ⟨s1, r1⟩ := segAt_rising asks hlen z hz
    obtain ⟨s2, r2⟩ := segAt_rising asks hlen z' hz'
    have q1 := r1.inQ x (by rw [s1]; exact hx)
    have q2 := r2.inQ x' (by rw [s2]; exact hx')
    rw [← he] at q2
    exact inPiece_apart hT (Nat.ne_of_lt hlt) q1 q2

/-! ## 5. The layouts that the verifier returns -/

/-- **The marking of each call's columns returns**, for every call number, in a record whose layout
Head.layout has returned. -/
theorem marks_of_layout {h : Model.Head.Shape} {tauFC : Array F} {R : Model.Head.Run}
    (hy : Model.Head.layout h tauFC = .ok R.L) (q : ℕ) :
    ∃ w, (R.L.calls.getD q default).segs.foldlM (fun w g => Model.Head.markColumns R w g)
      (Array.replicate (R.L.calls.getD q default).J 0) = some w := by
  have A := admittedH_of_layout hy
  obtain ⟨cs, hc, _, hL⟩ := A.calls
  obtain ⟨c1, _⟩ := callsOf_spec hc
  by_cases hq : q < cs.length
  · have hg : R.L.calls.getD q default = cs[q] := by
      rw [hL]
      exact toArray_getD_some (List.getElem?_eq_getElem hq) default
    obtain ⟨name, kind, asks, fl, e1, e2⟩ := c1 cs[q] (List.getElem_mem hq)
    rw [hg, e1]
    refine place_marks name kind asks fl fun a ha => ?_
    obtain ⟨x, f1, f2⟩ := e2 a ha
    rw [f2]
    exact segments_lt A x (List.mem_of_find?_eq_some f1)
  · have hg : R.L.calls.getD q default = default := by
      rw [hL]
      simp [Array.getD, hq]
    rw [hg]
    exact ⟨_, rfl⟩

/-- What one line of the calls takes, with the kind: each segment has the length and the kind of the
first member of the list of segments with its name. -/
theorem lineSegs_kind (sd : List (String × String × ℕ)) (kind : String) :
    ∀ (ns seen : List String) (r : List SegAsk × List String),
      Model.Head.lineSegs sd kind ns seen = some r →
      ∀ a ∈ r.1, ∃ x, sd.find? (fun x => x.1 == a.1) = some x ∧ a.2.1 = x.2.2 ∧ x.2.1 = kind
  | [], seen, r, h => by
    have e : r = ([], seen) := (Option.some.inj h).symm
    subst e
    exact fun a ha => (by cases ha)
  | n0 :: ns, seen, r, h => by
    rw [Model.Head.lineSegs] at h
    split at h
    · cases h
    · rename_i x hf
      split at h
      · cases h
      · rename_i hcond
        have hk : x.2.1 = kind := by
          by_contra hne
          exact hcond (by simp [hne])
        cases hr : Model.Head.lineSegs sd kind ns (n0 :: seen) with
        | none =>
          rw [hr] at h
          cases h
        | some r' =>
          rw [hr] at h
          have e : ((n0, x.2.2, false) :: r'.1, r'.2) = r := Option.some.inj h
          subst e
          have i1 := lineSegs_kind sd kind ns (n0 :: seen) r' hr
          intro a ha
          rcases List.mem_cons.mp ha with e | ha'
          · subst e
            exact ⟨x, hf, rfl, hk⟩
          · exact i1 a ha'

/-- What the lines of the calls give, with the kind. -/
theorem callsFrom_kind (sd : List (String × String × ℕ)) (fl : ℕ) :
    ∀ (lines : List (List String)) (names seen : List String)
      (r : List Model.CallD × List String),
      Model.Head.callsFrom sd fl lines names seen = some r →
      ∀ c ∈ r.1, ∃ name kind asks, c = place name kind asks fl ∧
        ∀ a ∈ asks, ∃ x, sd.find? (fun x => x.1 == a.1) = some x ∧ a.2.1 = x.2.2 ∧ x.2.1 = kind
  | [], _, seen, r, h => by
    have e : r = ([], seen) := (Option.some.inj h).symm
    subst e
    exact fun c hc => (by cases hc)
  | [] :: _, _, _, _, h => by cases h
  | [_] :: _, _, _, _, h => by cases h
  | [_, _] :: _, _, _, _, h => by cases h
  | (name :: kind :: s :: ss) :: rest, names, seen, r, h => by
    rw [Model.Head.callsFrom] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i asks seen' hl
        cases hr : Model.Head.callsFrom sd fl rest (name :: names) seen' with
        | none =>
          rw [hr] at h
          cases h
        | some r' =>
          rw [hr] at h
          have e : (place name kind asks fl :: r'.1, r'.2) = r := Option.some.inj h
          subst e
          have l1 := lineSegs_kind sd kind (s :: ss) seen (asks, seen') hl
          have i1 := callsFrom_kind sd fl rest (name :: names) seen' r' hr
          intro c hc
          rcases List.mem_cons.mp hc with e | hc'
          · exact ⟨name, kind, asks, e, l1⟩
          · exact i1 c hc'

/-- What callsOf returns, with the kind. -/
theorem callsOf_kind {h : Model.Head.Shape} {L : Model.Head.HL} {cs : List Model.CallD}
    (hc : Model.Head.callsOf h L = .ok cs) :
    ∀ c ∈ cs, ∃ name kind asks fl, c = place name kind asks fl ∧
      ∀ a ∈ asks, ∃ x, (Model.Head.segments h L).find? (fun x => x.1 == a.1) = some x ∧
        a.2.1 = x.2.2 ∧ x.2.1 = kind := by
  unfold Model.Head.callsOf at hc
  obtain ⟨-, hc⟩ := ok_of_needed hc
  dsimp only at hc
  split at hc
  · cases hc
  · rename_i calls seen hf
    obtain ⟨_, hc⟩ := ok_of_needed hc
    cases hc
    intro c hcm
    obtain ⟨name, kind, asks, e1, e2⟩ := callsFrom_kind _ _ _ [] [] (cs, seen) hf c hcm
    exact ⟨name, kind, asks, _, e1, e2⟩

/-- A family of the plain head and a family with the same name have the same kind. -/
theorem kind_of_name {s : Inst.Model.Head.Fam} {f : Cm.Plain.Fam} (e : nameH s = segName f) :
    famKind s = plainKind f := by
  cases s <;> cases f <;> first | rfl | (simp [nameH, segName] at e)

section Full

variable {h : Model.Head.Shape} {tauFC : Array F} {R : Model.Head.Run}
  (hy : Model.Head.layout h tauFC = .ok R.L) (h1 : h.lt = 10) (h2 : h.d = 5120)
  (h3 : h.V = 202048) (h4 : h.XL = 5)
include hy h1 h2 h3 h4

omit h2 in
/-- The lengths in the head's list of segments at the library's sizes. -/
theorem full_lens : R.L.JV = 202048 ∧ R.L.JVa = 131072 ∧ Model.ledNRH h.XL = 120 := by
  have A := admittedH_of_layout hy
  obtain ⟨-, hla, -⟩ := A.bounds
  have hls : h.ls ≤ 6 := by
    unfold Model.Head.Shape.ls
    omega
  have hdv : h.S2 ∣ h.V := by
    rw [h3]
    exact Dvd.dvd.trans (pow_dvd_pow 2 hls) (by norm_num)
  have hV : R.L.JV = h.V := A.JV_iff.2 hdv
  have hJa : R.L.JVa = 131072 := by
    rw [A.JVa, hV, h3]
    decide +kernel
  exact ⟨hV.trans h3, hJa, by rw [h4]; rfl⟩

/-- Each member of the head's list of segments is a family's: name, kind, and at most the family's
number of entries. -/
theorem segments_fam (x : String × String × ℕ) (hx : x ∈ Model.Head.segments h R.L) :
    ∃ s : Inst.Model.Head.Fam, x.1 = nameH s ∧ x.2.1 = famKind s ∧
      x.2.2 ≤ Inst.Model.Head.len s := by
  obtain ⟨e1, e2, e3⟩ := full_lens hy h1 h3 h4
  unfold Model.Head.segments at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.NF, rfl, rfl, le_of_eq h2⟩
  · exact ⟨.NFH, rfl, rfl, le_of_eq h2⟩
  · exact ⟨.HD0, rfl, rfl, le_of_eq e1⟩
  · exact ⟨.HD1, rfl, rfl, le_of_eq e1⟩
  · exact ⟨.ROW, rfl, rfl, le_of_eq e3⟩
  · exact ⟨.HD2, rfl, rfl, le_of_eq e1⟩
  · exact ⟨.CNF, rfl, rfl, le_of_eq h2⟩
  · exact ⟨.HE0, rfl, rfl, le_of_eq e2⟩
  · refine ⟨.HE1, rfl, rfl, ?_⟩
    show R.L.JV - R.L.JVa ≤ 70976
    omega

/-- **Every segment of every call has a family's name, at most its number of entries, and stands in
a call of its kind.** -/
theorem segsFit_of_layout : SegsFit R := by
  intro q g hg
  have A := admittedH_of_layout hy
  obtain ⟨cs, hc, _, hL⟩ := A.calls
  have c1 := callsOf_kind hc
  by_cases hq : q < cs.length
  · have hgq : R.L.calls.getD q default = cs[q] := by
      rw [hL]
      exact toArray_getD_some (List.getElem?_eq_getElem hq) default
    obtain ⟨name, kind, asks, fl, e1, e2⟩ := c1 cs[q] (List.getElem_mem hq)
    rw [hgq, e1] at hg ⊢
    obtain ⟨a, ha, a1, a2, -⟩ := place_segs name kind asks fl g hg
    obtain ⟨x, f1, f2, f3⟩ := e2 a ha
    obtain ⟨s, s1, s2, s3⟩ :=
      segments_fam hy h1 h2 h3 h4 x (List.mem_of_find?_eq_some f1)
    have hxn : x.1 = a.1 := by simpa using List.find?_some f1
    refine ⟨s, by rw [a1, ← hxn, s1], by rw [a2, f2]; exact s3, ?_⟩
    show kind = famKind s
    rw [← f3, s2]
  · have hgq : R.L.calls.getD q default = default := by
      rw [hL]
      simp [Array.getD, hq]
    have e0 : (default : Model.CallD).segs = [] := rfl
    rw [hgq, e0] at hg
    cases hg

/-- One family of the plain head: its segment. -/
theorem has_one {f : Cm.Plain.Fam} (x : String × String × ℕ)
    (hx : x ∈ Model.Head.segments h R.L) (hname : x.1 = segName f)
    (hlen : Cm.Plain.len f ≤ x.2.2) :
    ∃ q g, g ∈ (R.L.calls.getD q default).segs ∧ g.name = segName f ∧ Cm.Plain.len f ≤ g.n ∧
      (R.L.calls.getD q default).kind = plainKind f := by
  have A := admittedH_of_layout hy
  obtain ⟨q, g, name, kind, asks, fl, _, hp, hg, hgm, hn, -⟩ := seg_of_admitted A x hx
  have hgm' : g ∈ (R.L.calls.getD q default).segs := by
    rw [hp]
    exact hgm
  have hgn : g.name = x.1 := by simpa using List.find?_some hg
  obtain ⟨s, s1, _, s3⟩ := segsFit_of_layout hy h1 h2 h3 h4 q g hgm'
  exact ⟨q, g, hgm', hgn.trans hname, by rw [hn]; exact hlen,
    s3.trans (kind_of_name (s1.symm.trans (hgn.trans hname)))⟩

/-- **Every family of the plain head has a segment with at least its number of entries, in a call of
its kind.** -/
theorem hasAll_of_layout : HasAll R := by
  obtain ⟨e1, _, e3⟩ := full_lens hy h1 h3 h4
  intro f
  cases f
  · exact has_one hy h1 h2 h3 h4 ("NF", "R16", h.d) (by simp [Model.Head.segments]) rfl
      (le_of_eq h2.symm)
  · exact has_one hy h1 h2 h3 h4 ("NFH", "R16", h.d) (by simp [Model.Head.segments]) rfl
      (le_of_eq h2.symm)
  · exact has_one hy h1 h2 h3 h4 ("HD0", "R16", R.L.JV) (by simp [Model.Head.segments]) rfl
      (le_of_eq e1.symm)
  · exact has_one hy h1 h2 h3 h4 ("HD1", "R16", R.L.JV) (by simp [Model.Head.segments]) rfl
      (le_of_eq e1.symm)
  · exact has_one hy h1 h2 h3 h4 ("ROW", "R8", Model.ledNRH h.XL)
      (by simp [Model.Head.segments]) rfl (by rw [e3]; decide)
  · exact has_one hy h1 h2 h3 h4 ("HD2", "R8", R.L.JV) (by simp [Model.Head.segments]) rfl
      (le_of_eq e1.symm)
  · exact has_one hy h1 h2 h3 h4 ("CNF", "FC", h.d) (by simp [Model.Head.segments]) rfl
      (le_of_eq h2.symm)

/-- **The hypotheses of next_token_of_calls are met together at every record whose layout the
verifier's function has returned for a shape of the library's sizes**: met_ledger of
Johnson/Road/HeadSumMet.lean at the record R, without its three hypotheses on the record. At every
lawful table and for every policy with AcceptancePolicy.OK there are an index, a true request for the next token
and integer cells such that: the final normalisation is lawful; the layers give what the head
borrows; the cells are small; the identities are 0 in the challenge field; and for every inverse c
of 2^23: the marking of each call's columns returns, the keys kvL and the tables tabL have CallsFit
at R, the calls' functions exist, and every value of each is a row of the call's table. -/
theorem met_of_layout {s : Cm.Scales} (hs : s.Lawful) {pol : Inst.Model.AcceptancePolicy} (hpol : pol.OK) :
    ∃ (i : Inst.Model.Index Inst.Model.ppref) (x : Inst.Model.Instance Inst.Model.ppref)
      (tz : Inst.Model.Head.Cells ℤ),
      x.r = 1023 ∧ x.e = 1024 ∧ s.nf.OK ∧
      Top.LayersGive s.kap (fun _ => Inst.Model.tbRef) i.val x.prompt tz ∧
      Cm.Plain.Small (2 ^ 18) tz ∧
      (∀ a < Inst.Model.Head.nT, ∀ k < 17, Cm.Plain.idn s.nf (tz.cast Cb.Gl.E) a k = 0) ∧
      ∀ c : Cb.Gl.E, c * 2 ^ 23 = 1 → ∃ w : ℕ → Array ℕ,
        (∀ q, (R.L.calls.getD q default).segs.foldlM
          (fun w g => Model.Head.markColumns R w g)
          (Array.replicate (R.L.calls.getD q default).J 0) = some (w q)) ∧
        CallsFit R
          (kvL c s.nf (tz.cast Cb.Gl.E) (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Cm.reqOf x)
            (Inst.Model.Head.Req.of pol x))
          (tabL R) c s.nf (tz.cast Cb.Gl.E) (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E))
          (Cm.reqOf x) ∧
        ∃ fn : ℕ → ℕ → ℕ → Cb.Gl.E,
          (∀ q, KeyFn (R.L.calls.getD q default).segs (w q) (R.L.calls.getD q default).J
            (kvL c s.nf (tz.cast Cb.Gl.E) (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E))
              (Cm.reqOf x) (Inst.Model.Head.Req.of pol x))
            (((tabL R q).pad : ℤ) : Cb.Gl.E) (fn q)) ∧
          ∀ q j, j < (R.L.calls.getD q default).J → ∀ a, a < Inst.Model.Head.nT →
            Inst.Model.Head.InLut (tabL R q) (fn q j a) := by
  obtain ⟨i, x, tz, hr, he, hn, hl, hsm, hid, hR⟩ := met_ledger hs hpol
  choose w hw using marks_of_layout (R := R) hy
  exact ⟨i, x, tz, hr, he, hn, hl, hsm, hid, fun c hc =>
    ⟨w, hw, hR R c w hc (segsFit_of_layout hy h1 h2 h3 h4) (hasAll_of_layout hy h1 h2 h3 h4) hw⟩⟩

end Full

#print axioms place_marks
#print axioms marks_of_layout
#print axioms segsFit_of_layout
#print axioms hasAll_of_layout
#print axioms met_of_layout

end OnBytes.Road.Hd
