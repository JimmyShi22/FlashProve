-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/K3X/HeadLaidLaw.lean: the host's count of padding keys at the output head's lookup
(laidHead, Johnson/Desc/First/Look/Laid.lean) is the fold that pubOf_eq
(Johnson/AtFull/Head/PubOfLaw.lean) has for the layout's own count (Head.pubOf,
OnBytes/Model/HeadLayout.lean). A general law: nothing is evaluated. No sub-protocol imports this
file.

Why. laidHead marks the columns of each call one by one in an array with one entry a column, and
then walks all columns. At the full size a call has up to 262,144 columns. For Lean's kernel an
array is a list, so a run of single writes into such an array costs about the square of its length.
Whether the kernel would bear that here was not measured. The law needs no evaluation: on calls that
the placing rule (place, OnBytes/Model/Calls.lean) has made, the marking returns, a column bears the
mark 1 just if the call's own array of marks (used) has a mark there, and so the host's walk adds
what the layout's walk adds.

Statements.
  markColumns_eq the marking that Laid.lean types anew (markColumnsP) is the verifier program's own
                 (Head.markColumns, OnBytes/Model/HeadForms.lean) at a run's shape and layout: by
                 definition.
  fold_marks     marking columns that are inside the array, unmarked and all different returns; each
                 of them reads its mark afterwards; every other entry stays.
  mark_one       where a segment has no entry behind the vocabulary each of its marks is 1.
  marks_all      the same for a list of segments that share no column.
  place_marked   on a placed call: the marking returns, and a column's mark is not 1 just if the
                 call's array used reads 0 there.
  foldlM_some    a fold in Option whose steps all return, under an invariant, is a plain fold.
  laidHeadCall_eq  one call: the host adds what addCols (Johnson/AtFull/Head/PubOfLaw.lean) adds.
  zipIdx_as_range  a numbered list, by its numbers.
  laidHead_eq    THE LAW: laidHead h L = some (the fold of addCols over the numbered calls): the
                 very term that pubOf_eq (Johnson/AtFull/Head/PubOfLaw.lean) has for Head.pubOf and
                 that pub_value (Johnson/AtFull/Head/PubValue.lean) turns into a closed form.
Premises of laidHead_eq. The layout's calls are a list of placed calls; each segment is shorter than
2 ^ 41; no segment with one entry a vocabulary entry has an entry behind the vocabulary (so the mark
2 is never written); the tree of each call's last column is one of the lookup's trees.

Limits. As the head of Laid.lean says: the host counts next to the key forms, from the lists of
columns, not from the forms: this law says that two counts made of the same lists agree; a fault in
a list or inside a form is not seen by either. Where a segment has entries behind the vocabulary
nothing is said. That the host's walk over a call (laidHeadCall) counts as the program's own routine
(Head.keyForm) counts is not shown: the program reads three numbers off the heard record's shape,
the host off the layout's. No soundness is claimed. On hiding nothing.
-/
import Johnson.AtFull.Head.PubValue
import Johnson.Desc.First.Look.Laid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.K3X
open OnBytes OnBytes.Model OnBytes.Model.Head
open VerifiableInference.Desc.First.Look (markColumnsP laidHeadCall laidHead)
open OnBytes.Road (le_two_pow_ceilLog2)
open OnBytes.Road.Hd (NoShare Rising segAt segAt_rising place_segs_eq getD_replicate_zero
  getD_set_ne getD_set_self inPiece_apart zipIdx_rising ranged_piecesBelow toArray_getD_some)
open Johnson.Unfolds (marks_made)
open _root_.AtFull.Head (addCols addCols_adds marks_none asks_lt)

/-- The marking typed anew is the verifier program's own, at a run's shape and layout. -/
theorem markColumns_eq (R : OnBytes.Model.Head.Run) :
    OnBytes.Model.Head.markColumns R = markColumnsP R.h R.L := rfl

/-- Marking the columns pos 0, ..., pos (n - 1), which lie within the array, bear no mark and are
all different: no step refuses, each of them reads its mark, every other entry stays. -/
theorem fold_marks (pos mk : Nat → Nat) :
    ∀ (n : Nat) (w : Array Nat), (∀ x, x < n → pos x < w.size) →
      (∀ x, x < n → w.getD (pos x) 0 = 0) → (∀ x x', x < x' → x' < n → pos x ≠ pos x') →
      ∃ w', (List.range n).foldlM (fun w x =>
        if pos x < w.size && w.getD (pos x) 1 == 0 then some (w.set! (pos x) (mk x)) else none)
        w = some w' ∧ w'.size = w.size ∧ (∀ x, x < n → w'.getD (pos x) 0 = mk x) ∧
        ∀ j, (∀ x, x < n → j ≠ pos x) → w'.getD j 0 = w.getD j 0
  | 0, w, _, _, _ =>
    ⟨w, by simp, rfl, fun x hx => absurd hx (Nat.not_lt_zero x), fun _ _ => rfl⟩
  | n + 1, w, hs, hf, hi => by
    obtain ⟨w1, h1, s1, v1, o1⟩ := fold_marks pos mk n w (fun x hx => hs x (Nat.lt_succ_of_lt hx))
      (fun x hx => hf x (Nat.lt_succ_of_lt hx)) (fun x x' h h' => hi x x' h (Nat.lt_succ_of_lt h'))
    have c1 : pos n < w1.size := by
      rw [s1]
      exact hs n (Nat.lt_succ_self n)
    have c0 : w1.getD (pos n) 0 = 0 := by
      rw [o1 (pos n) fun x hx => (hi x n hx (Nat.lt_succ_self n)).symm]
      exact hf n (Nat.lt_succ_self n)
    have c2 : w1[pos n] = 0 := by simpa [Array.getD, c1] using c0
    refine ⟨w1.set! (pos n) (mk n), ?_, ?_, ?_, ?_⟩
    · rw [List.range_succ, List.foldlM_append, h1]
      simp [c1, c2]
    · rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, s1]
    · intro x hx
      rw [Array.set!_eq_setIfInBounds]
      by_cases e : x = n
      · rw [e]
        exact getD_set_self w1 c1 _
      · have hx' : x < n := by omega
        rw [getD_set_ne w1 (hi x n hx' (Nat.lt_succ_self n)).symm, v1 x hx']
    · intro j hj
      rw [Array.set!_eq_setIfInBounds, getD_set_ne w1 (hj n (Nat.lt_succ_self n)).symm,
        o1 j fun x hx => hj x (Nat.lt_succ_of_lt hx)]

/-- Where a segment has no entry behind the vocabulary each of its marks is 1. -/
theorem mark_one {p : Bool} {v0 x V n : Nat} (hx : x < n) (hv : p = true → n - (V - v0) = 0) :
    (if p && decide (v0 + x ≥ V) then 2 else 1 : Nat) = 1 := by
  cases p with
  | false => simp
  | true =>
    have h0 := hv rfl
    have h1 : ¬ (v0 + x ≥ V) := by omega
    simp [h1]

/-- The marking of the columns of a list of segments, if all listed columns lie within the array and
bear no mark, no segment lists a column twice, no two share one, and none has an entry behind the
vocabulary: it returns, each listed column reads 1, every other entry stays. -/
theorem marks_all (h : Shape) (L : HL) :
    ∀ (l : List Seg) (w : Array Nat),
      (∀ g ∈ l, ∀ x, x < g.n → g.pos.getD x 0 < w.size) →
      (∀ g ∈ l, ∀ x, x < g.n → w.getD (g.pos.getD x 0) 0 = 0) →
      (∀ g ∈ l, ∀ x x', x < x' → x' < g.n → g.pos.getD x 0 ≠ g.pos.getD x' 0) →
      l.Pairwise NoShare →
      (∀ g ∈ l, perEntry g.name = true → g.n - (h.V - firstEntry L g.name) = 0) →
      ∃ w', l.foldlM (markColumnsP h L) w = some w' ∧ w'.size = w.size ∧
        (∀ g ∈ l, ∀ x, x < g.n → w'.getD (g.pos.getD x 0) 0 = 1) ∧
        ∀ j, (∀ g ∈ l, ∀ x, x < g.n → j ≠ g.pos.getD x 0) → w'.getD j 0 = w.getD j 0
  | [], w, _, _, _, _, _ =>
    ⟨w, by simp, rfl, fun _ hg => absurd hg List.not_mem_nil, fun _ _ => rfl⟩
  | g :: l, w, hs, hf, hi, hp, hv => by
    have hg : g ∈ g :: l := List.mem_cons_self ..
    obtain ⟨w1, h1, s1, v1, o1⟩ := fold_marks (fun x => g.pos.getD x 0)
      (fun x => if perEntry g.name && firstEntry L g.name + x ≥ h.V then 2 else 1) g.n w
      (hs g hg) (hf g hg) (hi g hg)
    have hm : markColumnsP h L w g = some w1 := h1
    obtain ⟨hpg, hpl⟩ := List.pairwise_cons.mp hp
    obtain ⟨w', h2, s2, v2, o2⟩ := marks_all h L l w1
      (fun g' hg' x hx => by
        rw [s1]
        exact hs g' (List.mem_cons_of_mem _ hg') x hx)
      (fun g' hg' x hx => by
        rw [o1 (g'.pos.getD x 0) fun y hy => (hpg g' hg' y hy x hx).symm]
        exact hf g' (List.mem_cons_of_mem _ hg') x hx)
      (fun g' hg' => hi g' (List.mem_cons_of_mem _ hg')) hpl
      (fun g' hg' => hv g' (List.mem_cons_of_mem _ hg'))
    refine ⟨w', ?_, by rw [s2, s1], ?_, ?_⟩
    · rw [List.foldlM_cons, hm]
      exact h2
    · intro g' hg' x hx
      rcases List.mem_cons.1 hg' with e | hl
      · rw [e] at hx ⊢
        rw [o2 (g.pos.getD x 0) fun g'' hg'' y hy => hpg g'' hg'' x hx y hy, v1 x hx]
        exact mark_one hx (hv g hg)
      · exact v2 g' hl x hx
    · intro j hj
      rw [o2 j fun g' hg' => hj g' (List.mem_cons_of_mem _ hg'), o1 j (hj g hg)]

/-- **On a placed call the marking returns, and a column's mark is not 1 just if the call's own
array of marks reads 0 there.** -/
theorem place_marked (h : Shape) (L : HL) (name kind : String) (asks : List SegAsk) (fl : Nat)
    (hlen : ∀ a ∈ asks, a.2.1 < 2 ^ (topBit + 1))
    (hv : ∀ g ∈ (place name kind asks fl).segs, perEntry g.name = true →
      g.n - (h.V - firstEntry L g.name) = 0) :
    ∃ w, (place name kind asks fl).segs.foldlM (markColumnsP h L)
        (Array.replicate (place name kind asks fl).J 0) = some w ∧
      ∀ j, j < (place name kind asks fl).J →
        (w.getD j 0 != 1) = ((place name kind asks fl).used.getD j 0 == 0) := by
  have hJ : (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).2 ≤ (place name kind asks fl).J := by
    show (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).2 ≤
      2 ^ max (ceilLog2 (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).2) fl
    exact Nat.le_trans (le_two_pow_ceilLog2 _)
      (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
  have hT := ranged_piecesBelow (asks.map (·.2.1)) (topBit + 1) 0
  have sz : ∀ g ∈ (place name kind asks fl).segs, g.pos.size = g.n := by
    intro g hg
    rw [place_segs_eq] at hg
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hg
    exact (segAt_rising asks hlen z hz).1
  have a1 : ∀ g ∈ (place name kind asks fl).segs, ∀ x, x < g.n →
      g.pos.getD x 0 < (Array.replicate (place name kind asks fl).J 0).size := by
    intro g hg x hx
    rw [place_segs_eq] at hg
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hg
    obtain ⟨s1, r1⟩ := segAt_rising asks hlen z hz
    rw [Array.size_replicate]
    exact Nat.lt_of_lt_of_le (r1.lt x (by rw [s1]; exact hx)) hJ
  have a3 : ∀ g ∈ (place name kind asks fl).segs, ∀ x x', x < x' → x' < g.n →
      g.pos.getD x 0 ≠ g.pos.getD x' 0 := by
    intro g hg x x' hxx hx'
    rw [place_segs_eq] at hg
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hg
    obtain ⟨s1, r1⟩ := segAt_rising asks hlen z hz
    exact Nat.ne_of_lt (r1.mono x x' hxx (by rw [s1]; exact hx'))
  have a4 : (place name kind asks fl).segs.Pairwise NoShare := by
    rw [place_segs_eq, List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ (zipIdx_rising asks 0)
    intro z z' hz hz' hlt x hx x' hx' he
    obtain ⟨s1, r1⟩ := segAt_rising asks hlen z hz
    obtain ⟨s2, r2⟩ := segAt_rising asks hlen z' hz'
    have q1 := r1.inQ x (by rw [s1]; exact hx)
    have q2 := r2.inQ x' (by rw [s2]; exact hx')
    rw [← he] at q2
    exact inPiece_apart hT (Nat.ne_of_lt hlt) q1 q2
  obtain ⟨w, hw, -, v, o⟩ := marks_all h L (place name kind asks fl).segs
    (Array.replicate (place name kind asks fl).J 0) a1
    (fun _ _ _ _ => getD_replicate_zero _ _) a3 a4 hv
  refine ⟨w, hw, fun j hj => ?_⟩
  have hu : (place name kind asks fl).used = (place name kind asks fl).segs.foldl markUsed
      (Array.replicate (place name kind asks fl).J 0) := rfl
  by_cases hl : ∃ g ∈ (place name kind asks fl).segs, ∃ x, x < g.n ∧ j = g.pos.getD x 0
  · obtain ⟨g, hg, x, hx, e⟩ := hl
    have hx' : x < g.pos.size := by
      rw [sz g hg]
      exact hx
    have hm : j ∈ g.pos.toList := by
      rw [e]
      simp [Array.getD, hx']
    have hne := marks_made j (place name kind asks fl).segs
      (Array.replicate (place name kind asks fl).J 0) (by simpa using hj) ⟨g, hg, hm⟩
    have hw1 : w.getD j 0 = 1 := by
      rw [e]
      exact v g hg x hx
    rw [hw1, hu, beq_eq_false_iff_ne.2 hne]
    rfl
  · have hn : ∀ g ∈ (place name kind asks fl).segs, ∀ x, x < g.n → j ≠ g.pos.getD x 0 :=
      fun g hg x hx e => hl ⟨g, hg, x, hx, e⟩
    rw [o j hn, getD_replicate_zero, hu, marks_none j _ _ ?_, getD_replicate_zero]
    · rfl
    · intro s hs hm
      obtain ⟨i, hi, e⟩ := List.getElem_of_mem hm
      have hi' : i < s.pos.size := by simpa using hi
      refine hn s hs i (by rw [← sz s hs]; exact hi') ?_
      rw [← e]
      simp [Array.getD, hi']

/-- A fold in Option whose steps all return, under an invariant, is a plain fold. -/
theorem foldlM_some {α β : Type} (f : β → α → Option β) (g : β → α → β) (I : β → Prop) :
    ∀ (l : List α) (b : β), I b → (∀ a ∈ l, ∀ b, I b → f b a = some (g b a) ∧ I (g b a)) →
      l.foldlM f b = some (l.foldl g b) ∧ I (l.foldl g b)
  | [], _, hb, _ => ⟨rfl, hb⟩
  | a :: l, b, hb, h => by
    obtain ⟨e, i⟩ := h a (List.mem_cons_self ..) b hb
    rw [List.foldlM_cons, e]
    exact foldlM_some f g I l (g b a) i fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- **One call: the host adds what the layout adds.** -/
theorem laidHeadCall_eq (h : Shape) (L : HL) (q : Nat) (name kind : String) (asks : List SegAsk)
    (fl : Nat) (hc : L.calls.getD q default = place name kind asks fl)
    (hlen : ∀ a ∈ asks, a.2.1 < 2 ^ (topBit + 1))
    (hv : ∀ g ∈ (place name kind asks fl).segs, perEntry g.name = true →
      g.n - (h.V - firstEntry L g.name) = 0)
    (n : Nat) (hfit : ∀ j, j < (place name kind asks fl).J →
      L.fs.first.getD q 0 + j / 2 ^ (L.fs.dT - h.lt) < n)
    (laid : Array Nat) (hs : laid.size = n) :
    laidHeadCall h L q laid = some (addCols h.T (L.fs.dT - h.lt) (L.fs.first.getD q 0)
      (place name kind asks fl) laid) := by
  obtain ⟨w, hw, hval⟩ := place_marked h L name kind asks fl hlen hv
  unfold laidHeadCall addCols
  dsimp only
  rw [hc, hw]
  refine (foldlM_some _ _ (fun r => r.size = n) _ laid hs ?_).1
  intro j hj b hb
  have hj' := List.mem_range.1 hj
  dsimp only
  by_cases hu : ((place name kind asks fl).used.getD j 0 == 0) = true
  · have hm : (w.getD j 0 != 1) = true := by
      rw [hval j hj']
      exact hu
    rw [if_pos hm, if_pos (by rw [hb]; exact hfit j hj'), if_pos hu]
    exact ⟨rfl, by rw [Array.size_modify]; exact hb⟩
  · have hm : ¬ (w.getD j 0 != 1) = true := by
      rw [hval j hj']
      exact hu
    rw [if_neg hm, if_neg hu]
    exact ⟨rfl, hb⟩

/-- A numbered list, by its numbers. -/
theorem zipIdx_as_range {α : Type} [Inhabited α] (l : List α) :
    l.zipIdx = (List.range l.length).map fun q => (l.toArray.getD q default, q) := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  have hi : i < l.length := by simpa using h1
  simp [Array.getD, hi]

/-- **The host's count at the output head's lookup is the fold that the layout's count is.** -/
theorem laidHead_eq (h : Shape) (L : HL) (calls : List CallD) (hc : L.calls = calls.toArray)
    (hp : ∀ cd ∈ calls, ∃ name kind asks fl, cd = place name kind asks fl)
    (hn : ∀ cd ∈ calls, ∀ s ∈ cd.segs, s.n < 2 ^ (topBit + 1))
    (H2 : ∀ cd ∈ calls, ∀ g ∈ cd.segs, perEntry g.name = true →
      g.n - (h.V - firstEntry L g.name) = 0)
    (hfit : ∀ x ∈ calls.zipIdx,
      L.fs.first.getD x.2 0 + (x.1.J - 1) / 2 ^ (L.fs.dT - h.lt) < L.fs.NT) :
    laidHead h L = some (calls.zipIdx.foldl
      (fun pub x => addCols h.T (L.fs.dT - h.lt) (L.fs.first.getD x.2 0) x.1 pub)
      (Array.replicate L.fs.NT 0)) := by
  unfold laidHead
  have hsz : L.calls.size = calls.length := by
    rw [hc]
    simp
  rw [hsz, zipIdx_as_range calls, List.foldl_map]
  refine (foldlM_some _ _ (fun r => r.size = L.fs.NT) _ _ (by simp) ?_).1
  intro q hq b hb
  have hq' := List.mem_range.1 hq
  have mem : calls[q] ∈ calls := List.getElem_mem hq'
  have hz : (calls[q], q) ∈ calls.zipIdx :=
    List.mem_iff_getElem.2 ⟨q, by simpa using hq', by simp⟩
  obtain ⟨name, kind, asks, fl, e⟩ := hp _ mem
  have hg : L.calls.getD q default = place name kind asks fl := by
    rw [hc, ← e]
    exact toArray_getD_some (List.getElem?_eq_getElem hq') default
  have hl := hn _ mem
  have h2 := H2 _ mem
  have hf := hfit _ hz
  dsimp only at hf ⊢
  rw [e] at hl h2 hf
  rw [← hc, hg]
  refine ⟨laidHeadCall_eq h L q name kind asks fl hg (asks_lt hl) h2 L.fs.NT (fun j hj => ?_) b hb,
    (addCols_adds _ _ _ L.fs.NT _ b hb).1⟩
  have hd : j / 2 ^ (L.fs.dT - h.lt) ≤ ((place name kind asks fl).J - 1) / 2 ^ (L.fs.dT - h.lt) :=
    Nat.div_le_div_right (by omega)
  omega

end Johnson.AtFull.K3X

#print axioms Johnson.AtFull.K3X.markColumns_eq
#print axioms Johnson.AtFull.K3X.fold_marks
#print axioms Johnson.AtFull.K3X.mark_one
#print axioms Johnson.AtFull.K3X.marks_all
#print axioms Johnson.AtFull.K3X.place_marked
#print axioms Johnson.AtFull.K3X.foldlM_some
#print axioms Johnson.AtFull.K3X.laidHeadCall_eq
#print axioms Johnson.AtFull.K3X.zipIdx_as_range
#print axioms Johnson.AtFull.K3X.laidHead_eq
