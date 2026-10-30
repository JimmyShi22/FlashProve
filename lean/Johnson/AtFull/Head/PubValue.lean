-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Head/PubValue.lean: the counts of padding keys of the output head's lookup
(`Head.pubOf`, OnBytes/Model/HeadLayout.lean) IN CLOSED FORM: the placing rule (`place`,
OnBytes/Model/Calls.lean) lays its pieces one behind the other from column 0 without a gap, so the
columns that a call's segments take are just those below the sum of the segments' lengths, and the
number of a tree's columns that no segment takes is the length of an interval. General laws: nothing
is evaluated. No sub-protocol imports this file.

Why. `pubOf` walks all columns of a call and reads a mark for each; the marks are an array with one
entry a column, made by folds of single writes. At the full size a call has more than 10 ^ 5 columns
(its vocabulary's segments have 202,048 entries). Whether Lean's kernel would bear that was not
measured; in earlier trials of this project it has failed at arrays of 65,536. The closed
form reads of a call its number of columns and its segments' lengths alone.

Statements.
  `cover_piecesOfSize`, `cover_piecesBelow`: no gap: each column from the first free one on, below
    the new first free one, lies in a piece, and that piece's segment is one of the list.
  `mem_fold`, `mem_columnsOf`: a column in a piece of segment s is one of segment s's columns.
  `lt_of_mem`, `marks_none`: tools.
  `place_used_iff`: for lengths below 2 ^ 41: column j of a placed call bears no mark just if the
    sum of the lengths is at most j.
  `count_block`: how many j below J have S ≤ j and j / M = t: an interval's length.
  `takenOf cd`: the sum of a call's segments' lengths. `takenOf_place`.
  `formAt`: the closed form of a tree's count.
  `colsAt_form`: what one call adds at one tree (`colsAt`, Johnson/AtFull/Head/PubOfLaw.lean) is the
    closed form's summand.
  `pub_value`: the fold of `pubOf_eq` is the array of the closed form's values.

Limits. On placed calls whose segments' lengths are below 2 ^ 41. The second inner loop of `pubOf`
(entries behind the vocabulary) is not treated: `pubOf_eq` takes that it is empty. No soundness is
claimed. On hiding nothing.
-/
import Johnson.AtFull.Head.PubOfLaw
import Johnson.Road.HeadCallsLaid
import Johnson.Road.FormsKeysPos
import Johnson.Unfolds.Used

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.Head
open OnBytes OnBytes.Model OnBytes.Model.Head
open OnBytes.Road (piecesOfSize_cons_true piecesOfSize_cons_false piecesBelow_succ columnsOf_eq
  layStep run markUsed_get piecesBelow_total le_two_pow_ceilLog2)
open OnBytes.Road.Hd (Rising segAt segAt_rising place_segs_eq getD_replicate_zero)
open Johnson.Unfolds (marks_made in_block sum_zero)

/-- No gap among the pieces of one size. -/
theorem cover_piecesOfSize (b : Nat) : ∀ (ns : List Nat) (s off c : Nat), off ≤ c →
    c < (piecesOfSize b ns s off).2 →
    ∃ p ∈ (piecesOfSize b ns s off).1, p.1 < s + ns.length ∧ p.2.2 ≤ c ∧ c < p.2.2 + 2 ^ p.2.1
  | [], s, off, c, h1, h2 => by
    simp only [piecesOfSize] at h2
    omega
  | n :: ns, s, off, c, h1, h2 => by
    cases hb : n.testBit b with
    | true =>
      rw [piecesOfSize_cons_true hb] at h2 ⊢
      by_cases hc : c < off + 2 ^ b
      · exact ⟨(s, b, off), List.mem_cons_self .., by simp, h1, hc⟩
      · obtain ⟨p, hp, a1, a2, a3⟩ :=
          cover_piecesOfSize b ns (s + 1) (off + 2 ^ b) c (by omega) h2
        refine ⟨p, List.mem_cons_of_mem _ hp, ?_, a2, a3⟩
        rw [List.length_cons]
        omega
    | false =>
      rw [piecesOfSize_cons_false hb] at h2 ⊢
      obtain ⟨p, hp, a1, a2, a3⟩ := cover_piecesOfSize b ns (s + 1) off c h1 h2
      refine ⟨p, hp, ?_, a2, a3⟩
      rw [List.length_cons]
      omega

/-- **No gap among all pieces.** -/
theorem cover_piecesBelow (ns : List Nat) : ∀ (k off c : Nat), off ≤ c →
    c < (piecesBelow ns k off).2 →
    ∃ p ∈ (piecesBelow ns k off).1, p.1 < ns.length ∧ p.2.2 ≤ c ∧ c < p.2.2 + 2 ^ p.2.1
  | 0, off, c, h1, h2 => by
    simp only [piecesBelow] at h2
    omega
  | k + 1, off, c, h1, h2 => by
    rw [piecesBelow_succ] at h2 ⊢
    by_cases hc : c < (piecesOfSize k ns 0 off).2
    · obtain ⟨p, hp, a1, a2, a3⟩ := cover_piecesOfSize k ns 0 off c h1 hc
      exact ⟨p, List.mem_append_left _ hp, by omega, a2, a3⟩
    · obtain ⟨p, hp, a⟩ := cover_piecesBelow ns k (piecesOfSize k ns 0 off).2 c (by omega) h2
      exact ⟨p, List.mem_append_right _ hp, a⟩

/-- What is laid stays, and each piece's columns are laid. -/
theorem mem_fold (c : Nat) : ∀ (F : List (Nat × Nat × Nat)) (a : Array Nat),
    (c ∈ a.toList ∨ ∃ p ∈ F, p.2.2 ≤ c ∧ c < p.2.2 + 2 ^ p.2.1) →
    c ∈ (F.foldl layStep a).toList
  | [], a, h => by
    rcases h with h | ⟨p, hp, _⟩
    · exact h
    · cases hp
  | q :: F, a, h => by
    rw [List.foldl_cons]
    refine mem_fold c F _ ?_
    rcases h with h | ⟨p, hp, h1, h2⟩
    · left
      unfold layStep
      rw [Array.toList_append]
      exact List.mem_append_left _ h
    · rcases List.mem_cons.1 hp with e | hp'
      · left
        subst e
        unfold layStep run
        rw [Array.toList_append]
        refine List.mem_append_right _ ?_
        simp only [Array.toList_map, Array.toList_range, List.mem_map, List.mem_range]
        exact ⟨c - p.2.2, by omega, by omega⟩
      · exact Or.inr ⟨p, hp', h1, h2⟩

/-- A column in a piece of segment s is one of segment s's columns. -/
theorem mem_columnsOf {P : List (Nat × Nat × Nat)} {p : Nat × Nat × Nat} (hp : p ∈ P) {c : Nat}
    (h1 : p.2.2 ≤ c) (h2 : c < p.2.2 + 2 ^ p.2.1) (n : Nat) :
    c ∈ (columnsOf P p.1 n).toList := by
  rw [columnsOf_eq, Array.toList_append]
  refine List.mem_append_left _ (mem_fold c _ _ (Or.inr ⟨p, ?_, h1, h2⟩))
  exact List.mem_filter.2 ⟨hp, by simp⟩

theorem lt_of_mem {a : Array Nat} {Q : Nat → Prop} {top : Nat} (R : Rising a Q top) {j : Nat}
    (h : j ∈ a.toList) : j < top := by
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem h
  have hi' : i < a.size := by simpa using hi
  have k := R.lt i hi'
  have e2 : a.getD i 0 = j := by
    rw [← e]
    simp [Array.getD, hi']
  omega

/-- Where no segment lists a column its entry stays. -/
theorem marks_none (j : Nat) : ∀ (segs : List Seg) (u : Array Nat),
    (∀ s ∈ segs, j ∉ s.pos.toList) → (segs.foldl markUsed u).getD j 0 = u.getD j 0
  | [], _, _ => rfl
  | g :: segs, u, h => by
    rw [List.foldl_cons, marks_none j segs _ fun s hs => h s (List.mem_cons_of_mem _ hs)]
    exact (markUsed_get u g j).2.2 (h g (List.mem_cons_self ..))

/-- **The columns that a placed call's segments take are those below the sum of the lengths.** -/
theorem place_used_iff (name kind : String) (asks : List SegAsk) (fl : Nat)
    (hlen : ∀ a ∈ asks, a.2.1 < 2 ^ (topBit + 1)) (j : Nat)
    (hj : j < (place name kind asks fl).J) :
    ((place name kind asks fl).used.getD j 0 == 0) = decide ((asks.map (·.2.1)).sum ≤ j) := by
  have hS : (piecesBelow (asks.map (·.2.1)) (topBit + 1) 0).2 = (asks.map (·.2.1)).sum :=
    piecesBelow_total _ _ fun n hn => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hn
      exact hlen a ha
  have hu : (place name kind asks fl).used =
      (asks.zipIdx.map (segAt asks)).foldl markUsed
        (Array.replicate (place name kind asks fl).J 0) := rfl
  rw [hu]
  by_cases hc : (asks.map (·.2.1)).sum ≤ j
  · rw [decide_eq_true hc, marks_none j _ _ ?_, getD_replicate_zero]
    · rfl
    · intro s hs hm
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hs
      have k := lt_of_mem (segAt_rising asks hlen z hz).2 hm
      omega
  · rw [decide_eq_false hc]
    obtain ⟨p, hp, a1, a2, a3⟩ := cover_piecesBelow (asks.map (·.2.1)) (topBit + 1) 0 j
      (Nat.zero_le _) (by omega)
    rw [List.length_map] at a1
    have hz : (asks[p.1], p.1) ∈ asks.zipIdx :=
      List.mem_iff_getElem.2 ⟨p.1, by simpa using a1, by simp⟩
    have hne := marks_made j (asks.zipIdx.map (segAt asks))
      (Array.replicate (place name kind asks fl).J 0) (by simpa using hj)
      ⟨segAt asks (asks[p.1], p.1), List.mem_map.2 ⟨_, hz, rfl⟩, mem_columnsOf hp a2 a3 _⟩
    exact beq_eq_false_iff_ne.2 hne

/-- How many j below J have S ≤ j and j / M = t, each weighed with T. -/
theorem count_block (S M t T : Nat) (hM : 0 < M) : ∀ J : Nat,
    ((List.range J).map fun j => if decide (S ≤ j) = true ∧ j / M = t then T else 0).sum =
      T * (min (t * M + M) J - max (t * M) S)
  | 0 => by simp
  | J + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, count_block S M t T hM J]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
      decide_eq_true_eq]
    have hd : J / M = t ↔ t * M ≤ J ∧ J < t * M + M :=
      ⟨fun h => in_block hM h, fun h => Nat.div_eq_of_lt_le h.1 (by rw [Nat.succ_mul]; exact h.2)⟩
    by_cases hc : S ≤ J ∧ J / M = t
    · rw [if_pos hc]
      obtain ⟨h3, h4⟩ := hd.1 hc.2
      have h5 := hc.1
      generalize t * M = a at h3 h4 ⊢
      have e : min (a + M) (J + 1) - max a S = (min (a + M) J - max a S) + 1 := by omega
      rw [e, Nat.mul_succ]
    · rw [if_neg hc]
      have h3 : ¬ (S ≤ J ∧ t * M ≤ J ∧ J < t * M + M) := fun h => hc ⟨h.1, hd.2 h.2⟩
      generalize t * M = a at h3 ⊢
      have e : min (a + M) (J + 1) - max a S = min (a + M) J - max a S := by omega
      rw [e, Nat.add_zero]

/-- The sum of a call's segments' lengths. -/
def takenOf (cd : CallD) : Nat := (cd.segs.map (·.n)).sum

theorem map_segAt (asks all : List SegAsk) : ∀ k : Nat,
    ((asks.zipIdx k).map (segAt all)).map (·.n) = asks.map (·.2.1) := by
  induction asks with
  | nil => intro k; rfl
  | cons a l ih =>
    intro k
    rw [List.zipIdx_cons, List.map_cons, List.map_cons, List.map_cons, ih (k + 1)]
    rfl

theorem takenOf_place (name kind : String) (asks : List SegAsk) (fl : Nat) :
    takenOf (place name kind asks fl) = (asks.map (·.2.1)).sum := by
  unfold takenOf
  rw [place_segs_eq, map_segAt]

/-- The closed form of a tree's count. -/
def formAt (T cs : Nat) (fs : Forest.Shape) (calls : List CallD) (θ : Nat) : Nat :=
  (calls.zipIdx.map fun x =>
    if fs.first.getD x.2 0 ≤ θ then
      T * (min ((θ - fs.first.getD x.2 0) * 2 ^ cs + 2 ^ cs) x.1.J -
        max ((θ - fs.first.getD x.2 0) * 2 ^ cs) (takenOf x.1))
    else 0).sum

/-- What one placed call adds at one tree. -/
theorem colsAt_form (T cs base : Nat) (name kind : String) (asks : List SegAsk) (fl : Nat)
    (hlen : ∀ a ∈ asks, a.2.1 < 2 ^ (topBit + 1)) (θ : Nat) :
    colsAt T cs base (place name kind asks fl) θ =
      if base ≤ θ then
        T * (min ((θ - base) * 2 ^ cs + 2 ^ cs) (place name kind asks fl).J -
          max ((θ - base) * 2 ^ cs) (takenOf (place name kind asks fl)))
      else 0 := by
  by_cases hb : base ≤ θ
  · rw [if_pos hb]
    obtain ⟨t, rfl⟩ : ∃ t, θ = base + t := ⟨θ - base, by omega⟩
    rw [colsAt_in, Nat.add_sub_cancel_left, takenOf_place,
      ← count_block _ _ t T (Nat.two_pow_pos cs)]
    congr 1
    refine List.map_congr_left fun j hj => ?_
    rw [place_used_iff name kind asks fl hlen j (List.mem_range.1 hj)]
  · rw [if_neg hb]
    unfold colsAt
    refine sum_zero _ _ fun j _ => ?_
    rw [if_neg]
    rintro ⟨_, e⟩
    generalize j / 2 ^ cs = d at e
    omega

theorem asks_lt {name kind : String} {asks : List SegAsk} {fl : Nat}
    (h : ∀ s ∈ (place name kind asks fl).segs, s.n < 2 ^ (topBit + 1)) :
    ∀ a ∈ asks, a.2.1 < 2 ^ (topBit + 1) := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have hz : (asks[i], i) ∈ asks.zipIdx := List.mem_iff_getElem.2 ⟨i, by simpa using hi, by simp⟩
  exact h (segAt asks (asks[i], i)) (by rw [place_segs_eq]; exact List.mem_map.2 ⟨_, hz, rfl⟩)

theorem fst_mem' {α : Type} : ∀ (l : List α) (k : Nat) (x : α × Nat), x ∈ l.zipIdx k → x.1 ∈ l
  | [], _, _, h => absurd h (by simp)
  | a :: l, k, x, h => by
    rw [List.zipIdx_cons] at h
    rcases List.mem_cons.1 h with e | h'
    · subst e
      exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (fst_mem' l (k + 1) x h')

/-- **The counts in closed form.** -/
theorem pub_value (T cs : Nat) (fs : Forest.Shape) (calls : List CallD)
    (hp : ∀ cd ∈ calls, ∃ name kind asks fl, cd = place name kind asks fl)
    (hn : ∀ cd ∈ calls, ∀ s ∈ cd.segs, s.n < 2 ^ (topBit + 1)) :
    calls.zipIdx.foldl (fun pub x => addCols T cs (fs.first.getD x.2 0) x.1 pub)
      (Array.replicate fs.NT 0) = ((List.range fs.NT).map (formAt T cs fs calls)).toArray := by
  obtain ⟨s, f⟩ := calls_add
    (fun (x : CallD × Nat) pub => addCols T cs (fs.first.getD x.2 0) x.1 pub)
    (fun x θ => colsAt T cs (fs.first.getD x.2 0) x.1 θ) fs.NT
    (fun x pub hs => addCols_adds T cs _ fs.NT x.1 pub hs) calls.zipIdx
    (Array.replicate fs.NT 0) (by simp)
  generalize calls.zipIdx.foldl (fun pub x => addCols T cs (fs.first.getD x.2 0) x.1 pub)
    (Array.replicate fs.NT 0) = A at s f ⊢
  refine Array.ext (by rw [s]; simp) fun i h1 h2 => ?_
  have hi : i < fs.NT := by rw [s] at h1; exact h1
  have g := f i hi
  rw [getD_replicate_zero, Nat.zero_add] at g
  have e1 : A[i] = A.getD i 0 := by simp [Array.getD, h1]
  rw [e1, g]
  simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
  unfold formAt
  congr 1
  refine List.map_congr_left fun x hx => ?_
  obtain ⟨name, kind, asks, fl, e⟩ := hp x.1 (fst_mem' _ _ _ hx)
  have hl := hn x.1 (fst_mem' _ _ _ hx)
  rw [e] at hl ⊢
  exact colsAt_form T cs _ name kind asks fl (asks_lt hl) i

end AtFull.Head

#print axioms AtFull.Head.cover_piecesOfSize
#print axioms AtFull.Head.cover_piecesBelow
#print axioms AtFull.Head.mem_fold
#print axioms AtFull.Head.mem_columnsOf
#print axioms AtFull.Head.lt_of_mem
#print axioms AtFull.Head.marks_none
#print axioms AtFull.Head.place_used_iff
#print axioms AtFull.Head.count_block
#print axioms AtFull.Head.map_segAt
#print axioms AtFull.Head.takenOf_place
#print axioms AtFull.Head.colsAt_form
#print axioms AtFull.Head.asks_lt
#print axioms AtFull.Head.fst_mem'
#print axioms AtFull.Head.pub_value
