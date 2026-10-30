-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndCover.lean: every place of the part of a vector that holds tables is named by
a read of the smallness test: from objectsF's own tests (OnBytes/Model/Tail.lean).

Definitions, and theorems with their proofs. objectsF keeps one mark for each place of the part of
U1, and of U3, that holds tables. All marks begin unset. A mark is set only where a read is added,
at the places that the read names, by the function that also gives the read's claim its places
(`tabAt`). At its end objectsF tests that all marks are set. OnBytes/Tie/Pv/Tail/EndReads.lean has
the other direction: every place that a read names lies in the part.

Main names:
  `markAt rd p i`: mark i of part p is set.
  `markLoop_marks`, `markRead_marks`: a mark that is set after a read was set before, or is at a
    place that the read names.
  `runFold_cover`: the reads one after the other.
  `objectsF_marks`: the run of objectsF, as far as the marks go. `cover_of_marks`: what follows from
    it.
  `objectsF_cover`: if objectsF returns, then every place of the part is named by a read, at one of
    its matrix's columns.
  `objectsF_coverU3`: where the part of U3 begins at 0 and has the vector's length: every place
    below the length.

Limits: nothing on whether two reads name one place (objectsF refuses that too: a mark that is set
is not set again; not stated here). Nothing on what the reads add. That the part of U3 is the whole
vector is a premise of `objectsF_coverU3`.


-/
import OnBytes.Tie.Pv.Tail.EndReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port

/-- A mark that is set after the places of one read are marked was set before, or is at a place that
the read names. -/
theorem markLoop_marks (tl : HTailF2) (Fn : HFun) (sg t0 : Nat) :
    ∀ (count c : Nat) (marks marks' : Array Bool),
      tl.markLoop Fn sg t0 count c marks = some marks' →
      ∀ i, marks'.getD i false = true → marks.getD i false = true ∨
        ∃ d, c ≤ d ∧ d < c + count ∧ posOf tl Fn sg d = t0 + i
  | 0, c, marks, marks', h => by
    simp only [HTailF2.markLoop, Option.some.injEq] at h
    subst h
    exact fun i hi => Or.inl hi
  | count + 1, c, marks, marks', h => by
    simp only [HTailF2.markLoop] at h
    cases hp : tl.tabAt Fn c sg with
    | none => simp [hp] at h
    | some pos =>
      simp only [hp] at h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
        intro i hi
        rcases markLoop_marks tl Fn sg t0 count (c + 1) _ _ h i hi with h1 | ⟨d, d1, d2, d3⟩
        · by_cases hie : i = pos - t0
          · refine Or.inr ⟨c, Nat.le_refl _, by omega, ?_⟩
            unfold posOf
            rw [hp]
            show pos = _
            omega
          · left
            have e : (marks.set! (pos - t0) true).getD i false = marks.getD i false := by
              by_cases hlt : i < marks.size
              · simp [Array.getD, hlt, Ne.symm hie]
              · simp [Array.getD, hlt]
            rw [e] at h1
            exact h1
        · exact Or.inr ⟨d, by omega, by omega, d3⟩
      · simp at h

/-- Mark i of part p is set. -/
def markAt (rd : Array (Array Bool)) (p i : Nat) : Prop := (rd.getD p #[]).getD i false = true

/-- A mark that is set after one read was set before, or is at a place that the read names. -/
theorem markRead_marks (tl : HTailF2) (Fn : HFun) (sg : Nat) (rd rd' : Array (Array Bool))
    (h : tl.markRead Fn sg rd = some rd') (p i : Nat) (hm : markAt rd' p i) :
    markAt rd p i ∨ (p = Fn.tree / 2 ∧ ∃ d, d < (tl.mats.getD Fn.mat {}).k ∧
      posOf tl Fn sg d = tl.tabFirst.getD p 0 + i) := by
  unfold HTailF2.markRead at h
  simp only [] at h
  cases hl : tl.markLoop Fn sg (tl.tabFirst.getD (Fn.tree / 2) 0) (tl.mats.getD Fn.mat {}).k 0
      (rd.getD (Fn.tree / 2) #[]) with
  | none =>
    rw [hl] at h
    exact absurd h (by simp)
  | some marks =>
    simp only [hl, Option.map_some, Option.some.injEq] at h
    subst h
    unfold markAt at hm ⊢
    by_cases hp : p = Fn.tree / 2
    · subst hp
      by_cases hlt : Fn.tree / 2 < rd.size
      · have e : ((rd.set! (Fn.tree / 2) #[]).set! (Fn.tree / 2) marks).getD (Fn.tree / 2) #[] =
            marks := by
          simp [Array.getD, hlt]
        rw [e] at hm
        rcases markLoop_marks tl Fn sg _ _ _ _ _ hl i hm with h1 | ⟨d, -, d2, d3⟩
        · exact Or.inl h1
        · exact Or.inr ⟨rfl, d, by omega, d3⟩
      · have e : ((rd.set! (Fn.tree / 2) #[]).set! (Fn.tree / 2) marks).getD (Fn.tree / 2) #[] =
            rd.getD (Fn.tree / 2) #[] := by
          simp [Array.getD, hlt]
        rw [e] at hm
        exact Or.inl hm
    · have e : ((rd.set! (Fn.tree / 2) #[]).set! (Fn.tree / 2) marks).getD p #[] =
          rd.getD p #[] := by
        by_cases hlt : p < rd.size
        · simp [Array.getD, hlt, Ne.symm hp]
        · simp [Array.getD, hlt]
      rw [e] at hm
      exact Or.inl hm

/-- The reads one after the other: a mark that is set at the end was set at the start, or is at a
place that one of the reads names. -/
theorem runFold_cover (tl : HTailF2) :
    ∀ (l : List (HFun × Nat)) (b : MProd Nat (Array (Array Bool))) (F : Fork) (c : Ctx)
      (b' : MProd Nat (Array (Array Bool))) (F' : Fork) (c' : Ctx),
      RunFoldS (stepM tl) l b F c b' F' c' → ∀ p i, markAt b'.snd p i →
      markAt b.snd p i ∨ ∃ x ∈ l, p = x.1.tree / 2 ∧ ∃ d, d < (tl.mats.getD x.1.mat {}).k ∧
        posOf tl x.1 x.2 d = tl.tabFirst.getD p 0 + i
  | [], b, _, _, b', _, _, h, p, i, hm => by
    obtain ⟨rfl, -, -⟩ := h
    exact Or.inl hm
  | a :: l, b, F, c, b', F', c', h, p, i, hm => by
    obtain ⟨b1, F1, c1, ⟨-, hr⟩, ht⟩ := h
    rcases runFold_cover tl l b1 F1 c1 b' F' c' ht p i hm with h1 | ⟨x, hx, e, d, d1, d2⟩
    · rcases markRead_marks tl a.1 a.2 _ _ hr p i h1 with h2 | ⟨e, d, d1, d2⟩
      · exact Or.inl h2
      · exact Or.inr ⟨a, List.mem_cons_self, e, d, d1, d2⟩
    · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, e, d, d1, d2⟩

/-- The numbers of marks stay as they were. -/
theorem runFold_sizes (tl : HTailF2) :
    ∀ (l : List (HFun × Nat)) (b : MProd Nat (Array (Array Bool))) (F : Fork) (c : Ctx)
      (b' : MProd Nat (Array (Array Bool))) (F' : Fork) (c' : Ctx),
      RunFoldS (stepM tl) l b F c b' F' c' → ∀ p, marksOf b'.snd p = marksOf b.snd p
  | [], b, _, _, b', _, _, h, p => by
    obtain ⟨rfl, -, -⟩ := h
    rfl
  | a :: l, b, F, c, b', F', c', h, p => by
    obtain ⟨b1, F1, c1, ⟨-, hr⟩, ht⟩ := h
    exact (runFold_sizes tl l b1 F1 c1 b' F' c' ht p).trans ((markRead_spec tl a.1 a.2 _ _ hr).1 p)

/-- Inside an array the entry is returned. -/
theorem getD_lt {α : Type} (a : Array α) (i : Nat) (d : α) (h : i < a.size) :
    a.getD i d = a[i] := by
  simp [Array.getD, h]

/-- The run of objectsF, as far as the marks go: the reads, one after the other, lead from marks
that are all unset to marks that are all set. tl1: the record that objectsF returns, before its last
four fields are set. -/
theorem objectsF_marks (tl tl' : HTailF2) (funs : Array HFun) (F G : Fork) (c c' : Ctx)
    (h : tl.objectsF funs F c = .ok ((tl', G), c')) :
    ∃ (tl1 : HTailF2) (b' : MProd Nat (Array (Array Bool))) (Fx Fy : Fork) (cx cy : Ctx)
      (t1 t2 : Array Nat) (t3 : Nat) (t4 : Array E),
      tl' = { tl1 with tieObj := t1, tiesOn := t2, nX4Laid := t3, lsTail := t4 } ∧
      RunFoldS (stepM tl1) (readsList tl1 funs)
        ⟨0, tl1.tabLen.map fun n => Array.replicate n false⟩ Fx cx b' Fy cy ∧
      (b'.snd.all fun a => a.all id) = true := by
  unfold HTailF2.objectsF at h
  simp only [bind_ok, get_ok, ask_ok, lift_ok, mustAs_ok, Option.some.injEq, SubM.claims] at h
  obtain ⟨_, _, _, ⟨⟨_, rfl⟩, rfl⟩, _, _, _, ⟨⟨hfh, rfl⟩, rfl⟩, _, _, _, ⟨_, rfl, rfl⟩,
    _, _, _, ⟨ht, rfl⟩, h⟩ := h
  have := testAs_ctx _ _ _ _ _ ht
  subst this
  obtain ⟨g, _, _, ⟨hg, rfl, rfl⟩, _, _, _, ⟨_, rfl, rfl⟩, _, Fa, ca, hFo, _, _, _, ⟨_, rfl, rfl⟩,
    _, _, _, ⟨⟨_, rfl⟩, rfl⟩, _, _, _, ⟨_, rfl, rfl⟩, tla, Fb, cb, hJ, tlb, Fc, cc, hB,
    _, _, _, ⟨_, rfl, rfl⟩, _, _, _, ⟨⟨_, rfl⟩, rfl⟩, tl1, F1, c1, hWt, h⟩ := h
  obtain ⟨_, F1', c1', ⟨_, hF1, hc1⟩, bT, F2, c2, hT, bR, F3, c3, hR, h⟩ := h
  obtain ⟨_, _, _, ⟨⟨_, rfl⟩, rfl⟩, _, _, _, ⟨⟨hrd, rfl⟩, rfl⟩, _, _, _, ⟨ht0, rfl, rfl⟩,
    _, _, _, ⟨ht2, rfl, rfl⟩, _, _, _, ⟨_, rfl, rfl⟩, _, _, _, ⟨⟨_, rfl⟩, rfl⟩,
    _, _, _, ⟨⟨_, rfl⟩, rfl⟩, _, _, _, ⟨⟨_, rfl⟩, rfl⟩, _, _, _, ⟨_, rfl, rfl⟩, h⟩ := h
  obtain ⟨rfl, rfl, rfl⟩ := (pure_ok _ _ _ _ _ _).1 h
  -- the reads: four loops, flattened
  have rR := forInS_inv _
    (fun mu => RunFoldS (fun un => RunFoldS (fun (Fn : HFun) => RunFoldS (stepM tl1)
      (segsOf tl1 mu un Fn)) funs.toList) [0, 2])
    (by
      intro mu b F c r F' c' hb
      simp only [bind_ok, pure_ok] at hb
      obtain ⟨b2, Fx, cx, h2, _, _, _, ⟨_, rfl, rfl⟩, rfl, rfl, rfl⟩ := hb
      refine ⟨_, rfl, ?_⟩
      refine forInS_inv _ _ ?_ _ _ _ _ _ _ _ h2
      intro un b F c r F' c' hb
      simp only [bind_ok, pure_ok] at hb
      obtain ⟨b3, Fx, cx, h3, _, _, _, ⟨_, rfl, rfl⟩, rfl, rfl, rfl⟩ := hb
      refine ⟨_, rfl, ?_⟩
      refine forInS_inv_array _ _ ?_ _ _ _ _ _ _ _ h3
      intro Fn b F c r F' c' hb
      by_cases hc : (Fn.mat == mu && Fn.tree == un) = true
      · rw [if_pos hc] at hb
        simp only [bind_ok, pure_ok, lift_ok, mustAs_ok] at hb
        obtain ⟨_, _, _, ⟨⟨hsome, rfl⟩, rfl⟩, _, _, _, ⟨⟨_, rfl⟩, rfl⟩, b4, Fx, cx, h4,
          _, _, _, ⟨_, rfl, rfl⟩, rfl, rfl, rfl⟩ := hb
        refine ⟨_, rfl, ?_⟩
        rw [segsOf, if_pos hc]
        apply runFold_map
        refine forInS_inv _ _ ?_ _ _ _ _ _ _ _ h4
        intro sg b F c r F' c' hb
        simp only [bind_ok, pure_ok, get_ok] at hb
        obtain ⟨rd, _, _, ⟨hmr, rfl, rfl⟩, _, Fy, cy, hl, _, _, _, ⟨_, rfl, rfl⟩, rfl, rfl,
          rfl⟩ := hb
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        refine ⟨_, rfl, ?_, hmr⟩
        show (tl1.ix.U.getD Fn.tree none).isSome = true
        rw [hc.2]
        exact hsome
      · rw [if_neg hc] at hb
        simp only [bind_ok, pure_ok] at hb
        obtain ⟨_, _, _, ⟨_, rfl, rfl⟩, rfl, rfl, rfl⟩ := hb
        refine ⟨_, rfl, ?_⟩
        rw [segsOf, if_neg hc]
        exact ⟨rfl, rfl, rfl⟩) _ _ _ _ _ _ _ hR
  have s1 := runFold_mono _
    (fun mu => RunFoldS (fun un => RunFoldS (stepM tl1)
      (funs.toList.flatMap (segsOf tl1 mu un))) [0, 2])
    (fun mu _ _ _ _ _ _ h2 => runFold_mono _
      (fun un => RunFoldS (stepM tl1) (funs.toList.flatMap (segsOf tl1 mu un)))
      (fun un _ _ _ _ _ _ h3 => runFold_flat (stepM tl1) (segsOf tl1 mu un) _ _ _ _ _ _ _ h3)
      _ _ _ _ _ _ _ h2) _ _ _ _ _ _ _ rR
  have s2 := runFold_mono _
    (fun mu => RunFoldS (stepM tl1)
      ([0, 2].flatMap fun un => funs.toList.flatMap (segsOf tl1 mu un)))
    (fun mu _ _ _ _ _ _ h2 => runFold_flat (stepM tl1)
      (fun un => funs.toList.flatMap (segsOf tl1 mu un)) _ _ _ _ _ _ _ h2) _ _ _ _ _ _ _ s1
  have fP := runFold_flat (stepM tl1)
    (fun mu => [0, 2].flatMap fun un => funs.toList.flatMap (segsOf tl1 mu un)) _ _ _ _ _ _ _ s2
  exact ⟨tl1, _, _, _, _, _, _, _, _, _, rfl, fP, hrd⟩

/-- Where the reads lead from marks that are all unset to marks that are all set, every place of the
part is named by a read. -/
theorem cover_of_marks (tl1 : HTailF2) (funs : Array HFun)
    (b' : MProd Nat (Array (Array Bool))) (Fx Fy : Fork) (cx cy : Ctx)
    (hr : RunFoldS (stepM tl1) (readsList tl1 funs)
      ⟨0, tl1.tabLen.map fun n => Array.replicate n false⟩ Fx cx b' Fy cy)
    (hall : (b'.snd.all fun a => a.all id) = true) (p i : Nat) (hi : i < tl1.tabLen.getD p 0) :
    ∃ x ∈ readsList tl1 funs, p = x.1.tree / 2 ∧ ∃ d, d < (tl1.mats.getD x.1.mat {}).k ∧
      posOf tl1 x.1 x.2 d = tl1.tabFirst.getD p 0 + i := by
  have h0 : ∀ q, marksOf (tl1.tabLen.map fun n => Array.replicate n false) q =
      tl1.tabLen.getD q 0 := by
    intro q
    unfold marksOf
    by_cases hq : q < tl1.tabLen.size
    · simp [Array.getD, hq]
    · simp [Array.getD, hq]
  have hs : marksOf b'.snd p = tl1.tabLen.getD p 0 :=
    (runFold_sizes tl1 _ _ _ _ _ _ _ hr p).trans (h0 p)
  have hset : markAt b'.snd p i := by
    unfold markAt
    unfold marksOf at hs
    have hlt : i < (b'.snd.getD p #[]).size := by omega
    have hp : p < b'.snd.size := by
      by_contra hge
      have : b'.snd.getD p #[] = #[] := by simp [Array.getD, hge]
      rw [this] at hlt
      simp at hlt
    have hmem : b'.snd.getD p #[] ∈ b'.snd := by
      rw [getD_lt _ _ _ hp]
      exact Array.getElem_mem hp
    have ha := (Array.all_eq_true_iff_forall_mem.1 hall) _ hmem
    have hb := (Array.all_eq_true_iff_forall_mem.1 ha) _ (Array.getElem_mem hlt)
    rw [getD_lt _ _ _ hlt]
    exact hb
  rcases runFold_cover tl1 _ _ _ _ _ _ _ hr p i hset with h1 | h1
  · exfalso
    unfold markAt at h1
    by_cases hq : p < tl1.tabLen.size
    · by_cases hi2 : i < tl1.tabLen[p]
      · simp [Array.getD, hq, hi2] at h1
      · simp [Array.getD, hq, hi2] at h1
    · simp [Array.getD, hq] at h1
  · exact h1

/-- If objectsF returns, every place of the part of a vector that holds tables is named by a read.
-/
theorem objectsF_cover (tl tl' : HTailF2) (funs : Array HFun) (F G : Fork) (c c' : Ctx)
    (h : tl.objectsF funs F c = .ok ((tl', G), c')) (p i : Nat) (hi : i < tl'.tabLen.getD p 0) :
    ∃ x ∈ readsList tl' funs, p = x.1.tree / 2 ∧ ∃ d, d < (tl'.mats.getD x.1.mat {}).k ∧
      posOf tl' x.1 x.2 d = tl'.tabFirst.getD p 0 + i := by
  obtain ⟨tl1, b', Fx, Fy, cx, cy, t1, t2, t3, t4, rfl, hr, hall⟩ :=
    objectsF_marks tl tl' funs F G c c' h
  exact cover_of_marks tl1 funs b' Fx Fy cx cy hr hall p i hi

/-- Where the part of U3 begins at 0 and has the vector's length: every place below the length is
named by a read on U3. -/
theorem objectsF_coverU3 (tl tl' : HTailF2) (funs : Array HFun) (F G : Fork) (c c' : Ctx)
    (h : tl.objectsF funs F c = .ok ((tl', G), c')) (hf : tl'.tabFirst.getD 1 0 = 0)
    (hl : tl'.tabLen.getD 1 0 = tl'.nUF.getD 2 0) (pos : Nat) (hp : pos < tl'.nUF.getD 2 0) :
    ∃ x ∈ readsList tl' funs, x.1.tree = 2 ∧ ∃ d, d < (tl'.mats.getD x.1.mat {}).k ∧
      posOf tl' x.1 x.2 d = pos := by
  obtain ⟨x, hx, e, d, d1, d2⟩ := objectsF_cover tl tl' funs F G c c' h 1 pos (by omega)
  refine ⟨x, hx, ?_, d, d1, by omega⟩
  have hun : x.1.tree = 0 ∨ x.1.tree = 2 := by
    obtain ⟨mu, -, hx⟩ := List.mem_flatMap.1 hx
    obtain ⟨un, hun, hx⟩ := List.mem_flatMap.1 hx
    obtain ⟨Fn, -, hx⟩ := List.mem_flatMap.1 hx
    unfold segsOf at hx
    split at hx
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨sg, -, rfl⟩ := List.mem_map.1 hx
      show Fn.tree = 0 ∨ Fn.tree = 2
      rw [hc.2]
      simpa using hun
    · simp at hx
  rcases hun with e0 | e2
  · rw [e0] at e
    omega
  · exact e2

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.objectsF_cover
#print axioms OnBytes.Tie.Pv.Tail.objectsF_coverU3
