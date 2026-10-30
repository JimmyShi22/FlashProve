-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndReads.lean: every place of a table's vector that a read of the smallness test
names lies below the vector's length, and the vector is there: from objectsF's own tests
(OnBytes/Model/Tail.lean).

Definitions, and theorems with their proofs. Before objectsF adds a read it tests that the read's
vector is there, and it marks each place that the read names in an array of marks that has one mark
for each place of the part of the vector that holds tables; a place outside that part is refused. At
its end it tests that the part ends at or before the vector's length.

Main names:
  `markLoop_spec`, `markRead_spec`: marking keeps the arrays' sizes, and every place marked lies in
    the part.
  `tablesTile_le`: the part ends at or before the vector's length, where the vector is there.
  `stepM`: one read, as far as its vector and its marks go.
  `runFold_marks`: the reads one after the other.
  `objectsF_reads`: if objectsF returns, then for every read the vector is there, and every place
    that the read names lies below the length that the smallness test's state holds for the vector.

Limits: nothing on what the reads add (OnBytes/Tie/Pv/Tail/EndLoops.lean). That the state's length
of a vector is the number of columns of its array is not stated here
(OnBytes/Tie/Pv/Tail/EndAdd.lean).


-/
import OnBytes.Tie.Pv.Tail.EndLoops

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port

/-- Marking the places of one read keeps the number of marks, and every place lies in the part. -/
theorem markLoop_spec (tl : HTailF2) (Fn : HFun) (sg t0 : Nat) :
    ∀ (count c : Nat) (marks marks' : Array Bool),
      tl.markLoop Fn sg t0 count c marks = some marks' →
      marks'.size = marks.size ∧
        ∀ d, c ≤ d → d < c + count → posOf tl Fn sg d < t0 + marks.size
  | 0, c, marks, marks', h => by
    simp only [HTailF2.markLoop, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun d h1 h2 => by omega⟩
  | count + 1, c, marks, marks', h => by
    simp only [HTailF2.markLoop] at h
    cases hp : tl.tabAt Fn c sg with
    | none => simp [hp] at h
    | some pos =>
      simp only [hp] at h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
        obtain ⟨e1, e2⟩ := markLoop_spec tl Fn sg t0 count (c + 1) _ _ h
        have hsz : (marks.set! (pos - t0) true).size = marks.size := by simp
        refine ⟨e1.trans hsz, fun d h1 h2 => ?_⟩
        by_cases hd : d = c
        · subst hd
          have hlt : pos - t0 < marks.size := by
            by_contra hge
            have : marks.getD (pos - t0) true = true := by simp [Array.getD, hge]
            rw [this] at hc
            exact absurd hc.2 (by simp)
          unfold posOf
          rw [hp]
          show pos < _
          omega
        · have := e2 d (by omega) (by omega)
          rw [hsz] at this
          exact this
      · simp at h

/-- The number of marks of part p. -/
def marksOf (rd : Array (Array Bool)) (p : Nat) : Nat := (rd.getD p #[]).size

/-- Marking the places of one read keeps the numbers of marks, and every place lies in its part. -/
theorem markRead_spec (tl : HTailF2) (Fn : HFun) (sg : Nat) (rd rd' : Array (Array Bool))
    (h : tl.markRead Fn sg rd = some rd') :
    (∀ p, marksOf rd' p = marksOf rd p) ∧
      ∀ d, d < (tl.mats.getD Fn.mat {}).k →
        posOf tl Fn sg d < tl.tabFirst.getD (Fn.tree / 2) 0 + marksOf rd (Fn.tree / 2) := by
  unfold HTailF2.markRead at h
  simp only [] at h
  cases hm : tl.markLoop Fn sg (tl.tabFirst.getD (Fn.tree / 2) 0) (tl.mats.getD Fn.mat {}).k 0
      (rd.getD (Fn.tree / 2) #[]) with
  | none =>
    rw [hm] at h
    exact absurd h (by simp)
  | some marks =>
    simp only [hm, Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨e1, e2⟩ := markLoop_spec tl Fn sg _ _ _ _ _ hm
    refine ⟨fun p => ?_, fun d hd => e2 d (by omega) (by omega)⟩
    unfold marksOf
    by_cases hp : p = Fn.tree / 2
    · subst hp
      by_cases hlt : Fn.tree / 2 < rd.size
      · have : ((rd.set! (Fn.tree / 2) #[]).set! (Fn.tree / 2) marks).getD (Fn.tree / 2) #[] =
            marks := by
          simp [Array.getD, hlt]
        rw [this, e1]
      · have : ((rd.set! (Fn.tree / 2) #[]).set! (Fn.tree / 2) marks).getD (Fn.tree / 2) #[] =
            rd.getD (Fn.tree / 2) #[] := by
          simp [Array.getD, hlt]
        rw [this]
    · have : ((rd.set! (Fn.tree / 2) #[]).set! (Fn.tree / 2) marks).getD p #[] =
          rd.getD p #[] := by
        by_cases hlt : p < rd.size
        · simp [Array.getD, hlt, Ne.symm hp]
        · simp [Array.getD, hlt]
      rw [this]

/-- The part of a vector that holds tables ends at or before the vector's length. -/
theorem tablesTile_le (tl : HTailF2) (funs : Array HFun) (un s : Nat)
    (h : tl.tablesTile funs un = some s) (hU : (tl.ix.U.getD un none).isSome = true) :
    tl.tabFirst.getD (un / 2) 0 + tl.tabLen.getD (un / 2) 0 ≤ tl.nUF.getD un 0 := by
  unfold HTailF2.tablesTile at h
  simp only [] at h
  obtain ⟨⟨pos, segs⟩, -, h⟩ := Option.bind_eq_some_iff.1 h
  simp only [] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc.2 with hn | hle
    · rw [Option.isNone_iff_eq_none] at hn
      rw [hn] at hU
      simp at hU
    · omega
  · simp at h

/-- One read, as far as its vector and its marks go. -/
def stepM (tl : HTailF2) (x : HFun × Nat) (b : MProd Nat (Array (Array Bool))) (_ : Fork)
    (_ : Ctx) (b1 : MProd Nat (Array (Array Bool))) (_ : Fork) (_ : Ctx) : Prop :=
  (tl.ix.U.getD x.1.tree none).isSome = true ∧ tl.markRead x.1 x.2 b.snd = some b1.snd

/-- The reads one after the other: each read's vector is there, and its places lie in their part. -/
theorem runFold_marks (tl : HTailF2) (len : Nat → Nat) :
    ∀ (l : List (HFun × Nat)) (b : MProd Nat (Array (Array Bool))) (F : Fork) (c : Ctx)
      (b' : MProd Nat (Array (Array Bool))) (F' : Fork) (c' : Ctx),
      RunFoldS (stepM tl) l b F c b' F' c' → (∀ p, marksOf b.snd p = len p) →
      ∀ x ∈ l, (tl.ix.U.getD x.1.tree none).isSome = true ∧
        ∀ d, d < (tl.mats.getD x.1.mat {}).k →
          posOf tl x.1 x.2 d < tl.tabFirst.getD (x.1.tree / 2) 0 + len (x.1.tree / 2)
  | [], _, _, _, _, _, _, _, _ => fun _ hx => absurd hx (List.not_mem_nil)
  | a :: l, b, F, c, b', F', c', h, h0 => by
    obtain ⟨b1, F1, c1, ⟨hs, hm⟩, hr⟩ := h
    obtain ⟨e1, e2⟩ := markRead_spec tl a.1 a.2 _ _ hm
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · refine ⟨hs, fun d hd => ?_⟩
      rw [← h0]
      exact e2 d hd
    · exact runFold_marks tl len l b1 F1 c1 b' F' c' hr (fun p => (e1 p).trans (h0 p)) x hx

/-- If objectsF returns: for every read the vector is there, and every place that the read names
lies below the length that the smallness test's state holds for the vector. -/
theorem objectsF_reads (tl tl' : HTailF2) (funs : Array HFun) (F G : Fork) (c c' : Ctx)
    (h : tl.objectsF funs F c = .ok ((tl', G), c')) :
    ∀ x ∈ readsList tl' funs, (tl'.ix.U.getD x.1.tree none).isSome = true ∧
      ∀ d, d < (tl'.mats.getD x.1.mat {}).k →
        posOf tl' x.1 x.2 d < tl'.nUF.getD x.1.tree 0 := by
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
  obtain ⟨_, _, _, ⟨⟨_, rfl⟩, rfl⟩, _, _, _, ⟨⟨_, rfl⟩, rfl⟩, _, _, _, ⟨ht0, rfl, rfl⟩,
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
  have hall := runFold_marks tl1 (fun p => tl1.tabLen.getD p 0) _ _ _ _ _ _ _ fP (by
    intro p
    unfold marksOf
    by_cases hp : p < tl1.tabLen.size
    · simp [Array.getD, hp]
    · simp [Array.getD, hp])
  intro x hx
  obtain ⟨hs, hp⟩ := hall x hx
  refine ⟨hs, fun d hd => ?_⟩
  have hlt := hp d hd
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
  have hle : tl1.tabFirst.getD (x.1.tree / 2) 0 + tl1.tabLen.getD (x.1.tree / 2) 0 ≤
      tl1.nUF.getD x.1.tree 0 := by
    rcases hun with e | e
    · rw [e] at hs ⊢
      exact tablesTile_le tl1 funs 0 _ ht0 hs
    · rw [e] at hs ⊢
      exact tablesTile_le tl1 funs 2 _ ht2 hs
  exact Nat.lt_of_lt_of_le hlt hle

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.objectsF_reads
