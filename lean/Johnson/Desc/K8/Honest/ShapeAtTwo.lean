-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/ShapeAtTwo.lean: WHAT THE VERIFIER's MAKER OF A LOOKUP's SHAPE
(`Forest.shape`, OnBytes/Model/Forest.lean) RETURNS AT TWO CALLS OF AS MANY KEYS: its numbers in
closed form, the two arrays iota and first as arrays. For the smallness test's public test
(Johnson/Desc/K8/Honest/HeldPublic.lean), whose clauses compare these very numbers. Lemmas on the
verifier's own text; none of the library's goals.

  `shape_first_size` the array of the calls' first trees has an entry for each call
  `pair_entries` an array of two numbers is its two entries
  **`shape_two`** Forest.shape #[c1, c2] lid = .ok fo · c2.n = c1.n ⊢, with io := c1.n - min c1.n
                   lid: fo.dT = min c1.n lid · fo.kT = max c1.k c2.k · fo.NT = 2 ^ (io + 1) · fo.rK
                   = io + 1 · fo.iota = #[io, io] · fo.first = #[0, 2 ^ io] · fo.dT + fo.rK < 32
By: the library's `shape_dT` (Johnson/Road/FormsKeysCap.lean) · `shape_numbers`, `forIn_keeps`,
`loopKeeps_step` (Johnson/Road/FormsKeysForest.lean) · `shape_more`
(OnBytes/Tie/Pv/Lookup/Port/FoShape.lean) · `shape_adm` (OnBytes/Tie/Pv/Lookup/Ends/ShapePrem.lean)
· `piecesF_tail_cnt_clog2` (Ends/PiecesFTailCnt.lean).
WRITTEN A FURTHER TIME: the proof of `shape_first_size` is the walk of the library's
`shape_numbers`, whose statement does not hand the array's size: its loop's invariant has it.
Limits. From a return of the routine alone. Nothing on the fields callOf, cK and pub. Two calls of
as many keys, no other case.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Road.FormsKeysForest
import OnBytes.Tie.Pv.Lookup.Port.FoShape
import OnBytes.Tie.Pv.Lookup.Ends.ShapePrem
import OnBytes.Tie.Pv.Lookup.Ends.PiecesFTailCnt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model
open OnBytes.Road (ok_of_bind ok_of_jp forIn_keeps LoopKeeps loopKeeps_step pairwise_byFallingKey
  mem_byFallingKey shape_numbers shape_dT)

/-- The array of the calls' first trees has an entry for each call. -/
theorem shape_first_size {calls : Array Call} {lid : Nat} {fo : Forest.Shape}
    (h : Forest.shape calls lid = .ok fo) : fo.first.size = calls.size := by
  unfold Forest.shape at h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨r, hr, h⟩ := ok_of_bind h
  obtain ⟨callOf, first, free⟩ := r
  obtain ⟨-, h⟩ := ok_of_jp h
  have e := (Except.ok.inj h).symm
  subst e
  generalize hio : (calls.map fun c => c.n - calls.foldl (fun m c => min m c.n) lid) = io at hr
  have K := forIn_keeps _ (byFallingKey calls.size fun c => io.getD c 0)
    (fun pre (s : MProd (Array ℕ) (MProd (Array ℕ) ℕ)) =>
      LoopKeeps (fun c => io.getD c 0) (fun c => 2 ^ io.getD c 0) calls.size pre s.2.1 s.2.2)
    (fun pre a rest e s s' hI hs => by
      obtain ⟨co, fi, fr⟩ := s
      obtain ⟨-, hs⟩ := ok_of_jp hs
      obtain ⟨co', -, hs⟩ := ok_of_bind hs
      have e' := (Except.ok.inj hs).symm
      refine ⟨_, e', ?_⟩
      have pw := pairwise_byFallingKey (fun c => io.getD c 0) calls.size
      rw [e] at pw
      have ha : a < calls.size :=
        (mem_byFallingKey (fun c => io.getD c 0) calls.size a).mp (by rw [e]; simp)
      exact loopKeeps_step hI ha fun x hx =>
        (List.pairwise_append.mp pw).2.2 x hx a List.mem_cons_self)
    (byFallingKey calls.size fun c => io.getD c 0) [] _ _ rfl
    ⟨by simp, rfl, fun c hc => by cases hc⟩ hr
  exact K.1

/-- An array of two numbers is its two entries. -/
theorem pair_entries (a : Array Nat) (hs : a.size = 2) : a = #[a.getD 0 0, a.getD 1 0] := by
  apply Array.ext
  · simp [hs]
  · intro i h1 h2
    have hi : i < 2 := by omega
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
    · obtain rfl : i = 0 := by omega
      simp [Array.getD, hs]
    · subst h
      simp [Array.getD, hs]

/-- **What Forest.shape returns at two calls of as many keys.** -/
theorem shape_two {c1 c2 : Call} {lid : Nat} {fo : Forest.Shape}
    (h : Forest.shape #[c1, c2] lid = .ok fo) (hn : c2.n = c1.n) :
    fo.dT = min c1.n lid ∧ fo.kT = max c1.k c2.k ∧
      fo.NT = 2 ^ (c1.n - min c1.n lid + 1) ∧ fo.rK = c1.n - min c1.n lid + 1 ∧
      fo.iota = #[c1.n - min c1.n lid, c1.n - min c1.n lid] ∧
      fo.first = #[0, 2 ^ (c1.n - min c1.n lid)] ∧ fo.dT + fo.rK < 32 := by
  have d : fo.dT = min c1.n lid := by
    rw [shape_dT h]
    simp only [List.foldl_toArray', List.foldl_cons, List.foldl_nil, hn]
    omega
  obtain ⟨n1, n2, n3, n4⟩ := shape_numbers h
  have i : fo.iota = #[c1.n - min c1.n lid, c1.n - min c1.n lid] := by
    rw [n1, d]
    simp [hn]
  have i0 : fo.iota.getD 0 0 = c1.n - min c1.n lid := by
    rw [i]
    rfl
  have i1 : fo.iota.getD 1 0 = c1.n - min c1.n lid := by
    rw [i]
    rfl
  have sz : (#[c1, c2] : Array Call).size = 2 := rfl
  have t : fo.NT = 2 ^ (c1.n - min c1.n lid + 1) := by
    rw [n2, sz, Finset.sum_range_succ, Finset.sum_range_one, i0, i1, pow_succ]
    omega
  have r : fo.rK = c1.n - min c1.n lid + 1 := by
    rw [n3, t]
    exact _root_.Fo.PiecesF.piecesF_tail_cnt_clog2 _
  have f0 : fo.first.getD 0 0 = 0 := by
    rw [n4 0 (by rw [sz]; omega), sz, Finset.sum_range_succ, Finset.sum_range_one, i0, i1]
    simp
  have f1 : fo.first.getD 1 0 = 2 ^ (c1.n - min c1.n lid) := by
    rw [n4 1 (by rw [sz]; omega), sz, Finset.sum_range_succ, Finset.sum_range_one, i0, i1]
    simp
  have f : fo.first = #[0, 2 ^ (c1.n - min c1.n lid)] := by
    rw [pair_entries fo.first ((shape_first_size h).trans sz), f0, f1]
  have k : fo.kT = max c1.k c2.k := by
    rw [(Cb.Fo.shape_more h).2.2.2.1]
    simp
  exact ⟨d, k, t, r, i, f, (OnBytes.Ends.shape_adm h).1⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.shape_first_size
#print axioms VerifiableInference.Desc.First.K8.Honest.pair_entries
#print axioms VerifiableInference.Desc.First.K8.Honest.shape_two
