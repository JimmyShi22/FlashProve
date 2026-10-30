-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndSyms.lean: every array of the kind «symbols» is the symbol array of a matrix
of the smallness test's list, and so has a tie: from objectsF's own tests (OnBytes/Model/Tail.lean).

Definitions, and theorems with their proofs. While objectsF adds the ties it counts, for each array
of the list, the ties that were added on it. At its end it tests that the count is 1 on each array
of the kind «symbols» and 0 on every other, and that no two matrices have one array.

Main names:
  `stepT`: one tie, as far as the counts go. `runFold_ties`: a count that has changed belongs to the
    array of one of the matrices.
  `allDistinct_nodup`: what the test `allDistinct` says.
  `objectsF_syms`: if objectsF returns, then every array of the kind «symbols» in the state that it
    leaves is `gtTree[mu]` for a matrix mu of the list; and no number occurs twice in `gtTree`.

Limits: the other direction (the array of each matrix is of the kind «symbols») is not stated here;
the verifier's test of the weights has it (`tileSelfTest_shapes`,
OnBytes/Tie/Pv/Tail/EndFrame.lean). Nothing on what a tie adds (OnBytes/Tie/Pv/Tail/EndLoops.lean).


-/
import OnBytes.Tie.Pv.Tail.EndCoef
import OnBytes.Tie.Pv.Tail.EndLoops

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port

/-- One tie, as far as the counts go: the count of the matrix's array rises by one. -/
def stepT (tl : HTailF2) (mu : Nat) (b : MProd (Array Nat) (Array Nat)) (_ : Fork) (_ : Ctx)
    (b1 : MProd (Array Nat) (Array Nat)) (_ : Fork) (_ : Ctx) : Prop :=
  b1.snd = b.snd.modify (tl.gtTree.getD mu 0) (· + 1)

/-- A count that has changed belongs to the array of one of the matrices. -/
theorem runFold_ties (tl : HTailF2) :
    ∀ (l : List Nat) (b : MProd (Array Nat) (Array Nat)) (F : Fork) (c : Ctx)
      (b' : MProd (Array Nat) (Array Nat)) (F' : Fork) (c' : Ctx),
      RunFoldS (stepT tl) l b F c b' F' c' → ∀ t, b'.snd.getD t 0 ≠ b.snd.getD t 0 →
      ∃ mu ∈ l, tl.gtTree.getD mu 0 = t
  | [], b, _, _, b', _, _, h, t, ht => by
    obtain ⟨rfl, -, -⟩ := h
    exact absurd rfl ht
  | a :: l, b, F, c, b', F', c', h, t, ht => by
    obtain ⟨b1, F1, c1, hs, hr⟩ := h
    by_cases e : tl.gtTree.getD a 0 = t
    · exact ⟨a, List.mem_cons_self, e⟩
    · have h1 : b1.snd.getD t 0 = b.snd.getD t 0 := by
        rw [hs, getD_modify, if_neg (fun q => e q.1)]
      obtain ⟨mu, hmu, e2⟩ := runFold_ties tl l b1 F1 c1 b' F' c' hr t (by rw [h1]; exact ht)
      exact ⟨mu, List.mem_cons_of_mem _ hmu, e2⟩

/-- What the test says: no member occurs twice. -/
theorem allDistinct_nodup : ∀ (l : List Nat), HTailF2.allDistinct l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: t, h => by
    simp only [HTailF2.allDistinct, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.2 ⟨?_, allDistinct_nodup t h.2⟩
    intro hx
    have : t.contains x = true := by simpa using hx
    rw [this] at h
    exact absurd h.1 (by simp)

/-- If objectsF returns: every array of the kind «symbols» is the array of a matrix of the list, and
no two matrices have one array. -/
theorem objectsF_syms (tl tl' : HTailF2) (funs : Array HFun) (F G : Fork) (c c' : Ctx)
    (h : tl.objectsF funs F c = .ok ((tl', G), c')) :
    (∀ t, t < G.trees.size → (G.trees.getD t {}).kind = HKind.symbols →
      ∃ mu, mu < tl'.NM ∧ tl'.gtTree.getD mu 0 = t) ∧ tl'.gtTree.toList.Nodup := by
  unfold HTailF2.objectsF at h
  simp only [bind_ok, get_ok, ask_ok, lift_ok, mustAs_ok, Option.some.injEq, SubM.claims] at h
  obtain ⟨_, _, _, ⟨⟨_, rfl⟩, rfl⟩, _, _, _, ⟨⟨hfh, rfl⟩, rfl⟩, _, _, _, ⟨_, rfl, rfl⟩,
    _, _, _, ⟨ht, rfl⟩, h⟩ := h
  have := testAs_ctx _ _ _ _ _ ht
  subst this
  obtain ⟨g, _, _, ⟨hg, rfl, rfl⟩, _, _, _, ⟨_, rfl, rfl⟩, _, Fa, ca, hFo, _, _, _, ⟨_, rfl, rfl⟩,
    _, _, _, ⟨⟨_, rfl⟩, rfl⟩, _, _, _, ⟨_, rfl, rfl⟩, tla, Fb, cb, hJ, tlb, Fc, cc, hB,
    _, _, _, ⟨_, rfl, rfl⟩, _, _, _, ⟨⟨_, rfl⟩, rfl⟩, tl1, F1, c1, hWt, h⟩ := h
  obtain ⟨n0, F1', c1', ⟨hn0, hF1, hc1⟩, bT, F2, c2, hT, bR, F3, c3, hR, h⟩ := h
  obtain ⟨_, _, _, ⟨⟨_, rfl⟩, rfl⟩, _, _, _, ⟨⟨_, rfl⟩, rfl⟩, _, _, _, ⟨_, rfl, rfl⟩,
    _, _, _, ⟨_, rfl, rfl⟩, kinds, _, _, ⟨hkinds, rfl, rfl⟩, _, _, _, ⟨⟨hex1, rfl⟩, rfl⟩,
    _, _, _, ⟨⟨_, rfl⟩, rfl⟩, _, _, _, ⟨⟨hex3, rfl⟩, rfl⟩, _, _, _, ⟨_, rfl, rfl⟩, h⟩ := h
  obtain ⟨rfl, rfl, rfl⟩ := (pure_ok _ _ _ _ _ _).1 h
  have rT := forInS_inv _ (stepT tl1)
    (by
      intro mu b F c r F' c' hb
      simp only [bind_ok, pure_ok, ask_ok, Option.some.injEq] at hb
      obtain ⟨_, _, _, ⟨_, rfl, rfl⟩, _, Fx, cx, hl, _, _, _, ⟨_, rfl, rfl⟩, rfl, rfl, rfl⟩ := hb
      exact ⟨_, rfl, rfl⟩) _ _ _ _ _ _ _ hT
  simp only [Bool.and_eq_true] at hex3
  refine ⟨fun t ht hk => ?_, allDistinct_nodup _ hex3.2⟩
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hex1
  have hsz : kinds.size = G.trees.size := by
    rw [← hkinds]
    simp
  have hkt : kinds.getD t HKind.table = HKind.symbols := by
    rw [← hkinds, ← hk]
    simp [Array.getD, ht]
  have h1 := hex1 t (by rw [hsz]; exact ht)
  rw [hkt] at h1
  have h1' : bT.snd.getD t 0 = 1 := by simpa using h1
  obtain ⟨mu, hmu, e⟩ := runFold_ties tl1 _ _ _ _ _ _ _ rT t (by
    rw [h1']
    by_cases hq : t < n0
    · simp [Array.getD, hq]
    · simp [Array.getD, hq])
  exact ⟨mu, List.mem_range.1 hmu, e⟩

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.objectsF_syms
