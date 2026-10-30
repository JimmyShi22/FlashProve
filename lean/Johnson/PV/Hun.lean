-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
NO SOUNDNESS.

Johnson/PV/Hun.lean: linkPutC_eq's ONE PREMISE, PAID: the written way back unA v s
  (Johnson/PV/LinkPut.lean, w4's) IS the way back by choice along pairA codeA, followed by trAns.
So linkPutC … (unA v s) … IS (linkAt … codeA trAns …).pL.put, with no premise left (linkPutC_is).


-/
import Johnson.PV.LinkPut
import OnBytes.Flat.LinkSibFit

set_option autoImplicit false

namespace W4M
open OnBytes OnBytes.Slice OnBytes.Flat TypedOracleCompiler.Slice TypedOracleCompiler.Run.LinkFirstAns
open TypedOracleCompiler.Run.FirstAnswers (T3)
open _root_.Iop (Dig)

/-! ## 64 bits, summed, give the word back -/

theorem sumBits (n : ℕ) : ∀ k : ℕ,
    (List.range k).foldl (fun acc j => if n.testBit j then acc + 2 ^ j else acc) 0 = n % 2 ^ k
  | 0 => by simp [Nat.mod_one]
  | k + 1 => by
    rw [List.range_succ, List.foldl_append, sumBits n k]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ k) with h | h <;> simp [h]

theorem wordAt_of (d : Dig 256) (off : ℕ) (w : UInt64) (hoff : off + 64 ≤ 256)
    (hb : ∀ j (hj : j < 64), d ⟨off + j, by omega⟩ = w.toNat.testBit j) : wordAt d off = w := by
  unfold wordAt
  have e : (List.range 64).foldl (fun acc j =>
      if h : off + j < 256 then (if d ⟨off + j, h⟩ then acc + 2 ^ j else acc) else acc) 0 =
      (List.range 64).foldl (fun acc j => if w.toNat.testBit j then acc + 2 ^ j else acc) 0 := by
    apply List.foldl_ext
    intro acc j hj
    have hj' : j < 64 := List.mem_range.1 hj
    rw [dif_pos (by omega), hb j hj']
  rw [e, sumBits, Nat.mod_eq_of_lt w.toNat_lt]
  exact UInt64.ofNat_toNat

theorem wordAt_c0 (e : E) : wordAt (digW e) 0 = e.c0 :=
  wordAt_of _ 0 _ (by omega) fun j hj => by simp [digW, hj]
theorem wordAt_c1 (e : E) : wordAt (digW e) 64 = e.c1 :=
  wordAt_of _ 64 _ (by omega) fun j hj => by
    simp [digW, show ¬ 64 + j < 64 by omega, show 64 + j < 128 by omega]
theorem wordAt_c2 (e : E) : wordAt (digW e) 128 = e.c2 :=
  wordAt_of _ 128 _ (by omega) fun j hj => by
    simp [digW, show ¬ 128 + j < 64 by omega, show ¬ 128 + j < 128 by omega,
      show 128 + j < 192 by omega]

/-! ## One digest -/

theorem un1_digE (x : GE) : un1 (digE x) = some (ofE x) := by
  have hx : toE (wordAt (digE x) 0, wordAt (digE x) 64, wordAt (digE x) 128) = x := by
    unfold digE
    rw [wordAt_c0, wordAt_c1, wordAt_c2]
    exact toE_ofE x
  simp only [un1]
  rw [hx, if_pos (List.all_eq_true.2 fun i _ => beq_self_eq_true _)]

theorem un1_some (d : Dig 256) (t : T3) (h : un1 d = some t) : ∃ x : GE, d = digE x ∧ t = ofE x :=
    by
  simp only [un1] at h
  split at h
  · rename_i hall
    refine ⟨_, funext fun i => ?_, (Option.some.inj h).symm⟩
    exact (beq_iff_eq.1 (List.all_eq_true.1 hall i (List.mem_finRange i))).symm
  · cases h

/-! ## A list of digests -/

theorem mapM_un1_map : ∀ xs : List GE, (xs.map digE).mapM un1 = some (xs.map ofE)
  | [] => rfl
  | x :: xs => by
    rw [List.map_cons, List.mapM_cons, un1_digE, mapM_un1_map xs]
    rfl

theorem mapM_un1 : ∀ (l : List (Dig 256)) (ts : List T3), l.mapM un1 = some ts →
    ∃ xs : List GE, l = xs.map digE ∧ ts = xs.map ofE
  | [], ts, h => ⟨[], rfl, (Option.some.inj h).symm⟩
  | d :: l, ts, h => by
    rw [List.mapM_cons] at h
    cases hd : un1 d with
    | none => rw [hd] at h; cases h
    | some t =>
      cases hl : l.mapM un1 with
      | none => rw [hd, hl] at h; cases h
      | some ts' =>
        rw [hd, hl] at h
        obtain ⟨x, rfl, rfl⟩ := un1_some d t hd
        obtain ⟨xs, rfl, rfl⟩ := mapM_un1 l ts' hl
        exact ⟨x :: xs, rfl, (Option.some.inj h).symm⟩

/-! ## Two tables' answers -/

section
variable {v s : ℕ}

/-- the answers in the order of the two lists -/
def xsOf (a : (Fin v → Bool) × Fin s → GE) : List GE :=
  List.ofFn fun n : Fin (2 ^ v * s) =>
    a (vtx v (n.val / s), ⟨n.val % s, Nat.mod_lt _ (pos_of_place n)⟩)

theorem codeA_xs (a : (Fin v → Bool) × Fin s → GE) : codeA a = (xsOf a).map digE := by
  unfold codeA xsOf
  rw [List.map_ofFn]
  rfl
theorem trAns_xs (a : (Fin v → Bool) × Fin s → GE) : trAns a = (xsOf a).map ofE := by
  unfold trAns xsOf
  rw [List.map_ofFn]
  rfl
theorem xsOf_length (a : (Fin v → Bool) × Fin s → GE) : (xsOf a).length = 2 ^ v * s := by
  unfold xsOf
  rw [List.length_ofFn]

theorem unA_pair (a a' : (Fin v → Bool) × Fin s → GE) :
    unA v s (pairA codeA (a, a')) = some (trAns a, trAns a') := by
  unfold unA pairA
  rw [if_pos (by rw [List.length_append, codeA_length, codeA_length]), codeA_xs, codeA_xs,
    ← List.map_append, mapM_un1_map, List.map_append, ← trAns_xs, ← trAns_xs]
  have hl : (trAns a).length = 2 ^ v * s := by rw [trAns_xs, List.length_map, xsOf_length]
  show some ((trAns a ++ trAns a').take (2 ^ v * s), (trAns a ++ trAns a').drop (2 ^ v * s)) = _
  rw [List.take_left' hl, List.drop_left' hl]

theorem codeA_anT (xs : List GE) (h : xs.length = 2 ^ v * s) :
    codeA (anT v s (xs.map ofE)) = xs.map digE := by
  have e : xs.map ofE = (xs.map writeE).map E.triple := by
    rw [List.map_map]
    rfl
  have t : trAns (anT v s (xs.map ofE)) = xs.map ofE := by
    rw [e]
    exact trAns_anT v s _ (by rw [List.length_map, h]) fun a ha => by
      obtain ⟨x, _, rfl⟩ := List.mem_map.1 ha
      exact okE_writeE x
  have c : ∀ a : (Fin v → Bool) × Fin s → GE,
      codeA a = (trAns a).map fun t => digW (E.ofTriple t) := fun a => by
    rw [codeA_xs, trAns_xs, List.map_map]
    rfl
  rw [c, t, List.map_map]
  rfl

theorem unA_some (l : List (Dig 256)) (p : List T3 × List T3) (h : unA v s l = some p) :
    ∃ aa : ((Fin v → Bool) × Fin s → GE) × ((Fin v → Bool) × Fin s → GE), pairA codeA aa = l := by
  unfold unA at h
  split at h
  · rename_i hlen
    cases hm : l.mapM un1 with
    | none => rw [hm] at h; cases h
    | some ts =>
      obtain ⟨xs, rfl, rfl⟩ := mapM_un1 l ts hm
      rw [List.length_map] at hlen
      refine ⟨(anT v s ((xs.take (2 ^ v * s)).map ofE), anT v s ((xs.drop (2 ^ v * s)).map ofE)),
          ?_⟩
      unfold pairA
      rw [codeA_anT _ (by rw [List.length_take, hlen]; omega),
        codeA_anT _ (by rw [List.length_drop, hlen]; omega), ← List.map_append,
        List.take_append_drop]
  · cases h

/-- **THE PREMISE, PAID.** -/
theorem hun (l : List (Dig 256)) :
    unA v s l = (backOf (pairA (codeA (v := v) (s := s))) l).map fun aa => (trAns aa.1, trAns aa.2)
        := by
  by_cases h : ∃ aa, pairA (codeA (v := v) (s := s)) aa = l
  · obtain ⟨⟨a, a'⟩, rfl⟩ := h
    rw [backOf_apply _ (pairA_inj codeA codeA_inj fun x y => by rw [codeA_length, codeA_length])]
    exact unA_pair a a'
  · have hb : backOf (pairA (codeA (v := v) (s := s))) l = none := by
      unfold backOf
      rw [dif_neg h]
    rw [hb]
    cases hu : unA v s l with
    | none => rfl
    | some p => exact (h (unA_some l p hu)).elim

end

end W4M

#print axioms W4M.hun
