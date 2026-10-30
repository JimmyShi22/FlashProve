-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/LedgerAt.lean: THE LEDGER BEHIND THE HEAD's ONE SUMCHECK (bridge B2 of Lemma 2b, at
the call). Three runs of layings: the claimed sum (the factor 1), the end values (the factor beta),
the hiding polynomial's coefficients (0 shown, the factor -1). `hidden_vals`: under a ledger that had
a place for each of its numbers, the hidden scalars behind them: the claimed sum: what was sent less
its mask entry; a coefficient: its mask entry itself; an end value: what the ledger shows less beta
times its mask entry.
-/
import Mathlib
import Johnson.Desc.Kinds.Law.Tables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE oneE subE)
open OnBytes.Model (Aff Fork Reading World)
open Part.MaskedSum (Var hidingAt ownSlots rowLaid)

theorem hide_unfold {ld : List E} {F0 Fa : Fork} {c : Array Hid}
    (h : hide ld F0 [] = some (c, Fa, [])) :
    ({ F0 with next := F0.next + ld.length } : Fork).hideRun F0.next ld.toArray oneE = some Fa ∧
      c = ld.toArray.mapIdx fun j x => { var := Aff.slot (F0.next + j), shown := x } := by
  unfold hide at h
  cases hr : ({ F0 with next := F0.next + ld.length } : Fork).hideRun F0.next ld.toArray oneE with
  | none => rw [hr] at h; simp at h
  | some X =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨by rw [h.2.1], h.1.symm⟩

theorem rd_neg_one : rd (subE zeroE oneE) = -1 := by
  have h := Reading.gl.sub zeroE oneE
  rw [Reading.gl.zero, Reading.gl.one] at h
  show Reading.gl.val _ = _
  rw [h]; ring

/-- **The hidden scalars behind three runs of layings on ranges that follow each other.** a: the
first number; one lead scalar c0; own numbers of the sumcheck's own; then the end values. -/
theorem hidden_vals {F0 Fa G F1 : Fork} {c0 beta : E} {own : Nat} {vals : Array E} {n1 n2 : Nat}
    (mask : Nat → E) (hW : WellLaid F0)
    (r1 : ({ F0 with next := n1 } : Fork).hideRun F0.next #[c0] oneE = some Fa)
    (r2 : ({ Fa with next := n2 } : Fork).hideRun (F0.next + 1 + own) vals beta = some G)
    (r3 : G.hideRun (F0.next + 1) (Array.replicate own zeroE) (subE zeroE oneE) = some F1) :
    rd (hidden F1 mask F0.next) = rd c0 - rd (mask F0.next) ∧
    (∀ i, i < own → rd (hidden F1 mask (F0.next + 1 + i)) = rd (mask (F0.next + 1 + i))) ∧
    (∀ j, j < vals.size → rd (hidden F1 mask (F0.next + 1 + own + j))
      = rd (F1.vp.getD (F0.next + 1 + own + j) zeroE)
        - rd beta * rd (mask (F0.next + 1 + own + j))) ∧
    Fa.vp.getD F0.next zeroE = c0 := by
  obtain ⟨w1, _, _, v1, m1⟩ := hideRun_frame (F := { F0 with next := n1 }) hW r1
  obtain ⟨w2, _, _, v2, m2⟩ := hideRun_frame (F := { Fa with next := n2 }) w1 r2
  obtain ⟨_, _, _, v3, m3⟩ := hideRun_frame w2 r3
  have s1 : (#[c0] : Array E).size = 1 := rfl
  have s3 : (Array.replicate own zeroE).size = own := Array.size_replicate
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold hidden
    rw [v3, m3, if_neg (by omega), if_neg (by omega), v2, m2, if_neg (by omega),
      if_neg (by omega), v1, m1, if_pos (by rw [s1]; omega), if_pos (by rw [s1]; omega), rd_sub,
      rd_mul]
    simp only [Nat.sub_self]
    show rd c0 - Reading.gl.val oneE * _ = _
    rw [Reading.gl.one, one_mul]
  · intro i hi
    unfold hidden
    rw [v3, m3, if_pos (by rw [s3]; omega), if_pos (by rw [s3]; omega), rd_sub, rd_mul, rd_neg_one]
    have : (Array.replicate own zeroE).toList.getD (F0.next + 1 + i - (F0.next + 1)) (0 : E)
        = zeroE := by
      have hi' : F0.next + 1 + i - (F0.next + 1) = i := by omega
      rw [hi', Array.toList_replicate, List.getD_eq_getElem?_getD, List.getElem?_replicate,
        if_pos hi]
      rfl
    rw [this]
    show Reading.gl.val zeroE - _ = _
    rw [Reading.gl.zero]
    ring
  · intro j hj
    unfold hidden
    rw [m3, if_neg (by rw [s3]; omega), m2, if_pos (by omega), rd_sub, rd_mul]
    have : F1.vp.getD (F0.next + 1 + own + j) (0 : E) = F1.vp.getD (F0.next + 1 + own + j) zeroE := by
      rw [v3, v3, if_neg (by rw [s3]; omega), if_neg (by rw [s3]; omega), v2, v2,
        if_pos (by omega), if_pos (by omega)]
      have hlt : F0.next + 1 + own + j - (F0.next + 1 + own) < vals.toList.length := by
        rw [Array.length_toList]; omega
      rw [List.getD_eq_getElem _ _ hlt, List.getD_eq_getElem _ _ hlt]
    rw [this]
  · rw [v1, if_pos (by rw [s1]; omega)]
    simp

end VerifiableInference.Desc.Kinds.Head.Law
