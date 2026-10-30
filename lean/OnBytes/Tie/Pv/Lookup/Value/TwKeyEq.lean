-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Value/TwKeyEq.lean.
The keys' claim of an assembled lookup, as a row, is the flat function's key row, spread.

States: `key_eq`: keyRow (OnBytes/Tie/Pv/Lookup/Value/TwForms.lean) of the library's masked claim on
the keys is TwV.rowKey at the trace of the state, spread (toRow, Cb/Pv/Lookup/Alg/TwGen.lean: a list
of places with coefficients as a function on all places): general in A, for every reading kAt, every
caller's state st and every last state o. No premise.
  `eqN_list`: the library's weight at the point read backwards is TwV.eqN over the list of the
    point's coordinates (low bit first), at every key number below 2^k.
  `ofFn_snoc`, `pnt_list`, `key_pnt`: a level's point as a list: the sumcheck's challenges put back
    by variable, then the line's draw.
Does not say: what ties the reading kAt of the keys to A.key; anything on a transcript.

-/
import Cb.Pv.Lookup.Out.TwRows
import OnBytes.Tie.Pv.Lookup.Value.TwTeeth

set_option autoImplicit false

namespace Tw3
open TwV Cb Cb.Tw Cb.LdLkp

section
variable {E : Type} [Field E]

theorem eqN_list (k k' : ℕ) (h : k' = k) (z : Fin k' → E) (X : ℕ) (hX : X < 2 ^ k) :
    Blocks.eqN k 0 (Blocks.nat fun i : Fin k' => z i.rev) X = TwV.eqN (List.ofFn z) X := by
  subst h
  obtain ⟨b, rfl⟩ := numLE_surj (k := k') (c := X) hX
  rw [blocks_eqN_rev, eqN_ofFn]

theorem ofFn_snoc {α : Type} {k : ℕ} (f : Fin k → α) (a : α) : List.ofFn (Fin.snoc f a : Fin (k + 1)
    → α) = List.ofFn f ++ [a] := by
  rw [List.ofFn_succ', List.concat_eq_append]
  simp

variable [Fintype E]

theorem pnt_list (D : TreeP E) (l : ℕ) (s : (D.lv (l + 1)).T.St) :
    List.ofFn ((D.lv (l + 1)).pnt s) =
      byVar (List.ofFn fun j : Fin (D.g + l) => ((D.sg l j : Fin (D.g + l)) : ℕ)) (ppList (D.lv
          l).T.par.fmt s.1.pt) ++ [s.2] := by
  rw [byVar_perm]
  have e : (D.lv (l + 1)).pnt s = (Fin.snoc ((D.lv l).gam s.1) s.2 : Fin (D.g + l + 1) → E) := rfl
  rw [e, ofFn_snoc]
  congr 2
  funext v
  exact lv_gamL D l s.1 v

variable (A : LkAsmH E) (kAt : ℕ → A.J ⊕ E) (st : A.St) (o : A.XB)

/-- the keys' top point as the list TwV.pntTop -/
theorem key_pnt :
    List.ofFn (((A.IK.setV (A.v' + 1)).DK.lv (A.v' + 1)).pnt (A.oldT o).2) =
      pntTop (numsOf A st kAt).oK [] (traceOf A o).keys.reverse := by
  rw [show (traceOf A o).keys.reverse = lvN (A.IK.setV (A.v' + 1)).DK (A.v' + 1) (A.oldT o).2 from
      List.reverse_reverse _]
  rw [pnt_list]
  show _ = byVar ((numsOf A st kAt).oK (lvN (A.IK.setV (A.v' + 1)).DK A.v' (A.oldT
      o).2.1.st).length) _ ++ _
  rw [lvN_length]
  rfl

theorem key_eq :
    Cb.Tw.keyRow (A.v' + 1) kAt (A.clK (A.oldT o)) = toRow (TwV.rowKey (numsOf A st kAt) (traceOf A
        o)) := by
  have hw : ∀ X < 2 ^ (A.v' + 1),
      Blocks.eqN (A.v' + 1) 0 (A.clK (A.oldT o)).pt X = TwV.eqN (pntTop (numsOf A st kAt).oK []
          (traceOf A o).keys.reverse) X := by
    intro X hX
    rw [← key_pnt A kAt st o]
    exact eqN_list (A.v' + 1) (0 + (A.v' + 1)) (Nat.zero_add _) _ X hX
  have hm : ∀ j, (A.clK (A.oldT o)).mf j =
      dense (scale (-1) (incTop (numsOf A st kAt).ledK (TwV.fK (numsOf A st kAt) (traceOf A o))
          (traceOf A o).keys.reverse)) j := by
    intro j
    rw [dense_scale, show (traceOf A o).keys.reverse = lvN (A.IK.setV (A.v' + 1)).DK (A.v' + 1)
        (A.oldT o).2 from List.reverse_reverse _]
    have := @lv_inc E _ _ (A.IK.setV (A.v' + 1)).DK A.decJ _ (A.v' + 1) (A.oldT o).2 (fK_dense A kAt
        st o) j
    rw [neg_one_mul]
    exact congrArg Neg.neg this
  unfold Cb.Tw.keyRow toRow TwV.rowKey
  refine congrArg₂ Row.mk (funext fun j => ?_) ?_
  · simp only
    rw [dense_append, dense_flatMap_range, hm j]
    congr 1
    refine Finset.sum_congr rfl fun X hX => ?_
    rw [hw X (Finset.mem_range.mp hX)]
    have hk : (numsOf A st kAt).kAt X = (kAt X).getLeft? := rfl
    rw [hk]
    cases kAt X with
    | inl p =>
      show _ * (if p = j then 1 else 0) = dense [(p, _)] j
      rw [dense_one]
      split_ifs <;> simp
    | inr a =>
      show _ * 0 = dense [] j
      rw [mul_zero, dense_nil]
  · simp only
    rw [sum_map_range]
    have ht : (A.clK (A.oldT o)).tg = (traceOf A o).lam - (traceOf A o).kT := by
      show (A.b2 (A.oR (((A.IK.setV (A.v' + 1)).DK.lv (A.v' + 1)).base (A.oldT o).2))).2 - (A.oldT
          o).1 = _
      rw [ldLkpSegK_base E (A.IK.setV (A.v' + 1)).DK (A.v' + 1) (A.oldT o).2]
      rfl
    refine congrArg₂ (· - ·) ht (Finset.sum_congr rfl fun X hX => ?_)
    rw [hw X (Finset.mem_range.mp hX)]
    have hk : (numsOf A st kAt).kAt X = (kAt X).getLeft? := rfl
    have hc : (numsOf A st kAt).kC X = Sum.elim (fun _ => 0) id (kAt X) := rfl
    rw [hk, hc]
    cases kAt X with
    | inl p => exact mul_zero _
    | inr a => rfl

end
end Tw3
#print axioms Tw3.eqN_list
#print axioms Tw3.ofFn_snoc
#print axioms Tw3.pnt_list
#print axioms Tw3.key_pnt
#print axioms Tw3.key_eq
