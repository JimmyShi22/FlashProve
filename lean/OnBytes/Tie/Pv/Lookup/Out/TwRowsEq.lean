-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Out/TwRowsEq.lean.
The rows read out of an assembled lookup's last state are the flat function's at the trace of that
state.

States: `rows_eq`: outA A kAt (A.rd o), that is the rows of the read-out A.rd o and then the keys'
claim as a row, is the flat, computable function TwV.rowsOfTrace at the trace of o, each sparse row
spread (toRow): as lists, row by row, coefficient by coefficient and target by target. For every A :
LkAsmH E, every kAt, every o : A.XB, reached by a run or not. No premise.
  `rows_len`: the list has (n + 1) + (v' + 1) + d + 5 rows: the equation is not between empty lists.
    It tests nothing at a transcript.
  `xb_nonempty`: there is a state o as soon as there is a caller's state: the quantifier does not
    range over nothing.
  `o65_rows_eq`, `o65_rows_len`, `o65_xb_nonempty`: the same at the small lookup o65A
    (seventeen rows).
Does not say: this is the half on states of the equation between the verifier's value and the flat
function. It names no reduction, no out, no transcript and no plain data: the two arguments of
rowsOfTrace here, numsOf and traceOf, are noncomputable and read the library's state. "Equal" is
said of the spread rows, not of the sparse lists. Of the orders it pins oE, oB and oK at the last
key level alone; oK at the levels below and oT are not reached from the statement. A.key is read by
nothing in it.

-/
import Cb.Pv.Lookup.Out.TwRows16
import OnBytes.Tie.Pv.Lookup.Value.TwKeyEq

set_option autoImplicit false

namespace Tw3
open TwV Cb Cb.Tw Cb.LdLkp

variable {E : Type} [Field E] [Fintype E] (A : LkAsmH E) (kAt : ℕ → A.J ⊕ E) (o : A.XB)

/-- The rows of the read-out, then the keys' row, are the flat function's rows, spread. -/
theorem rows_eq : outA A kAt (A.rd o) = (rowsOfTrace (numsOf A (A.rd o).1 kAt) (traceOf A o)).map
    toRow := by
  have h : rowsOfTrace (numsOf A (A.rd o).1 kAt) (traceOf A o) =
      (rowsOfTrace (numsOf A (A.rd o).1 kAt) (traceOf A o)).dropLast ++ [rowKey (numsOf A (A.rd o).1
          kAt) (traceOf A o)] := by
    unfold rowsOfTrace
    rw [List.dropLast_concat]
  rw [h, List.map_append, ← rows16_eq A kAt o]
  show (A.rd o).2.2 ++ [keyRow (A.v' + 1) kAt (A.clK (A.oldT o))] = _
  rw [key_eq A kAt (A.rd o).1 o]
  rfl

/-- how many rows -/
theorem rows_len : (outA A kAt (A.rd o)).length = (A.n + 1) + (A.v' + 1) + A.d + 5 := by
  have hT : ∀ (N : Nums A.J E) (lam : E) (l : List (Sc E)), (tieRowsR N lam l).length = l.length :=
      by
    intro N lam l
    induction l with
    | nil => rfl
    | cons s r ih => exact congrArg (· + 1) ih
  have hL : ∀ (led : ℕ → Led A.J) (g : ℕ) (inc0 : List (A.J × E)) (l : List (Sc E × E)), (lvRowsR
      led g inc0 l).length = l.length := by
    intro led g inc0 l
    induction l with
    | nil => rfl
    | cons s r ih => exact congrArg (· + 1) ih
  rw [rows_eq, List.length_map]
  unfold rowsOfTrace
  simp only [List.length_append, List.length_cons, List.length_nil, hT, hL, List.length_reverse]
  show (tieN A.H.tie (A.n + 1) _).reverse.length + ((lvN (A.IK.setV (A.v' + 1)).DK (A.v' + 1)
      _).reverse.length +
    ((lvN A.D A.d _).reverse.length + (0 + 1 + 1 + 1) + (0 + 1))) + (0 + 1) = _
  rw [List.length_reverse, List.length_reverse, List.length_reverse, tieN_length, lvN_length,
      lvN_length]
  omega

/-! ### The quantifier «every o : A.XB» does not range over nothing -/

omit [Fintype E] in
theorem ppt_nonempty : ∀ l : List (PFmt E), Nonempty (PPt l)
  | [] => ⟨()⟩
  | _ :: l => (ppt_nonempty l).elim fun γ => ⟨((0 : E), γ)⟩

omit [Fintype E] in
theorem out_nonempty (Y : PscPar E) (h : Nonempty Y.St) : Nonempty Y.Out :=
  h.elim fun st => (ppt_nonempty Y.fmt).elim fun γ => ⟨⟨st, 0, γ, 0, fun _ => 0⟩⟩

theorem tie_nonempty (D : TieF E) (h : Nonempty D.St0) : ∀ l, Nonempty (D.lv l).T.St
  | 0 => h
  | l + 1 => out_nonempty (D.lv l).T.par (tie_nonempty D h l)

theorem lv_nonempty (D : TreeP E) (h : Nonempty D.St0) : ∀ l, Nonempty (D.lv l).T.St
  | 0 => h.elim fun x => ⟨(x, fun _ => 0)⟩
  | l + 1 => (out_nonempty (D.lv l).T.par (lv_nonempty D h l)).elim fun o => ⟨(o, 0)⟩

theorem xb_nonempty (h : Nonempty A.St) : Nonempty A.XB := by
  have h2 : Nonempty A.X2 := (tie_nonempty A.H.tie (h.elim fun s => ⟨(s, (0 : E))⟩) (A.n + 1)).elim
      fun s => ⟨((0 : E), s)⟩
  have hR : Nonempty A.XR := h2.elim fun x => ⟨((0 : E), (x, fun _ => 0))⟩
  have h4 : Nonempty A.X4 := (lv_nonempty (A.IK.setV (A.v' + 1)).DK hR (A.v' + 1)).elim fun s =>
      ⟨((0 : E), s)⟩
  have hE : Nonempty A.XE := (lv_nonempty A.D h4 A.d).elim fun s => (ppt_nonempty A.En.par.fmt).elim
      fun γ => ⟨⟨s, 0, γ, 0⟩⟩
  exact out_nonempty A.Bt.zc.next.par (hE.elim fun z => ⟨(z, ((), fun _ => 0))⟩)

/-! ### At the small lookup -/

/-- rows_eq at the small lookup o65A, with its out-statement o65Out -/
theorem o65_rows_eq (o : o65A.XB) :
    o65Out (o65A.rd o) = (rowsOfTrace (numsOf o65A () (Cb.Tw.kAt Cb.Gl.E TwNums.o65S)) (traceOf o65A
        o)).map toRow :=
  rows_eq o65A _ o

theorem o65_rows_len (o : o65A.XB) : (o65Out (o65A.rd o)).length = 17 :=
  rows_len o65A (Cb.Tw.kAt Cb.Gl.E TwNums.o65S) o

theorem o65_xb_nonempty : Nonempty o65A.XB := xb_nonempty o65A ⟨()⟩

end Tw3
#print axioms Tw3.rows_eq
#print axioms Tw3.rows_len
#print axioms Tw3.ppt_nonempty
#print axioms Tw3.out_nonempty
#print axioms Tw3.tie_nonempty
#print axioms Tw3.lv_nonempty
#print axioms Tw3.xb_nonempty
#print axioms Tw3.o65_rows_eq
#print axioms Tw3.o65_rows_len
#print axioms Tw3.o65_xb_nonempty
