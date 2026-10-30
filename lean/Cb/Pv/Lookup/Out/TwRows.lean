-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Out/TwRows.lean.
The rows of an assembled lookup, kind by kind, are the rows of the flat function, spread.

Proofs. For every A : LkAsmH E (Cb/Pv/Lookup/Asm/AsmH.lean) and every last state o : A.XB of its
chain, each kind of row in the list that the read-out A.rd hands on is the sparse row that
Cb/Pv/Lookup/Out/TwV.lean computes from what o holds as plain data (tieN, lvN, traceOf:
Cb/Pv/Lookup/Out/TwTraceOf.lean) at the numbers numsOf A st kAt, spread by toRow
(Cb/Pv/Lookup/Alg/TwGen.lean). Cb/Pv/Lookup/Out/TwRows16.lean puts the kinds together.

Main names:
  `ledD D l`: the places of a tree's masks at level l.
  `lv_incS`, `lv_inc`, `lv_row`, `lv_rows`: a product tree (the keys' and the table's alike): the
    form that comes into a level; a level's row; the rows of all levels below l.
  `lv_gamL`: a level's end point, coordinate by coordinate, in the list of its challenges.
  `tie_row0`, `tie_rowS`, `tie_row`, `tie_rows`: the tie's rows.
  `tie_be`, `tie_bT`, `tie_bK`, `fK_dense`, `formT_dense`, `incT0_dense`: the forms of the claims
    that the tie leaves, and their combination at the drawn point.
  `rows4_eq`, `rowsT_eq`: the keys' side's rows; the table's levels' rows.
  `num_eq`, `bitU_eq`, `bitE_eq`: the row that sums the counts; the two rows of the sumcheck on the
    bits. `bit_gam`: the bits' point, variable by variable.
  `end_gam`, `end_degs`, `end_rowB`, `end_S1`, `end_eq`: the row of the closing sumcheck.
Limits: equations on states alone: nothing is stated on which states a run reaches.
`lv_inc`, `lv_row` and `lv_rows` stand under a premise: the form that comes into level 0 is
dense inc0. `fK_dense` and `incT0_dense` meet it for the two trees.
No row of this file reads kAt: it is an idle letter in every statement here that names it.
Only the tie's first row and the closing's row read the table (A.tab st): these are stated at the
caller's state that the state in hand holds. Where st is a free letter, the row does not read it.
No row reads a target of the claims that the tie leaves, so nothing is stated on these targets.
Not claimed: anything on soundness, completeness or hiding.

-/
import Cb.Pv.Lookup.Out.TwTraceOf

set_option autoImplicit false

namespace Tw3
open TwV Cb Cb.Tw Cb.LdLkp

section
variable {E : Type} [Field E] [Fintype E]

/-! ## A tree (the keys' and the table's alike) -/

section Tree
variable (D : TreeP E) [DecidableEq D.J]

/-- the places of a tree's masks -/
noncomputable def ledD (l : ℕ) : Led D.J := ledOf _ (D.wAt l) fun a => D.cAt l (decide (a ≠ 0))

omit [DecidableEq D.J] in
theorem lvN_length : ∀ (l : ℕ) (s : (D.lv l).T.St), (lvN D l s).length = l
  | 0, _ => rfl
  | l + 1, s => congrArg (· + 1) (lvN_length l s.1.st)

omit [DecidableEq D.J] in
theorem lv_cAt : ∀ (l : ℕ) (b : Bool), (D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two b)) = D.cAt l b
  | 0, _ => rfl
  | _ + 1, _ => rfl

omit [DecidableEq D.J] in
/-- A level's end point at coordinate i is the challenge of the round that binds it. The statement
is that of Cb.Tw.lv_gam (Cb/Pv/Lookup/Order/TwPoint.lean), a file that this one does not import. -/
theorem lv_gamL : ∀ (l : ℕ) (o : (D.lv l).T.par.Out) (i : Fin (D.g + l)),
    (D.lv l).gam o i = (ppList (D.lv l).T.par.fmt o.pt).getD ((D.sg l).symm i : Fin (D.g + l)) 0
  | 0, o, i => hFnOf_list (pfCube E 2) (pDummy E 2) (pDummyD E 2) (D.g + 0) _ o.pt ((D.sg 0).symm i)
  | l + 1, o, i => hFnOf_list (pfCube E 2) (pDummy E 2) (pDummyD E 2) (D.g + l + 1) _ o.pt ((D.sg (l
      + 1)).symm i)

theorem lv_degs (k : ℕ) : (List.replicate k (pfCube E 2) ++ [pDummy E 2]).map PFmt.n =
    List.replicate k 2 ++ [2] := by
  rw [List.map_append, List.map_replicate]
  rfl

/-- the form that comes into level l + 1 is the one that level l's line step hands on -/
theorem lv_incS (l : ℕ) (s : (D.lv (l + 1)).T.St) (j : D.J) :
    (D.lv (l + 1)).T.slS s j =
      dense (lineForm (ledD D l) (scOf (D.lv l).T.par [(D.lv l).two false, (D.lv l).two true] s.1)
          s.2) j := by
  have h := @line_dense E _ D.J _ (D.cAt l false) (D.cAt l true) j
    ((ppList (D.lv l).T.par.fmt s.1.pt).getLastD 0) (1 - s.2) s.2 (Classical.propDecidable _)
        (Classical.propDecidable _)
  have h0 : (D.lv (l + 1)).T.slS s j = (D.lv l).T.lst s.1.st ((D.lv l).T.par.hp s.1.st s.1.pt) *
      ((@ite _ (j = (D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two false))) (Classical.propDecidable _)
          (1 - s.2) 0) +
        @ite _ (j = (D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two true))) (Classical.propDecidable _)
            s.2 0) := rfl
  rw [h0, lv_cAt, lv_cAt, lst_be]
  exact h

/-- the form that comes into level l, pushed onto the tree's names: TwV.incTop -/
theorem lv_inc (inc0 : List (D.J × E)) : ∀ (l : ℕ) (s : (D.lv l).T.St),
    (∀ j, D.inc0 (D.root l s).1 (D.root l s).2 j = dense inc0 j) →
    ∀ j, pushJ (D.lv l).toJ ((D.lv l).T.slS s) j = dense (incTop (ledD D) inc0 (lvN D l s)) j
  | 0, s, h, j => (congrFun (pushJ_id (J := D.J) _) j).trans (h j)
  | l + 1, s, _, j => by
    refine (congrFun (pushJ_id (J := D.J) _) j).trans ?_
    rw [lv_incS]
    show _ = dense (lineForm (ledD D (lvN D l s.1.st).length) _ _) j
    rw [lvN_length]

theorem lv_row (inc0 : List (D.J × E)) : ∀ (l : ℕ) (o : (D.lv l).T.par.Out),
    (∀ j, D.inc0 (D.root l o.st).1 (D.root l o.st).2 j = dense inc0 j) →
    D.rowU l o = toRow (rowU (ledD D l) (List.replicate (D.g + l) 2 ++ [2])
      (scOf (D.lv l).T.par [(D.lv l).two false, (D.lv l).two true] o) (incTop (ledD D) inc0 (lvN D l
          o.st))
      ((scOf (D.lv l).T.par [(D.lv l).two false, (D.lv l).two true] o).v 0 *
        (scOf (D.lv l).T.par [(D.lv l).two false, (D.lv l).two true] o).v 1))
  | 0, o, h => by
    unfold TreeP.rowU
    refine Eq.trans (congrArg₂ Row.mk (pushJ_id (J := D.J) _) rfl) ?_
    exact @rowU_eq E _ (D.lv 0).T.par (inferInstanceAs (DecidableEq D.J)) (D.emB 0)
      (pOne_our _ fun st => pOne_eqs 2 _ _) _ _ _ o _ (lv_degs _) _ h _ rfl
  | l + 1, o, h => by
    unfold TreeP.rowU
    refine Eq.trans (congrArg₂ Row.mk (pushJ_id (J := D.J) _) rfl) ?_
    refine @rowU_eq E _ (D.lv (l + 1)).T.par (inferInstanceAs (DecidableEq D.J)) (D.emB (l + 1))
      (pOne_our _ fun st => pOne_eqs 2 _ _) _ _ _ o _ (lv_degs _) _ (fun j => ?_) _ rfl
    exact (congrFun (pushJ_id (J := D.J) _) j).symm.trans (lv_inc D inc0 (l + 1) o.st h j)

/-- A tree's rows: the rows of the levels below l (TreeP.rowsAt) are TwV.lvRowsR at these levels'
plain data (lvN), spread; under the premise that the form that comes into level 0 is dense inc0. -/
theorem lv_rows (inc0 : List (D.J × E)) : ∀ (l : ℕ) (s : (D.lv l).T.St),
    (∀ j, D.inc0 (D.root l s).1 (D.root l s).2 j = dense inc0 j) →
    D.rowsAt l s = (lvRowsR (ledD D) D.g inc0 (lvN D l s)).map toRow
  | 0, _, _ => rfl
  | l + 1, s, h => by
    show D.rowU l s.1 :: D.rowsAt l s.1.st =
      toRow (rowU (ledD D (lvN D l s.1.st).length) (List.replicate (D.g + (lvN D l s.1.st).length) 2
          ++ [2])
        (scOf (D.lv l).T.par [(D.lv l).two false, (D.lv l).two true] s.1) (incTop (ledD D) inc0 (lvN
            D l s.1.st))
        ((scOf (D.lv l).T.par [(D.lv l).two false, (D.lv l).two true] s.1).v 0 *
          (scOf (D.lv l).T.par [(D.lv l).two false, (D.lv l).two true] s.1).v 1)) ::
      (lvRowsR (ledD D) D.g inc0 (lvN D l s.1.st)).map toRow
    rw [lvN_length, lv_row D inc0 l s.1 h, lv_rows inc0 l s.1.st h]

end Tree

/-! ## The tie -/

theorem tieN_length (D : TieF E) : ∀ (l : ℕ) (s : (D.lv l).T.St), (tieN D l s).length = l
  | 0, _ => rfl
  | l + 1, o => congrArg (· + 1) (tieN_length D l o.st)

variable (A : LkAsmH E) (kAt : ℕ → A.J ⊕ E)

theorem tie_row0 (o : (A.H.tie.lv 0).T.par.Out) :
    rowUof (A.H.tie.lv 0).T (A.H.tie.emB 0) (A.H.tie.lv 0).toJ o =
      toRow (rowU ((numsOf A o.st.1 kAt).ledTie 0) [3] (scOf (A.H.tie.lv 0).T.par (tieSh A.H.tie 0)
          o) []
        (tieS0 (numsOf A o.st.1 kAt) o.st.2 0 (scOf (A.H.tie.lv 0).T.par (tieSh A.H.tie 0) o))) :=
            by
  unfold rowUof
  refine Eq.trans (congrArg₂ Row.mk (pushJ_id (J := A.J) _) rfl) ?_
  exact @rowU_eq E _ (A.H.tie.lv 0).T.par A.decJ (A.H.tie.emB 0) (pOne_our _ fun _ => trivial)
      (tiePl A 0) _ _ o [3] rfl []
    (fun _ => rfl) _ rfl

theorem tiePl_nx (l : ℕ) : tiePl A l (nxAt l) = A.cAt l false := by
  cases l with
  | zero => rfl
  | succ l => simp [tiePl, nxAt]

theorem tie_rowS (st : A.St) (lam : E) (l : ℕ) (o : (A.H.tie.lv (l + 1)).T.par.Out) :
    rowUof (A.H.tie.lv (l + 1)).T (A.H.tie.emB (l + 1)) (A.H.tie.lv (l + 1)).toJ o =
      toRow (rowU ((numsOf A st kAt).ledTie (l + 1)) [3] (scOf (A.H.tie.lv (l + 1)).T.par (tieSh
          A.H.tie (l + 1)) o)
        (tieInc (numsOf A st kAt) (tieN A.H.tie (l + 1) o.st))
        (tieS0 (numsOf A st kAt) lam (l + 1) (scOf (A.H.tie.lv (l + 1)).T.par (tieSh A.H.tie (l +
            1)) o))) := by
  unfold rowUof
  refine Eq.trans (congrArg₂ Row.mk (pushJ_id (J := A.J) _) rfl) ?_
  refine @rowU_eq E _ (A.H.tie.lv (l + 1)).T.par A.decJ (A.H.tie.emB (l + 1)) (pOne_our _ fun _ =>
      trivial)
    (tiePl A (l + 1)) _ _ o [3] rfl _ (fun j => ?_) _ ?_
  · have hj : ∀ j : A.J, (if j = (A.H.tie.lv l).toJ ((A.H.tie.lv l).T.cAt (A.H.tie.lv l).nx) then
        (A.H.tie.lv l).T.lst o.st.st ((A.H.tie.lv l).T.par.hp o.st.st o.st.pt) else 0) =
      dense [(tiePl A (tieN A.H.tie l o.st.st).length (nxAt (tieN A.H.tie l o.st.st).length),
        (ppList (A.H.tie.lv l).T.par.fmt o.st.pt).getLastD 0)] j := fun j => by
      rw [tieN_length, tiePl_nx, dense_one, A.H.tie.c_nx l, lst_be]
      exact if_congr eq_comm rfl rfl
    exact hj j
  · exact (if_neg (Nat.succ_ne_zero l)).symm

theorem tie_row : ∀ (l : ℕ) (o : (A.H.tie.lv l).T.par.Out),
    rowUof (A.H.tie.lv l).T (A.H.tie.emB l) (A.H.tie.lv l).toJ o =
      toRow (rowU ((numsOf A ((A.H.tie.lv l).base o.st).1 kAt).ledTie l) [3] (scOf (A.H.tie.lv
          l).T.par (tieSh A.H.tie l) o)
        (tieInc (numsOf A ((A.H.tie.lv l).base o.st).1 kAt) (tieN A.H.tie l o.st))
        (tieS0 (numsOf A ((A.H.tie.lv l).base o.st).1 kAt) ((A.H.tie.lv l).base o.st).2 l
          (scOf (A.H.tie.lv l).T.par (tieSh A.H.tie l) o)))
  | 0, o => tie_row0 A kAt o
  | l + 1, o => tie_rowS A kAt _ _ l o

/-- The tie's rows: the rows of the steps below l (TieF.rowsAt) are TwV.tieRowsR at these steps'
plain data (tieN), spread. The caller's state and λ are those that the state s holds (base). -/
theorem tie_rows : ∀ (l : ℕ) (s : (A.H.tie.lv l).T.St),
    A.H.tie.rowsAt l s =
      (tieRowsR (numsOf A ((A.H.tie.lv l).base s).1 kAt) ((A.H.tie.lv l).base s).2 (tieN A.H.tie l
          s)).map toRow
  | 0, _ => rfl
  | l + 1, o => by
    show rowUof (A.H.tie.lv l).T (A.H.tie.emB l) (A.H.tie.lv l).toJ o :: A.H.tie.rowsAt l o.st =
      toRow (rowU ((numsOf A ((A.H.tie.lv l).base o.st).1 kAt).ledTie (tieN A.H.tie l o.st).length)
          [3]
          (scOf (A.H.tie.lv l).T.par (tieSh A.H.tie l) o)
          (tieInc (numsOf A ((A.H.tie.lv l).base o.st).1 kAt) (tieN A.H.tie l o.st))
          (tieS0 (numsOf A ((A.H.tie.lv l).base o.st).1 kAt) ((A.H.tie.lv l).base o.st).2 (tieN
              A.H.tie l o.st).length
            (scOf (A.H.tie.lv l).T.par (tieSh A.H.tie l) o))) ::
        (tieRowsR (numsOf A ((A.H.tie.lv l).base o.st).1 kAt) ((A.H.tie.lv l).base o.st).2 (tieN
            A.H.tie l o.st)).map toRow
    rw [tieN_length, tie_row A kAt l o, tie_rows l o.st]
    rfl

/-! ## What the tie leaves -/

theorem tie_rev_succ (D : TieF E) (l : ℕ) (o : (D.lv (l + 1)).T.St) :
    (tieN D (l + 1) o).reverse = (tieN D l o.st).reverse ++ [scOf (D.lv l).T.par (tieSh D l) o] :=
  List.reverse_cons

theorem tie_be (D : TieF E) (l : ℕ) (o : (D.lv (l + 1)).T.St) :
    D.be l o = ((tieN D (l + 1) o).reverse.getD l Sc.zero).be := by
  rw [tie_rev_succ, List.getD_append_right _ _ _ _ (by rw [List.length_reverse, tieN_length]),
    List.length_reverse, tieN_length, Nat.sub_self]
  exact lst_be (D.lv l).T o

theorem tie_get_st (D : TieF E) (l j : ℕ) (hj : j < l) (o : (D.lv (l + 1)).T.St) :
    (tieN D (l + 1) o).reverse.getD j Sc.zero = (tieN D l o.st).reverse.getD j Sc.zero := by
  rw [tie_rev_succ, List.getD_append _ _ _ _ (by rw [List.length_reverse, tieN_length]; exact hj)]

theorem tie_bT (D : TieF E) : ∀ (l : ℕ) (o : (D.lv (l + 1)).T.St) (j : ℕ), j ≤ l →
    (D.bT l o j).1 = ((tieN D (l + 1) o).reverse.getD j Sc.zero).be
  | 0, o, j, hj => by
    obtain rfl : j = 0 := by omega
    exact tie_be D 0 o
  | l + 1, o, j, hj => by
    by_cases h : j = l + 1
    · subst h
      exact (congrArg Prod.fst (if_pos rfl : D.bT (l + 1) o (l + 1) = _)).trans (tie_be D (l + 1) o)
    · rw [tie_get_st D (l + 1) j (by omega) o, ← tie_bT D l o.st j (by omega)]
      exact congrArg Prod.fst (if_neg h : D.bT (l + 1) o j = _)

theorem tie_bK (D : TieF E) : ∀ (l : ℕ) (o : (D.lv (l + 1)).T.St),
    (D.bK l o).1 = ((tieN D (l + 1) o).reverse.getD 0 Sc.zero).be
  | 0, o => tie_be D 0 o
  | l + 1, o => by
    rw [tie_get_st D (l + 1) 0 (by omega) o]
    exact tie_bK D l o.st

theorem tiePl_pt (l : ℕ) : tiePl A l (ptAt l) = A.cAt l true := by
  cases l with
  | zero => rfl
  | succ l => simp [tiePl, ptAt]

variable (st : A.St) (o : A.XB)

/-- the form of the masked claim on the keys' product -/
theorem fK_dense (j : A.J) :
    A.fK (A.oR (A.o4 (A.oldT o))) j = dense (TwV.fK (numsOf A st kAt) (traceOf A o)) j := by
  show (if j = A.cZ then (A.H.tie.bK A.n (A.oR (A.o4 (A.oldT o))).2).1 else 0) =
    dense [(A.cZ, ((tieN A.H.tie (A.n + 1) (A.oR (A.o4 (A.oldT o))).2).reverse.getD 0 Sc.zero).be)]
        j
  rw [dense_one, tie_bK]
  exact if_congr eq_comm rfl rfl

/-- the forms of the claims on the table's products -/
theorem formT_dense (θ : Fin (A.w + 0) → Bool) (j : A.J) :
    A.formT (A.oR (A.o4 (A.oldT o))) θ j = dense (TwV.formT (numsOf A st kAt) (traceOf A o) (numLE
        θ)) j := by
  unfold LkAsmH.formT TwV.formT
  show _ = dense (if numLE θ < A.n + 1 then
      [(tiePl A (numLE θ) (ptAt (numLE θ)),
        ((tieN A.H.tie (A.n + 1) (A.oR (A.o4 (A.oldT o))).2).reverse.getD (numLE θ) Sc.zero).be)]
    else if numLE θ = A.n + 1 then
      [(tiePl A A.n (nxAt A.n), ((tieN A.H.tie (A.n + 1) (A.oR (A.o4 (A.oldT o))).2).reverse.getD
          A.n Sc.zero).be)]
    else []) j
  by_cases h1 : numLE θ < A.n + 1
  · rw [if_pos h1, if_pos h1, dense_one, tiePl_pt, ← tie_bT A.H.tie A.n _ _ (by omega)]
    exact if_congr eq_comm rfl rfl
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : numLE θ = A.n + 1
    · rw [if_pos h2, if_pos h2, dense_one, tiePl_nx, ← tie_be]
      exact if_congr eq_comm rfl rfl
    · rw [if_neg h2, if_neg h2]
      rfl

/-- the form that comes into the table's level 0: the combination at the point -/
theorem incT0_dense (j : A.J) :
    A.D.inc0 (A.D.root A.d (A.outE o).st).1 (A.D.root A.d (A.outE o).st).2 j =
      dense (incT0 (numsOf A st kAt) (traceOf A o)) j := by
  unfold incT0
  rw [dense_flatMap_range]
  show (∑ θ : Fin (A.w + 0) → Bool, Alg.eqk (A.D.root A.d (A.outE o).st).2 θ * A.formT (A.oR (A.o4
      (A.oldT o))) θ j) =
    ∑ th ∈ Finset.range (2 ^ (A.w + 0)),
      dense (scale (eqN (List.ofFn (A.D.root A.d (A.outE o).st).2) th) (TwV.formT (numsOf A st kAt)
          (traceOf A o) th)) j
  rw [← ldLkpNum_sum E (A.w + 0)]
  refine Finset.sum_congr rfl fun θ _ => ?_
  rw [dense_scale, formT_dense A kAt st o]
  exact congrArg (· * _) (eqN_ofFn (A.w + 0) (A.D.root A.d (A.outE o).st).2 θ).symm

/-- The keys' side's rows (here) and the table's levels' rows (`rowsT_eq`), at the trace of o. -/
theorem rows4_eq : A.rows4 (A.oldT o) =
    (lvRowsR (numsOf A st kAt).ledK 0 (TwV.fK (numsOf A st kAt) (traceOf A o)) (traceOf A
        o).keys.reverse).map toRow := by
  rw [show (traceOf A o).keys.reverse = lvN (A.IK.setV (A.v' + 1)).DK (A.v' + 1) (A.oldT o).2 from
      List.reverse_reverse _]
  exact @lv_rows E _ _ (A.IK.setV (A.v' + 1)).DK A.decJ _ (A.v' + 1) (A.oldT o).2 (fK_dense A kAt st
      o)

theorem rowsT_eq : A.D.rowsAt A.d (A.outE o).st =
    (lvRowsR (numsOf A st kAt).ledT A.w (incT0 (numsOf A st kAt) (traceOf A o)) (traceOf A
        o).tabl.reverse).map toRow := by
  rw [show (traceOf A o).tabl.reverse = lvN A.D A.d (A.outE o).st from List.reverse_reverse _]
  exact @lv_rows E _ _ A.D A.decJ _ A.d (A.outE o).st (incT0_dense A kAt st o)

/-! ## The row that sums the counts; the bits' two rows -/

/-- The row that sums the counts (A.numRow) is TwV.rowNum, spread. -/
theorem num_eq : A.numRow = toRow (rowNum (numsOf A st kAt)) := by
  unfold toRow rowNum
  refine congrArg₂ Row.mk (funext fun i => ?_) rfl
  rw [dense_flatMap_range]
  exact Finset.sum_congr rfl fun u _ => (dense_map_range (fun j => (A.bAt u j, (2 : E) ^ j)) (A.n +
      2) i).symm

/-- The first row of the bits' sumcheck (slU, tU) is TwV.rowBitU, spread. -/
theorem bitU_eq : (⟨A.Bt.zc.next.par.slU (fun _ b => b.elim) o, A.Bt.zc.next.par.tU o⟩ : Row E A.J)
    =
    toRow (rowBitU (numsOf A st kAt) (traceOf A o)) := by
  refine @rowU_eq E _ A.Bt.zc.next.par A.decJ (inferInstanceAs (IsEmpty Empty)) (pOne_our _ fun s =>
      pOne_eqs 2 _ _)
    (fun _ => A.cB) [()] _ o _ (lv_degs _) [] (fun _ => rfl) _ ?_
  show (∑ t : Unit, (1 : E) * (o.vals () * (o.vals () - 1))) = o.vals () * (o.vals () - 1)
  rw [Finset.univ_unique, Finset.sum_singleton, one_mul]

/-- the bits' point by variable -/
theorem bit_gam : byVar (numsOf A st kAt).oB (traceOf A o).bits.xs =
    List.ofFn (A.Bt.zc.fn o.st.2.2 (A.Bt.zc.next.ini o.st (A.Bt.zc.next.par.hp o.st o.pt))) := by
  refine (byVar_perm A.oB _).trans (congrArg List.ofFn (funext fun v => ?_))
  exact (hFnOf_list (pfCube E 2) (pDummy E 2) (pDummyD E 2) (A.w + A.d) _ o.pt (A.oB.symm v)).symm

/-- The second row of the bits' sumcheck (slE, the shown value) is TwV.rowBitE, spread. -/
theorem bitE_eq : (⟨A.Bt.zc.next.par.slE A.Bt.rowA () o, o.vals ()⟩ : Row E A.J) =
    toRow (rowBitE (numsOf A st kAt) (traceOf A o)) := by
  unfold toRow rowBitE bitsForm
  refine congrArg₂ Row.mk (funext fun j => ?_) rfl
  rw [dense_append, dense_one, bit_gam]
  have h := cube_dense (fun e => A.bAt (e / 2 ^ A.w) (e % 2 ^ A.w)) (A.w + A.d)
    (A.Bt.zc.fn o.st.2.2 (A.Bt.zc.next.ini o.st (A.Bt.zc.next.par.hp o.st o.pt))) j
  refine Eq.trans ?_ (congrArg₂ (· + ·) h (if_congr eq_comm (lst_be A.Bt.zc.next o) rfl))
  unfold PscPar.slE LkBit.rowA
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun b _ => ?_) ?_
  · congr
  · congr

/-! ## The closing -/

/-- the closing's point by variable -/
theorem end_gam : byVar (numsOf A st kAt).oE (traceOf A o).cls.xs =
    List.ofFn fun v => A.En.fn (A.outE o).st (A.En.par.hp (A.outE o).st (A.outE o).pt) (A.oE.symm v)
        := by
  refine (byVar_perm A.oE _).trans (congrArg List.ofFn (funext fun v => ?_))
  exact (hFnMix_list (A.w + A.d) (dgEnd A.w A.d A.oE) _ (A.outE o).pt (A.oE.symm v)).symm

theorem end_degs : A.En.par.fmt.map PFmt.n = dgE (numsOf A st kAt) := by
  refine (mix_degs E (A.w + A.d) (dgEnd A.w A.d A.oE)).trans ?_
  unfold dgE
  show _ = (List.ofFn fun j : Fin (A.w + A.d) => ((A.oE j : Fin (A.w + A.d)) : ℕ)).map _
  rw [List.map_ofFn]
  rfl

/-- the closing's one map, which stays as a term of the end claim (LkEndM.rowB), as a sparse form -/
theorem end_rowB (j : A.J) :
    A.En.rowB (A.outE o).st () (A.En.par.hp (A.outE o).st (A.outE o).pt) j =
      dense (bitsForm (numsOf A st kAt) (byVar (numsOf A st kAt).oE (traceOf A o).cls.xs)) j := by
  rw [end_gam]
  refine Eq.trans ?_ (cube_dense (fun e => A.bAt (e / 2 ^ A.w) (e % 2 ^ A.w)) (A.w + A.d) _ j)
  unfold LkEndM.rowB
  refine Fintype.sum_equiv (A.oE.arrowCongr (Equiv.refl Bool)) _ _ fun b => ?_
  have h := Alg.eqk_equiv A.oE.symm (A.En.fn (A.outE o).st (A.En.par.hp (A.outE o).st (A.outE
      o).pt)) b
  exact if_congr Iff.rfl h.symm rfl

/-- the public factor at the rows' coordinates -/
theorem end_S1 :
    A.En.par.S1 (A.outE o).st (A.En.par.hp (A.outE o).st (A.outE o).pt) (A.En.outOf (A.outE o)).vals
        () =
      ((List.range (2 ^ A.d)).map fun r =>
        eqN ((byVar (numsOf A (A.rd o).1 kAt).oE (traceOf A o).cls.xs).drop A.w) r *
          ((traceOf A o).lam - 1 - A.tab (A.rd o).1 r)).sum := by
  rw [sum_map_range, ← ldLkpNum_sum E A.d, end_gam, drop_ofFn]
  show (∑ r : Fin A.d → Bool, Alg.eqk _ r * (A.IT.lam ((A.D.lv A.d).base (A.outE o).st) - 1 -
    A.tab (A.IT.st ((A.D.lv A.d).base (A.outE o).st)) (numLE r))) = _
  rw [ldLkpSegK_base E A.D A.d (A.outE o).st]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [eqN_ofFn]
  rfl

/-- The closing's row (slU at LkEndM.rowB, tU) is TwV.rowEnd, spread, at the state that o holds. -/
theorem end_eq : (⟨A.En.par.slU A.En.rowB (A.En.outOf (A.outE o)), A.En.par.tU (A.En.outOf (A.outE
    o))⟩ : Row E A.J) =
    toRow (rowEnd (numsOf A (A.rd o).1 kAt) (traceOf A o)) := by
  unfold toRow rowEnd
  refine congrArg₂ Row.mk (funext fun j => ?_) rfl
  rw [@slU_dense E _ A.En.par A.decJ (fun s => pOne_mix _ _ _) (fun _ => A.cB)]
  simp only []
  rw [dense_append, dense_append, dense_scale, dense_scale, ← end_rowB A kAt (A.rd o).1 o j,
    ← end_degs A kAt (A.rd o).1]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) rfl (congrArg ((A.outE o).eps * ·) ?_)) ?_
  · rw [show (traceOf A o).tabl.reverse = lvN A.D A.d (A.outE o).st from List.reverse_reverse _]
    exact @lv_inc E _ _ A.D A.decJ _ A.d (A.outE o).st (incT0_dense A kAt (A.rd o).1 o) j
  · have hU : ∀ f : Unit → E, ∑ b : Unit, f b = f () := fun f => by
      rw [Finset.univ_unique, Finset.sum_singleton]
    refine Eq.trans (congrArg ((A.outE o).eps * ·) (hU _)) ?_
    rw [mul_assoc]
    exact congrArg ((A.outE o).eps * ·) (congrArg (· * _) (end_S1 A kAt o))

end
end Tw3
#print axioms Tw3.lvN_length
#print axioms Tw3.lv_cAt
#print axioms Tw3.lv_gamL
#print axioms Tw3.lv_degs
#print axioms Tw3.lv_incS
#print axioms Tw3.lv_inc
#print axioms Tw3.lv_row
#print axioms Tw3.lv_rows
#print axioms Tw3.tieN_length
#print axioms Tw3.tie_row0
#print axioms Tw3.tiePl_nx
#print axioms Tw3.tie_rowS
#print axioms Tw3.tie_row
#print axioms Tw3.tie_rows
#print axioms Tw3.tie_rev_succ
#print axioms Tw3.tie_be
#print axioms Tw3.tie_get_st
#print axioms Tw3.tie_bT
#print axioms Tw3.tie_bK
#print axioms Tw3.tiePl_pt
#print axioms Tw3.fK_dense
#print axioms Tw3.formT_dense
#print axioms Tw3.incT0_dense
#print axioms Tw3.rows4_eq
#print axioms Tw3.rowsT_eq
#print axioms Tw3.num_eq
#print axioms Tw3.bitU_eq
#print axioms Tw3.bit_gam
#print axioms Tw3.bitE_eq
#print axioms Tw3.end_gam
#print axioms Tw3.end_degs
#print axioms Tw3.end_rowB
#print axioms Tw3.end_S1
#print axioms Tw3.end_eq
