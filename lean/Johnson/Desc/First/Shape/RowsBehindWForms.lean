-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Shape/RowsBehindWForms.lean: THE MAKES OF THE STATEMENT's ROWS BEHIND KIND K13's
QUIET SUB-PROTOCOL BEHIND W's COMMITMENT (K13.rowsB at the first chain's lens): the one small law
more that ChainF.lean asks of a member that turns the statement. General laws; nothing is evaluated.
  `eqOnTableSh`, `eqOnTable_sh`: the make of an equality vector laid on a table (VectorLay.onTable,
    OnBytes/Iop/Tensor.lean): of the number of its coordinates and the table's bits alone.
  **`evalMk`**, `eval_mk`: the make of the row (Eval) (linEvalRow, OnBytes/Iop/Lin.lean): plain; one
    term on W's main table; the claim's masks as single entries; no run, no form: a function of the
    codes, the plan's shape, the claim's shape and W's number. eval_mk stands at any layout and does
    not name evalMk: at lay := linLayW codes S its right side is evalMk's text.
  `joins_forms`, **`eval_forms`**: behind K13.rows the makes are those in front with one new group,
    which holds the row (Eval) alone.
  `rowsForms p a F`, **`rowsB_forms`**: behind a yes of K13.rowsB: formsOf t.st = rowsForms p
    (chainSh s) (formsOf s.st): rowsForms reads off the shape what stands at the memory (the numbers
    handed on, the claim's shape), the number of groups and the codes.
By Forms.lean's newGroup_forms, join_forms, addRows_forms; Makes.lean's tensorSh_insertChoice; the
library's rows_is (Johnson/Desc/K13/Law/TextIs.lean), rowsB_ok (Law/M4Proof.lean) and join_codes
(Law/M4.lean).
Limits. From a yes alone. rowsForms IS TOTAL AND ANSWERS IN SILENCE: where the shape does not stand
at the memory with a claim laid it returns F itself, as if the member turned no row; where no number
is handed on it lays the row on the message noId; and it takes the new group's number from the
CORE's number of groups while it lays on F's list: where the two lengths differ the row lands on
another group or on none (modAt turns nothing outside the list). THE BARE WORD modAt IN rowsForms
AND IN eval_forms' STATEMENT IS VerifiableInference.Desc.First.Shape.modAt (Parts.lean), NOT THE
Ground.Sh.modAt THAT AN open LINE OF THIS FILE NAMES (asked of Lean: rowsForms names the first
alone). The two are two constants with one text: a law that is stated of the one is not stated of
the other. Nothing on what the row is worth. Nothing on soundness, completeness or hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Shape.RowsBehindW
import Johnson.Desc.First.Shape.Forms
import Johnson.Desc.K13.Law.M4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Shape
open OnBytes OnBytes.Model OnBytes.Params VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Ground.Sh (CoreSh coreSh shD modAt)
open VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc.K13.Honest (claimSh4)

/-- The make of an equality vector of n coordinates, laid on a table. -/
def eqOnTableSh (l : VectorLay) (n : Nat) : TensorSh :=
  { pairs := n + (l.bits - n), denseVars := [], values := 0, first := 0 }

theorem eqOnTable_sh (l : VectorLay) (z : List E) :
    tensorSh (l.onTable (Tensor.eq z)) = eqOnTableSh l z.length := by
  have hv : (Tensor.eq z).vars = z.length := by
    show (z.map fun x => (subE oneE x, x)).length = _
    rw [List.length_map]
  have h1 := tensorSh_insertChoice (Tensor.eq z) (Tensor.eq z).vars (l.bits - (Tensor.eq z).vars) 0
  have h2 : tensorSh ((Tensor.eq z).insertChoice (Tensor.eq z).vars
      (l.bits - (Tensor.eq z).vars) 0) = eqOnTableSh l z.length := by
    rw [h1, hv]
    show TensorSh.mk ((z.map fun x => (subE oneE x, x)).length + (l.bits - z.length))
      (([] : List Nat).map _) 0 0 = _
    rw [List.length_map]
    rfl
  unfold VectorLay.onTable
  dsimp only
  generalize (Tensor.eq z).insertChoice (Tensor.eq z).vars (l.bits - (Tensor.eq z).vars) 0 = w
    at h2 ⊢
  obtain ⟨sc, ps, dv, vs, fi⟩ := w
  have e1 : ps.length = z.length + (l.bits - z.length) := congrArg TensorSh.pairs h2
  have e2 : dv = [] := congrArg TensorSh.denseVars h2
  have e3 : vs.size = 0 := congrArg TensorSh.values h2
  have e4 : fi = 0 := congrArg TensorSh.first h2
  subst e2 e4
  split
  · show TensorSh.mk (ps.drop l.placeBits ++ ps.take l.placeBits).length [] vs.size 0 = _
    have e5 : (ps.drop l.placeBits ++ ps.take l.placeBits).length = ps.length := by
      rw [List.length_append, List.length_drop, List.length_take]
      omega
    rw [e5, e1, e3]
    rfl
  · exact h2

/-- **The make of the row (Eval)**: one term on W's main table, the equality vector at the claim's
point laid on that table; the claim's masks as single entries. c: the claim's shape; w: W's number.
-/
def evalMk (codes : Codes) (S : LinShape) (c : K13.Honest.ClaimSh) (w : Nat) : RowMk :=
  ⟨.plain, [⟨w, .main, eqOnTableSh (linLayW codes S) c.point⟩],
    c.slots.map fun u => ⟨u.1, u.2.1, u.2.2⟩, [], []⟩

theorem eval_mk {S : LinShape} {claim : LinClaim} {w : Nat} {lay : VectorLay} {row : OnBytes.Row}
    (h : linEvalRow S claim w lay = some row) :
    rowMk row = ⟨.plain, [⟨w, .main, eqOnTableSh lay (claimSh4 claim).point⟩],
      (claimSh4 claim).slots.map fun u => ⟨u.1, u.2.1, u.2.2⟩, [], []⟩ := by
  unfold linEvalRow at h
  by_cases hc : (claim.psi.length == S.kCol) = true
  · simp only [hc, guard, if_true] at h
    obtain rfl := Option.some.inj h
    show RowMk.mk .plain [⟨w, .main, tensorSh (lay.onTable (Tensor.eq claim.psi))⟩]
      (claim.masks.toList.map unitMk) [] [] = _
    rw [eqOnTable_sh]
    congr 1
    show _ = (claim.masks.toList.map fun u => (u.oracle, u.part, u.index)).map _
    rw [List.map_map]
    rfl
  · simp [hc, guard] at h

/-- K13.joinAll leaves the makes and the codes. -/
theorem joins_forms {g : Nat} : ∀ (l : List Nat) (d d' : K13.St), K13.joinAll g l d = .ok d' →
    formsOf d'.st = formsOf d.st ∧ d'.st.codes = d.st.codes
  | [], d, d', hj => by
    obtain rfl : d = d' := Except.ok.inj hj
    exact ⟨rfl, rfl⟩
  | o :: l, d, d', hj => by
    simp only [K13.joinAll, K13.Law.bind_ok, K13.Law.there_ok] at hj
    obtain ⟨d₁, h1, h2⟩ := hj
    obtain ⟨a, b⟩ := joins_forms l d₁ d' h2
    exact ⟨a.trans (join_forms h1), b.trans (join_codes h1)⟩

/-- **The makes behind K13.rows**: one new group, which holds the row (Eval) alone. -/
theorem eval_forms {S : LinShape} {claim : LinClaim} {ids : Array Nat} {d : K13.St}
    {o : LinFirst × K13.St} (h : K13.rows S claim ids d = .ok o) :
    formsOf o.2.st = { formsOf d.st with
      groups := modAt ((formsOf d.st).groups ++ [[]]) d.st.groups.size
        (· ++ [evalMk d.st.codes S (claimSh4 claim) ((ids[0]?).getD noId)]) } := by
  simp only [rows_is, K13.Law.bind_ok, K13.Law.there_ok, K13.Law.pure_ok] at h
  obtain ⟨w, hw, b, hb, d₁, h1, d₂, h2, split, hsp, d₃, h3, mask, hmask, row, hrow, d₄, h4, rfl⟩ :=
      h
  obtain ⟨g, d₀⟩ := b
  have f0 := newGroup_forms hb
  have hg : g = d.st.groups.size ∧ d₀.st.codes = d.st.codes := by
    unfold Ground.newGroupP at hb
    split at hb
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hb)
      exact ⟨rfl, rfl⟩
    · cases hb
  obtain ⟨f1, c1⟩ := joins_forms _ _ _ h1
  have f2 := join_forms h2
  have c2 := join_codes h2
  have f3 : formsOf d₃.st = formsOf d₂.st ∧ d₃.st.codes = d₂.st.codes := by
    by_cases hs : S.ownSplitNeeded = true
    · rw [if_pos hs] at h3
      exact ⟨join_forms h3, join_codes h3⟩
    · rw [if_neg hs] at h3
      rw [Option.some.inj h3]
      exact ⟨rfl, rfl⟩
  have f4 := addRows_forms h4
  have hc : d₃.st.codes = d.st.codes := f3.2.trans (c2.trans (c1.trans hg.2))
  have hm := eval_mk hrow
  rw [hc] at hm
  show formsOf d₄.st = _
  rw [f4, f3.1, f2, f1, f0, hw]
  show _ = { formsOf d.st with
    groups := modAt ((formsOf d.st).groups ++ [[]]) d.st.groups.size
      (· ++ [evalMk d.st.codes S (claimSh4 claim) w]) }
  rw [← hg.1]
  show FormsSh.mk _ _ = FormsSh.mk _ _
  congr 1
  show modAt _ g (· ++ [rowMk row]) = _
  rw [hm]
  rfl

/-- The makes behind the quiet sub-protocol, of the shape in front and the makes in front. TOTAL: it
answers in silence where the sub-protocol would refuse: see the head's Limits. -/
def rowsForms (p : K13.Where) (a : ChainSh) (F : FormsSh) : FormsSh :=
  match a.atEnd with
  | some (_, ids, some l) =>
    { F with
      groups := modAt (F.groups ++ [[]]) a.core.st.groups.length
        (· ++ [evalMk a.core.st.codes p.lin l.claim ((ids[0]?).getD noId)]) }
  | _ => F

/-- **The one small law more** (ChainF.lean) at K13.rowsB. -/
theorem rowsB_forms {p : K13.Where} {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K13.rowsB (Cl := Unit) K13.atS p).decide s rs gs = .ok t) :
    formsOf t.st = rowsForms p (chainSh s) (formsOf s.st) := by
  obtain ⟨q, l, o, hp, hl, hrows, rfl⟩ := rowsB_ok K13.atS p h
  cases hs : s.here with
  | mem a =>
    simp only [K13.atS, hs] at hp
    obtain rfl := Option.some.inj hp
    have hl' : a.lin = some l := hl
    have hrows' : K13.rows p.lin l.claim a.ids ⟨s.st, s.book, s.roots, [], ()⟩ = .ok o := hrows
    have hE := eval_forms hrows'
    have hend : (chainSh s).atEnd = some (a.msg, a.ids, some (K13.Honest.laidSh l)) := by
      show endSh s.here = _
      rw [hs]
      show some (a.msg, a.ids, a.lin.map K13.Honest.laidSh) = _
      rw [hl']
      rfl
    have hst : (K13.atS.set s
        { owed := if s.noneWaits = true then none else s.rowsOwed
          heard := s.out.reply
          indexMasks := s.out.indexMasks
          pile := s.out.pending
          msg := a.msg
          ids := a.ids
          lin := some o.1
          d := o.2 }).st = o.2.st := by
      simp only [K13.atS, hs]
    show formsOf (K13.atS.set s _).st = _
    rw [hst, hE]
    unfold rowsForms
    rw [hend]
    show _ = { formsOf s.st with
      groups := modAt ((formsOf s.st).groups ++ [[]]) (Ground.Sh.stSh s.st).groups.length
        (· ++ [evalMk s.st.codes p.lin (claimSh4 l.claim) ((a.ids[0]?).getD noId)]) }
    rw [Ground.Sh.grp_size]
  | between => simp [K13.atS, hs] at hp
  | lay a => simp [K13.atS, hs] at hp
  | att a => simp [K13.atS, hs] at hp
  | head a => simp [K13.atS, hs] at hp
  | fin a => simp [K13.atS, hs] at hp

end VerifiableInference.Desc.First.Shape

#print axioms VerifiableInference.Desc.First.Shape.eqOnTable_sh
#print axioms VerifiableInference.Desc.First.Shape.eval_mk
#print axioms VerifiableInference.Desc.First.Shape.joins_forms
#print axioms VerifiableInference.Desc.First.Shape.eval_forms
#print axioms VerifiableInference.Desc.First.Shape.rowsB_forms
#print axioms VerifiableInference.Desc.First.Shape.eqOnTableSh
#print axioms VerifiableInference.Desc.First.Shape.evalMk
#print axioms VerifiableInference.Desc.First.Shape.rowsForms
