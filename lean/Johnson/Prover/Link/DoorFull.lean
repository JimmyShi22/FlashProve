-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/DoorFull.lean: THE FORM's HALF AT THE LINK, AT THE FULL SIZE: THE DOOR INTO THE
PROXIMITY TEST WITH EVERY PREMISE ON THE PLAN PAID: door_premises'
(Johnson/Prover/Link/DoorPayGp.lean) and formInv0 (DoorInv0.lean) at the link's typed parameters frP
(Johnson/Desc/K15/TypedP.lean) and the letters of DoorPlanFull.lean.

Main names (namespace Johnson.Prover.Link.Full).
  full_rows   the rows that the place's numbers count: one closed clause, by Lean's kernel
      ("decide +kernel").
  rows_count_of   from the declared round's count, the place's number and the group's open rows to
      the count that the batching asks. General.
  curF_of, nxtF_of   whoever names the place's stages as a list's head and second names curF, nxtF.
  door_full   THE DOOR's THREE STRUCTURES AT frP, and the library's structure of facts with them.
  formInv0_full   THE FORM's HALF OF THE LOOP's INVARIANT AT STAGE 0, AT frP.

By calls: door_premises', doorPlan_full, gpPlan_full, formInv0, seatPlan_full, ran_of_front,
ran_group (this folder); plan_full (Johnson/Prover/Link/AtD.lean).

Limits. STILL PREMISES: the two keys' items; that the six front blocks accept; LinkSeats, "in order"
and the number of the group's open rows behind them; that the batching's declared round counts the
place's rows; for formInv0_full besides: the batching's own equation, the written column's length,
and the field "decl". That the parameters that run are frP is a law in scope elsewhere. Nothing on
values. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.DoorGpMembers
import Johnson.Prover.Link.DoorInv0Members
import Johnson.Prover.Link.AtD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link.Full
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Desc.K15 (St P15 frP frontBlock blocksOrV first ctxOf t12Of fiveOf)
open Johnson.Prover.Link.Members (gpPlan_full seatPlan_full)

theorem full_rows : pF.nums.rows =
    2 * frP.S.table.answers + (frP.S.columnsFirst + frP.S.columnsFurther) + 1 + 2 := by
  decide +kernel

/-- From the declared round's count to the count that the batching asks. -/
theorem rows_count_of {p : P12} {cut : List Fmt.DeclaredRound} {G : Group} {X : Nat}
    (hcut : ∀ d ∈ cut, d.entry.rows = p.nums.rows) (hp : p.nums.rows = X + 2)
    (hG : G.rows.size = X) : ∀ d ∈ cut, d.entry.rows = G.rows.size + 2 :=
  fun d hd => by rw [hcut d hd, hp, hG]

/-- Whoever names the place's stages as a first one and the rest names curF; and nxtF, where there
is a second. -/
theorem curF_of {a : Fmt.M1.Stage} {l : List Fmt.M1.Stage} (h : pF.nums.stages = a :: l) :
    a = curF := by
  unfold curF
  rw [h]
  rfl

theorem nxtF_of {a b : Fmt.M1.Stage} {l : List Fmt.M1.Stage} (h : pF.nums.stages = a :: b :: l) :
    b = nxtF := by
  unfold nxtF
  rw [h]
  rfl

section
variable (x : TableKey × TableKey) (hi0 : x.1.item = 0) (hi1 : x.2.item = 1)
  (es : List Fmt.Entry) (d' : St) (G' : Group) (rs rest : List Fmt.RoundView) (cols cols' : List OpenedColumn)
  (h : foldBlocks 0 (frontBlock frP :: blocksOrV frP) (first frP.codes x) rs cols =
    .ok (d', rest, cols'))
  (hS : LinkSeats frP.par d' G') (ho : InOrder d'.st)
  (hn : G'.rows.size =
    2 * frP.S.table.answers + (frP.S.columnsFirst + frP.S.columnsFurther) + 1)

include hi0 hi1 h hS ho hn

/-- **THE DOOR AT THE FULL SIZE.** -/
theorem door_full (cut : List Fmt.DeclaredRound) (hcut : ∀ d ∈ cut, d.entry.rows = pF.nums.rows) :
    TestFront pF curF nxtF (t12Of d') G' iF nF 2 ∧ BatOwes pF cut (t12Of d') G' ∧
      FrontOwes pF (t12Of d') G' ∧
      ∃ X D, LinkRanR frP.S x.1 x.2 (ctxOf es (first frP.codes x) rs cols)
        (ctxOf (es.drop 5) d' rest cols') X D ∧ X.group = d'.loc.g ∧
        X.mask = d'.loc.firstMask :=
  door_premises' frP x doorPlan_full gpPlan_full plan_full.2.1 plan_full.2.2.2 rfl _
    plan_full.1 es hi0 hi1 plan_full.2.2.1 d' G' rs rest cols cols' h hS ho cut
    (rows_count_of hcut full_rows hn)

omit hn in
/-- **THE FORM's HALF OF THE LOOP's INVARIANT AT STAGE 0, AT THE FULL SIZE.** θ: the element that
"BAT" sampled; row: the batched claim. -/
theorem formInv0_full (θ : E) (row : GroupRow)
    (hc : Bat.combine (begun d'.st d'.loc.g G') d'.loc.g
      ⟨layoutOf d'.st G', runRows d'.st G'⟩ θ = some row)
    (l : Laid) (col : ℕ → List UInt64)
    (hcol : ∀ y, (col y).length = 3 * (frP.S.rows + (frP.S.rows + 1)))
    (hdecl : ∀ T : Tree, T.number = 0 → T.shape.logN = curF.C.a →
      (∃ lay, layTrees frP.codes (linkMessage frP.S 1) = some lay ∧
        lay.shapes[0]? = some T.shape) →
      ∀ dS dC, ((l.drop (1 + curF.k)).take 2).map (·.1) = [dS, dC] →
        ∃ o, dC.opens = [o] ∧ o.1.tree = T.number ∧ o.1.a = curF.C.a ∧
          o.1.W = T.shape.mainWidth + T.shape.maskWidth) :
    ∃ T : Tree,
      FormInv pF 0 curF l (batT (t12Of d') G' row) col row (layoutOf d'.st G')
        ⟨iF.1, iF.2, curF.k, curF.h⟩ nF 2 0 T ∧ T.number = 0 := by
  obtain ⟨X, D, hR, e1, e2⟩ := ran_of_front frP x plan_full.2.1 plan_full.2.2.2 rfl _
    plan_full.1 [] d' rs rest cols cols' hi0 hi1 plan_full.2.2.1 h
  have hG : G' = linkGrpR frP.S D.rec0 D.rec1 D.rows0 D.rows1 D.rE 0 := by
    have a := hS.group
    have b := ran_group hR
    rw [e1] at b
    exact Option.some.inj (a.symm.trans b)
  subst hG
  have hroots : pF.nums.free = (t12Of d').roots := by
    rw [doorPlan_full.free]
    have a : d'.roots = 0 + D.lay.shapes.size := hR.roots
    rw [doorPlan_full.one D.lay hR.laid] at a
    exact a.symm
  obtain ⟨T, hF, hnum, hsh⟩ := formInv0 hR doorPlan_full (t := t12Of d') rfl rfl e1.symm e2.symm
    seatPlan_full ho hroots θ row hc l col hcol
    (fun T h1 h2 h3 => hdecl T h1 h3 ⟨D.lay, hR.laid, h2⟩)
  exact ⟨T, hF, hnum⟩

omit ho hn in
/-- **NOTHING IS LEFT UNTESTED BEHIND THE BATCHING, AT THE FULL SIZE.** -/
theorem left0_full (row : GroupRow) : ChainEnd.NothingLeft (batT (t12Of d') G' row).st := by
  obtain ⟨X, D, hR, e1, -⟩ := ran_of_front frP x plan_full.2.1 plan_full.2.2.2 rfl _
    plan_full.1 [] d' rs rest cols cols' hi0 hi1 plan_full.2.2.1 h
  have hG : G' = linkGrpR frP.S D.rec0 D.rec1 D.rows0 D.rows1 D.rE 0 := by
    have a := hS.group
    have b := ran_group hR
    rw [e1] at b
    exact Option.some.inj (a.symm.trans b)
  subst hG
  exact left0 hR doorPlan_full (t := t12Of d') rfl e1.symm rfl rfl

end

end Johnson.Prover.Link.Full

#print axioms Johnson.Prover.Link.Full.full_rows
#print axioms Johnson.Prover.Link.Full.rows_count_of
#print axioms Johnson.Prover.Link.Full.curF_of
#print axioms Johnson.Prover.Link.Full.nxtF_of
#print axioms Johnson.Prover.Link.Full.door_full
#print axioms Johnson.Prover.Link.Full.formInv0_full
#print axioms Johnson.Prover.Link.Full.left0_full
