-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/RowsAttLight.lean: THE TEN ROWS OF AN ATTENTION LINK's BATCHING (`rowsAtt`,
BatchCellsAtt.lean) ONCE MORE, WITH SIX THINGS REWRITTEN BENEATH THE STEPS OF THE FIVE ROWS THAT ARE
THE LINK's OWN, EACH BY A LAW: `List.mergeSort` BY `Johnson.Unfolds.mergeSort_eq`
(Johnson/Unfolds/MergeSort.lean) · THE TABLES' MAKER `tablesP` BY `tablesP_S`
(Johnson/Desc/First/Att/Row/K5DryTwin.lean) · THE RUN `keysRun` BY `keysRun_Q`
(Row/K5DryNoPad.lean), UNDER THAT LAW's PREMISE: THE PLAN PASSES THE TEST ON THE PADDING KEYS · THE
MAKING OF FORMS BY `addMul_eq` AND ITS KIN (AddMulL.lean), IN THE TWO RUNS THROUGH RunsMade.lean ·
leftP's READS OF THE LEDGER BY `shown_add` (ShownAt.lean) · THE LAYING OF THE THREE FORMS OF
"planes" BY `addAllSh_L` (AddAllL.lean). THE SECOND TEXT OF THE ROWS IS WRITTEN NOWHERE: LEAN MAKES
IT. Three definitions, one theorem.

Purpose. The steps of the rows first, keys, join, second and planes all run inBlank
(Johnson/Desc/K5/Honest/Law/RunsLaw.lean), behind a test on the shape (tabsGC), which is not laid
open here. Beneath inBlank `weights` (Johnson/Desc/First/Att/Geo.lean) and `piecesOf`
(Att/Points.lean) sort a unit's pieces by List.mergeSort, which Lean's kernel does not evaluate, and
`lng` (Att/TablesP.lean) asks the size of an array that the kernel then builds whole: the two things
that K5DryTwin.lean's head names. The rows keys and join run keysRun (Att/RunsP.lean), whose
`paddingLaid` first asks padKeyOk: one entry of each call's table. The runs first and second, and
the rows that leftP lays (`left`, `leftKey`, `formOf`: Att/LeftP.lean; `MaskedSum.onSlots`:
Johnson/Desc/Part/MaskedSum4.lean), make their forms by Aff.addMul: one push an entry
(AddMulL.lean). `left` and `leftKey` read the ledger by Fork.shown some hundred times, each read by
its index (ShownAt.lean). The row planes (`planesShG`,
Johnson/Desc/ProofFile/Honest/K3/Shape/ClaimPlanes.lean) lays each of its three forms by addAllSh:
one append at the end for each column (AddAllL.lean). Whoever evaluates the batching's step on
shapes may evaluate rowsAttL.1 in rowsAtt's place, where padKeyOk is had otherwise.

How. `⟨_, fun A lm h => by delta …; simp -zeta only […]; …; rfl⟩`: delta lays the named definitions'
own texts open; simp rewrites by the named laws; the closing rfl fills the hole with the term that
then stands there. So the made term follows the library's texts at every build, and nobody types it.
It is the way of the closed facts that rewrite their own goal by mergeSort_eq (for one,
Johnson/AtFull/Entry/AttRow5.lean), with a name laid on the result. It is not the library's texts
with some words changed: the definitions' bodies stand in one another's places. One text is typed:
keysBlankQ, three lines: keysBlank's with keysRunQ.

Main names.
* `inBlankL`: inBlankL.1 A a; inBlankL.2 : ∀ A a, inBlank A a = inBlankL.1 A a. No premise.
* `keysBlankQ`; `keysBlank_Q`: where padKeyOk (parCOf A).geo = true: keysBlank A a = keysBlankQ A a.
  By `inAt_holds` (RunsLaw.lean): what inBlank returns has the plan's own numbers.
* **`rowsAttL`**: rowsAttL.1 A lm; rowsAttL.2 : ∀ A lm, padKeyOk (parCOf A).geo = true → rowsAtt A
  lm = rowsAttL.1 A lm.

Limits. THE TIE OF rowsAttL HAS A PREMISE, AND THIS FILE DOES NOT PAY IT. The library has padKeyOk
by general laws, without evaluation (`padKeyOk_ofPlan`, `padKeyOk_row`:
Johnson/Desc/First/Att/Row/K5PadKeyOk.lean), each under its own premises. WHAT A READER LOSES: THE
LIGHT TEXT CAN BE READ NOWHERE IN THIS FILE; `#print Johnson.AtFull.Shape.rowsAttL` shows it. THAT
NO List.mergeSort, NO lng, NO paddingLaid, NO Aff.addMul, NO Fork.shown AND NO addAllSh IS LEFT
BENEATH THE FIVE STEPS IS NOT STATED HERE AND CANNOT BE: it is seen by a walk over the made term's
constants, outside the library. THE TYPES OF inBlankL AND rowsAttL SAY "EQUAL", NEVER "LIGHT": both
are met by the choice that changes nothing. AND THE BUILD DOES NOT HOLD THE SIX REWRITINGS ONE BY
ONE (but for keysBlank_Q, which stands alone in its call): "simp only […]" fails only where none of
its laws rewrites: if one of several stops firing after a change in a callee's text, the file still
builds, the tie still holds, and the made term holds the heavy thing in silence: only that walk,
made anew, would show it. The five other rows (objects and guests, twice; K8.equations) stand as
rowsAtt has them; beneath K8.equations another sort stands (tablesTile). The fields run and pre of a
row are not unfolded. Equalities of functions: nothing says that a step returns, and nothing is
evaluated here. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.BatchCellsAtt
import Johnson.Desc.First.Att.Row.K5DryNoPad
import Johnson.AtFull.Shape.RunsMade
import Johnson.AtFull.Shape.ShownAt
import Johnson.AtFull.Shape.AddAllL

set_option autoImplicit false
set_option relaxedAutoImplicit false
-- For the elaboration of the made terms, which are deep.
set_option maxRecDepth 100000

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.Att
open H2K5.Honest
open AddMulL (addMul_eq sub_eq)
open ShownAt (shown_add)
open AddAllL (addAllSh_L)
open ProofFile.Honest.K3.Shape (planesShG planesShO planesAtSh)

/-- inBlank (Johnson/Desc/K5/Honest/Law/RunsLaw.lean) with the two sorts beneath it rewritten by
mergeSort_eq, the tables' maker by tablesP_S, the making of leftP's rows by addMul_eq and sub_eq,
and leftP's reads of the ledger by shown_add. The first field is made by Lean: the closing rfl fills
it. The second field is the tie. -/
def inBlankL : { f : Attention.Plan → ChainSh → Option (P.Runs.In × Nat) //
    ∀ A a, inBlank A a = f A a } :=
  ⟨_, fun A a => by
    delta inBlank K5Law.inAt P.ptsFrom P.leftP P.left P.leftKey P.formOf
      VerifiableInference.Desc.Part.MaskedSum.onSlots P.scoreW P.pointsOf P.weights P.piecesOf
    simp -zeta only [Johnson.Unfolds.mergeSort_eq, P.tablesP_S, addMul_eq, sub_eq, shown_add]
    rfl⟩

/-- keysBlank's text (RunsLaw.lean) with keysRunQ (Johnson/Desc/First/Att/Row/K5DryNoPad.lean):
keysRun less its test on the padding keys. -/
def keysBlankQ (A : Attention.Plan) (a : ChainSh) : Option (Array Aff) :=
  (partsOf a).bind fun q => (inBlank A a).bind fun x =>
    (P.Runs.firstRun x.1 x.2).bind fun y => P.Runs.keysRunQ x.1 (P.padOfO q.2.1.shape) y.2

/-- Where the plan passes the test on the padding keys, keysBlank is keysBlankQ. -/
theorem keysBlank_Q (A : Attention.Plan) (h : P.padKeyOk (P.parCOf A).geo = true) (a : ChainSh) :
    keysBlank A a = keysBlankQ A a := by
  unfold keysBlank keysBlankQ
  cases hq : partsOf a with
  | none => rfl
  | some q =>
    simp only [Option.bind_some]
    cases hx : inBlank A a with
    | none => rfl
    | some x =>
      simp only [Option.bind_some]
      have hi : K5Law.inAt (P.parCOf A) q.2.1.blank (heard5Blank q.1) (ledBlank q.2.2) =
          some x := by
        unfold inBlank at hx
        rw [hq] at hx
        exact hx
      obtain ⟨p, t, -, -, -, e⟩ := inAt_holds hi
      have hg : P.padKeyOk x.1.g = true := by rw [e]; exact h
      congr 1
      funext y
      exact P.Runs.keysRun_Q _ _ hg

/-- **The ten rows of an attention link (rowsAtt, BatchCellsAtt.lean), WHERE THE PLAN PASSES THE
TEST ON THE PADDING KEYS: with keysRunQ for keysRun, the two sorts beneath the steps of its five own
rows rewritten by mergeSort_eq, the tables' maker by tablesP_S, the runs first and second by
firstRun_L and secondRun_L (RunsMade.lean), and the laying of the three forms of "planes" by
addAllSh_L (AddAllL.lean).** Made as inBlankL is. -/
def rowsAttL : { R : Attention.Plan → Nat → List ((Nat × String) × Row) //
    ∀ A lm, P.padKeyOk (P.parCOf A).geo = true → rowsAtt A lm = R A lm } :=
  ⟨_, fun A lm h => by
    delta rowsAtt k5FirstG k5KeysG k5JoinG k5SecondG k5ReadersG planesShG planesShO planesAtSh
    simp -zeta only [keysBlank_Q A h]
    delta keysBlankQ inBlank K5Law.inAt P.ptsFrom P.leftP P.left P.leftKey P.formOf
      VerifiableInference.Desc.Part.MaskedSum.onSlots P.scoreW P.pointsOf P.weights P.piecesOf
    simp -zeta only [Johnson.Unfolds.mergeSort_eq, P.tablesP_S, firstRun_L, secondRun_L, addMul_eq,
      sub_eq, shown_add, addAllSh_L]
    rfl⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.inBlankL
#print axioms Johnson.AtFull.Shape.keysBlankQ
#print axioms Johnson.AtFull.Shape.keysBlank_Q
#print axioms Johnson.AtFull.Shape.rowsAttL
