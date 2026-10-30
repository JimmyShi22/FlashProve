-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Road/K4/RowLightOfHead.lean: THE LIGHT TEST ON THE PENDING ROW OF K4's SUB-PROTOCOL
(`rowLightB`, Johnson/Road/K4/PendLightDefs.lean) ACCEPTS AT ALL TWELVE GROUPS OF LAYERS, FROM THE
HEAD `P5J.AtMgA` ALONE: the arithmetic half of the row `k4RowB` (Johnson/Road/K4/K4RowTest.lean).
THE STATEMENT IS THAT OF K4's FILES, TO THE LETTER.
Definitions, and statements with their proofs. WHAT THE TEST READS. rowLightB P g n lin is pendB
P.wsLay (unitsOf P g) n lin. (1) The committed table's layout P.wsLay: in the goals' scope it is
the maker's return at written values (`args_of_steps`, Johnson/Goal/Numbers/KeyPlansAtPure.lean;
the four lines that draw it here are those of `wsLay_in_scope_O`
(Johnson/Desc/Sound/K11Tests/PendAllInScope.lean)). (2) The group's
units: `unitsOf` (Johnson/Road/K4/Total/PlanRowDefs.lean) reads the layers' layout y, WHICH IS NO
WRITTEN VALUE IN SCOPE, through a view alone: the names of the segments of y's calls; y.Lam,
y.LamM; y.h.p3, y.h.L; the list of calls with terms in the second token sumcheck. Each of these is
closed in scope by a law: `LinesAre`, `callsAC_of_lines` (Johnson/Road/FormsKeysPans.lean),
`ts_of_lines` (FormsKeysPansTS.lean), `laySizes_of_layout` (Johnson/Road/K4/PlanSizes.lean), all
off `pub34_all` (Johnson/Goal/Meaning/Pub34All.lean). (3) n = hp.NCL is nclOf y g by the planner's
text (`planG_slots`, Johnson/Road/K4/Riders/LookInByMake.lean): the same view. (4) lin =
Zp.first.lin is the written shape under the first pin (`first_written_in_scope`,
Johnson/Goal/Numbers/MadeInScope.lean), and the pin comes off the head (`pins_of_laid`,
Johnson/Goal/Skeleton/PinsOfLaid.lean): MOVED INTO THE HEAD, NOT PAID. `unitsAV`, `unitsTV`,
  `unitsV`: the texts of unitsA, unitsT, unitsOf off the view's letters. `unitsA_view`,
  `unitsT_view`, **`unitsOf_view`**: they are the same functions: by rfl, at every plan.
  `linesNames`, `segs_at`, `acW`, `tsW`: the library's eight lines by their segments' names; a
  call's names under LinesAre; the two closed lists. `rowsAllB W lin k ac ts`: the test at the
  twelve groups, with k claims more. **`rowLight_written`**: BY LEAN's KERNEL, stated over the
  maker's return: all twelve accept. LOOKED AT WITH THE EVALUATOR FIRST (33 units at the first
  group, 32 at each other: nclOf's numbers). `rowLight_bite`: it can fail, at every group: one
  claim more; the first segment's name left out; another number of rows of the committed table:
  all 36 reject; a refusal of the maker would not pass for it. **`rowLight_of_head`**: the
  statement.
What is not claimed. That the head can be met at other files than `storedPublicFiles` and `zGap`, or at another
hash than secondHashFunction: no example in Lean. Nothing on
frontB, the other half of the row. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. At
OnBytes.secondHashFunction and the full size alone. Nothing on soundness. Terms: lean/GLOSSARY.md.

-/
import Johnson.Road.K4.PendLightDefs
import Johnson.Road.K4.Riders.LookInByMake
import Johnson.Road.K4.RefInScope
import Johnson.Road.FormsKeysPansTS
import Johnson.Goal.Numbers.KeyPlansAtPure
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Goal.Skeleton.PinsOfLaid
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Pend
open OnBytes OnBytes.K.Kc OnBytes.Model
open OnBytes.Model.Layer (Lay Pub Reads HPlan2 ClaimEnv layout readsOf isAcc callsTS callsAC nclOf)
open OnBytes.Model.Verify (Public publicOf layerShape)
open OnBytes.Params (LinShape recordLines)
open OnBytes.Desc.First.K4.Total (unitsA unitsT unitsW unitsOf planEnv)
open Inst.Model.All (DF)
open Inst.Model.FFSeg (Dim fams)
open Lk6.AtPlan (wsFull inScope_policy)
open VerifiableInference.PlanWritten (proofSizedFull)

/-- The units of one segment's claims in the lookup's join, off five letters. -/
def unitsAV (Lam LamM : ℕ) (p3 : Bool) (W : WsLay) (g : ℕ) (sn : String) : Option (List ℕ) :=
  if !isAcc sn then some []
  else
    (List.range (if sn == "LR" then LamM else Lam)).mapM fun i =>
      let lam := if sn == "LR" then 2 * i + 1 else i
      let mo := p3 && lam % 2 == 1
      let X := if sn == "G" then (if mo then 5 else 3)
        else if sn == "U" then (if mo then 6 else 4)
        else if sn == "V" then 1 else if sn == "O" then 2 else if sn == "D" then 9 else 11
      W.unitOf X (g * Lam + lam)

/-- The units of one segment's claims in the second token sumcheck, off five letters. -/
def unitsTV (Lam LamM : ℕ) (p3 : Bool) (W : WsLay) (g : ℕ) (sn : String) : Option (List ℕ) :=
  if sn == "QK" then (List.range Lam).mapM fun lam => W.unitOf 0 (g * Lam + lam)
  else if p3 && (sn == "G" || sn == "U" || sn == "D") then
    (List.range LamM).mapM fun lm =>
      W.unitOf (if sn == "G" then 7 else if sn == "U" then 8 else 10) (g * Lam + (2 * lm + 1))
  else some []

/-- The group's units, off six letters and the two lists of segments' names. -/
def unitsV (Lam LamM L : ℕ) (p3 : Bool) (W : WsLay) (g : ℕ) (ac ts : List String) :
    Option (List ℕ) :=
  ((ac.mapM (unitsAV Lam LamM p3 W g)).bind fun a =>
    (ts.mapM (unitsTV Lam LamM p3 W g)).map fun t => a.flatten ++ t.flatten).bind fun cp =>
      (if (g == 0) = true then (W.unitOf 12 L).map ([·]) else some []).map fun ce => cp ++ ce

theorem unitsA_view (c : ClaimEnv) (sn : String) :
    unitsA c sn = unitsAV c.v.y.Lam c.v.y.LamM c.v.y.h.p3 c.wsLay c.v.g sn := rfl

theorem unitsT_view (c : ClaimEnv) (sn : String) :
    unitsT c sn = unitsTV c.v.y.Lam c.v.y.LamM c.v.y.h.p3 c.wsLay c.v.g sn := rfl

/-- **The group's units read the plan through this view alone.** -/
theorem unitsOf_view (P : Pub) (g : ℕ) {TS : List ℕ} (hTS : callsTS P = some TS) :
    unitsOf P g = unitsV P.y.Lam P.y.LamM P.y.h.L P.y.h.p3 P.wsLay g
      ((callsAC P.y).flatMap fun q => (P.y.calls.getD q default).segs.map (·.name))
      (TS.flatMap fun q => (P.y.calls.getD q default).segs.map (·.name)) := by
  unfold unitsOf
  rw [hTS]
  rfl

/-- The library's eight lines of calls, by their segments' names. -/
def linesNames : List (List String) := (List.finRange 8).map fun cc => (fams cc).map segName

theorem segs_at {y : Lay} (hN : LinesAre y) (q : ℕ) :
    (y.calls.getD q default).segs.map (·.name) = (linesNames[q]?).getD [] := by
  unfold LinesAre at hN
  unfold linesNames
  rw [← hN, List.getElem?_map, Array.getElem?_toList, Array.getD_eq_getD_getElem?]
  cases y.calls[q]? <;> rfl

def acW : List String := [0, 1, 2].flatMap fun q => (linesNames[q]?).getD []
def tsW : List String := [0, 1, 2, 5].flatMap fun q => (linesNames[q]?).getD []

/-- The light test at all twelve groups, at a layout of the committed table, with k claims more. -/
def rowsAllB (W : WsLay) (lin : LinShape) (k : ℕ) (ac ts : List String) : List Bool :=
  (List.range 12).map fun g =>
    match unitsV 4 2 48 true W g ac ts with
    | none => false
    | some uis => pendB W uis (6 * 4 + 4 * 2 + (if g == 0 then 1 else 0) + k) lin


/-- **The kernel's fact**: at the written layout of the committed table and the written shape of the
test on it, the light test accepts at all twelve groups. Stated over the maker's return. -/
theorem rowLight_written :
    (match wsLayOf wsFull true recordLines.blockLog with
      | .ok W => (rowsAllB W proofSizedFull.batch.shape 0 acW tsW).all id
      | .error _ => false) = true := by decide +kernel

/-- It can fail, at every group: one claim more; the first segment's name left out; another number
of rows of the committed table. (A refusal of the maker would not pass for a rejection.) -/
theorem rowLight_bite :
    (match wsLayOf wsFull true recordLines.blockLog with
      | .ok W => (rowsAllB W proofSizedFull.batch.shape 1 acW tsW).any id ||
          (rowsAllB W proofSizedFull.batch.shape 0 (acW.drop 1) tsW).any id ||
          (rowsAllB W { proofSizedFull.batch.shape with matrixRows := 1 } 0 acW tsW).any id
      | .error _ => true) = false := by decide +kernel

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **THE LIGHT TEST ON THE PENDING ROW ACCEPTS AT ALL TWELVE GROUPS, FROM THE HEAD.** -/
theorem rowLight_of_head (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) :
    ∀ g, g < 12 → ∀ hp, Zp.p.X.G[g]? = some hp →
      rowLightB Zp.p.X.layers g hp.NCL Zp.first.lin = true := by
  intro g hg hp hG
  have hX : publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X := hA.pubOne
  obtain ⟨⟨hy, S, _, hrd, Zd, _, hN, _, Zw, hsL, _, _⟩, _⟩ :=
    Meaning.P34.pub34_all hA.scope hA.reads hX gl_numerals
  have hy' : layout (layerShape Zp.p.X.P) Zp.p.X.P.polCalls = .ok Zp.p.X.layers.y := hy
  have hN' : LinesAre Zp.p.X.layers.y := hN
  have hrd' : readsOf Zp.p.X.layers.y = .ok Zp.p.X.layers.rd := hrd
  have L := laySizes_of_layout hy'
  have ell : (layerShape Zp.p.X.P).ll = 2 := by
    rw [← Zd.lL]
    rfl
  have eLam : Zp.p.X.layers.y.Lam = 4 := by
    rw [L.Lam, ell]
    norm_num
  have eLamM : Zp.p.X.layers.y.LamM = 2 := by
    rw [L.LamM, ell]
    norm_num
  have ep3 : Zp.p.X.layers.y.h.p3 = true := by
    rw [L.shape]
    exact S.p3
  have eL : Zp.p.X.layers.y.h.L = 48 := by
    rw [L.shape, ← hsL, Zw.L]
    rfl
  have hTS : callsTS Zp.p.X.layers = some [0, 1, 2, 5] := ts_of_lines hy' S.p3 hN' hrd'
  have hW : wsLayOf wsFull true recordLines.blockLog = .ok Zp.p.X.layers.wsLay := by
    have hO := ProofFile.Law.pub_public hA.laid.pub
    obtain ⟨v, hv⟩ := inScope_policy hA.scope
    rw [hv] at hO
    exact (VerifiableInference.Number.ByRuns.args_of_steps
      (VerifiableInference.PlanWritten.publicSteps_of_O hO)).2
  have hn : hp.NCL = nclOf Zp.p.X.layers.y g :=
    (Riders.planG_slots _ g _ hp (Fo.Pub.public_G hX g hp hG)).2.1
  have hlin : Zp.first.lin = proofSizedFull.batch.shape :=
    (VerifiableInference.PlanWritten.Joined.first_written_in_scope hA.scope hA.laid.pub
      (P5J.pins_of_laid hA.scope hA.laid).1).2.1
  have hf := rowLight_written
  rw [hW] at hf
  have hg' := List.all_eq_true.1 hf _ (List.mem_map.2 ⟨g, List.mem_range.2 hg, rfl⟩)
  unfold rowLightB
  rw [unitsOf_view _ _ hTS, callsAC_of_lines hN']
  simp only [segs_at hN']
  rw [eLam, eLamM, eL, ep3, hn, hlin]
  unfold nclOf
  rw [eLam, eLamM, ep3]
  exact hg'

end

end OnBytes.Road.K4.Pend

#print axioms OnBytes.Road.K4.Pend.rowLight_of_head
#print axioms OnBytes.Road.K4.Pend.rowLight_written
#print axioms OnBytes.Road.K4.Pend.rowLight_bite
#print axioms OnBytes.Road.K4.Pend.unitsOf_view
#print axioms OnBytes.Road.K4.Pend.segs_at
