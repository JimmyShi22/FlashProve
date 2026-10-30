-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Public/Owners.lean: publicOfO's STEPS P15 · P16 · P14's TWINS · P17 · P18 TOGETHER,
  NO FREE LETTER: owners_W.
Behind Layer.Pub.of, plansG and the twelve groups' twins attentionOwners returns; the attention's
  arms with its smallness tests are the
written one; these tests' views are the library's xShapeFull's at the odd segments; ownerOf returns.
RE-CUT BY PROGRAM out of an earlier working file of this project, which is not in this repository
  (sha256 dbf68584…), its lines 347-476: NO LETTER OF LEAN TURNS; its twins (lines
23-345) are Twins.lean's. The recursion limit is raised in this file (maxRecDepth 1000000), as its
  writers had it.
Nothing on soundness.
-/
import Johnson.AtFull.Public.Twins
import OnBytes.Model.VerifySubproofs
import OnBytes.Model.RoundSizes
import Johnson.G.XShapeLit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace OnBytes.Road.K4.Trial.AttK7Owners
open OnBytes OnBytes.Model OnBytes.Model.Layer

/-- The strict scan's WRITTEN value at the stored free numbers. -/
def PW : PolScan := VerifierAndGoals.Lines.scanAt VerifierAndGoals.Lines.frameRef VerifierAndGoals.storedLines

/-- The layers' shape at that value. -/
def hW : Layer.Shape := Verify.layerShape PW

/-- A test at the value of the layers' layout's first half (false where it does not return). group
  reads
none of the three fields that the second half sets (cl, fo, kbm). -/
def withY (f : Lay → Bool) : Bool :=
  match baseNoFill hW VerifierAndGoals.Lines.callsRef with
  | .ok y => f y
  | .error _ => false

/-- A test at the scales, off the WRITTEN list of the scale file's words (false where scalesOf
  refuses). -/
def withS (f : Layer.Scales → Bool) : Bool :=
  match Layer.scalesOf hW Tie.Pv.Plan.scalesF.toArray with
  | .ok s => f s
  | .error _ => false

/-- A test at the lines callA as read (false where readLines refuses). -/
def withLines (f : List Attention.Line → Bool) : Bool :=
  match Attention.readLines PW.polCallsA with
  | .ok l => f l
  | .error _ => false

/-- A test at the configuration of the attention sub-protocol of group g (false where fill refuses).
  -/
def withCf (g : Nat) (f : Attention.Cfg → Bool) : Bool :=
  withY fun y => withS fun s => withLines fun l =>
    match Attention.fill PW y s l g with
    | .ok cf => f cf
    | .error _ => false


/-- A test at what a maker returns; false where it refuses. -/
def onOk {ε α : Type} (x : Except ε α) (f : α → Bool) : Bool :=
  match x with
  | .ok a => f a
  | .error _ => false

/-- layoutLook's own first line (LayerLayout.lean:604). -/
def clOf (y : Lay) : Array Call := y.calls.mapIdx fun q cd => y.callRecord q cd

/-- A test at a layout OF THE FORM THAT layoutLook RETURNS (LayerLayout.lean:615): the first half's
  value with cl, the forest's
numbers (made without the tests on the calls' tables: the twin shapeNoAsk), the columns of matrix b;
  THE PADDING COUNTS pub ARE A
FREE LETTER. -/
def withLook (pub : Array Nat) (f : Lay → Bool) : Bool :=
  onOk (baseNoFill hW VerifierAndGoals.Lines.callsRef) fun y0 =>
    onOk (Forest.shapeNoAsk (clOf y0) y0.h.lidb) fun fo =>
      onOk (Forest.planeCols fo y0.h.lmb) fun kbm =>
        f { y0 with cl := clOf y0, fo := { fo with pub := pub }, kbm := kbm }

/-- A test at the layers' public numbers as publicOfO makes them (PublicAt.lean:129-154). -/
def withPub (pub : Array Nat) (f : Layer.Pub → Bool) : Bool :=
  withLook pub fun y => onOk (Layer.scalesOf y.h Tie.Pv.Plan.scalesF.toArray) fun sc =>
    onOk (wsLayOf (Verify.weightShape PW y) y.h.p3 PW.lkW) fun wsLay =>
      onOk (Layer.ropeOf y.h) fun rope =>
        onOk (Layer.Pub.of y sc rope wsLay PW.h.V #[] PW.settings) f

/-- layoutLook's padding counts (LayerLayout.lean:610-611), or none where its loop refuses: A CLOSED
  TERM THAT NO FACT HERE OPENS. -/
def pubOf (y : Lay) (fo : Forest.Shape) : Array Nat :=
  ((y.calls.toList.zipIdx).foldlM (fun pub x => y.pubOfCall fo x.2 x.1 pub) (Forest.noPub
      fo)).toOption.getD #[]

/-- withLook with layoutLook's own padding counts, as a closed term: NO FREE LETTER. -/
def withLookC (f : Lay → Bool) : Bool :=
  onOk (baseNoFill hW VerifierAndGoals.Lines.callsRef) fun y0 =>
    onOk (Forest.shapeNoAsk (clOf y0) y0.h.lidb) fun fo =>
      onOk (Forest.planeCols fo y0.h.lmb) fun kbm =>
        f { y0 with cl := clOf y0, fo := { fo with pub := pubOf y0 fo }, kbm := kbm }

/-- withPub likewise. -/
def withPubC (f : Layer.Pub → Bool) : Bool :=
  withLookC fun y => onOk (Layer.scalesOf y.h Tie.Pv.Plan.scalesF.toArray) fun sc =>
    onOk (wsLayOf (Verify.weightShape PW y) y.h.p3 PW.lkW) fun wsLay =>
      onOk (Layer.ropeOf y.h) fun rope =>
        onOk (Layer.Pub.of y sc rope wsLay PW.h.V #[] PW.settings) f

/-- The number that names group g's matrix qa: publicOfO's own term (PublicAt.lean:150). -/
def mqOf (y : Lay) (g : Nat) : Nat := (((Layer.tailsOf y).getD g {}).mats.getD (Layer.matIx y).iQA
    {}).aId

/-- The table of exponentials: the library's list (L5.expTable_ref). -/
def ttR : Option (Array Nat) := some OnBytes.Road.L5.refL.toArray

/-- What armOf reads of the plan of the layers' group g
  (Johnson/Desc/First/Link/RowsRun.lean:82-85), WRITTEN: off a print of Lean's
evaluator at the verifier's own routines (by a sheet that is not in this repository). A value for
  the test armsG below: no fact in this file
runs that test; the layers' arms are held by arms_W (ArmsAtMakers.lean). -/
def armGW (g : Nat) : Params.ForestSize × Params.LayerRounds × Params.SmallSize × Nat :=
  ({ v := 30, d := 19, shifted := true },
   { lt := 10, ls := 6, lNI := 3, lPd := 13, ll := 2, lPf := 14, lfe := 13, lamS := 23, lkW := 18,
       NI := 8, NS := 9,
     NP := 7, NO := 4, withTerms := true, shownByTheTerms := 266, neverSent := 3, weightClaims :=
         32,
     firstGroup := g == 0, routed := true },
   { columns := 24086, tau := 128, digits := { v := 27, d := 11, shifted := true } },
   if g == 0 then 32005923 else 32005793)

/-- What armOf reads of an attention's plan (:88-90), WRITTEN: off a print of Lean's evaluator (by a
  sheet that is not in this repository). -/
def armAW : Params.ForestSize × Params.AttentionRounds × Params.SmallSize :=
  ({ v := 29, d := 18, shifted := true },
   { lt := 10, lgk := 3, pairs := 20, Lam := 4, planeMessages := 2, score := [(17, 20), (14, 20)], e
       := 13,
     valueM := 16, valueD := 13, attained := 20, bits := 17, rows := 14166783 },
   { columns := 10248, tau := 128, digits := { v := 26, d := 11, shifted := true } })

/-- A TEST, and no fact in this file runs it (the layers' arms are arms_W's, ArmsAtMakers.lean): the
  layers' twelve arms are the written ones, and the views of their smallness tests (tailView,
Johnson/Desc/Ok/PlanWritten/XShape.lean) are the written xShapeFull's at the even segments
  (Johnson/G/XShapeLit.lean). -/
def armsG (L : Layer.Pub) (G : Array Layer.HPlan2) : Bool :=
  G.size == 12 && G.toList.zipIdx.all fun x =>
    decide ((forestSize L.y.fo, Verify.layerNumbers L x.1 x.2, smallSize x.1.tl, x.1.nBatched) =
        armGW x.2) &&
      decide (some (VerifiableInference.PlanWritten.tailView x.1.tl) = Johnson.G.xShapeFull.1.getD
          (2 * x.2) none)

/-- publicOfO's lines 156-160 behind the plans: attentionOwners returns; the attention's twelve
  arms, with the smallness tests that it
returns, are the written one, and these tests' views are xShapeFull's at the odd segments; ownerOf
  returns. -/
def ownersB (L : Layer.Pub) (G : Array Layer.HPlan2) (A0 : Array Attention.Plan) : Bool :=
  onOk (Verify.attentionOwners L.y.h.p4 L.y.NGr (G.map fun O => (⟨O.tl, O.Fp, O.Tp⟩ :
      Verify.SubPlan))
      (A0.map fun X => ⟨X.seam.tl, X.seam.Fp, X.seam.Tp⟩)) fun seenA =>
    let A := A0.zipWith (fun X s => { X with seam := { X.seam with tl := s.tl } }) seenA
    A.size == 12 &&
      (A.toList.zipIdx.all fun x => decide ((forestSize x.1.fs, x.1.own, smallSize x.1.seam.tl) =
          armAW) &&
        decide (some (VerifiableInference.PlanWritten.tailView x.1.seam.tl) =
          Johnson.G.xShapeFull.1.getD (2 * x.2 + 1) none)) &&
      onOk (Verify.ownerOf L.y G) fun _ => true

theorem owners_W : withPubC (fun L => onOk (Layer.plansG L) fun G =>
    onOk (Attention.readLines PW.polCallsA) fun l =>
      onOk ((List.range L.y.NGr).mapM (Attention.groupS ttR PW L.y L.sc (mqOf L.y) l)) fun ps =>
        ownersB L G ps.toArray) = true := by
  decide +kernel

end OnBytes.Road.K4.Trial.AttK7Owners

#print axioms OnBytes.Road.K4.Trial.AttK7Owners.owners_W
