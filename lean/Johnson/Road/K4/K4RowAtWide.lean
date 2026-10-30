-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4RowAtWide.lean: K4's ROW AT THE TABLE OF JOINTS, ON THE SIDE OF THE PROMISE AND OF
WHAT RIDES, CALLED AT THE WIDER MEANING OVER THE CLOSED BASE: `mgWide Dm E mgBase`
(Johnson/Desc/Sound/MgWide.lean, MgBase.lean), at the data `k4DataWide Dm E mgBase`
(K4MeansAtWide.lean), at the full size's written lists, at a place of K4's. Dm AND E ARE LETTERS: no
letter for a meaning or for its data is left: what is left is asked of Dm's and E's parameters, of
the public parameters X, of the piece, and of one value of the type `Link`. Three structures, three
statements with their proofs: calls.

  `K4OnD`: EIGHT EQUATIONS AND LINES ON Dm's PARAMETERS: links · nextOfPlan X m = some n (on X
    alone) · nsOf m = some par.hp.ns · d1.lay · d1.ncl m · smp is the named reader of OOD samples ·
    the committed table's decoder reads no state (NoRec) · H.req reads the public part alone.
  `K4NamedW`: NINE NAMED TESTS, each decidable, with code: toldFit · book · fence · room1 · front ·
  row · lookIn · maskP · readsP.
  `moreL_wide`: the data's door is the closed door at which the kernel's rows of
  Riders/PlanFull.lean stand.
  `k4RowPlan_wide`: `K4OnX` (nine facts on X: theorems in the goals' scope elsewhere) · `K4OnD` ·
  `K4NamedW` ⟹ `K4RowPlan` at that data and at the sort restNames: fifteen of its 36 fields fall
  inside (eleven by the kernel's rows, four by the make of Dm.runs).
  **`k4Row_wide`**: hH · these three · hhead (the head's part rides inside the fence) · hbase (one
  fact on the piece) · Dm.lk m = some l · the five ties on l's sub-protocols ⟹ `K4Front` ∧
  `K4Riders` ∧ a place pl' with `K4Keeps`, all three at `mgWide Dm E mgBase`.
  PAID INSIDE, AT THE TERM: the 44 equations of `K4Means` · the five of `K4PileNames` · the line
  `K4Kept` at twelve names · six of the seven lines of `K4Reads` (three under `K4OnD`'s lines: decT
  · req · smp; three under none: rw · stMask · base) · hDoor and hDoorP ("K8.funsThird" is the one
  name that the door lets K4's row make: by Lean's kernel; its test accepts after K4's sub-protocol
    accepts).

Limits. THE WIDER MEANING IS A BRIDGE's SIDE, NOT THE MEANING THAT COUNTS: what is shown at it
counts only when the bridge's premises are paid: facts on reached states, most of them owed. EVERY
PREMISE NAMED STANDS; THEY ARE SHOWN TOGETHER AT NO Dm. E IS A FREE LETTER: E.dP's free0, fvs and tl
are tied here by the wider meaning's own tests alone: room1 asks little; at tl m = none "K8.lay7" at
m is false at every state and the promise in front of K4 is empty. OF `K4OnX`'s NINE, g AND y ARE
SPENT BY NOTHING HERE. THE PROMISE's SIDE ALONE: what the claims that K4 opens are WORTH is not
touched. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.

-/
import Johnson.Road.K4.K4RowOfMeans
import Johnson.Road.K4.K4OnX
import Johnson.Road.K4.K4MeansAtWide
import Johnson.Road.K4.K4ReadsOf
import Johnson.Road.K4.Riders.PlanFull
import Johnson.Road.K4.Riders.Full
import Johnson.Road.K4.Riders.DoorFuns
import Johnson.Desc.Sound.MgAt.Runs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Riders (ObjRun GuestRun)
open OnBytes.Desc.First.K4.Total (rowB frontB)
open OnBytes.Road.K4.InT (StatesAt)
open OnBytes.Road.K4.Rec (readsArrayP)
open OnBytes.Road.K4.Riders (lookInPlanB riders_full k4_next_full k4_tied_full pub_fit_full
  k4_pub_full k4_door_full k4_only_full k4_obj_full k4_openAll_full door_of_fit only_of_fit
  objOpen_of_fit openAll_of_fit restNames k4Kept_of_means door_funs)
open _root_.Run (ckP)
open VerifiableInference.Desc (Place Wit Claim Link K9.statesOfLink)
open VerifiableInference.Desc.First (S ModelPart flatPlacesOf bookFit fenceFit moreItem)
open VerifiableInference.Desc.First.FillK4 (isLay k4ToldFit nextOfPlan)
open VerifiableInference.Desc.First.Look (Stored.NoRec)
open VerifiableInference.Desc.First.RecordPlan (maskSeatP)
open Johnson.Desc.First.Walk.Tied (rowsBefore)
open VerifiableInference.OnPublicFiles (LeftQ headLink)
open VerifiableInference.Desc.Sound (Frame Piece strsOf MsgT mgAll mgWide MgData WideData mgBase
  linksFull smpNamed moreWideAll runsAt_of runs_layers mgAll_pubP_said)

variable {Xi P Tok Cl : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}

/-- Eight equations and lines on the composed meaning's parameters (MgData). -/
structure K4OnD (Dm : MgData Xi P Tok rows cols nR X) (m : ℕ) (par : Par) (n : ℕ) : Prop where
  links : Dm.links = linksFull
  nextOf : nextOfPlan X m = some n
  nsOf : Dm.pubD.nsOf m = some par.hp.ns
  lay : Dm.d1.lay = par.P.wsLay
  ncl : Dm.d1.ncl m = par.hp.NCL
  smp : ∃ seats : List (ℕ × ℕ), Dm.smp = smpNamed Dm.cs seats
  dec : Stored.NoRec Dm.decT
  req : ∃ R : P → P5J.TReq, Dm.H.req = fun a => R a.1

/-- Nine named tests. -/
structure K4NamedW (Dm : MgData Xi P Tok rows cols nR X) (E : WideData P) (k m : ℕ) (par : Par)
    (told : List (List VerifiableInference.Desc.Oracle)) (n : ℕ) : Prop where
  toldFit : k4ToldFit linksFull (flatPlacesOf linksFull true) told = true
  book : bookFit Dm.N (flatPlacesOf linksFull true) told = true
  fence : fenceFit Dm.N linksFull (flatPlacesOf linksFull true) = true
  room1 : 1 ≤ E.dP.free0 - rowsBefore E.dP.fvs m
  front : frontB (!par.k3Runs) par.P par.hp par.g par.P.y.fo = true
  row : rowB par.P par.g par.hp.NCL Dm.d1.lin = true
  lookIn : lookInPlanB par X m n par.hp.ns = true
  maskP : (maskSeatP Dm.sent.shape Dm.pubD.dS (Dm.N.sent m 0) E.d12.L.places
    (Dm.N.msgsAt (flatPlacesOf linksFull true)[k]?) m).isSome = true
  readsP : readsArrayP par.hp Dm.sent.shape Dm.sent.layout (Dm.sent.arrayOf.getD m #[]) m
    (Dm.pubD.dS.trees m) = true

variable (Dm : MgData Xi P Tok rows cols nR X) (E : WideData P) {Z : P} {k m : ℕ} {pl : Place}
  {par : Par} {q : Piece (ckP .two) Fr S Cl (Wit (CellsK rows cols) Tok MsgT)}
  {told : List (List VerifiableInference.Desc.Oracle)} {pol KL : ByteArray}
  {layout : Option ByteArray} {n : ℕ} {l : Link S Claim} {nO nG : String}
  {runO runG : ℕ → S → Except String (List Claim × S)}

/-- The closed base, at the witness's type. -/
local notation "Bm" => (mgBase (P := P) (W := Wit (CellsK rows cols) Tok MsgT))

/-- The data's door is the closed door at which the kernel's rows stand. -/
theorem moreL_wide : (k4DataWide Dm E Bm).moreL = moreWideAll := rfl

/-- **`K4RowPlan` at the wider meaning's own data.** -/
theorem k4RowPlan_wide (H : AtK4 linksFull (flatPlacesOf linksFull true) k m pl)
    (Sx : K4OnX X pol KL layout m par) (Sd : K4OnD Dm m par n) (Sn : K4NamedW Dm E k m par told n) :
    K4RowPlan (k4DataWide Dm E Bm) restNames linksFull (flatPlacesOf linksFull true) k m pl par told
      pol KL layout par.hp n := by
  have hM := moreL_wide Dm E
  have hd := door_of_fit H k4_door_full
  have hr : ∀ j r, (k4DataWide Dm E Bm).runs m j r =
      VerifiableInference.Desc.First.runsOf .layers j r := fun j r => by
    show VerifiableInference.Desc.Sound.runsAt Dm.links m j r = _
    rw [Sd.links]
    exact runsAt_of linksFull m .layers H.sub j r
  exact
    { linksIs := Sd.links
      sort := riders_full H
      next := k4_next_full
      toldFit := Sn.toldFit
      book := Sn.book
      fence := Sn.fence
      fit := hM ▸ pub_fit_full
      pub := hM ▸ k4_pub_full
      tied := k4_tied_full
      only := hM ▸ only_of_fit H k4_only_full
      askRoom := hM ▸ hd.2.1
      askLeft := hM ▸ hd.2.2.2
      askBare := hM ▸ hd.2.2.1
      objOpen := objOpen_of_fit H k4_obj_full
      room1 := Sn.room1
      front := Sn.front
      shape := Sx.shape
      openAll := hM ▸ openAll_of_fit H k4_openAll_full
      maskP := Sn.maskP
      readsP := Sn.readsP
      pc2 := Sx.pc2
      pc7 := Sx.pc7
      runsOwn := (hr 3 "own").trans runs_layers.2.1
      runsObj := (hr 2 "objects").trans runs_layers.1
      runsPl := (hr 2 "planes").trans runs_layers.2.2.2.2.1
      runsJo := (hr 2 "join").trans runs_layers.2.2.2.2.2
      nextOf := Sd.nextOf
      nsOf := Sd.nsOf
      lookIn := Sn.lookIn
      lay := Sd.lay
      ncl := Sd.ncl
      row := Sn.row
      pubOf := Sx.pubOf
      notHead := Sx.notHead
      step := Sx.step
      plan := Sx.plan }

/-- **UNDER hH, H, Sx, Sd, Sn, hhead, hbase, hlk AND THE FIVE TIES (ALL PREMISES): K4's row's three
structures of lines, at the wider meaning over the closed base.** -/
theorem k4Row_wide (hH : isLay Dm.links (headLink X) = false)
    (H : AtK4 linksFull (flatPlacesOf linksFull true) k m pl) (Sx : K4OnX X pol KL layout m par)
    (Sd : K4OnD Dm m par n) (Sn : K4NamedW Dm E k m par told n)
    (hhead : ∀ s s' (x y : Fr.E.Str), LayRest s s' → SameStr Fr q.base x y → ∀ p i w,
      Dm.headPart p i (Z, s') (strsOf Fr y) w → Dm.headPart p i (Z, s) (strsOf Fr x) w)
    (hbase : Dm.N.treesAt (some pl) = q.base) (hlk : Dm.lk m = some l)
    (st : ∀ s, StatesAt (K9.statesOfLink l) 2 par "front" s ∧
      StatesAt (K9.statesOfLink l) 2 par "back" s)
    (fO : (K9.statesOfLink l 1).find? (fun r => r.1 == "objects") = some (nO, runO))
    (oRun : ObjRun runO)
    (fG : (K9.statesOfLink l 1).find? (fun r => r.1 == "guests") = some (nG, runG))
    (gRun : GuestRun runG) :
    K4Front (mgWide Dm E Bm) Z linksFull (flatPlacesOf linksFull true) m X.y.fo X.y.h.lmb 0
        (LeftQ par.hp.ns) ∧
      K4Riders Dm.N (mgWide Dm E Bm) Z linksFull (flatPlacesOf linksFull true) k m q par ∧
      ∃ pl', K4Keeps Dm.N (mgWide Dm E Bm) Z linksFull (flatPlacesOf linksFull true) k m pl pl' q
        par := by
  obtain ⟨seats, hsmp⟩ := Sd.smp
  obtain ⟨R, hreq⟩ := Sd.req
  have Em := k4Means_mgWide Dm E Bm hH (fun _ _ _ _ h => h) fun _ _ _ => rfl
  have Ep := k4Pile_mgWide Dm E Bm
  have hmk : ((mgWide Dm E Bm).more.rows linksFull pl).makes = [(some m, "K8.funsThird")] :=
    (door_of_fit H k4_door_full).1
  have Rd : K4Reads (k4DataWide Dm E Bm) Z Fr q.base :=
    k4Reads_at Z Fr q.base (arr := Dm.arr) (mat := Dm.mat13) (R := R) (seats := seats) rfl Sd.dec
      hreq hsmp rfl (fun _ _ _ _ => rfl) hhead
  refine k4Row_of_means Em (k4Kept_of_means Em Ep) Rd H (k4RowPlan_wide Dm E H Sx Sd Sn) hbase
    ⟨VerifiableInference.Desc.K9.readersAt_some Dm.lk X _ m l hlk, st, fO, oRun, fG, gRun⟩
    (door_funs Ep hmk) fun nm hnm a => ?_
  rw [hmk, List.mem_singleton] at hnm
  subst hnm
  exact mgAll_pubP_said Dm (.more (some m) "K8.funsThird") a rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.moreL_wide
#print axioms OnBytes.Road.K4.k4RowPlan_wide
#print axioms OnBytes.Road.K4.k4Row_wide
set_option pp.deepTerms true in
set_option pp.maxSteps 1000000 in
#check @OnBytes.Road.K4.k4Row_wide
