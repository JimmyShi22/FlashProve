-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/FormsAtPinsFirst.lean: THE LINE "forms" OF `K4Lines` AT THE PINNED VALUE IN THE
FIRST GROUP. The twin of `forms_pins` (Johnson/Road/K4/FormsAtPins.lean), by its proof:
`forms_of_means` (Johnson/Road/K4/FormsOfMeans.lean) is general in the value's letters QK and in
part: here QK := the letters that the first group's reference value (`RefSeat.atRecF`,
CloseRefFirst.lean) shares with a later group's, at a structure A : `PinPlan` (`PinPlan.seatN`),
part := `partOf`, M := `matsOfB`. `mask_pins`, `raw_pins`, `recIs_run` (FormsAtPins.lean) name no
value and no group: they are taken as they stand. One theorem. No new argument.

  `forms_pinsF`: THE LINE, at `((A.seatN …).atRecF X par).toPlan4K.semOf`: the sentence that the
    first group's filling's line forms asks (K4PinsAllFirst.lean, K4PinsEndFirst.lean), with the
    promise behind that remembers the accepting run (`keptFrom`) in hand.

WHAT PARTS FROM THE MODEL: the value; the premise par.g < 12 falls; `mats_rawF`
(K4PinsIdnFirst.lean) stands for `mats_raw`. NOTHING IN IT ASKS THAT THE GROUP IS THE FIRST.

Limits. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. EVERY PREMISE OF `forms_pins`
IS A PREMISE HERE, none paid: E, hRd, hruns, hk, hcs · asks · the five tests with code on the public
parameters (hO, hArr, hMask, hCells, hell) · hsits, hcov · hns · hSt: FormsAtPins.lean's Limits say
what each is. THE TEST hO (`openAllB`, Johnson/Road/K4/Rec/Whole.lean) ASKS SIX PUBLIC ITEMS AT
BORDER k, OF WHICH THREE ("frame.liveIs", "K12.seatsCarried", "K12.msgShapes") LEAVE THE TABLE's
DOOR IN THE COMPOSED FILLING `mgAll` (`leavesName`, Johnson/Desc/First/SmallDoor.lean): AT A DOOR
WITHOUT THEM hO IS FALSE AND THIS THEOREM SAYS NOTHING: it speaks at a wider door alone. WHETHER
asks, hns AND hSt CAN BE HAD IN THE FIRST GROUP, whose list of rounds is another (`dsFirst`), HAS
NOT BEEN LOOKED AT. Met through Lean at no member. Nothing on soundness.
-/
import Johnson.Road.K4.FormsAtPins
import Johnson.Road.K4.K4PinsIdnFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4

open Iop OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Flat OnBytes.Maker
open OnBytes.Model.Layer (Pub Own Lay)
open OnBytes.Desc.First.K4 (Par seatS formsBack)
open OnBytes.Desc.First.K4.Total (KeptAsks)
open OnBytes.Desc.First.K4.InT (segAt_lay)
open OnBytes.Road.K4.InT (InTAsks StatesAt kept_open)
open OnBytes.Road.K4.Rec (RecIs RecPlan Part9 recPlanOf recIs_at recIs_behind readsArrayP
  readsArray_plan maskPlanB maskPlan_of_B maskOne_of_plan maskEllP maskEllP_at arraysPlanB
  arrayPlan_of_B cellPlan_of_array cellOne_of_plan openAllB)
open _root_.Run (ckP)
open VerifiableInference.Desc (Place Wit Claim Link K9.LinkHoles K9.statesOfLink K9.readersOfLink
  K9.segAt?)
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers)
open VerifiableInference.Desc.First.Look (sigListCalls szOf)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (Frame Piece Mem onQ meansQ MsgT GQ dataQ seatTab StatedIs)
open VerifiableInference.Desc.Plain.K04 (FormsT frontRun)

variable [scl : Inst.Model.Scl] {Xi P Tok Cl : Type} {rows cols nR kC : ℕ} {X : Verify.Public}
  {Fr : Frame}
  {Mg : Meaning P (Wit (CellsK rows cols) Tok MsgT)} {D : K4Data Xi P Tok rows cols nR kC X} {Z : P}
  {links : List ModelPart} {ps : List Place} {k m : ℕ}
  {q : Piece (ckP .two) Fr S Cl (Wit (CellsK rows cols) Tok MsgT)} {par : Par}

/-- **THE LINE "forms" AT THE PINNED VALUE IN THE FIRST GROUP**, under E hRd hruns hk hcs · asks ·
hO hArr hMask hCells hell · hsits hcov · hns hSt. -/
theorem forms_pinsF (A : PinPlan (CellsK rows cols)) (nV : ℕ) (y : Lay)
    (nM nRr nC n0 ns nx v7 : ℕ) (E : K4Means Mg D) {Hh : K9.LinkHoles}
    {l : Link S Claim} (hRd : D.Rd m = K9.readersOfLink Hh l)
    (hruns : D.runs m 3 "own" = [(2, "front"), (2, "back")]) (hk : par.k3Runs = true)
    (hcs : A.D.codes = D.cs)
    (asks : ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∃ (P₀ : Pub) (o₀ : Own),
        KeptAsks par a.1 (behindOf seatS q a τ o G').1 P₀ o₀ ∧
        InTAsks (D.N.sent m 0) par a.1 (behindOf seatS q a τ o G').1 ∧
        StatesAt (K9.statesOfLink l) 2 par "front" (behindOf seatS q a τ o G').1 ∧
        StatesAt (K9.statesOfLink l) 2 par "back" (behindOf seatS q a τ o G').1)
    (hO : openAllB D.moreL links ps k m = true)
    (hArr : readsArrayP par.hp D.D3.shape D.D3.layout (D.D3.arrayOf.getD m #[]) m (D.sd.trees m) =
      true)
    (hMask : maskPlanB A (D.N.sent m 0) (recPlanOf D D.sd) (D.N.msgsAt ps[k]?) m = true)
    (hCells : arraysPlanB A par.hp.tl (D.N.sent m 0) (recPlanOf D D.sd) (D.N.msgsAt ps[k]?) m =
      true)
    (hell : nV ≤ maskEllP A)
    (hsits : SitsIn (sigListCalls A.D A.rad A.link) A.seatT D.ms D.N m)
    (hcov : Covers par.hp.tl nM nRr nC)
    (hns : ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∀ G, (behindOf seatS q a τ o G').1.fork? = some G → G.ns ≤ nV)
    (hSt : ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' →
      StatedIs D.St (uLay par.hp.tl fun _ B => matsOfB A par.hp.tl B)
        (behindOf seatS q a τ o G').1) :
    ∀ b w, keptFrom (tableOn0 D.N Mg Z links ps k) par q b →
      onQ D.N Mg links ps (fun s => (Z, s)) (k + 1) b → b.1.failed = none →
      meansQ (Fr := Fr) D.N Mg (fun s => (Z, s)) (.formsT m 3 "own") b w →
      FormsT seatS
        (((A.seatN nV D.N par.hp.tl y nM nRr nC n0 ns nx v7).atRecF X par).toPlan4K.semOf
          (partOf A.D.codes D.arr D.ms D.N m) par.hp.tl) (frontRun par) formsBack b.1 w := by
  have hrec : ∀ a τ fo o G', onQ D.N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G' → ∀ A', K9.segAt? (behindOf seatS q a τ o G').1 = some A' →
      RecIs A' (recPlanOf D D.sd) (D.N.msgsAt ps[k]?) m := by
    intro a τ fo o G' ha hu Y A' hA'
    obtain ⟨_, _, As, _, _, _⟩ := asks a τ fo o G' ha hu Y
    exact recIs_run E hO ha hu Y As.sized hA'
  refine forms_of_means _ _ (fun _ B => matsOfB A par.hp.tl B) E hRd hruns hk asks ?_ ?_ ?_ ?_
  · intro a τ fo o G' ha hu Y
    obtain ⟨_, a', _, _, _, _, _, _, _, ha', _⟩ := kept_open (kept_of_yes Y)
    obtain ⟨A', hA', _, _⟩ := segAt_lay ha'
    rw [readsArray_plan (hrec a τ fo o G' ha hu Y A' hA') par.hp ha' hA']
    exact hArr
  · intro a τ fo o G' ha hu Y w A' o' c hA' ho' hc h2
    obtain ⟨_, a', _, o₁, _, _, _, _, _, ha', _, eo, ho₁, _⟩ := kept_open (kept_of_yes Y)
    obtain ⟨A'', hA'', _, eAL⟩ := segAt_lay ha'
    obtain rfl : A'' = A' := Option.some.inj (hA''.symm.trans hA')
    obtain rfl : o₁ = o' := Option.some.inj (ho₁.symm.trans ho')
    exact statedAt_of_is (hSt a τ fo o G' ha hu Y) ha' eo (by rw [← eAL]; exact hc) h2 _ _
  · intro a τ fo o G' ha hu Y w A' G hA' hG j hj
    show A.maskN nV (partOf A.D.codes D.arr D.ms D.N m w) j = _
    rw [← hcs]
    exact mask_pins A D.arr D.ms D.N m hsits hMask (hrec a τ fo o G' ha hu Y A' hA') hell w
      (Nat.lt_of_lt_of_le hj (hns a τ fo o G' ha hu Y G hG))
  · intro a τ fo o G' ha hu Y w A' hA' x r c _ _ _
    rw [mats_rawF A nV D.N par.hp.tl y nM nRr nC n0 ns nx v7 hcov X par, ← hcs,
      raw_pins A D.arr D.ms D.N m hsits par.hp.tl hCells (hrec a τ fo o G' ha hu Y A' hA') w]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.forms_pinsF
