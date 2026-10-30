--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/More/KeptAtStates.lean: WHAT AN ACCEPT OF K4's SUB-PROTOCOL KEEPS AND MAKES OF THE
PUBLIC TESTS, AT TWO STATES OF THE VERIFIER: no meaning, no piece, no promise. Each statement has
the form: K : KeptAtS par s s' (Johnson/Road/K4/KeptAtS.lean), tests at the state in front s by
their own names, tests and equations on the public data, give one public item's own test at the
state behind s'. For the debt MadeOwed of K4's authors at K4's
places.

  THE FRONT: `kept_of_decide`, `kept_of_stepYes`, `kept_of_step`: an accept of the sub-protocol that
    is seated at K4's place gives KeptAtS at the lot's member's parameters.
  KEPT: `lookOut_at` (lookOut m 2) · `objects_at` (formsInT m 2 "objects"). (The three items that
    read the ledger are another house's to join: their cores at states stand as ledgerB_kept,
    freeAboveB_kept in Johnson/Road/K4/K4KeepKeeper.lean, treesAreB_kept in
    Riders/KeepsOfMeans.lean.)
  MADE: `lookIn_at` (lookIn m 7) · `hasRow_at` (hasRow m).
No new argument: the cores are k3OnOutAt_kept (Riders/KeepsOfMeans.lean) · objects_forward,
guests_in (Riders/Objects.lean), walked as in hObj_of_means (Riders/ObjectsAtMeans.lean) ·
lookIn_made_B (Riders/LookInPlanB.lean) · hasRow_of_plan (Total/RowOfPlan.lean) · roomFor_of_leftIs
(Riders/MoreFront.lean) · k4_yes (Johnson/IMR/K4Seat.lean) · kept_atS.
Limits. Every test in front is a premise. K04_law, the law of K4's sub-protocol itself, IS NOT
PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.FunsThirdReached
import Johnson.Road.K4.Riders.KeepsOfMeans
import Johnson.Road.K4.Riders.ObjAsksOfMeans
import Johnson.Road.K4.Riders.InRowAtMeans
import Johnson.Road.K4.Riders.LookInPlanB

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.More
open Iop OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Flat OnBytes.Maker
open OnBytes.Model.Layer (Pub HPlan2 Own)
open OnBytes.Params (LinShape)
open VerifiableInference.Desc.Sound (step_ok_iff)
open OnBytes.PscRun (Filled Later)
open OnBytes.Desc.First.K4 (Par Rest)
open OnBytes.Desc.First.K4.Riders (ObjRun GuestRun reader_objects reader_guests objects_forward
  guests_in hne_of_bare rowsOwn_of_hne)
open OnBytes.Desc.First.K4.Total (rowB roomFor hasRow_of_plan)
open OnBytes.Desc.First.K4.Slots (hear_trees)
open OnBytes.Road.K4.Riders (k3OnOutAt_kept link_forms sized_of_ledgerB
  free_of_freeAboveB next_le_sFv lookInPlanB lookIn_made_B link_of_shape roomFor_of_leftIs)
open VerifiableInference.Desc (Block Place Claim Link K9.readerOf K9.readersOfLink K9.statesOfLink
  K9.LinkHoles K9.formsInT K9.mergeOf)
open VerifiableInference.Desc.First (S LayOwn ModelPart ledgerB freeAboveB shapeAt)
open VerifiableInference.Desc.First.FillK4 (look_agrees lookLayB callerInLayB)
open VerifiableInference.Desc.First.FillBare (rowsBareB)
open VerifiableInference.Desc.First.Look (Sent placeAt k3LookInAt k3OnOutAt)
open VerifiableInference.OnPublicFiles (linkFreshB)
open Johnson.Desc.First.Walk.Tied (StepYes stepYes_decide roomIsB rowsBefore)
open Johnson.Desc.First.Walk.Law (hasRow)

/-! ## The front -/

/-- An accept of the seated sub-protocol at K4's place gives KeptAtS. -/
theorem kept_of_decide {b : Block S ProofFile.Cl} {x : Bool × Par} {name : String} {g : ℕ}
    (h : IM.LaidAlone ProofFile.sameReply b (ProofFile.k4Block x) name (k4PlaceAt g)) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} (hd : b.decide s rs gs = .ok s') :
    KeptAtS (parOf x) s s' :=
  kept_atS ((IM.k4_yes h s s' rs gs).1 hd).1

/-- The same of an accepting step. -/
theorem kept_of_stepYes {b : Block S ProofFile.Cl} {x : Bool × Par} {name : String} {g : ℕ}
    (h : IM.LaidAlone ProofFile.sameReply b (ProofFile.k4Block x) name (k4PlaceAt g)) {ft : ℕ} {s s' : S}
    (hy : StepYes ft b s s') : KeptAtS (parOf x) s s' := by
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  exact kept_of_decide h hd

/-- The same of a step that returns, whatever it reads. -/
theorem kept_of_step {b : Block S ProofFile.Cl} {x : Bool × Par} {name : String} {g : ℕ}
    (h : IM.LaidAlone ProofFile.sameReply b (ProofFile.k4Block x) name (k4PlaceAt g)) {ft : ℕ} {s s' : S}
    (hy : ∃ rs cols n, b.step ft s rs cols = .ok (s', n)) : KeptAtS (parOf x) s s' := by
  obtain ⟨rs, cols, n, e⟩ := hy
  exact kept_of_decide h ((step_ok_iff ft b s s' rs cols n).1 e).2.2.2

variable {par : Par} {s s' : S}

/-! ## Kept -/

theorem lookOut_at (K : KeptAtS par s s') {X3 : Verify.Public} {i : ℕ} {dg : Bool}
    (h : k3OnOutAt X3 i dg s = true) : k3OnOutAt X3 i dg s' = true :=
  k3OnOutAt_kept K h

/-- **formsInT m 2 "objects" rides past an accept of K4's.** -/
theorem objects_at (K : KeptAtS par s s') {Hh : K9.LinkHoles} {l : Link S Claim} {nO nG : String}
    {runO runG : ℕ → S → Except String (List Claim × S)}
    (fO : (K9.statesOfLink l 1).find? (fun r => r.1 == "objects") = some (nO, runO))
    (oRun : ObjRun runO)
    (fG : (K9.statesOfLink l 1).find? (fun r => r.1 == "guests") = some (nG, runG))
    (gRun : GuestRun runG) {n : ℕ} {sent : List (ℕ × ℕ)} (hlook : lookLayB s = true)
    (hbare : rowsBareB s = true)
    (hl : ledgerB s = true) (hfa : freeAboveB n s = true)
    (hin : K9.formsInT (K9.readersOfLink Hh l) sent 1 "objects" s = true) :
    ([(1, "objects"), (1, "guests")].all fun p =>
      K9.formsInT (K9.readersOfLink Hh l) sent p.1 p.2 s') = true := by
  obtain ⟨al, fo', o', G', hal, hfo, hfork, hLat, hown, _, _, _, hR, _, _, t, u, hh0⟩ := K
  have hh : al.lookHeard = some fo' := (look_agrees hlook hal).symm.trans hfo
  have hb : (fo'.rows.all fun f => f.ents.isEmpty) = true := by
    unfold rowsBareB at hbare
    rw [hal] at hbare
    simp only [hh, Option.any_some] at hbare
    simpa [Array.all_eq_true_iff_forall_mem, List.all_eq_true] using hbare
  have hne := hne_of_bare hb
  have hS : PscRun.Sized al.F := sized_of_ledgerB hal hl
  obtain ⟨al', hal', _, _, _, hlh⟩ := hR.here al hal
  have hown' : al'.own = some o' := by
    have e : s'.own? = al'.own := by simp only [S.own?, hal']
    rw [← e]
    exact hown
  have hmg : K9.mergeOf s' = some o'.wo.sFv := by
    simp only [K9.mergeOf, hal', hown', Option.map_some]
  have rO : K9.readerOf (K9.statesOfLink l) 1 "objects" s =
      some { forms := fo'.rows.toList, late := [] } := by
    rw [reader_objects fO oRun hal hh, if_pos (rowsOwn_of_hne al.F hne)]
  have rO' : K9.readerOf (K9.statesOfLink l) 1 "objects" s' =
      some { forms := fo'.rows.toList, late := [] } := by
    rw [reader_objects fO oRun hal' (hlh.trans hh), if_pos (rowsOwn_of_hne al'.F hne)]
  have hf := objects_forward hal hR hfork hLat (hear_trees hS hh0) fO oRun hh hmg
    (next_le_sFv hS hh0) hS (free_of_freeAboveB hal hS hfa) (link_forms (Hh := Hh) (by decide) rO)
    (link_forms (Hh := Hh) (by decide) rO') hin
  show (K9.formsInT (K9.readersOfLink Hh l) sent 1 "objects" s' &&
    (K9.formsInT (K9.readersOfLink Hh l) sent 1 "guests" s' && true)) = true
  rw [hf, guests_in hal' fG gRun (link_forms (by decide) (reader_guests fG gRun hal'))]
  rfl

/-! ## Made -/

/-- **lookIn m 7 is made.** -/
theorem lookIn_at (K : KeptAtS par s s') {X3 : Verify.Public} {D3 : Sent} {m n ns : ℕ}
    (hB : lookInPlanB par X3 m n ns = true) (hl : ledgerB s = true)
    (hfa : freeAboveB ns s = true) (hfresh : linkFreshB (D3.arrayOf.getD m #[]) s = true)
    (hcall : callerInLayB n s = true) {links : List ModelPart} {ps : List Place} {k : ℕ} {pl : Place}
    (H : AtK4 links ps k m pl) (hs : shapeAt links (some pl) s = true)
    (hpl : ∀ p, placeAt X3 m true = some p → p.link = m) : k3LookInAt X3 D3 m true s' = true :=
  lookIn_made_B K hB hl hfa hfresh hcall
    fun p hp Lk hLk => (link_of_shape H hs hLk).trans (hpl p hp).symm

/-- **hasRow m is made.** -/
theorem hasRow_at (K : KeptAtS par s s') {lin : LinShape} {free0 m : ℕ} {fvs : List Bool}
    (hB : rowB par.P par.g par.hp.NCL lin = true) (h1 : 1 ≤ free0 - rowsBefore fvs m)
    (hroom : roomIsB free0 fvs m s = true) : hasRow par.P.wsLay par.hp.NCL lin s' = true :=
  hasRow_of_plan K hB h1 (roomFor_of_leftIs hroom)

end OnBytes.Road.K4.More

#print axioms OnBytes.Road.K4.More.kept_of_stepYes
#print axioms OnBytes.Road.K4.More.kept_of_step
#print axioms OnBytes.Road.K4.More.lookOut_at
#print axioms OnBytes.Road.K4.More.objects_at
#print axioms OnBytes.Road.K4.More.lookIn_at
#print axioms OnBytes.Road.K4.More.hasRow_at
