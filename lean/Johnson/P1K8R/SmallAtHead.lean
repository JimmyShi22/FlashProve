-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/SmallAtHead.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: A
PAYMENT BENEATH THE KIND'S FROZEN CONDITION: THE FIELD `small` OF `K8LeftT`, TO THE LETTER, FROM THE
HEAD, THE FACTS ALONG "REACHED" (`FoldFacts`), AND CLOSED SENTENCES ON PUBLIC DATA ALONE. NO
SOUNDNESS.

  `drawPlaceB`, `draw_place_full`: at the draw's number of each of the 25 links the written list of
    places has a place of that link, early enough for `FoldFacts.frameIs`, at which two moments are
    sent: by the kernel.
  `SmallPlan`: THE CLOSED SENTENCES AT LINK l, all on public data: `names` (the built link's list
    names the array of each matrix's label at the plan's number of that matrix's array); `lawful`
    (the programs' own test on the layout); `mats` (`MatPlan` at each matrix's array, with two
    moments sent).
  `smallOwes_of_plan`: `SmallOwes` from `FoldFacts` and `SmallPlan`.
  `small_of_plan`: **under the head: `FoldFacts` along a condition that gives `RchAt`, and
    `SmallPlan`, give `K8LeftT`'s field `small`, to the letter**: no premise is left that reads a
    state or a witness but `FoldFacts`, which is a field of the head with the facts on every reached
    state (`P5J.AtMgR.fold`).
Limits. `SmallPlan` is shown nowhere here and has run nowhere. AT `OnBytes.secondHashFunction` ALONE. Nothing on
soundness.

-/
import Johnson.P1K8R.MatAtFold
import Johnson.P1K8R.FoldAtDraw
import Johnson.P5J.FoldAt

set_option autoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open Iop
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain Place Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart FoldFacts momentAt shiftAt flatPlacesOf)
open VerifiableInference.Desc.First.K8
open Johnson.Desc.First.Walk.Tied (RchAt)
open Desc.K14.Law (secondAt seatZ)
open ProofFile (Cl)
open P5J (AtMgA mgAtAll)

/-- The test at link l: the place at the draw's number. -/
def drawPlaceB (links : List ModelPart) (ps : List Place) (l : ℕ) : Bool :=
  match ps[drawAt l]? with
  | some p => decide (p.link = some l) && decide (p.piece ≤ 11 + 2 * shiftAt links l) &&
      decide (momentAt (shiftAt links l) p.piece = 2)
  | none => false

theorem drawPlaceB_full :
    ((List.range 25).all fun l => drawPlaceB linksFull (flatPlacesOf linksFull true) l) = true := by
  decide +kernel

/-- **THE PLACE AT THE DRAW's NUMBER**, at the full size. -/
theorem draw_place_full (l : ℕ) (hl : l ≤ 24) :
    ∃ p, (flatPlacesOf linksFull true)[drawAt l]? = some p ∧ p.link = some l ∧
      p.piece ≤ 11 + 2 * shiftAt linksFull l ∧ momentAt (shiftAt linksFull l) p.piece = 2 := by
  have h := List.all_eq_true.1 drawPlaceB_full l (List.mem_range.2 (Nat.lt_succ_of_le hl))
  unfold drawPlaceB at h
  split at h
  · rename_i p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨p, hp, h.1.1, h.1.2, h.2⟩
  · cases h

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **THE CLOSED SENTENCES AT LINK l**: on public data alone. -/
structure SmallPlan (Zp : ProofFile.Pub) (cF : Chain S Cl) (L₀ : VerifiableInference.Desc.K12.Door.Laid)
    (l : ℕ) (Xl : LinkH) : Prop where
  names : ∀ μ, μ < (Meaning.tlAt (P5J.At.X Zp) l).NM →
    Xl.arrayOf[(Meaning.tlAt (P5J.At.X Zp) l).gtTree.getD μ 0]? =
      some (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) l μ),
        Meaning.nameOf (Meaning.ownerA (Meaning.labAt (P5J.At.X Zp) l μ)))
  lawful : reqLayoutOk (P5J.At.cs Zp) (P5J.At.shape Zp) (P5J.At.layout Zp) = true
  mats : ∀ μ, μ < (Meaning.tlAt (P5J.At.X Zp) l).NM → ∀ A,
    VerifiableInference.Desc.arrayOf (P5J.At.layout Zp)
      (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) l μ))
      (Meaning.nameOf (Meaning.ownerA (Meaning.labAt (P5J.At.X Zp) l μ))) = some A →
    MatPlan (P5J.At.foldD Zp cF L₀) ((P5J.At.N Zp cF).group l) (P5J.At.arr Zp) (P5J.At.num Zp) l 2
      ((P5J.At.N Zp cF).msgsAt (flatPlacesOf linksFull true)[drawAt l]?)
      (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) l μ)) A

/-- `SmallOwes` from the facts along "reached" and the closed sentences. -/
theorem smallOwes_of_plan (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {Fr : Frame}
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24)
    {Xl : LinkH} {Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop}
    {L₀ : VerifiableInference.Desc.K12.Door.Laid}
    (FF : FoldFacts Rch (fun a => a.1) (P5J.At.foldD Zp cF L₀) P5J.At.reqW P5J.At.links P5J.At.ps)
    (T : SmallPlan Zp cF L₀ l Xl) : SmallOwes h G l Xl Rch where
  names := T.names
  layout := layout_at hG
  mats := by
    intro z a L ha hr hm hL μ hμ A hA
    obtain ⟨p, hp, hlk, hpc, hmo⟩ := draw_place_full l hl
    have hB := bookAt_of_onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
      (fun s => (z, s)) (drawAt l) a ha hm
    have T1 := T.mats μ hμ A hA
    rw [← hmo] at T1
    exact matAt_of_fold (Zp := Zp) (cF := cF) FF (k := drawAt l) (a := ((z, a.1), a.2)) (p := p)
      (l := l) hr hm hp hlk hpc hL hB T.lawful
      (name := Meaning.nameOf (Meaning.ownerA (Meaning.labAt (P5J.At.X Zp) l μ)))
      ((Meaning.reqArray_eq_arrayOf _ _ _).trans hA) T1

/-- **THE FIELD `small` OF `K8LeftT`, TO THE LETTER, FROM THE HEAD, `FoldFacts` AND CLOSED
SENTENCES.** -/
theorem small_of_plan (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {Fr : Frame} {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24) {Xl : LinkH}
    (e3 : G.built[l]? = some Xl) {Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop}
    (hRch : ∀ k a, Rch k a → RchAt (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a)
    {L₀ : VerifiableInference.Desc.K12.Door.Laid}
    (FF : FoldFacts Rch (fun a => a.1) (P5J.At.foldD Zp cF L₀) P5J.At.reqW P5J.At.links P5J.At.ps)
    (T : SmallPlan Zp cF L₀ l Xl) :
    ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str) w,
      onQ (P5J.At.N Zp cF) (mgAtAll h) linksFull (flatPlacesOf linksFull true)
        (fun s => (z, s)) (drawAt l) a →
      Rch (drawAt l) ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none →
      TieAt (cellsAt (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF) l
        (z, a.1)) a.1 w →
      (mgAtAll h).constr l .small (z, a.1) (strsOf Fr a.2) w :=
  small_of_owes h hG hl e3 hRch (k08_fold_field h hG hl e3 hRch) (smallOwes_of_plan h hG hl FF T)

end

end P1K8T

#print axioms P1K8T.draw_place_full
#print axioms P1K8T.smallOwes_of_plan
#print axioms P1K8T.small_of_plan
