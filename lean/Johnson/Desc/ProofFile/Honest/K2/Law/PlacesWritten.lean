-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/PlacesWritten.lean: the kind "the code switch" (K2): UNDER THE
HEAD `P5J.AtMg` AND THE OPENING IN ITS LETTERS, THE KIND's PLACES WITH THEIR PUBLIC DATA
(`switchPlaces`, Honest/K2/Half.lean), THE SEGMENTS' PUBLIC DATA (`segmentsOf`,
Honest/K2/AtPlan.lean) AND THE COUNT OF ORACLE MESSAGES STATED IN FRONT OF A BORDER (`treesTo`,
Honest/Thread/Thr.lean) ARE CLOSED TERMS. So a public test on them can be put to Lean's kernel once,
at the written plan. Definitions with code; statements with their proofs: unfoldings, list laws and
calls. Nothing is evaluated here.

  `placesAt`, `segsAt` THE BODIES OF `switchPlaces` AND `segmentsOf` A SECOND TIME, as functions of
                    what they read of the public part and the ground: what `prepOf` returns · what
                    `spotsOf` returns at the table of stretches · the numbers of the rounds "FOLD
                    round"
  `switchPlaces_is`, `segmentsOf_is` THE TIES, WITH NO HYPOTHESIS AT ALL: at every Z and G each
                    first text is the second at what the look-ups return there
  `entryNumbers`, `roundNumbers_entries` the numbers of the rounds of a name hang on the declared
                    rounds' entries alone
  `treesTo_told` the frame's count `treesTo` is the library's `treesTold` at what the sub-protocols
                    tell
  `placesW`, `segsW` THE CLOSED TERMS: at `IM.prepW`, `spotsWritten` and `P5T.esFull.1`
  `prep_at_head`, `spots_at_head`, `entries_at_head` the three letters under the head and the
                    opening
  `places_at_head`, `segments_at_head`, `treesTo_at_head` THE TOPS: `switchPlaces Zp Bs.G₀ =
                    placesW` · `segmentsOf Zp Bs.G₀ = segsW` · `treesTo cF.blocksInOrder b = treesTold
                    toldFull b`, at every b

By, the library's: `prep_pinned`, `prepW` (Johnson/IMR/SendsPinned.lean) · `plans_front`
(Johnson/Desc/First/Att/Row/K5FrontE0.lean), `cuts_of_plans`, `entries_of_plans`
(Johnson/Desc/First/Att/Row/K5FrontOne.lean: they ask `ProofFile.pubBy …`, which the opening's
`pureRoad.pub …` is by unfolding) · `spots_written`, `spotsWritten`
(Johnson/AtFull/Desc/SpotsWritten.lean) · `toldOf_of_cut`, `toldFull`
(Johnson/Top/H0/K2Ties/ToldAt.lean), `treesTold` (Johnson/Desc/First/BookFit.lean). Ours:
`tests_at_head` (Johnson/Desc/K2/Honest/Returns/UnderHead.lean). THE PATTERN:
Johnson/Desc/K1/Law/SitsSwitch.lean, which pins the lot's numbers to `IM.prepW` by the same law and
tests them there.

Limits. `placesAt` AND `segsAt` ARE SECOND TEXTS, OF PUBLIC DATA, WRITTEN SO THAT LEAN's KERNEL CAN
EVALUATE THEM AT CLOSED LETTERS: the two ties, not the eye, hold them to the first; whoever speaks
of the kind's places or segments goes on speaking of `switchPlaces` and `segmentsOf`. THE HEAD IS
SHOWN MET BY NOBODY HERE. The full size alone; the format's second hash function alone. No test is run here:
that the closed terms are what anybody wants is not said. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.AtPlan
import Johnson.Desc.ProofFile.Honest.Thread.Thr
import Johnson.Desc.K2.Honest.Returns.UnderHead
import Johnson.Desc.First.Att.Row.K5FrontOne
import Johnson.AtFull.Desc.SpotsWritten
import Johnson.Top.H0.K2Ties.ToldAt
import Johnson.IMR.SendsPinned

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S treesTold)
open VerifiableInference.Desc.First.K2Ties (toldFull toldOf_of_cut)
open VerifiableInference.Desc.K2.Honest.Returns (tests_at_head)
open Johnson.AtFull.Desc (spotsWritten spots_written)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- **The body of `switchPlaces`**, at what `prepOf` and `spotsOf` return. -/
def placesAt (P? : Option P1K2.Prep) (sps? : Option (List Spot)) : List SwitchPlace :=
  match P?, sps? with
  | some P, some sps =>
    let f₀ : OnBytes.ReqFrame := { shape := P.z.request, groups := OnBytes.reqGroups P.z.request }
    (sps.filter fun sp => sp.place.kind == .K2).map fun sp =>
      let l := sp.place.link.getD P.z.request.link.length
      let T := (f₀.groups.getD l {}).target
      { place := sp.place, link := l
        sizes := ⟨P.z.codes, P.z.request.code, P.z.request.maskCode, T.kept.toList.map (·.shape), T⟩
        others := OnBytes.ReqFrame.notices ({ f₀ with link := l }.atMoment 0) ++
          #[OnBytes.foldMaskNotice (f₀.foldShape l {})]
        foldVars := (f₀.groups.getD l {}).k
        front := frontOf P.z.codes f₀ sps l
        addrs := addrOf f₀ sps }
  | _, _ => []

/-- The first text is the second at these letters. -/
theorem switchPlaces_is (Z : Pub) (G : Ground) :
    switchPlaces Z G = placesAt (P1K2.prepOf Z G) (spotsOf Z.cuts) := by
  unfold switchPlaces placesAt
  cases P1K2.prepOf Z G <;> cases spotsOf Z.cuts <;> rfl

/-- **The body of `segmentsOf`**, at what `prepOf` returns and the numbers of the rounds
"FOLD round". -/
def segsAt (P? : Option P1K2.Prep) (fold : List Nat) : List SegmentPub :=
  match P? with
  | none => []
  | some P =>
    let f₀ : OnBytes.ReqFrame := { shape := P.z.request, groups := OnBytes.reqGroups P.z.request }
    let ks := P.z.request.link.zipIdx.map fun L => (f₀.groups.getD L.2 {}).k
    P.z.request.link.zipIdx.map fun L =>
      let j := L.2
      let T := (f₀.groups.getD j {}).target
      let own := ({ f₀ with link := j }.atMoment 0).length
      { sizes := ⟨P.z.codes, P.z.request.code, P.z.request.maskCode, T.kept.toList.map (·.shape), T⟩
        sent := (List.range (OnBytes.reqMoments L.1)).map fun m =>
          if j == 0 && m == 0 then (P1K2.noticesAt f₀ j m).extract 0 (own + 1)
          else P1K2.noticesAt f₀ j m
        ownKept := L.1.messages.map fun m => decide (0 < m.life)
        foldVars := ks.getD j 0
        gamma := (fold.drop ((ks.take j).foldl (· + ·) 0)).take (ks.getD j 0) }

/-- The first text is the second at these letters. -/
theorem segmentsOf_is (Z : Pub) (G : Ground) :
    segmentsOf Z G = segsAt (P1K2.prepOf Z G) (roundNumbers Z.D.1 "FOLD round") := by
  unfold segmentsOf segsAt
  cases P1K2.prepOf Z G <;> rfl

/-- The numbers, in a list of entries, of the entries of a name. -/
def entryNumbers (es : List Fmt.Entry) (name : String) : List Nat :=
  es.zipIdx.filterMap fun d => if d.1.name == name then some d.2 else none

/-- The numbers of the rounds of a name hang on the declared rounds' entries alone. -/
theorem roundNumbers_entries (D : List Fmt.DeclaredRound) (name : String) :
    roundNumbers D name = entryNumbers (D.map (·.entry)) name := by
  unfold roundNumbers entryNumbers
  rw [List.zipIdx_map, List.filterMap_map]
  rfl

/-- The frame's count is the library's, at what the sub-protocols tell. -/
theorem treesTo_told {St Cl : Type} (bs : List (Block St Cl)) (b : Nat) :
    treesTo bs b = treesTold (bs.map fun x => x.oracles.flatten) b := by
  unfold treesTo treesTold
  rw [List.length_flatMap, ← List.map_take, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun a _ => ?_)
  show (List.flatMap id a.oracles).length = a.oracles.flatten.length
  rw [List.flatMap_id]

/-- **The places, closed.** -/
def placesW : List SwitchPlace := placesAt IM.prepW (some spotsWritten)

/-- **The segments, closed.** -/
def segsW : List SegmentPub := segsAt IM.prepW (entryNumbers P5T.esFull.1 "FOLD round")

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

theorem prep_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    P1K2.prepOf Zp Bs.G₀ = IM.prepW :=
  IM.prep_pinned O.pub h.pins.1 O.blank

theorem spots_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    spotsOf Zp.cuts = some spotsWritten := by
  have h1 := H2K5.Row.plans_front h.scope O.pub (tests_at_head h O).1
  rw [H2K5.Row.cuts_of_plans (show ProofFile.pubBy (ProofFile.PlainG.madeOf OnBytes.secondHashFunction) ProofFile.plainStarts
    W.pol W.lay W.KL = .ok Zp from O.pub) h1]
  exact spots_written

theorem entries_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    Zp.D.1.map (·.entry) = P5T.esFull.1 :=
  H2K5.Row.entries_of_plans (show ProofFile.pubBy (ProofFile.PlainG.madeOf OnBytes.secondHashFunction) ProofFile.plainStarts
    W.pol W.lay W.KL = .ok Zp from O.pub) (H2K5.Row.plans_front h.scope O.pub (tests_at_head h O).1)

/-- **Under the head and the opening the kind's places are the closed list.** -/
theorem places_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    switchPlaces Zp Bs.G₀ = placesW := by
  rw [switchPlaces_is, prep_at_head h O, spots_at_head h O]
  rfl

/-- **And the segments.** -/
theorem segments_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    segmentsOf Zp Bs.G₀ = segsW := by
  rw [segmentsOf_is, prep_at_head h O, roundNumbers_entries, entries_at_head h O]
  rfl

/-- **And the count of oracle messages stated in front of a border.** -/
theorem treesTo_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) (b : Nat) :
    treesTo cF.blocksInOrder b = treesTold toldFull b := by
  rw [treesTo_told]
  exact congrArg (fun t => treesTold t b) (toldOf_of_cut (tests_at_head h O).2.1)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.placesAt
#print axioms ProofFile.Honest.K2.Law.switchPlaces_is
#print axioms ProofFile.Honest.K2.Law.segsAt
#print axioms ProofFile.Honest.K2.Law.segmentsOf_is
#print axioms ProofFile.Honest.K2.Law.entryNumbers
#print axioms ProofFile.Honest.K2.Law.roundNumbers_entries
#print axioms ProofFile.Honest.K2.Law.treesTo_told
#print axioms ProofFile.Honest.K2.Law.placesW
#print axioms ProofFile.Honest.K2.Law.segsW
#print axioms ProofFile.Honest.K2.Law.prep_at_head
#print axioms ProofFile.Honest.K2.Law.spots_at_head
#print axioms ProofFile.Honest.K2.Law.entries_at_head
#print axioms ProofFile.Honest.K2.Law.places_at_head
#print axioms ProofFile.Honest.K2.Law.segments_at_head
#print axioms ProofFile.Honest.K2.Law.treesTo_at_head
