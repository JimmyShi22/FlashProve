-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/GrownStart.lean: THE TABLE OF JOINTS' PROMISE AT THE PROOF FILE, THE HALF THAT READS THE
VERIFIER's STATE ALONE: (S0): X 0 AT THE PROOF FILE's OWN FIRST STATE, IF IT BEARS NO MARK: THE
TABLE's FOUR FIXED TESTS PAID; THE PLAN's TWO COUNTS AT THE FRONT AND
THE FURTHER TESTS E ARE PREMISES. AT EVERY o; NO PREMISE ON SCOPE.
THE BRICKS ARE CALLED: Johnson/Desc/First/BordersStart.lean (rowsHeld_start · membersHeld_start · shapeAt_start · bookAt_start · IsStart · isStart_if · blank_marked · openSets_head) · Johnson/Desc/ProofFile/Law/PureMade.lean's pubBy_start (the first state in a public part is the value of the function that was passed in for it).


  start_isStart     ProofFile.startS Z p is a first state in BordersStart.lean's sense: the bare start with the request's words laid, or the marked blank.
  bk_start          at a first state without a mark, at a list of places that begins with the front's: BK N links ps 0 s = true, from N.treesAt | N.msgsAt = 0 at the front's place.
  s0_of_open        (S0) at an opening's own letters: (ProofFile.startS Z p).failed = none → XK N links (c.blocksInOrder.map (·.place)) E 0 (ProofFile.startS Z p) = true.
  x_reached         IN SCOPE, THE WHOLE ROAD: the ten shares (seated form) · the two counts at the front · E 0 at the first state ⟹ X k at every state that the fold over the first k sub-protocols reaches from ProofFile.startS Z p without a mark.

What is not claimed. The shares; hT | hM; hE. No soundness.
-/
import Johnson.IMR.GrownSeated
import Johnson.IMR.HandsFold
import Johnson.Desc.First.BordersStart
import Johnson.Desc.ProofFile.Law.PureMade

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

variable {o : ProofFile.SecondHashFunctionArgument}

open VerifiableInference.Desc (Block Chain FileDescription Place KindName foldBlocks OpenedColumn)
open VerifiableInference.Desc.First (S ModelPart Numbers IsStart frontPlace start)
open ProofFile (Cl)

/-- At a first state without a mark the table's four fixed tests accept at border 0. -/
theorem bk_start {N : Numbers} {links : List ModelPart} {ps : List Place} {codes : OnBytes.Codes}
    {req : Array UInt32} {s : S} (hp : ps[0]? = some frontPlace) (hs : IsStart codes req s)
    (hu : s.failed = none) (hT : N.treesAt (some frontPlace) = 0)
    (hM : N.msgsAt (some frontPlace) = 0) : BK N links ps 0 s = true := by
  rcases hs with ⟨c, rfl⟩ | rfl
  · have hO : openAt links ps 0 = start links :=
      VerifiableInference.Desc.First.openSets_head links ps (start links)
    unfold BK
    rw [hO, hp, VerifiableInference.Desc.First.shapeAt_start,
      VerifiableInference.Desc.First.rowsHeld_start, VerifiableInference.Desc.First.membersHeld_start,
      VerifiableInference.Desc.First.bookAt_start N codes c req hT hM]
    rfl
  · exact absurd hu VerifiableInference.Desc.First.blank_marked

section
variable {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The proof file's own first state is a first state in the table's sense. -/
theorem start_isStart (O : Open o pol lay KL F Z Bs base c A B) (p : ProofFile.InstPub) :
    IsStart Z.first.codes (OnBytes.Model.Verify.words32 p.request) (ProofFile.startS Z p) := by
  have h0 : S.start? (VerifiableInference.Desc.First.parP Z.first) Z.first.codes Z.first.shape
      Z.first.layout = some Z.s₀ := ProofFile.Law.pubBy_start (st := ProofFile.plainStarts) O.pub
  exact VerifiableInference.Desc.First.isStart_if h0 _ _ _

/-- **(S0)**, at an opening's own letters: at every o; no premise on scope. -/
theorem s0_of_open (O : Open o pol lay KL F Z Bs base c A B) {N : Numbers} {links : List ModelPart}
    {E : ℕ → S → Bool} (p : ProofFile.InstPub) (hT : N.treesAt (some frontPlace) = 0)
    (hM : N.msgsAt (some frontPlace) = 0)
    (hE : (ProofFile.startS Z p).failed = none → E 0 (ProofFile.startS Z p) = true) :
    (ProofFile.startS Z p).failed = none →
      XK N links (c.blocksInOrder.map (·.place)) E 0 (ProofFile.startS Z p) = true := by
  intro hu
  obtain ⟨b, e0, -, -, hpl, -⟩ := front_of O
  have hp : (c.blocksInOrder.map (·.place))[0]? = some frontPlace := by
    rw [List.getElem?_map, e0]
    exact congrArg some hpl
  unfold XK
  rw [bk_start hp (start_isStart O p) hu hT hM, hE hu]
  rfl

end

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **IN SCOPE, THE WHOLE ROAD: X k AT EVERY STATE THAT THE FOLD REACHES FROM THE PROOF FILE's OWN FIRST STATE WITHOUT A MARK.** -/
theorem x_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {N : Numbers} {E : ℕ → S → Bool}
    {ft : ℕ} (Sh : SharesS N E ft Z Bs.G₀ c) (p : ProofFile.InstPub)
    (hT : N.treesAt (some frontPlace) = 0) (hM : N.msgsAt (some frontPlace) = 0)
    (hE : (ProofFile.startS Z p).failed = none → E 0 (ProofFile.startS Z p) = true) {k : ℕ} (hk : k ≤ 358)
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {out : S × List Fmt.RoundView × List OpenedColumn}
    (hf : foldBlocks ft (c.blocksInOrder.take k) (ProofFile.startS Z p) rs cols = .ok out)
    (hu : out.1.failed = none) : XK N linksW placesW E k out.1 = true := by
  have hlen : c.blocksInOrder.length = 358 := by
    rw [← List.length_map (f := (·.place)), places_scope hS hR O, places_len]
  have h := x_at_cut (s1_of_seated hS hR O Sh) (s0_of_open O p hT hM hE) (hlen ▸ hk) hf hu
  rwa [places_scope hS hR O] at h

end

end IM

#print axioms IM.bk_start
#print axioms IM.start_isStart
#print axioms IM.s0_of_open
#print axioms IM.x_reached
