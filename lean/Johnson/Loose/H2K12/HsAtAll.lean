-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.SpotsAtAll
import Johnson.Top.H0.K2Caller.StandsLow
import Johnson.Goal.Skeleton.PinsOfLaid
/-
Johnson/Loose/H2K12/HsAtAll.lean: Code switching (the kind K2) on the
proof file's first chain: THE NUMBERS OF THE PLACE WHOSE SWITCH OPENS GROUP 24 (`ProofFile.pAtK2 Zp 23`, Johnson/Desc/ProofFile/CarryAt.lean) STAND
IN THE OUTPUT HEAD's DRESS: UNDER THE HEAD OF THE COMPOSED MEANING's CONSTANT. Statements and proofs: calls alone; nothing is evaluated here.


(Where this and lean/THEOREM.md differ, the page holds.)
THE ROAD. `stands23` (Johnson/Top/H0/K2Caller/StandsLow.lean) has the end under the named test `spotsFitB` and "25
links". The test: `spots_atAll` (H2K12/SpotsAtAll.lean), under the head and "the first chain's division into sub-protocols is the
written one". "25 links": `links25_open`, here. The written division: out of the head's own field "laid", by a lemma of the
library's (`P5J.pins_of_laid`, Johnson/Goal/Skeleton/PinsOfLaid.lean), which stands only where the entry tests ask that row.
  `links25_open`: at an opening in scope whose test on the list of rounds accepts: the shape of a request in the first state's frame
    has 25 links: a place of the kind has numbers there (`P1K2.pAt_answers_low`), so what the numbers are made of is made, and holds
    the planner's own sizes (`prep_is`), whose request has 25 links (`pub_links`, Johnson/Top/H0/Opts/PlannerRequestHas25Links.lean).
  `hs_of_cut`: the end under the head and the written division as a named premise.
  `hs_atAll`: the end under the head alone: the statement of a row in other files, to the letter.
What it is not. THE WRITTEN DIVISION RESTS ON PRINTS OF LEAN's EVALUATOR; the entry test compares it at a run. NO EXAMPLE BY A THEOREM OF THIS FILE
of the head. It says nothing on what the switch does. No soundness is claimed. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2Caller (spot_is stands23 pub_links)

/-- **25 links in the first state's frame's shape of a request.** -/
theorem links25_open {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) (hp : F.planOk = true) :
    Z.s₀.check.frame.shape.link.length = 25 := by
  have hs := P1K2.pAt_answers_low hS hR O hp 0 (by omega)
  unfold ProofFile.pAtK2? at hs
  cases hf : (ProofFile.k2SpotsAt Z).find? (fun x => x.2.grp == 0 + 1) with
  | none =>
    rw [hf] at hs
    cases hs
  | some y =>
    have hy := List.mem_of_find?_eq_some hf
    unfold ProofFile.k2SpotsAt at hy
    rw [O.blank] at hy
    have hy' : y ∈ P1K2.pureSpots Z Bs.G₀ := hy
    obtain ⟨Q, n, hQ, _, _⟩ := spot_is hy'
    obtain ⟨ez, es⟩ := prep_is hQ
    rw [es, ez]
    exact pub_links hS O.pub

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The end, under the head and the written division into sub-protocols.** -/
theorem hs_of_cut (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = VerifiableInference.PlanWritten.cutFirstFull) :
    (ProofFile.pAtK2 Zp 23).stands = .head := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact stands23 h.scope h.reads O h.laid.planOk (spots_atAll h hc)
    (links25_open h.scope h.reads O h.laid.planOk)

/-- **At the switch at the output head's segment the numbers stand in the head's dress: under the head alone.** -/
theorem hs_atAll (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : (ProofFile.pAtK2 Zp 23).stands = .head :=
  hs_of_cut h (P5J.pins_of_laid h.scope h.laid).2

end

end H2K12

#print axioms H2K12.links25_open
#print axioms H2K12.hs_of_cut
#print axioms H2K12.hs_atAll
