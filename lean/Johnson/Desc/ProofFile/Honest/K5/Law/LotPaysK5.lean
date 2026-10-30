-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/LotPaysK5.lean: conditional: under the library's head, at the book of the prover that
the maker "onlineProverFromPublicFiles" returns at any filling: the lot of the attention segments' own rounds (kind K5: the label of that
sub-protocol in the description) pays for itself in the sense of "LotPays" (ReadyOfLots.lean). And so, as a test that the
general law bites: at a filling whose one lot it is, "ready" returns. Two theorems; no definition; nothing is evaluated.

  lotPays_k5          h, hA ⊢ LotPays at the head's description, A's book, the head's public part, A's ground and the lot
  ready_of_lots_k5    IT IS NOT THE HONEST PROVER: TEN OF THE ELEVEN KINDS SEND NOTHING: the end of ready_at_k5Lot
                      (ReadyAtK5Lot.lean), to its letters, by ready_of_lots at the list of that one lot

By. k5LotK_places_once (LotClean.lean); k5Lot_place_at_head, k5_member_steps (ReadyAtK5Lot.lean); k5_member
(Member.lean); k5LotK_find_K3 (LotFind.lean): a side of the lot stands at the kind's place of a group below 12; the member
there is the kind's; the side is the one that the lot's own list has first at that place, since no two stand at one place.
The steps are those inside ready_at_k5Lot's proof, with the list of sides a letter.

Limits. The head and hA are premises. All limits of ReadyAtK5Lot.lean and ReadyOfLots.lean hold: never under a law over
coins, never as "the prover", never as a ground that anything is simulated.
No property of the protocol is claimed: nothing on soundness, completeness or what anything reveals.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.ReadyOfLots
import Johnson.Desc.ProofFile.Honest.K5.Law.ReadyAtK5Lot

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block FileDescription Place Chain)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **K5's lot pays for itself, at the maker's book.** Conditional: h; hA, at any filling. -/
theorem lotPays_k5 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {W₀ Rc X₀ X : Type}
    {P : OnlineProverParts W₀ Rc Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    LotPays (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.B Zp A.G
      (k5LotK (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) id keyOfK3) := by
  obtain ⟨e1, eG, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := by
    rw [← eZ]
    exact eG
  have hp : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).placesOk = true :=
    Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk
  have hn : ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.map (·.place)).Nodup :=
    (List.nodup_append.1 (List.nodup_append.1 (orderOf_nodup hp)).1).1
  have once := k5LotK_places_once (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) id keyOfK3 Zp A.G
  refine ⟨once, fun q hq b hb hbq hs hf w k => ?_⟩
  obtain ⟨j, hj, ej⟩ := k5Lot_place_at_head h hG id keyOfK3 q hq
  obtain ⟨blk, a, hm, Pl, Dc⟩ := k5_member h hj
  have hbm : blk ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder := List.mem_of_getElem? hm
  have hbp : blk.place = placeOf j := Dc.place
  obtain rfl : b = blk := List.inj_on_of_nodup_map hn hb hbm (by rw [hbq, ej, hbp])
  have hfind := k5LotK_find_K3 (W₀ := W₀) (Rc := Rc) (X := X) h hj hG id Pl.plan
  have hmem := List.mem_of_find?_eq_some hfind
  have hpl : (k5Half (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) id
      (seatOf keyOfK3 Zp A.G cF j a)).place = placeOf j := by
    simpa using List.find?_some hfind
  obtain rfl : q = k5Half id (seatOf keyOfK3 Zp A.G cF j a) :=
    List.inj_on_of_nodup_map once hq hmem (by rw [ej, hpl])
  exact k5_member_steps h hj hA Pl.plan Dc hf (some w) k

/-- IT IS NOT THE HONEST PROVER: TEN OF THE ELEVEN KINDS SEND NOTHING. **The end of ready_at_k5Lot, by the general law.**
Conditional: h; hL, hS, h2; hA; hi; ht. -/
theorem ready_of_lots_k5 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {W₀ Rc X₀ X : Type}
    {P : OnlineProverParts W₀ Rc Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    (hL : P.lots = [k5LotK id keyOfK3]) (hS : ∀ Z' G', P.shared Z' G' = [])
    (h2 : ∀ Z' G', P.second Z' G' = [])
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {w₀ : W₀} {x : ProofFile.Inst} {tr : Cells}
    (hi : P.inRange w₀ = true) (ht : P.trace Zp w₀ x = some tr) (rc : Rc) (k : Coins A.B) :
    ∃ R, ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.B A.H w₀ rc x k = .ok R := by
  refine ready_of_lots h hA (fun L hLm => ?_) ?_ hS h2 hi ht rc k
  · rw [hL] at hLm
    obtain rfl := List.mem_singleton.1 hLm
    exact lotPays_k5 h hA
  · rw [hL]
    exact List.pairwise_singleton _ _

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.lotPays_k5
#print axioms ProofFile.Honest.K5.ready_of_lots_k5
