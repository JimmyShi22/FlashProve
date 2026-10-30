-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstReachAt.lean: FROM FIVE FACTS AT EVERY REACHED LAST STATE OF
THE FIRST CHAIN (five_at_end, Johnson/IMR/EndFive.lean: in that file's own letters, "reached"
written out) TO THE SENTENCE THAT THE SHARED TABLE's CONSTANT SPENDS (Sh.ReachOwed,
Johnson/Desc/K14/Law/SharedConstReachOwed.lean). The part of the last step that names none of that
file's definitions.

  Sh.FiveAtEnd Z c L   five_at_end's END, TO THE LETTER, as a Prop by def: it names the public value
                       Z, the first chain c and the written list L alone
  Sh.reachOwed_of_five     (FiveAtEnd says more than is asked: at every public instance; ReachOwed
                       asks at typed instances alone) FiveAtEnd Z c L and "the parameters' codes are
                           the first chain's" give
                       ReachOwed o Z N B' c L: EndAt₁ at seatF … IS "reached" written out, by
                       unfolding
  Sh.first_inj         two spellings of one IOP as written in Lean by the maker's own text have one
                       first chain: so a fact at the chain that one opening names is a fact
                       at the chain that another names
  Sh.open_at           what the verifier makes, in the letters descN … Z N c, can be opened in the
                       form IM.Open (Johnson/IMR/SeatOpen.lean) AT THAT VERY Z AND c
  Sh.reachOwed_in_scope    **in the goals' scope, at the value that is laid: ReachOwed at the second
                       hash function itself**, from FiveAtEnd at every such opening: five_at_end's
                       own form, once its three named premises are in hand at that opening
WHAT IS NOT HERE. No law. FiveAtEnd itself: the theorem five_at_end, under its named premises.
What is not claimed. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.SharedConstReachOwed
import Johnson.Desc.K14.Law.SharedConstLaid
import Johnson.IMR.SeatOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)
open VerifiableInference.Desc.Third (P₁₄)

open Johnson.Desc.First.Walk.Tied (Reach EndAt₁)
open Johnson.G (codesFull2)
open VerifiableInference.Desc.K1 (realSized)
open H2K.JointK (descN)

namespace Sh

/-- **The five facts of five_at_end (Johnson/IMR/EndFive.lean), at that theorem's own end.** -/
def FiveAtEnd (Z : ProofFile.Pub) (c : VerifiableInference.Desc.Chain First.S ProofFile.Cl)
    (L : VerifiableInference.Desc.K12.Door.Laid) : Prop :=
  ∀ p : ProofFile.InstPub × First.S, Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) c.blocksInOrder.length p →
    p.2.failed = none →
    VerifiableInference.Desc.K12.Door.atFirstBook 0 p.2 = true ∧ bookFitsB p.2.book = true ∧
      p.2.book.place.size = p.2.st.oracles.size ∧ p.2.st.codes = Z.first.codes ∧
      VerifiableInference.Desc.K12.Door.atFirstSeats L p.2 = true

/-- **To the constant's sentence.** -/
theorem reachOwed_of_five (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (N : H2U.Places4)
    (B' : ProofFile.SecondSeat) (c : VerifiableInference.Desc.Chain First.S ProofFile.Cl)
    (L : VerifiableInference.Desc.K12.Door.Laid) (h5 : FiveAtEnd Z c L)
    (ec : (planAt Z N (seatF o Z N B' c)).Q.codes = Z.first.codes) :
    ReachOwed o Z N B' c L := by
  intro p hr _ hm
  obtain ⟨a1, a2, a3, a4, a5⟩ := h5 p hr hm
  exact ⟨a1, a2, a3, a4.trans ec.symm, a5⟩

/-- **One IOP as written in Lean, one first chain.** -/
theorem first_inj {o o' : ProofFile.SecondHashFunctionArgument} {mk mk' : ProofFile.LinksBy} {Z Z' : ProofFile.Pub}
    {s s' : ProofFile.SharedSeat} {B B' : ProofFile.SecondSeat}
    {c c' : VerifiableInference.Desc.Chain First.S ProofFile.Cl}
    (e : ProofFile.fileDescBy o mk Z s B (fun t => t) (ProofFile.startS Z) c =
      ProofFile.fileDescBy o' mk' Z' s' B' (fun t => t) (ProofFile.startS Z') c') : c = c' := by
  have h := congrArg (fun F : FileDescription ProofFile.Inst =>
    (⟨F.S₁, F.Cl, F.first⟩ : Σ (S C : Type), VerifiableInference.Desc.Chain S C)) e
  have h2 : (⟨First.S, ProofFile.Cl, c⟩ : Σ (S C : Type), VerifiableInference.Desc.Chain S C) =
      ⟨First.S, ProofFile.Cl, c'⟩ := h
  have h3 := eq_of_heq (Sigma.mk.inj h2).2
  exact eq_of_heq (Sigma.mk.inj h3).2

/-- **An opening at that very Z and c.** -/
theorem open_at {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub} {N : H2U.Places4}
    {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl}
    (hF : ProofFile.onlineDescription o pol lay KL = .ok (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c))
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) :
    ∃ Bs base A B, IM.Open o pol lay KL (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) Z Bs base c A B
        := by
  obtain ⟨Z', Bs, base, c', A, B, O⟩ := IM.seat_open hF
  obtain rfl : Z' = Z := Except.ok.inj (O.pub.symm.trans hZ)
  obtain rfl : c = c' := first_inj O.desc
  exact ⟨Bs, base, A, B, O⟩

/-- **ReachOwed in the goals' scope, at the value laid, at the second hash function itself.** -/
theorem reachOwed_in_scope {S : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {x : LinSized} {Z : ProofFile.Pub} {N : H2U.Places4}
    {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl}
    {L : VerifiableInference.Desc.K12.Door.Laid} (hS : VerifierAndGoals.InScope S = true)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles OnBytes.secondHashFunction S.pol S.lay S.KL = .ok (D, r))
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction S.pol S.lay S.KL = .ok (descN OnBytes.secondHashFunction
                                   ProofFile.pureRoad.links guardedProximityTestParts Z N c))
    (hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction S.pol S.lay S.KL = .ok Z)
    (hs : VerifiableInference.PlanWritten.sizedPinnedAt Z.p.X.P Z.p.chains.made = true)
    (hf : VerifiableInference.PlanWritten.firstPinnedAt Z.p.X.P Z.first = true)
    (hx : realSized = some (x, codesFull2))
    (h5 : ∀ Bs base A B, IM.Open OnBytes.secondHashFunction S.pol S.lay S.KL (descN OnBytes.secondHashFunction
                    ProofFile.pureRoad.links guardedProximityTestParts Z N c) Z Bs base c A B →
      FiveAtEnd Z c L) :
    ReachOwed OnBytes.secondHashFunction Z N (H2K.JointK.secondN guardedProximityTestParts Z N) c L := by
  obtain ⟨Bs, base, A, B, O⟩ := open_at hF hZ
  exact reachOwed_of_five OnBytes.secondHashFunction Z N _ c L (h5 Bs base A B O)
    (codes_first_in_scope hS hZ hs hf hL hx N _)

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.reachOwed_of_five
#print axioms Desc.K14.Law.Sh.first_inj
#print axioms Desc.K14.Law.Sh.open_at
#print axioms Desc.K14.Law.Sh.reachOwed_in_scope
