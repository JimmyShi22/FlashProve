-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/MsgsAtLotData.lean: the kind "the code switch" (K2): THE FIELD msgs OF THE RECORD
`K2SeatedL`, AT THE JOINED SCRIPT `joinQ`, AT EVERY MESSAGE OF EVERY SWITCH OF THE PLAN, AT THE
LETTERS AT WHICH THIS HOUSE's LAST ASSEMBLIES STAND: the list of jobs is the shared sending's lot's
at `K1.lotData S₀`, with the jobs of W behind; the switches' filling is `withSwitchData S₀
(K1.lotData S₀)`. `msgs_at_join_all` (AtFullSide/K2/MsgsAtJoinAll.lean) WITH hx, hdat AND hcl GONE.
A join: calls. No definition; nothing is evaluated here.

  `lotData_heard_first`   at the opening's sender's addresses `K1.lotData` reads no challenge
  `msgs_at_lot_data`   THE END

By. Here: `msgs_at_join_all` · `fillings_at_link_one` (FillingsAtLinkOne.lean) ·
`first_job_in_list` (Johnson/Desc/ProofFile/Honest/K8/MsgFirstAtJoin.lean): the opening's job stands
with the number 2 in that list; a file on no list of the library's · `closing_at_head`
(Honest/K2/Law/ClosingAtHead.lean): each switch's closing passes its public test. What it is for:
the field msgs of `SwitchLeftV` (Honest/K2/Law/MadeValuesLeft.lean) → the kind's debt under "the
exchange", by kind.

Limits. SIX PREMISES BESIDE THE HEAD, THE OPENING AND THE BOOK: F (the list is fit) · hin (it holds
the kind's share) · hpub · hD1, as in `msgs_at_join` (AtFullSide/K2/MsgsAtJoin.lean) · hI, hR: at
each input that is meant the sender's reader wit hands the input's own instance and the readers that
the switches read. Whether a text answers is not said. That the joined Script is the honest prover's
is not said here: it is laid from lots, and holds what their texts say. A tie to a Script: what is
WRITTEN where, at each run's coins. The limits of the files called stand.
NOT IN FRONT OF A LAW OVER COINS. It speaks at the head's own size and hash: the full size, the
format's second hash function. Nothing on any property.
-/
import AtFullSide.K2.FillingsAtLinkOne
import Johnson.Desc.ProofFile.Honest.K8.MsgFirstAtJoin
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Block Place)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.HonestTrace (Sz)
open OnBytes.SendSim.Seat (wJobs)
open Johnson.G (proofSendsFull)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.K1 (seatAtMember)
open ProofFile.Honest.FirstThread (TreeLot OwnMsgs Others joinQ JoinFit byNo)
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law

/-- At the opening's sender's addresses `K1.lotData` reads no challenge. -/
theorem lotData_heard_first (S₀ : Sz) (Z : ProofFile.Pub) (G : ProofFile.Ground) (x : ProofFile.Inst) (n : Nat) :
    (K1.lotData S₀ Z G x).heardAt ⟨K1.firstAddr, n⟩ = 0 := rfl

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {B : ProverCoinCounts} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
  {W₀ Rc Tr X Cells Tok : Type}
  {wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst} {own₀ : X}
  {Oth : Others B (Local W₀ Rc ProofFile.Inst Tr)} {readers : Local W₀ Rc ProofFile.Inst Tr → Readers}
  {rest : Nat → TreeLot B (Local W₀ Rc ProofFile.Inst Tr)}

/-- **THE FIELD msgs AT THE JOINED SCRIPT, AT EVERY MESSAGE OF EVERY SWITCH OF THE PLAN, AT THE
SHARED SENDING's LOT's OWN DATA.** NOT IN FRONT OF A LAW OVER COINS. -/
theorem msgs_at_lot_data (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    (S₀ : Sz) (no : Place → Nat) (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
    (F : JoinFit cF.blocksInOrder 0 (P5J.At.arr Zp) (P5J.At.seats Zp) wit own₀
      (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                 wJobs (X := X) no Dd Zp Bs.G₀)) Oth)
    (hin : ShareIn (switchShareAt B cF.blocksInOrder 0 Zp Bs.G₀ (withSwitchData S₀ (K1.lotData S₀) Zp Bs.G₀)
      readers rest) Oth)
    (cells : Local W₀ Rc ProofFile.Inst Tr → Cells) (tok : Local W₀ Rc ProofFile.Inst Tr → Tok)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (hpub : ∀ p ∈ switchPlaces Zp Bs.G₀, ∀ w, Vd w →
      publicOk (withSwitchData S₀ (K1.lotData S₀) Zp Bs.G₀) Bs.G₀.first.layout p
        ((segmentsOf Zp Bs.G₀).take p.link) w.x = true)
    (hD1 : ∀ p₀ ∈ switchPlaces Zp Bs.G₀, ∀ p ∈ switchPlaces Zp Bs.G₀, p₀.link + 1 = p.link →
      ∀ w, Vd w → ∀ s m a, s < p₀.link → p.addrs s m = some a →
        (withSwitchData S₀ (K1.lotData S₀) Zp Bs.G₀ w.x).heardAt a ≤
          0 + roundsTo cF.blocksInOrder (switchNo p₀))
    (hI : ∀ w, Vd w → (wit w).x = w.x) (hR : ∀ w, Vd w → (wit w).R = readers w) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, ∀ n, n < (switchPar p).sent.size →
      OwnMsgs (joinQ cF.blocksInOrder 0 cells tok (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := X) no (K1.lotData S₀) Zp Bs.G₀ ++
                 wJobs (X := X) no Dd Zp Bs.G₀)) Oth) Vd
        (0 + roundsTo cF.blocksInOrder (switchNo p))
        (P5J.At.arr Zp (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n).1
          (seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n).2)
        (0 + roundsTo cF.blocksInOrder (switchNo p))
        (switchMsgOff 0 (withSwitchData S₀ (K1.lotData S₀) Zp Bs.G₀) readers
          (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p n) :=
  msgs_at_join_all h O hB F hin cells tok Vd (closing_at_head h.toAtMg O) hpub hD1
    (K8.first_job_in_list h O no S₀ Dd)
    (fillings_at_link_one h O S₀ (K1.lotData S₀) Vd (no ⟨1, some 0, 1, .K1⟩) hI hR
      fun w _ n => by rw [lotData_heard_first]; exact Nat.zero_le _)

end AtFullSide.K2

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms AtFullSide.K2.lotData_heard_first
#print axioms AtFullSide.K2.msgs_at_lot_data
