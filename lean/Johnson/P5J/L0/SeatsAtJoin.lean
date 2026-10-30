-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/P5J/L0/SeatsAtJoin.lean: THE FIELD seats OF THE TESTS ON THE PLAN THAT THE LAST TABLE's
LAW ASKS (`LLT25.PlanCore₃`), IN ITS OWN TEXT AT THE JOIN's OWN TERMS, FROM THE HEAD `AtMg`
(Johnson/P5J/AtMg.lean) AND ONE TEST: `madePinnedAt` accepts at the head's public part.

  `seatsFit_first`: the first table's members' seats fit, at that table's own codes: from the head's
    own field `plan.fit` (`seatsFitP`), as `At.PlanOk.hG` spends it.
  `told_shared`: hG at the head's description: its shared chain tells what `chainOf` tells at the
    seat's parameters.
  **`seats_at_join`**: `SeatsFit (p14At Zp).codes (F0T o Zp Np cF) (mineOf (At.ms Zp Z.lay)
    (Sh.ms (Sh.planAt Zp Np (F0T o Zp Np cF))) (At.N Zp cF) Ns)`, at every Ns.
Limits. `madePinnedAt`'s accept is a premise (over the entry tests' list of 13 rows the head gives
it: `AtMg.made_accepts`). A member of the head is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction;
side library AtFullSide/Top/). The full size alone. Nothing on soundness.
On hiding nothing.

-/
import Johnson.P5J.AtMg
import Johnson.LLT25R.MineSeats
import Johnson.Desc.Sound.SeamDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J.L0
open OnBytes OnBytes.Maker
open VerifiableInference.Desc (Chain oraclesOf)
open VerifiableInference.Desc.Sound (SeatsFit seatsFit_of_B)
open VerifiableInference.Desc.Shared (NumbersS)
open VerifiableInference.PlanWritten (madePinnedAt)
open _root_.Desc.K14 (p14Of beforePointOf chainOf)
open _root_.Desc.K14.Law (Sh.planAt Sh.ms)
open LLT25 (mineOf seatsFit_mineOf seatsFit_sh codes_one)
open ToldDesc (p14At)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- The first table's members' seats fit, at that table's own codes. -/
theorem seatsFit_first {lay : ByteArray} (ok : At.PlanOk o Zp Np cF lay) :
    SeatsFit (At.cs Zp) (F0T o Zp Np cF) (At.ms Zp lay) :=
  seatsFit_of_B (F0T o Zp Np cF) (At.cs Zp) (At.members Zp lay)
    ((P5T.seatsFitB_R _ _ _ _ _ (fun p hp _ => P5T.planSeats_send_lt Zp Zp.D.1 p hp)).trans ok.fit)

/-- The head's description's shared chain tells what `chainOf` tells at the seat's parameters. -/
theorem told_shared (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) :
    oraclesOf (F0T o Zp Np cF).shared.blocksInOrder =
      oraclesOf (chainOf Zp.p.chains (p14Of Zp.p.chains (beforePointOf Np))
        (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last).blocksInOrder :=
  _root_.Desc.K14.Law.Fence.oracles_retype _ rfl

/-- **THE FIELD seats.** -/
theorem seats_at_join (h : AtMg o Z D r Zp Np cF)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) (Ns : NumbersS) :
    SeatsFit (p14At Zp).codes (F0T o Zp Np cF)
      (mineOf (At.ms Zp Z.lay) (Sh.ms (Sh.planAt Zp Np (F0T o Zp Np cF))) (At.N Zp cF) Ns) := by
  have e : At.cs Zp = (p14At Zp).codes := codes_one h.scope h.laid.pub hy
  exact seatsFit_mineOf (e ▸ seatsFit_first h.plan)
    (seatsFit_sh h.scope h.laid.pub hy Np _ _ _ (told_shared o Zp Np cF))

end P5J.L0

#print axioms P5J.L0.seatsFit_first
#print axioms P5J.L0.told_shared
#print axioms P5J.L0.seats_at_join
