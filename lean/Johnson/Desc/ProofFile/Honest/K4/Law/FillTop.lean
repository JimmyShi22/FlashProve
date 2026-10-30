-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/FillTop.lean: CONDITIONAL.

What is here. `AcceptedS` AT THE MEMBER OF THE FEED-FORWARD LAYERS' ROUNDS, AT THE FIRST CHAIN's
THREAD (`lettersHead`) OF THE HONEST PROVER THAT THE FRAME's MAKER `onlineProverFromPublicFiles` RETURNS AT THE PUBLIC
FILES OF h : AtMgA, AT THE FALLS BY THE MEMBER's NUMBER. It asks: h · `LaidK4` (`laid_head`,
Law/SeatedHead.lean, gives one from h and AtK4) · that the maker returns (hA) · that K4's lot is
among the filling's lots (hL) · that no other lot of the filling has a half at a place of the kind
K4 (ho) · that K4's own fall is among the falls (hm). NOTHING ELSE: nothing on the plan, on
`k4PubOf`, on the state's tokens or on what the lookup has heard. One statement: a call of
`k4_accepted_fill` (Law/HalfAtPure.lean) with `lookRestIx_head` (Law/LookJoin.lean).

Not shown here. OF h TOGETHER WITH hA, hL AND ho NO EXAMPLE IS KNOWN TO US (`LaidK4` asks nothing
beyond h: `laid_head`, Law/SeatedHead.lean, at the library's `atK4_full`; hm speaks of a list of
falls that the caller picks). THAT `onlineProverFromPublicFiles` RETURNS AT ANY FILLING THAT HOLDS K4's LOT: no such
filling is laid here. THAT h CAN HOLD: the side library AtFullSide proves, with no hypothesis, that
h has a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean,
whose own Limits say what it is worth). `AcceptedS` speaks only where the thread stands: that it
stands at any run is not shown. NOT COMPLETENESS. THE MEMBER's STEP TESTS NO SENT VALUE
(Law/Hears.lean): it accepts every play of the right shape, a false one too. THE FULL SIZE ALONE,
and at `OnBytes.secondHashFunction` alone. TWO TESTS ON THE PLAN REST ON CHECKS BY LEAN's OWN KERNEL
(`kernel_rfl`). OF THE FOURTEEN CLAUSES OF `k4PublicX` TEN REST WHOLLY ON SUCH CHECKS (seven facts
under Johnson/Road/K4/C/Free/, over Johnson/Road/K4/RowHead/ClosedAt.lean and ClosedTies.lean);
three more lean on one such fact beside a law. `k4TableFits`, WHICH THE LOT ASKS BEFORE IT LAYS A
HALF, IS ACCEPTED THROUGH AN EIGHTH FACT OF THAT FOLDER (`freeOwners`; Law/FitsMember.lean's head).
No independent checker has replayed them. A LAW, NOT A PART: no file that defines a part of the
proof file's description may import this one: as Law/DearTop.lean says of itself. Transitive
imports: those of Law/HalfAtPure.lean and of Law/LookJoin.lean: not counted. No property is claimed.

  `k4_accepted_filled`   **`AcceptedS` at the member, at the maker's prover.**

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.HalfAtPure
import Johnson.Desc.ProofFile.Honest.K4.Law.LookJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X' : Type}

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts}
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL. **`AcceptedS` AT THE MEMBER, AT THE MAKER's PROVER**, at the falls by the member's
number: from h, `LaidK4`, hA, hL, ho and hm alone. -/
theorem k4_accepted_filled {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard)
    (hL : k4HLot cells weights look ∈ P.lots)
    (ho : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    {fs : List (Fall TS)} (hm : k4Fall (k4PubAt cF k x) ∈ fs) :
    AcceptedS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (fallsBy fs cF.blocksInOrder) k :=
  k4_accepted_fill h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hA Said Lh cells weights look hL ho
    (lookRestIx_head h Lh.lt) hm

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_accepted_filled
