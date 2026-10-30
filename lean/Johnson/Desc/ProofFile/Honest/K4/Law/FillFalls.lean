-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/FillFalls.lean: CONDITIONAL.

What is here. `AcceptedS` AT THE MEMBER OF THE LAYERS' OWN ROUNDS (kind K4), at the first chain's
thread (`lettersHead`) OF THE HONEST PROVER THAT THE FRAME's MAKER `onlineProverFromPublicFiles` RETURNS at the public
files of h, AT THE FALLS THAT K4's OWN LIST HOLDS (`k4LotFalls`, Honest/K4/LotFalls.lean). It is
`k4_accepted_filled` (Law/FillTop.lean) WITH ITS HYPOTHESIS hm STRUCK: that the member's fall
`k4Fall (k4PubAt cF k x)` is among the falls. The member's parameters x are known only to exist
(`laid_head`, Law/SeatedHead.lean), so no written list can be shown to hold the fall at x; here the
fall is shown to be a member of the list that is made off the lot's own list of places, at the
maker's own public part and ground (`k4Fall_mem_atPure`). Where the words are defined: `Fall`:
Honest/Side.lean; `fallsBy`: Honest/Law/FallFree.lean; `AcceptedS`: Honest/Thread/PaysS.lean;
`OnlineProverParts`, `onlineProverFromPublicFiles`: Honest/AtPure.lean. Three statements with their proofs.

  `k4Fall_mem_atPure`   **the member's fall is in K4's list, at A.Z and A.G.**
  `k4_accepted_falls`   **`AcceptedS` at every list of falls that holds K4's list.**
  `k4_accepted_lotFalls`   the same at K4's list itself.

Limits. CONDITIONAL: on h · LaidK4 · hA (the maker returns); the two on `AcceptedS` besides on hL
(K4's lot is among the filling's lots) · ho (no other lot of the filling has a half at a place of
the kind K4); `k4_accepted_falls` besides on hs (the list of falls holds K4's). «EVERY LIST THAT
HOLDS K4's» IS THE WEAKER WAY: `AcceptedS` asks that no fall at the place has spoken, so each
further fall at K4's place makes it say less. K4's SECOND FALL, on the free slots behind the
batching, IS NOT IN THE LIST (Honest/K4/LotFalls.lean's head). That `onlineProverFromPublicFiles` returns at any filling
that holds K4's lot is not shown here; no example of the hypotheses together is known. `AcceptedS`
speaks only where the thread stands. NOT COMPLETENESS: the member's step tests no sent value
(Law/Hears.lean): it accepts every play of the right shape. EACH FALL's SHARE IS A STATED NUMBER:
nothing is added up here. THE FULL SIZE ALONE, AND THE FORMAT's EARLIER HASH ALONE; that h holds of
any files is not shown here: the side library AtFullSide proves, with no hypothesis, that h has a
member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). Of h together with LaidK4 · hA · hL · ho · hs no example is known
to us. Beneath `tableFits_member` stand comparisons by Lean's own kernel that no independent checker
has replayed (Law/FitsMember.lean's head names them). IT IS A LAW, NOT A PART: it rests on modules
under Johnson/Goal/: no file that defines a part may build on it; it states no goal. Nothing on
soundness, on completeness or on any other property.
No property is claimed.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FillTop
import Johnson.Desc.ProofFile.Honest.K4.LotFalls

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

/-- CONDITIONAL: on h, Lh and hA. **THE MEMBER's FALL IS IN K4's LIST, AT THE MAKER's OWN PUBLIC
PART AND GROUND.** -/
theorem k4Fall_mem_atPure {S : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    (k4Fall (k4PubAt cF k x) : Fall S) ∈ k4LotFalls A.Z A.G := by
  obtain ⟨hZ, hG, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (hZ.symm.trans h.laid.pub)
  obtain ⟨G₀, hG₀, hx⟩ := Lh.lot
  have eG : G₀ = A.G := Option.some.inj (hG₀.symm.trans (eZ ▸ hG))
  subst eG
  rw [eZ]
  exact k4Fall_mem hx (k4Pub_head h Lh) (tableFits_member h Lh)

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts}
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL: on h, Lh, hA, hL, ho and hs. **`AcceptedS` AT THE MEMBER, AT THE MAKER's PROVER, AT
EVERY LIST OF FALLS THAT HOLDS K4's LIST.** -/
theorem k4_accepted_falls {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard)
    (hL : k4HLot cells weights look ∈ P.lots)
    (ho : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    {fs : List (Fall TS)} (hs : ∀ f ∈ k4LotFalls A.Z A.G, f ∈ fs) :
    AcceptedS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (fallsBy fs cF.blocksInOrder) k :=
  k4_accepted_filled h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hA Said Lh cells weights look hL ho
    (hs _ (k4Fall_mem_atPure h Lh hA))

/-- CONDITIONAL: on h, Lh, hA, hL and ho. The same at K4's list itself. -/
theorem k4_accepted_lotFalls {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard)
    (hL : k4HLot cells weights look ∈ P.lots)
    (ho : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G) :
    AcceptedS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (fallsBy (k4LotFalls A.Z A.G) cF.blocksInOrder) k :=
  k4_accepted_falls h Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hA Said Lh cells weights look hL ho
    fun _ hf => hf

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4Fall_mem_atPure
#print axioms ProofFile.Honest.K4.k4_accepted_falls
#print axioms ProofFile.Honest.K4.k4_accepted_lotFalls
