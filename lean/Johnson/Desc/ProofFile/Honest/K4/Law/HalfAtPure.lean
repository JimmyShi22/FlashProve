-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/HalfAtPure.lean: CONDITIONAL.

What is here. AT THE HONEST PROVER THAT THE FRAME's MAKER `onlineProverFromPublicFiles` RETURNS AT THE PUBLIC FILES OF h
: AtMgA (Honest/AtPure.lean), FROM A FILLING WHOSE LIST OF LOTS HOLDS K4's (`k4HLot`; hL) AND IN
WHICH NO OTHER LOT HAS A HALF AT A PLACE OF THE KIND K4 (ho): (1) the hypothesis half of
`k4_accepted_dear` (Law/DearTop.lean) HOLDS: the first half of the prover's first chain at the
member's place is K4's, at the public data `k4PubAt`; (2) so `AcceptedS` at the member of the
feed-forward layers' rounds, at the falls by the member's number of every list that holds K4's own
fall. The maker's public part is h's, and its ground is the one that `LaidK4` names: both by the
frame's `atPure_ok` (Honest/AtPureLaw.lean). Which half is found: the frame's
`atPure_first_find_kind` (Honest/FirstFindKind.lean), with `lot_half_head` (Law/HalfHead.lean) for
what K4's own list holds. Statements and proofs: calls.

Not shown here. THAT `onlineProverFromPublicFiles` RETURNS AT ANY FILLING THAT HOLDS K4's LOT: a hypothesis; no such
filling is laid here. ho: that every other lot of the filling has no half at a place of the kind K4:
a hypothesis: it speaks of the other lots. THAT h CAN HOLD: the side library AtFullSide
proves, with no hypothesis, that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). OF h TOGETHER WITH hA,
hL AND ho NO EXAMPLE IS KNOWN TO US (`LaidK4` asks nothing beyond h: `laid_head`,
Law/SeatedHead.lean, at the library's `atK4_full`; hR is a theorem under h: `lookRestIx_head`,
Law/LookJoin.lean; hm speaks of a list of falls that the caller picks). `AcceptedS` speaks only
where the thread stands: that it stands at any run is not shown. NOT COMPLETENESS. THE MEMBER's STEP
TESTS NO SENT VALUE (Law/Hears.lean): it accepts every play of the right shape, a false one too.
`LookRestIx` (Law/LookMemberHead.lean) stays a hypothesis here: it stands under h in
Law/LookJoin.lean. THE FULL SIZE ALONE, and at `OnBytes.secondHashFunction` alone. Beneath it stand comparisons
by Lean's own kernel (`kernel_rfl`): the test `k4TableFits` is accepted through `tableFits_member`
(Law/TableFitsMember.lean), whose head says where they stand; no independent checker has replayed
them. A LAW, NOT A PART: no file that defines a part of the proof file's description may import this
one: as Law/DearTop.lean says of itself. Transitive imports, by a program's walk over import lines.
Opening every module that it reaches: 175 modules under Johnson/Goal/, 53 whose name holds
RecCompile, 140 under ThirdParty/. Stopping unopened at Johnson/Goal/, Johnson/D/ and ThirdParty/
(so these are floors): 71 under Johnson/Goal/, 46 whose name holds RecCompile, 2 under ThirdParty/.
By both: none under Johnson/D/; none of RecCompile's Honest*, Both or PassH*.
No property is claimed.

  `half_atPure`   **half, at the maker's prover.**
  `k4_accepted_fill`   **`AcceptedS` at the member, at the maker's prover.**

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.HalfHead
import Johnson.Desc.ProofFile.Honest.K4.Law.DearTop
import Johnson.Desc.ProofFile.Honest.FirstFindKind

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

/-- CONDITIONAL: on h, `LaidK4`, hA, hL and ho. **half, AT THE MAKER's PROVER.** -/
theorem half_atPure (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) {P : OnlineProverParts W₀ Rc Tr X₀ X'}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard)
    (hL : k4HLot cells weights look ∈ P.lots)
    (ho : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G) :
    A.H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights k4Tokens (look Zp A.G) (k4PubAt cF k x)) := by
  obtain ⟨hZ, hG, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (hZ.symm.trans h.laid.pub)
  obtain ⟨G₀, hG₀, hx⟩ := Lh.lot
  have eG : G₀ = A.G := Option.some.inj (hG₀.symm.trans (eZ ▸ hG))
  subst eG
  refine atPure_first_find_kind hA hL ho ?_
  rw [eZ]
  exact lot_half_head h Lh cells weights look hx

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts}
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL. **`AcceptedS` AT THE MEMBER, AT THE MAKER's PROVER**, at the falls by the member's
number. -/
theorem k4_accepted_fill {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard)
    (hL : k4HLot cells weights look ∈ P.lots)
    (ho : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    (hR : LookRestIx cF.blocksInOrder (28 * g + 3)) {fs : List (Fall TS)}
    (hm : k4Fall (k4PubAt cF k x) ∈ fs) :
    AcceptedS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (fallsBy fs cF.blocksInOrder) k :=
  k4_accepted_dear h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said Lh
    (half_atPure h Lh hA cells weights look hL ho) hR (hf_head Lh hm)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.half_atPure
#print axioms ProofFile.Honest.K4.k4_accepted_fill
