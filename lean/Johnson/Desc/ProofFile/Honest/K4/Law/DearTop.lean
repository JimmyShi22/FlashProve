-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/DearTop.lean: CONDITIONAL.

What is here. `AcceptedS` AT THE MEMBER OF THE FEED-FORWARD LAYERS' ROUNDS, AT THE FIRST CHAIN's
THREAD (`lettersHead`), WITH NO HYPOTHESIS ON THE PLAN BESIDE WHAT half HOLDS, AND NONE ON `k4PubOf`
OR ON THE STATE's TOKENS: the test `k4PublicX`, that `k4PubOf` returns and `tokensFit` stand under h
: AtMgA and `LaidK4` (`publicX_head`, Law/DearX.lean · `k4Pub_head`, Law/FrontCount.lean ·
`tokens_head`, Law/TokensHead.lean). One statement: a call. The public data `k4PubAt` are defined in
Law/TableFitsMember.lean. Words: Law/ElevenHead.lean's head.

Not shown here. THAT h CAN HOLD: the side library AtFullSide proves, with no hypothesis, that h has
a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). OF h TOGETHER WITH half AND hf NO EXAMPLE IS KNOWN TO US (`LaidK4`
asks nothing beyond h: `laid_head`, Law/SeatedHead.lean, at the library's `atK4_full`; hL is a
theorem under h: `lookRestIx_head`, Law/LookJoin.lean). `Behind` and `AcceptedS` speak only where
the thread stands: that it stands at any run is not shown. NOT COMPLETENESS. THE MEMBER's STEP TESTS
NO SENT VALUE (Law/Hears.lean): it accepts every play of the right shape, a false one too. WHAT
STAYS FOR `AcceptedS`, BY NAME: the structure Lh : LaidK4 on the member (h and AtK4 give one) · half
(the prover's list of halves holds K4's half at the member's place, at the public data `k4PubAt`;
whoever shows it out of K4's lot's honest side shows `k4TableFits` of that public data beside: A
TEST ON THE PLAN, Honest/K4/Part.lean) · `LookRestIx` (Law/LookMemberHead.lean: the conclusion of a
statement of the writers of Honest/K3/; it stands under h in Law/LookJoin.lean) · hf (where the fall
says nothing the honest side's test on one sampled element says nothing). THE FULL SIZE ALONE, and
at `OnBytes.secondHashFunction`, the format's second hash function, alone. TEN OF THE FOURTEEN CLAUSES OF THE TEST ON
THE PLAN REST WHOLLY ON CHECKS BY LEAN's OWN KERNEL (`kernel_rfl`: seven facts under
Johnson/Road/K4/C/Free/, over Johnson/Road/K4/RowHead/ClosedAt.lean and ClosedTies.lean); three more
lean on one such fact beside a law; no independent checker has replayed them. A LAW, NOT A PART: no
file that defines a part of the proof file's description may import this one: its imports reach
Johnson/Goal/; what it calls RESTS, through the library's `refPub_in_scope`, ON A STATEMENT OF A
FILE UNDER Johnson/Goal/ (`Meaning.P34.pub34_all`), and Law/FrontCount.lean calls one there by name
(`P5J.pins_of_laid`). Transitive imports, by a program's walk over import lines. Opening every
module that it reaches: 175 modules under Johnson/Goal/, 53 whose name holds RecCompile, 140 under
ThirdParty/. Stopping unopened at Johnson/Goal/, Johnson/D/ and ThirdParty/ (so these are floors):
71 under Johnson/Goal/, 46 whose name holds RecCompile, 2 under ThirdParty/. By both: none under
Johnson/D/; none of RecCompile's Honest*, Both or PassH*. No property is claimed.

  `k4_accepted_dear`   **`AcceptedS` at the member.**

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.TableFitsMember
import Johnson.Desc.ProofFile.Honest.K4.Law.PublicOne
import Johnson.Desc.ProofFile.Honest.K4.Law.DearX
import Johnson.Desc.ProofFile.Honest.K4.Law.FrontCount
import Johnson.Desc.ProofFile.Honest.K4.Law.TokensHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Claim Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL. **`AcceptedS` AT THE MEMBER**, with no hypothesis on the plan beside what half
holds. -/
theorem k4_accepted_dear (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop)
    {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard}
    {fall : Nat → S → List Fmt.Drawn → Option String}
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights tokens look (k4PubAt cF k x)))
    (hL : LookRestIx cF.blocksInOrder (28 * g + 3))
    (hf : ∀ s ds, fall k s ds = none → k4CoinZero (k4PubAt cF k x) ds = none) :
    AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall k :=
  k4_accepted_one h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (publicX_head h) Said Lh
    (k4Pub_head h Lh) half hL
    (fun _ _ _ _ _ hT => tokens_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lh hT.1) hf

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_accepted_dear
