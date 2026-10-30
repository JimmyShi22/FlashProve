-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/PublicOne.lean: CONDITIONAL.

What is here. The tests on the plan that `AcceptedS` at the members of the feed-forward layers'
rounds still asks (Law/ElevenHead.lean, Law/LookMemberHead.lean), as one test with code on the
public parameters, in the form of the library's own tests at the twelve groups. That the
sub-protocol covers the plan is not in it: it is shown under h : AtMgA. (`Behind` asks no such test:
`k4_behind_all`, Law/ElevenHead.lean.) The tests are defined in Law/PublicX.lean, which imports no
other file under Johnson/Desc/ProofFile/. Statements with their proofs. Words: Law/ElevenHead.lean's
head.

Not shown here. THAT THE TEST IS TRUE AT ANY PUBLIC PARAMETERS. In `k4_accepted_one` the public part
Zp is a variable under h : AtMgA: SO `k4PublicX (P5J.At.X Zp) = true` CAN BE HAD THERE BY NO
EVALUATION AND BY NO DECISION OF THE KERNEL: IT WANTS A STATEMENT FROM h, as the library's
`front_at_head` (Johnson/Road/K4/RowHead/FrontFreeK.lean) is one for another test of this form.
Law/DearX.lean HAS THAT STATEMENT: `publicX_head` : `k4PublicX (P5J.At.X Zp) = true` under h. An
evaluation at given public parameters is a test that can fail, and no more. No file of this folder
evaluates it; Law/PublicOneTest.lean evaluates its part `k4PublicB` at a small synthetic plan. IT IS
NOT ALL THAT IS PUBLIC IN WHAT `k4_accepted_one` ASKS: hQ (that `k4PubOf` returns) reads the public
part alone (Law/FrontCount.lean has it under h and `LaidK4`); and whoever shows half out of K4's
lot's honest side shows `k4TableFits` of the public data beside (Honest/K4/Part.lean). That the
top's hypotheses can hold together: no example is known (by binder, beside h: `public_of_X`: hB, Lh
· `k4_accepted_one`: hB, Lh, hQ, half, hL, hTok, hf). `covers_head` takes h and `LaidK4` alone:
`LaidK4` asks nothing beyond h (`laid_head`, Law/SeatedHead.lean, at the library's `atK4_full`), and
of h alone: the side library AtFullSide proves, with no hypothesis, that h has a member at one place
(AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it
is worth). `Behind` and `AcceptedS` speak only where the thread stands: that it stands at any run is
not shown. NOT COMPLETENESS. THE MEMBER's STEP TESTS NO SENT VALUE (Law/Hears.lean): it accepts
every play of the right shape, a false one too. THE FULL SIZE ALONE, and at `OnBytes.secondHashFunction`, the
format's second hash function, alone. A LAW, NOT A PART: no file that defines a part of the proof file's
description may import this one: its imports reach Johnson/Goal/. Transitive imports, by a program's
walk over import lines. Opening every module that it reaches: 163 modules under Johnson/Goal/, 53
whose name holds RecCompile, 140 under ThirdParty/. Stopping unopened at Johnson/Goal/, Johnson/D/
and ThirdParty/ (so these are floors): 70 under Johnson/Goal/, 46 whose name holds RecCompile, 2
under ThirdParty/. By both: none under Johnson/D/; none of RecCompile's Honest*, Both or PassH*.
No property is claimed.

  `k4PublicB p` (Law/PublicX.lean)   at one member's parameters: ten comparisons of the plan's
      numbers and the pure functions that the hearing calls (two of the three tests of `k4PlanB`,
      Law/Hears.lean) · `k4ShapeB` (there too) · the slots that the lookup and this sub-protocol's
      hearing take are at most the plan's number of slots · lt ≤ dT at the plan's shape. It reads
      the public numbers, the plan and the group alone: `k4PublicB_reads`.
  `k4PublicX X` (there)   **the test on the public parameters**: that test at each group below 12,
      at the group's plan.
  `covers_head`   under h the sub-protocol covers the plan: the member's own test on the plan holds
      it.
  `public_of_X`   the test at the parameters of a member with `LaidK4`.
  `k4_accepted_one`   **`AcceptedS`**, from h, `LaidK4`, the test, and: hQ · half · `LookRestIx`
      (Law/LookMemberHead.lean) · the test on the state's tokens in the first group
      (Law/TokensHead.lean has it under h and `LaidK4`) · that where the fall says nothing the
      honest side's test on one sampled element says nothing.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.LookMemberHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (HPlan2)
open OnBytes.Desc.First.K4 (Par seatS covers)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Desc.First.K4.Rt (k4Takes planNumsB)
open OnBytes.Desc.First.K4.RtPub (tokensFit hearPB)
open OnBytes.Road.K4 (parOf)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Claim Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- The test at the parameters of a member with `LaidK4`. -/
theorem public_of_X (hB : k4PublicX (P5J.At.X Zp) = true) {k m g : ℕ} {x : Bool × Par}
    {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) : k4PublicB (parOf x) = true := by
  unfold k4PublicX at hB
  have h1 := List.all_eq_true.1 hB g (List.mem_range.2 Lh.lt)
  rw [Lh.hp, Option.any_some] at h1
  rw [k4PublicB_reads]
  show k4PublicB (parAt x.2.P x.2.hp x.2.g) = true
  rw [Lh.P, Lh.grp]
  exact h1

/-- **Under h the sub-protocol covers the plan**: the description's test on the plan accepts (a
field of h), so the member's does, and that holds the sub-protocol's own. -/
theorem covers_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) : covers (parOf x).P = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have ok := IM.blocksOk_of_planOk O h.laid.planOk
  unfold VerifiableInference.Desc.blocksOk at ok
  have h1 := List.all_eq_true.1 ok blk (List.mem_of_getElem? Lh.member)
  have h2 : blk.planOk = true := ((Bool.and_eq_true _ _).mp h1).1
  have h3 : ((OnBytes.Desc.First.K4.blockAtC { x.2 with k3Runs := true }).planOk && x.1) = true :=
    IM.laid_planOk Lh.laid.laid h2
  exact ((Bool.and_eq_true _ _).mp h3).1

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **`AcceptedS` AT THE MEMBER**, from the test on the public parameters. CONDITIONAL. -/
theorem k4_accepted_one (hB : k4PublicX (P5J.At.X Zp) = true)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    {fall : Nat → S → List Fmt.Drawn → Option String} (hQ : k4PubOf Zp x.2 = some Qp)
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights tokens look Qp))
    (hL : LookRestIx cF.blocksInOrder (28 * g + 3))
    (hTok : g = 0 → ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said k c s mm E →
      tokensFit { (parOf x).P with tokv := seatS.tokv s } (parOf x).g = true)
    (hf : ∀ s ds, fall k s ds = none → k4CoinZero Qp ds = none) :
    AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall k := by
  have hP := public_of_X hB Lh
  unfold k4PublicB at hP
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hP
  obtain ⟨⟨⟨⟨hNu, hHe⟩, hSh⟩, hn⟩, h2⟩ := hP
  have hPl : k4PlanB (parOf x) = true := by
    unfold k4PlanB
    rw [covers_head h Lh, hNu, hHe]
    rfl
  have Sx := (nine_head h Lh).Sx
  refine k4_accepted_rest h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said Lh hQ half hPl hSh ?_ h2
    hL hTok hf
  rw [Sx.shape]
  exact hn

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.public_of_X
#print axioms ProofFile.Honest.K4.covers_head
#print axioms ProofFile.Honest.K4.k4_accepted_one
