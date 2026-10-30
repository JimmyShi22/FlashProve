-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/FiveTabled.lean: the linear claim's shared rounds (kind K14): THE TWO FIELDS treesU
AND treesO OF K14Asks (Johnson/Desc/ProofFile/Honest/K14/Asks.lean) AT THE THREAD OF THE PROOF
FILE's OWN DESCRIPTION (lettersShared, Honest/Thread/SharedHead.lean), WHERE THE LETTER table IS
tableShared (Honest/K12/AtFile/TableShared.lean); and so the five statements on one sub-protocol at
the members 1 to 8 of the shared chain, at the prover that the maker onlineProverFromPublicFiles returns at the filling
onlineProverPartsInUse, with the two premises treesU and treesO of five_at_base
(AtFullSide/K14/FiveAtBase.lean) traded for two equations on the letter fixed and the laying of the
letter table.

  trees_tabled        **the two fields**: treesU_at_shared and treesO_at_shared
                      (Honest/K12/AtFile/TreesAtShared.lean) speak of the thread of this kind's own
                      letters (letters2, Honest/K14/Thread2.lean); under the nine equations Asked
                      the thread of lettersShared is that thread (letters_eq,
                      Honest/K14/LettersVar.lean)
  five_at_base_tabled **the five at a member b, 1 ≤ b ≤ 8**, at that prover's thread
  five_at_base_laid   **the same WITHOUT THE PREMISE Asked**, at letters at which it holds: this
                      kind's makers laid at the five letters Mg, shape, order, wit, keeps (mgWords,
                      form2, "the statement is in order", witL, kp2: Honest/K14/Thread2.lean,
                      AskedAtShared.lean), over Mg₀, shape₀, rest, Kp₀ that stay free. WHAT ROOM
                      THAT LEAVES THE CHAIN's OTHER MEMBERS (0, 9, 10, 11): order has no free part;
                      the fields pin, row, nearU, recRow, omU of Mg are laid whole; the form at the
                      borders 2 to 9 is this kind's; keeps is free at their four places
  fixedShared_low     at the written rounds the letter fixed laid as fixedShared
                      (Honest/K12/AtFile/TableShared.lean) is 1 at own 0 and 4 at own 1 and 2: the
                      two premises h0, h1: by evaluation in the kernel

WHAT trees_tabled ASKS OF THE LETTERS. table is tableShared at the plan, at the two readers, at any
two test jobs JU, JO and any own₀. fixed is 1 at the chain's own tree 0, and 4 at its own trees 1
and 2: the numbers of challenges after which these trees' tables change no more. letters: Asked.

What is not claimed. That any premise holds. What five_at_base does not claim. Nothing on
completeness, soundness or hiding.
Terms. letter, border: lean/GLOSSARY.md. A thread is the invariant along a chain with its parameters
(Honest/Thread/Thr.lean). A member is a sub-protocol of a chain's flat list, numbered from 0.
-/
import AtFullSide.K14.FiveAtBase
import Johnson.Desc.ProofFile.Honest.K12.AtFile.TreesAtShared
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Chain Place Alike₂)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.K12.Seat (tests last)
open ProofFile (Pub Ground SecondHashFunctionArgument)
open ProofFile.Honest ProofFile.Honest.K14
open ProofFile.Honest.K12 (TestJob)
open ProofFile.Honest.K12.AtFile (tableShared fixedShared treesU_head treesU_at_shared treesO_at_shared)
open ProofFile.Honest.SharedThread (lettersShared)
open P2Law.ProofPlan (WP)
open P5J (AtMgA TS)
open Desc.K14 (St)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bk : ProverCoinCounts} {P₁ Wt : Type} {ℓ : WitLens Wt} {N : NumbersS}
  {shape : Nat → St → Bool} {nothingLeft : St → Bool} {order : St → Prop}
  {fixed : Fmt.TreeSource → Nat} {n₁ n₂ : Nat} {Kp : Place → St → St → Prop}

/-- **The fields treesU and treesO at lettersShared, where the letter table is tableShared.** L
stands for the letters, by the equation hL. General in the prover H and in the two readers. -/
theorem trees_tabled {W₀ Rc Tr X₀ X : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {H : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ X} {weights : W₀ → Weights} {rand : Rc → TableRand}
    {JU JO : TestJob (Common W₀ Rc TableKey) X₀} {own₀ : X₀}
    {Mg : Common W₀ Rc TableKey → MeaningS St P₁ Wt}
    {wit : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt}
    {Vd : Common W₀ Rc TableKey → Prop} {Rd : Nat → Common W₀ Rc TableKey → St → Prop}
    {w : Common W₀ Rc TableKey}
    {L : SharedThread.Letters Bk St ProofFile.Cl W₀ Rc TableKey X₀ P₁ Wt}
    (hL : L = lettersShared Zp Np cF H N Mg shape nothingLeft order wit
      (tableShared (qAt Zp Np) weights rand JU JO own₀) fixed n₁ n₂ Vd Rd Kp w)
    (letters : Asked ℓ L (qAt Zp Np) (sentWithU Zp Np) Zp.p.chains (tests Np) last
      (holds2 (qAt Zp Np) weights rand))
    (h0 : fixed (.own 0) = 1) (h1 : ∀ i, i < 2 → fixed (.own (1 + i)) = 4) :
    TreesLaid L.thread 2 (jobU ⟨qAt Zp Np, 0⟩) (witOf (qAt Zp Np) weights rand) ∧
      TreesLaid L.thread 5 (jobOmega ⟨qAt Zp Np, 0⟩) (witOf (qAt Zp Np) weights rand) := by
  obtain ⟨layO, hQ⟩ := plan2_sentWithU h
  have hu := treesU_head h.toAtMg
  have e := letters_eq letters
  have hb : List.Forall₂ Alike₂ WP.shared.blocksInOrder L.thread.bs := by
    rw [hL]
    exact (planAlike_at_head h).shared
  have hl := Eq.mp (congrArg (fun T : SharedThread.Letters Bk St ProofFile.Cl W₀ Rc TableKey X₀ P₁ Wt =>
    List.Forall₂ Alike₂ WP.shared.blocksInOrder T.thread.bs) e) hb
  have f0 : (othersOf ℓ L Zp.p.chains (tests Np) last (holds2 (qAt Zp Np) weights rand)).fixed
      (.own 0) = 1 := by
    rw [hL]
    exact h0
  have f1 : ∀ i, i < 2 → (othersOf ℓ L Zp.p.chains (tests Np) last
      (holds2 (qAt Zp Np) weights rand)).fixed (.own (1 + i)) = 4 := by
    rw [hL]
    exact h1
  have tb : (othersOf ℓ L Zp.p.chains (tests Np) last (holds2 (qAt Zp Np) weights rand)).table =
      tableShared (qAt Zp Np) weights rand JU JO own₀ := by
    rw [hL]
    rfl
  exact ⟨Eq.mpr (congrArg (fun T : SharedThread.Letters Bk St ProofFile.Cl W₀ Rc TableKey X₀ P₁ Wt =>
      TreesLaid T.thread 2 (jobU ⟨qAt Zp Np, 0⟩) (witOf (qAt Zp Np) weights rand)) e)
      (treesU_at_shared hu hQ ProofFile.Cl hl f0 tb),
    Eq.mpr (congrArg (fun T : SharedThread.Letters Bk St ProofFile.Cl W₀ Rc TableKey X₀ P₁ Wt =>
      TreesLaid T.thread 5 (jobOmega ⟨qAt Zp Np, 0⟩) (witOf (qAt Zp Np) weights rand)) e)
      (treesO_at_shared hu hQ ProofFile.Cl hl f1 tb)⟩

/-- At the written description's declared rounds of the shared chain, fixedShared is 1 at the
chain's own tree 0, and 4 at its own trees 1 and 2. -/
theorem fixedShared_low :
    fixedShared P2Law.ProofPlan.declProofFull.2.1 (.own 0) = 1 ∧
      ∀ i, i < 2 → fixedShared P2Law.ProofPlan.declProofFull.2.1 (.own (1 + i)) = 4 := by
  have h : fixedShared P2Law.ProofPlan.declProofFull.2.1 (.own 0) = 1 ∧
      fixedShared P2Law.ProofPlan.declProofFull.2.1 (.own 1) = 4 ∧
      fixedShared P2Law.ProofPlan.declProofFull.2.1 (.own 2) = 4 := by decide +kernel
  refine ⟨h.1, fun i hi => ?_⟩
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  · exact h.2.1
  · exact h.2.2

/-- **The five at a member b, 1 ≤ b ≤ 8, at the prover that onlineProverFromPublicFiles returns at the filling, where the
letter table is tableShared.** L stands for the letters, by the equation hL. The premises are
five_at_base's without treesU and treesO, and trees_tabled's two on the letter fixed. -/
theorem five_at_base_tabled {W₀ : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (I : WiderIn W₀) (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o' S O) = .ok A)
    {JU JO : TestJob (Common W₀ IndexCommitterCoins TableKey) Unit}
    {Mg : Common W₀ IndexCommitterCoins TableKey → MeaningS St P₁ Wt}
    {wit : Coins Bk → Common W₀ IndexCommitterCoins TableKey → List Fmt.Drawn → Wt}
    {Vd : Common W₀ IndexCommitterCoins TableKey → Prop} {Rd : Nat → Common W₀ IndexCommitterCoins TableKey → St → Prop}
    {w : Common W₀ IndexCommitterCoins TableKey}
    {L : SharedThread.Letters Bk St ProofFile.Cl W₀ IndexCommitterCoins TableKey Unit P₁ Wt}
    (hL : L = lettersShared Zp Np cF A.H N Mg shape nothingLeft order wit
      (tableShared (qAt Zp Np) (I.weights Zp) (randNow (qAt Zp Np)) JU JO ()) fixed n₁ n₂ Vd Rd Kp
      w)
    (letters : Asked ℓ L (qAt Zp Np) (sentWithU Zp Np) Zp.p.chains (tests Np) last
      (holds2 (qAt Zp Np) (I.weights Zp) (randNow (qAt Zp Np))))
    (h0 : fixed (.own 0) = 1) (h1 : ∀ i, i < 2 → fixed (.own (1 + i)) = 4)
    (tenant : Function.Injective N.tenant)
    (five : FiveFields (qAt Zp Np) (fun v => v = w ∧ Vd v) (fun v => A.H.storedWords v.w₀ v.rc)
      (I.weights Zp) (randNow (qAt Zp Np)))
    (book : ∀ e ∈ Bk.ahead, e.spender = ⟨place 8, 0⟩ → e.once = true →
      e.owner = ⟨sendPlace 5, 0⟩ ∧ e.start = ⟨0, offsetOf (jobOmega ⟨qAt Zp Np, 0⟩).Q.codes
        (jobOmega ⟨qAt Zp Np, 0⟩).Q.sent (jobOmega ⟨qAt Zp Np, 0⟩).sort 1⟩)
    (Said : Nat → Coins Bk → Mid (Common W₀ IndexCommitterCoins TableKey) Unit → Prop)
    (fall : Nat → St → List Fmt.Drawn → Option String)
    {R₀ : Nat → Common W₀ IndexCommitterCoins TableKey → St → Prop}
    {cs : List (RiderCl (Common W₀ IndexCommitterCoins TableKey) St)}
    (hr : ∀ b v s, Rd b v s ↔ R₀ b v s ∧ ridersOf cs b v s) (b : Nat) (hb1 : 1 ≤ b) (hb8 : b ≤ 8)
    (h₀ : ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' → R₀ (b + 1) m.st.input s')
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy L.thread b c)
    (hl : ∀ c ∈ cs, c.lo = b + 1 → LaysAtS L.thread Said b c) :
    PlaysS L.thread Said b ∧ BehindS L.thread Said b ∧ ExchangeS L.thread Said b ∧
      RidesPastS L.thread Said b ∧ AcceptedS L.thread Said fall b := by
  obtain ⟨tU, tO⟩ := trees_tabled h hL letters h0 h1
  subst hL
  exact five_at_base h I o' S O hA letters tenant tU tO five book Said fall hr b hb1 hb8 h₀ hst hl

/-- **The five at a member b, 1 ≤ b ≤ 8, at the prover that onlineProverFromPublicFiles returns at the filling, at
letters at which Asked holds**: this kind's makers laid over Mg₀, shape₀, rest, Kp₀; the letter
table is tableShared. L stands for the letters, by the equation hL. -/
theorem five_at_base_laid {W₀ : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (I : WiderIn W₀) (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o' S O) = .ok A)
    {JU JO : TestJob (Common W₀ IndexCommitterCoins TableKey) Unit}
    {Mg₀ : Common W₀ IndexCommitterCoins TableKey → MeaningS St P₁ Wt} {shape₀ : Nat → St → Bool}
    {rest : Coins Bk → Common W₀ IndexCommitterCoins TableKey → List Fmt.Drawn → Wt}
    {Kp₀ : Place → St → St → Prop}
    {Vd : Common W₀ IndexCommitterCoins TableKey → Prop} {Rd : Nat → Common W₀ IndexCommitterCoins TableKey → St → Prop}
    {w : Common W₀ IndexCommitterCoins TableKey}
    {L : SharedThread.Letters Bk St ProofFile.Cl W₀ IndexCommitterCoins TableKey Unit P₁ Wt}
    (hL : L = lettersShared Zp Np cF A.H N (fun v => mgWords ℓ (qAt Zp Np) N (Mg₀ v))
      (form2 (qAt Zp Np) shape₀) nothingLeft (fun s => OnBytes.Means.InOrder s.st)
      (witL ℓ (qAt Zp Np) (sentWithU Zp Np)
        (holds2 (qAt Zp Np) (I.weights Zp) (randNow (qAt Zp Np))) rest)
      (tableShared (qAt Zp Np) (I.weights Zp) (randNow (qAt Zp Np)) JU JO ()) fixed n₁ n₂ Vd Rd
      (kp2 (qAt Zp Np) (sentWithU Zp Np) Kp₀) w)
    (h0 : fixed (.own 0) = 1) (h1 : ∀ i, i < 2 → fixed (.own (1 + i)) = 4)
    (tenant : Function.Injective N.tenant)
    (five : FiveFields (qAt Zp Np) (fun v => v = w ∧ Vd v) (fun v => A.H.storedWords v.w₀ v.rc)
      (I.weights Zp) (randNow (qAt Zp Np)))
    (book : ∀ e ∈ Bk.ahead, e.spender = ⟨place 8, 0⟩ → e.once = true →
      e.owner = ⟨sendPlace 5, 0⟩ ∧ e.start = ⟨0, offsetOf (jobOmega ⟨qAt Zp Np, 0⟩).Q.codes
        (jobOmega ⟨qAt Zp Np, 0⟩).Q.sent (jobOmega ⟨qAt Zp Np, 0⟩).sort 1⟩)
    (Said : Nat → Coins Bk → Mid (Common W₀ IndexCommitterCoins TableKey) Unit → Prop)
    (fall : Nat → St → List Fmt.Drawn → Option String)
    {R₀ : Nat → Common W₀ IndexCommitterCoins TableKey → St → Prop}
    {cs : List (RiderCl (Common W₀ IndexCommitterCoins TableKey) St)}
    (hr : ∀ b v s, Rd b v s ↔ R₀ b v s ∧ ridersOf cs b v s) (b : Nat) (hb1 : 1 ≤ b) (hb8 : b ≤ 8)
    (h₀ : ∀ blk, L.thread.bs[b]? = some blk → ∀ k s m E ds y cols s',
      ThrS L.thread Said b k s m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k s m E ds y cols s' → R₀ (b + 1) m.st.input s')
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy L.thread b c)
    (hl : ∀ c ∈ cs, c.lo = b + 1 → LaysAtS L.thread Said b c) :
    PlaysS L.thread Said b ∧ BehindS L.thread Said b ∧ ExchangeS L.thread Said b ∧
      RidesPastS L.thread Said b ∧ AcceptedS L.thread Said fall b :=
  five_at_base_tabled h I o' S O hA hL
    (hL ▸ asked_laid Zp Np cF A.H N nothingLeft _ fixed n₁ n₂ Vd Rd w ℓ Mg₀ shape₀ rest Kp₀) h0 h1
    tenant five book Said fall hr b hb1 hb8 h₀ hst hl

end AtFullSide.K14

#print axioms AtFullSide.K14.trees_tabled
#print axioms AtFullSide.K14.fixedShared_low
#print axioms AtFullSide.K14.five_at_base_tabled
#print axioms AtFullSide.K14.five_at_base_laid
