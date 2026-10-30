-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/OField.lean: the five sentences at member 10 at the letter that keeps the
field, `SaidField T BaseNil` (Honest/Thread/SaidField.lean), and what that letter asks of the member.

  `field_of_saidNil`   at the letter, at a stand, the field holds the columns of the fold: no base in front: a
                 chain started at nothing
  `treesNext_ten`   `TreesNext` at 10: what `saidNext_field` asks of the member
  `five_at_said`   `five_at_letters` at that letter: the premise on the field is gone

Limits.
- NOT IN FRONT OF A LAW OVER COINS.
- That a stand meets the letter is not said here: `saidNext_field` carries it, under `opensAvailable` and `DepthsAt` at the
  border behind.
- Nothing on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OFiveAt
import Johnson.Desc.ProofFile.Honest.Thread.SaidField

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Place Chain)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open Desc.K14 (St blocks)
open ProofFile.Honest
open ProofFile.Honest.K14 (jobOmega sendPlace WitLens)
open OnBytes.Means (Words)
open ProofFile.Honest.K12
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.SharedThread (lettersShared)
open Johnson.G (proofSendsFull)

/-- **At the letter, at a stand, the field holds just the columns of the fold.** -/
theorem field_of_saidNil {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb) {b : ℕ}
    {k : Coins Bk} {s : S} {m : Mid W X} {E : Env}
    (u : ThrS T (SaidField T BaseNil) b k s m E) (cols : List VerifiableInference.Desc.OpenedColumn)
    (hc : T.colsTo b m E = .ok cols) : m.opened = some cols := by
  obtain ⟨base, cols', hB, hc', ho⟩ := opened_of_saidField T u.1 u.2
  obtain rfl : base = [] := hB
  obtain rfl : cols' = cols := Except.ok.inj (hc'.symm.trans hc)
  exact ho

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {pO : P12}
  {x₀ : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X P₁ Wt : Type} {Bk : ProverCoinCounts}
  {H : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ X} {N : NumbersS}
  {Mg : Common W₀ Rc TableKey → MeaningS St P₁ Wt} {shape : ℕ → St → Bool} {nothingLeft : St → Bool}
  {order : St → Prop} {wit : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt}
  {table : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table}
  {fixed : Fmt.TreeSource → ℕ} {n₁ n₂ : ℕ} {Vd : Common W₀ Rc TableKey → Prop}
  {Rd : ℕ → Common W₀ Rc TableKey → St → Prop} {Kp : Place → St → St → Prop}
  {w : Common W₀ Rc TableKey} {ℓ : WitLens Wt} {Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt}
  {wts : W₀ → Weights} {rnd : Rc → TableRand}
  {rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Words Cb.Gl.E}
  {JU : TestJob (Common W₀ Rc TableKey) X₀} {own₀ : X₀}

/-- The thread's letters. -/
local notation "𝐋" => lettersShared Zp Np cF H N Mg shape nothingLeft order wit table fixed n₁ n₂ Vd Rd Kp w

set_option maxHeartbeats 1000000 in
/-- **The five sentences at member 10, at the letter that keeps the field.** -/
theorem five_at_said (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hO : (fourOf Np).O = some pO)
    (hB : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok Bk)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (G : LetterO N Mg wit table fixed Zp Np pO
      [b1, b2, b3, b4, b5, b6, b7, b8] ℓ Mg₀ wts rnd rest JU own₀)
    (K : LettersTen (𝐋) (SaidField (𝐋).thread BaseNil))
    (hhalf : (H.shared.find? fun g => g.place == pO.place) =
      some (proverSideOfProximityTest (jobDoorO (X₀ := X₀) Zp Np pO [b1, b2, b3, b4, b5, b6, b7, b8] wts rnd).toRun.toTest :
        Placed Empty _ X₀).needsField)
    (fall : ℕ → St → List Fmt.Drawn → Option String) :
    PlaysS (𝐋).thread (SaidField (𝐋).thread BaseNil) 10 ∧
      BehindS (𝐋).thread (SaidField (𝐋).thread BaseNil) 10 ∧
      ExchangeS (𝐋).thread (SaidField (𝐋).thread BaseNil) 10 ∧
      RidesPastS (𝐋).thread (SaidField (𝐋).thread BaseNil) 10 ∧
      AcceptedS (𝐋).thread (SaidField (𝐋).thread BaseNil) fall 10 :=
  five_at_letters h hO hB b1 b2 b3 b4 b5 b6 b7 b8 hb G _ K hhalf
    (fun _ _ _ _ u cols hc => field_of_saidNil _ u cols hc) fall

set_option maxHeartbeats 1000000 in
/-- **`TreesNext` at member 10**: what the letter's carrying asks of the member. -/
theorem treesNext_ten (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hO : (fourOf Np).O = some pO)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (G : LetterO N Mg wit table fixed Zp Np pO
      [b1, b2, b3, b4, b5, b6, b7, b8] ℓ Mg₀ wts rnd rest JU own₀)
    (hhalf : (H.shared.find? fun g => g.place == pO.place) =
      some (proverSideOfProximityTest (jobDoorO (X₀ := X₀) Zp Np pO [b1, b2, b3, b4, b5, b6, b7, b8] wts rnd).toRun.toTest :
        Placed Empty _ X₀).needsField)
    (c5 : takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega ⟨K1.qAt Zp Np, 0⟩) = true) :
    TreesNext (𝐋).thread (SaidField (𝐋).thread BaseNil) 10 := by
  obtain ⟨blk, H'⟩ := standO_at h hO b1 b2 b3 b4 b5 b6 b7 b8 hb G (SaidField (𝐋).thread BaseNil) hhalf c5
    (fun _ _ _ _ u cols hc => field_of_saidNil _ u cols hc)
  obtain ⟨s₁, t₁, l, hs₀⟩ := stages_O
  have hstg : (jobDoorO (X₀ := X₀) Zp Np pO [b1, b2, b3, b4, b5, b6, b7, b8] wts rnd).toRun.toTest.p.nums.stages =
      s₁ :: t₁ :: l := by
    show pO.nums.stages = _
    rw [ProofFile.Honest.K12.Light.nums_head_O h.toAtMg hO]
    exact hs₀
  intro blk' hblk' k s m E ds y cols hA _ hd hM
  rw [H'.member] at hblk'
  cases hblk'
  exact trees_head_O h.toAtMg hO _ _ wts rnd JU own₀ Zp.p.chains _ H' (fixedO_at h G) s₁ t₁ l hstg k s m E
    ds y cols hA hd hM

end ProofFile.Honest.K12.AtFile

end

#print axioms ProofFile.Honest.K12.AtFile.field_of_saidNil
#print axioms ProofFile.Honest.K12.AtFile.five_at_said
#print axioms ProofFile.Honest.K12.AtFile.treesNext_ten
