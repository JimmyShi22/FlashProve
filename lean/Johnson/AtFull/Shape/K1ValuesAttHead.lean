-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/K1ValuesAttHead.lean: k1_valuesJ_att (K1ValuesAtt.lean) in the form of the field
readsAtt of SortValuesLeft: at every odd link below 24, general in the thread, and at lettersHead's
thread at all its letters, from the test halved.

Limits. The run on shapes and halved stay premises. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.K1ValuesAtt
import Johnson.Desc.ProofFile.Honest.Thread.FitsAll
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest (Shape Thread ProverCoinCounts Coins Mid Prover Local ValuesJ FitsAt shapeJ halved)
open ProofFile.Honest.FirstThread (Script lettersHead WtF)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- **The field readsAtt, at any thread on the chain.** -/
theorem readsAtt_values (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {V W X Pb : Type} {Bk : ProverCoinCounts}
    (T : Thread Bk S ProofFile.Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String) (hbs : T.bs = cF.blocksInOrder) (hft : T.ft = 0)
    (hs₀ : ∀ k w hd s₀, T.begun k w hd s₀ → ∃ p, s₀ = ProofFile.startS Zp p) {a₀ : ShA}
    (hyes : (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes a₀ 358 = true)
    (h4 : halved cF.blocksInOrder T.hs = true) :
    ∀ l, l < 24 → l % 2 = 1 →
      ValuesJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀)
        (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) fall (14 * l + 4 + 1) := by
  intro l hl ho
  obtain ⟨k, rfl⟩ : ∃ k, l = 2 * k + 1 := ⟨l / 2, by omega⟩
  exact k1_valuesJ_att h hB T Said fall hbs hft hs₀ (k := k) (by omega)
    (ProofFile.Honest.fitsAt_of_halved T (by rw [hbs]; exact h4) _) hyes

/-- **The field readsAtt at lettersHead's thread, at all its letters.** -/
theorem readsAtt_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String) {a₀ : ShA}
    (hyes : (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes a₀ 358 = true)
    (h4 : halved cF.blocksInOrder H.first = true) :
    ∀ l, l < 24 → l % 2 = 1 →
      ValuesJ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀)
        (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) fall (14 * l + 4 + 1) :=
  readsAtt_values h hB _ Said fall rfl rfl (fun _ _ _ _ h0 => ⟨_, h0⟩) hyes h4

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.readsAtt_values
#print axioms Johnson.AtFull.Shape.readsAtt_at_head
