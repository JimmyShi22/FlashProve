-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/K1DebtsAll.lean: THE FILE RULE's TWO DEBTS AT ALL 51 MEMBERS OF THE KIND K1 IN THE FIRST CHAIN BUT W's SENDING:
number 2 and K1.noL l d, l < 25: by K1DebtsJ.lean and k1_valuesJ_att (K1ValuesAtt.lean).

Premises. As debtsJ_at and k1_valuesJ_head: the head, the base, the thread's list, first tree and start; hyes, the run on shapes;
hs, a side at the member. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.K1DebtsJ
import Johnson.AtFull.Shape.K1ValuesAtt
import Johnson.Desc.ProofFile.Honest.K1.Seated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open ProofFile.Honest (Thread Coins Mid ProverCoinCounts AcceptedJ NextJ shapeJ)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **K1's record gives a side at its member**: the half that stands at the job's place. -/
theorem side_of_seated {Cells Tok W₀ Rc Xi Tr P Xo : Type} {L : ProofFile.Honest.FirstThread.Letters Bk ProofFile.Cl W₀ Rc Xi Tr Xo P Cells Tok VerifiableInference.Desc.Sound.MsgT}
    {b : Nat} {blk : VerifiableInference.Desc.Block S ProofFile.Cl} {wit} {J} {own₀ sort arr seats₀ ms rad}
    (h : ProofFile.Honest.K1.K1Seated L b blk wit J own₀ sort arr seats₀ ms rad) : SideAt L.thread b := by
  intro blk' hb'
  have e : blk' = blk := Option.some.inj (Eq.trans hb'.symm h.member)
  subst e
  rw [h.shape.1]
  exact ⟨_, h.half⟩

/-- **K1's 51 IN THE FIRST CHAIN.** -/
theorem k1_debtsJ_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (T : Thread Bk S ProofFile.Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String) (hbs : T.bs = cF.blocksInOrder) (hft : T.ft = 0)
    (hs₀ : ∀ k w hd s₀, T.begun k w hd s₀ → ∃ p, s₀ = ProofFile.startS Zp p) {a₀ : ShA}
    (hyes : (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes a₀ 358 = true) {b : Nat}
    (hb : b = 2 ∨ ∃ l d, l < 25 ∧ b = VerifiableInference.Desc.K1.noL l d) (hs : SideAt T b) :
    AcceptedJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀) fall b ∧
      NextJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀) fall b := by
  rcases hb with rfl | ⟨l, d, hl, rfl⟩
  · exact k1_debtsJ_free h hB T Said fall hbs hyes (Or.inl rfl) hs
  · cases d with
    | true =>
      exact k1_debtsJ_free h hB T Said fall hbs hyes (Or.inr (Or.inl ⟨l, hl, rfl⟩)) hs
    | false =>
      by_cases h24 : l = 24
      · subst h24
        exact k1_debtsJ_head h hB T Said fall hbs hft hs₀ hyes hs
      · by_cases he : l % 2 = 0
        · exact k1_debtsJ_free h hB T Said fall hbs hyes
            (Or.inr (Or.inr ⟨l, by omega, he, rfl⟩)) hs
        · obtain ⟨k, rfl⟩ : ∃ k, l = 2 * k + 1 := ⟨l / 2, by omega⟩
          have e : VerifiableInference.Desc.K1.noL (2 * k + 1) false = 14 * (2 * k + 1) + 5 := by
            simp [VerifiableInference.Desc.K1.noL, IM.k1Ix, h24]
          rw [e] at hs ⊢
          exact debtsJ_at h hB T Said fall hbs hyes (by omega) hs
            (k1_valuesJ_att h hB T Said fall hbs hft hs₀ (by omega) (fitsAt_of_side T hs) hyes)

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.side_of_seated
#print axioms Johnson.AtFull.Shape.k1_debtsJ_at
