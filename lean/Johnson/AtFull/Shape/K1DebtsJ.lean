-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/K1DebtsJ.lean: THE FILE RULE's TWO DEBTS AT ONE MEMBER OF THE FIRST CHAIN, OFF THE TABLE OF STEPS ON SHAPES,
AND AT THE KIND K1's MEMBERS. first_chain_debts_halved (RuleAtTable.lean) asks the values at all 358 members; these laws ask them at
the member at hand, and a side at that member alone.

  debtsJ_at        any member b < 358: from the run on shapes, a side at b, and ValuesJ at b: AcceptedJ and NextJ at b.
  k1_debtsJ_free   at 38 of K1's 51 members, those with no test on values.
  k1_debtsJ_head   at the head's reads (342).

Premises. hyes: the run on shapes. hhalf: a side stands at the member's place. For the 12 attention reads the values stay a premise of
debtsJ_at. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.K1ValuesHead
import Johnson.AtFull.Shape.RuleAtTable
import Johnson.Desc.ProofFile.Honest.Thread.FitsAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open ProofFile.Honest (Thread Coins Mid ProverCoinCounts ValuesJ FitsAt AcceptedJ NextJ shapeJ fitsAt_member halved_of_half
  acceptedJ_of_shapeV nextJ_of_shapeV)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {V W X Pb : Type} {Bk : ProverCoinCounts}

/-- A side at the member at number b. -/
def SideAt (T : Thread Bk S ProofFile.Cl V W X Pb) (b : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∃ g, (T.hs.find? fun g => g.place == blk.place) = some g

theorem fitsAt_of_side (T : Thread Bk S ProofFile.Cl V W X Pb) {b : Nat} (hs : SideAt T b) : FitsAt T b := by
  cases hb : T.bs[b]? with
  | none =>
    intro blk hblk
    rw [hb] at hblk
    cases hblk
  | some blk =>
    obtain ⟨g, hg⟩ := hs blk hb
    exact fitsAt_member T hb (halved_of_half hg)

/-- **THE TWO DEBTS AT ONE MEMBER.** -/
theorem debtsJ_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (T : Thread Bk S ProofFile.Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String) (hbs : T.bs = cF.blocksInOrder) {a₀ : ShA}
    (hyes : (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes a₀ 358 = true) {b : Nat} (hb : b < 358)
    (hs : SideAt T b)
    (hV : ValuesJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀)
      (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) fall b) :
    AcceptedJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀) fall b ∧
      NextJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀) fall b :=
  ⟨acceptedJ_of_shapeV T Said _ hb hyes (by rw [hbs]; exact (table_all h hB b hb T.ft).2)
      (fitsAt_of_side T hs) hV,
    nextJ_of_shapeV T Said _ hb hyes (by rw [hbs]; exact carriesU_of_V (table_all h hB b hb T.ft).1) hV⟩

theorem noL_lt {l : Nat} (hl : l < 25) (d : Bool) : VerifiableInference.Desc.K1.noL l d < 358 := by
  unfold VerifiableInference.Desc.K1.noL IM.k1Ix
  cases d <;> by_cases h : l = 24 <;> simp [h] <;> omega

/-- **38 OF K1's 51 MEMBERS: THOSE WITHOUT A TEST ON VALUES.** -/
theorem k1_debtsJ_free (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (T : Thread Bk S ProofFile.Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String) (hbs : T.bs = cF.blocksInOrder) {a₀ : ShA}
    (hyes : (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes a₀ 358 = true) {b : Nat}
    (hb : b = 2 ∨ (∃ l, l < 25 ∧ b = VerifiableInference.Desc.K1.noL l true) ∨
      (∃ l, l < 24 ∧ l % 2 = 0 ∧ b = VerifiableInference.Desc.K1.noL l false))
    (hs : SideAt T b) :
    AcceptedJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀) fall b ∧
      NextJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀) fall b :=
  debtsJ_at h hB T Said fall hbs hyes
    (by
      rcases hb with rfl | ⟨l, hl, rfl⟩ | ⟨l, hl, -, rfl⟩
      · omega
      · exact noL_lt hl true
      · exact noL_lt (by omega) false)
    hs (k1_valuesJ_free T Said _ fall Zp Bs.G₀ hb)

/-- **THE HEAD's READS.** -/
theorem k1_debtsJ_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (T : Thread Bk S ProofFile.Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String) (hbs : T.bs = cF.blocksInOrder) (hft : T.ft = 0)
    (hs₀ : ∀ k w hd s₀, T.begun k w hd s₀ → ∃ p, s₀ = ProofFile.startS Zp p) {a₀ : ShA}
    (hyes : (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes a₀ 358 = true)
    (hs : SideAt T 342) :
    AcceptedJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀) fall 342 ∧
      NextJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀) fall 342 :=
  debtsJ_at h hB T Said fall hbs hyes (by omega) hs
    (k1_valuesJ_head h hB T Said fall hbs hft hs₀ (fitsAt_of_side T hs) hyes)

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.fitsAt_of_side
#print axioms Johnson.AtFull.Shape.noL_lt
#print axioms Johnson.AtFull.Shape.debtsJ_at
#print axioms Johnson.AtFull.Shape.k1_debtsJ_free
#print axioms Johnson.AtFull.Shape.k1_debtsJ_head
