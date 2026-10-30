-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Law/AgainAtReads.lean: THE TWO ITEMS THAT ARE OPEN IN FRONT OF THE
KIND K1's READS AND OWED AGAIN BEHIND THEM: `pin l 0` AND `constr l small`: `ExchangeAtS` at
`K1.noL l false`, by ProofFile's `exchangeAtS_again`, from `BehindS` and the item's passing.

  `open_reads_B`, `open_reads`     both are open in front: by Lean's kernel
  `exchangeAtS_pin0_reads`, `exchangeAtS_constr_reads`

Limits. Nothing on any property. Full size, the format's second hash function.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.BehindAtFifty

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Strs Place KindName)
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

set_option maxRecDepth 1000000 in
/-- **BOTH ARE OPEN IN FRONT OF THE READS**, by Lean's kernel. -/
theorem open_reads_B : ((List.range 25).all fun l =>
    (fwdOpen (VerifiableInference.Desc.First.start P5J.At.links)
      (FirstRows.rows P5J.At.links P5J.At.ps) (K1.noL l false)).contains (Item.pin l 0) &&
    (fwdOpen (VerifiableInference.Desc.First.start P5J.At.links)
      (FirstRows.rows P5J.At.links P5J.At.ps) (K1.noL l false)).contains (Item.constr l .small)) =
    true := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where) (w : Local W₀ Rc ProofFile.Inst Tr)
  {ν : Nat} {st : Nat → TS → Prop} {R : Nat → Option OnBytes.Model.Forest.Heard → Prop}

/-- **`pin l 0` OWED AGAIN BEHIND THE READS.** -/
theorem exchangeAtS_pin0_reads (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {l : ℕ} (hl : l < 25) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said (K1.noL l false)
      (Item.pin l 0) := by
  have t := List.all_eq_true.1 open_reads_B l (List.mem_range.2 hl)
  rw [Bool.and_eq_true] at t
  have hi : Item.pin l 0 ∈ fwdOpen (VerifiableInference.Desc.First.start P5J.At.links)
      (FirstRows.rows P5J.At.links P5J.At.ps) (K1.noL l false) := by
    simpa only [List.contains_iff_mem] using t.1
  have hp := place_fifty hl false
  have hpiece : (IM.k1PlaceL l false).piece ≠ 1 := by
    show IM.k1Ix l false + 1 ≠ 1
    simp only [IM.k1Ix]
    split <;> simp
  have hlen : K1.noL l false ≤ cF.blocksInOrder.length := by
    rw [head_len h]
    rcases noL_cases hl false with ⟨-, -, c⟩ | ⟨-, -, c⟩ | ⟨-, -, c⟩ | ⟨-, -, c⟩ <;> omega
  refine exchangeAtS_again _ _ hi
    (k1_behindS_fifty h H Q test carryX item n₁ n₂ Vd G take P11 p12 P13 w Said hl false)
    (ridesPastAtS_of _ _ (ridesPastAt_pin_older h H Q test carryX item n₁ n₂ 339 Vd _ _ w l 0
      (head_older_k1 h H Q test carryX item n₁ n₂ 339 Vd _ _ w hlen fun s s' a => ?_)))
  have a' := (head_keeps h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
    (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hp s s').1 a
  exact k1_keeps_rest ((fHead_K1_later Zp cF G take P11 p12 P13 (l := l) rfl hpiece s s').1
    a'.1.1.1.1.1).1

/-- **`constr l small` OWED AGAIN BEHIND THE READS.** -/
theorem exchangeAtS_constr_reads (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {l : ℕ} (hl : l < 25) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R))
      (kpBy (fHeadJ Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said (K1.noL l false)
      (Item.constr l .small) := by
  have t := List.all_eq_true.1 open_reads_B l (List.mem_range.2 hl)
  rw [Bool.and_eq_true] at t
  have hi : Item.constr l .small ∈ fwdOpen (VerifiableInference.Desc.First.start P5J.At.links)
      (FirstRows.rows P5J.At.links P5J.At.ps) (K1.noL l false) := by
    simpa only [List.contains_iff_mem] using t.2
  exact exchangeAtS_again _ _ hi
    (k1_behindS_fifty h H Q test carryX item n₁ n₂ Vd G take P11 p12 P13 w Said hl false)
    (ridesPastAtS_of _ _ fun _ _ _ _ _ _ _ _ _ h0 => h0)

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.open_reads_B
#print axioms ProofFile.Honest.K1.exchangeAtS_pin0_reads
#print axioms ProofFile.Honest.K1.exchangeAtS_constr_reads
