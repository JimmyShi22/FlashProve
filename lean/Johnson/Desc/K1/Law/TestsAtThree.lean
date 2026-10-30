-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/TestsAtThree.lean: three small payers beside TestsAtCounts.lean (this folder),
for the forms of the law on the sub-protocol K1 that stand at the IOP's own data D
(k01_fifty_atThree, K01FiftyAtThree.lean, this folder). Statements with their proofs; nothing is
evaluated.

  `hOk_of_planOk`    **hOk**: where the opened IOP as written in Lean passes its own test on the
                     list of rounds, every sub-protocol of the first chain passes its own test on
                     its parameters and is shaped: `IM.blocksOk_of_planOk`, member
                     by member
  `hSeats_atThree`   **hSeats** with the piece's base counted in D (`baseD D c l d`): `hSeats_at`
                     behind `six_together` (Johnson/Desc/Sound/SixTogether.lean), which gives the
                     written rounds of which D is made
  `dkOf_written`     where the proof file's lists of sendings are the written ones, the proximity
                     test's data that are meant (`dkOf Z`, PlanThree.lean, this folder) ARE MADE,
                     and are the first tree's number with the written layout and shapes

What is not claimed. TestsAtCounts.lean's premise hC stays. NO EXAMPLE. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.TestsAtScope
import Johnson.Desc.K1.Law.K01FiftyAtThree
import Johnson.IMR.PlanOkFlat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params Johnson.G
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.Sound (linksFull six_together)
open VerifiableInference.Desc.First (S ModelPart Numbers flatPlacesOf)
open VerifiableInference.Desc.K13.Law (CountsAre seatsFull LFull MFull)
open VerifiableInference.Desc.K12.Door (K12Data laidOfChain)
open VerifiableInference.Desc.ReqLit (shapeFull)
open P5T (N0Full)
open ProofFile (Cl)
open IM (Open)

/-- **hOk.** At every letter for the second hash function. -/
theorem hOk_of_planOk {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (O : Open o pol lay KL F Z Bs base₀ c A B)
    (hp : F.planOk = true) : ∀ b ∈ c.blocksInOrder, b.planOk = true ∧ b.shaped = true := by
  intro b hb
  have h := List.all_eq_true.1 (IM.blocksOk_of_planOk O hp) b hb
  exact Bool.and_eq_true_iff.1 h

/-- **hSeats, the base counted in the IOP's own data.** -/
theorem hSeats_atThree {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {N : Numbers} {s : ReqShape}
    {links : List ModelPart} (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B) {D : WholeD} {file : String}
    (hD : (FD Z A B c).data file = .ok D) (hp : (FD Z A B c).planOk = true)
    {b₁ : Block (FD Z A B c).S₁ (FD Z A B c).Cl} {l₁ : List (Block (FD Z A B c).S₁ (FD Z A B c).Cl)}
    {b₂ : Block (FD Z A B c).S₂ (FD Z A B c).Cl} {l₂ : List (Block (FD Z A B c).S₂ (FD Z A B c).Cl)}
    {b₃ : Block (FD Z A B c).S₃ (FD Z A B c).Cl} {l₃ : List (Block (FD Z A B c).S₃ (FD Z A B c).Cl)}
    (q₁ : (FD Z A B c).first.blocksInOrder = b₁ :: l₁) (q₂ : (FD Z A B c).shared.blocksInOrder = b₂ :: l₂)
    (q₃ : (FD Z A B c).second.blocksInOrder = b₃ :: l₃)
    (hc : Bs.G₀.first.codes = codesFull2) (hs : Bs.G₀.first.shape = shapeFull)
    (hOk : ∀ b ∈ c.blocksInOrder, b.planOk = true ∧ b.shaped = true)
    (hN : N = N0Full.atBlocks s links c.blocksInOrder) (hC : CountsAre (First.toldOf c.blocksInOrder))
    {seats : List (ℕ × ℕ)} (hseats : seats = seatsFull) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ j : Fin (shapesOf (parL Z Bs.G₀ l d)).length,
      seats[N.msgsAt (flatPlacesOf linksFull true)[noL l d]? + j.val]? =
        some (seatOfMsg (parL Z Bs.G₀ l d) (baseD D c l d) j.val) := by
  obtain ⟨R₁, R₂, R₃, hDD, w₁, hRoots, -, -⟩ := six_together (W := Unit) hD hp q₁ q₂ q₃
  subst hDD
  exact hSeats_at hS hR O hc hs w₁ hOk hRoots hN hC hseats

/-- **The data that are meant are made**, and what they are. -/
theorem dkOf_written {Z : ProofFile.Pub} (hs : Z.made.proof = proofSendsFull) :
    dkOf Z = some ⟨(gpOf Z).firstTree, LFull, MFull⟩ := by
  have hc : proofSendsFull.1.codes = codesFull2 :=
    (List.cons.inj (congrArg Prod.snd PlanWritten.written_codes)).1
  have e : laidOfChain proofSendsFull.1 = some LFull := by
    rw [K12.Door.laidOfChain_is, hc]
    exact K13.Law.laid_written
  unfold dkOf dkOfChain
  rw [hs, e, K13.Law.msgs_written]
  rfl

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hOk_of_planOk
#print axioms VerifiableInference.Desc.K1.hSeats_atThree
#print axioms VerifiableInference.Desc.K1.dkOf_written
