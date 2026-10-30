-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/FiveJ.lean: the closing of a segment (K10): the five statements in the form with a
family J in hand (`FiveAtBorderJ`, Honest/Thread/FiveAtBorder.lean), at J := "the run on shapes over the members in front
returns the state's shape" (`shapeJ` at the table of steps on shapes, Johnson/AtFull/Shape/), at all 25 closings of the first
chain's thread as a named term (`firstThread`).

  `k10_next_first`      `NextJ (firstThread h parts w) Said (shapeJ Zs a₀) fall b`: the family goes one member on across a closing
  **`k10_fiveJ_first`**  `FiveAtBorderJ (firstThread h parts w) Said (shapeJ Zs a₀) fall b` at each of the 25 closings

Premises beside those of `k10_five_first` (Pay/Five.lean): hB: the public part's seat makes a base Bs, at whose ground the table
stands; hyes: the run on shapes returns over all 358 members from a₀ (`Shape.yes`), a closed question at given public files
that no theorem here answers.

Limits. As Pay/Five.lean's: `ThreeLeft` is a premise. Where the thread's invariant holds at no stand of a border, or the
family at no state there, the statements hold for nothing.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.Five
import Johnson.Desc.ProofFile.Honest.K10.Pay.NextJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open Johnson.AtFull.Shape
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.Close (Par)
open P5J (TS)
open ProofFile.Honest.FirstThread

variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL (onlineProverPartsInUse I o S O) = .ok A)
  (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)

/-- **At the first thread the family on shapes goes one member on across each closing.** -/
theorem k10_next_first {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs) (l : Nat)
    (hl : l < 25) {Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop}
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) (fall : Nat → TS → List Fmt.Drawn → Option String) (a₀ : ShA)
    (hyes : (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)).yes a₀ 358 = true) :
    NextJ (firstThread h parts w) Said (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) a₀) fall
      (14 * l + IM.nAt l + 5) :=
  nextJ_at_closing h.head A.H parts.script _ _ _ _ _ _ _ _ _ w hB hl hSaid fall a₀ hyes

include hA in
/-- **The five statements with the family on shapes in hand, at each of the 25 closings of the first thread.** -/
theorem k10_fiveJ_first {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs) (l : Nat)
    (hl : l < 25) {Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop}
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) (fall : Nat → TS → List Fmt.Drawn → Option String) (a₀ : ShA)
    (hyes : (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)).yes a₀ 358 = true)
    (Left : ∀ p Qc blk, Tied h.firstChain A.Z l p Qc blk → ThreeLeftFirst I S h parts w Said l Qc blk) :
    FiveAtBorderJ (firstThread h parts w) Said (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) a₀) fall
      (14 * l + IM.nAt l + 5) :=
  fiveJ_of_five (k10_five_first I o S O hA h parts w l hl hSaid fall Left)
    (k10_next_first h parts w hB l hl hSaid fall a₀ hyes)

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.k10_next_first
#print axioms ProofFile.Honest.K10.k10_fiveJ_first
