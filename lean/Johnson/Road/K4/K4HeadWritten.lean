-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Road/K4/K4HeadWritten.lean: THE TWO CONDITIONS ON THE PUBLIC FILES UNDER WHICH K4's TESTS
ON ITS
PLAN ARE THEOREMS (`WrittenAt Zp`; the written cut of the first chain) FOLLOW FROM THE ONE HEAD
`P5J.AtMg` (Johnson/P5J/AtMg.lean), OVER THE VERIFIER's ENTRY TESTS' LIST OF FOURTEEN ROWS
(GLOSSARY.md, "entry tests"). Five theorems: calls. Nothing is evaluated.

  **`written_of_head`**: `WrittenAt Zp`: `writtenAt_of_laid`
    (Johnson/Road/K4/K4PlanOfLaid.lean) at the head's fields scope and laid.
  **`cut_of_head`**: `cutOf cF.blocksInOrder = cutFirstFull`: `pins_of_laid`
    (Johnson/Goal/Skeleton/PinsOfLaid.lean), its second half; the IOP as written in Lean at the
    head's letters has cF as its first chain by its make.
  `laid_of_head`: the closed parameters' reader of the listed seats returns something
    (`laid_written`, Johnson/Road/K4/K4PinsPaid.lean).
  **`nextFits_head`**, **`pins_head`**: the fields nextFits and pins of `K4Cond`
    (Johnson/Road/K4/K04Cond.lean), to the letter, FROM THE HEAD `P5J.AtMgA` ALONE; pins at the L
    that the reader returns (a premise).

KIN: `P5J.LaidAt.laidPOf`, `P5J.AtMg.pins` (Johnson/P5T/FenceAtMg.lean): the same
two steps, above a file that wants some 11 GB to compile: not imported.

Limits. K04_law IS NOT PROVED BY THIS. IT NEEDS THE NINTH AND THE TENTH OF THE VERIFIER's ENTRY
TESTS (`LPFD.lawsAsk`), which compare the plan and the cut with the written values. The list
has fourteen rows; its first eight ask neither.
A MEMBER OF THE HEAD IS PROVED AT `storedPublicFiles` AND `zGap` ALONE (AT secondHashFunction; SIDE LIBRARY
AtFullSide/Top/). The two ends speak at the wider
meaning: they count only when the bridge to the meaning that counts is paid. The full size alone.

-/
import Johnson.Road.K4.K4PlanOfLaid
import Johnson.Road.K4.K4PinsPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes.Maker (WholeD)
open VerifiableInference.PlanWritten (cutFirstFull)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.Sound

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **Under the head, over the list of entry tests: five parts of the public parameters are
the written values.** -/
theorem written_of_head (h : P5J.AtMg o Z D r Zp Np cF) : WrittenAt Zp :=
  writtenAt_of_laid h.scope h.laid

/-- **Under the head, over the list of entry tests: the first chain's cut into sub-protocols
is the written one.** -/
theorem cut_of_head (h : P5J.AtMg o Z D r Zp Np cF) :
    VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull :=
  (P5J.pins_of_laid h.scope h.laid).2

/-- Under the head, over the entry tests: the reader of the listed seats returns something. -/
theorem laid_of_head (h : P5J.AtMg o Z D r Zp Np cF) : ∃ L, P5J.At.laid? Zp = some L :=
  laid_written (written_of_head h)

variable {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **THE FIELD nextFits OF `K4Cond`, from the head alone**, over the list of entry tests. -/
theorem nextFits_head (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (L : VerifiableInference.Desc.K12.Door.Laid) :
    ∀ g, g < 12 →
      Rec.nextFitsB (k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).cs
      (k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).d12.M
      ((k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).N.msgsAt
      (flatPlacesOf linksFull true)[28 * g + 4 + 1]?)
        (k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).N.indexNo
        (k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).free0
        (k4DataWide hA.𝔇 (eAll Zp cF L) mgBase).fvs (2 * g) = true :=
  nextFits_paid hA L (written_of_head hA.toAtMg) (cut_of_head hA.toAtMg)

/-- **THE FIELD pins OF `K4Cond`, from the head alone**, over the list of entry tests, at the
L that the closed parameters' reader returns. -/
theorem pins_head (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (L : VerifiableInference.Desc.K12.Door.Laid) (hL : P5J.At.laid? Zp = some L) :
    ∀ {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)},
    IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (Desc.K14.Law.seatZ Zp Np) (Desc.K14.Law.secondAt Zp Np) →
    ∀ g, g < 12 → ∀ x b, K4Here cF Zp Bs.G₀ g x b → firstFastB Zp g = true →
      K4PinsTests hA.𝔇 (eAll Zp cF L) Zp (28 * g + 4) g (parOf x) :=
  pins_paid hA L hL (written_of_head hA.toAtMg) (cut_of_head hA.toAtMg)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.written_of_head
#print axioms OnBytes.Road.K4.cut_of_head
#print axioms OnBytes.Road.K4.laid_of_head
#print axioms OnBytes.Road.K4.nextFits_head
#print axioms OnBytes.Road.K4.pins_head
