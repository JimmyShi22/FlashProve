-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/MarksAtHeadBlocks.lean: THE HONEST SIDE's FRAME: THE FIELD hM AT THE FRAME's AUTHORS'
OWN LIST `marksHead`, AT STRINGS OF HASH BLOCKS, WITH THE LOOKUPS' MARKS' BOUND ALONE STILL ASKED. A
lemma; NONE OF THE LIBRARY's GOALS. A joining: one call more than Johnson/P1K8R/MarksAtHead.lean.
Nothing on completeness, soundness or hiding.

  **`marksHead_hM_owners`**   `marksHead_hM_left` (MarksAtHead.lean); h6_blocks
      (Johnson/Desc/ProofFile/Honest/Law/MarksHeadK6Blocks.lean), which calls the output head's own
      rounds' authors' part4Marks_debt_blocks (Honest/K6/Law/K6MarksBlocks.lean); the library's
      IM.Open.blank (Johnson/IMR/SeatOpen.lean)
Kin. The frame's authors' marksHead_hM_blocks6 (MarksHeadK6Blocks.lean): the same end, with eight
premises on the four other lists still asked (four on kinds, four on bounds): this is that lemma
with seven of the eight met.
Limits. All that Johnson/P1K8R/MarksAtHead.lean says under "Limits" stands. AT ONE KIT OF
CHALLENGES: Run.ckP .two. hK3 IS A HYPOTHESIS. THE END SETS qMHead's SECOND LETTER, which
`falls_five_by_owner` (Johnson/P1K8R/FallsAtLists.lean) has free (kapH): whoever calls the two side
by side sets kapH so. WHAT hK6 IS EXCHANGED FOR IS NO MORE THAN ITS OWNERS SAY OF IT: by h6_blocks'
own head it is a check that two forms meet, and no more; THE TWO MARKS' STATED SHARES ARE NOT HELD
AT THIS KIT: they lack the factor Iop.kapSl 128 ^ 3: their numerators alone are spent; and
part4Marks_debt_blocks speaks of a chance: by its authors' head no reviewer who owns such statements
has seen it, and nothing there is a result before that. It is conditional on the head; the law on
one round's strings of hash blocks is named, not derived. No number is evaluated. One option is
raised, for the one theorem (maxHeartbeats). No tactic that searches.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.MarksAtHead
import Johnson.Desc.ProofFile.Honest.Law.MarksHeadK6Blocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open OnBytes.Maker (RDT WholeD)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open ProofFile.Honest (Mark MarkDebt KindFits marksHead qMHead)
open scoped ENNReal

set_option maxHeartbeats 4000000 in
/-- **hM AT THE LIST AS IT STANDS, AT THE KIT Run.ckP .two, WITH ONE AUTHOR's BOUND STILL ASKED**:
hK3: the lookups' marks. `marksHead_hM_left` (Johnson/P1K8R/MarksAtHead.lean) with hK6 := the
frame's authors' h6_blocks. ITS END SETS qMHead's SECOND LETTER: the library's factor for the
sampler's bias, cubed, over p ^ 3. -/
theorem marksHead_hM_owners {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (kapL : ℝ≥0∞)
    {pre₁ : List (Block P5J.TS ProofFile.Cl)} {e₁ : Block P5J.TS ProofFile.Cl}
    (cut : cF.blocksInOrder = pre₁ ++ [e₁]) {PM : Block P5J.TS ProofFile.Cl → List Fmt.Drawn → Prop}
    (hK3 : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (ProofFile.Honest.K3.Good.k3Marks Zp Bs.G₀).filter (fun m => m.place == b.place),
      ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      MarkDebt (_root_.Run.ckP .two) mk dsb (PM b) ((mk.share.num : ℝ≥0∞) * kapL)) :
    ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (marksHead Zp Bs.G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      MarkDebt (_root_.Run.ckP .two) mk dsb (PM b)
        (qMHead kapL (Iop.kapSl 128 ^ 3 / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)) b mk) := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  exact marksHead_hM_left h hB kapL _ cut hK3 (ProofFile.Honest.h6_blocks h O.blank cut)

end P1K8

#print axioms P1K8.marksHead_hM_owners
