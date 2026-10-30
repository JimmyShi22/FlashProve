-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/K1NumbersAtHead.lean: UNDER THE HYPOTHESIS `P5J.AtMg`, AT AN OPENING, THE
NUMBERS OF THE KIND K1 AT ITS PLACES ON THE LINKS OF THE FIRST CHAIN, `K1.parLater Bs.G₀.first
(K1.gpOf Zp) l pc m` (Johnson/Desc/K1/Places.lean) AND `K1.firstPar Bs.G₀.first (K1.gpOf Zp)`
(Johnson/Desc/K1/First.lean), ARE THE SAME TWO FUNCTIONS AT THE LIBRARY's PLACEHOLDER `K1.qFull`
(Johnson/Desc/K1/Law/QFull.lean) AND AT WRITTEN NUMBERS: CLOSED TERMS. The proofs combine laws of
the library with BackNumbersAtHead.lean; nothing is evaluated.

Words. `P5J.AtMg` (Johnson/P5J/AtMg.lean) is the library's hypothesis at the full size; the library
calls it "the head". Below: the hypothesis. An opening is a value of `IM.Open`
(Johnson/IMR/SeatOpen.lean).

Purpose. A table of steps on shapes, one for each of the 358 blocks in the first chain's blocksInOrder list,
is to be evaluated at closed terms. It is not in the library yet, so nothing about what it reads is
claimed here. These equations are meant for its steps at the places of the kind K1; none of these
steps is at closed terms by this alone.

How. The two functions read of the first chain's parameters the codes and the shape alone
(`parLater_congr`, `firstPar_congr`: by unfolding). The ground's parameters are the public part's
(`IM.Open.first`). Codes and shape are written under the hypothesis (`Written354.codes`,
Johnson/Loose/H2K12/ClosedOfPins354.lean; `first_at_head`); so are the plan's two numbers
(`par_at_head`).

Main names.
* `gpW`. `parLater_congr`, `firstPar_congr`: general. `gp_at_head`. **`parLater_at_head`**,
  **`firstPar_at_head`**.

Limits. qFull IS A PLACEHOLDER, NO VALUE THAT ANY FILE GIVES: by its own file's opening comment its
fields given, layout, identifiers and more are empty fillings, and nothing that reads them may be
stated at it. The two equations here hold all the same, because parLater and firstPar read the codes
and the shape alone. `parLater_congr` and `firstPar_congr` repeat, premise for premise, two laws
that the library has under the same short names in another namespace (VerifiableInference.Desc.K1,
QFull.lean, which this file imports); the library also has `parLater_full` and `firstPar_full`,
which lead to qFull. UNDER THE HYPOTHESIS, AND AT AN OPENING: the two statements take an opening O
with its own F, c, A and B as a premise of its own; the hypothesis gives one (its field
laid.opened). That the hypothesis can be met is shown only for `P5J.AtMgA`, which extends AtMg, at
the hash OnBytes.secondHashFunction and at two named sets of public files (`headMember_zFull`,
AtFullSide/Top/HeadMemberAtFull.lean; `headMember_zGap`, AtFullSide/Top/HeadMemberAtGap.lean); by
the first file's own words the example's weights are synthetic. Closed terms, not evaluated. Only
the full-size parameters are covered. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.BackNumbersAtHead
import Johnson.IMR.SeatOpen
import Johnson.Desc.K1.Law.QFull
import Johnson.Desc.ProofFile.Lot.K1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open VerifiableInference
open VerifiableInference.Desc (Chain Block FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (parLater firstPar gpOf qFull noticesAt firstParts firstLaid frame₀
  ownGroup)
open VerifiableInference.PlanWritten (proofSizedFull)
open OnBytes.Maker (WholeD)
open P5J (AtMg)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- The two numbers of the plan that parLater and firstPar take, written. -/
def gpW : _root_.Desc.Plain.GPar := { samples := proofSizedFull.request.answers, firstTree := 0 }

/-- K1's numbers at a later moment read of the first chain's parameters the codes and the shape
alone. General. (The library has the same law: VerifiableInference.Desc.K1.parLater_congr.) -/
theorem parLater_congr {q q' : OnBytes.Params.First} (hc : q.codes = q'.codes)
    (hs : q.shape = q'.shape) (gp : _root_.Desc.Plain.GPar) (l pc m : Nat) :
    parLater q gp l pc m = parLater q' gp l pc m := by
  unfold parLater noticesAt
  rw [hc, hs]

/-- The like at the first segment's opening. General. (The library has the same law:
VerifiableInference.Desc.K1.firstPar_congr.) -/
theorem firstPar_congr {q q' : OnBytes.Params.First} (hc : q.codes = q'.codes)
    (hs : q.shape = q'.shape) (gp : _root_.Desc.Plain.GPar) : firstPar q gp = firstPar q' gp := by
  unfold firstPar firstParts firstLaid frame₀ ownGroup
  rw [hc, hs]

/-- Under the hypothesis the two numbers are the written ones. -/
theorem gp_at_head (h : AtMg o Z D r Zp Np cF) : gpOf Zp = gpW := by
  unfold gpOf gpW
  rw [par_at_head h]

section
variable {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **UNDER THE HYPOTHESIS, AT AN OPENING, K1's NUMBERS AT A LATER MOMENT OF A LINK ARE parLater's
AT THE PLACEHOLDER qFull AND AT gpW.** -/
theorem parLater_at_head (h : AtMg o Z D r Zp Np cF)
    (O : IM.Open o Z.pol Z.lay Z.KL F Zp Bs base c A B) (l pc m : Nat) :
    parLater Bs.G₀.first (gpOf Zp) l pc m = parLater qFull gpW l pc m := by
  have W4 := H2K12.written354_of_pins h.scope h.laid.pub h.pins.1 h.laid.laidPOf
  obtain ⟨-, -, f3, -, -, -⟩ := first_at_head h
  rw [gp_at_head h, O.first]
  exact parLater_congr W4.codes f3 gpW l pc m

/-- **THE LIKE AT THE FIRST SEGMENT's OPENING.** -/
theorem firstPar_at_head (h : AtMg o Z D r Zp Np cF)
    (O : IM.Open o Z.pol Z.lay Z.KL F Zp Bs base c A B) :
    firstPar Bs.G₀.first (gpOf Zp) = firstPar qFull gpW := by
  have W4 := H2K12.written354_of_pins h.scope h.laid.pub h.pins.1 h.laid.laidPOf
  obtain ⟨-, -, f3, -, -, -⟩ := first_at_head h
  rw [gp_at_head h, O.first]
  exact firstPar_congr W4.codes f3 gpW

end

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.parLater_congr
#print axioms Johnson.AtFull.Shape.firstPar_congr
#print axioms Johnson.AtFull.Shape.gp_at_head
#print axioms Johnson.AtFull.Shape.parLater_at_head
#print axioms Johnson.AtFull.Shape.firstPar_at_head
