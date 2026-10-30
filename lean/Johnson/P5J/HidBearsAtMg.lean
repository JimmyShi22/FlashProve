-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/HidBearsAtMg.lean: "H DOES NOT READ THE PADS" AT THE COMPOSED MEANING'S CONSTANT, UNDER
    THE ONE HEAD: the payer of the named premise on H (HidBears (h.𝔇 𝔇₀).H L m,
    Johnson/Top/H0/K2Ties/Constr.lean), from ONE named test on the
list of rounds.
  `AtMg.offC h`: the named test `placesOffC` (PlacesOffPadC.lean) at the constant's own letters.
  `AtMg.placesOff`: AtMg → h.offC = true → `PlacesOffPad` at the constant's own sizes and seats: by
      `placesOffPad_of_C` (laidThere is a field of PlanOk), `sizesOf_beyond`. (The
          constant's H
    stands at the label's form of the seats: no rewrite in scope is wanted.)
  **`AtMg.hid_bears`**: AtMg → h.offC = true → two witnesses that agree in every component but the
      pads of a list L have the same (h.𝔇 𝔇₀).H.hid and the same (h.𝔇 𝔇₀).H.base j, all j.
Limits. Whether h.offC accepts at the release's own files is a RUN's matter, not shown here. That a
    sub-protocol's extractor turns pads alone is for its kind's files to show. The full size alone.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.MgAtConst
import Johnson.P5J.PlacesOffPadC

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.First (Comp)
open VerifiableInference.Desc.Sound (MgData MsgT sameQ)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **The named test, at the constant's own letters.** -/
def AtMg.offC (_ : AtMg o Z D r Zp Np cF) : Bool :=
  placesOffC (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) (At.X Zp) (sizesOf (At.X Zp))
    (At.layout Zp) (At.num Zp)

/-- An accept of the test gives the condition at the constant's own sizes and seats. -/
theorem AtMg.placesOff (h : AtMg o Z D r Zp Np cF) (hC : h.offC = true) :
    PlacesOffPad (At.cs Zp) (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF) (sizesOf (At.X Zp))
      (seatBy (fLay (At.layout Zp) (At.num Zp)) (At.X Zp) (sizesOf (At.X Zp))) :=
  placesOffPad_of_C h.plan.laid hC (sizesOf_beyond (At.X Zp))

/-- **THE CONSTANT's H DOES NOT READ THE PADS.** -/
theorem AtMg.hid_bears (h : AtMg o Z D r Zp Np cF) (hC : h.offC = true) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (L : List (ℕ × ℕ)) (w w' : Wit (CellsM numsFull) At.Tok MsgT)
    (hw : ∀ c : Comp, (∀ x ∈ L, c ≠ .pad x.1 x.2) → sameQ c w w') :
    (h.𝔇 𝔇₀).H.hid w' = (h.𝔇 𝔇₀).H.hid w ∧ ∀ j, (h.𝔇 𝔇₀).H.base j w' ↔ (h.𝔇 𝔇₀).H.base j w :=
  hid_bears_turn (At.X Zp) tokVOf _ _ h.plan.hN h.plan.hG
    (h.placesOff hC) L w w' hw

end P5J

#print axioms P5J.AtMg.placesOff
#print axioms P5J.AtMg.hid_bears
