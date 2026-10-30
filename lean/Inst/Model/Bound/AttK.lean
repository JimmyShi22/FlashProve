-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Bound/AttK.lean: an attention segment at any lawful shift: from the field relation to the
program (Inst/Model/Program.lean), at a variable number p.

The statements that read the modulus are here, in the namespace `Cm.TI`, for a variable number p
with `Big p` (Inst/Model/Bound/Base.lean; that p is prime is not assumed); the others are in
Inst/Model/Att/Scales.lean.

Main names:
  `noWrapK`: under the hypotheses of its statement, among them the segment's field relation over
    `ZMod p` (`hRF`) and `InputsAre` for one layer (the cells hold the program's inputs),
    `OutputIs`: the cells hold the program's output of that layer (Inst/Model/Att/Trace.lean).
  `outBoundK`: the bound on the output, under the hypotheses of its statement.

Why: `Big p` enters through `half1` (Inst/Model/Bound/Att1.lean) and `NW2.out_link`, `NW2.fa12`
(Inst/Model/Bound/Att2.lean).

Limits: for what each name is, what is stated and what is not said, see the head of
Inst/Model/Att/Scales.lean. (The limits on the prime: the head of Inst/Model/Bound/Base.lean.)
Terms: lean/GLOSSARY.md.
-/
import Inst.Model.Att.Scales
import Inst.Model.Bound.Att2


set_option autoImplicit false

namespace Cm.TI.AttSeg

open Inst.Model Inst.Model.AttSeg

variable {p : ℕ} [Big p]

open Finset

/-- From the field relation to the program, one layer, at the layer's own parameters and tables.
(not all hypotheses are named here: see the statement below) -/
theorem noWrapK [scl : Scl] {D : Dim} (hD : SizeOK D) {tb : Tables}
    (hT : ExpTab D tb) {t : Raw → ℤ} (hRF : RFraw D tb (ZMod p) t) {lam : ℕ}
    {P : Params} {tbP : Tables} (hF : NW2.Fit D P) (hX : tbP.Exp = tb.Exp)
    {w : LayerW} {L : ℕ} {x : ℕ → Vec} (hin : InputsAre D P tbP w L x lam t) :
    OutputIs D P tbP w L x lam t := by
  intro b hb hl g hg i hi n hn
  have h := intRel_of_rfraw hRF
  exact NW2.out_link hD.ex hT.rng hT.zero hX h
    (half1 h hD.ch hD.lT hb (NW2.inB_of_inputs hin hb hl)) hD.T hF hin hb hl hg hi hn

/-- The bound on the output. -/
theorem outBoundK [scl : Scl] {D : Dim} (hD : SizeOK D) {tb : Tables} (hT : ExpTab D tb)
    {t : Raw → ℤ} (hRF : RFraw D tb (ZMod p) t)
    (hq : ∀ b < D.nb, ∀ g < D.nG, ∀ i < D.T, ∀ n < D.ch, |qryV t b g i n| ≤ 2047)
    (hkv : ∀ lam < D.nl,
      ∀ g < D.nG, ∀ j < D.T, ∀ n < D.ch, |keyV t lam g j n| ≤ 2047 ∧ |valV t lam g j n| ≤ 2047) :
    ∀ b < D.nb, ∀ g < D.nG, ∀ i < D.T, ∀ n < D.ch, |outV t b g i n| ≤ 2047 := by
  intro b hb g hg i hi n hn
  have h := intRel_of_rfraw hRF
  have hin : InB D t b :=
    ⟨fun g hg i hi n hn => hq b hb g hg i hi n hn,
      fun g hg j hj n hn => hkv (D.lamOf b) (NW2.lamOf_lt hb) g hg j hj n hn⟩
  exact (NW2.fa12 hD.ex hT.rng h (half1 h hD.ch hD.lT hb hin) hb hT.zero hD.T hin hg hi hn).2

/-! On `noWrapK`: the statement covers only a trace whose arrays hold the program's q, kx, v: "step
(PL6) on the integers of the trace, whatever they are" cannot be said here, because the program's o
is a function of (w, L, x). It is stated layer by layer because the induction on the stream learns
the stream before layer lam + 1 only from the output of layer lam. -/

end Cm.TI.AttSeg
