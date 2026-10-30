-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/Q38E/TiesAtHead.lean: ties under the one head for the closed side of `DigAheadOk`
(Johnson/Desc/First/Look/K3DigitsAhead.lean): the first chain has 25 segments; at every segment the
lookups' condition on public data `DigOK` holds at the head's own terms for what is sent and for the
radii; and the structure of the segment's approximate range proof passes `DgP.colsTest`.

Row or tool. Ties under the head: each a call of the library's laws; nothing is evaluated. For the
law on
the digits of the sub-protocol K8: the condition `DigAheadOk` at the state behind the draw of the
approximate range proof.

What it spends. Rows are those of the proof file's entry tests, `LPFD.lawsAsk`
(Johnson/Desc/Laid/ProofAsks.lean), counted from 1: row 1 holds the
declared rounds to the written ones, row 9 the made plan (`madeRow`), row 11 is the lookups' digits'
row (`digEntry`). `links25_at_head`: no row: the head's fields `scope` and `laid` (its `publicO`).
`digOK_at_head` and `digAt_all25`: row 11, through Johnson/HB/LLHARD/Q38E/DigAtHead.lean.
`cols_at_head`: no row: the head's field `pubOne`. Over entry tests without row 11
the two in the middle cannot be had.

What is here (namespace Q38).
  `links25_at_head`: `K3Asks.linksOf (At.X Zp) = 25`.
  `digOK_at_head`: for l up to 24 and `digAt (At.X Zp) l = some (x, tl)`: `DigOK` at x, tl,
    `h.𝔇.sent`, `h.𝔇.l3.rad` and the field's characteristic. That the entry test's own term for what
    is sent is the head's is by definition.
  `digAt_all25`: at every l up to 24 the reader answers.
  `cols_at_head`: `DgP.colsTest tl = true`: by `cols_at`, `colsAll_of_public`
    (Johnson/Desc/First/Look/ColsAt.lean) and `digAt_is`, `shapeZAll_of_public`
    (DigitsShapeAt.lean).
`links25_at_head` and `digAt_all25` are called by no file beside this one: they stand for callers.

Limits. Nothing on soundness.


-/
import Johnson.HB.LLHARD.Q38E.DigAtHead
import Johnson.Desc.First.Look.ColsAt
import Johnson.Desc.First.Look.DigitsShapeAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Q38
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain K3Asks.linksOf)
open VerifiableInference.Desc.First.Look
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x₀ : Place}

/-- The first chain has 25 segments. -/
theorem links25_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) :
    K3Asks.linksOf (P5J.At.X Zp) = 25 :=
  links_25 h.scope h.laid

set_option maxRecDepth 40000 in
/-- **The lookups' condition on public data, at the head's own terms.** -/
theorem digOK_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {l : ℕ} (hl : l ≤ 24)
    {x : Place} {tl : HTailF2} (hx : digAt (P5J.At.X Zp) l = some (x, tl)) :
    DigOK (Params.settingOf (P5J.At.X Zp).P.frame) x tl h.𝔇.sent h.𝔇.l3.rad Cb.Gl.p := by
  obtain ⟨x', tl', e, H⟩ := digOK_at_name h.scope h.laid hl h.𝔇.l3.rad
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (e.symm.trans hx))
  exact H

/-- At every segment the reader answers. -/
theorem digAt_all25 (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) :
    ∀ l ≤ 24, ∃ x tl, digAt (P5J.At.X Zp) l = some (x, tl) :=
  fun _ hl => digAt_at_head h hl

/-- **The structure of the segment's approximate range proof passes the test on the columns.** -/
theorem cols_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {l : ℕ} {x : Place}
    {tl : HTailF2} (hx : digAt (P5J.At.X Zp) l = some (x, tl)) : DgP.colsTest tl = true :=
  cols_at (colsAll_of_public h.pubOne) (digAt_is (shapeZAll_of_public h.pubOne) hx)

end Q38


#print axioms Q38.links25_at_head
#print axioms Q38.digOK_at_head
#print axioms Q38.digAt_all25
#print axioms Q38.cols_at_head
