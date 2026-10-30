-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/RcAtEnd.lean: THE PREMISE hRc OF THE LAST TABLE's FIELD (own3_at_top | own3_at_end,
Johnson/LLT25R/LastTop.lean | Johnson/LLT25R/LastEnd.lean), IN ITS BINDER's SIGNS, FROM: the five
facts at the first chain's reached end · the test `ownSitsB` there · the test `sampleTwoB` there.
Two theorems. Joinings.

Why. `ToldDesc.rcLastB ft V L cs s` is five tests on the first chain's last state. Three of them
(`bookInOrderB`, `bookFitsB`, `seatsCarriedB`) are clauses of a walk's end along the first chain's
fold; the two others have their own laws. Another joining of the five
(Johnson/Desc/Sound/RcOfFold.lean) takes the three from the structure FoldFacts, whole, which speaks
of every border. This one asks them AT THE LAST BORDER ALONE.

  `rcLastB_of_parts`: the five tests' accepts give `rcLastB`'s.
  `hRc_of_five`: at every `get`, Oc and Rc: where Rc gives a condition E on `get q`; E with "no
    mark" gives `atFirstBook 0`, `bookFitsB`, two facts more (X, Y: letters) and `atFirstSeats L`;
    and under Oc, Rc and "no mark" `ownSitsB V` and `sampleTwoB cs V` accept: then under Oc, Rc and
    "no mark" `rcLastB 0 V L cs (get q).2 = true`.

Limits. The three premises are shown nowhere here. ONE L: the list of places and shapes in the
conclusion is the one of the five facts. Nothing on soundness.
-/
import Johnson.ToldDescR.RcLast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law
open OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Last
open VerifiableInference.Desc.Sound (bookFitsB)
open VerifiableInference.Desc.K12.Door (atFirstBook atFirstSeats bookInOrderB seatsCarriedB Laid)
open ToldDesc (rcLastB sampleTwoB)

/-- The five tests' accepts give the one test's. -/
theorem rcLastB_of_parts {ft : Nat} {V : OwnSeats} {L : Laid} {cs : Codes} {s : First.S}
    (h1 : bookInOrderB ft s.book s.roots = true) (h2 : bookFitsB s.book = true)
    (h3 : ownSitsB V s = true) (h4 : sampleTwoB cs V s = true)
    (h5 : seatsCarriedB L s.book = true) : rcLastB ft V L cs s = true := by
  unfold rcLastB
  rw [h1, h2, h3, h4, h5]
  rfl

/-- **hRc, in its binder's signs, from the five facts at the last border and the two tests.** -/
theorem hRc_of_five {P S₁ P₀ Str : Type} (get : P × S₁ → P₀ × First.S)
    (Oc : P × S₁ → Str → Prop) (Rc : P × S₁ → Prop) (E : P₀ × First.S → Prop)
    (hE : ∀ q, Rc q → E (get q)) {X Y : P₀ × First.S → Prop} (V : OwnSeats) (L : Laid)
    (cs : Codes)
    (H5 : ∀ p : P₀ × First.S, E p → p.2.failed = none →
      atFirstBook 0 p.2 = true ∧ bookFitsB p.2.book = true ∧ X p ∧ Y p ∧
        atFirstSeats L p.2 = true)
    (h₃ : ∀ q y, Oc q y → Rc q → (get q).2.failed = none → ownSitsB V (get q).2 = true)
    (h₄ : ∀ q y, Oc q y → Rc q → (get q).2.failed = none → sampleTwoB cs V (get q).2 = true) :
    ∀ q y, Oc q y → Rc q → (get q).2.failed = none → rcLastB 0 V L cs (get q).2 = true := by
  intro q y ho hq hm
  have H := H5 _ (hE q hq) hm
  exact rcLastB_of_parts H.1 H.2.1 (h₃ q y ho hq hm) (h₄ q y ho hq hm) H.2.2.2.2

end P2Law
