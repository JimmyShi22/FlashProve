-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/ConstrRides.lean: the sentence "this part of segment k's relaxed relation holds
of the witness", as it is meant (`P5J.constrQAt`, Johnson/P5J/MeansQ.lean), goes back over every
relation between two statements that keeps what it reads of them: the request and the decoded table.
Three theorems. The reading of the witness H, the head's and the digits' sentences are letters.

Why. Of the pairs of a block and an item that rides past it, about half at the small list are parts
of later segments' relations (by an evaluation of the table's own functions: 580 of 1,177). The tie
for what rides asks each of them to go back over a yes of the block
(Johnson/Desc/Sound/ItemsRide.lean: `GoesBack`, `FieldsBack.constr`).

What is said.
  `constrQAt_back`: at a segment that is not the head's and a part that is not "every digit lies in
    the digits' table": over every rel that keeps `H.req` and `H.dec`.
  `constrQAt_back_public`: where `H.req` reads the public part alone, and `H.dec` the public part
    and the stored table's cells alone: over "the public part is the same and the cells are the
    same".
  `constr_field`: so the field `constr` of `FieldsBack` at `P5J.meaningQAt`, with
    own m p := the part is the digits' or the segment is the head's.

Limits. (1) At the head's segment and at the digits' part the sentence is another author's letter:
nothing is said of it. (2) That the H of any filling reads so is a premise. (3) That a yes of any
block keeps the public part and the cells is not shown here. (4) One direction: from behind to in
front. No soundness of any verifier follows from this file.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P5J.MeansQ
import Johnson.Desc.Sound.ItemsRide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open Inst.Model Inst.Model.All
open OnBytes
open VerifiableInference.Desc.First (Meaning)
open P5J (HidAt TPart TReq TS constrQAt meaningQAt)

section
variable {X : Model.Verify.Public} {P W : Type} {rows cols : ℕ}

/-- **The meant sentence goes back over every relation that keeps the request and the decoded
table.** -/
theorem constrQAt_back (hd : ℕ) (put : TReq → Fin ppref.V → TReq) (H : HidAt X P W rows cols)
    (headPart : TPart → Cm.Idx → P × TS → Strs → W → Prop)
    (digitsPart : ℕ → P × TS → Strs → W → Prop) (k : ℕ) (p : TPart) (hp : p ≠ .lookDigits)
    (hk : k ≠ hd) (rel : P × First.S → Strs → P × First.S → Strs → Prop)
    (hreq : ∀ a y b y', rel a y b y' → H.req a = H.req b)
    (hdec : ∀ a y b y', rel a y b y' → H.dec a y = H.dec b y') :
    GoesBack rel (constrQAt hd put H headPart digitsPart k p) := by
  intro a y b y' w hr h
  unfold constrQAt at h ⊢
  rw [if_neg hp] at h ⊢
  refine ⟨h.1, fun M i hM hH => ?_⟩
  have h2 := h.2 M i (by rw [← hdec a y b y' hr]; exact hM) hH
  rw [if_neg hk] at h2 ⊢
  rw [hreq a y b y' hr]
  exact h2

/-- Where the reading reads the public part and the cells alone. -/
theorem constrQAt_back_public (hd : ℕ) (put : TReq → Fin ppref.V → TReq)
    (H : HidAt X P W rows cols) (headPart : TPart → Cm.Idx → P × TS → Strs → W → Prop)
    (digitsPart : ℕ → P × TS → Strs → W → Prop) (k : ℕ) (p : TPart) (hp : p ≠ .lookDigits)
    (hk : k ≠ hd) (hR : ∀ a b : P × TS, a.1 = b.1 → H.req a = H.req b)
    (hD : ∀ (a b : P × TS) (y y' : Strs), a.1 = b.1 → y'.cell = y.cell → H.dec a y = H.dec b y') :
    GoesBack (fun a y b y' => a.1 = b.1 ∧ y'.cell = y.cell)
      (constrQAt hd put H headPart digitsPart k p) :=
  constrQAt_back hd put H headPart digitsPart k p hp hk _ (fun a _ b _ h => hR a b h.1)
    fun a y b y' h => hD a b y y' h.1 h.2

/-- **The field `constr` of `FieldsBack` at the meant filling.** -/
theorem constr_field (hd : ℕ) (put : TReq → Fin ppref.V → TReq) (H : HidAt X P W rows cols)
    (headPart : TPart → Cm.Idx → P × TS → Strs → W → Prop)
    (digitsPart : ℕ → P × TS → Strs → W → Prop) (Mg : Meaning P W)
    (rel : P × First.S → Strs → P × First.S → Strs → Prop)
    (hreq : ∀ a y b y', rel a y b y' → H.req a = H.req b)
    (hdec : ∀ a y b y', rel a y b y' → H.dec a y = H.dec b y') (m : ℕ) (p : TPart)
    (ho : (p == .lookDigits || m == hd) = false) :
    GoesBack rel ((meaningQAt hd put H headPart digitsPart Mg).constr m p) := by
  have h1 : p ≠ .lookDigits := by
    intro e
    subst e
    simp at ho
  have h2 : m ≠ hd := by
    intro e
    subst e
    simp at ho
  exact constrQAt_back hd put H headPart digitsPart m p h1 h2 rel hreq hdec

end

end VerifiableInference.Desc.Sound
