-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/ConstrRidesHead.lean: the sentence "this part of segment k's relaxed relation
holds of the witness", as it is meant (`P5J.constrQAt`, Johnson/P5J/MeansQ.lean), goes back at the
head's segment too, wherever the head's own sentence does. Two theorems.

Why. Johnson/Desc/Sound/ConstrRides.lean leaves the head's segment out: there the sentence is a
letter, `headPart`. By an evaluation of the table's own functions the head's four parts ride past
the code switch at 24 of its 25 places: so the tie for what rides asks them there.

  `constrQAt_back_any`: at every segment, at a part that is not "every digit lies in the digits'
    table": over every rel that keeps `H.req` and `H.dec` and over which `headPart p i` goes back
    for every i.
  `constr_all`: so `Mg.constr m p` at `P5J.meaningQAt`, for all m and all p but the digits' part:
    the first of the four facts of `t5_four_at_table` (Johnson/Desc/Sound/RidersTie.lean).

Limits. That `headPart` goes back over any relation is a premise. All the limits of
ConstrRides.lean. No soundness of any verifier follows from this file.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.ConstrRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open Inst.Model Inst.Model.All
open OnBytes
open VerifiableInference.Desc.First (Meaning)
open P5J (HidAt TPart TReq TS constrQAt meaningQAt)

section
variable {X : Model.Verify.Public} {P W : Type} {rows cols : ℕ}

/-- **At every segment.** -/
theorem constrQAt_back_any (hd : ℕ) (put : TReq → Fin ppref.V → TReq) (H : HidAt X P W rows cols)
    (headPart : TPart → Cm.Idx → P × TS → Strs → W → Prop)
    (digitsPart : ℕ → P × TS → Strs → W → Prop) (k : ℕ) (p : TPart) (hp : p ≠ .lookDigits)
    (rel : P × First.S → Strs → P × First.S → Strs → Prop)
    (hreq : ∀ a y b y', rel a y b y' → H.req a = H.req b)
    (hdec : ∀ a y b y', rel a y b y' → H.dec a y = H.dec b y')
    (hh : ∀ i, GoesBack rel (headPart p i)) :
    GoesBack rel (constrQAt hd put H headPart digitsPart k p) := by
  by_cases hk : k = hd
  · intro a y b y' w hr h
    unfold constrQAt at h ⊢
    rw [if_neg hp] at h ⊢
    refine ⟨h.1, fun M i hM hH => ?_⟩
    have h2 := h.2 M i (by rw [← hdec a y b y' hr]; exact hM) hH
    rw [if_pos hk] at h2 ⊢
    exact hh i a y b y' w hr h2
  · exact constrQAt_back hd put H headPart digitsPart k p hp hk rel hreq hdec

/-- **The first of the four facts, at the meant filling.** -/
theorem constr_all (hd : ℕ) (put : TReq → Fin ppref.V → TReq) (H : HidAt X P W rows cols)
    (headPart : TPart → Cm.Idx → P × TS → Strs → W → Prop)
    (digitsPart : ℕ → P × TS → Strs → W → Prop) (Mg : Meaning P W)
    (rel : P × First.S → Strs → P × First.S → Strs → Prop)
    (hreq : ∀ a y b y', rel a y b y' → H.req a = H.req b)
    (hdec : ∀ a y b y', rel a y b y' → H.dec a y = H.dec b y')
    (hh : ∀ p i, GoesBack rel (headPart p i)) (m : ℕ) (p : TPart) (hp : p ≠ .lookDigits) :
    GoesBack rel ((meaningQAt hd put H headPart digitsPart Mg).constr m p) :=
  constrQAt_back_any hd put H headPart digitsPart m p hp rel hreq hdec (hh p)

end

end VerifiableInference.Desc.Sound
