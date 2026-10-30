-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Keep/LateLaidAt.lean: UNDER EVERY SLOT THAT A FORM NAMES THE TABLE OF JOINTS' HIDDEN
VALUE (slotW, Johnson/Desc/Sound/FormsQ.lean) IS THE ONE OFF THE LEDGER
BEHIND THE RUN: for a list of forms each of which passes the sentence's own test (affInT, or
affIn), at the late slots K9.lateOf. THE CONCLUSION IS WRITTEN OUT SO THAT IT IS, TO THE LETTER,
THE BODY OF A CALLING KIND's DEFINITION "LateLaid a.F (lateOf a.F G) G fs"
(Johnson/Desc/First/Att/K05WorthLate.lean), which this file does not
import. Statements and proofs: an adapter over Johnson/Top/H/Keep/LateWorld.lean.

OBJECT: slotW; K9.lateOf, K9.slotIn, K9.affIn, K9.affInT.
Used by Johnson/Desc/First/Att/K05PlanesEnts.lean.
LETTERS: own, free, a, G, fs free.
Compiled with the whole library.

Main names:
  lateLaid_slots: from slotIn at every slot that a form names.
  lateLaid_affInT, lateLaid_affIn: from the two tests on forms.

Limits. G is later than the ledger in front (Fo.Later): a premise: each run's law gives it.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.LateWorld

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (lateOf slotIn affIn affInT)

theorem lateLaid_slots (own : List (ℕ × ℕ)) (free : Option ℕ) (a : K9.Part) (G : Fork)
    (hL : _root_.Fo.Later a.F G) (fs : List Aff)
    (h : ∀ f ∈ fs, ∀ y ∈ f.slots.toList, slotIn own free (lateOf a.F G) a y.1 = true) :
    ∀ f ∈ fs, ∀ y ∈ f.slots.toList, ∀ mk : ℕ → GQ,
      slotW a.F (lateOf a.F G) mk y.1 =
        Reading.gl.val (G.vp.getD y.1 zeroE) - Reading.gl.val (G.mf.getD y.1 zeroE) * mk y.1 := by
  intro f hf y hy mk
  obtain ⟨c1, c2⟩ := slotIn_behind own free a G hL y.1 (h f hf y hy)
  exact slotW_lateOf a.F G hL mk y.1 c1 c2

theorem lateLaid_affInT (own : List (ℕ × ℕ)) (free : Option ℕ) (a : K9.Part) (G : Fork)
    (hL : _root_.Fo.Later a.F G) (fs : List Aff)
    (h : ∀ f ∈ fs, affInT own free (lateOf a.F G) a f = true) :
    ∀ f ∈ fs, ∀ y ∈ f.slots.toList, ∀ mk : ℕ → GQ,
      slotW a.F (lateOf a.F G) mk y.1 =
        Reading.gl.val (G.vp.getD y.1 zeroE) - Reading.gl.val (G.mf.getD y.1 zeroE) * mk y.1 :=
  lateLaid_slots own free a G hL fs fun f hf y hy => by
    have h0 := h f hf
    unfold affInT at h0
    exact List.all_eq_true.1 (Eq.mp (Bool.and_eq_true _ _) h0).2 y hy

theorem lateLaid_affIn (own : List (ℕ × ℕ)) (free : Option ℕ) (a : K9.Part) (G : Fork)
    (hL : _root_.Fo.Later a.F G) (fs : List Aff)
    (h : ∀ f ∈ fs, affIn own free (lateOf a.F G) a f = true) :
    ∀ f ∈ fs, ∀ y ∈ f.slots.toList, ∀ mk : ℕ → GQ,
      slotW a.F (lateOf a.F G) mk y.1 =
        Reading.gl.val (G.vp.getD y.1 zeroE) - Reading.gl.val (G.mf.getD y.1 zeroE) * mk y.1 :=
  lateLaid_slots own free a G hL fs fun f hf y hy => by
    have h0 := h f hf
    unfold affIn at h0
    exact List.all_eq_true.1 (Eq.mp (Bool.and_eq_true _ _) h0).2 y hy

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.lateLaid_slots
#print axioms VerifiableInference.Desc.Sound.lateLaid_affInT
#print axioms VerifiableInference.Desc.Sound.lateLaid_affIn
