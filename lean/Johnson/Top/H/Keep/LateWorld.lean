-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Keep/LateWorld.lean: THE WORLD IN WHICH THE TABLE OF JOINTS' SENTENCE READS A RUN's
FORMS (worldOwn, Johnson/Desc/Sound/FormsQ.lean) IS, AT THE SLOTS THAT
THESE FORMS MAY NAME, THE WORLD OF THE LEDGER BEHIND THE RUN: where the late slots are those that
are free in front and filled behind (K9.lateOf, Johnson/Desc/First/Batch/ReaderOf.lean).
General in the run. Statements and proofs.

OBJECT: slotW, worldOwn; K9.lateOf, K9.lateAt, K9.slotIn, K9.affIn; Fork.worldOf.
Used by Johnson/P1K9R/ItemPlanes.lean, Johnson/Top/H/Keep/LateLaidAt.lean and
  Johnson/Top/H/Keep/PlanesSlotsIn.lean.
LETTERS: F | a, G, mask | D, j, f, own, free.
Compiled with the whole library.

Main names:
  mem_lateOf, lateOf_mem: what the list of late slots holds.
  lateAt_late, lateAt_filled: what it says at a slot that the run fills; at one filled in front.
  slotW_lateOf: at a slot below G's number that is filled in G: the sentence's hidden value is
    shown - factor * mask OFF G.
  slotIn_behind: a slot that passes the sentence's own test is such a slot.
  value_behind: THE END: a form that passes affIn is worth in worldOwn a (lateOf a.F G) D what it is
    worth in G.worldOf gl D.mask (the same entries).

Limits. G is later than the ledger in front (Fo.Later): a premise: each run's law gives it. On the
slots alone: the entries are carried over as they are. Nothing says that the reader's list of late
slots is lateOf: Johnson/Top/H/Keep/ReaderIsRun.lean's Cut.late says it of a link's readers.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.FormsQ
import Johnson.Desc.First.Batch.ReaderOf
import OnBytes.Tie.Pv.Lookup.Forest.FoForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (lateAt lateOf slotIn affIn)
open VerifiableInference.Desc.K9L (Bound)

theorem mem_lateOf {F G : Fork} {x : ℕ × E × E} (h : x ∈ lateOf F G) :
    x.1 < G.ns ∧ F.gotF.getD x.1 false = false ∧ G.gotF.getD x.1 false = true ∧
      x.2 = (G.vp.getD x.1 zeroE, G.mf.getD x.1 zeroE) := by
  unfold lateOf at h
  obtain ⟨j, hj, hx⟩ := List.mem_filterMap.1 h
  by_cases hc : (!(F.gotF.getD j false) && G.gotF.getD j false) = true
  · rw [if_pos hc] at hx
    obtain rfl := Option.some.inj hx
    obtain ⟨c1, c2⟩ := Eq.mp (Bool.and_eq_true _ _) hc
    refine ⟨List.mem_range.1 hj, ?_, c2, rfl⟩
    show F.gotF.getD j false = false
    cases hF : F.gotF.getD j false with
    | false => rfl
    | true =>
      rw [hF] at c1
      exact nomatch c1
  · rw [if_neg hc] at hx
    exact nomatch hx

theorem lateOf_mem {F G : Fork} {j : ℕ} (hj : j < G.ns) (h1 : F.gotF.getD j false = false)
    (h2 : G.gotF.getD j false = true) :
    (j, G.vp.getD j zeroE, G.mf.getD j zeroE) ∈ lateOf F G := by
  unfold lateOf
  refine List.mem_filterMap.2 ⟨j, List.mem_range.2 hj, ?_⟩
  rw [h1, h2]
  rfl

/-- At a slot that the run fills. -/
theorem lateAt_late {F G : Fork} {j : ℕ} (hj : j < G.ns) (h1 : F.gotF.getD j false = false)
    (h2 : G.gotF.getD j false = true) :
    lateAt (lateOf F G) j = some (G.vp.getD j zeroE, G.mf.getD j zeroE) := by
  unfold lateAt
  cases e : (lateOf F G).find? (fun x => x.1 == j) with
  | none =>
    have h0 := List.find?_eq_none.1 e _ (lateOf_mem hj h1 h2)
    simp at h0
  | some x =>
    have hxj : x.1 = j := by
      have h0 := List.find?_some e
      simpa using h0
    obtain ⟨_, _, _, h4⟩ := mem_lateOf (List.mem_of_find?_eq_some e)
    show some x.2 = _
    rw [h4, hxj]

/-- At a slot that is filled in front. -/
theorem lateAt_filled {F G : Fork} {j : ℕ} (h1 : F.gotF.getD j false = true) :
    lateAt (lateOf F G) j = none := by
  unfold lateAt
  cases e : (lateOf F G).find? (fun x => x.1 == j) with
  | none => rfl
  | some x =>
    have hxj : x.1 = j := by
      have h0 := List.find?_some e
      simpa using h0
    obtain ⟨_, h3, _, _⟩ := mem_lateOf (List.mem_of_find?_eq_some e)
    rw [hxj, h1] at h3
    exact nomatch h3

/-- **The sentence's hidden value is the one off the ledger behind.** -/
theorem slotW_lateOf (F G : Fork) (hL : _root_.Fo.Later F G) (mask : ℕ → GQ) (j : ℕ)
    (hj : j < G.ns) (hg : G.gotF.getD j false = true) :
    slotW F (lateOf F G) mask j =
      Reading.gl.val (G.vp.getD j zeroE) - Reading.gl.val (G.mf.getD j zeroE) * mask j := by
  cases h1 : F.gotF.getD j false with
  | false => rw [slotW_late F _ mask j _ (lateAt_late hj h1 hg)]
  | true =>
    rw [slotW_ledger F _ mask j (lateAt_filled h1)]
    obtain ⟨_, e1, e2⟩ := hL.keep j h1
    rw [e1, e2]

/-- A slot that passes the sentence's own test is below G's number and filled in G. -/
theorem slotIn_behind (own : List (ℕ × ℕ)) (free : Option ℕ) (a : K9.Part) (G : Fork)
    (hL : _root_.Fo.Later a.F G) (j : ℕ) (h : slotIn own free (lateOf a.F G) a j = true) :
    j < G.ns ∧ G.gotF.getD j false = true := by
  unfold slotIn at h
  obtain ⟨c1, h⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨_, h⟩ := Eq.mp (Bool.and_eq_true _ _) h
  obtain ⟨_, h⟩ := Eq.mp (Bool.and_eq_true _ _) h
  refine ⟨by rw [hL.ns]; exact of_decide_eq_true c1, ?_⟩
  rcases Eq.mp (Bool.or_eq_true _ _) h with h | h
  · cases h1 : a.F.gotF.getD j false with
    | true => exact (hL.keep j h1).1
    | false =>
      unfold lateAt at h
      cases e : (lateOf a.F G).find? (fun x => x.1 == j) with
      | none =>
        rw [e] at h
        exact nomatch h
      | some x =>
        have hxj : x.1 = j := by
          have h0 := List.find?_some e
          simpa using h0
        obtain ⟨_, _, h3, _⟩ := mem_lateOf (List.mem_of_find?_eq_some e)
        rw [hxj] at h3
        exact h3
  · exact (hL.keep j (Eq.mp (Bool.and_eq_true _ _) h).1).1

/-- **THE END.** -/
theorem value_behind (own : List (ℕ × ℕ)) (free : Option ℕ) (a : K9.Part) (G : Fork)
    (hL : _root_.Fo.Later a.F G) (D : Bound GQ) (f : Aff)
    (h : affIn own free (lateOf a.F G) a f = true) :
    f.value Reading.gl (worldOwn a (lateOf a.F G) D) =
      f.value Reading.gl (G.worldOf Reading.gl D.mask (worldOwn a (lateOf a.F G) D).entry) := by
  refine value_eq _ _ f (fun _ _ => rfl) fun x hx => ?_
  unfold affIn at h
  have h2 := List.all_eq_true.1 (Eq.mp (Bool.and_eq_true _ _) h).2 x hx
  obtain ⟨c1, c2⟩ := slotIn_behind own free a G hL x.1 h2
  exact slotW_lateOf a.F G hL D.mask x.1 c1 c2

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.slotW_lateOf
#print axioms VerifiableInference.Desc.Sound.slotIn_behind
#print axioms VerifiableInference.Desc.Sound.value_behind
