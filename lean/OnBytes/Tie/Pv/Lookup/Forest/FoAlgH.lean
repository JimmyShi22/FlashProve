-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoAlgH.lean.
The head's key forms: the named proposition Fo.AlgH, cut down to its affine part.

Fo.AlgH (OnBytes/Tie/Pv/Lookup/Ends/FoKeysH.lean) says that the value of a key form of the head is
the extension of the call's key vector, in every world that meets the law of the reads and in which
two slots hold the extensions of the products' shares. This file takes the products out: what is
left to show says nothing of a product.

Defines:
  AlgHAff: A CLOSED PROPOSITION, NOT PROVED HERE: under the law of the reads alone, the value of a
    key form is the extension of the AFFINE part of the call's key vector (OnBytes.Ends.H.affH),
    plus, in the call with the segment NF, what stands under the slot of the stream's sumcheck,
    plus, in the call with HD0, 2^lPd / 2^(sh + 15) times what stands under the slot of the logits'
    sumcheck.
  SegOnce R: the segments NF and HD0 stand in the calls qN and qH alone. A fact on the layout.
  (Its test on the layout's lists, segOnceB: OnBytes/Tie/Pv/Lookup/Ends/FoHeadBDefs.lean.)
States:
  extL_add, extL_zero: the extension at a list is additive.
  segOnce_of_test: the test gives SegOnce, if the default call (read beyond the layout's last) has
    no segment; that is a premise.
  kvH_split: a key is its affine part and the two segments' products.
  algH_at: at one record: the affine part and SegOnce give Fo.AlgH's statement at that record.
  algH_of_aff: AlgHAff, and SegOnce at every record made as the head's check makes it, give AlgH.
Not claimed: anything on soundness, completeness or hiding. Nor are AlgHAff and SegOnce claimed.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoKeysH
import OnBytes.Tie.Pv.Lookup.Ends.FoHeadBDefs

set_option autoImplicit false

namespace Fo
open TwV Finset OnBytes OnBytes.Model OnBytes.Ends OnBytes.Ends.H

section
variable {K : Type} [CommRing K]

theorem extL_add (f g : ℕ → K) (z : List K) :
    extL (fun i => f i + g i) z = extL f z + extL g z := by
  unfold extL
  rw [lsum, lsum, lsum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem extL_zero (z : List K) : extL (fun _ => (0 : K)) z = 0 := by
  unfold extL
  rw [lsum]
  exact Finset.sum_eq_zero fun i _ => by ring

end

/-- The segments NF and HD0 stand in the calls qN and qH alone. -/
def SegOnce (R : Head.Run) : Prop :=
  ∀ q j x, (colH R.L q j = some ("NF", x) → q = R.x.qN) ∧
    (colH R.L q j = some ("HD0", x) → q = R.x.qH)

theorem colH_name {L : Head.HL} {q j x : ℕ} {sn : String} (h : colH L q j = some (sn, x)) :
    ∃ g ∈ (L.calls.getD q default).segs, g.name = sn := by
  unfold colH at h
  obtain ⟨g, hg, hx⟩ := List.exists_of_findSome?_eq_some h
  cases hi : g.pos.findIdx? (· == j) with
  | none => rw [hi] at hx; exact absurd hx (by simp)
  | some y =>
    rw [hi] at hx
    exact ⟨g, hg, congrArg Prod.fst (Option.some.inj hx)⟩

/-- The test gives SegOnce, if a call beyond the layout's last has no segment. -/
theorem segOnce_of_test (R : Head.Run) (h : segOnceB R.L R.x.qN R.x.qH = true)
    (hd : (default : CallD).segs = []) : SegOnce R := by
  have key : ∀ q j x sn, colH R.L q j = some (sn, x) →
      (sn != "NF" || q == R.x.qN) = true ∧ (sn != "HD0" || q == R.x.qH) = true := by
    intro q j x sn hc
    obtain ⟨g, hg, rfl⟩ := colH_name hc
    by_cases hq : q < R.L.calls.size
    · unfold segOnceB at h
      have h1 := List.all_eq_true.mp h q (List.mem_range.mpr hq)
      have h2 := List.all_eq_true.mp h1 g hg
      simpa [Bool.and_eq_true] using h2
    · have e : R.L.calls.getD q default = default := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
        rfl
      rw [e, hd] at hg
      exact absurd hg (by simp)
  intro q j x
  refine ⟨fun hc => ?_, fun hc => ?_⟩
  · simpa using (key q j x _ hc).1
  · simpa using (key q j x _ hc).2

section
variable {K : Type} [Field K]

/-- A key is its affine part and the two segments' products. -/
theorem kvH_split (P : PubH) (cell : NameH → K) (q i : ℕ) :
    kvH P cell q i =
      kvOf P (affH P cell) q i + gamAt P cell "NF" q i + gamAt P cell "HD0" q i := by
  unfold kvH kvOf gamAt
  cases hcol : colH P.L q (i / P.h.T) with
  | none => simp
  | some sx =>
    obtain ⟨sn, x⟩ := sx
    show segH P cell sn x (i % P.h.T) = affH P cell sn x (i % P.h.T) +
      (if sn == "NF" then gamH P cell "NF" x (i % P.h.T) else 0) +
      (if sn == "HD0" then gamH P cell "HD0" x (i % P.h.T) else 0)
    rw [segH_eq]
    by_cases h1 : sn = "NF"
    · subst h1
      simp
    · by_cases h2 : sn = "HD0"
      · subst h2
        simp
      · have e : gamH P cell sn x (i % P.h.T) = 0 := by
          unfold gamH
          simp [h1, h2]
        simp [h1, h2, e]

theorem gamAt_zero (P : PubH) (cell : NameH → K) (sn : String) (q : ℕ)
    (h : ∀ j x, colH P.L q j ≠ some (sn, x)) (i : ℕ) : gamAt P cell sn q i = 0 := by
  unfold gamAt
  cases hcol : colH P.L q (i / P.h.T) with
  | none => rfl
  | some sx =>
    obtain ⟨s, x⟩ := sx
    show (if s == sn then _ else 0) = 0
    rw [if_neg]
    intro hs
    have : s = sn := by simpa using hs
    exact h _ x (this ▸ hcol)

end

/-- Fo.AlgH at one record. -/
def AlgHAt (R : Head.Run) (lay : WsLay) : Prop :=
  ∀ (q : ℕ) (laid laid' : Array ℕ) (F G : Fork) (c c' : Ctx) (v : Aff),
    q < R.x.g1.shape.NC → Head.keyForm R q laid F c = .ok (((v, laid'), G), c') →
    ∀ (W : World Cb.Gl.E) (cell : NameH → Cb.Gl.E),
      ReadsAll Reading.gl R.hp.tl.mats (funsH R) W.entry R.iU3 (colsOf F R.iU3)
        (fun m r c => cell (.cell m r c)) →
      ProdH Reading.gl R lay W cell →
      v.value Reading.gl W = extL (kvH (pubH R lay) cell q) (zkH Reading.gl R q)

theorem algH_iff : AlgH ↔ ∀ R lay, MadeH R → AlgHAt R lay := Iff.rfl

/-- The affine part, at one record. -/
def AlgHAffAt (R : Head.Run) (lay : WsLay) : Prop :=
  ∀ (q : ℕ) (laid laid' : Array ℕ) (F G : Fork) (c c' : Ctx) (v : Aff),
    q < R.x.g1.shape.NC → Head.keyForm R q laid F c = .ok (((v, laid'), G), c') →
    ∀ (W : World Cb.Gl.E) (cell : NameH → Cb.Gl.E),
      ReadsAll Reading.gl R.hp.tl.mats (funsH R) W.entry R.iU3 (colsOf F R.iU3)
        (fun m r c => cell (.cell m r c)) →
      v.value Reading.gl W =
        extL (kvOf (pubH R lay) (affH (pubH R lay) cell) q) (zkH Reading.gl R q) +
          (if q = R.x.qN then W.slot R.x.tN.sCl else 0) +
          (if q = R.x.qH then iw (pubH R lay) * 2 ^ R.h.lPd * W.slot R.x.tH.sCl else 0)

/-- **The affine part of Fo.AlgH, as one closed proposition.** -/
def AlgHAff : Prop := ∀ (R : Head.Run) (lay : WsLay), MadeH R → AlgHAffAt R lay

/-- The products leave, at one record. -/
theorem algH_at {R : Head.Run} {lay : WsLay} (hA : AlgHAffAt R lay) (hS : SegOnce R) :
    AlgHAt R lay := by
  intro q laid laid' F G c c' v hq hk W cell hU hP
  rw [hA q laid laid' F G c c' v hq hk W cell hU]
  have e : kvH (pubH R lay) cell q = fun i =>
      (kvOf (pubH R lay) (affH (pubH R lay) cell) q i + gamAt (pubH R lay) cell "NF" q i) +
        gamAt (pubH R lay) cell "HD0" q i := funext fun i => kvH_split _ _ _ _
  rw [e, extL_add, extL_add]
  congr 1
  · congr 1
    by_cases h1 : q = R.x.qN
    · rw [if_pos h1, h1]
      exact hP.stream
    · rw [if_neg h1]
      have z : gamAt (pubH R lay) cell "NF" q = fun _ => 0 :=
        funext (gamAt_zero _ _ _ _ fun j x hc => h1 ((hS q j x).1 hc))
      rw [z, extL_zero]
  · by_cases h2 : q = R.x.qH
    · rw [if_pos h2, h2]
      exact hP.logits
    · rw [if_neg h2]
      have z : gamAt (pubH R lay) cell "HD0" q = fun _ => 0 :=
        funext (gamAt_zero _ _ _ _ fun j x hc => h2 ((hS q j x).2 hc))
      rw [z, extL_zero]

/-- The products leave the named proposition. -/
theorem algH_of_aff (hA : AlgHAff) (hS : ∀ R, MadeH R → SegOnce R) : AlgH :=
  fun R lay hR => algH_at (hA R lay hR) (hS R hR)

end Fo
