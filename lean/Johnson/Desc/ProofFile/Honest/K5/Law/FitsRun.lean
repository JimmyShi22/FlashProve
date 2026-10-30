-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/FitsRun.lean: CONDITIONAL: THE ROW FITS ITS SHAPES AT THE LISTS
THAT A PART READS IN A RUN. The maker of a place's public data asks its tests at one list:
challenges of the shapes of the declared rounds in front, all 0. A part of the row reads the key
points at another: all that was heard, with the drawn values, longer than the front from the place's
second round on. Here: one named public premise on the reader of the key points that carries the
first test from the one list to the other, and with it the laws of Honest/K5/Law/Fits.lean. One
definition of a proposition; statements with their proofs.

  `sameSizes_of_map`   the same list of lengths gives the same length at each number
  `KeyWide Z ds`   **the premise**: at every list whose first entries are such as the rounds ds can
      draw, whatever is heard behind, the key points are as many and as long as at the challenges
      that are all 0
  `aloneOk_run`   the test on the named points says yes at a run's list
  `fits_of_blank_wide`   the first test at every list that the rounds in front can draw: the form of
      the last clause of `K5Seated` (Honest/K5/Law/Seated.lean)
  `jobs_fit_run`, `jobs_whole_run`   **the row's jobs fit, and no list of values is filled up or
      cut, at a run's list**

Beside `KeySizes` and `KeyLong` (Honest/K5/Law/Fits.lean). These two speak of a key point's length
number by number, where a number beyond the list reads as the empty point: they do not say how many
key points there are. `KeyWide` speaks of the list of lengths.

Who is meant to show `KeyWide`: whoever lays the reader of the key points. It is shown of one
reader: the one at the lookup's honest side (`keyOfK3`: `keyWide_K3`, Honest/K5/Law/KeyOfK3.lean).

Limits. Lengths and counts alone. Nothing on a value. Nothing is claimed on soundness, completeness
or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Fits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E)
open H2K5.Honest

/-! ## 1 The wide premise on the reader of the key points -/

/-- Two lists of key points with the same list of lengths have the same length at each number. -/
theorem sameSizes_of_map {zk zk' : Array (Array E)} (h : zk.map (·.size) = zk'.map (·.size)) :
    SameSizes zk zk' := by
  intro i
  have e : ∀ z : Array (Array E), (z.getD i #[]).size = (z.map (·.size)).getD i 0 := by
    intro z
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
    cases z[i]? <;> rfl
  rw [e, e, h]

/-- **A NAMED PUBLIC PREMISE on the reader of the key points, AT THE LISTS THAT A PART READS IN A
RUN**: at every list whose first entries are such as the declared rounds ds in front can draw,
whatever is heard behind them, the key points are as many and as long as at the challenges of these
shapes that are all 0: the list at which the maker of the public data asks its tests. It is a
definition: a premise's form. It speaks of lengths alone. -/
def KeyWide (Z : Seat5) (ds : List Fmt.DeclaredRound) : Prop :=
  ∀ front more : List Fmt.Drawn, drawsFit ds front = true →
    (Z.keyAt (front ++ more)).map (·.size) = (Z.keyAt (blankDraws ds)).map (·.size)

variable {Z : Seat5} {ds : List Fmt.DeclaredRound}

/-- **The test on the named points, at a run's list.** CONDITIONAL: `KeyWide`; the first test says
yes at the challenges that are all 0; the first entries are such as the rounds in front can draw. -/
theorem aloneOk_run (hW : KeyWide Z ds) (hb : Z.fits (blankDraws ds) = true)
    (front more : List Fmt.Drawn) (hf : drawsFit ds front = true) :
    aloneOk Z.P (chalOf Z (front ++ more)) = true := by
  unfold Seat5.fits at hb
  rw [Bool.and_eq_true] at hb
  rw [← hb.2]
  exact aloneOk_congr (P := Z.P) (c := chalOf Z (front ++ more)) (c' := chalOf Z (blankDraws ds))
    (sameSizes_of_map (hW front more hf))

/-- **The first test, at every list that the rounds in front can draw**: the form of the last clause
of `K5Seated`. CONDITIONAL: `KeyWide`; the test says yes at the challenges that are all 0. -/
theorem fits_of_blank_wide (hW : KeyWide Z ds) (hb : Z.fits (blankDraws ds) = true) :
    ∀ front, drawsFit ds front = true → Z.fits front = true := by
  intro front hf
  have ha := aloneOk_run hW hb front [] hf
  rw [List.append_nil] at ha
  have hl : front.length = (blankDraws ds).length := by
    have := congrArg List.length ((SumLaw.elems_of_fit ds front hf).trans (blank_elems ds).symm)
    rwa [List.length_map, List.length_map] at this
  have hb' := hb
  unfold Seat5.fits at hb' ⊢
  rw [Bool.and_eq_true] at hb' ⊢
  exact ⟨by rw [hl]; exact hb'.1, ha⟩

/-- **THE ROW's JOBS FIT AT A RUN's LIST**, at every input. CONDITIONAL: as `aloneOk_run`; the
planner's numbers are the shape's. -/
theorem jobs_fit_run (hW : KeyWide Z ds) (hb : Z.fits (blankDraws ds) = true)
    (hc : Z.P.counted = true) (front more : List Fmt.Drawn) (hf : drawsFit ds front = true)
    (w : K5In) : (jobs Z.P).fits Z.P.x w (chalOf Z (front ++ more)) = true :=
  jobs_fit (aloneOk_run hW hb front more hf) hc w

/-- **AT A RUN's LIST NO LIST OF VALUES OF THE ROW IS FILLED UP OR CUT**: `jobs_whole`
(Honest/K5/Law/Fits.lean) at the challenges that a part reads. CONDITIONAL: as `jobs_fit_run`. -/
theorem jobs_whole_run (hW : KeyWide Z ds) (hb : Z.fits (blankDraws ds) = true)
    (hc : Z.P.counted = true) (front more : List Fmt.Drawn) (hf : drawsFit ds front = true)
    (w : K5In) (q : Nat) (s : PartShape) (hq : (shapes Z.P.x)[q]? = some s) :
    match s with
    | .sum k => padTo k.lead ((jobs Z.P).alone q w (chalOf Z (front ++ more))) =
          (jobs Z.P).alone q w (chalOf Z (front ++ more)) ∧
        ∀ rs, padTo ((k.ends.map (·.n)).getD 0)
            (((jobs Z.P).sum q w (chalOf Z (front ++ more))).endsAt rs) =
          ((jobs Z.P).sum q w (chalOf Z (front ++ more))).endsAt rs
    | .one n => padTo n ((jobs Z.P).alone q w (chalOf Z (front ++ more))) =
        (jobs Z.P).alone q w (chalOf Z (front ++ more)) := by
  have h := jobs_whole (aloneOk_run hW hb front more hf) hc w q s hq
  cases s <;> exact h

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.sameSizes_of_map
#print axioms ProofFile.Honest.K5.aloneOk_run
#print axioms ProofFile.Honest.K5.fits_of_blank_wide
#print axioms ProofFile.Honest.K5.jobs_fit_run
#print axioms ProofFile.Honest.K5.jobs_whole_run
