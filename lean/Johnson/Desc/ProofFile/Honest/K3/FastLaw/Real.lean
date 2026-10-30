-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/FastLaw/Real.lean: the two fillings of a lookup's summands, as they
are seated at a proof file's lookup, yield the same lists. Conditional on the hypotheses below.
Theorems, with three definitions.

Terms. Honest/K3/GLOSSARY.md. In this file: `stages_agree` (Honest/K3/FastLaw/All.lean) compares
`fastJobs f row` with `specJobsAt f row pads`, the specification's filling at public numbers made of
the face. At a proof file's lookup of shape h the row is seated at two other terms
(Honest/K3/LotRow.lean): `specJobsF h lm jLK`, the specification's filling at the library's own
numbers `Fo.numsF` (OnBytes/Tie/Pv/Lookup/Forest/FoV.lean), of which the library's statements speak;
and `fastJobs (faceOf h) (rowOfFace (faceOf h))`, whose table is read off the face's `leaf` on
corners. This file compares these two.

What is shown, by the file's sections. There is one table in the middle: `rowLib h`, the library's
joined table `Fo.tabF h` (FoV.lean) laid back into the program's elements.
  1. `strip`, `spec_strip`: of the public numbers the five jobs read ten fields alone, none of which
     names a place: a structure without the fields that name places gives the same jobs.
  2. `rowLib`, `numsOf_real`, `spec_real`: the numbers made of the face, at `rowLib` and the
     library's padding, are the library's numbers without these fields. So the two fillings by the
     specification are one.
  3. `factor_real`: the hypothesis on the public factor (`FactorFits`, Honest/K3/FastLaw/Tie.lean)
     holds there.
  4. `tab_congr`, `srcOf_congr`, `fastJobs_congr`: the filling that folds tables reads the table's
     rows below 2 ^ d alone.
  5. `bitsL`, `sum_bits`, `corner_bits`, `rowOfFace_real`: on a corner the face's leaf is the
     library's row.
  6. `real_agree`, the main theorem: at every stage of the row that is a masked sumcheck the two
     seated fillings yield the same lists.

Hypotheses that remain, in `real_agree`.
  `hok`: `FoNums.ok h`, the library's test on the shape.
  `ht`: the shift's words are below the prime.
  `Z`: each point has as many coordinates as its stage has variables (`PtsSized`, All.lean).
In the theorems on the way. `h`: (in `tab_congr`, `srcOf_congr`, `fastJobs_congr`) the two rules, or
the two tables, agree below n, or below 2 ^ d. `hu`: (in `rowOfFace_real`, beside `hok`)
u < 2 ^ h.d. `factor_real` asks `hok` alone. Without a name, in front of arrows: in `bitsL_getD` and
`sum_bits`, a range; in `real_agree`, that the stage has a call.

Users. `agreeAt_real` (Honest/K3/FastLaw/Lift.lean).

Limits. No statement of this file says that either filling is right. Nothing is said at other
lengths of the lists of challenges than those that the masked sumcheck's part gives its job.
`rowLib` is a device of this proof: nothing is meant to run it.
An instance: Honest/K3/FastLaw/RealMember.lean [not in this library] (by evaluation): the hypotheses
of `real_agree` met together, and its conclusion evaluated at six stages.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.All
import Johnson.Desc.ProofFile.Honest.K3.JobsSpecTies

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.FastLaw
open Finset TwV
open OnBytes (E addE subE mulE zeroE oneE okE)
open OnBytes.Slice (readE readV readE_sub readE_one readE_zero)
open VerifiableInference.Desc.K3 (faceOf)

/-! ## 1 Without the fields that name places -/

/-- Public numbers without the fields that name a place: the ten fields that the jobs read stay. -/
def strip {P : Type} (N : TwV.Nums P KE) : TwV.Nums Unit KE where
  v' := N.v'
  d := N.d
  w := N.w
  n := N.n
  tab := N.tab
  pads := N.pads
  oK := N.oK
  oT := N.oT
  oE := N.oE
  oB := N.oB
  kAt := fun _ => none
  kC := fun _ => 0
  bAt := fun _ _ => ()
  ledTie := fun _ => noLed
  ledK := fun _ => noLed
  ledT := fun _ => noLed
  ledE := noLed
  ledB := noLed

/-- **The specification's filling does not read a place.** -/
theorem spec_strip {P : Type} (N : KE → TwV.Nums P KE) (s : Stage) :
    (specJobs N).job s = (specJobs fun theta => strip (N theta)).job s := by
  cases s with
  | key i m => cases i <;> rfl
  | _ => rfl

/-! ## 2 The numbers made of the face are the library's -/

/-- The library's joined table, laid back into the program's elements. -/
def rowLib (h : OnBytes.Model.Forest.Shape) (theta : E) (u : ℕ) : E :=
  down (_root_.Fo.tabF h (up theta) u)

theorem numsOf_real (h : OnBytes.Model.Forest.Shape) (lm jLK : ℕ) (theta : KE) :
    numsOf (faceOf h) (rowLib h) (FoNums.pads h) theta =
      strip (_root_.Fo.numsF h lm jLK theta) := by
  have ht : (fun u => up (rowLib h (down theta) u)) = _root_.Fo.tabF h theta := by
    funext u
    show up (down (_root_.Fo.tabF h (up (down theta)) u)) = _
    rw [up_down, up_down]
  show ({ v' := FoNums.v' h, d := h.d, w := 5, n := 30
          tab := fun u => up (rowLib h (down theta) u), pads := FoNums.pads h
          oK := FoNums.ordK h, oT := FoNums.ordT
          oE := OnBytes.Model.orderDefault (5 + h.d), oB := OnBytes.Model.orderDefault (5 + h.d)
          kAt := fun _ => none, kC := fun _ => 0, bAt := fun _ _ => ()
          ledTie := fun _ => noLed, ledK := fun _ => noLed, ledT := fun _ => noLed
          ledE := noLed, ledB := noLed } : TwV.Nums Unit KE) =
        { v' := FoNums.v' h, d := h.d, w := 5, n := 30
          tab := _root_.Fo.tabF h theta, pads := FoNums.pads h
          oK := FoNums.ordK h, oT := FoNums.ordT
          oE := (List.range (5 + h.d)).map (FoNums.placeOf (5 + h.d))
          oB := (List.range (5 + h.d)).map (FoNums.placeOf (5 + h.d))
          kAt := fun _ => none, kC := fun _ => 0, bAt := fun _ _ => ()
          ledTie := fun _ => noLed, ledK := fun _ => noLed, ledT := fun _ => noLed
          ledE := noLed, ledB := noLed }
  rw [ht, countDown_eq]

/-- **The two fillings by the specification are one**, stage by stage. -/
theorem spec_real (h : OnBytes.Model.Forest.Shape) (lm jLK : ℕ) (s : Stage) :
    (specJobsAt (faceOf h) (rowLib h) (FoNums.pads h)).job s = (specJobsF h lm jLK).job s := by
  have e : numsOf (faceOf h) (rowLib h) (FoNums.pads h) =
      fun theta => strip (_root_.Fo.numsF h lm jLK theta) := by
    funext theta
    exact numsOf_real h lm jLK theta
  show (specJobs (numsOf (faceOf h) (rowLib h) (FoNums.pads h))).job s = _
  rw [e]
  exact (spec_strip (fun theta => _root_.Fo.numsF h lm jLK theta) s).symm

/-! ## 3 The public factor -/

/-- **Conditional on `FoNums.ok h`: the hypothesis on the public factor holds at the face of shape
h, the library's table and the library's padding.** An instance: Honest/K3/FastLaw/RealMember.lean
[not in this library] (by evaluation). -/
theorem factor_real (h : OnBytes.Model.Forest.Shape) (hok : FoNums.ok h = true) (p : Pts) :
    FactorFits (faceOf h) (rowLib h) (FoNums.pads h) p := by
  have e := factor_tie h hok 0 0 ⟨fun _ _ _ => zeroE, fun _ _ => zeroE⟩ p
  have ht : (fun u => readE (rowLib h p.theta u)) = _root_.Fo.tabF h (up p.theta) := by
    funext u
    exact up_down _
  unfold FactorFits
  rw [ht]
  exact e

/-! ## 4 The filling that folds tables reads the rows below 2 ^ d alone -/

theorem tab_congr (n : ℕ) (g g' : ℕ → E) (h : ∀ i, i < n → g i = g' i) :
    (Array.range n).map g = (Array.range n).map g' := by
  refine Array.ext (by simp) fun i h1 _ => ?_
  have hi : i < n := by simpa using h1
  simp only [Array.getElem_map, Array.getElem_range]
  exact h i hi

theorem srcOf_congr (f : LFace) (row row' : E → ℕ → E) (w : Hidden) (theta alpha : E)
    (h : ∀ u, u < 2 ^ f.d → row theta u = row' theta u) :
    Fast.srcOf f row w theta alpha = Fast.srcOf f row' w theta alpha := by
  have e := tab_congr (2 ^ f.d) (fun u => subE (subE alpha oneE) (row theta u))
    (fun u => subE (subE alpha oneE) (row' theta u)) fun u hu => by
      show subE (subE alpha oneE) (row theta u) = subE (subE alpha oneE) (row' theta u)
      rw [h u hu]
  unfold Fast.srcOf
  simp only [e]

/-- **Two tables that agree below 2 ^ d give one filling that folds tables.** -/
theorem fastJobs_congr (f : LFace) (row row' : E → ℕ → E)
    (h : ∀ theta u, u < 2 ^ f.d → row theta u = row' theta u) :
    fastJobs f row = fastJobs f row' := by
  have e : ∀ w theta alpha, Fast.srcOf f row w theta alpha = Fast.srcOf f row' w theta alpha :=
    fun w theta alpha => srcOf_congr f row row' w theta alpha (h theta)
  unfold fastJobs Fast.stageJob
  simp only [e]

/-! ## 5 On a corner the face's leaf is the library's row -/

/-- The d lowest bits of u, the lowest first, as elements of the field. -/
def bitsL : ℕ → ℕ → List KE
  | 0, _ => []
  | d + 1, u => (if u % 2 = 1 then 1 else 0) :: bitsL d (u / 2)

theorem bitsL_length : ∀ d u, (bitsL d u).length = d
  | 0, _ => rfl
  | d + 1, u => by
    show (bitsL d (u / 2)).length + 1 = d + 1
    rw [bitsL_length d]

theorem bitsL_getD : ∀ (d u i : ℕ), i < d →
    (bitsL d u).getD i 0 = if u / 2 ^ i % 2 = 1 then 1 else 0
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | d + 1, u, 0, _ => by
    show (if u % 2 = 1 then (1 : KE) else 0) = _
    rw [pow_zero, Nat.div_one]
  | d + 1, u, i + 1, h => by
    show (bitsL d (u / 2)).getD i 0 = _
    rw [bitsL_getD d (u / 2) i (by omega), Nat.div_div_eq_div_mul, pow_succ']

/-- Under the equality weights at the corner of u, the weighted sum of F over the cube is F u. -/
theorem sum_bits : ∀ (d u : ℕ), u < 2 ^ d → ∀ F : ℕ → KE,
    ∑ x ∈ range (2 ^ d), eqN (bitsL d u) x * F x = F u
  | 0, u, h, F => by
    have e : u = 0 := by simpa using h
    subst e
    simp [bitsL, eqN]
  | d + 1, u, h, F => by
    have e := OnBytes.HonestTrace.Look.sum_cons (if u % 2 = 1 then (1 : KE) else 0)
      (bitsL d (u / 2)) F
    rw [List.length_cons, bitsL_length] at e
    have hu : u / 2 < 2 ^ d := by
      rw [pow_succ] at h
      omega
    show ∑ x ∈ range (2 ^ (d + 1)),
      eqN ((if u % 2 = 1 then (1 : KE) else 0) :: bitsL d (u / 2)) x * F x = F u
    rw [e, sum_bits d (u / 2) hu fun y => F (2 * y), sum_bits d (u / 2) hu fun y => F (2 * y + 1)]
    by_cases hb : u % 2 = 1
    · have e2 : 2 * (u / 2) + 1 = u := by omega
      rw [if_pos hb, e2]
      ring
    · have e2 : 2 * (u / 2) = u := by omega
      rw [if_neg hb, e2]
      ring

theorem list_sum_range (n : ℕ) (g : ℕ → KE) :
    ((List.range n).map g).sum = ∑ i ∈ range n, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]
    simp

/-- The corner of row u, translated, without the planes' coordinates: the bits of u. -/
theorem corner_bits (f : LFace) (u : ℕ) :
    (byBit (Fast.cornerOf f u)).drop f.mu = bitsL f.d u := by
  have hs : (Fast.cornerOf f u).size = f.mu + f.d := tab_size _ _
  apply List.ext_getElem
  · rw [List.length_drop, byBit_length, hs, bitsL_length]
    omega
  · intro i h1 h2
    have hi : i < f.d := by rwa [bitsL_length] at h2
    have hb : f.mu + i < (Fast.cornerOf f u).size := by rw [hs]; omega
    have hb' : f.mu + i < (byBit (Fast.cornerOf f u)).length := by rw [byBit_length]; exact hb
    rw [List.getElem_drop, ← List.getD_eq_getElem _ 0 hb', ← List.getD_eq_getElem _ 0 h2,
      byBit_getD _ _ hb, bitsL_getD _ _ _ hi, hs]
    have hj : f.mu + f.d - 1 - (f.mu + i) < f.mu + f.d := by omega
    have e : (Fast.cornerOf f u).getD (f.mu + f.d - 1 - (f.mu + i)) zeroE =
        if (u * 2 ^ f.mu).testBit (f.mu + f.d - 1 - (f.mu + f.d - 1 - (f.mu + i))) then oneE
        else zeroE := tab_getD _ _ hj
    have e2 : f.mu + f.d - 1 - (f.mu + f.d - 1 - (f.mu + i)) = f.mu + i := by omega
    have e3 : (u * 2 ^ f.mu) / 2 ^ (f.mu + i) = u / 2 ^ i := by
      rw [pow_add, Nat.mul_comm u, Nat.mul_div_mul_left _ _ (Nat.two_pow_pos _)]
    rw [e, e2, Nat.testBit_eq_decide_div_mod_eq, e3]
    by_cases hbit : u / 2 ^ i % 2 = 1
    · simp only [hbit, decide_true, if_true]
      exact readE_one
    · simp only [hbit, decide_false, if_false, Bool.false_eq_true]
      exact readE_zero

/-- **Conditional on `FoNums.ok h`: below 2 ^ d the table read off the face is the library's.**
An instance: Honest/K3/FastLaw/RealMember.lean [not in this library] (by evaluation). -/
theorem rowOfFace_real (h : OnBytes.Model.Forest.Shape) (hok : FoNums.ok h = true) (theta : E)
    (u : ℕ) (hu : u < 2 ^ h.d) : Fast.rowOfFace (faceOf h) theta u = rowLib h theta u := by
  have hs : (Fast.cornerOf (faceOf h) u).size = 5 + h.d := tab_size _ _
  have e := leaf_tie h hok 0 0 theta zeroE (Fast.cornerOf (faceOf h) u) hs
  have hc : (byBit (Fast.cornerOf (faceOf h) u)).drop 5 = bitsL h.d u := corner_bits (faceOf h) u
  rw [hc, list_sum_range, sum_bits h.d u hu] at e
  have er : up (Fast.rowOfFace (faceOf h) theta u) = _root_.Fo.tabF h (up theta) u := by
    show readE (subE (subE zeroE oneE)
      ((faceOf h).leaf theta zeroE (Fast.cornerOf (faceOf h) u))) = _
    rw [readE_sub, readE_sub, readE_zero, readE_one]
    have e' : readE ((faceOf h).leaf theta zeroE (Fast.cornerOf (faceOf h) u)) =
        readE zeroE - 1 - _root_.Fo.tabF h (up theta) u := e
    rw [e', readE_zero]
    ring
  show _ = down (_root_.Fo.tabF h (up theta) u)
  rw [← er]
  exact (down_up _ (ok_sub _ _)).symm

/-! ## 6 The theorem -/

/-- **Conditional on `FoNums.ok h`, on the shift's words and on the points' sizes: at a proof
file's lookup of shape h, at every stage of the row that is a masked sumcheck, the filling that
folds tables, with its table read off the face, and the specification's filling at the library's own
numbers yield the same lists**: the round polynomial behind fewer challenges than the stage has
variables; the polynomial in Y and the end values behind as many. An instance:
Honest/K3/FastLaw/RealMember.lean [not in this library] (by evaluation: the hypotheses met together;
the conclusion evaluated at six stages). -/
theorem real_agree (h : OnBytes.Model.Forest.Shape) (hok : FoNums.ok h = true) (lm jLK : ℕ)
    (w : Hidden) (p : Pts) (ht : okE p.theta = true) (Z : PtsSized (faceOf h) h.v p) :
    ∀ s ∈ stages (faceOf h), ∀ k, s.call (faceOf h) = some k →
      (∀ rs : List E, rs.length < k.vs.length →
        ((fastJobs (faceOf h) (Fast.rowOfFace (faceOf h))).job s).round w p rs =
          ((specJobsF h lm jLK).job s).round w p rs) ∧
      (∀ rs mk : List E, rs.length = k.vs.length →
        ((fastJobs (faceOf h) (Fast.rowOfFace (faceOf h))).job s).inY w p rs mk =
            ((specJobsF h lm jLK).job s).inY w p rs mk ∧
          ((fastJobs (faceOf h) (Fast.rowOfFace (faceOf h))).job s).ends w p rs =
            ((specJobsF h lm jLK).job s).ends w p rs) := by
  have e1 : fastJobs (faceOf h) (Fast.rowOfFace (faceOf h)) = fastJobs (faceOf h) (rowLib h) :=
    fastJobs_congr _ _ _ fun theta u hu => rowOfFace_real h hok theta u hu
  have hv := Cb.Fo.ok_v hok
  have H : Sized (faceOf h) h.v p :=
    ⟨rfl, by omega, by show (2 : ℕ) ≤ 32; omega, by show (32 : ℕ) ≤ 2 ^ 5; norm_num, ht⟩
  have hO : ∀ m < h.v, ((faceOf h).orders 0 m).Perm (List.range m) := fun m _ => by
    have e := _root_.Fo.ordK_perm h (Cb.Fo.ok_parts hok).1.1 m
    rwa [Nat.zero_add] at e
  intro s hs k hk
  have A := stages_agree (faceOf h) (rowLib h) (FoNums.pads h) w p H (factor_real h hok p) Z hO
    s hs k hk
  rw [e1, ← spec_real h lm jLK s]
  exact A

end ProofFile.Honest.K3.FastLaw

#print axioms ProofFile.Honest.K3.FastLaw.spec_strip
#print axioms ProofFile.Honest.K3.FastLaw.numsOf_real
#print axioms ProofFile.Honest.K3.FastLaw.spec_real
#print axioms ProofFile.Honest.K3.FastLaw.factor_real
#print axioms ProofFile.Honest.K3.FastLaw.srcOf_congr
#print axioms ProofFile.Honest.K3.FastLaw.fastJobs_congr
#print axioms ProofFile.Honest.K3.FastLaw.sum_bits
#print axioms ProofFile.Honest.K3.FastLaw.corner_bits
#print axioms ProofFile.Honest.K3.FastLaw.rowOfFace_real
#print axioms ProofFile.Honest.K3.FastLaw.real_agree
#print axioms ProofFile.Honest.K3.FastLaw.tab_congr
#print axioms ProofFile.Honest.K3.FastLaw.bitsL_length
#print axioms ProofFile.Honest.K3.FastLaw.bitsL_getD
#print axioms ProofFile.Honest.K3.FastLaw.list_sum_range
