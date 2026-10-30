-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/FastLaw/Tie.lean: the honest side of the kind "lookup" (K3). At the
tie's steps the end values and the polynomial in Y of the filling that folds tables are the
specification's. Conditional on the hypotheses below. Theorems, and the definitions of two
hypotheses.

Terms. Honest/K3/GLOSSARY.md. In this file: the tie's steps are the stages `Stage.tie s`: masked
sumchecks without a variable. Their end values are roots of the two sides' product trees and powers
of them. Honest/K3/JobsFast.lean reads them off its arrays; the specification has them as products
in the library's field (`tieJob`, Johnson/HonestTrace/LookDefs.lean).

What is shown.
  `Sized`: the hypothesis on numbers and points: one part of keys, of one bit at least; from two to
    2 ^ mu planes; the shift's words are below the prime.
  `FactorFits`: the hypothesis on the public factor: the face's factor, read in the field, is the
    library's `padFac` (Cb/Pv/Lookup/Alg/PadAlg.lean) at the table's rows and the padding by rows.
  `tie_ends`, `tie_inY`, `tie_round`: the equations between the two fillings at step s: the same end
    values, the same polynomial in Y, the same list for the round polynomial.
  `tie_ends_read`, `tie_ends_ok`, `tie_inY_read`, `tie_inY_ok`: the two lists at step s, read in the
    field; and the words of their entries are below the prime.
  `Z_read`, `G_read`, `powerP_read`, `P_read`, `a_read`: the key side's root; plane j's root; the
    chain of powers (with `powerP_go`, `powerP_ok`); the public factor.
  `getD_ups`: entry i of a list read in the field. `sqMulY_read`: (p + Y mp) ^ 2 (g + Y mg), four
    coefficients.

Hypotheses that remain.
  `H`: `Sized f v p`.
  `A`: `FactorFits f row pads p`. The statements on the polynomial in Y (`tie_inY_read`, `tie_inY`)
    assume it at every step; their proof uses it at step 0 alone.
  `hs`: s + 2 ≤ planes. These are the steps of a lookup's row. (In `P_read`: s + 1 ≤ planes; in
    `powerP_read`: s + 1 ≤ W.)
  `hj`: (in `G_read`) j < 2 ^ mu. `hG`: (in `powerP_go`, `powerP_read`) the array reads as G below
    W; in `powerP_go`, without a name: k + 1 ≤ W. `hg`: (in `powerP_ok`) the array's entries have
    words below the prime.

Users. The files InY.lean and Rounds.lean of Honest/K3/FastLaw/ import this file.

Limits. `FactorFits` is a hypothesis here. At the face of a proof file's lookup it is shown in
`factor_real` (Honest/K3/FastLaw/Real.lean), conditional on the library's test on the shape;
`numsFit` (Honest/K3/JobsSpec.lean) tests it at one shift and one alpha. No statement of this file
says that either filling is right.
An instance of `Sized` and `FactorFits`: the small synthetic lookup of
Honest/K3/FastLaw/AllToy.lean [not in this library] (by evaluation).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.Levels

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.FastLaw
open OnBytes (E addE subE mulE zeroE oneE okE)
open OnBytes.Slice (readE readV readE_mul readE_add readE_sub readE_one readE_zero)
open OnBytes.HonestTrace.Look (tieJob sqMul addP)

/-! ## 1 The hypotheses -/

/-- **The hypothesis on numbers and points**: one part of keys, of one bit at least; from two to
2 ^ mu planes; the shift's words are below the prime. -/
structure Sized (f : LFace) (v : Nat) (p : Pts) : Prop where
  parts : f.parts = [v]
  one : 1 ≤ v
  two : 2 ≤ f.planes
  fit : f.planes ≤ 2 ^ f.mu
  theta : okE p.theta = true

/-- **The hypothesis on the public factor**: the face's factor, read in the field, is the library's
`padFac` at the table's rows and the padding by rows. -/
def FactorFits (f : LFace) (row : E → Nat → E) (pads : List (Nat × Nat)) (p : Pts) : Prop :=
  readE (f.factor p.theta p.alpha) =
    Cb.Lkp.padFac (fun u => readE (row p.theta u)) pads (readE p.alpha)

/-! ## 2 Small facts -/

/-- Entry i of a list read in the field. -/
theorem getD_ups : ∀ (m : List E) (i : Nat), (ups m).getD i 0 = readE (m.getD i zeroE)
  | [], i => by
    show ([] : List KE).getD i 0 = readE (([] : List E).getD i zeroE)
    rw [List.getD_nil, List.getD_nil, readE_zero]
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => getD_ups l i

/-- (p + Y mp) ^ 2 (g + Y mg). -/
theorem sqMulY_read (a g ma mg : E) :
    (Fast.sqMulY a g ma mg).map readE = sqMul (readE a) (readE g) (readE ma) (readE mg) := by
  unfold Fast.sqMulY sqMul
  simp only [List.map_cons, List.map_nil, readE_mul, readE_add]
  congr 1
  · ring
  congr 1
  · ring
  congr 1
  · ring
  congr 1
  ring

/-- The chain of powers, on any array that reads as G below W. -/
theorem powerP_go (g : Array E) (G : Nat → KE) (W : Nat) (hG : ∀ j < W, readV g j = G j) :
    ∀ k, k + 1 ≤ W →
      readE ((List.range k).foldl (fun q i => mulE (mulE q q) (g.getD (W - 2 - i) zeroE))
        (g.getD (W - 1) zeroE)) = Alg.Lookup.chainFrom G k (W - 1 - k)
  | 0, h => by
    show readV g (W - 1) = G (W - 1 - 0)
    rw [Nat.sub_zero]
    exact hG _ (by omega)
  | k + 1, h => by
    rw [List.range_succ, List.foldl_append]
    show readE (mulE (mulE _ _) (g.getD (W - 2 - k) zeroE)) = _
    rw [readE_mul, readE_mul, powerP_go g G W hG k (by omega)]
    show _ * _ * readV g (W - 2 - k) = _
    rw [hG _ (by omega), show W - 1 - k = W - 1 - (k + 1) + 1 by omega,
      show W - 2 - k = W - 1 - (k + 1) by omega]
    show _ = Alg.Lookup.chainFrom G k (W - 1 - (k + 1) + 1) ^ 2 * G (W - 1 - (k + 1))
    ring

theorem powerP_read (g : Array E) (G : Nat → KE) (W : Nat) (hG : ∀ j < W, readV g j = G j)
    {s : Nat} (hs : s + 1 ≤ W) :
    readE (Fast.powerP g W s) = Alg.Lookup.chainFrom G (W - 1 - s) s := by
  have h := powerP_go g G W hG (W - 1 - s) (by omega)
  rw [show W - 1 - (W - 1 - s) = s by omega] at h
  exact h

theorem powerP_ok (g : Array E) (hg : ∀ x, okE (g.getD x zeroE) = true) (W s : Nat) :
    okE (Fast.powerP g W s) = true := by
  unfold Fast.powerP
  generalize W - 1 - s = k
  cases k with
  | zero => exact hg _
  | succ k =>
    rw [List.range_succ, List.foldl_append]
    exact ok_mul _ _

/-! ## 3 The roots -/

section
variable (f : LFace) (row : E → Nat → E) (pads : List (Nat × Nat)) (w : Hidden) (p : Pts)
variable {v : Nat}

/-- **The key side's root.** Conditional on `Sized`. -/
theorem Z_read (H : Sized f v p) :
    readE ((srcAt f row w p).rootsFrom f.parts.length 0) = (datAt f row pads w p).Z := by
  have hk := (keyLvl_read f row pads w p H.parts H.one (Nat.zero_le v)).2 0 (by norm_num)
  have hD : (datAt f row pads w p).v = v := by
    show f.parts.headD 0 - 1 + 1 = v
    rw [H.parts]
    show v - 1 + 1 = v
    have := H.one
    omega
  have e : (srcAt f row w p).rootsFrom f.parts.length 0 =
      mulE oneE (((srcAt f row w p).keyLvl 0 0).getD 0 zeroE) := by
    rw [H.parts]
    rfl
  rw [e, readE_mul, readE_one, one_mul]
  show readV ((srcAt f row w p).keyLvl 0 0) 0 = _
  rw [hk]
  show Blocks.lvl 0 (datAt f row pads w p).v _ 0 0 = Cb.Lkp.keyProd (datAt f row pads w p).v _ _
  rw [Blocks.lvl_zero]
  unfold Cb.Lkp.keyProd Cb.Lkp.facK
  exact Finset.prod_congr rfl fun b _ => by simp

/-- **Plane j's root.** Conditional on `Sized`, at j < 2 ^ mu. -/
theorem G_read (H : Sized f v p) {j : Nat} (hj : j < 2 ^ f.mu) :
    readV ((srcAt f row w p).tabLvl 0) j = (datAt f row pads w p).G j := by
  rw [(tabLvl_read f row pads w p H.two H.theta (Nat.zero_le _)).2 j
    (by rw [Nat.zero_add]; exact hj)]
  show Blocks.lvl f.mu f.d _ 0 j = Cb.Lkp.tabProd f.d _ _ _ j
  rw [Blocks.lvl_zero]
  unfold Cb.Lkp.tabProd Cb.Lkp.facT
  refine Finset.prod_congr rfl fun u _ => ?_
  have h1 : (u * 2 ^ f.mu + j) / 2 ^ f.mu = u := by
    rw [Nat.mul_comm, Nat.mul_add_div (by positivity), Nat.div_eq_of_lt hj, Nat.add_zero]
  have h2 : (u * 2 ^ f.mu + j) % 2 ^ f.mu = j := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  have hw : (datAt f row pads w p).N.w = f.mu := rfl
  rw [hw, h1, h2]

/-- **The chain of powers.** Conditional on `Sized`, at s + 1 ≤ planes. -/
theorem P_read (H : Sized f v p) {s : Nat} (hs : s + 1 ≤ f.planes) :
    readE (Fast.powerP ((srcAt f row w p).tabLvl 0) f.planes s) = (datAt f row pads w p).Pc s := by
  rw [powerP_read _ (datAt f row pads w p).G f.planes
    (fun j hj => G_read f row pads w p H (lt_of_lt_of_le hj H.fit)) hs]
  show _ = Alg.Lookup.chainFrom _ (f.planes - 2 + 1 - s) s
  rw [show f.planes - 2 + 1 = f.planes - 1 by have := H.two; omega]

/-- The public factor. Conditional on `Sized` and `FactorFits`. -/
theorem a_read (H : Sized f v p) (A : FactorFits f row pads p) :
    readE (f.factor p.theta p.alpha) = (datAt f row pads w p).a := by
  rw [A]
  show _ = Cb.Lkp.padFac (fun u => up (row (down (up p.theta)) u)) pads (up p.alpha)
  rw [down_up _ H.theta]

/-! ## 4 The two lists at a step -/

/-- **The end values at step s, read in the field.** Conditional on `Sized`, at s + 2 ≤ planes. -/
theorem tie_ends_read (H : Sized f v p) {s : Nat} (hs : s + 2 ≤ f.planes) (rs : List E) :
    (((fastJobs f row).job (.tie s)).ends w p rs).map readE =
      (tieJob (datAt f row pads w p) s).ends (ups rs) := by
  have h0 : 0 < 2 ^ f.mu := by positivity
  cases s with
  | zero =>
    show [readE ((srcAt f row w p).rootsFrom f.parts.length 0),
        readE (Fast.powerP ((srcAt f row w p).tabLvl 0) f.planes 1),
        readV ((srcAt f row w p).tabLvl 0) 0] = [_, _, _]
    rw [Z_read f row pads w p H, P_read f row pads w p H (by omega), G_read f row pads w p H h0]
  | succ s =>
    show [readE (Fast.powerP ((srcAt f row w p).tabLvl 0) f.planes (s + 2)),
        readV ((srcAt f row w p).tabLvl 0) (s + 1)] = [_, _]
    rw [P_read f row pads w p H (by omega),
      G_read f row pads w p H (lt_of_lt_of_le (by omega) H.fit)]

/-- The words of their entries are below the prime. -/
theorem tie_ends_ok (s : Nat) (rs : List E) :
    ∀ x ∈ ((fastJobs f row).job (.tie s)).ends w p rs, okE x = true := by
  have hP := fun t => powerP_ok ((srcAt f row w p).tabLvl 0) (tabLvl_ok f row w p 0) f.planes t
  have hG := tabLvl_ok f row w p 0
  have hZ : okE ((srcAt f row w p).rootsFrom f.parts.length 0) = true := by
    unfold Fast.Src.rootsFrom
    generalize (List.range (f.parts.length - 0)).map _ = l
    induction l using List.reverseRecOn with
    | nil => rfl
    | append_singleton l a _ =>
      rw [List.foldl_append]
      exact ok_mul _ _
  cases s with
  | zero =>
    intro x hx
    have hx' : x ∈ [(srcAt f row w p).rootsFrom f.parts.length 0,
        Fast.powerP ((srcAt f row w p).tabLvl 0) f.planes 1,
        ((srcAt f row w p).tabLvl 0).getD 0 zeroE] := hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
    rcases hx' with rfl | rfl | rfl
    · exact hZ
    · exact hP 1
    · exact hG 0
  | succ s =>
    intro x hx
    have hx' : x ∈ [Fast.powerP ((srcAt f row w p).tabLvl 0) f.planes (s + 2),
        ((srcAt f row w p).tabLvl 0).getD (s + 1) zeroE] := hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
    rcases hx' with rfl | rfl
    · exact hP _
    · exact hG _

/-- **The polynomial in Y at step s, read in the field.** Conditional on `Sized` and `FactorFits`,
at s + 2 ≤ planes. -/
theorem tie_inY_read (H : Sized f v p) (A : FactorFits f row pads p) {s : Nat}
    (hs : s + 2 ≤ f.planes) (rs mk : List E) :
    (((fastJobs f row).job (.tie s)).inY w p rs mk).map readE =
      (tieJob (datAt f row pads w p) s).inY (ups rs) (ups mk) := by
  have h0 : 0 < 2 ^ f.mu := by positivity
  cases s with
  | zero =>
    show (addL [(srcAt f row w p).rootsFrom f.parts.length 0, mk.getD 0 zeroE]
        ((Fast.sqMulY (Fast.powerP ((srcAt f row w p).tabLvl 0) f.planes 1)
          (((srcAt f row w p).tabLvl 0).getD 0 zeroE) (mk.getD 1 zeroE) (mk.getD 2 zeroE)).map
          fun x => subE zeroE (mulE (f.factor p.theta p.alpha) x))).map readE =
      addP [(datAt f row pads w p).Z, (ups mk).getD 0 0]
        ((sqMul ((datAt f row pads w p).Pc 1) ((datAt f row pads w p).G 0) ((ups mk).getD 1 0)
          ((ups mk).getD 2 0)).map (-(datAt f row pads w p).a * ·))
    rw [← Z_read f row pads w p H, ← P_read f row pads w p H (by omega : 1 + 1 ≤ f.planes),
      ← G_read f row pads w p H h0, ← a_read f row pads w p H A, getD_ups, getD_ups, getD_ups]
    unfold Fast.sqMulY sqMul
    simp only [List.map_cons, List.map_nil, addL, addP, readE_add, readE_sub, readE_mul,
      readE_zero, OnBytes.Slice.readV]
    congr 1
    · ring
    congr 1
    · ring
    congr 1
    · ring
    congr 1
    ring
  | succ s =>
    show (Fast.sqMulY (Fast.powerP ((srcAt f row w p).tabLvl 0) f.planes (s + 2))
        (((srcAt f row w p).tabLvl 0).getD (s + 1) zeroE) (mk.getD 0 zeroE)
        (mk.getD 1 zeroE)).map readE =
      sqMul ((datAt f row pads w p).Pc (s + 1 + 1)) ((datAt f row pads w p).G (s + 1))
        ((ups mk).getD 0 0) ((ups mk).getD 1 0)
    rw [sqMulY_read, P_read f row pads w p H (by omega), getD_ups, getD_ups]
    show sqMul _ (readV ((srcAt f row w p).tabLvl 0) (s + 1)) _ _ = _
    rw [G_read f row pads w p H (lt_of_lt_of_le (by omega) H.fit)]

/-- The words of its coefficients are below the prime. -/
theorem tie_inY_ok (s : Nat) (rs mk : List E) :
    ∀ x ∈ ((fastJobs f row).job (.tie s)).inY w p rs mk, okE x = true := by
  cases s with
  | zero =>
    intro x hx
    have hx' : x ∈ addL [(srcAt f row w p).rootsFrom f.parts.length 0, mk.getD 0 zeroE]
        ((Fast.sqMulY (Fast.powerP ((srcAt f row w p).tabLvl 0) f.planes 1)
          (((srcAt f row w p).tabLvl 0).getD 0 zeroE) (mk.getD 1 zeroE) (mk.getD 2 zeroE)).map
          fun x => subE zeroE (mulE (f.factor p.theta p.alpha) x)) := hx
    unfold Fast.sqMulY at hx'
    simp only [List.map_cons, List.map_nil, addL, List.mem_cons, List.not_mem_nil,
      or_false] at hx'
    rcases hx' with rfl | rfl | rfl | rfl
    · exact ok_add _ _
    · exact ok_add _ _
    · exact ok_sub _ _
    · exact ok_sub _ _
  | succ s =>
    intro x hx
    have hx' : x ∈ Fast.sqMulY (Fast.powerP ((srcAt f row w p).tabLvl 0) f.planes (s + 2))
        (((srcAt f row w p).tabLvl 0).getD (s + 1) zeroE) (mk.getD 0 zeroE)
        (mk.getD 1 zeroE) := hx
    unfold Fast.sqMulY at hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
    rcases hx' with rfl | rfl | rfl | rfl
    · exact ok_mul _ _
    · exact ok_add _ _
    · exact ok_add _ _
    · exact ok_mul _ _

/-! ## 5 The equations between the two fillings -/

/-- **At a tie's step the two fillings have the same end values.** Conditional on `Sized f v p`, at
a step s with s + 2 ≤ planes. An instance: the small synthetic lookup of
Honest/K3/FastLaw/AllToy.lean [not in this library] (by evaluation). -/
theorem tie_ends (H : Sized f v p) {s : Nat} (hs : s + 2 ≤ f.planes) (rs : List E) :
    ((fastJobs f row).job (.tie s)).ends w p rs =
      ((specJobsAt f row pads).job (.tie s)).ends w p rs :=
  eq_downs (tie_ends_ok f row w p s rs) (tie_ends_read f row pads w p H hs rs)

/-- **At a tie's step the two fillings have the same polynomial in Y.** Conditional on `Sized f v p`
and `FactorFits f row pads p`, at a step s with s + 2 ≤ planes. An instance: the small synthetic
lookup of Honest/K3/FastLaw/AllToy.lean [not in this library] (by evaluation). -/
theorem tie_inY (H : Sized f v p) (A : FactorFits f row pads p) {s : Nat}
    (hs : s + 2 ≤ f.planes) (rs mk : List E) :
    ((fastJobs f row).job (.tie s)).inY w p rs mk =
      ((specJobsAt f row pads).job (.tie s)).inY w p rs mk :=
  eq_downs (tie_inY_ok f row w p s rs mk) (tie_inY_read f row pads w p H A hs rs mk)

/-- At a tie's step the two fillings yield the same list for the round polynomial: neither has
one. -/
theorem tie_round (s : Nat) (rs : List E) :
    ((fastJobs f row).job (.tie s)).round w p rs =
      ((specJobsAt f row pads).job (.tie s)).round w p rs := by
  cases s <;> rfl

end

end ProofFile.Honest.K3.FastLaw

#print axioms ProofFile.Honest.K3.FastLaw.tie_inY_ok
#print axioms ProofFile.Honest.K3.FastLaw.tie_ends
#print axioms ProofFile.Honest.K3.FastLaw.tie_inY
#print axioms ProofFile.Honest.K3.FastLaw.tie_round
#print axioms ProofFile.Honest.K3.FastLaw.getD_ups
#print axioms ProofFile.Honest.K3.FastLaw.sqMulY_read
#print axioms ProofFile.Honest.K3.FastLaw.powerP_go
#print axioms ProofFile.Honest.K3.FastLaw.powerP_read
#print axioms ProofFile.Honest.K3.FastLaw.powerP_ok
#print axioms ProofFile.Honest.K3.FastLaw.Z_read
#print axioms ProofFile.Honest.K3.FastLaw.G_read
#print axioms ProofFile.Honest.K3.FastLaw.P_read
#print axioms ProofFile.Honest.K3.FastLaw.a_read
#print axioms ProofFile.Honest.K3.FastLaw.tie_ends_read
#print axioms ProofFile.Honest.K3.FastLaw.tie_ends_ok
#print axioms ProofFile.Honest.K3.FastLaw.tie_inY_read
