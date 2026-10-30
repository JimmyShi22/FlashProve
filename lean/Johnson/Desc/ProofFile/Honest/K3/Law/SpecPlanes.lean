-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/SpecPlanes.lean: the honest side of the kind "lookup" (K3).
What `planesOf` (Honest/K3/Law/SpecLawful.lean) comes to at the three product forms that the
verifier's claims on the planes have. Theorems.

Terms. Honest/K3/GLOSSARY.md ("count, bits, planes", "relation after the challenge").

What is shown, by the file's sections.
  1. `cornerW_eq`, `eqPairs_eq`, `planes_eq`: at the equality pairs of a point: the extension of the
     bits at the translated point.
  2. `cornerW_append`, `cornerW_ones`, `cornerW_pows`, `cornerW_count`: at the pairs of the count:
     2 ^ j at a leaf of plane j.
  3. `sum_split`, `planes_count`: conditional on the relation after the challenge, and on bits that
     are 0 at planes that do not count: the counts add up to the number of keys that are no padding.

Hypotheses that remain. In `planes_count`: `hM`: the relation after the challenge (`Data.Mid`);
`hz`: the bits are 0 at planes that do not count; `hw`, `hroom`: the data's w is the face's mu; n +
2 ≤ 2 ^ w. `hz`: (in `eqPairs_eq`, `planes_eq`) the point's size. `hM`: (in `sum_split`) 0 < M.
`cornerW_pows` bears "j < 2 ^ mu" without a name.

Users. This file is imported by Honest/K3/Law/ReadersSayOf.lean and Honest/K3/Law/SpecProof.lean.

Limits. Facts on sums over the cube. No course is read here.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.SpecLawful
import Johnson.Desc.ProofFile.Honest.K3.JobsSpecPoints
import OnBytes.Tie.Pv.Lookup.Ends.PortA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Spec
open OnBytes (E zeroE oneE subE)
open OnBytes.Model (ofNat)
open OnBytes.Slice (readE readE_sub readE_one)
open OnBytes.HonestTrace.Look (Data ext)
open VerifiableInference.Desc.K3 (eqPairs)

variable {P : Type}

/-! ## 1 At the equality pairs of a point -/

theorem cornerW_eq : ∀ (l : List E) (X : Nat),
    cornerW (l.map fun x => (subE oneE x, x)) X = TwV.eqN (ups l) X
  | [], _ => rfl
  | x :: l, X => by
    show (if X % 2 = 1 then up x else up (subE oneE x)) * cornerW _ (X / 2) =
      (if X % 2 = 1 then up x else 1 - up x) * TwV.eqN (ups l) (X / 2)
    rw [cornerW_eq l (X / 2), show up (subE oneE x) = 1 - up x by
      show readE _ = _
      rw [readE_sub, readE_one]]

theorem eqPairs_eq (m : Nat) (z : Array E) (hz : z.size = m) :
    eqPairs m z = z.toList.reverse.map fun x => (subE oneE x, x) := by
  unfold eqPairs
  apply List.ext_getElem
  · simp [hz]
  · intro t h1 h2
    have ht : t < m := by simpa using h1
    simp only [List.getElem_map, List.getElem_range, List.getElem_reverse, Array.length_toList]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]
    simp [hz]

/-- **At the equality pairs of a point the planes come to the extension of the bits at the
translated point.** -/
theorem planes_eq (D : Data P KE) (z : Array E) (hz : z.size = D.N.w + D.N.d) :
    planesOf D (eqPairs (D.N.w + D.N.d) z) = ext (D.N.w + D.N.d) D.bitAt (byBit z) := by
  unfold planesOf ext
  rw [eqPairs_eq _ z hz]
  exact Finset.sum_congr rfl fun X _ => by rw [cornerW_eq]; rfl

/-! ## 2 At the pairs of the count -/

theorem cornerW_append : ∀ (l l' : List (E × E)) (X : Nat),
    cornerW (l ++ l') X = cornerW l (X % 2 ^ l.length) * cornerW l' (X / 2 ^ l.length)
  | [], l', X => by simp [cornerW]
  | p :: l, l', X => by
    have e1 : X % 2 ^ (l.length + 1) % 2 = X % 2 := by
      rw [pow_succ]
      exact Nat.mod_mul_left_mod _ _ _
    have e2 : X % 2 ^ (l.length + 1) / 2 = X / 2 % 2 ^ l.length := by
      rw [pow_succ, Nat.mul_comm]
      exact Nat.mod_mul_right_div_self _ _ _
    have e3 : X / 2 ^ (l.length + 1) = X / 2 / 2 ^ l.length := by
      rw [pow_succ, Nat.mul_comm, Nat.div_div_eq_div_mul]
    simp only [List.cons_append, cornerW, List.length_cons]
    rw [cornerW_append l l' (X / 2)]
    simp only [e1, e2, e3]
    ring

theorem cornerW_ones : ∀ (d X : Nat), cornerW (List.replicate d (oneE, oneE)) X = 1
  | 0, _ => rfl
  | d + 1, X => by
    rw [List.replicate_succ]
    show (if X % 2 = 1 then up oneE else up oneE) * cornerW _ (X / 2) = 1
    rw [cornerW_ones d, ite_self, mul_one]
    exact readE_one

theorem cornerW_pows : ∀ (mu j : Nat), j < 2 ^ mu →
    cornerW ((List.range mu).map fun t => (oneE, ofNat (2 ^ 2 ^ t))) j = 2 ^ j
  | 0, j, h => by
    have : j = 0 := by simpa using h
    subst this
    rfl
  | mu + 1, j, h => by
    rw [List.range_succ, List.map_append, cornerW_append, List.length_map, List.length_range,
      cornerW_pows mu _ (Nat.mod_lt _ (by positivity))]
    show _ * ((if j / 2 ^ mu % 2 = 1 then up (ofNat (2 ^ 2 ^ mu)) else up oneE) * 1) = _
    have hb : j / 2 ^ mu < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), Nat.mul_comm, ← pow_succ]
      exact h
    have hj := Nat.div_add_mod j (2 ^ mu)
    rw [show up (ofNat (2 ^ 2 ^ mu)) = ((2 ^ 2 ^ mu : Nat) : KE) from
      OnBytes.Ends.A.readE_ofNat _, show up oneE = 1 from readE_one, mul_one]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hb with h0 | h1
    · have h0' : j / 2 ^ mu = 0 := Nat.lt_one_iff.1 h0
      rw [h0'] at hj ⊢
      have hj' : j % 2 ^ mu = j := by simpa using hj
      simp only [Nat.zero_mod, Nat.zero_ne_one, if_false, mul_one]
      rw [hj']
    · rw [h1] at hj ⊢
      simp only [Nat.one_mod, if_true]
      conv_rhs => rw [← hj]
      rw [pow_add, Nat.mul_one]
      push_cast
      ring

/-- At the pairs of the count a leaf of plane j counts 2 ^ j. -/
theorem cornerW_count (f : LFace) (X : Nat) :
    cornerW (countPairs f) X = 2 ^ (X % 2 ^ f.mu) := by
  unfold countPairs
  rw [cornerW_append, cornerW_ones, mul_one, List.length_map, List.length_range,
    cornerW_pows f.mu _ (Nat.mod_lt _ (by positivity))]

/-! ## 3 The counts add up -/

/-- A sum over the numbers below n M, by quotient and remainder. -/
theorem sum_split (M : Nat) (hM : 0 < M) (G : Nat → Nat → KE) : ∀ n : Nat,
    ∑ X ∈ Finset.range (n * M), G (X / M) (X % M) =
      ∑ u ∈ Finset.range n, ∑ j ∈ Finset.range M, G u j
  | 0 => by simp
  | n + 1 => by
    rw [Nat.succ_mul, Finset.sum_range_add, sum_split M hM G n, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' := Finset.mem_range.1 hx
    rw [Nat.mul_comm n M, Nat.mul_add_div hM, Nat.mul_add_mod, Nat.div_eq_of_lt hx',
      Nat.mod_eq_of_lt hx', Nat.add_zero]

/-- **Conditional on the relation after the challenge: the counts add up.** Conditional besides on
bits that are 0 at planes that do not count, on w = mu and on n + 2 ≤ 2 ^ w. The right side is the
natural numbers' difference 2 ^ v - the padding's number, cast into the field. -/
theorem planes_count (f : LFace) (D : Data P KE) (hw : D.N.w = f.mu)
    (hroom : D.N.n + 2 ≤ 2 ^ D.N.w) (hz : ∀ u j, D.N.n + 2 ≤ j → D.bits u j = 0) (hM : D.Mid) :
    planesOf D (countPairs f) = ((2 ^ D.v - Cb.Lkp.padNum D.N.pads : Nat) : KE) := by
  rw [← hM.2.1]
  unfold planesOf
  rw [Finset.sum_congr rfl fun X _ => show cornerW (countPairs f) X * D.bitAt X =
    (fun u j => (2 : KE) ^ j * D.bits u j) (X / 2 ^ D.N.w) (X % 2 ^ D.N.w) by
      rw [cornerW_count, ← hw]; rfl,
    Nat.add_comm, pow_add,
    sum_split (2 ^ D.N.w) (by positivity) (fun u j => (2 : KE) ^ j * D.bits u j) (2 ^ D.N.d)]
  refine Finset.sum_congr rfl fun u _ => ?_
  refine (Finset.sum_subset (Finset.range_subset_range.2 hroom) fun j _ hj => ?_).symm
  rw [hz u j (by simpa using hj), mul_zero]

#print axioms ProofFile.Honest.K3.Law.Spec.cornerW_eq
#print axioms ProofFile.Honest.K3.Law.Spec.eqPairs_eq
#print axioms ProofFile.Honest.K3.Law.Spec.planes_eq
#print axioms ProofFile.Honest.K3.Law.Spec.cornerW_append
#print axioms ProofFile.Honest.K3.Law.Spec.cornerW_ones
#print axioms ProofFile.Honest.K3.Law.Spec.cornerW_pows
#print axioms ProofFile.Honest.K3.Law.Spec.cornerW_count
#print axioms ProofFile.Honest.K3.Law.Spec.sum_split
#print axioms ProofFile.Honest.K3.Law.Spec.planes_count

end ProofFile.Honest.K3.Law.Spec
