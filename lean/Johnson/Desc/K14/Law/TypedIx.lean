-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/TypedIx.lean: the equations LocEq and RecEq, on vectors that are indexed by
numbers, are the library's typed rows on the folded row (Cb/Ld/LdFoldEq.lean, Cb/Ld/LdLin.lean) at
typed data of the encoded index that is made of the public shape.

The typed data (ixOf): a location is a number below 2 ^ logN; a full message is a row's message and
its random tail; the generator matrix is read off the plain function generatorAt; a seed of the
record gives each answer a point and a factor; the sample map's matrix has the equality vector at
the point in front of the pads, the factor times (1, X, X ^ 2) on the answer's own three pads, and 0
on the other pads.
Main names: genMatrix, fullOf, mulVec_iff (LocEq at x is: the generator matrix applied to the full
message has, at x, the fold of the column), recMat, rec_sum, sampleOf, ixOf, recOf, recRow_iff.

What is not claimed. That generatorAt gives the code's generator matrix. That the sample map has the
library's property (Sample.OK) at any number: the number, the radius of decoding and the decoder's
order are letters here. A seed's factor may be 0 in this type. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.Typed
import Johnson.Desc.K14.Law.MeansLoc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Model (Reading)

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## (loc_x) -/

/-- The generator matrix: a row for each location, a column for each entry of a full message. -/
def genMatrix (S : FoldeqShape) :
    Matrix (Fin (2 ^ S.index.code.logN)) (Fin S.index.code.ell ⊕ Fin S.index.code.r) K :=
  fun x k =>
    let g := generatorAt S.index.code x.val
    let f := g.f.map fun a => ρ.val (ofF a)
    match k with
    | .inl j => ρ.val (ofF g.messageScale) * bitsK (f.take S.index.code.logEll) j.val
    | .inr j => ρ.val (ofF g.tailScale) * bitsK (f.take S.index.code.logR) j.val

/-- The full message that a vector holds: the message from entry 0 on, the tail from tailFirst on.
-/
def fullOf (S : FoldeqShape) (U : Nat → K) : Fin S.index.code.ell ⊕ Fin S.index.code.r → K :=
  Sum.elim (fun j => U j.val) (fun j => U (S.tailFirst + j.val))

/-- **LocEq at x**: the generator matrix applied to the full message has, at x, the fold of the
column. -/
theorem mulVec_iff (S : FoldeqShape) (x : Fin (2 ^ S.index.code.logN)) (w : Nat → K) (rows : Nat)
    (col U : Nat → K) :
    LocEq ρ S (generatorAt S.index.code x.val) w rows col U ↔
      (genMatrix ρ S).mulVec (fullOf S U) x = ∑ r ∈ Finset.range rows, w r * col r := by
  have e : (genMatrix ρ S).mulVec (fullOf S U) x =
      ρ.val (ofF (generatorAt S.index.code x.val).messageScale) *
        (∑ j ∈ Finset.range S.index.code.ell,
          bitsK (((generatorAt S.index.code x.val).f.map fun a => ρ.val (ofF a)).take
            S.index.code.logEll) j * U j) +
      ρ.val (ofF (generatorAt S.index.code x.val).tailScale) *
        (∑ j ∈ Finset.range S.index.code.r,
          bitsK (((generatorAt S.index.code x.val).f.map fun a => ρ.val (ofF a)).take
            S.index.code.logR) j * U (S.tailFirst + j)) := by
    unfold Matrix.mulVec dotProduct
    rw [Fintype.sum_sum_type, Finset.mul_sum, Finset.mul_sum,
      ← Fin.sum_univ_eq_sum_range (fun j =>
        ρ.val (ofF (generatorAt S.index.code x.val).messageScale) *
          (bitsK (((generatorAt S.index.code x.val).f.map fun a => ρ.val (ofF a)).take
            S.index.code.logEll) j * U j)),
      ← Fin.sum_univ_eq_sum_range (fun j =>
        ρ.val (ofF (generatorAt S.index.code x.val).tailScale) *
          (bitsK (((generatorAt S.index.code x.val).f.map fun a => ρ.val (ofF a)).take
            S.index.code.logR) j * U (S.tailFirst + j)))]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by simp only [genMatrix, fullOf, Sum.elim_inl]; ring
    · exact Finset.sum_congr rfl fun j _ => by simp only [genMatrix, fullOf, Sum.elim_inr]; ring
  rw [e]
  rfl

/-! ## (rec_gamma) -/

/-- The sample map's matrix for answer i, at entry j of a row's message. -/
def recMat (s : IndexShape) (z : List K) (beta : K) (theta : Nat → K) (i j : Nat) : K :=
  if j < s.plain then eqK z j
  else if s.padPlace i 0 ≤ j ∧ j < s.padPlace i 0 + 3 then beta * theta (j - s.padPlace i 0)
  else 0

/-- That matrix applied to a message. -/
theorem rec_sum (s : IndexShape) (z : List K) (beta : K) (theta : Nat → K) (i : Nat) (u : Nat → K)
    (hi : i < s.answers) (hp : s.plain + 3 * s.answers = s.code.ell) :
    ∑ j ∈ Finset.range s.code.ell, recMat s z beta theta i j * u j =
      (∑ k ∈ Finset.range s.plain, eqK z k * u k) +
        ∑ t ∈ Finset.range 3, beta * theta t * u (s.padPlace i t) := by
  rw [← hp, Finset.sum_range_add, sum_blocks]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [recMat, if_pos (Finset.mem_range.1 hk)]
  · have h : ∀ a ∈ Finset.range s.answers,
        (∑ t ∈ Finset.range 3, recMat s z beta theta i (s.plain + (t + 3 * a)) *
          u (s.plain + (t + 3 * a))) =
        if i = a then ∑ t ∈ Finset.range 3, beta * theta t * u (s.padPlace a t) else 0 := by
      intro a _
      by_cases hia : i = a
      · subst hia
        rw [if_pos rfl]
        refine Finset.sum_congr rfl fun t ht => ?_
        have ht' := Finset.mem_range.1 ht
        have e : s.plain + (t + 3 * i) = s.padPlace i t := by
          unfold IndexShape.padPlace; omega
        rw [e, recMat, if_neg (by unfold IndexShape.padPlace; omega),
          if_pos (by unfold IndexShape.padPlace; omega)]
        have e2 : s.padPlace i t - s.padPlace i 0 = t := by
          unfold IndexShape.padPlace; omega
        rw [e2]
      · rw [if_neg hia]
        refine Finset.sum_eq_zero fun t ht => ?_
        have ht' := Finset.mem_range.1 ht
        rw [recMat, if_neg (by omega), if_neg (by unfold IndexShape.padPlace; omega), zero_mul]
    rw [Finset.sum_congr rfl h, Finset.sum_ite_eq, if_pos (Finset.mem_range.2 hi)]

/-- **The record's sample map**, typed. A seed gives each answer a point and a factor. err: a
letter. -/
def sampleOf [Fintype K] (s : IndexShape) (theta : Nat → K) (err : Nat) :
    Cb.Ood.Sample K (Fin s.code.ell) where
  D := Fin s.answers → (Fin s.cubeBits → K) × K
  S := Fin s.answers
  mat := fun sd a j => recMat s (List.ofFn (sd a).1) (sd a).2 theta a.val j.val
  err := err

/-- **The encoded index's typed data**, of the public shape. err, eM, rank: letters. -/
def ixOf [Fintype K] (S : FoldeqShape) (err eM : Nat)
    (rank : ((Fin S.index.v → Bool) → Fin S.index.code.ell ⊕ Fin S.index.code.r → K) → Nat) :
    Cb.LdIx K (Fin (2 ^ S.index.code.logN)) (Fin S.index.code.ell ⊕ Fin S.index.code.r)
      (Fin S.index.code.ell) where
  v := S.index.v
  G := genMatrix ρ S
  pl := Sum.inl
  Z := sampleOf S.index (fun t => ρ.val (thetaE t)) err
  eM := eM
  rank := rank

/-- The record's answers, typed: row r's answer a is entry r * answers + a. -/
def recOf (s : IndexShape) (y : Nat → K) : (Fin s.v → Bool) × Fin s.answers → K :=
  fun x => y (numOf s.v x.1 * s.answers + x.2.val)

/-- **RecEq at all answers is the typed row RecRow.** -/
theorem recRow_iff [Fintype K] (S : FoldeqShape) (err eM : Nat)
    (rank : ((Fin S.index.v → Bool) → Fin S.index.code.ell ⊕ Fin S.index.code.r → K) → Nat)
    (hp : S.index.plain + 3 * S.index.answers = S.index.code.ell)
    (sd : Fin S.index.answers → (Fin S.index.cubeBits → K) × K) (gam : Fin S.index.v → K)
    (y U : Nat → K) :
    (ixOf ρ S err eM rank).RecRow (sd, recOf S.index y) gam (fullOf S U) ↔
      ∀ a : Fin S.index.answers,
        RecEq S.index (List.ofFn (sd a).1) (sd a).2 (fun t => ρ.val (thetaE t)) a.val
          (fun r => eqK (List.ofFn gam) r) y U := by
  unfold Cb.LdIx.RecRow
  rw [funext_iff]
  refine forall_congr' fun a => ?_
  have hL : (ixOf ρ S err eM rank).Z.val sd ((ixOf ρ S err eM rank).msg (fullOf S U)) a =
      (∑ k ∈ Finset.range S.index.plain, eqK (List.ofFn (sd a).1) k * U k) +
        ∑ t ∈ Finset.range 3, (sd a).2 * ρ.val (thetaE t) * U (S.index.padPlace a.val t) := by
    rw [← rec_sum S.index _ _ (fun t => ρ.val (thetaE t)) a.val U a.isLt hp,
      ← Fin.sum_univ_eq_sum_range fun j =>
        recMat S.index (List.ofFn (sd a).1) (sd a).2 (fun t => ρ.val (thetaE t)) a.val j * U j]
    rfl
  have hR : (ixOf ρ S err eM rank).tgt (sd, recOf S.index y) gam a =
      ∑ r ∈ Finset.range S.index.rows,
        eqK (List.ofFn gam) r * y (r * S.index.answers + a.val) := by
    unfold Cb.LdIx.tgt
    show ∑ r : Fin S.index.v → Bool, Alg.eqk gam r * recOf S.index y (r, a) = _
    rw [sum_bits]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [eqK_ofFn, recOf, numOf_bitsOf _ _ (Finset.mem_range.1 hr)]
  rw [hL, hR]
  exact Iff.rfl

end Desc.K14.Law
