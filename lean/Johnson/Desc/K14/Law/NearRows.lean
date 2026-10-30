--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/NearRows.lean: "near" from the stored table's rows before encoding, by
linearity, so that it need not be asked location by location.

NearAt (Johnson/Desc/K14/Law/LocNear.lean) counts the locations at which (loc_x)'s equation fails. A
real table has millions of locations, and the equation at one location is a sum over a whole row.
Here: if the stored column at every location is the code's symbol of each row, and the folded row u
is the rows' fold by the weights, then the equation holds at every location.

  genK                  row x of the code's generator matrix applied to a message with its tail:
                        (loc_x)'s left side. genK_sum: it is linear. genK_congr: what it reads.
  locAt_of_rows         the equation at one location, from the two facts above.
  nearAt_of_rows        NearAt, at every radius.
  foldRowsB             computes "u is the rows' fold by the weights", at the message's places and
                        the tail's: one comparison for each place.
  nearAt_of_foldRowsB   its yes, with the first fact, gives NearAt at every radius.

What is not claimed. That a table's columns are the code's symbols of any rows: that is a premise
here (hcol); Johnson/Desc/K14/Law/TabOfRows.lean defines a table of which it is a theorem. The
converse of any test. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K14.Law.NearB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Means (Words)

variable {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)

/-- Row x of the code's generator matrix, applied to a message with its random tail: (loc_x)'s left
side at v in u's place. -/
def genK (S : FoldeqShape) (x : Nat) (v : Nat → K) : K :=
  ρ.val (OnBytes.ofF (generatorAt S.index.code x).messageScale) *
      (∑ j ∈ Finset.range S.index.code.ell,
        bitsK (((generatorAt S.index.code x).f.map fun a => ρ.val (OnBytes.ofF a)).take
          S.index.code.logEll) j * v j) +
    ρ.val (OnBytes.ofF (generatorAt S.index.code x).tailScale) *
      (∑ j ∈ Finset.range S.index.code.r,
        bitsK (((generatorAt S.index.code x).f.map fun a => ρ.val (OnBytes.ofF a)).take
          S.index.code.logR) j * v (S.tailFirst + j))

/-- It is linear. -/
theorem genK_sum (S : FoldeqShape) (x n : Nat) (w : Nat → K) (M : Nat → Nat → K) :
    genK ρ S x (fun k => ∑ r ∈ Finset.range n, w r * M r k) =
      ∑ r ∈ Finset.range n, w r * genK ρ S x (M r) := by
  unfold genK
  simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ => ?_
    ring

/-- It reads the message's places and the tail's alone. -/
theorem genK_congr (S : FoldeqShape) (x : Nat) (v v' : Nat → K)
    (h1 : ∀ j < S.index.code.ell, v j = v' j)
    (h2 : ∀ j < S.index.code.r, v (S.tailFirst + j) = v' (S.tailFirst + j)) :
    genK ρ S x v = genK ρ S x v' := by
  unfold genK
  congr 2
  · exact Finset.sum_congr rfl fun j hj => by rw [h1 j (Finset.mem_range.1 hj)]
  · exact Finset.sum_congr rfl fun j hj => by rw [h2 j (Finset.mem_range.1 hj)]

/-- **Where the stored column at x is the code's symbol of each row, and u is the rows' fold by the
weights, (loc_x)'s equation holds at x.** M r: row r's message with its tail, laid out as u is. -/
theorem locAt_of_rows (p : Par) (d : St) (m : Words K) (tab : Nat → List UInt64) (x : Nat)
    (M : Nat → Nat → K)
    (hcol : ∀ r < (weights p.S d.loc).size,
      ρ.val (OnBytes.ofF ((tab x).toArray.getD r 0)) = genK ρ p.S.fold x (M r))
    (hu1 : ∀ j < p.S.fold.index.code.ell, uOf d.loc m j =
      ∑ r ∈ Finset.range (weights p.S d.loc).size,
        ρ.val ((weights p.S d.loc).getD r zeroE) * M r j)
    (hu2 : ∀ j < p.S.fold.index.code.r, uOf d.loc m (p.S.fold.tailFirst + j) =
      ∑ r ∈ Finset.range (weights p.S d.loc).size,
        ρ.val ((weights p.S d.loc).getD r zeroE) * M r (p.S.fold.tailFirst + j)) :
    LocAt ρ p d m tab x := by
  have e := genK_sum ρ p.S.fold x (weights p.S d.loc).size
    (fun r => ρ.val ((weights p.S d.loc).getD r zeroE)) M
  rw [← genK_congr ρ p.S.fold x (uOf d.loc m) _ hu1 hu2] at e
  unfold LocAt LocEq
  refine Eq.trans e (Finset.sum_congr rfl fun r hr => ?_)
  show _ = ρ.val ((weights p.S d.loc).getD r zeroE) *
    ρ.val (OnBytes.ofF ((tab x).toArray.getD r 0))
  rw [hcol r (Finset.mem_range.1 hr)]

open Classical in
/-- **So the folded row's code word is the fold of the table's columns at every location.** -/
theorem nearAt_of_rows (p : Par) (d : St) (m : Words K) (tab : Nat → List UInt64)
    (M : Nat → Nat → K)
    (hcol : ∀ x < 2 ^ p.S.fold.index.code.logN, ∀ r < (weights p.S d.loc).size,
      ρ.val (OnBytes.ofF ((tab x).toArray.getD r 0)) = genK ρ p.S.fold x (M r))
    (hu1 : ∀ j < p.S.fold.index.code.ell, uOf d.loc m j =
      ∑ r ∈ Finset.range (weights p.S d.loc).size,
        ρ.val ((weights p.S d.loc).getD r zeroE) * M r j)
    (hu2 : ∀ j < p.S.fold.index.code.r, uOf d.loc m (p.S.fold.tailFirst + j) =
      ∑ r ∈ Finset.range (weights p.S d.loc).size,
        ρ.val ((weights p.S d.loc).getD r zeroE) * M r (p.S.fold.tailFirst + j))
    (e' : Nat) : NearAt ρ p d m tab e' := by
  unfold NearAt
  rw [Finset.filter_false_of_mem fun x _ =>
    not_not.2 (locAt_of_rows ρ p d m tab x.val M (hcol x.val x.isLt) hu1 hu2)]
  exact Nat.zero_le _

/-- u is the rows' fold by the weights, at the message's places and the tail's: computed. ME r: row
r's message with its tail, as the program's elements. -/
def foldRowsB (p : Par) (d : St) (mE : Words E) (ME : Nat → Nat → E) : Bool :=
  let w := weights p.S d.loc
  ((List.range p.S.fold.index.code.ell).all fun j =>
    decide (mE d.loc.oU.oracle .main (d.loc.oU.lay.index j) =
      sumE w.size fun r => mulE (w.getD r zeroE) (ME r j))) &&
  ((List.range p.S.fold.index.code.r).all fun j =>
    decide (mE d.loc.oU.oracle .main (d.loc.oU.lay.index (p.S.fold.tailFirst + j)) =
      sumE w.size fun r => mulE (w.getD r zeroE) (ME r (p.S.fold.tailFirst + j))))

open Classical in
/-- **A yes of that one comparison, with the table's columns the code's symbols of the rows, gives
"near" at every radius.** -/
theorem nearAt_of_foldRowsB (p : Par) (d : St) (mE : Words E) (tab : Nat → List UInt64)
    (ME : Nat → Nat → E)
    (hcol : ∀ x < 2 ^ p.S.fold.index.code.logN, ∀ r < (weights p.S d.loc).size,
      ρ.val (OnBytes.ofF ((tab x).toArray.getD r 0)) =
        genK ρ p.S.fold x (fun k => ρ.val (ME r k)))
    (h : foldRowsB p d mE ME = true) (e' : Nat) : NearAt ρ p d (wordsOf ρ mE) tab e' := by
  simp only [foldRowsB, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  refine nearAt_of_rows ρ p d (wordsOf ρ mE) tab (fun r k => ρ.val (ME r k)) hcol ?_ ?_ e'
  · intro j hj
    have e := congrArg ρ.val (h.1 j hj)
    simp only [val_sumE, ρ.mul] at e
    exact e
  · intro j hj
    have e := congrArg ρ.val (h.2 j hj)
    simp only [val_sumE, ρ.mul] at e
    exact e

end Desc.K14.Law
