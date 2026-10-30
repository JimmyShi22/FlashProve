-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TermsTrips.lean: CONDITIONAL.

What is here. THE SECOND TOKEN SUMCHECK OF THE FEED-FORWARD LAYERS' ROUNDS: FROM ONE HYPOTHESIS ON
THE PRODUCTS OF ITS SUMMAND TO THREE OF THE NINE THAT THE CUBE's TIE (CubeSum.lean) ASKS OF A JOB.
The honest side's summand at a point z (`Sides.summand`, Johnson/Desc/K4/Honest/Sides.lean) is a sum
of products (weight, first factor, second factor). The hypothesis `TripsAt`: at z, and at ANY values
in the place of the shown factors, each product has the weight that it has at the first token; its
first factor is one of these values, or the combination, under the point's equality weights, of its
first factors at the tokens; its second factor is that combination of its second factors. It asks
besides that the reads at z and the products ARE MADE at every list of such values, as many products
as at the first token, and (its second field) that at each token a shown factor is that token's true
value; the equalities are of readings, not of words. From it, by algebra alone: the summand reads
the given values through the reading alone; along a line in them it is a polynomial of degree at
most 1; and at the extensions of the tokens' true values it is the sum over the products of the
weight times the two factors' extensions. Statements and proofs.

  `TokRows`, `wAt`, `aAt`, `bAt`, `shAt`   the tokens' rows; a product's weight at the first token;
     its factors, and a shown value, at a token
  `firstAt`, `firstAt_some`, `firstAt_none`, `TripsAt`   **the hypothesis**
  `foldl_trips`, `sum_by_number`, `trips_read`   the summand as a sum
  `getD_read`, `trips_alike`, `trips_poly`   it reads the values through the reading; a polynomial
     along a line
  `trips_end`   **at the extensions of the tokens' true values**

Limits. At the reading `Reading.gl`. `TripsAt` IS A HYPOTHESIS: NOTHING HERE SHOWS IT (KindsOf.lean,
`tripsAt_at`, has it for some idx, from premises on public data AND ON RETURNS of the honest side's
makers, and from the test `triPlainB` (TermsPubOf.lean's `triPlainB_of_lay` has it at a layout that
`wsLayOf` returns for a model with mixtures of experts, where `Sides.of` returns); no example of
these together is known at the full size (KindsOf.lean's Limits on the small plan)). It is a
hypothesis of statements on what an honest sum is worth; where it is false nothing is said. The job
of the sumcheck is not named here: the statements speak of the summand, of the tokens' rows
(`tokenRows`, Johnson/Desc/K4/Honest/Terms.lean) and of tables made of these.

No property is claimed.
-/
import Johnson.Desc.K4.Honest.Terms
import Johnson.Desc.K4.Honest.Law.CubeInY

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE maddE mulE)
open OnBytes.Model (Reading eqTab)
open OnBytes.Road (pt)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw
open Polynomial

/-- The tokens' rows, as `tokenRows` makes them. -/
abbrev TokRows : Type := Array (Array E × Array Trip)

/-- Product number k's weight at the first token. -/
def wAt (rows : TokRows) (k : ℕ) : E :=
  ((rows.getD 0 (#[], #[])).2.getD k (zeroE, zeroE, zeroE)).1

/-- Its first factor at token t. -/
def aAt (rows : TokRows) (t k : ℕ) : E :=
  ((rows.getD t (#[], #[])).2.getD k (zeroE, zeroE, zeroE)).2.1

/-- Its second factor at token t. -/
def bAt (rows : TokRows) (t k : ℕ) : E :=
  ((rows.getD t (#[], #[])).2.getD k (zeroE, zeroE, zeroE)).2.2

/-- The true value, at token t, of shown value number i. -/
def shAt (rows : TokRows) (t i : ℕ) : E := (rows.getD t (#[], #[])).1.getD i zeroE

/-- What product number k's first factor reads as at the point z, at the values e in the place of
the shown factors. idx k: the number of the shown value that it is; none: it is none. -/
noncomputable def firstAt (lt : ℕ) (rows : TokRows) (z : Array E) (idx : ℕ → Option ℕ)
    (e : Array E) (k : ℕ) : Cb.Gl.E :=
  match idx k with
  | some i => Reading.gl.val (e.getD i zeroE)
  | none => Blocks.ext lt (fun t => Reading.gl.val (aAt rows t k)) (pt Reading.gl z)

theorem firstAt_some {lt : ℕ} {rows : TokRows} {z : Array E} {idx : ℕ → Option ℕ} {e : Array E}
    {k i : ℕ} (h : idx k = some i) :
    firstAt lt rows z idx e k = Reading.gl.val (e.getD i zeroE) := by
  unfold firstAt
  rw [h]

theorem firstAt_none {lt : ℕ} {rows : TokRows} {z : Array E} {idx : ℕ → Option ℕ} {e : Array E}
    {k : ℕ} (h : idx k = none) :
    firstAt lt rows z idx e k =
      Blocks.ext lt (fun t => Reading.gl.val (aAt rows t k)) (pt Reading.gl z) := by
  unfold firstAt
  rw [h]

/-- **The products of the summand at a point z, at any values in the place of the shown factors.**
This defines a hypothesis; the definition claims nothing. -/
structure TripsAt (S : Sides) (rows : TokRows) (z : Array E) (idx : ℕ → Option ℕ) : Prop where
  /-- the products are made, as many as at the first token, and read as said -/
  made : ∀ e : Array E, ∃ R l, S.readsTok z = some R ∧
    S.trips R (eqTab z) (fun lm yv => (S.gatedUnder (eqTab z)).getD (S.routedAt lm yv) zeroE) e =
      some l ∧
    l.size = (rows.getD 0 (#[], #[])).2.size ∧ ∀ k, k < l.size →
      Reading.gl.val (l.getD k (zeroE, zeroE, zeroE)).1 = Reading.gl.val (wAt rows k) ∧
      Reading.gl.val (l.getD k (zeroE, zeroE, zeroE)).2.1 =
        firstAt S.v.y.h.lt rows z idx e k ∧
      Reading.gl.val (l.getD k (zeroE, zeroE, zeroE)).2.2 =
        Blocks.ext S.v.y.h.lt (fun t => Reading.gl.val (bAt rows t k)) (pt Reading.gl z)
  /-- at a token a shown factor is that token's true value -/
  shown : ∀ k i, idx k = some i → ∀ t, t < 2 ^ S.v.y.h.lt → aAt rows t k = shAt rows t i

/-! ## 1 The summand as a sum -/

/-- The summand's loop, read. -/
theorem foldl_trips : ∀ (l : List Trip) (s : E),
    Reading.gl.val (l.foldl (fun s x => maddE s x.1 (mulE x.2.1 x.2.2)) s) =
      Reading.gl.val s + (l.map fun x => Reading.gl.val x.1 *
        (Reading.gl.val x.2.1 * Reading.gl.val x.2.2)).sum
  | [], s => by simp
  | x :: l, s => by
    have hm : ∀ u v z : E, Reading.gl.val (maddE u v z) =
        Reading.gl.val u + Reading.gl.val v * Reading.gl.val z := OnBytes.Slice.readE_maddE
    rw [List.foldl_cons, foldl_trips l, hm, Reading.gl.mul, List.map_cons, List.sum_cons]
    ring

/-- A list's sum by the members' numbers. -/
theorem sum_by_number {α : Type} (d : α) (f : α → Cb.Gl.E) : ∀ l : List α,
    (l.map f).sum = ∑ k ∈ Finset.range l.length, f (l.getD k d)
  | [] => by simp
  | x :: l => by
    rw [List.map_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ',
      sum_by_number d f l]
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

variable {S : Sides} {rows : TokRows} {z : Array E} {idx : ℕ → Option ℕ}

/-- **The summand at z, at any values in the place of the shown factors.** -/
theorem trips_read (T : TripsAt S rows z idx) (e : Array E) :
    Reading.gl.val ((S.summand e z).getD zeroE) =
      ∑ k ∈ Finset.range (rows.getD 0 (#[], #[])).2.size, Reading.gl.val (wAt rows k) *
        (firstAt S.v.y.h.lt rows z idx e k *
          Blocks.ext S.v.y.h.lt (fun t => Reading.gl.val (bAt rows t k)) (pt Reading.gl z)) := by
  obtain ⟨R, l, hR, hl, hs, hk⟩ := T.made e
  have e1 : S.summand e z =
      some (l.foldl (fun s x => maddE s x.1 (mulE x.2.1 x.2.2)) zeroE) := by
    unfold Sides.summand
    rw [hR]
    show (S.trips R (eqTab z) _ e).bind _ = _
    rw [hl]
    rfl
  rw [e1, Option.getD_some, ← Array.foldl_toList, foldl_trips, Reading.gl.zero, zero_add,
    sum_by_number (zeroE, zeroE, zeroE), Array.length_toList, hs]
  refine Finset.sum_congr rfl fun k hk' => ?_
  have hk2 : k < l.size := by
    rw [hs]
    exact Finset.mem_range.mp hk'
  obtain ⟨a1, a2, a3⟩ := hk k hk2
  have eg : l.toList.getD k (zeroE, zeroE, zeroE) = l.getD k (zeroE, zeroE, zeroE) := by
    rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  rw [eg, a1, a2, a3]

/-! ## 2 Two of the three -/

/-- A member of an array of a list, read. -/
theorem getD_read (a : List E) (i : ℕ) :
    Reading.gl.val (a.toArray.getD i zeroE) = (a.map Reading.gl.val).getD i 0 := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD,
    List.getElem?_map]
  cases a[i]? with
  | none => exact Reading.gl.zero
  | some x => rfl

/-- **On two lists that read alike the summand's values read alike.** -/
theorem trips_alike (T : TripsAt S rows z idx) :
    ReadsAlike fun e => (S.summand e.toArray z).getD zeroE := by
  intro a b hab
  show Reading.gl.val ((S.summand a.toArray z).getD zeroE) =
    Reading.gl.val ((S.summand b.toArray z).getD zeroE)
  rw [trips_read T, trips_read T]
  refine Finset.sum_congr rfl fun k _ => ?_
  have ef : firstAt S.v.y.h.lt rows z idx a.toArray k =
      firstAt S.v.y.h.lt rows z idx b.toArray k := by
    unfold firstAt
    cases idx k with
    | none => rfl
    | some i =>
      show Reading.gl.val (a.toArray.getD i zeroE) = Reading.gl.val (b.toArray.getD i zeroE)
      rw [getD_read, getD_read, hab]
  rw [ef]

/-- **Along a line in the shown factors' values the summand is a polynomial of degree at most
1.** -/
theorem trips_poly (T : TripsAt S rows z idx) (ends m : List E) :
    PolyOn 1 fun y => (S.summand (maskedEnds ends m y).toArray z).getD zeroE := by
  have hk : ∀ k, ∃ p : Cb.Gl.E[X], p.natDegree ≤ 1 ∧ ∀ y,
      firstAt S.v.y.h.lt rows z idx (maskedEnds ends m y).toArray k =
        p.eval (Reading.gl.val y) := by
    intro k
    unfold firstAt
    cases idx k with
    | none =>
      exact ⟨C (Blocks.ext S.v.y.h.lt (fun t => Reading.gl.val (aAt rows t k)) (pt Reading.gl z)),
        by rw [natDegree_C]; exact Nat.zero_le 1, fun _ => eval_C.symm⟩
    | some i => exact PolyOn.entryA ends m i
  choose p hp1 hp2 using hk
  refine ⟨∑ k ∈ Finset.range (rows.getD 0 (#[], #[])).2.size, C (Reading.gl.val (wAt rows k)) *
    (C (Blocks.ext S.v.y.h.lt (fun t => Reading.gl.val (bAt rows t k))
      (pt Reading.gl z)) * p k), ?_, fun y => ?_⟩
  · exact natDegree_sum_le_of_forall_le _ _ fun k _ =>
      (natDegree_C_mul_le _ _).trans ((natDegree_C_mul_le _ _).trans (hp1 k))
  · rw [trips_read T, eval_finset_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eval_mul, eval_mul, eval_C, eval_C, hp2]
    ring

/-! ## 3 The third -/

/-- **At the extensions of the tokens' true values the summand is the sum over the products of the
weight times the two factors' extensions.** e: for each shown value the extension, at z, of the
table of its true values at the tokens, as it is read. -/
theorem trips_end (T : TripsAt S rows z idx) (e : Array E)
    (he : ∀ k i, idx k = some i → Reading.gl.val (e.getD i zeroE) =
      Blocks.ext S.v.y.h.lt (fun t => Reading.gl.val (shAt rows t i)) (pt Reading.gl z)) :
    Reading.gl.val ((S.summand e z).getD zeroE) =
      ∑ k ∈ Finset.range (rows.getD 0 (#[], #[])).2.size, Reading.gl.val (wAt rows k) *
        (Blocks.ext S.v.y.h.lt (fun t => Reading.gl.val (aAt rows t k)) (pt Reading.gl z) *
          Blocks.ext S.v.y.h.lt (fun t => Reading.gl.val (bAt rows t k)) (pt Reading.gl z)) := by
  rw [trips_read T]
  refine Finset.sum_congr rfl fun k _ => ?_
  have ef : firstAt S.v.y.h.lt rows z idx e k =
      Blocks.ext S.v.y.h.lt (fun t => Reading.gl.val (aAt rows t k)) (pt Reading.gl z) := by
    unfold firstAt
    cases hi : idx k with
    | none => rfl
    | some i =>
      show Reading.gl.val (e.getD i zeroE) = _
      rw [he k i hi]
      exact Blocks.ext_congr (fun t ht => by rw [T.shown k i hi t ht]) _
  rw [ef]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.firstAt_some
#print axioms ProofFile.Honest.K4.firstAt_none
#print axioms ProofFile.Honest.K4.foldl_trips
#print axioms ProofFile.Honest.K4.sum_by_number
#print axioms ProofFile.Honest.K4.trips_read
#print axioms ProofFile.Honest.K4.getD_read
#print axioms ProofFile.Honest.K4.trips_alike
#print axioms ProofFile.Honest.K4.trips_poly
#print axioms ProofFile.Honest.K4.trips_end
