-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/ReadersSayOf.lean: the honest side of the kind "lookup" (K3).
The caller's readers' law on the two points (`ReadersSay.at0`, `ReadersSay.at1`,
Honest/K3/Law/SeatedWorth.lean), cut down to what is the caller's. Conditional on the caller's
columns' law (`ColsSay`): each column's form is worth the column's cells under the weights on the
rows of the planes' matrix. Theorems, with one definition.

Terms. Honest/K3/GLOSSARY.md ("count, bits, planes", "form", "reader, readers", "world, worth").

What is shown.
  `ColsSay`: the named hypothesis, in one world: `(B col).value` is the sum, over the rows, of the
    row's weight (`Fo.phiBK`, OnBytes/Tie/Pv/Lookup/Forest/FoPlane.lean) times the cell (row, col).
    Its right side writes out the body of the library's `colsK`
    (OnBytes/Tie/Pv/Lookup/Forest/FoPlaneRows.lean); so it is the clause of the fields bit0 and bit1
    of the library's `Meaning.Planes.K3HostPlanes` (Johnson/Meaning/PlanesLaw.lean). The tie:
    `hostPlanes_iff` (Honest/K3/Law/TiesSealedForms.lean [not in this library]).
  `bits_ext`: the lookup's form on the bits, under a reading of the places, is the extension of the
    data's bits, where each bit of the data is the reading of its place.
  `planes_of_cols`: the planes' form (`planesAff`), folded up from the columns' forms, is worth the
    planes' value under the equality pairs of the point (`planesOf`, Honest/K3/Law/SpecLawful.lean;
    `eqPairs`, Johnson/Desc/First/Look/K3LookupGeneral.lean).

Hypotheses that remain, in `planes_of_cols`.
  `hB`: `ColsSay`. Shown at the constant forms `readersAt` alone (Thread/ExchangePlanes.lean).
  `h0`, `hbit`: the reading reads the place "zero" as 0, and each bit of the data (row below 2 ^ d,
    plane below 2 ^ w) is the reading of its place. So the bits are 0 at rows whose call's number is
    NC or more.
  `hNC`, `h5`, `hlm`, `hsh`, `hz`, `hD`: on the shape's public numbers, on the heard structure's
    shape and point, and on the data's public numbers.

How the proof goes. It rests on `Cb.Fo.PlaneClaims.planesAff_value`
(OnBytes/Tie/Pv/Lookup/Forest/FoPlaneClaims.lean), `Fo.plane_sum` (FoPlane.lean) and `planes_eq`
(Honest/K3/Law/SpecPlanes.lean).

Users. Honest/K3/Law/ReadersSayAt.lean imports this file.

Limits. No instance of these hypotheses is exhibited in this file. That the seated text's fold in
its own monad is `planesAff` is not shown here. The count's clause (`ReadersSay.count`) is not
reached.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.SeatedWorth
import Johnson.Desc.ProofFile.Honest.K3.Law.SpecPlanes
import OnBytes.Tie.Pv.Lookup.Forest.FoPlane

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Spec
open OnBytes (E zeroE)
open OnBytes.Model (Aff Reading World)
open OnBytes.Model.Forest (Shape)
open OnBytes.HonestTrace.Look (Data)
open VerifiableInference.Desc.K3 (eqPairs)
open Finset (range)

local notation "extL" => OnBytes.HonestTrace.Look.ext

/-- **The caller's columns' law, in one world**: the form that the caller's reader yields for a
column is worth the column's cells under the weights on the rows of the planes' matrix at the point
z (the top bit first), at every column of the matrix. μ: a reading of the places. -/
def ColsSay (h : Shape) (lm : Nat) (z : List KE) (μ : _root_.Fo.Pl → KE) (B : Nat → Aff)
    (Wd : World KE) : Prop :=
  ∀ col, col < h.NC * 2 ^ (h.kT + 5 - lm) → (B col).value Reading.gl Wd =
    ∑ row ∈ range (2 ^ lm), (_root_.Fo.phiBK h lm z).getD row 0 * μ (.cell row col)

/-- The lookup's form on the bits is the extension of the data's bits. -/
theorem bits_ext {P : Type} (D : Data P KE) (μ : P → KE)
    (hbit : ∀ u j, u < 2 ^ D.N.d → j < 2 ^ D.N.w → D.bits u j = μ (D.N.bAt u j)) (x : List KE) :
    _root_.Fo.valS (TwV.bitsForm D.N x) μ = extL (D.N.w + D.N.d) D.bitAt x := by
  unfold _root_.Fo.valS TwV.bitsForm OnBytes.HonestTrace.Look.ext
  rw [List.map_map, _root_.Fo.lsum]
  refine Finset.sum_congr rfl fun e he => ?_
  have he' : e < 2 ^ D.N.w * 2 ^ D.N.d := by
    rw [← pow_add]
    exact Finset.mem_range.1 he
  show TwV.eqN x e * μ (D.N.bAt (e / 2 ^ D.N.w) (e % 2 ^ D.N.w)) = TwV.eqN x e * D.bitAt e
  rw [← hbit _ _ (Nat.div_lt_of_lt_mul he') (Nat.mod_lt _ (by positivity))]
  rfl

/-- A fold reads its step at the list's entries alone. -/
theorem foldl_congr_mem {α β : Type} (g g' : β → α → β) : ∀ (l : List α) (b : β),
    (∀ b, ∀ a ∈ l, g b a = g' b a) → l.foldl g b = l.foldl g' b
  | [], _, _ => rfl
  | a :: l, b, h => by
    rw [List.foldl_cons, List.foldl_cons, h b a (by simp)]
    exact foldl_congr_mem g g' l _ fun b x hx => h b x (List.mem_cons_of_mem _ hx)

/-- **Conditional on the caller's columns' law (`ColsSay`): the planes' form is worth the planes'
value under the equality pairs of the point.** No instance of these hypotheses is exhibited in this
file. -/
theorem planes_of_cols (h : Shape) (lm jLK : Nat) (θ : KE) (μ : _root_.Fo.Pl → KE)
    (h0 : μ .zero = 0) (hNC : h.NC ≤ 2 ^ h.cK) (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5)
    (g' : OnBytes.Model.Forest.Heard) (hsh : g'.shape = h) (e : Nat)
    (hz : (g'.zb e).size = 5 + h.d) (B : Nat → Aff) (Wd : World KE)
    (hB : ColsSay h lm (_root_.Fo.rdL Reading.gl (g'.zb e)) μ B Wd)
    (D : Data _root_.Fo.Pl KE) (hD : D.N = _root_.Fo.numsF h lm jLK θ)
    (hbit : ∀ u j, u < 2 ^ D.N.d → j < 2 ^ D.N.w → D.bits u j = μ (D.N.bAt u j)) :
    (Cb.Fo.PlaneClaims.planesAff g' lm e B).value Reading.gl Wd =
      planesOf D (eqPairs (5 + h.d) (g'.zb e)) := by
  have hw : D.N.w + D.N.d = 5 + h.d := by rw [hD]; rfl
  have hx : byBit (g'.zb e) = (_root_.Fo.rdL Reading.gl (g'.zb e)).reverse := by
    unfold byBit ups _root_.Fo.rdL
    rw [List.map_reverse]
    rfl
  have hlen : (byBit (g'.zb e)).length = 5 + (h.kT + h.cK) := by
    unfold byBit ups
    simp only [List.length_map, List.length_reverse, Array.length_toList]
    exact hz
  -- The point, by coordinate, cut in four.
  obtain ⟨xp, xc, xl, xh, hcut, hp, hc, hl, hh⟩ : ∃ xp xc xl xh : List KE,
      byBit (g'.zb e) = xp ++ (xc ++ (xl ++ xh)) ∧ xp.length = 5 ∧ xc.length = h.cK ∧
        xl.length = lm - 5 ∧ xh.length = h.kT + 5 - lm := by
    refine ⟨(byBit (g'.zb e)).take 5, ((byBit (g'.zb e)).drop 5).take h.cK,
      (((byBit (g'.zb e)).drop 5).drop h.cK).take (lm - 5),
      (((byBit (g'.zb e)).drop 5).drop h.cK).drop (lm - 5), ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.take_append_drop, List.take_append_drop, List.take_append_drop]
    · rw [List.length_take, hlen]; omega
    · rw [List.length_take, List.length_drop, hlen]; omega
    · rw [List.length_take, List.length_drop, List.length_drop, hlen]; omega
    · rw [List.length_drop, List.length_drop, List.length_drop, hlen]; omega
  have hrev : _root_.Fo.rdL Reading.gl (g'.zb e) = (xp ++ (xc ++ (xl ++ xh))).reverse := by
    rw [← hcut, hx, List.reverse_reverse]
  rw [← hw, planes_eq D (g'.zb e) (by rw [hw]; exact hz), ← bits_ext D μ hbit, hcut, hD,
    _root_.Fo.plane_sum h lm jLK θ μ h0 hNC h5 hlm xp xc xl xh hp hc hl hh,
    Cb.Fo.PlaneClaims.planesAff_value, hsh, ← hrev]
  unfold _root_.Fo.planesK
  refine foldl_congr_mem _ _ _ _ fun b col hcol => ?_
  beta_reduce
  rw [hB col (List.mem_range.1 hcol)]

#print axioms ProofFile.Honest.K3.Law.Spec.bits_ext
#print axioms ProofFile.Honest.K3.Law.Spec.foldl_congr_mem
#print axioms ProofFile.Honest.K3.Law.Spec.planes_of_cols

end ProofFile.Honest.K3.Law.Spec
