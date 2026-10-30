-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/ReadersSayCount.lean: the honest side of the kind "lookup"
(K3). The third clause of the caller's readers' law (`ReadersSay.count`,
Honest/K3/Law/SeatedWorth.lean), cut down to what is the caller's, and the three clauses together.
Conditional on the caller's columns' laws (`ColsSay` at the two points,
Honest/K3/Law/ReadersSayOf.lean; `PinsSay` here): `ReadersSay` holds of the very forms that the
seated text's folds yield, at the planes' values of data whose bits are the reading of their places.
Theorems, with one definition.

Terms. Honest/K3/GLOSSARY.md ("count, bits, planes", "form", "reader, readers", "world, worth").

What is shown.
  `PinsSay`: the named hypothesis, in one world: the form that the caller's second reader yields for
    a column is worth the column's cells, the cell of plane j counted 2 ^ j. It writes out the field
    pin of the library's `Meaning.Planes.K3HostPlanes` (Johnson/Meaning/PlanesLaw.lean), at the
    value of a form in that world; `ColsSay` at the two points writes out its fields bit0 and bit1.
    The tie: `hostPlanes_iff` (Honest/K3/Law/TiesSealedForms.lean [not in this library]).
  `num_planes`: the form of the row that sums the counts, under a reading of the places, is the
    planes' value under the count's pairs.
  `countFold_is`: the seated fold over the pins (`countFold`, SeatedWorth.lean) is the plain form
    `countAff`.
  `count_of_pins`: the third clause.
  `toHeard_zb`: the two points that `toHeard` gives are the hearing's.
  `readersSay_of`: the three clauses.

Hypotheses that remain, in `readersSay_of`.
  `hB0`, `hB1`, `hP`: `ColsSay` at the two points, `PinsSay`. Shown at the constant forms
    `readersAt` alone (Thread/ExchangePlanes.lean). The three together are the library's
    `K3HostPlanes`, written out; Honest/K3/Law/Total/PlanesAt341.lean calls a theorem of the
    library's that ends in that structure (`host_statedAll`, Johnson/Desc/Kinds/Law/PlanesArm.lean):
    it speaks of the head's link alone and has five hypotheses of its own.
  `h0`, `hbit`: the reading reads the place "zero" as 0, and each bit of the data (row below 2 ^ d,
    plane below 2 ^ w) is the reading of its place.
  `hNC`, `h5`, `hlm`, `hv`: on public numbers: NC ≤ 2 ^ cK, 5 ≤ lm ≤ kT + 5, v < 64.
  `hz0`, `hz1`: the two points have 5 + d coordinates.
  Besides: `toHeard` returns (`hg`), the data's public numbers are the library's (`hD`), and the
    three seated folds return (`ha0`, `ha1`, `hc`).
In the others: `hw`, `hn`: (in `num_planes`) the data's w is the face's mu; n + 2 = 2 ^ w. `h`: (in
`countFold_is`) the seated fold returns. `hsh`, `hD`, `hc`: (in `count_of_pins`) the heard
structure's shape; the data's numbers; the fold's return. `e`: (in `toHeard_zb`) `toHeard` returns.

How the proof goes. It rests on `Cb.Fo.PlaneClaims.countAff_value`
(OnBytes/Tie/Pv/Lookup/Forest/FoPlaneClaims.lean), `Cb.Fo.Pin.pin_sum` and `foldl_add_from`
(OnBytes/Tie/Pv/Lookup/Forest/FoPin.lean), and on `cornerW_count` and `sum_split`
(Honest/K3/Law/SpecPlanes.lean).

Users. Honest/K3/Law/Thread/ExchangePlanes.lean calls `readersSay_of`.

Limits. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.ReadersSayAt
import OnBytes.Tie.Pv.Lookup.Forest.FoPin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Spec
open OnBytes (E zeroE negE ofF)
open OnBytes.Model (Fork Aff Reading World)
open OnBytes.Model.Forest (Shape)
open OnBytes.K.Kc (Fl Tape)
open OnBytes.HonestTrace.Look (Data)
open VerifiableInference.Desc.K3 (HeardV faceOf toHeard toHeardG eqPairs)
open VerifiableInference.Desc.First.Look (planesAtF)
open ProofFile.Honest.K3.Law (countFold ReadersSay countPairs)
open Finset (range)

/-- **The caller's second columns' law, in one world**: the form that the caller's reader of the
pins yields for a column is worth the column's cells, the cell of plane j counted 2 ^ j; at every
column of the matrix. μ: a reading of the places. -/
def PinsSay (h : Shape) (lm : Nat) (μ : _root_.Fo.Pl → KE) (P : Nat → Aff) (Wd : World KE) : Prop :=
  ∀ col, col < h.NC * 2 ^ (h.kT + 5 - lm) →
    (P col).value Reading.gl Wd = Cb.Fo.Pin.pinColK lm μ col

/-- The form of the row that sums the counts is the planes' value under the count's pairs. -/
theorem num_planes {P : Type} (D : Data P KE) (f : LFace) (μ : P → KE) (hw : D.N.w = f.mu)
    (hn : D.N.n + 2 = 2 ^ D.N.w)
    (hbit : ∀ u j, u < 2 ^ D.N.d → j < 2 ^ D.N.w → D.bits u j = μ (D.N.bAt u j)) :
    _root_.Fo.valS (TwV.rowNum D.N).cf μ = planesOf D (countPairs f) := by
  show _root_.Fo.valS ((List.range (2 ^ D.N.d)).flatMap fun u =>
    (List.range (D.N.n + 2)).map fun j => (D.N.bAt u j, (2 : KE) ^ j)) μ = _
  rw [Cb.Fo.Pin.valS_flatMap]
  unfold planesOf
  rw [Finset.sum_congr rfl fun X _ => show cornerW (countPairs f) X * D.bitAt X =
    (fun u j => (2 : KE) ^ j * D.bits u j) (X / 2 ^ D.N.w) (X % 2 ^ D.N.w) by
      rw [cornerW_count, ← hw]; rfl,
    Nat.add_comm D.N.w D.N.d, pow_add,
    sum_split (2 ^ D.N.w) (by positivity) (fun u j => (2 : KE) ^ j * D.bits u j) (2 ^ D.N.d)]
  refine Finset.sum_congr rfl fun u hu => ?_
  unfold _root_.Fo.valS
  rw [List.map_map, _root_.Fo.lsum, hn]
  refine Finset.sum_congr rfl fun j hj => ?_
  show (2 : KE) ^ j * μ (D.N.bAt u j) = (2 : KE) ^ j * D.bits u j
  rw [hbit u j (Finset.mem_range.1 hu) (Finset.mem_range.1 hj)]

/-- **The seated fold over the pins is the plain form**, at the readers' forms. -/
theorem countFold_is (g' : OnBytes.Model.Forest.Heard) (lm : Nat) (pn : Nat → Option Aff)
    {F G : Fork} {t u : Tape} {c : Aff}
    (h : countFold g' lm (fun col => Fl.need (pn col)) F t = some (c, G, u)) :
    c = Cb.Fo.PlaneClaims.countAff g' lm (fun col => (pn col).getD {}) ∧ G = F ∧ u = t := by
  have h' : (List.range (g'.shape.NC * 2 ^ (g'.shape.kT + 5 - lm))).foldlM
      (fun (f : Aff) col => Fl.need (pn col) >>= fun y => (pure (f + y) : Fl Aff))
      (Aff.ofConst (negE (ofF (2 ^ g'.shape.v - g'.shape.padding).toUInt64))) F t =
      some (c, G, u) := h
  have k := fl_fold_need pn (fun f _ y => f + y) F t _ _ c G u h'
  unfold Cb.Fo.PlaneClaims.countAff
  exact k

/-- **Conditional on the caller's second columns' law (`PinsSay`): what the seated fold over the
pins yields is worth the planes' value under the count's pairs, less the number of keys that are no
padding.** No instance of these hypotheses is exhibited in this file. -/
theorem count_of_pins (h : Shape) (lm jLK : Nat) (θ : KE) (μ : _root_.Fo.Pl → KE)
    (h0 : μ .zero = 0) (hNC : h.NC ≤ 2 ^ h.cK) (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5) (hv : h.v < 64)
    (g' : OnBytes.Model.Forest.Heard) (hsh : g'.shape = h) (pn : Nat → Option Aff) (Wd : World KE)
    (hP : PinsSay h lm μ (fun col => (pn col).getD {}) Wd)
    (D : Data _root_.Fo.Pl KE) (hD : D.N = _root_.Fo.numsF h lm jLK θ)
    (hbit : ∀ u j, u < 2 ^ D.N.d → j < 2 ^ D.N.w → D.bits u j = μ (D.N.bAt u j))
    {F G : Fork} {t u : Tape} {c : Aff}
    (hc : countFold g' lm (fun col => Fl.need (pn col)) F t = some (c, G, u)) :
    c.value Reading.gl Wd =
      planesOf D (countPairs (faceOf h)) - ((2 ^ h.v - h.padding : Nat) : KE) := by
  have hw : D.N.w = (faceOf h).mu := by rw [hD]; rfl
  have hn : D.N.n + 2 = 2 ^ D.N.w := by rw [hD]; rfl
  rw [(countFold_is g' lm pn hc).1,
    Cb.Fo.PlaneClaims.countAff_value Reading.gl Wd g' lm _ (by rw [hsh]; exact hv), hsh]
  unfold Cb.Fo.Pin.countK
  rw [Cb.Fo.Pin.foldl_add_from,
    Finset.sum_congr rfl (fun col hcol => hP col (Finset.mem_range.1 hcol)),
    ← Cb.Fo.Pin.pin_sum h lm jLK θ μ h0 hNC h5 hlm, ← hD, num_planes D (faceOf h) μ hw hn hbit]
  ring

/-- The two points that `toHeard` gives are the hearing's. -/
theorem toHeard_zb {h : Shape} {g : HeardV} {g' : OnBytes.Model.Forest.Heard}
    (e : toHeard h (toHeardG g) = some g') : g'.zb 0 = g.zb0 ∧ g'.zb 1 = g.zb1 := by
  unfold toHeard at e
  split at e
  · simp only at e
    split at e
    · cases e
      exact ⟨rfl, rfl⟩
    · cases e
  · cases e

/-- **Conditional on the caller's columns' laws (`ColsSay` at the two points, `PinsSay`): the
caller's readers' law holds of the forms that the seated text's three folds yield.** No instance of
these hypotheses is exhibited in this file. -/
theorem readersSay_of (h : Shape) (lm jLK : Nat) (θ : KE) (μ : _root_.Fo.Pl → KE)
    (h0 : μ .zero = 0) (hNC : h.NC ≤ 2 ^ h.cK) (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5) (hv : h.v < 64)
    (g : HeardV) (g' : OnBytes.Model.Forest.Heard) (hg : toHeard h (toHeardG g) = some g')
    (hz0 : g.zb0.size = 5 + h.d) (hz1 : g.zb1.size = 5 + h.d)
    (b : Nat → Nat → Option Aff) (pn : Nat → Option Aff) (Wd : World KE)
    (hB0 : ColsSay h lm (_root_.Fo.rdL Reading.gl g.zb0) μ (fun col => (b 0 col).getD {}) Wd)
    (hB1 : ColsSay h lm (_root_.Fo.rdL Reading.gl g.zb1) μ (fun col => (b 1 col).getD {}) Wd)
    (hP : PinsSay h lm μ (fun col => (pn col).getD {}) Wd)
    (D : Data _root_.Fo.Pl KE) (hD : D.N = _root_.Fo.numsF h lm jLK θ)
    (hbit : ∀ u j, u < 2 ^ D.N.d → j < 2 ^ D.N.w → D.bits u j = μ (D.N.bAt u j))
    {F : Fork} {t : Tape} {a0 a1 c : Aff}
    (ha0 : planesAtF g' lm 0 (fun e col => Fl.need (b e col)) F t = some (a0, F, t))
    (ha1 : planesAtF g' lm 1 (fun e col => Fl.need (b e col)) F t = some (a1, F, t))
    (hc : countFold g' lm (fun col => Fl.need (pn col)) F t = some (c, F, t)) :
    ReadersSay (faceOf h) g (planesOf D) (2 ^ h.v - h.padding) a0 a1 c Wd := by
  obtain ⟨hsh, _, _, _⟩ := ProofFile.Honest.K3.Law.toHeard_fields hg
  obtain ⟨z0, z1⟩ := toHeard_zb hg
  refine ⟨?_, ?_, ?_⟩
  · have := at_of_cols h lm jLK θ μ h0 hNC h5 hlm g' hsh 0 (by rw [z0]; exact hz0) b Wd
      (by rw [z0]; exact hB0) D hD hbit ha0
    rw [z0] at this
    exact this
  · have := at_of_cols h lm jLK θ μ h0 hNC h5 hlm g' hsh 1 (by rw [z1]; exact hz1) b Wd
      (by rw [z1]; exact hB1) D hD hbit ha1
    rw [z1] at this
    exact this
  · exact count_of_pins h lm jLK θ μ h0 hNC h5 hlm hv g' hsh pn Wd hP D hD hbit hc

#print axioms ProofFile.Honest.K3.Law.Spec.num_planes
#print axioms ProofFile.Honest.K3.Law.Spec.countFold_is
#print axioms ProofFile.Honest.K3.Law.Spec.count_of_pins
#print axioms ProofFile.Honest.K3.Law.Spec.toHeard_zb
#print axioms ProofFile.Honest.K3.Law.Spec.readersSay_of

end ProofFile.Honest.K3.Law.Spec
