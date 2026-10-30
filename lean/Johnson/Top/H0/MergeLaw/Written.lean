-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/Written.lean: the merge of the claims on the weights at its WRITTEN rounds:
each written count, as a share of all written verifier messages of its round, is at most 2⁻¹ ^ 128.

Johnson/Top/H0/K11Caller/RoundsBelow.lean has the bound at the typed rounds: a count of bad typed
values over the number of typed values. A written verifier message is a string of hash blocks (and
of test bits, if the round has work); the format's sampler makes the typed value of it, and it is
not quite uniform. Johnson/Top/H0/MergeLaw/Maps.lean reads the written rounds as the typed ones
(`mergeMaps`); the written counts are the maps' image of the proved block's
(`Maps.err`, OnBytes/Flat/CarrySMaps.lean: a typed count times the sampler's weight). Here the
library's `Maps.HeldN 128` (OnBytes/Flat/CarrySNum.lean) is filled at each of the merge's rounds,
so `Maps.below_pow` gives the bound. Definitions, and theorems with their proofs.

WHERE THE 128 BITS COME FROM, round by round.
  The field's size: it has q ≥ 2 ^ 191 elements. The typed counts are n - 1 (the batching round, n
    claims), 1, 2 for each column bit, 1 out of q - 1 (the further variable), 0 (the end value). At
    n - 1 ≤ 2 ^ 62 each is a share of at most 2 ^ -129 of its round's typed values.
  The sampler's bias: a factor 1 + 2 ^ -128 for each hash block of the round: five blocks where one
    element is drawn, nine where the element is other than 0. It uses up less than the one bit that
    is left.
  Work: none is needed. A round's bits of work stand on the right side of the comparison and only
    help; the statement holds whatever their number.

Main names:
  `OneElem d`, `OneNZ d`: the written round d draws one element, or one element other than 0, and
    nothing else; its kind is neither seeds nor sealed. Conditions on d's entry and kind alone.
  `MergeWr`: these, of the merge's written rounds but the last, of which nothing is asked.
  `StepN`, `HeldL`, `heldN_of_list`: `Maps.HeldN` from the list of the typed counts.
  `merge_heldN`, `merge_written`: `Maps.HeldN 128`; `Err.Below` of the written counts at 2⁻¹ ^ 128.
  `K11Written`, `k11Written`: the same as one closed proposition; its proof.

Limits. The premises: `MergeDs` (Maps.lean) and `MergeWr` of the written rounds, which are letters:
no written round is taken from a plan here; n - 1 ≤ 2 ^ 62. A share is a count among all strings of
hash blocks and test bits: nothing on the hash function. A bound on each round, not on a sum over
rounds. That the typed counts bound a prover's chance is `WeightsL.knowAt`'s. It is no soundness of
the protocol. Nothing on hiding.

-/
import Johnson.Top.H0.MergeLaw.Maps
import OnBytes.Flat.CarrySNum
import OnBytes.Slice.HeldCounts
import OnBytes.Slice.RatesTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open Iop IOR Cb Cb.Pv.Lay Johnson.L5.Layers
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open _root_.Run (bsRound planDraws_law)
open scoped ENNReal

/-! ### What is asked of a written round -/

/-- The written round draws one element and nothing else. -/
structure OneElem (d : RDT) : Prop where
  drawE : d.entry.drawE = 1
  drawNZ : d.entry.drawNZ = 0
  poss : d.entry.poss = 0
  trits : d.entry.trits = 0
  logN : d.entry.logN ≤ 64
  k1 : d.kind ≠ .seeds
  k2 : d.kind ≠ .sealed

/-- The written round draws one element other than 0 and nothing else. -/
structure OneNZ (d : RDT) : Prop where
  drawE : d.entry.drawE = 1
  drawNZ : d.entry.drawNZ = 1
  poss : d.entry.poss = 0
  trits : d.entry.trits = 0
  logN : d.entry.logN ≤ 64
  k1 : d.kind ≠ .seeds
  k2 : d.kind ≠ .sealed

theorem OneElem.vals {d : RDT} (h : OneElem d) :
    nVals (Fmt.dsOf d.entry d.kind) = Fmt.Fld.two.p ^ 3 := by
  rw [nVals_dsOf _ _ h.k1 h.k2, h.drawE, h.drawNZ, h.poss, h.trits]
  simp

theorem OneNZ.vals {d : RDT} (h : OneNZ d) :
    nVals (Fmt.dsOf d.entry d.kind) = Fmt.Fld.two.p ^ 3 - 1 := by
  rw [nVals_dsOf _ _ h.k1 h.k2, h.drawE, h.drawNZ, h.poss, h.trits]
  simp

/-- Five hash blocks. -/
theorem OneElem.blocks {d : RDT} (h : OneElem d) : (bsRound .two d.entry d.kind).b = 5 := by
  rw [(planDraws_law .two d.entry d.kind h.logN).2]
  unfold Fmt.wordsAtMost Fmt.blocksFor
  rw [h.poss, h.drawE, h.drawNZ, h.trits, if_neg h.k2]

/-- Nine hash blocks. -/
theorem OneNZ.blocks {d : RDT} (h : OneNZ d) : (bsRound .two d.entry d.kind).b = 9 := by
  rw [(planDraws_law .two d.entry d.kind h.logN).2]
  unfold Fmt.wordsAtMost Fmt.blocksFor
  rw [h.poss, h.drawE, h.drawNZ, h.trits, if_neg h.k2]

/-- The field's number of elements, in the format's words. -/
theorem p3_big : 2 ^ 191 ≤ Fmt.Fld.two.p ^ 3 := by
  rw [← card_GE]
  exact card_GE_big

/-! ### The comparisons of natural numbers -/

/-- One element, five hash blocks, a count of at most 2 ^ 62, any work. -/
theorem elem_num128 (e q w : ℕ) (he : e ≤ 2 ^ 62) (hq : 2 ^ 191 ≤ q) :
    (2 ^ 128 + 1) ^ 5 * e * 2 ^ 128 ≤ (2 ^ 128) ^ 5 * q * 2 ^ w := by
  have h0 : (2 ^ 128 + 1) ^ 5 * 2 ^ 62 * 2 ^ 128 ≤ (2 ^ 128) ^ 5 * 2 ^ 191 := by decide +kernel
  calc (2 ^ 128 + 1) ^ 5 * e * 2 ^ 128 ≤ (2 ^ 128 + 1) ^ 5 * 2 ^ 62 * 2 ^ 128 :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ he)
    _ ≤ (2 ^ 128) ^ 5 * 2 ^ 191 := h0
    _ ≤ (2 ^ 128) ^ 5 * q := Nat.mul_le_mul_left _ hq
    _ ≤ (2 ^ 128) ^ 5 * q * 2 ^ w := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos w)

/-- One element other than 0, nine hash blocks, the count 1, any work. -/
theorem nz_num128 (q w : ℕ) (hq : 2 ^ 191 ≤ q) :
    (2 ^ 128 + 1) ^ 9 * 1 * 2 ^ 128 ≤ (2 ^ 128) ^ 9 * (q - 1) * 2 ^ w := by
  have h0 : (2 ^ 128 + 1) ^ 9 * 1 * 2 ^ 128 ≤ (2 ^ 128) ^ 9 * (2 ^ 191 - 1) := by decide +kernel
  calc (2 ^ 128 + 1) ^ 9 * 1 * 2 ^ 128 ≤ (2 ^ 128) ^ 9 * (2 ^ 191 - 1) := h0
    _ ≤ (2 ^ 128) ^ 9 * (q - 1) := Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hq 1)
    _ ≤ (2 ^ 128) ^ 9 * (q - 1) * 2 ^ w := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos w)

/-! ### `Maps.HeldN` from the list of the typed counts -/

/-- The clause of `Maps.HeldN k` at one written round d and one typed count e. -/
def StepN (k : ℕ) (d : RDT) (e : ℕ) : Prop :=
  ∃ n D : ℕ, 0 < D ∧ e * D ≤ n * nVals (Fmt.dsOf d.entry d.kind) ∧
    (2 ^ 128 + 1) ^ (bsRound .two d.entry d.kind).b * n * 2 ^ k ≤
      (2 ^ 128) ^ (bsRound .two d.entry d.kind).b * D * 2 ^ d.entry.work

theorem OneElem.step {d : RDT} (h : OneElem d) (e : ℕ) (he : e ≤ 2 ^ 62) : StepN 128 d e := by
  refine ⟨e, Fmt.Fld.two.p ^ 3, lt_of_lt_of_le (by positivity) p3_big, ?_, ?_⟩
  · rw [h.vals]
  · rw [h.blocks]
    exact elem_num128 e _ _ he p3_big

theorem OneNZ.step {d : RDT} (h : OneNZ d) : StepN 128 d 1 := by
  refine ⟨1, Fmt.Fld.two.p ^ 3 - 1, ?_, ?_, ?_⟩
  · have := p3_big
    have h2 : 2 ≤ 2 ^ 191 := by decide +kernel
    omega
  · rw [h.vals]
  · rw [h.blocks]
    exact nz_num128 _ _ p3_big

/-- A count of 0 asks nothing of the round. -/
theorem step_zero (k : ℕ) (d : RDT) : StepN k d 0 := ⟨0, 1, Nat.one_pos, by simp, by simp⟩

/-- The clauses along the maps, at a list of counts. -/
def HeldL (k : ℕ) : {ds : List RDT} → {s' : Shape} → Maps ds s' → List ℕ → Prop
  | _, _, .nil, _ => True
  | _, _, .step (d := d) _ rest, e :: l => StepN k d e ∧ HeldL k rest l
  | _, _, .step _ _, [] => False
  | _, _, .skip _ rest, l => HeldL k rest l

theorem heldN_of_list {k : ℕ} : ∀ {ds : List RDT} {s' : Shape} (M : Maps ds s') (ε : Err s'),
    HeldL k M (TWhole.errList ε) → M.HeldN k ε
  | _, _, .nil, _, _ => trivial
  | _, _, .step (d := d) _ rest, (e, ε), h => by
      have h' : StepN k d e ∧ HeldL k rest (TWhole.errList ε) := h
      exact ⟨h'.1, heldN_of_list rest ε h'.2⟩
  | _, _, .skip _ rest, ε, h => heldN_of_list rest ε h

/-- The list of counts does not mind a cast along an equation of shapes. -/
theorem errList_cast {s t : Shape} (h : s = t) (δ : Err t) :
    TWhole.errList (h ▸ δ : Err s) = TWhole.errList δ := by
  subst h
  rfl

/-! ### The merge -/

/-- What is asked of the merge's written rounds, beside `MergeDs`. Of the last, the round of the end
value, nothing. -/
structure MergeWr (dZ d0 : RDT) (ds : List RDT) (dY : RDT) : Prop where
  z : OneElem dZ
  o : OneElem d0
  r : ∀ d ∈ ds, OneElem d
  y : OneNZ dY

theorem mid_heldL (dY dV : RDT) (hY : OneNZ dY) : ∀ ds : List RDT, (∀ d ∈ ds, OneElem d) →
    HeldL 128 (midMaps dY dV ds) (List.replicate ds.length 2 ++ [1, 0])
  | [], _ => ⟨hY.step, step_zero 128 dV, trivial⟩
  | d :: ds, h =>
      ⟨(h d List.mem_cons_self).step 2 (by decide +kernel),
        mid_heldL dY dV hY ds fun d' hd' => h d' (List.mem_cons_of_mem _ hd')⟩

/-- **`Maps.HeldN 128` at the merge's written rounds.** -/
theorem merge_heldN (G : WeightsL GE) (Ex : ExtSpec) {dZ d0 : RDT} {ds : List RDT} {dY dV : RDT}
    (hk : ds.length = G.k) (H : MergeWr dZ d0 ds dY) (hn : G.n - 1 ≤ 2 ^ 62) :
    (mergeMaps G Ex dZ d0 ds dY dV hk).HeldN 128 (G.eps (Kc := Unit) (G.L.V1 Ex)) := by
  unfold mergeMaps
  refine Maps.heldN_castT (merge_shape G Ex ds hk) (heldN_of_list _ _ ?_)
  rw [errList_cast (merge_shape G Ex ds hk), G.errs (G.L.V1 Ex), ← hk]
  exact ⟨H.z.step _ hn, H.o.step 1 (by decide +kernel), mid_heldL dY dV H.y ds H.r⟩

/-- **The merge's written counts are shares of at most 2⁻¹ ^ 128.** -/
theorem merge_written (G : WeightsL GE) (Ex : ExtSpec) {dZ d0 : RDT} {ds : List RDT} {dY dV : RDT}
    (hk : ds.length = G.k) (HD : MergeDs dZ d0 ds dY dV) (H : MergeWr dZ d0 ds dY)
    (hn : G.n - 1 ≤ 2 ^ 62) :
    Err.Below ((mergeMaps G Ex dZ d0 ds dY dV hk).err (G.eps (Kc := Unit) (G.L.V1 Ex)))
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  Maps.below_pow _ (mergeMaps_ok G Ex hk HD) _ (merge_heldN G Ex hk H hn)

/-- **The row, as one closed proposition.** -/
def K11Written : Prop :=
  ∀ (G : WeightsL GE) (Ex : ExtSpec) (dZ d0 : RDT) (ds : List RDT) (dY dV : RDT)
    (hk : ds.length = G.k), MergeDs dZ d0 ds dY dV → MergeWr dZ d0 ds dY → G.n - 1 ≤ 2 ^ 62 →
    Err.Below ((mergeMaps G Ex dZ d0 ds dY dV hk).err (G.eps (Kc := Unit) (G.L.V1 Ex)))
      ((2 : ℝ≥0∞)⁻¹ ^ 128)

theorem k11Written : K11Written := fun G Ex _ _ _ _ _ hk HD H hn => merge_written G Ex hk HD H hn

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.heldN_of_list
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_heldN
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_written
#print axioms VerifiableInference.Desc.First.MergeLaw.k11Written
