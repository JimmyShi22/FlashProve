-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/RecRows.lean: what the linear claim's shared rounds (the shared chain) read
of the committed table's key, paid by the key of the out-of-domain (OOD) sample (`oodAt`, `oodSh`,
Johnson/Bind/ForProver/Ood.lean): row by row, and at the rows' fold under any coefficients.

Why. The place "(rec_gamma)" of the shared rounds lays, for each seed of the key, one constraint on
the folded row (`recGamma`, Johnson/Desc/K14/Text.lean). What that constraint says of words is
`Desc.K14.Law.RecEq` (Johnson/Desc/K14/Law/LawRL.lean): the folded row's own sample at the seed is
the fold of the rows' answers. An honest side owes that equation. It follows from one fact on each
row: the row's answer in the key is that sample at the row's own message.

Main names (namespace `Bind.ForProver`).
  `toE_eqAt`   the stand-in committer's equality kernel (`Bind.Twin.eqAt`, Johnson/Bind/Twin.lean),
    read in the extension field, is the law's `eqK` at the point's coordinates as read.
  `mul_toE_pads`   a factor times three pads, read, is the sum over 1, X, X^2.
  `msgK sh entry ρ r j`   entry j of row r's message, in the extension field: the cast of `rowMsgF`
    (Johnson/Bind/ForProver/Rows.lean). `msgK_pad`: what it is at a pad of an answer.
  **`ans_at`**   the answer of row r under seed number i, as the key holds it and as it is read, is
    the left side of `RecEq` at row r's message: at every list of sh.s seeds, whatever its words.
  **`recEq_fold`**   so `RecEq` holds at the key's answers and the rows' fold under any
    coefficients.
  `ans_oodSh`, **`recEq_oodSh`**   the two at `oodSh sh Z k`: no premise on the seeds.
  **`ownAnswers_oodSh`**   the first at every seed of the key with its number and every row.
  `factorsOwn_oodSh`   no factor is 0, in the description's own spelling: with `keyFits_oodSh_of`
    the first two of the three tests in front of "(rec_gamma)" (`laysRecL`).

Limits. Asked: a message has room for its pads (3 s ≤ l). Nothing here says that the state's key in
a run is `oodSh` at these readers, that the words of the folded row's message are the rows' fold, or
that the coefficients are those of the folding point: these are the run's matter. The third test in
front of "(rec_gamma)" reads no key. Nothing here says that the seeds are those of the table's name.
(The library calls a fold's coefficients `weights`; they are not
the model's.) `msgK` has no code (the cast into the extension field): it stands in statements alone.
`recEq_oodSh` stands at `indexOf sh`; the rows' law at the public part's own index shape, at the
honest side's rows, where `rowsFit` passes: `ownAnswers_rowsOf`
(Johnson/Bind/ForProver/RecRowsK14.lean). The forms at the index type `Cm.Idx`:
Johnson/Bind/ForProver/RecRowsAtIndex.lean. An equation in a field: no completeness, no soundness,
no correctness of extraction, no binding of the commitment (the opening form, `BindsWith`,
VerifiableInference/MoreStatements.lean), no index privacy; nothing on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.OodPlaces
import Johnson.Desc.K14.Law.LawRL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.ForProver
open OnBytes (E SampleSeed TableKey zeroE thetaE)
open OnBytes.Slice (toF toE ofF readE)
open OnBytes.Model (Reading)
open Desc.K14.Law (eqK RecEq)
open ProofFile.Honest (TableRand Weights Isk)

/-- **The committer's equality kernel, read, is the law's.** -/
theorem toE_eqAt : ∀ (z : List Fmt.Ext) (k : ℕ),
    toE (Bind.Twin.eqAt z k) = eqK (z.map toE) k
  | [], _ => OnBytes.Slice.toE_oneE
  | x :: zs, k => by
    show toE (Fmt.Fld.two.mulE (if k % 2 = 1 then x else Fmt.Fld.two.subE Fmt.Fld.oneE x)
      (Bind.Twin.eqAt zs (k / 2))) =
        (if k % 2 = 1 then toE x else 1 - toE x) * eqK (zs.map toE) (k / 2)
    rw [OnBytes.Slice.toE_mulE, toE_eqAt zs (k / 2)]
    by_cases h : k % 2 = 1
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h, OnBytes.Slice.toE_subE, OnBytes.Slice.toE_oneE]

/-- A factor times three pads, read, is the sum over 1, X, X^2. -/
theorem mul_toE_pads (β : Cb.Gl.E) (a b c : UInt64) :
    β * toE (a, b, c) =
      β * readE (thetaE 0) * algebraMap Cb.Gl.F Cb.Gl.E (toF a) +
        β * readE (thetaE 1) * algebraMap Cb.Gl.F Cb.Gl.E (toF b) +
          β * readE (thetaE 2) * algebraMap Cb.Gl.F Cb.Gl.E (toF c) := by
  apply Code.Cubic.ext <;> simp [OnBytes.Slice.readE_theta, toE] <;> ring

/-- Entry j of row r's message, in the extension field. -/
noncomputable def msgK (sh : Bind.Twin.Shape) (entry : ℕ → ℕ → UInt64) (ρ : TableRand)
    (r j : ℕ) : Cb.Gl.E :=
  algebraMap Cb.Gl.F Cb.Gl.E (rowMsgF sh entry ρ r j)

/-- A row's message at a pad of an answer. -/
theorem msgK_pad (sh : Bind.Twin.Shape) (entry : ℕ → ℕ → UInt64) (ρ : TableRand)
    (h3 : 3 * sh.s ≤ sh.l) (r i t : ℕ) (hi : i < sh.s) (ht : t < 3) :
    msgK sh entry ρ r ((indexOf sh).padPlace i t) =
      algebraMap Cb.Gl.F Cb.Gl.E (toF ((tableOfRand entry ρ).pad r (3 * i + t))) := by
  show algebraMap Cb.Gl.F Cb.Gl.E (rowMsgF sh entry ρ r (sh.l - 3 * sh.s + 3 * i + t)) =
    algebraMap Cb.Gl.F Cb.Gl.E (toF (ofF (ρ.pad r (3 * i + t))))
  rw [OnBytes.Slice.toF_ofF]
  unfold rowMsgF Bind.Twin.Shape.plain
  rw [if_neg (by omega), if_pos (by omega)]
  have e : sh.l - 3 * sh.s + 3 * i + t - (sh.l - 3 * sh.s) = 3 * i + t := by omega
  rw [e]

/-- **The answer of row r under seed number i, read, is the sample at row r's own message.** -/
theorem ans_at (sh : Bind.Twin.Shape) (entry : ℕ → ℕ → UInt64) (ρ : TableRand)
    (sd : List SampleSeed) (h : sd.length = sh.s) (h3 : 3 * sh.s ≤ sh.l) (r i : ℕ)
    (hr : r < 2 ^ sh.v) (y : SampleSeed) (hy : sd[i]? = some y) :
    Reading.gl.val ((oodAt sh entry ρ sd).record.getD (r * sh.s + i) zeroE) =
      (∑ k ∈ Finset.range (indexOf sh).plain,
          eqK (y.z.map Reading.gl.val) k * msgK sh entry ρ r k) +
        ∑ t ∈ Finset.range 3, Reading.gl.val y.beta * Reading.gl.val (thetaE t) *
          msgK sh entry ρ r ((indexOf sh).padPlace i t) := by
  have hi : i < sh.s := by
    obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.1 hy
    rw [← h]
    exact hi
  have hg : (oodAt sh entry ρ sd).record.getD (r * sh.s + i) zeroE =
      E.ofTriple (Bind.Twin.answerAt sh (tableOfRand entry ρ) r i
        (Bind.Twin.eqTable (y.z.map E.triple) sh.plain) y.beta.triple) := by
    rw [Array.getD_eq_getD_getElem?]
    show ((keyAt sh (tableOfRand entry ρ) sd).record[r * sh.s + i]?).getD zeroE = _
    rw [record_place sh (tableOfRand entry ρ) sd h r i hr y hy]
    rfl
  rw [hg]
  show toE (E.ofTriple (Bind.Twin.answerAt sh (tableOfRand entry ρ) r i
    (Bind.Twin.eqTable (y.z.map E.triple) sh.plain) y.beta.triple)).triple = _
  rw [E.triple_ofTriple, Bind.Twin.toE_answerAt]
  congr 1
  · show ∑ k ∈ Finset.range sh.plain, _ = ∑ k ∈ Finset.range sh.plain, _
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [toE_eqAt, List.map_map, Algebra.smul_def, mul_comm]
    unfold msgK rowMsgF
    rw [if_pos (Finset.mem_range.1 hk)]
    rfl
  · rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, msgK_pad sh entry ρ h3 r i 0 hi (by omega),
      msgK_pad sh entry ρ h3 r i 1 hi (by omega), msgK_pad sh entry ρ h3 r i 2 hi (by omega)]
    exact mul_toE_pads _ _ _ _

/-- **(rec_gamma)'s equation, at the key's answers and the rows' fold under any coefficients.** -/
theorem recEq_fold (sh : Bind.Twin.Shape) (entry : ℕ → ℕ → UInt64) (ρ : TableRand)
    (sd : List SampleSeed) (h : sd.length = sh.s) (h3 : 3 * sh.s ≤ sh.l) (i : ℕ)
    (y : SampleSeed) (hy : sd[i]? = some y) (w : ℕ → Cb.Gl.E) :
    RecEq (indexOf sh) (y.z.map Reading.gl.val) (Reading.gl.val y.beta)
      (fun t => Reading.gl.val (thetaE t)) i w
      (fun k => Reading.gl.val ((oodAt sh entry ρ sd).record.getD k zeroE))
      (fun k => ∑ r ∈ Finset.range (2 ^ sh.v), w r * msgK sh entry ρ r k) := by
  have hR : ∑ r ∈ Finset.range (2 ^ sh.v),
        w r * Reading.gl.val ((oodAt sh entry ρ sd).record.getD (r * sh.s + i) zeroE) =
      ∑ r ∈ Finset.range (2 ^ sh.v), w r *
        ((∑ k ∈ Finset.range (indexOf sh).plain,
            eqK (y.z.map Reading.gl.val) k * msgK sh entry ρ r k) +
          ∑ t ∈ Finset.range 3, Reading.gl.val y.beta * Reading.gl.val (thetaE t) *
            msgK sh entry ρ r ((indexOf sh).padPlace i t)) :=
    Finset.sum_congr rfl fun r hr => by
      rw [ans_at sh entry ρ sd h h3 r i (Finset.mem_range.1 hr) y hy]
  show (∑ k ∈ Finset.range (indexOf sh).plain, eqK (y.z.map Reading.gl.val) k *
        ∑ r ∈ Finset.range (2 ^ sh.v), w r * msgK sh entry ρ r k) +
      ∑ t ∈ Finset.range 3, Reading.gl.val y.beta * Reading.gl.val (thetaE t) *
        ∑ r ∈ Finset.range (2 ^ sh.v), w r * msgK sh entry ρ r ((indexOf sh).padPlace i t) =
    ∑ r ∈ Finset.range (2 ^ sh.v),
      w r * Reading.gl.val ((oodAt sh entry ρ sd).record.getD (r * sh.s + i) zeroE)
  rw [hR]
  simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun k _ => by ring
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => by ring

section
variable (sh : Bind.Twin.Shape) (Z : ProofFile.Pub) (k : Isk Weights (ℕ → TableRand) (Seed sh × ℕ))

/-- The answer of a row under a seed, at `oodSh`. -/
theorem ans_oodSh (h3 : 3 * sh.s ≤ sh.l) (r i : ℕ) (hr : r < 2 ^ sh.v) (y : SampleSeed)
    (hy : (spell sh k.seed.1)[i]? = some y) :
    Reading.gl.val ((oodSh sh Z k).record.getD (r * sh.s + i) zeroE) =
      (∑ j ∈ Finset.range (indexOf sh).plain, eqK (y.z.map Reading.gl.val) j *
          msgK sh (entryOfPub Z k.index) (k.coins 0) r j) +
        ∑ t ∈ Finset.range 3, Reading.gl.val y.beta * Reading.gl.val (thetaE t) *
          msgK sh (entryOfPub Z k.index) (k.coins 0) r ((indexOf sh).padPlace i t) :=
  ans_at sh _ _ _ (fits_spell _ _).1 h3 r i hr y hy

/-- **(rec_gamma)'s equation at `oodSh`**, under any coefficients. -/
theorem recEq_oodSh (h3 : 3 * sh.s ≤ sh.l) (i : ℕ) (y : SampleSeed)
    (hy : (oodSh sh Z k).seeds[i]? = some y) (w : ℕ → Cb.Gl.E) :
    RecEq (indexOf sh) (y.z.map Reading.gl.val) (Reading.gl.val y.beta)
      (fun t => Reading.gl.val (thetaE t)) i w
      (fun j => Reading.gl.val ((oodSh sh Z k).record.getD j zeroE))
      (fun j => ∑ r ∈ Finset.range (2 ^ sh.v),
        w r * msgK sh (entryOfPub Z k.index) (k.coins 0) r j) :=
  recEq_fold sh _ _ _ (fits_spell _ _).1 h3 i y hy w

/-- **Every answer of the key, seed by seed and row by row**: in the order in which the place
"(rec_gamma)" walks the key's seeds. -/
theorem ownAnswers_oodSh (h3 : 3 * sh.s ≤ sh.l) :
    ∀ x ∈ (oodSh sh Z k).seeds.zipIdx, ∀ r < (indexOf sh).rows,
      (∑ j ∈ Finset.range (indexOf sh).plain, eqK (x.1.z.map Reading.gl.val) j *
          msgK sh (entryOfPub Z k.index) (k.coins 0) r j) +
        ∑ t ∈ Finset.range 3, Reading.gl.val x.1.beta * Reading.gl.val (thetaE t) *
          msgK sh (entryOfPub Z k.index) (k.coins 0) r ((indexOf sh).padPlace x.2 t) =
      Reading.gl.val ((oodSh sh Z k).record.getD (r * (indexOf sh).answers + x.2) zeroE) :=
  fun x hx r hr =>
    (ans_oodSh sh Z k h3 r x.2 hr x.1 (List.mem_zipIdx_iff_getElem?.1 hx)).symm

/-- No factor is 0, in the description's own spelling. -/
theorem factorsOwn_oodSh :
    ((oodSh sh Z k).seeds.all (!VerifiableInference.Desc.Own.allZero ·.beta)) = true :=
  factors_keyAt _ _ _ (fits_spell _ _)

end

end Bind.ForProver

#print axioms Bind.ForProver.toE_eqAt
#print axioms Bind.ForProver.mul_toE_pads
#print axioms Bind.ForProver.msgK_pad
#print axioms Bind.ForProver.ans_at
#print axioms Bind.ForProver.recEq_fold
#print axioms Bind.ForProver.ans_oodSh
#print axioms Bind.ForProver.recEq_oodSh
#print axioms Bind.ForProver.ownAnswers_oodSh
#print axioms Bind.ForProver.factorsOwn_oodSh
#print axioms Bind.ForProver.msgK
