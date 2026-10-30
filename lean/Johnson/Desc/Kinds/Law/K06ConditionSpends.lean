-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06ConditionSpends.lean: Law/K06Condition.lean's STRUCTURE K06Cond IS SPENT: from it the premises on public numbers of the laws on the output head, UNDER THE LAWS' OWN NAMES, and where
a law's whole premise is paid, its conclusion. So that the condition is no list beside the laws.
WHAT IT DOES NOT SHOW. Nothing of soundness. THAT THESE ARE ALL THE LAWS' PREMISES ON PUBLIC NUMBERS. The laws' other premises (the request, the token, the record, the transcript, the cells, the public table) stay theirs.
  spends_row       K06_law's two (Law/RowRides.lean): (parOf h work).ok = true · hasFeatures (parOf h work).
  spends_stream    StreamFits h b (Law/ReadsFitNorm.lean).      spends_origin  that file's stream_at_zero's conclusion: limb l of the stream lies at feature l d.
  spends_reads     numbers h returns some L, and at it: readLen_fits' · readLenN_fits' · wideLenN_fits' CONCLUSIONS (Law/ReadsFit.lean · ReadsFitNorm.lean).
  spends_below     Law/K06Below.lean's k06Below's CONCLUSION at the kind's own lt, lPd and the setting's work.
  spends_record    the record of which Law/HeadPrices.lean speaks (recOf) is the one with the planner's fields h.lt, h.lPd.
  SO THAT «once» AND «reads» ARE NO FIELDS ON BARE LETTERS AND admitted IS SPENT:
  K06CondAt W      the structure AT THE PLAN's OWN READERS: W.hS · borderOf W.y · the setting's work and instances · the plan's array of reads: no letter is free but the public record W.
  spends_block     reads: Head.blockOf W l IS some block: K06_law speaks of a block.      spends_rides  K06_law's two premises in Law/RowRides.lean's own letters (workOf W).
  spends_once      once: Law/K06RoundsAtPlan.lean's bounds_priced's CONCLUSION at the record's own setting: the bounds that the planner's close prices are the pairs' quotients.
  spends_own       limbs and pad: at every plan P of the head the planner's own record gives the entries of the kind's declared rounds (own_is; k6_entries).
  admitted_pays    admitted ALONE gives features, point, rows, index's second half and blocks: so these five fields are the program's own tests' consequences.
  spends_point     Law/K06Rounds.lean's 0 < lt.      spends_lookup  K06OutAtLookupStatement's two.      spends_norm  the normalization's laws' two.

-/
import Johnson.Desc.Kinds.Law.K06Condition
import Johnson.Desc.Kinds.Law.RowRides
import Johnson.Desc.Kinds.Law.K06Below
import Johnson.Desc.Kinds.Law.ReadsFitNorm
import Johnson.Desc.Kinds.Law.K06RoundsAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.Cond

open OnBytes.Model.Head (Shape Border HL)
open Norm (lt ls d lPd S2)
open Johnson.Bridge (KindFits)
open OnBytes.Slice (RoundBelow)
open _root_.Run (PQ.RD)
open scoped ENNReal

variable {h : Shape} {b : Border} {work inst : Nat} {reads : Option Nat}

theorem spends_row (C : K06Cond h b work inst reads) :
    (parOf h work).ok = true ∧ hasFeatures (parOf h work) := ⟨C.ok, C.features⟩

theorem spends_stream (C : K06Cond h b work inst reads) : StreamFits h b := C.stream

theorem spends_origin (C : K06Cond h b work inst reads) (l : Nat) : b.cell l 0 = l * h.d :=
  stream_at_zero b h.d C.origin.1 C.origin.2 l

theorem spends_reads (C : K06Cond h b work inst reads) :
    ∃ L : HL, OnBytes.Model.Head.numbers h = .ok L ∧
      (∀ r : Read, @readLen (sizesOf h) r ≤ widthOf h L r) ∧
      (∀ r : FinalNorm.Read, @readLenN (sizesOf h) r ≤ widthOfN h L b r) ∧
      @wideLenN (sizesOf h) ≤ widthOf h L .wideAtKeys := by
  cases hL : OnBytes.Model.Head.numbers h with
  | error e =>
    have hn := C.numbers
    rw [hL] at hn
    cases hn
  | ok L =>
    exact ⟨L, rfl, readLen_fits h L hL C.rows C.limbs,
      readLenN_fits h L b hL C.rows C.limbs C.stream, wideLenN_fits h L hL C.rows C.limbs⟩

theorem spends_below (C : K06Cond h b work inst reads) :
    letI := sizesOf h
    ∀ p ∈ Below.k6Priced lt lPd work, ∀ r : PQ.RD, r.entry = p.1 → KindFits false r.kind →
      RoundBelow p.2 r ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  letI := sizesOf h
  Below.k06Below lt lPd work C.point
    (le_trans (le_trans (Nat.le_add_right _ _) C.index.1) (by norm_num)) C.work

theorem spends_record (C : K06Cond h b work inst reads) :
    letI := sizesOf h
    Prices.recOf = Prices.recAt h.lt h.lPd := by
  rw [C.pad]
  rfl

theorem spends_point (C : K06Cond h b work inst reads) : letI := sizesOf h; 0 < lt := C.point

theorem spends_lookup (C : K06Cond h b work inst reads) :
    letI := sizesOf h
    (∀ k : PlaceKey, lenOf k < 2 ^ 41) ∧ S2 ∣ JVa := ⟨C.keys, C.table⟩

theorem spends_norm (C : K06Cond h b work inst reads) :
    letI := sizesOf h
    S2 ∣ d ∧ ls ≤ lPd := ⟨C.blocks, C.block⟩

/-! ## At the plan's own readers -/

/-- **The structure at a public record**: every letter read off W by the program's own readers. -/
def K06CondAt (W : OnBytes.Model.Verify.Public) : Prop :=
  K06Cond W.hS (OnBytes.Model.Verify.borderOf W.y)
    ((OnBytes.Params.settingOf W.P.frame).workOf .field .request)
    (OnBytes.Params.settingOf W.P.frame).instances (W.H.tl.ix.U.getD 2 none)

/-- reads: there is a block. -/
theorem spends_block {W : OnBytes.Model.Verify.Public} (C : K06CondAt W) (l : Nat) :
    ∃ blk, blockOf W l = some blk := by
  have hr := C.reads
  unfold blockOf
  cases hU : W.H.tl.ix.U.getD 2 none with
  | none =>
    rw [hU] at hr
    cases hr
  | some i => exact ⟨_, rfl⟩

/-- K06_law's two premises on public numbers, in its own letters. -/
theorem spends_rides {W : OnBytes.Model.Verify.Public} (C : K06CondAt W) :
    (parOf W.hS (workOf W)).ok = true ∧ hasFeatures (parOf W.hS (workOf W)) := ⟨C.ok, C.features⟩

/-- once: the priced bounds of the head's own rounds, at the record's own setting. -/
theorem spends_once {W : OnBytes.Model.Verify.Public} (C : K06CondAt W) :
    (OnBytes.Params.headOwnList (OnBytes.Params.settingOf W.P.frame) (Prices.recAt W.hS.lt W.hS.lPd)).map
        (fun r => r.bound (OnBytes.Params.settingOf W.P.frame) .request) =
      (Prices.headRatios (OnBytes.Params.settingOf W.P.frame).cardE (Prices.recAt W.hS.lt W.hS.lPd)).map
        fun o => (OnBytes.Tie.Pv.Lay.boundOf o).getD (OnBytes.Params.Bound.ofWord 0) :=
  bounds_priced _ (le_of_eq C.once) _ (by simp [Prices.recAt])

/-- limbs and pad: the planner's own record gives the entries of the kind's declared rounds. -/
theorem spends_own (C : K06Cond h b work inst reads) (P : OnBytes.Model.Head.HPlanH2) (w : Nat) :
    letI := sizesOf h
    rounds.map (Round.entry w) = OnBytes.Tie.Pv.Head.headOwnList w (P.own h) := by
  letI := sizesOf h
  rw [own_is P h C.limbs w, Prices.k6_entries w C.point, spends_record C]

/-- The program's own tests on the shape give five of the fields. -/
theorem admitted_pays (h : Shape) (ha : OnBytes.Model.Head.admitted h = true) :
    0 < h.d ∧ 0 < h.lt ∧ h.lt ≤ h.la ∧ h.la ≤ 63 ∧ h.d % h.S2 = 0 := by
  simp only [OnBytes.Model.Head.admitted, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ha
  omega

end VerifiableInference.Desc.Kinds.Head.Law.Cond

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Cond.spends_row
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Cond.spends_reads
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Cond.spends_below
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Cond.spends_record
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Cond.spends_block
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Cond.spends_rides
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Cond.spends_once
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Cond.spends_own
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Cond.admitted_pays
