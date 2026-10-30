-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/K14PointCap.lean: the joint at the shared chain's block 1, "LIN point", for a
batch of up to 64 requests: the two lists of errors at which the law of that block is stated, the
key's part once and a slot's part N times, lie beneath the cap of the written round, at the
release's numbers.

The law of the block (point_leadsB_at_place, Johnson/Desc/Sound/PointAtPlace.lean) ends at the plain
form for a batch in two parts (Johnson/Desc/Plain/Both.lean: LeadsB key on Q εK εO) with
  εK := (vecMaps d kCol).err (ef q ^ kLo, ()) ef: the right side of the statement on codes' count
  εO := (vecMaps d kCol).err (kCol q ^ (kCol - 1), ())
and the form at one list of errors is LeadsBN key on Q N ε := there are εK, εO with Err.le (Err.add
εK (Err.times N εO)) ε and LeadsB at them. Where a piece's errors are the cap (Iop/ErrCap.lean:
Err.cap 128), the joint is that one inequality of lists.
  err_add_times: the sum of the two written lists is the written list of the sum of the counts
  point_cap64: the inequality, at ef := efReal, for every N ≤ 64, at every written round with the
      entry and kind of the written list's round 0
  efForm_eq: at a shape with the release's index and the radius 2852142980 the right side of the
      statement on codes' count (Johnson/Bridge/FoldErrIx.lean: foldErr_ix), written at the index's
      own numbers, is efReal
  leadsBN_at_cap: so from LeadsB at these two lists: LeadsBN at the cap, for every N ≤ 64
  PointCap S Wr, point_cap_real, point_cap_key: in a proof file, in a key file

What is not claimed. THE LAW ITSELF: LeadsB is a premise of leadsBN_at_cap; that law's
theorem is called nowhere here (Johnson/Desc/Sound/PointAtCap.lean calls leadsBN_at_cap at it); no
member of that law's premises together is shown. That 64 is the plan's number of requests. It rests,
through efReal, on the files under ThirdParty/ (lean/LIMITS.md, L15). What the head of
Johnson/Goal/Numbers/K14JointAt.lean does not claim. Nothing on soundness of a verifier, on an
honest prover or on hiding.

-/
import Johnson.Goal.Numbers.K14JointAt
import Johnson.Desc.Plain.Both
import Iop.ErrCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Params.Prices OnBytes.Plan Johnson.G
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice Cb
open VerifiableInference.Desc.K1 (realSized)
open Lk6.AtPlan (keyFull)
open scoped ENNReal

/-- The brick: from a yes of the comparison to Err.Below of the written list. (Another file of this
folder has the same under the name vec_brick; it is typed here once more so that this file stands on
Johnson/Goal/Numbers/K14JointAt.lean alone.) -/
private theorem vecBrick (d : RDT) (n e : ℕ) {ns a : ℕ} (hd : SendsDraws (toRD d) ns n 0 a)
    (h : roundB d.entry d.kind e 128 = true) :
    Err.Below ((vecMaps d n).err ((e, ()) : ℕ × Unit)) ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  unfold roundB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact Maps.below_pow (vecMaps d n) (vecMaps_ok hd) ((e, ()) : ℕ × Unit)
    ⟨⟨e, nVals (Fmt.dsOf d.entry d.kind), h.1, Nat.le_refl _, h.2⟩, trivial⟩

/-- The sum of the two written lists is the written list of the sum. -/
theorem err_add_times (d : RDT) (n a b N : ℕ) :
    Err.add ((vecMaps d n).err ((a, ()) : ℕ × Unit))
        (Err.times N ((vecMaps d n).err ((b, ()) : ℕ × Unit))) =
      (vecMaps d n).err ((a + N * b, ()) : ℕ × Unit) := by
  refine Prod.ext ?_ rfl
  show a * (bsRound .two d.entry d.kind).w + N * (b * (bsRound .two d.entry d.kind).w) =
    (a + N * b) * (bsRound .two d.entry d.kind).w
  ring

/-- **The key's part once and a slot's part N times lie beneath the cap.** -/
theorem point_cap64 {S : LinShape} {Wr : Rounds} {rad work : ℕ}
    (h : K14Rounds S Wr rad cMax work) (ht : pointNB S Wr cMax64 64 = true) (d : RDT)
    (hd : atW Wr 0 = some (d.entry, d.kind)) (N : ℕ) (hN : N ≤ 64) :
    Err.le (Err.add ((vecMaps d S.kCol).err ((efReal * Fintype.card GE ^ S.kLo, ()) : ℕ × Unit))
        (Err.times N ((vecMaps d S.kCol).err
          ((S.kCol * Fintype.card GE ^ (S.kCol - 1), ()) : ℕ × Unit))))
      (Err.cap 128 (uLT (ckP .two) [d])) := by
  rw [err_add_times]
  refine Err.le_cap_of_below_inv 128 _ ?_
  unfold pointNB at ht
  rw [hd, Option.any_some] at ht
  refine vecBrick d _ _ (h.point d hd).1 (roundB_mono ?_ ht)
  have h64 := efReal_le64
  rw [card_GE_num] at h64 ⊢
  exact count_mono efReal cMax64 cardGl S.kLo _ N h64 hN

/-- **The statement on codes' count, written at the index's own numbers, is efReal.** -/
theorem efForm_eq {S : LinShape} (h : indexB S = true) :
    S.fold.index.v *
        ⌊bchksBound (2 ^ (codeOf S.fold.index.code).a)
          ((codeOf S.fold.index.code).r + (codeOf S.fold.index.code).l - 1) 2852142980⌋₊ *
        Fintype.card GE ^ (S.fold.index.v - 1) +
      listMax (2 ^ (codeOf S.fold.index.code).a)
          (2 ^ (codeOf S.fold.index.code).a -
            ((codeOf S.fold.index.code).r + (codeOf S.fold.index.code).l) + 1) 2852142980 *
        (S.fold.index.v * Fintype.card GE ^ (S.fold.index.v - 1)) = efReal := by
  obtain ⟨i1, i2, i3⟩ := indexB_sound h
  have e1 : (codeOf S.fold.index.code).r + (codeOf S.fold.index.code).l - 1 = 446693374 := by
    rw [i2]
  have e2 : 2 ^ (codeOf S.fold.index.code).a -
      ((codeOf S.fold.index.code).r + (codeOf S.fold.index.code).l) + 1 = 3848273922 := by
    rw [i2, i1]
    decide +kernel
  unfold efReal
  exact count_eq (codeOf S.fold.index.code) i1 S.fold.index.v (Fintype.card GE) i3 e1 e2

/-- What is had of a shape and a written list. -/
def PointCap (S : LinShape) (Wr : Rounds) : Prop :=
  indexB S = true ∧ ∀ (d : RDT), atW Wr 0 = some (d.entry, d.kind) → ∀ N ≤ 64,
    Err.le (Err.add ((vecMaps d S.kCol).err ((efReal * Fintype.card GE ^ S.kLo, ()) : ℕ × Unit))
        (Err.times N ((vecMaps d S.kCol).err
          ((S.kCol * Fintype.card GE ^ (S.kCol - 1), ()) : ℕ × Unit))))
      (Err.cap 128 (uLT (ckP .two) [d]))

/-- **From the law in two parts to the law at the cap**, for up to 64 slots. K: any reduction over
the one written round. -/
theorem leadsBN_at_cap {S : LinShape} {Wr : Rounds} (h : PointCap S Wr) (d : RDT)
    (hd : atW Wr 0 = some (d.entry, d.kind)) {A B κ : Type} (K : Reduction A B)
    (hs : K.shape = uLT (ckP .two) [d]) (key : A → κ) (on : A → Prop) (Q : A → B → Prop)
    (hL : K.LeadsB key on Q
      (hs ▸ (vecMaps d S.kCol).err ((efReal * Fintype.card GE ^ S.kLo, ()) : ℕ × Unit))
      (hs ▸ (vecMaps d S.kCol).err ((S.kCol * Fintype.card GE ^ (S.kCol - 1), ()) : ℕ × Unit)))
    (N : ℕ) (hN : N ≤ 64) : K.LeadsBN key on Q N (Err.cap 128 K.shape) := by
  obtain ⟨sh, out⟩ := K
  dsimp only at hs
  subst hs
  exact ⟨_, _, h.2 d hd N hN, hL⟩

theorem pointCap_of {S : LinShape} {Wr : Rounds} {rad work : ℕ} (hi : indexB S = true)
    (h : K14Rounds S Wr rad cMax work) (ht : pointNB S Wr cMax64 64 = true) : PointCap S Wr :=
  ⟨hi, fun d hd N hN => point_cap64 h ht d hd N hN⟩

/-- **In a proof file.** -/
theorem point_cap_real : ∃ x : LinSized, realSized = some (x, codesFull2) ∧ AtRecord x ∧
    PointCap x.shape dryProofFull.2.1 := by
  obtain ⟨x, a1, a2, -, a4⟩ := k14_rounds_real
  have h := real_test64
  have hi := index_real
  rw [a1, Option.any_some] at h hi
  exact ⟨x, a1, a2, pointCap_of hi a4 h⟩

/-- **In a key file.** -/
theorem point_cap_key : PointCap keyFull.once.shape dryKeyFull.2.1 :=
  pointCap_of index_key k14_rounds_key key_test64

end Desc.K14.Law
