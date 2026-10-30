-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/K14JointAt.lean: two joints at the round LIN point, at the release's numbers.

(1) The bound efReal of Johnson/Goal/Numbers/K14BadAt.lean on the bad fold points lies beneath the
number that Johnson/Bridge/PlanPoints.lean makes off the planner's record of the table and the
radius (PointPlace.top, at the place of the full-size table, the radius 2852142980, seven column
variables and 64 requests): so whatever is shown of that place's top holds of efReal. (2) The
round's written errors are shares of at most 2^-128 also at the count with the second term taken
once for each of up to 64 requests: efReal q ^ kLo + N (kCol q ^ (kCol - 1)), N ≤ 64: the form of
the library's own error of the point for a batch (LdLinP.errPtB). The law of the eight blocks
(row1to8_decoded) can be called at that count too: it asks e1 to be at least the count at N = 1.
  recordPlace: the place
  place_good: its test says yes: an evaluation in Lean's kernel (decide +kernel)
  top_eq: its top, written out: 11 B q ^ 10 + 26 (11 q ^ 10), B the bracket's bound
  efOf_le_of: at letters
  efReal_le_top: efReal ≤ recordPlace.top
  cMax64: 18446744060824648581 = cMax - 63 · 18: the largest whole number c at which the comparison
      holds with c q ^ 10 q ^ 7 + 64 (18 q ^ 17)
  pointNB, real_test64, key_test64: the comparison at cMax64 and 64: evaluations in Lean's kernel
  point_paid64: Err.Below at 2^-128 of the piece that bears efReal q ^ kLo + N (kCol q ^ (kCol -
      1)), for every N ≤ 64, at every written round with the entry and kind of the written round 0
  k14_point64_real, k14_point64_key: in a proof file, in a key file
  teeth64: at cMax64 + 1 the comparison says no, in both files

What is not claimed. WHICH count a batch of 64 requests is owed: that a round shared by a batch is
charged once, with the second term once for each request, is another row's matter; the whole count
taken 64 times does NOT pass the comparison. That 64 is the plan's number of requests. It rests,
through foldErr_ix, on the files under ThirdParty/ (lean/LIMITS.md, L15). What the heads of
Johnson/Goal/Numbers/K14RoundsAt.lean and Johnson/Goal/Numbers/K14BadAt.lean do not claim. Nothing
on soundness, on an honest prover or on hiding.

-/
import Johnson.Goal.Numbers.K14BadAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Params.Prices OnBytes.Plan Johnson.G
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice Cb
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.K1 (realSized)
open Lk6.AtPlan (keyFull)
open Cb.Gl.Ref (cntIx)
open Johnson.Bridge (PointPlace Br)
open scoped ENNReal

/-! ## (1) efReal against the place's top -/

/-- The place of the full-size table. -/
def recordPlace : PointPlace := ⟨recordTable, recordRadius, 7, 64⟩

theorem place_good : recordPlace.good = true := by decide +kernel

/-- The place's top, written out. -/
theorem top_eq : recordPlace.top =
    11 * recordPlace.br.N * (Cb.Gl.p ^ 3) ^ 10 + 26 * (11 * (Cb.Gl.p ^ 3) ^ 10) := by
  have e1 : recordPlace.T.v = 11 := by decide +kernel
  have e2 : listMax recordPlace.n (recordPlace.n - recordPlace.k) recordPlace.e = 26 := by
    decide +kernel
  unfold PointPlace.top
  rw [e1, e2]

/-- At letters. -/
theorem efOf_le_of (c B q : Nat) (h : c ≤ B) :
    efOf c q ≤ 11 * B * q ^ 10 + 26 * (11 * q ^ 10) := by
  unfold efOf
  have h1 : (11 * c + 286) * q ^ 10 = 11 * c * q ^ 10 + 26 * (11 * q ^ 10) := by ring
  rw [h1]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 11 h)) _

theorem cntIx_le_br : cntIx ≤ recordPlace.br.N := by
  have hg := place_good
  unfold PointPlace.good at hg
  rw [Bool.and_eq_true] at hg
  have h := Br.le hg.2
  have e1 : recordPlace.n = 2 ^ 32 := by decide +kernel
  have e2 : recordPlace.k = 446693374 := by decide +kernel
  have e3 : recordPlace.e = 2852142980 := rfl
  rw [e1, e2, e3] at h
  exact h

/-- **efReal lies beneath the place's top.** -/
theorem efReal_le_top : efReal ≤ recordPlace.top := by
  rw [top_eq]
  unfold efReal
  rw [Cb.Gl.gl_card.2.1]
  exact efOf_le_of cntIx recordPlace.br.N (Cb.Gl.p ^ 3) cntIx_le_br

/-! ## (2) Up to 64 requests -/

/-- The largest whole number c at which the comparison holds with 64 times the second term. -/
def cMax64 : Nat := 18446744060824648581

theorem efOf_le64 (c q : Nat) (h : c ≤ 1152921503801540608) : efOf c q ≤ cMax64 * q ^ 10 :=
  Nat.mul_le_mul_right _
    (Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left 11 h) 286) (by decide +kernel))

theorem efReal_le64 : efReal ≤ cMax64 * Fintype.card GE ^ 10 := by
  unfold efReal
  exact efOf_le64 cntIx (Fintype.card GE) cntIx_le

/-- The comparison at the written round 0, at c q ^ 10 q ^ kLo + N (kCol q ^ (kCol - 1)). -/
def pointNB (S : LinShape) (Wr : Rounds) (c N : Nat) : Bool :=
  (atW Wr 0).any fun x =>
    roundB x.1 x.2 (c * cardGl ^ 10 * cardGl ^ S.kLo + N * (S.kCol * cardGl ^ (S.kCol - 1))) 128

theorem real_test64 : (realSized.any fun p =>
    pointNB p.1.shape dryProofFull.2.1 cMax64 64) = true := by
  decide +kernel

theorem key_test64 : pointNB keyFull.once.shape dryKeyFull.2.1 cMax64 64 = true := by
  decide +kernel

/-- The count at letters is monotone. -/
theorem count_mono (e c q a b N : Nat) (h : e ≤ c * q ^ 10) (hN : N ≤ 64) :
    e * q ^ a + N * b ≤ c * q ^ 10 * q ^ a + 64 * b :=
  Nat.add_le_add (Nat.mul_le_mul_right _ h) (Nat.mul_le_mul_right _ hN)

/-- **LIN point, for up to 64 requests.** -/
theorem point_paid64 {S : LinShape} {Wr : Rounds} {rad work : Nat}
    (h : K14Rounds S Wr rad cMax work) (ht : pointNB S Wr cMax64 64 = true) (d : RDT)
    (hd : atW Wr 0 = some (d.entry, d.kind)) (W : Type) (F : Frame) (b : Block St Unit)
    (base N : Nat) (hN : N ≤ 64) :
    Err.Below (vecPiece (W := W) (F := F) b base d S.kCol
      (efReal * Fintype.card GE ^ S.kLo + N * (S.kCol * Fintype.card GE ^ (S.kCol - 1)))).err
      ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  unfold pointNB at ht
  rw [hd, Option.any_some] at ht
  refine vec_below b base d _ _ 128 (h.point d hd).1 (roundB_mono ?_ ht)
  have h64 := efReal_le64
  rw [card_GE_num] at h64 ⊢
  exact count_mono efReal cMax64 cardGl S.kLo _ N h64 hN

/-- What is had of a shape and a written list. -/
def Point64 (S : LinShape) (Wr : Rounds) : Prop :=
  ∀ (d : RDT), atW Wr 0 = some (d.entry, d.kind) →
    ∀ (W : Type) (F : Frame) (b : Block St Unit) (base N : Nat), N ≤ 64 →
      Err.Below (vecPiece (W := W) (F := F) b base d S.kCol
        (efReal * Fintype.card GE ^ S.kLo + N * (S.kCol * Fintype.card GE ^ (S.kCol - 1)))).err
        ((2 : ℝ≥0∞)⁻¹ ^ 128)

theorem point64_of {S : LinShape} {Wr : Rounds} {rad work : Nat}
    (h : K14Rounds S Wr rad cMax work) (ht : pointNB S Wr cMax64 64 = true) : Point64 S Wr :=
  fun d hd W F b base N hN => point_paid64 h ht d hd W F b base N hN

/-- **In a proof file.** -/
theorem k14_point64_real : ∃ x : LinSized, realSized = some (x, codesFull2) ∧ AtRecord x ∧
    Point64 x.shape dryProofFull.2.1 := by
  obtain ⟨x, a1, a2, -, a4⟩ := k14_rounds_real
  have h := real_test64
  rw [a1, Option.any_some] at h
  exact ⟨x, a1, a2, point64_of a4 h⟩

/-- **In a key file.** -/
theorem k14_point64_key : Point64 keyFull.once.shape dryKeyFull.2.1 :=
  point64_of k14_rounds_key key_test64

/-- The comparison can say no. -/
theorem teeth64 : ((realSized.any fun p =>
    !pointNB p.1.shape dryProofFull.2.1 (cMax64 + 1) 64) &&
    !pointNB keyFull.once.shape dryKeyFull.2.1 (cMax64 + 1) 64) = true := by
  decide +kernel

end Desc.K14.Law
