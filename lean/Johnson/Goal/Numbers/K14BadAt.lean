-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/K14BadAt.lean: the premise hbad of the law of the kind K14's eight blocks
(K14/Law/
FencedRow.lean: row1to8_decoded: "of the fold points of a table without a collision at the record's
seed at most ef are bad") at the release's numbers, with ef a named number; and that number is
beneath the ceiling of Johnson/Goal/Numbers/K14RoundsAt.lean: so the written errors of the round LIN
point, at the
law's own count with that ef, are shares of at most 2^-128.

Johnson/Bridge/FoldErrIx.lean has `Cb.Bridge.foldErr_ix`: for an index X with the
format's matrix of a code C, below the Johnson radius: at most v b q ^ (v - 1) + L (v q ^ (v - 1))
fold points are bad, b the integer part of `Cb.bchksBound`, L the Johnson bound's list. Here C has 2
^ 32
positions and 446693375 coefficients, v = 11, the radius is 2852142980: L = 26
(`fr_list_tables`), b = `cntIx` with cntIx 2 ^ 132 ≤ q (`cnt132`, Johnson/B/Core9.lean).
  efOf c q, efReal: (11 c + 286) q ^ 10; at c := cntIx and the proof library's field
  efReal_le: efReal ≤ cMax q ^ 10
  bad_le_efReal: at every code C with these two numbers and every index X over it with the format's
      matrix, eleven row variables and a decoder's radius from 2852142980 to below the distance
      3848273922: for every table f and record rec without a collision at the record's seed:
      cnt (X.Bad f rec 2852142980) ≤ efReal
  index_real, index_key: the typed shapes' index has that code and eleven row variables: evaluations
      in Lean's kernel (decide +kernel)
  point_paid: from K14Rounds: at every written round with the entry and kind of the written list's
      round 0: Err.Below at 2^-128 of the piece that bears efReal q ^ kLo + kCol q ^ (kCol - 1)
  k14_point_real, k14_point_key: both together, in a proof file and in a key file
HOW IT IS SPENT. bad_le_efReal and point_paid do not lie on the road of the shared chain's law for
the proof file (k14_at_free_head, Johnson/Desc/K14/Law/LedgerAtFreeHead.lean): that law calls
Cb.Bridge.foldErr_ix itself (Johnson/Desc/Sound/PointAtJoint.lean), and of this file it spends efOf,
efReal, cntIx_le, count_eq, indexB and indexB_sound. The two are spent through k14_point_real and
k14_point_key, which these files call: Johnson/RunOne/KeyRow21Key.lean (a row of the key file),
Johnson/Goal/Numbers/WrittenAtZ.lean and OwedK13K14.lean [not in this library], and, for another
form of the kind's law (row1to8_decoded), Johnson/Goal/Numbers/K14CalledAt.lean
[not in this library] and K14CalledAllAt.lean [not in this library].
In row1to8_decoded: e' := 2852142980, ef := efReal, hbad := fun f rec hc =>
bad_le_efReal (codeOf P.par.S.fold.index.code) … (ixOf2 P.par.S.fold err eM rank) rfl … f rec hc:
ixOf2's matrix is genOf (codeOf …) and its v the index's by make; eM is a letter in that range.

IT RESTS, as foldErr_ix's own head says, on Cb/Bridge/CodeListRSProved.lean and so on the files
under ThirdParty/: files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15).


What is not claimed. How often a table has a collision at a seed. That the call at ixOf2 is typed:
K14/Law/PointKey2.lean, which holds ixOf2, was not in the build in which this file was compiled.
One count a round: that a round shared by a batch is charged once is another row. What the heads of
Johnson/Goal/Numbers/K14RoundsAt.lean and Johnson/Bridge/FoldErrIx.lean do not claim. Nothing on
soundness, on an
honest prover or on hiding.

-/
import Johnson.Goal.Numbers.K14RoundsAt
import Johnson.Bridge.FoldErrIx
import OnBytes.Slice.FullRecCodes
import Johnson.B.Core9

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Params.Prices OnBytes.Plan Johnson.G
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice Cb
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.K1 (realSized)
open Lk6.AtPlan (keyFull key_eq_at_scope)
open Cb.Gl.Ref (cntIx cnt132)
open scoped ENNReal

/-- The count, with c for the integer part of the statement on codes' bound, at q elements. -/
def efOf (c q : Nat) : Nat := (11 * c + 286) * q ^ 10

/-- A bound on the count of the bad fold points at the release's numbers. -/
noncomputable def efReal : Nat := efOf cntIx (Fintype.card GE)

theorem cntIx_le : cntIx ≤ 1152921503801540608 := by
  have h : cntIx * 2 ^ 132 ≤ Cb.Gl.p ^ 3 := cnt132
  have hp : Cb.Gl.p ^ 3 / 2 ^ 132 = 1152921503801540608 := by decide +kernel
  rw [← hp]
  exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos 132)).2 h

theorem efOf_le (c q : Nat) (h : c ≤ 1152921503801540608) : efOf c q ≤ cMax * q ^ 10 :=
  Nat.mul_le_mul_right _
    (Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left 11 h) 286) (by decide +kernel))

/-- **It is beneath the ceiling.** -/
theorem efReal_le : efReal ≤ cMax * Fintype.card GE ^ 10 := by
  unfold efReal
  exact efOf_le cntIx (Fintype.card GE) cntIx_le

/-- The statement on codes' count at these numbers, in the form of efOf. -/
theorem count_eq (C : Fmt.M1.Code) (ha : C.a = 32) (v q : Nat) (hv : v = 11)
    (e1 : C.r + C.l - 1 = 446693374) (e2 : 2 ^ C.a - (C.r + C.l) + 1 = 3848273922) :
    v * ⌊bchksBound (2 ^ C.a) (C.r + C.l - 1) 2852142980⌋₊ * q ^ (v - 1) +
        listMax (2 ^ C.a) (2 ^ C.a - (C.r + C.l) + 1) 2852142980 * (v * q ^ (v - 1)) =
      efOf cntIx q := by
  have hc : ⌊bchksBound (2 ^ 32) 446693374 2852142980⌋₊ = cntIx := rfl
  rw [hv, e1, e2, ha, fr_list_tables, show (11 - 1 : Nat) = 10 from rfl, hc]
  generalize cntIx = c
  unfold efOf
  ring

/-- **The bad fold points at the release's numbers.** -/
theorem bad_le_efReal (C : Fmt.M1.Code) (ha : C.a = 32) (hrl : C.r + C.l = 446693375)
    {J : Type} [Fintype J] (X : LdIx GE (Fin (2 ^ C.a)) (Fin (C.r + C.l)) J)
    (hG : X.G = genOf C) (hv : X.v = 11) (hle : 2852142980 ≤ X.eM) (hM : X.eM < 3848273922)
    (f : X.Row → Fin (2 ^ C.a) → GE) (rec : X.Rec) (hc : ¬ X.Coll f rec.1) :
    cnt (X.Bad f rec 2852142980) ≤ efReal := by
  have e1 : C.r + C.l - 1 = 446693374 := by
    rw [hrl]
  have e2 : 2 ^ C.a - (C.r + C.l) + 1 = 3848273922 := by
    rw [hrl, ha]
    decide +kernel
  have b1 : C.a ≤ 32 := Nat.le_of_eq ha
  have b2 : 0 < C.r + C.l - 1 := by
    rw [e1]
    decide
  have b3 : C.r + C.l ≤ 2 ^ C.a := by
    rw [hrl, ha]
    decide +kernel
  have b4 : InJohnson (2 ^ C.a) (2 ^ C.a - (C.r + C.l) + 1) 2852142980 := by
    rw [e2, ha]
    unfold InJohnson
    decide +kernel
  have h := Cb.Bridge.foldErr_ix C X 2852142980 b1 b2 b3 hG (by decide) hle
    (lt_of_lt_of_eq hM e2.symm) b4 f rec hc
  unfold efReal
  exact le_trans h (le_of_eq (count_eq C ha X.v (Fintype.card GE) hv e1 e2))

/-! ## The typed shapes' index -/

/-- The index's numbers, as a test with code. -/
def indexB (S : LinShape) : Bool :=
  decide (S.fold.index.code.logN = 32) &&
    decide (S.fold.index.code.r + S.fold.index.code.ell = 446693375) &&
    decide (S.fold.index.v = 11)

theorem index_real : (realSized.any fun p => indexB p.1.shape) = true := by decide +kernel

theorem index_key : indexB keyFull.once.shape = true := by decide +kernel

theorem indexB_sound {S : LinShape} (h : indexB S = true) :
    (codeOf S.fold.index.code).a = 32 ∧
      (codeOf S.fold.index.code).r + (codeOf S.fold.index.code).l = 446693375 ∧
      S.fold.index.v = 11 := by
  unfold indexB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-! ## LIN point, paid -/

/-- **The round LIN point at the law's own count with ef := efReal.** -/
theorem point_paid {S : LinShape} {Wr : Rounds} {rad work : Nat}
    (h : K14Rounds S Wr rad cMax work) (d : RDT) (hd : atW Wr 0 = some (d.entry, d.kind))
    (W : Type) (F : Frame) (b : Block St Unit) (base : Nat) :
    Err.Below (vecPiece (W := W) (F := F) b base d S.kCol
      (efReal * Fintype.card GE ^ S.kLo + S.kCol * Fintype.card GE ^ (S.kCol - 1))).err
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  (h.point d hd).2.2 W F b base efReal efReal_le

/-- What is had of a shape S and a written list Wr. -/
def PointPaid (S : LinShape) (Wr : Rounds) : Prop :=
  (∀ {J : Type} [Fintype J]
    (X : LdIx GE (Fin (2 ^ (codeOf S.fold.index.code).a))
      (Fin ((codeOf S.fold.index.code).r + (codeOf S.fold.index.code).l)) J),
    X.G = genOf (codeOf S.fold.index.code) → X.v = S.fold.index.v → 2852142980 ≤ X.eM →
    X.eM < 3848273922 → ∀ (f : X.Row → Fin (2 ^ (codeOf S.fold.index.code).a) → GE) (rec : X.Rec),
      ¬ X.Coll f rec.1 → cnt (X.Bad f rec 2852142980) ≤ efReal) ∧
  ∀ (d : RDT), atW Wr 0 = some (d.entry, d.kind) →
    ∀ (W : Type) (F : Frame) (b : Block St Unit) (base : Nat),
      Err.Below (vecPiece (W := W) (F := F) b base d S.kCol
        (efReal * Fintype.card GE ^ S.kLo + S.kCol * Fintype.card GE ^ (S.kCol - 1))).err
        ((2 : ℝ≥0∞)⁻¹ ^ 128)

theorem pointPaid_of {S : LinShape} {Wr : Rounds} {rad work : Nat} (hi : indexB S = true)
    (h : K14Rounds S Wr rad cMax work) : PointPaid S Wr := by
  obtain ⟨i1, i2, i3⟩ := indexB_sound hi
  exact ⟨fun X hG hv hle hM f rec hc =>
    bad_le_efReal _ i1 i2 X hG (hv.trans i3) hle hM f rec hc,
    fun d hd W F b base => point_paid h d hd W F b base⟩

/-- **In a proof file.** -/
theorem k14_point_real : ∃ x : LinSized, realSized = some (x, codesFull2) ∧ AtRecord x ∧
    K14Rounds x.shape dryProofFull.2.1 recordRadius cMax 28 ∧
    PointPaid x.shape dryProofFull.2.1 := by
  obtain ⟨x, a1, a2, -, a4⟩ := k14_rounds_real
  have h := index_real
  rw [a1] at h
  exact ⟨x, a1, a2, a4, pointPaid_of h a4⟩

/-- **In a key file.** -/
theorem k14_point_key : PointPaid keyFull.once.shape dryKeyFull.2.1 :=
  pointPaid_of index_key k14_rounds_key

end Desc.K14.Law
