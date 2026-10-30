-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/K14RoundsAt.lean: the written errors of the kind K14's three drawing rounds
(LIN point, LOC,
LIN zeta) are shares of at most 2^-128 of the round's written challenges, at the kind's own counts,
from ONE comparison of natural numbers a round, which Lean's kernel evaluates at the written rounds
of
a proof file's and of a key file's second chain and at the typed shapes.

The kind's law (K14/Law/FencedRow.lean: row1to8_decoded) is stated at pieces that bear counts e1, e4
and e7: at least ef q ^ kLo + kCol q ^ (kCol - 1), (2 ^ logN - e' - 1) ^ n and kRow q ^ (kRow - 1).
At counts as large as the number of a round's values such a law says nothing. Here, by the library's
rule on written counts at natural numbers (`Maps.below_pow`, OnBytes/Flat/CarrySNum.lean), with b
the
round's hash blocks, V the number of its typed values and w its bits of work:
(2^128 + 1)^b e 2^128 ≤ (2^128)^b V 2^w gives `Err.Below` of the piece's errors at 2^-128.
  roundB en kd e k: the comparison, as a test with code · roundB_mono: it bears every smaller count
  vec_below, pos_below: from its yes: the errors of `vecPiece` and `posPiece`
  plainB, sends_of: a written round's entry and kind are such that the maps' condition
      `SendsDraws` holds, at the entry's own numbers
  K14Rounds S Wr rad cmax work: at every written round d with the entry and kind of Wr's round
      number
      0 | 3 | 6: SendsDraws at the shape's kCol | columns and logN | kRow; Err.Below at 2^-128 of
      the
      piece that bears ef q ^ kLo + kCol q ^ (kCol - 1) for EVERY ef ≤ cmax q ^ 10 | (2 ^ logN - rad
      -
      1) ^ columns | kRow q ^ (kRow - 1); and LOC's round bears `work` bits of work, the two others
      none
  k14RB, k14RB_sound: the test with code
  real_testR, key_testR: the test says yes: evaluations in Lean's kernel (decide +kernel)
  k14_rounds_real: in a proof file: rad 2852142980, cmax 18446744060824649715, 28 BITS OF WORK at
      LOC
  k14_rounds_key, k14_rounds_key_at_scope: in a key file: the same rad and cmax, 32 BITS OF WORK
      (what the written round bears; the comparison would pass at 31)
  teeth: the comparison says no at cmax + 1; at LOC with one bit of work less in a proof file (27)
      and two less in a key file (30); at LOC at the radius 0

HOW MANY BITS ARE WORK, as the row asks: LIN point and LIN zeta: no work. LOC: 28 of the 128 in the
scope of a batch (a proof file's shared chain), 32 in the scope of a one-time test (a key file's).

What is not claimed. hbad: that the count of the index's bad points is at most an ef ≤ cmax q ^ 10:
a premise of the law, «theorem on codes»' matter; cmax is the largest whole number at which the
comparison holds, no count of anything. One count a round: that a round shared by a batch is charged
once is another row. The two sendings between these rounds (K01_rounds). The round SPLIT behind
them, in which nothing is drawn. From Err.Below to the cap
(le_cap_of_below_inv) and the law's monotony in err: the user's step. That the written lists are
those of a description made of the release's files. What the heads of
Johnson/Goal/Numbers/K14CondAt.lean and
CondReal.lean do not claim. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Goal.Numbers.K14CondAt
import Johnson.Desc.K14.Law.GoodLoc
import OnBytes.Flat.CarrySNum
import OnBytes.Slice.RecordPriceGlue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Params.Prices OnBytes.Plan Johnson.G
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.K1 (realSized)
open Lk6.AtPlan (keyFull key_eq_at_scope)
open scoped ENNReal

/-! ## One comparison a round -/

/-- The comparison. -/
def roundB (en : Fmt.Entry) (kd : Fmt.Kind) (e k : Nat) : Bool :=
  decide (0 < nVals (Fmt.dsOf en kd)) &&
    decide ((2 ^ 128 + 1) ^ (bsRound .two en kd).b * e * 2 ^ k ≤
      (2 ^ 128) ^ (bsRound .two en kd).b * nVals (Fmt.dsOf en kd) * 2 ^ en.work)

theorem roundB_mono {en : Fmt.Entry} {kd : Fmt.Kind} {e e' k : Nat} (h : e' ≤ e)
    (hb : roundB en kd e k = true) : roundB en kd e' k = true := by
  unfold roundB at hb ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb ⊢
  exact ⟨hb.1, Nat.le_trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h)) hb.2⟩

variable {W : Type} {F : Frame}

theorem vec_below (b : Block St Unit) (base : Nat) (d : RDT) (n e k : Nat) {ns a : Nat}
    (hd : SendsDraws (toRD d) ns n 0 a) (h : roundB d.entry d.kind e k = true) :
    Err.Below (vecPiece (W := W) (F := F) b base d n e).err ((2 : ℝ≥0∞)⁻¹ ^ k) := by
  unfold roundB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  show Err.Below ((vecMaps d n).err ((e, ()) : Nat × Unit)) _
  exact Maps.below_pow (vecMaps d n) (vecMaps_ok hd) ((e, ()) : Nat × Unit)
    ⟨⟨e, nVals (Fmt.dsOf d.entry d.kind), h.1, Nat.le_refl _, h.2⟩, trivial⟩

theorem pos_below (b : Block St Unit) (base : Nat) (d : RDT) (a t e k : Nat) {ns : Nat}
    (hd : SendsDraws (toRD d) ns 0 t a) (h : roundB d.entry d.kind e k = true) :
    Err.Below (posPiece (W := W) (F := F) b base d a t e).err ((2 : ℝ≥0∞)⁻¹ ^ k) := by
  unfold roundB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  show Err.Below ((posMaps d a t).err ((e, ()) : Nat × Unit)) _
  exact Maps.below_pow (posMaps d a t) (posMaps_ok hd) ((e, ()) : Nat × Unit)
    ⟨⟨e, nVals (Fmt.dsOf d.entry d.kind), h.1, Nat.le_refl _, h.2⟩, trivial⟩

/-- An entry and a kind at which the maps' condition holds. -/
def plainB (en : Fmt.Entry) (kd : Fmt.Kind) : Bool :=
  decide (en.trits = 0) && decide (kd ≠ .sealed) && decide (kd ≠ .seeds) &&
    decide (en.drawNZ ≤ en.drawE) && decide (en.logN ≤ 64)

theorem sends_of (d : RDT) (h : plainB d.entry d.kind = true) :
    SendsDraws (toRD d) (nS d.items) d.entry.drawE d.entry.poss d.entry.logN := by
  unfold plainB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact sendsDraws_of (d := toRD d) (r := { entry := d.entry, kind := d.kind, items := d.items })
    ⟨rfl, rfl, rfl⟩ h.1.1.1.1 h.1.1.1.2 h.1.1.2 h.1.2 h.2

/-- The proof library's extension field has the format's number of elements. -/
theorem card_GE_num : Fintype.card GE = cardGl :=
  (cardE_card_GE recordSet rfl rfl).symm.trans recordSet_numbers.1

/-! ## The kind's three drawing rounds -/

/-- The entry and kind of a written list's round number i. -/
def atW (Wr : Rounds) (i : Nat) : Option (Fmt.Entry × Fmt.Kind) :=
  (Wr[i]?).map fun r => (r.1.entry, r.1.kind)

/-- **The kind's rounds at exact integers.** -/
structure K14Rounds (S : LinShape) (Wr : Rounds) (rad cmax work : Nat) : Prop where
  point : ∀ d : RDT, atW Wr 0 = some (d.entry, d.kind) →
    SendsDraws (toRD d) (nS d.items) S.kCol 0 d.entry.logN ∧ d.entry.work = 0 ∧
      ∀ (W : Type) (F : Frame) (b : Block St Unit) (base ef : Nat),
        ef ≤ cmax * Fintype.card GE ^ 10 →
          Err.Below (vecPiece (W := W) (F := F) b base d S.kCol
            (ef * Fintype.card GE ^ S.kLo + S.kCol * Fintype.card GE ^ (S.kCol - 1))).err
            ((2 : ℝ≥0∞)⁻¹ ^ 128)
  loc : ∀ d : RDT, atW Wr 3 = some (d.entry, d.kind) →
    SendsDraws (toRD d) (nS d.items) 0 S.fold.columns S.fold.index.code.logN ∧
      d.entry.work = work ∧
      ∀ (W : Type) (F : Frame) (b : Block St Unit) (base : Nat),
        Err.Below (posPiece (W := W) (F := F) b base d S.fold.index.code.logN S.fold.columns
          ((2 ^ S.fold.index.code.logN - rad - 1) ^ S.fold.columns)).err ((2 : ℝ≥0∞)⁻¹ ^ 128)
  zeta : ∀ d : RDT, atW Wr 6 = some (d.entry, d.kind) →
    SendsDraws (toRD d) (nS d.items) S.kRow 0 d.entry.logN ∧ d.entry.work = 0 ∧
      ∀ (W : Type) (F : Frame) (b : Block St Unit) (base : Nat),
        Err.Below (vecPiece (W := W) (F := F) b base d S.kRow
          (S.kRow * Fintype.card GE ^ (S.kRow - 1))).err ((2 : ℝ≥0∞)⁻¹ ^ 128)

/-- The test with code. -/
def k14RB (S : LinShape) (Wr : Rounds) (rad cmax work : Nat) : Bool :=
  (atW Wr 0).any (fun x => plainB x.1 x.2 && decide (x.1.drawE = S.kCol) &&
    decide (x.1.poss = 0) && decide (x.1.work = 0) &&
    roundB x.1 x.2 (cmax * cardGl ^ 10 * cardGl ^ S.kLo + S.kCol * cardGl ^ (S.kCol - 1)) 128) &&
  (atW Wr 3).any (fun x => plainB x.1 x.2 && decide (x.1.drawE = 0) &&
    decide (x.1.poss = S.fold.columns) && decide (x.1.logN = S.fold.index.code.logN) &&
    decide (x.1.work = work) &&
    roundB x.1 x.2 ((2 ^ S.fold.index.code.logN - rad - 1) ^ S.fold.columns) 128) &&
  (atW Wr 6).any (fun x => plainB x.1 x.2 && decide (x.1.drawE = S.kRow) &&
    decide (x.1.poss = 0) && decide (x.1.work = 0) &&
    roundB x.1 x.2 (S.kRow * cardGl ^ (S.kRow - 1)) 128)

theorem k14RB_sound {S : LinShape} {Wr : Rounds} {rad cmax work : Nat}
    (h : k14RB S Wr rad cmax work = true) : K14Rounds S Wr rad cmax work := by
  unfold k14RB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h0, h3⟩, h6⟩ := h
  refine ⟨fun d hd => ?_, fun d hd => ?_, fun d hd => ?_⟩
  · rw [hd] at h0
    simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at h0
    obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ := h0
    have s := sends_of d a1
    rw [a2, a3] at s
    refine ⟨s, a4, fun W F b base ef hef => vec_below b base d _ _ 128 s (roundB_mono ?_ a5)⟩
    rw [card_GE_num] at hef ⊢
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hef) _
  · rw [hd] at h3
    simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at h3
    obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := h3
    have s := sends_of d a1
    rw [a2, a3, a4] at s
    exact ⟨s, a5, fun W F b base => pos_below b base d _ _ _ 128 s a6⟩
  · rw [hd] at h6
    simp only [Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at h6
    obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ := h6
    have s := sends_of d a1
    rw [a2, a3] at s
    refine ⟨s, a4, fun W F b base => vec_below b base d _ _ 128 s ?_⟩
    rw [card_GE_num]
    exact a5

/-- The largest whole number c at which LIN point's comparison holds with c q ^ 10 q ^ 7. -/
def cMax : Nat := 18446744060824649715

/-! ## A proof file -/

theorem real_testR : (realSized.any fun p =>
    k14RB p.1.shape dryProofFull.2.1 recordRadius cMax 28) = true := by
  decide +kernel

/-- **The kind's rounds in a proof file: 28 bits of work at LOC, none elsewhere.** -/
theorem k14_rounds_real : ∃ x : LinSized, realSized = some (x, codesFull2) ∧ AtRecord x ∧
    (∀ (item : Nat) (bp : List (Nat × Nat)), bp ≠ [] →
      K14Cond 2 ⟨recordSet, .shared, codesFull2, x.shape, item, bp⟩ dryProofFull.2.1) ∧
    K14Rounds x.shape dryProofFull.2.1 recordRadius cMax 28 := by
  obtain ⟨x, a1, a2, a3⟩ := k14_real
  have h := real_testR
  rw [a1] at h
  exact ⟨x, a1, a2, a3, k14RB_sound h⟩

/-! ## A key file -/

theorem key_testR : k14RB keyFull.once.shape dryKeyFull.2.1 recordRadius cMax 32 = true := by
  decide +kernel

/-- **The kind's rounds in a key file: 32 bits of work at LOC, none elsewhere.** -/
theorem k14_rounds_key : K14Rounds keyFull.once.shape dryKeyFull.2.1 recordRadius cMax 32 :=
  k14RB_sound key_testR

theorem k14_rounds_key_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {p : Model.Verify.Planned} (hp : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p) :
    K14Rounds p.chains.made.sized.key.once.shape dryKeyFull.2.1 recordRadius cMax 32 := by
  rw [key_eq_at_scope hZ hp]
  exact k14_rounds_key

/-! ## The comparison can say no -/

/-- At cMax + 1; at LOC with less work; at LOC at the radius 0. -/
theorem teeth : (realSized.any fun p =>
    !k14RB p.1.shape dryProofFull.2.1 recordRadius (cMax + 1) 28 &&
    !k14RB p.1.shape dryProofFull.2.1 0 cMax 28 &&
    (atW dryProofFull.2.1 3).any (fun x => !roundB { x.1 with work := 27 } x.2
      ((2 ^ 32 - recordRadius - 1) ^ 64) 128) &&
    (atW dryKeyFull.2.1 3).any (fun x => !roundB { x.1 with work := 30 } x.2
      ((2 ^ 32 - recordRadius - 1) ^ 62) 128)) = true := by
  decide +kernel

end Desc.K14.Law
