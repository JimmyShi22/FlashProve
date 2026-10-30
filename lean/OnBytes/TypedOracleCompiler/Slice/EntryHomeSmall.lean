-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryHomeSmall.lean: WHAT IS LEFT OF THE ENTRY'S DEBTS, AT THE SMALL EXAMPLE OF
THE SETTING WITH A RECORD: the fields that are numbers, discharged.

The like of OnBytes/TypedOracleCompiler/Slice/EntryHomeFull.lean at the sizes `zSmall`
(OnBytes/TypedOracleCompiler/Slice/ShapesAtSmall.lean), the description `entryXD smallRecordGround` (the ground:
OnBytes/Tie/EntryGrounds.lean) and the error 2^-128: ONE TEXT OF DEFINITIONS AT ANOTHER SIZE.

Main theorems, each in the letters of its field of `HomeData.Left`.
 `small_base_ok`       the ground's description is in order at an empty statement.
 `small_fit`           the sizes are in order.
 `small_bound_letters`, `small_price`   the record's bound is at most the typed price of the
                       record's round at the small lines, so at most 2^-128 (that price is at most
                       2^-175).
 `small_depthIs`, `small_field`, `small_K`, `small_enough`, `small_blocksLe`   the depth is the
                       code's, 23; the field is the second; a verifier's message has 99 blocks; the
                       seeds' sampler reads 95; an answer has at most 101 blocks.
 `small_sizes`         the sizes of `zSmall` are those of the typed small link, by unfolding.
 `small_four`          the four data that soundness record by record asks of a description.
 `left_small`          `HomeData.Left` at these terms, at 101 blocks, from the three fields that
                       stay.

What did not go through, and what is not claimed: as the head of
OnBytes/TypedOracleCompiler/Slice/EntryHomeFull.lean says, read at the small example. That the small lines are those
of any file that a program is run with: see the heads of the files that type them.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryHomeGround
import OnBytes.TypedOracleCompiler.Slice.EntryDescWire
import OnBytes.TypedOracleCompiler.Slice.SmallRecDesc
import OnBytes.Slice.RecordPriceGlue
import OnBytes.Params.RecordBelow
import OnBytes.Params.EntryFactsRecord

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Prob Cb TypedOracleCompiler.Run
open OnBytes.Slice (recZ seedBS seedBS_b srS srD srRd srC)
open OnBytes.Slice.Shapes (zSmall zSmall_fit zSmall_lg zSmall_s)
open OnBytes.Tie (smallRecordGround)
open EntryAccept (asTypedCompilerDescription)
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (View)
open TypedOracleCompiler.Run.PQ (bodyS)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open OnBytes.Slice.Shapes (Cfg dgOf Spells)
open scoped ENNReal

/-- The ground's own description is in order at an empty statement. -/
theorem small_base_ok :
    (OnBytes.Params.entrySpecOf smallRecordGround.q smallRecordGround.rs ByteArray.empty).base.ok = true :=
  OnBytes.Tie.small_record_baseOk ByteArray.empty (by decide)

/-- The sizes are in order. -/
theorem small_fit : zSmall.Fit := zSmall_fit

/-- The setting of the small lines with a record has the extension field's number of elements. -/
theorem smallRecordSet_card : OnBytes.Params.smallRecordSet.cardE = Fintype.card OnBytes.Slice.GE :=
  OnBytes.Slice.cardE_card_GE OnBytes.Params.smallRecordSet (by decide +kernel) (by decide +kernel)

/-- The seeds' sampler at the small sizes reads 95 blocks. -/
theorem small_seed_blocks : (seedBS 19 1).b = 95 := by
  rw [seedBS_b]
  exact OnBytes.Params.record_seed_blocks.2

/-- The code of a table's row at the small sizes. -/
def smT : Fmt.M1.Code := ⟨23, 524288, 65535⟩

/-- The record's bound at the small sizes is at most the typed price of the record's round. -/
theorem small_bound_letters : kapSl 128 ^ (seedBS 19 1).b *
    ((((Cb.listMax (2 ^ smT.a) (2 ^ smT.a - (smT.r + smT.l) + 1) OnBytes.Params.smallRecordRadius).choose
      2 * (recZ smT.l 19 1).err : ℕ) : ℝ≥0∞) / Fintype.card (recZ smT.l 19 1).D) ≤
      ENNReal.ofReal ((OnBytes.Params.smallRecordPrice.val : ℚ) : ℝ) := by
  have e1 : (2 : ℕ) ^ smT.a = 2 ^ 23 := rfl
  have e2 : 2 ^ 23 - (smT.r + smT.l) + 1 = 7798786 := by decide
  have hpos : 0 < Fintype.card (recZ smT.l 19 1).D := Fintype.card_pos
  rw [e1, e2, small_seed_blocks, OnBytes.Slice.bound_ofReal 95 _ _ hpos,
    OnBytes.Slice.recZ_err_clash, OnBytes.Slice.recZ_card_all, ← smallRecordSet_card]
  exact ENNReal.ofReal_le_ofReal
    (OnBytes.Params.small_record_covers_at (b := 95) (by positivity) (by norm_num))

/-- 2^-175, as a real number, is at most 2^-128 in the extended reals. -/
theorem ofReal_two_175 : ENNReal.ofReal ((2 : ℝ) ^ (-175 : ℤ)) ≤ ((2 : ℝ≥0∞)⁻¹) ^ 128 := by
  have hr : (2 : ℝ) ^ (-175 : ℤ) ≤ ((2 : ℝ)⁻¹) ^ 128 := by
    have e : (2 : ℝ) ^ (-175 : ℤ) = ((2 : ℝ) ^ 175)⁻¹ := by
      rw [zpow_neg]
      norm_cast
    rw [e, inv_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) (by norm_num))
  have he : ENNReal.ofReal (((2 : ℝ)⁻¹) ^ 128) = ((2 : ℝ≥0∞)⁻¹) ^ 128 := by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by norm_num),
      ENNReal.ofReal_ofNat]
  rw [← he]
  exact ENNReal.ofReal_le_ofReal hr

/-- THE RECORD'S BOUND IS AT MOST 2^-128, in the letters of `HomeData.Left.price`. -/
theorem small_price : kapSl 128 ^ (seedBS zSmall.lg zSmall.s).b *
    ((((Cb.listMax (2 ^ zSmall.T.a) (2 ^ zSmall.T.a - (zSmall.T.r + zSmall.T.l) + 1)
      zSmall.eM).choose 2 * (recZ zSmall.T.l zSmall.lg zSmall.s).err : ℕ) : ℝ≥0∞) /
        Fintype.card (recZ zSmall.T.l zSmall.lg zSmall.s).D) ≤ ((2 : ℝ≥0∞)⁻¹) ^ 128 := by
  have eM : zSmall.eM = OnBytes.Params.smallRecordRadius := rfl
  have eT : zSmall.T = smT := rfl
  rw [zSmall_lg, eT, zSmall_s, eM]
  exact (small_bound_letters.trans
    (ENNReal.ofReal_le_ofReal OnBytes.Params.smallRecordPrice_below)).trans ofReal_two_175

/-- The depth of the description's stored tables is the code's. -/
theorem small_depthIs (c : ByteArray) : (entryXD smallRecordGround c).a = zSmall.T.a := by
  rw [entryXD_depth]
  exact OnBytes.Params.small_record_depth.1

/-- The description's field is the second. -/
theorem small_field (c : ByteArray) : (entryXD smallRecordGround c).base.plan.field = .two :=
  OnBytes.Params.record_field.2

/-- A verifier's message has 99 blocks. -/
theorem small_K (c : ByteArray) : (entryXD smallRecordGround c).K = 99 :=
  (entryXD_blocks smallRecordGround c).trans (OnBytes.Params.small_record_kOf ByteArray.empty)

/-- Blocks enough for the seeds' sampler. -/
theorem small_enough (c : ByteArray) :
    (seedBS zSmall.lg zSmall.s).b ≤ (entryXD smallRecordGround c).K := by
  rw [small_K, zSmall_lg]
  show (seedBS 19 1).b ≤ 99
  rw [small_seed_blocks]
  decide

/-- An answer has at most 101 blocks. -/
theorem small_blocksLe (c : ByteArray) : (entryXD smallRecordGround c).K + 2 ≤ 101 :=
  le_of_eq (congrArg (· + 2) (small_K c))

/-- The sizes of `zSmall` are those of the typed small link: code, row variables, radius; 19
coordinates; one answer. -/
theorem small_sizes : zSmall.T = srS.P.T ∧ zSmall.v = srS.P.v ∧ zSmall.eM = srS.eM ∧
    zSmall.lg = 19 ∧ zSmall.s = 1 := ⟨rfl, rfl, rfl, zSmall_lg, rfl⟩

/-- THE FOUR DATA THAT SOUNDNESS RECORD BY RECORD ASKS OF A DESCRIPTION, at every byte string
c. -/
theorem small_four (c : ByteArray) :
    (entryXD smallRecordGround c).base.plan.field = .two ∧
      (entryXD smallRecordGround c).ds =
        (srRd 0 :: srRd 1 :: srRd 2 :: srRd 3 :: srRd 4 :: srRd 5 :: srC.rds).map PQ.ofLib ∧
      (entryXD smallRecordGround c).a = srS.P.T.a ∧
      (entryXD smallRecordGround c).xs = srD.xs := by
  have hst : (entryXD smallRecordGround c).stored = (asTypedCompilerDescription srD).stored := rfl
  have hr : (entryXD smallRecordGround c).base.rounds = (asTypedCompilerDescription srD).base.rounds := rfl
  have ha : (entryXD smallRecordGround c).a = (asTypedCompilerDescription srD).a := by
    unfold PQ.XD.a
    rw [hst]
  have hx : (entryXD smallRecordGround c).xs = (asTypedCompilerDescription srD).xs := by
    unfold PQ.XD.xs
    rw [hst]
  exact ⟨small_field c, (PQ.rds_congr _ _ hr rfl).trans sr_two_ds, ha.trans sr_two_a,
    hx.trans sr_two_xs.1⟩

/-- `HomeData.Left` AT THESE TERMS, FROM THE THREE FIELDS THAT STAY. The six fields on numbers
are discharged, and the wiring's laws (`small_record_wiring`,
OnBytes/TypedOracleCompiler/Slice/EntryDescWire.lean); soundness record by record, the page's spelling and the typed
verifier's count are hypotheses, each in the letters of its field. The decision and the page's code
behind the escape are arguments. -/
theorem left_small (d₁ : Sd1 zSmall.lg zSmall.s) [DecidableEq (Sd1 zSmall.lg zSmall.s)]
    (dec : ByteArray → XE (List T3) zSmall.lg zSmall.s → View → Bool)
    (back : ∀ c, StrCode (AllPts 256 ((entryXD smallRecordGround c).K + 1)
      (EntryFill.Ls (entryXD smallRecordGround c) d₁)))
    (cfg : Cfg) (V : ℕ)
    (sound : ∀ c, c.size = 32 →
      ∃ ε : Err (Link0 (entryXD smallRecordGround c) fun _ => true).shape,
        (∀ x, (Link0 (entryXD smallRecordGround c) (dec c x)).Sound
          (fun _ => lgEX zSmall.T zSmall.v zSmall.eM zSmall.lg zSmall.s
            (entryXD smallRecordGround c) (anT zSmall.v zSmall.s) x) ε) ∧
          Err.Below ε (((2 : ℝ≥0∞)⁻¹) ^ 128))
    (spells : ∀ T₀ T₁, Spells
      ((HomeData.ofGround smallRecordGround zSmall d₁ small_base_ok dec back).atR cfg
        (fun _ => []) T₀ T₁).m
      (bodyS (entryXD smallRecordGround (dgOf cfg T₀)).a
        (entryXD smallRecordGround (dgOf cfg T₀)).base.plan.salt).embE (dgOf cfg T₀) zSmall.T.a
      zSmall.shape.saltBytes)
    (count : ∀ T₀ T₁,
      (((HomeData.ofGround smallRecordGround zSmall d₁ small_base_ok dec back).atR cfg
        (fun _ => []) T₀ T₁).base zSmall.T zSmall.v zSmall.eM (anT zSmall.v zSmall.s)
          (((2 : ℝ≥0∞)⁻¹) ^ 128)).J.tV = V) :
    (HomeData.ofGround smallRecordGround zSmall d₁ small_base_ok dec back).Left cfg
      (((2 : ℝ≥0∞)⁻¹) ^ 128) 101 V where
  fit := small_fit
  price := small_price
  depthIs := fun c _ => small_depthIs c
  field := fun c _ => small_field c
  enough := fun c _ => small_enough c
  wiring := small_record_wiring
  sound := sound
  blocksLe := fun c _ => small_blocksLe c
  spells := spells
  count := count

end TypedOracleCompiler.Slice
