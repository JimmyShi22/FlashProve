-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryHomeFull.lean: WHAT IS LEFT OF THE ENTRY'S DEBTS, AT THE FULL-SIZE FILES OF
THE SETTING WITH A RECORD: the fields that are numbers, discharged.

`HomeData.Left` (OnBytes/TypedOracleCompiler/Slice/EntryHome.lean) names what is left of the list of the entry's
debts. Here its fields on numbers are shown at the sizes `zFull`
(OnBytes/TypedOracleCompiler/Slice/ShapesAtFull.lean), the description `entryXD recordGround`
(OnBytes/TypedOracleCompiler/Slice/EntryDesc.lean; the ground: OnBytes/Tie/EntryGrounds.lean) and the error
2^-128.

Main theorems, each in the letters of its field.
 `full_base_ok`        the ground's description is in order at an empty statement: so
                       `HomeData.ofGround recordGround zFull` can be formed.
 `full_fit`            the sizes are in order.
 `full_price`          the record's bound is at most 2^-128 (it is at most the typed price,
                       which is at most 2^-178).
 `full_depthIs`, `full_field`, `full_K`, `full_enough`, `full_blocksLe`   the depth is the code's,
                       32; the field is the second; a verifier's message has 140 blocks; these are
                       enough for the seeds' sampler; an answer has at most 142 blocks.
 `full_sizes`          the sizes of `zFull` are those of the typed full-size link, by unfolding.
 `full_four`           the four data that soundness record by record asks of a description: the
                       field; the rounds' data are the typed link's five, the batching's and the
                       chain's, read as the second compiler's; the depth; the openings of stored
                       tables.

 `left_full`           `HomeData.Left` at these terms, at 142 blocks, from the three fields that
                       stay.

WHAT DID NOT GO THROUGH, AND WHY.
 (1) `sound`: the theorem that would give it, from two hypotheses of its own, at the decision of the
     program's link at keys written of an instance, is not imported.
     What it asks OF THE DESCRIPTION is shown (`full_four`);
     that the sizes of `zFull` are its sizes is shown too (`full_sizes`). So `sound` stays a
     hypothesis, and the decision a letter.
 (2) `spells`, `count`: not tried here. The first is the page's three equations of strings; the
     second a number.

What is not claimed. THREE FIELDS OF `Left` STAY HYPOTHESES. Soundness record by record is not
shown. Nothing is delivered. No probability but in the price, which is for one table and one key
fixed beforehand. The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made
with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryHomeGround
import OnBytes.TypedOracleCompiler.Slice.EntryDescWire
import OnBytes.TypedOracleCompiler.Slice.FullRecDesc
import OnBytes.Slice.RecordPriceGlue
import OnBytes.Params.RecordBelow
import OnBytes.Params.EntryFactsRecord

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Prob Cb TypedOracleCompiler.Run
open OnBytes.Slice (recZ seedBS recT recLg recS seedBS_b_full frS frD frRd frC)
open OnBytes.Slice.Shapes (zFull zFull_fit zFull_lg zFull_T zFull_s)
open OnBytes.Tie (recordGround)
open EntryAccept (asTypedCompilerDescription)
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (View)
open TypedOracleCompiler.Run.PQ (bodyS)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open OnBytes.Slice.Shapes (Cfg dgOf Spells)
open scoped ENNReal

/-- The ground's own description is in order at an empty statement. -/
theorem full_base_ok :
    (OnBytes.Params.entrySpecOf recordGround.q recordGround.rs ByteArray.empty).base.ok = true :=
  OnBytes.Tie.record_baseOk ByteArray.empty (by decide)

/-- The sizes are in order. -/
theorem full_fit : zFull.Fit := zFull_fit

/-- 2^-178, as a real number, is at most 2^-128 in the extended reals. -/
theorem ofReal_two_178 : ENNReal.ofReal ((2 : ℝ) ^ (-178 : ℤ)) ≤ ((2 : ℝ≥0∞)⁻¹) ^ 128 := by
  have hr : (2 : ℝ) ^ (-178 : ℤ) ≤ ((2 : ℝ)⁻¹) ^ 128 := by
    have e : (2 : ℝ) ^ (-178 : ℤ) = ((2 : ℝ) ^ 178)⁻¹ := by
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
theorem full_price : kapSl 128 ^ (seedBS zFull.lg zFull.s).b *
    ((((Cb.listMax (2 ^ zFull.T.a) (2 ^ zFull.T.a - (zFull.T.r + zFull.T.l) + 1) zFull.eM).choose
      2 * (recZ zFull.T.l zFull.lg zFull.s).err : ℕ) : ℝ≥0∞) /
        Fintype.card (recZ zFull.T.l zFull.lg zFull.s).D) ≤ ((2 : ℝ≥0∞)⁻¹) ^ 128 := by
  have eM : zFull.eM = OnBytes.Params.recordRadius := rfl
  rw [zFull_lg, zFull_T, zFull_s, eM]
  exact (OnBytes.Slice.record_bound_full_letters.trans
    (ENNReal.ofReal_le_ofReal OnBytes.Params.recordPrice_below)).trans ofReal_two_178

/-- The depth of the description's stored tables is the code's. -/
theorem full_depthIs (c : ByteArray) : (entryXD recordGround c).a = zFull.T.a := by
  rw [entryXD_depth]
  exact OnBytes.Params.record_depth.1

/-- The description's field is the second. -/
theorem full_field (c : ByteArray) : (entryXD recordGround c).base.plan.field = .two :=
  OnBytes.Params.record_field.1

/-- A verifier's message has 140 blocks. -/
theorem full_K (c : ByteArray) : (entryXD recordGround c).K = 140 :=
  (entryXD_blocks recordGround c).trans (OnBytes.Params.record_kOf ByteArray.empty)

/-- Blocks enough for the seeds' sampler. -/
theorem full_enough (c : ByteArray) :
    (seedBS zFull.lg zFull.s).b ≤ (entryXD recordGround c).K := by
  rw [full_K, zFull_lg]
  exact le_of_eq seedBS_b_full

/-- An answer has at most 142 blocks. -/
theorem full_blocksLe (c : ByteArray) : (entryXD recordGround c).K + 2 ≤ 142 :=
  le_of_eq (congrArg (· + 2) (full_K c))

/-- The sizes of `zFull` are those of the typed full-size link: code, row variables, radius; 29
coordinates; one answer. -/
theorem full_sizes : zFull.T = frS.P.T ∧ zFull.v = frS.P.v ∧ zFull.eM = frS.eM ∧ zFull.lg = 29 ∧
    zFull.s = 1 := ⟨rfl, rfl, rfl, zFull_lg, rfl⟩

/-- THE FOUR DATA THAT SOUNDNESS RECORD BY RECORD ASKS OF A DESCRIPTION, at every byte string
c. -/
theorem full_four (c : ByteArray) :
    (entryXD recordGround c).base.plan.field = .two ∧
      (entryXD recordGround c).ds =
        (frRd 0 :: frRd 1 :: frRd 2 :: frRd 3 :: frRd 4 :: frRd 5 :: frC.rds).map PQ.ofLib ∧
      (entryXD recordGround c).a = frS.P.T.a ∧ (entryXD recordGround c).xs = frD.xs := by
  have hst : (entryXD recordGround c).stored = (asTypedCompilerDescription frD).stored := rfl
  have hr : (entryXD recordGround c).base.rounds = (asTypedCompilerDescription frD).base.rounds := rfl
  have ha : (entryXD recordGround c).a = (asTypedCompilerDescription frD).a := by
    unfold PQ.XD.a
    rw [hst]
  have hx : (entryXD recordGround c).xs = (asTypedCompilerDescription frD).xs := by
    unfold PQ.XD.xs
    rw [hst]
  exact ⟨full_field c, (PQ.rds_congr _ _ hr rfl).trans fr_two_ds, ha.trans fr_two_a,
    hx.trans fr_two_xs.1⟩

/-- `HomeData.Left` AT THESE TERMS, FROM THE THREE FIELDS THAT STAY. The six fields on numbers
are discharged, and the wiring's laws (`record_wiring`,
OnBytes/TypedOracleCompiler/Slice/EntryDescWire.lean); soundness record by record, the page's spelling and the typed
verifier's count are hypotheses, each in the letters of its field. The decision and the page's code
behind the escape are arguments. -/
theorem left_full (d₁ : Sd1 zFull.lg zFull.s) [DecidableEq (Sd1 zFull.lg zFull.s)]
    (dec : ByteArray → XE (List T3) zFull.lg zFull.s → View → Bool)
    (back : ∀ c, StrCode (AllPts 256 ((entryXD recordGround c).K + 1)
      (EntryFill.Ls (entryXD recordGround c) d₁)))
    (cfg : Cfg) (V : ℕ)
    (sound : ∀ c, c.size = 32 →
      ∃ ε : Err (Link0 (entryXD recordGround c) fun _ => true).shape,
        (∀ x, (Link0 (entryXD recordGround c) (dec c x)).Sound
          (fun _ => lgEX zFull.T zFull.v zFull.eM zFull.lg zFull.s (entryXD recordGround c)
            (anT zFull.v zFull.s) x) ε) ∧ Err.Below ε (((2 : ℝ≥0∞)⁻¹) ^ 128))
    (spells : ∀ T₀ T₁, Spells
      ((HomeData.ofGround recordGround zFull d₁ full_base_ok dec back).atR cfg
        (fun _ => []) T₀ T₁).m
      (bodyS (entryXD recordGround (dgOf cfg T₀)).a
        (entryXD recordGround (dgOf cfg T₀)).base.plan.salt).embE (dgOf cfg T₀) zFull.T.a
      zFull.shape.saltBytes)
    (count : ∀ T₀ T₁,
      (((HomeData.ofGround recordGround zFull d₁ full_base_ok dec back).atR cfg
        (fun _ => []) T₀ T₁).base zFull.T zFull.v zFull.eM (anT zFull.v zFull.s)
          (((2 : ℝ≥0∞)⁻¹) ^ 128)).J.tV = V) :
    (HomeData.ofGround recordGround zFull d₁ full_base_ok dec back).Left cfg
      (((2 : ℝ≥0∞)⁻¹) ^ 128) 142 V where
  fit := full_fit
  price := full_price
  depthIs := fun c _ => full_depthIs c
  field := fun c _ => full_field c
  enough := fun c _ => full_enough c
  wiring := record_wiring
  sound := sound
  blocksLe := fun c _ => full_blocksLe c
  spells := spells
  count := count

end TypedOracleCompiler.Slice
