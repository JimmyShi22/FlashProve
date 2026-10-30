-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/RecordPriceGlue.lean: the bound of OnBytes/Slice/SeedBias.lean on the probability that
a stored table's record does not single one table out is at most the planner's price of the record's
round; at full size and the radius `recordRadius`, without a hypothesis.

OnBytes/Params/RecordPrice.lean compares numbers: a count (L choose 2) times `clashSeeds q lg ^ a`
among `allSeeds q lg ^ a` seeds, with a bias (1 + x) ^ b, against the error of `sampleError`. It
does not import the count. Here its letters are filled: q is the number of elements of the extension
field, a the number s of answers, the two numbers of seeds are the sample map's `err` and its number
of seeds, x is 2^-128 (`kapSl 128`), b the number of blocks, and L the library's `listMax`. The
planner's k is the dimension less 1, so its distance n - k is the code's own, 2^a - (r + l) + 1, at
which OnBytes/Slice/RecordColl.lean counts (`OnBytes.Params.wordOf_distance`).

The radius `recordRadius`: the planner's distance of the one-time test times the length, rounded
down (`OnBytes.Params.rr_radius`).

Main theorems.
 `card_NZ_sub`, `recZ_err_clash`, `recZ_card_all`   THE SAMPLE MAP'S TWO NUMBERS ARE THE PLANNER'S:
                        `(recZ l lg s).err = clashSeeds |GE| lg ^ s`; the number of its seeds is
                        `allSeeds |GE| lg ^ s`.
 `cardE_card_GE`, `recordSet_card`   a setting with the format's base field and the degree 3 has the
                        extension field's number of elements; so the setting of the full-size lines
                        with a record.
 `kapSl_real`, `bound_ofReal`   the bias and the share as a real number.
 `record_bound_le_price`   THE BOUND IS AT MOST THE PRICE `sampleError st list lg s`, for any list
                        size that is at least `listMax`.
 `coll_pr_bytes_price`, `coll_pr_bytes_full_price`   so the probabilities of `coll_pr_bytes` and
                        `coll_pr_bytes_full` (OnBytes/Slice/SeedRow.lean) are at most that price.
                        Used by nothing here.
 `record_bound_le_round`   the bound against the price at the list size of a table's one-time test,
                        under the hypotheses of `OnBytes.Params.record_round_covers`, for a table
                        whose code has the sizes of T and a dimension that is not 0 and at most the
                        length. Used by nothing here.
 `recordTable_sizes`, `recordLink_recShape`   THE LAW THAT TIES THE SIZES: the planner's table and
                        the entry's shape at the full-size lines with a record have the sizes of
                        OnBytes/Slice/RecordFull.lean.
 `record_bound_full_closed`, `record_bound_full_letters`   THE BOUND ITSELF, AT FULL SIZE AND THAT
                        RADIUS, WITHOUT A HYPOTHESIS, is at most `recordPrice`, the typed price of
                        the round RECORD (OnBytes/Params/RecordRound.lean): in the form of the right
                        side of the four theorems at full size, and in the letters in which a
                        compiled part's judge asks it.
 `coll_pr_bytes_full_closed`, `coll_measure_oracle_full_closed`   so the probability over uniform
                        blocks, and the measure of a set of oracles (OnBytes/Slice/SeedOracle.lean),
                        are at most that price.

What is not claimed. Before `recordTable_sizes` no number is evaluated: that the price is not marked
bad, that 2 b 2^-128 list ≤ 1, that the radius is within the one-time test's agreement are
hypotheses, and lg and s are arguments. From there on the numbers are those of
OnBytes/Params/RecordRound.lean, decided by Lean's kernel there. That `recordPrice` is below a
number: `OnBytes.Params.recordPrice_below` (OnBytes/Params/RecordBelow.lean), not imported here.
That a parameter file has the lines at which these sizes stand is proved of no file. ONE stored
table, and for the oracle ONE key, fixed beforehand; one try: nothing for a committer that tries
many names.

The planner does not compare this price with its target: it compares the round's error with the
draws' distance from uniform added (`wholeError`, OnBytes/Params/Planner.lean), which is larger;
here the bias is paid inside the price. The price is that of the ENTRY's plan at `recordLines`
(`OnBytes.Params.record_first_round`); the key's plan is not evaluated. Where a compiled part uses
the bound, it is no summand of its own: one error stands above it and is paid at every query of the
multiplied count (OnBytes/TypedOracleCompiler/Slice/SeedsBridge.lean). That the sample map is the program's is a
reading. Nothing on the fold's test at that radius. Nothing on proof of work. Nothing on any hash
function. What the heads of SeedRow.lean, SeedBias.lean, SeedOracle.lean and RecordColl.lean do not
claim.

-/
import OnBytes.Slice.SeedRow
import OnBytes.Slice.SeedOracle
import OnBytes.Slice.RatesToy
import OnBytes.Params.RecordRound

set_option autoImplicit false

namespace OnBytes.Slice
open Prob Cb Cb.Ood _root_.Iop _root_.Run
open scoped ENNReal
open OnBytes.Params (Setting clashSeeds allSeeds sampleError record_price_covers TableSize wordOf
  tableAnalysis tableAnalysis_fromM johnson listMax_le_list wordOf_distance recordSet recordRadius
  recordPrice record_radius_inJohnson record_full_covers
  recordTable)

/-! ## The sample map's two numbers are the planner's -/

/-- In any finite type there are as many elements other than a as elements, less one. Stated for a
letter α, so that no number of elements is computed. -/
theorem card_ne_sub_one {α : Type} [Fintype α] (a : α) [Fintype { x : α // x ≠ a }] :
    Fintype.card { x : α // x ≠ a } = Fintype.card α - 1 := by
  classical
  have h := Fintype.card_subtype_compl (fun x : α => x = a)
  rw [Fintype.card_subtype_eq] at h
  exact Eq.trans (@Fintype.card_congr _ _ _ _ (Equiv.refl _)) h

/-- There are as many factors as elements of the extension field less one. -/
theorem card_NZ_sub : Fintype.card NZ = Fintype.card GE - 1 := @card_ne_sub_one GE _ 0 _

/-- **The number `err` of the sample map is the number of clashing seeds of one answer, to the power
of the number of answers.** -/
theorem recZ_err_clash (l lg s : ℕ) :
    (recZ l lg s).err = clashSeeds (Fintype.card GE) lg ^ s := by
  rw [recZ_err, card_NZ_sub]
  rfl

/-- **The number of seeds of the sample map is the number of all seeds of one answer, to that
power.** -/
theorem recZ_card_all (l lg s : ℕ) :
    Fintype.card (recZ l lg s).D = allSeeds (Fintype.card GE) lg ^ s := by
  show Fintype.card (Fin s → (Fin lg → GE) × NZ) = _
  rw [Fintype.card_fun, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    card_NZ_sub]
  rfl

/-- A setting with the format's base field and the degree 3 has the extension field's number of
elements. -/
theorem cardE_card_GE (st : Setting) (hp : st.p = Fmt.Fld.two.p) (hd : st.degree = 3) :
    st.cardE = Fintype.card GE := by
  unfold Setting.cardE
  rw [hp, hd, card_GE]

/-! ## From extended non-negative reals to reals -/

/-- `kapSl 128` as a real number. -/
theorem kapSl_real : kapSl 128 = ENNReal.ofReal (1 + ((2 : ℝ) ^ 128)⁻¹) := by
  unfold kapSl
  rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
  norm_num

/-- A bias and a share of natural numbers, as a real number. -/
theorem bound_ofReal (b N M : ℕ) (hM : 0 < M) :
    kapSl 128 ^ b * ((N : ℝ≥0∞) / (M : ℝ≥0∞)) =
      ENNReal.ofReal ((1 + ((2 : ℝ) ^ 128)⁻¹) ^ b * ((N : ℝ) / (M : ℝ))) := by
  have hM' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity), ← kapSl_real,
    ENNReal.ofReal_div_of_pos hM', ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

/-! ## The bound against the price -/

/-- **THE BOUND OF `collRaw_pr` IS AT MOST THE PLANNER'S PRICE OF THE RECORD'S ROUND**:
`sampleError` at a list size `list`, the cube lg and s answers. Asked: the setting's extension field
is the format's; the library's bound on the list is at most `list`; 2 b 2^-128 list ≤ 1 for the
number b of blocks; the price is not marked bad. -/
theorem record_bound_le_price (st : Setting) (hE : st.cardE = Fintype.card GE)
    {n d eM list l lg s b : ℕ} (hL : listMax n d eM ≤ list)
    (hb : 2 * (b : ℝ) * ((2 : ℝ) ^ 128)⁻¹ * (list : ℝ) ≤ 1) (h1 : 1 ≤ list)
    (g : (sampleError st list lg s).bad = false) :
    kapSl 128 ^ b * ((((listMax n d eM).choose 2 * (recZ l lg s).err : ℕ) : ℝ≥0∞) /
        Fintype.card (recZ l lg s).D) ≤
      ENNReal.ofReal (((sampleError st list lg s).error.val : ℚ) : ℝ) := by
  have hq : 2 ≤ st.cardE := by
    rw [hE]
    exact le_trans (by norm_num) card_GE_large
  have hpos : 0 < Fintype.card (recZ l lg s).D := Fintype.card_pos
  rw [bound_ofReal b _ _ hpos, recZ_err_clash, recZ_card_all, ← hE]
  exact ENNReal.ofReal_le_ofReal
    (record_price_covers st hq hL (by positivity) hb h1 g)

/-- **So the probability of `coll_pr_bytes` is at most that price.** ONE stored table f, fixed
before the blocks; uniform blocks. -/
theorem coll_pr_bytes_price (st : Setting) (hE : st.cardE = Fintype.card GE) (T : Fmt.M1.Code)
    (v eM lg s list : ℕ) (ha : T.a ≤ 32) (hk : T.r + T.l ≤ 2 ^ T.a)
    (he : eM < 2 ^ T.a - (T.r + T.l) + 1)
    (hJ : InJohnson (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM) (h3 : 3 * s ≤ T.l)
    (hl : T.l - 3 * s ≤ 2 ^ lg)
    (hL : listMax (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM ≤ list)
    (hb : 2 * ((seedBS lg s).b : ℝ) * ((2 : ℝ) ^ 128)⁻¹ * (list : ℝ) ≤ 1) (h1 : 1 ≤ list)
    (g : (sampleError st list lg s).bad = false) (f : Fin (2 ^ T.a) → Run.PQ.SgX) :
    pr (unif (Fin (seedBS lg s).b → Dig 256))
        {u | (decRec T v eM lg s).coll f (seedOf lg s
          ((timesT (Fmt.drawSeed .two lg) s (Fmt.rowOf (blockBytes u)) 0).1.map fun x =>
            (x.1.map E.ofTriple, E.ofTriple x.2)))} ≤
      ENNReal.ofReal (((sampleError st list lg s).error.val : ℚ) : ℝ) :=
  (coll_pr_bytes T v eM lg s ha hk he hJ h3 hl f).trans
    (record_bound_le_price st hE hL hb h1 g)

/-- **The same at the sizes of OnBytes/Slice/RecordFull.lean**: 140 blocks; the radius eM and the
list size are arguments. -/
theorem coll_pr_bytes_full_price (st : Setting) (hE : st.cardE = Fintype.card GE) (eM list : ℕ)
    (he : eM < 3848273922) (hJ : InJohnson (2 ^ 32) 3848273922 eM)
    (hL : listMax (2 ^ 32) 3848273922 eM ≤ list)
    (hb : 2 * ((140 : ℕ) : ℝ) * ((2 : ℝ) ^ 128)⁻¹ * (list : ℝ) ≤ 1) (h1 : 1 ≤ list)
    (g : (sampleError st list recLg recS).bad = false) (f : Fin (2 ^ recT.a) → Run.PQ.SgX) :
    pr (unif (Fin (seedBS recLg recS).b → Dig 256))
        {u | (decRecFull eM).coll f (seedOf recLg recS
          ((timesT (Fmt.drawSeed .two recLg) recS (Fmt.rowOf (blockBytes u)) 0).1.map fun x =>
            (x.1.map E.ofTriple, E.ofTriple x.2)))} ≤
      ENNReal.ofReal (((sampleError st list recLg recS).error.val : ℚ) : ℝ) :=
  (coll_pr_bytes_full eM he hJ f).trans (record_bound_le_price st hE hL hb h1 g)

/-! ## At the list size of a table's one-time test -/

/-- **THE BOUND AGAINST THE PRICE OF THE RECORD'S ROUND OF A TABLE WITH INTEGERS**: `sampleError` at
the list size of the one-time test. The planner's k is the dimension less 1, so its n - k is the
code's own distance (`OnBytes.Params.wordOf_distance`). Asked beside the hypotheses of
`OnBytes.Params.record_round_covers`: the table's code has the sizes of T; its dimension is not 0
and at most its length; the setting has the extension field's number of elements. -/
theorem record_bound_le_round {st : Setting} {Tz : TableSize} (hE : st.cardE = Fintype.card GE)
    (T : Fmt.M1.Code) {eM l lg s b : ℕ} (ha : Tz.code.logN = T.a) (hr : Tz.code.r = T.r)
    (hl : Tz.code.ell = T.l) (h0 : 0 < Tz.code.dim) (hd : Tz.code.dim ≤ Tz.code.n)
    (hM : Tz.distances.mOnce ≠ 0) (hp : st.printed = true)
    (gc : (tableAnalysis st Tz).once.count.bad = false) (hk0 : 0 < (wordOf Tz.code).k)
    (her : (eM : ℝ) ≤ (1 - (wordOf Tz.code).agreeAt Tz.distances.mOnce true) *
      ((wordOf Tz.code).n : ℝ))
    (hb : 2 * (b : ℝ) * ((2 : ℝ) ^ 128)⁻¹ * ((tableAnalysis st Tz).once.list : ℝ) ≤ 1)
    (h1 : 1 ≤ (tableAnalysis st Tz).once.list)
    (g : (sampleError st (tableAnalysis st Tz).once.list lg s).bad = false) :
    kapSl 128 ^ b *
        ((((listMax (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM).choose 2 * (recZ l lg s).err : ℕ) :
          ℝ≥0∞) / Fintype.card (recZ l lg s).D) ≤
      ENNReal.ofReal
        (((sampleError st (tableAnalysis st Tz).once.list lg s).error.val : ℚ) : ℝ) := by
  have e1 := (tableAnalysis_fromM (s := st) hM).1
  rw [hp] at e1
  have gc' : (johnson (wordOf Tz.code) Tz.distances.mOnce true).count.bad = false := by
    rw [← e1]
    exact gc
  have hL0 : listMax (wordOf Tz.code).n ((wordOf Tz.code).n - (wordOf Tz.code).k) eM ≤
      (tableAnalysis st Tz).once.list := by
    rw [e1]
    exact listMax_le_list gc' hk0 her
  have hn : (wordOf Tz.code).n = 2 ^ T.a := by
    rw [← ha]
    rfl
  rw [wordOf_distance h0 hd, hn, ha, hr, hl] at hL0
  exact record_bound_le_price st hE hL0 hb h1 g

/-! ## At full size, closed -/

/-- The setting of the full-size lines with a record has the extension field's number of elements.
-/
theorem recordSet_card : recordSet.cardE = Fintype.card GE :=
  cardE_card_GE recordSet (by decide +kernel) (by decide +kernel)

/-- **The planner's table at the full-size lines with a record has the sizes of
OnBytes/Slice/RecordFull.lean.** -/
theorem recordTable_sizes : recordTable.code.logN = recT.a ∧ recordTable.code.ell = recT.l ∧
    recordTable.code.r = recT.r ∧ recordTable.v = recV ∧ recordTable.answers = recS ∧
    OnBytes.Params.clog2 recordTable.code.ell = recLg := by
  decide +kernel

/-- **The shape that the entry's sizes hold at these lines is the shape of
OnBytes/Slice/RecordFull.lean.** (That the port's own derivation gives these sizes at the lines
`recordLines`: `OnBytes.Params.record_first_round`.) -/
theorem recordLink_recShape : OnBytes.Params.recordLink.table = recShape := rfl

/-- **THE BOUND, AT THE SIZES OF OnBytes/Slice/RecordFull.lean AND THE RADIUS `recordRadius`, IS AT
MOST THE TYPED PRICE**: without a hypothesis. This is the right side of `coll_pr_full`,
`coll_pr_bytes_full`, `coll_pr_oracle_full` and `coll_measure_oracle_full`. By
`OnBytes.Params.record_full_covers`. -/
theorem record_bound_full_closed :
    kapSl 128 ^ 140 * ((((listMax (2 ^ 32) 3848273922 recordRadius).choose 2 *
        (recZ recT.l recLg recS).err : ℕ) : ℝ≥0∞) / Fintype.card (recZ recT.l recLg recS).D) ≤
      ENNReal.ofReal ((recordPrice.val : ℚ) : ℝ) := by
  have hpos : 0 < Fintype.card (recZ recT.l recLg recS).D := Fintype.card_pos
  rw [bound_ofReal 140 _ _ hpos, recZ_err_clash, recZ_card_all, ← recordSet_card]
  exact ENNReal.ofReal_le_ofReal record_full_covers

/-- The same in the letters in which a compiled part's judge asks it (`x3_judge_record_chalP`,
`key_judge_recordL`, `entry_judge_record`, `RecNums.price`, under OnBytes/TypedOracleCompiler/Slice/). In this
library `fr_bound` (OnBytes/Flat/EntryRecord.lean) calls it, in the letters of `recBound`. -/
theorem record_bound_full_letters :
    kapSl 128 ^ (seedBS recLg recS).b *
        ((((listMax (2 ^ recT.a) (2 ^ recT.a - (recT.r + recT.l) + 1) recordRadius).choose 2 *
          (recZ recT.l recLg recS).err : ℕ) : ℝ≥0∞) / Fintype.card (recZ recT.l recLg recS).D) ≤
      ENNReal.ofReal ((recordPrice.val : ℚ) : ℝ) := by
  have e1 : (2 : ℕ) ^ recT.a = 2 ^ 32 := rfl
  rw [seedBS_b_full, recT_dist, e1]
  exact record_bound_full_closed

/-- **AT THE SIZES OF OnBytes/Slice/RecordFull.lean AND THE RADIUS `recordRadius`, WITHOUT A
HYPOTHESIS**: for ONE stored table f, fixed before the blocks: over 140 uniform blocks, the seeds
that the expression of `recordSeeds` draws from the blocks' bytes are such that the record does not
single one table out with probability at most `OnBytes.Params.recordPrice`, a typed number; that it
is the error of the first round of the entry's plan at `recordLines`:
`OnBytes.Params.record_first_round`. The radius: the planner's distance of the one-time test times
the length, rounded down (`OnBytes.Params.rr_radius`). -/
theorem coll_pr_bytes_full_closed (f : Fin (2 ^ recT.a) → Run.PQ.SgX) :
    pr (unif (Fin (seedBS recLg recS).b → Dig 256))
        {u | (decRecFull recordRadius).coll f (seedOf recLg recS
          ((timesT (Fmt.drawSeed .two recLg) recS (Fmt.rowOf (blockBytes u)) 0).1.map fun x =>
            (x.1.map E.ofTriple, E.ofTriple x.2)))} ≤
      ENNReal.ofReal ((recordPrice.val : ℚ) : ℝ) :=
  (coll_pr_bytes_full recordRadius record_radius_inJohnson.2 record_radius_inJohnson.1 f).trans
    record_bound_full_closed

/-- **THE SAME OVER A UNIFORMLY RANDOM ORACLE**: for ONE stored table f and ONE key k, both fixed
before the oracle: the set of oracles under which the key's seeds are such that the record does not
single one table out has measure at most the typed price. -/
theorem coll_measure_oracle_full_closed (f : Fin (2 ^ recT.a) → Run.PQ.SgX)
    (k : OnBytes.Tie.IdKey) :
    Rom.U (Rom.rom 256)
        {g | ∃ ρ, seedUnder recLg recS k g = some ρ ∧ (decRecFull recordRadius).coll f ρ} ≤
      ENNReal.ofReal ((recordPrice.val : ℚ) : ℝ) :=
  (coll_measure_oracle_full recordRadius record_radius_inJohnson.2 record_radius_inJohnson.1 f
    k).trans record_bound_full_closed

end OnBytes.Slice

#print axioms OnBytes.Slice.card_ne_sub_one
#print axioms OnBytes.Slice.card_NZ_sub
#print axioms OnBytes.Slice.recZ_err_clash
#print axioms OnBytes.Slice.recZ_card_all
#print axioms OnBytes.Slice.cardE_card_GE
#print axioms OnBytes.Slice.kapSl_real
#print axioms OnBytes.Slice.bound_ofReal
#print axioms OnBytes.Slice.record_bound_le_price
#print axioms OnBytes.Slice.coll_pr_bytes_price
#print axioms OnBytes.Slice.coll_pr_bytes_full_price
#print axioms OnBytes.Slice.record_bound_le_round
#print axioms OnBytes.Slice.recordSet_card
#print axioms OnBytes.Slice.recordTable_sizes
#print axioms OnBytes.Slice.recordLink_recShape
#print axioms OnBytes.Slice.record_bound_full_closed
#print axioms OnBytes.Slice.record_bound_full_letters
#print axioms OnBytes.Slice.coll_pr_bytes_full_closed
#print axioms OnBytes.Slice.coll_measure_oracle_full_closed
