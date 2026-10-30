-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Oracle/YesNotFree.lean: beside the empty log the entry's language is not met for free: a
family of values of which it fails; so on each of them, fixed before the function is drawn, the
entry file's closed check says yes with probability at most 2^-104 (small example: 2^-105); and, for
all files that are fixed before the draw, the like bound on "the reader makes a value of the family
of them, and the check says yes on it". NO VALUE IS WRITTEN ON WHICH THESE BOUNDS DO WORK (below).

Why. The bounds of OnBytes/TypedOracleCompiler/Slice/EntryVerdictBound.lean and OnBytes/K/Oracle/VerdictOnFiles.lean
speak of the event "a yes, while the entry's language fails of two strings read off the maker's
log". If that language held of whatever is read off a log, the event would be empty and the bounds
would say nothing of any yes. OnBytes/K/Oracle/Decodes.lean shows that the language fails of some
strings written there, which nothing ties to a log. Here it is shown to fail IN THE EVENT's OWN
LETTERS, at one log: the empty one; so for the maker that asks nothing and puts out one fixed value
of the family below (`OComp.pure`: the theorems here are for that maker alone) the bounds are bounds
on the yes itself. At other values they need not be (by `dcd_words_iff`; a reading, stated here as
no theorem): where the first answers do not all read as 0 the first table of (0, no word) does not
decode with them, and where both lists read as 0 the copy is faithful: there the language holds
beside the empty log.

Main names (namespace `OnBytes.K.Oracle`; each of the last three also with Small):
  `dcd_words_iff`: at any decoder with a record whose radius is below the code's distance: a table
    of code words decodes with a record exactly if the record's answers are its own.
  `not_langE_noWord`: there the entry's language (`DecR.LangE`, OnBytes/Slice/DecoderRec.lean) fails
    of two tables of (0, no word) where the first record's answers are 0 and the second's are not,
    at all seeds.
  `rdC_nil`: off the empty log the written reading `rdC` is the table of (0, no word), under every
    root.
  `ZeroThenNot v s a`: the first table's answers in a read as 0, all of them; the further table's do
    not.
  `zeroOne n`, `zeroOne_family`, `zeroOne_fit`: a written member: n answers 0, n answers 1, roots of
    32 zero bytes, the run's value `one32` (32 bytes: a 1, then zeros: the tests reject 32 zero
    bytes), no seed, no round: it is in the family where 0 < s and 0 < n, and at a shape's number of
    answers it passes the closed check's tests on the value (`askedFit`), which are one conjunct of
    that check of two.
  `entryLangFull_fails`: for all cfg, g and every such a: `EntryLangFull cfg g a []` fails.
  `verifyEntryFull_rare`: such an a is fixed, then the function is drawn: the closed check says yes
    on a with probability at most `entryB (2⁻¹)^128 0 142 fullV 0` + 0. `…_rare_104`: at most
    2^-104.
  `verifyEntryFilesFull_rare`: five files are fixed, then the function is drawn: that the reader
    makes such a value of them and the closed check says yes on it has probability at most
    `entryB (2⁻¹)^128 41622 142 fullV 0` + 0. `…_rare_104`: at most 2^-104.

What is not claimed. THAT THE CHECK EVER SAYS YES: this file shows the other half, that it refuses;
a check that refused everything would meet all here. ONE FAMILY OF VALUES, far from honest ones: the
first table's record says "all answers 0" and the copy's says otherwise; nothing on a table that is
not 0; nothing on a maker that asks the function: off a log that holds a tree what `rdC` reads back
is not shown here. The written member has no round: it passes the tests on the value and is far from
anything that a reader returns. THE CLOSED CHECK REFUSES IT AT EVERY FUNCTION, FOR ITS FORM ALONE: a
chain of no round is typed against no description that has rounds (by `assembleS`'s text; no theorem
in this file): at it the bounds of this file do no work, and NO VALUE IS WRITTEN ON WHICH THEY DO.
By a reading, no theorem: any value that is fixed before the draw would, but for luck, be refused
for its seeds alone, which the function gives anew, whatever its answers: so at the one maker of
these theorems the bounds are not what refuses. The family also holds values that the tests refuse
outright: a list of no answers reads as 0. In the statement on files the family stands inside the
event: of which files the reader makes such a value is not said. The figures are ceilings of the
written bound at the budget 0; they count, at 6 of the 41 rounds (small: 4 of the 24), 32 of the 128
bits as proof of work; they are no level of security of any program; they rest on the statement on
codes, which is proved through Cb/Bridge/ over lean/ThirdParty/. The events are not shown
measurable, and `Rom.Pr` is a lower integral; each lies, at the one point in question, in the event
whose bound this is. THE EVENT OF THE BOUNDS IS NOT SHOWN INHABITED BY THIS: that needs a yes. All
that the heads of VerdictOnFiles.lean, EntryVerdictBound.lean and Decodes.lean do not claim. A
random function, not the format's hash. The entry file's part alone.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Oracle.VerdictOnFiles
import OnBytes.K.Oracle.DecodesAt
import OnBytes.K.Oracle.Nums

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Oracle
open Rom Prob Cb Cb.Ood Blocks OnBytes.Slice TypedOracleCompiler.Slice
open OnBytes.Tie (recordGround smallRecordGround AskedE)
open OnBytes.Slice.Shapes (Size Cfg dgOf dgOf_size pubS₀ pubS₁ zFull zSmall rdC rawBy mkZ)
open OnBytes.Slice.Shapes.FileSpec (own₀ own₁)
open scoped ENNReal

/-! ## A table of code words decodes with its own answers alone -/

section
variable (D : DecR) {d : ℕ}

/-- **A table of code words decodes with a record exactly if the record's answers are its own**, if
the radius is below the code's distance; and then to its own message parts. -/
theorem dcd_words_iff (hd : HasDist D.ix.G d) (he : D.eM < d) (f : D.toDec.Pos → Run.PQ.SgX)
    (M : D.ix.Row → D.toDec.Co → GE) (hf : ∀ r x, D.tab f r x = D.ix.G.mulVec (M r) x)
    (rec : D.Rec) (u : D.ix.Row × D.toDec.En → GE) :
    D.dcd f rec = some u ↔ u = D.ix.view M ∧ D.ix.ZR.val rec.1 (D.ix.view M) = rec.2 := by
  have hc : ¬ D.coll f rec.1 := not_coll_words D hd he f M hf rec.1
  have e : D.tab f = fun a => D.ix.G.mulVec (M a) := funext fun r => funext fun x => hf r x
  have a : ∀ M', DecodesTo D.ix.G D.eM (fun a => D.ix.G.mulVec (M a)) M' → M' = M := fun M' h =>
    funext fun _ => DecodesTo.row_unique hd (by omega : D.eM + 0 < d) h
      (decodesTo_mulVec D.ix.G 0 M) rfl
  unfold DecR.coll LdIx.Coll at hc
  unfold DecR.dcd LdIx.dec
  rw [e] at hc ⊢
  rw [ood_decMinS_good _ _ _ _ _ D.ix.G D.eM D.ix.rank D.ix.view D.ix.ZR _ rec.1 hc rec.2 u]
  constructor
  · rintro ⟨⟨M', h, rfl⟩, hy⟩
    rw [a M' h] at hy ⊢
    exact ⟨rfl, hy⟩
  · rintro ⟨rfl, hy⟩
    exact ⟨⟨M, decodesTo_mulVec D.ix.G D.eM M, rfl⟩, hy⟩

/-- The table in which every symbol is (0, no word) is the table of the code words of the messages
0. -/
theorem tab_noWord (r : D.ix.Row) (x : D.toDec.Pos) :
    D.tab (fun _ => (0, [])) r x =
      D.ix.G.mulVec ((fun _ => 0 : D.ix.Row → D.toDec.Co → GE) r) x := by
  show algebraMap GF GE (toF (([] : List UInt64).getD (Sz.rowNo r) 0)) = D.ix.G.mulVec 0 x
  rw [List.getD_nil, toF_zero, map_zero, Matrix.mulVec_zero]
  rfl

/-- The raw string of 2^a places that holds (0, no word) at each has that length. -/
theorem mkZ_hasLen (a : ℕ) (f : ℕ → Option Run.PQ.SgX) : Raw.HasLen (mkZ a f) (2 ^ a) := by
  intro j
  unfold mkZ
  by_cases hj : j < 2 ^ a
  · rw [if_pos hj]
    exact ⟨fun h => (by cases h), fun h => absurd hj (Nat.not_lt.2 h)⟩
  · rw [if_neg hj]
    exact ⟨fun _ => Nat.not_lt.1 hj, fun _ => rfl⟩

/-- What the decoder reads of it. -/
theorem mkZ_none_sym (a : ℕ) (j : ℕ) :
    ((mkZ a fun _ => none) j).getD ((0, []) : Run.PQ.SgX) = (0, []) := by
  unfold mkZ
  by_cases hj : j < 2 ^ a
  · rw [if_pos hj]
    rfl
  · rw [if_neg hj]
    rfl

/-- **THE ENTRY's LANGUAGE FAILS OF TWO TABLES OF (0, no word), WHERE THE FIRST RECORD's ANSWERS ARE
0 AND THE SECOND's ARE NOT**, at all seeds, if the radius is below the code's distance: the first
decodes, to the messages 0, and its record singles it out; the second does not decode with answers
that are not its own. -/
theorem not_langE_noWord (hd : HasDist D.ix.G d) (he : D.eM < d) (ρ₀ ρ₁ : D.Z.D)
    (y₁ : D.ix.ZR.S → GE) (hy : y₁ ≠ fun _ => 0) :
    ¬ DecR.LangE (DecR.wayColl D) (ρ₀, fun _ => 0) (ρ₁, y₁) (mkZ D.T.a fun _ => none)
      (mkZ D.T.a fun _ => none) := by
  have hz : ∀ ρ : D.Z.D, D.ix.ZR.val ρ (D.ix.view fun _ => 0) = fun _ => 0 := fun ρ => by
    funext s
    unfold Sample.val
    simp [LdIx.view]
  have hraw : ∀ rec : D.Rec, D.dcdRaw (mkZ D.T.a fun _ => none) rec =
      D.dcd (fun _ => (0, [])) rec := fun rec => by
    unfold DecR.dcdRaw
    rw [if_pos (mkZ_hasLen D.T.a _)]
    exact congrArg (fun f => D.dcd f rec) (funext fun p => mkZ_none_sym D.T.a p.val)
  rintro (h | h | ⟨u₀, u₁, -, h1, -, -⟩)
  · rw [hraw, (dcd_words_iff D hd he _ _ (tab_noWord D) (ρ₀, fun _ => 0) _).2 ⟨rfl, hz ρ₀⟩] at h
    cases h
  · have h2 : D.coll (fun p => ((mkZ D.T.a fun _ => none) p.val).getD (0, [])) ρ₀ := h.2
    rw [show (fun p : D.toDec.Pos => ((mkZ D.T.a fun _ => none) p.val).getD
      ((0, []) : Run.PQ.SgX)) = fun _ => (0, []) from funext fun p => mkZ_none_sym D.T.a p.val]
      at h2
    exact not_coll_words D hd he _ _ (tab_noWord D) ρ₀ h2
  · rw [hraw] at h1
    exact hy (((dcd_words_iff D hd he _ _ (tab_noWord D) (ρ₁, y₁) u₁).1 h1).2.symm.trans (hz ρ₁))

end

/-! ## What is read off the empty log -/

/-- In the empty log a walk finds nothing. -/
theorem walk_nil {Lf : Type} (k : Look 256 Lf) {t : Merkle.Shape} (p : t.Pos)
    (c : _root_.Iop.Dig 256) : k.walk [] p c = none := by
  cases p <;> rfl

/-- **Off the empty log the written reading is the table of (0, no word)**, under every root. -/
theorem rdC_nil (z : Size) (cfg : Cfg) (T₀ T₁ : Tab) (cm : _root_.Iop.Dig 256) :
    rdC z cfg T₀ T₁ [] cm = mkZ z.T.a fun _ => none := by
  show rawBy (dgOf cfg T₀) z.T.a z.shape.saltBytes [] cm = _
  unfold rawBy
  rw [if_pos (dgOf_size cfg T₀)]
  exact congrArg (mkZ z.T.a) (funext fun j => walk_nil _ _ cm)

/-! ## At the two sizes -/

/-- The first table's answers in a read as 0, all of them, and the further table's do not. -/
def ZeroThenNot (v s : ℕ) (a : AskedE) : Prop :=
  anT v s (a.first.answers.map E.triple) = (fun _ => 0) ∧
    anT v s (a.further.answers.map E.triple) ≠ fun _ => 0

/-! ## A written member of the family -/

/-- 32 bytes: a 1, then 31 zeros. -/
def one32 : ByteArray := ByteArray.mk #[1] ++ Fmt.zeroBytes 31

theorem one32_size : one32.size = 32 := by decide

/-- It is not 32 zero bytes. -/
theorem one32_ok : _root_.Fmt.runOk one32 = true := by decide

/-- A written value: n answers 0 in the first table, n answers 1 in the further one; both roots are
32 zero bytes, the run's value is `one32`; no seed, no round. -/
def zeroOne (n : ℕ) : AskedE where
  first := ⟨Fmt.zero32, List.replicate n ⟨0, 0, 0⟩⟩
  further := ⟨Fmt.zero32, List.replicate n ⟨1, 0, 0⟩⟩
  l0 := []
  l1 := []
  out := ⟨ByteArray.empty, some one32, ByteArray.empty, ByteArray.empty, [], #[]⟩

/-- It is in the family, where there is an answer at all. -/
theorem zeroOne_family (v s n : ℕ) (hs : 0 < s) (hn : 0 < n) : ZeroThenNot v s (zeroOne n) := by
  constructor
  · funext x
    show toE ((List.map E.triple (List.replicate n ⟨0, 0, 0⟩)).getD _ (0, 0, 0)) = 0
    rw [List.map_replicate]
    show toE ((List.replicate n ((0, 0, 0) : Fmt.Ext3)).getD _ (0, 0, 0)) = 0
    rw [getD_copies]
    exact toE_zeroE
  · intro h
    have h' := congrFun h (fun _ => false, ⟨0, hs⟩)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have e : anT v s ((zeroOne (m + 1)).further.answers.map E.triple) (fun _ => false, ⟨0, hs⟩) =
        toE Fmt.Fld.oneE := by
      show toE ((List.map E.triple (List.replicate (m + 1) ⟨1, 0, 0⟩)).getD
        (Sz.rowNo (fun _ : Fin v => false) * s + 0) (0, 0, 0)) = _
      rw [rowNo_false, Nat.zero_mul, List.replicate_succ]
      rfl
    rw [e, toE_oneE] at h'
    exact one_ne_zero h'

/-- At the shape's number of answers it passes the closed check's tests on the value. -/
theorem zeroOne_fit (sh : Params.IndexShape) :
    askedFit sh (zeroOne (2 ^ sh.v * sh.answers)) = true := by
  unfold askedFit
  have hW : askedWords (zeroOne (2 ^ sh.v * sh.answers)) = true := rfl
  have hS : ((zeroOne (2 ^ sh.v * sh.answers)).out.rounds.toList.all fun ro => ro.opens.all fun y =>
      y.2.2.salts.all fun s => s.size == sh.saltBytes) = true := rfl
  have hZ : (zeroOne (2 ^ sh.v * sh.answers)).out.run.all _root_.Fmt.runOk = true := one32_ok
  have hrun : (zeroOne (2 ^ sh.v * sh.answers)).out.run = some one32 := rfl
  rw [hW, hS, hZ]
  simp only [Bool.true_and, hrun, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨(fun _ h => by cases h), (show Fmt.zero32.size = 32 by decide)⟩,
    (show Fmt.zero32.size = 32 by decide)⟩, List.length_replicate⟩, List.length_replicate⟩,
    (fun x hx => by rw [List.eq_of_mem_replicate hx]; decide)⟩,
    (fun x hx => by rw [List.eq_of_mem_replicate hx]; decide)⟩, one32_size⟩

/-! ## Beside the empty log the language fails of the family -/

/-- **At the full size: beside the empty log the entry's language fails of every such value**, at
all public files, every function, all roots and seeds. -/
theorem entryLangFull_fails (cfg : Cfg) (g : Fam (rom 256)) (a : AskedE)
    (h : ZeroThenNot zFull.v zFull.s a) : ¬ EntryLangFull cfg g a [] := by
  unfold EntryLangFull
  rw [rdC_nil, rdC_nil]
  have e : anT zFull.v zFull.s (xOfAskedC zFull.lg zFull.s a).1.1 = fun _ => 0 := h.1
  rw [e]
  exact not_langE_noWord (decRec zFull.T zFull.v zFull.eM zFull.lg zFull.s) full_dist.1
    full_dist.2 _ _ _ h.2

/-- The same at the small example. -/
theorem entryLangSmall_fails (cfg : Cfg) (g : Fam (rom 256)) (a : AskedE)
    (h : ZeroThenNot zSmall.v zSmall.s a) : ¬ EntryLangSmall cfg g a [] := by
  unfold EntryLangSmall
  rw [rdC_nil, rdC_nil]
  have e : anT zSmall.v zSmall.s (xOfAskedC zSmall.lg zSmall.s a).1.1 = fun _ => 0 := h.1
  rw [e]
  exact not_langE_noWord (decRec zSmall.T zSmall.v zSmall.eM zSmall.lg zSmall.s) small_dist.1
    small_dist.2 _ _ _ h.2

/-! ## So a yes on such a value is rare -/

/-- For an algorithm that only returns x: an event that holds x wherever another does is at least as
likely. -/
theorem Pr_pure_mono {α : Type} (x : α) {E F : Fam (rom 256) → Set α}
    (h : ∀ f, x ∈ E f → x ∈ F f) :
    Rom.Pr (OComp.pure x : OComp (rom 256) α) E ≤ Rom.Pr (OComp.pure x : OComp (rom 256) α) F := by
  unfold Rom.Pr
  refine MeasureTheory.lintegral_mono fun f => ?_
  unfold Rom.PrCoins
  simp only [OComp.runEager, Prob.pr_pure]
  by_cases hx : x ∈ E f
  · rw [if_pos hx, if_pos (h f hx)]
  · rw [if_neg hx]
    exact zero_le _

/-- **On the family the bound is a bound on the yes itself, at the full size.** A value a whose
first answers read as 0 and whose further answers do not is fixed first; then the function is drawn.
The closed check says yes on a with probability at most `entryB (2⁻¹)^128 0 142 fullV 0` + 0. No
value is written on which this does work (the head). -/
theorem verifyEntryFull_rare (cfg : Cfg) (a : AskedE) (h : ZeroThenNot zFull.v zFull.s a) :
    Rom.Pr (OComp.pure (a, []) : OComp (rom 256) (AskedE × Trace (rom 256)))
        (fun g => {y | verifyEntryFull cfg y.1 g = true}) ≤
      entryB (((2 : ℝ≥0∞)⁻¹) ^ 128) 0 142 fullV 0 + ((0 ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  le_trans (Pr_pure_mono (F := EntryFailFull cfg) (a, []) fun g hy =>
      (entryFailFull_iff cfg g a []).2 ⟨hy, entryLangFull_fails cfg g a h⟩)
    (verifyEntryFull_copyBound cfg (OComp.pure a) 0 trivial)

/-- The same at the small example. -/
theorem verifyEntrySmall_rare (cfg : Cfg) (a : AskedE) (h : ZeroThenNot zSmall.v zSmall.s a) :
    Rom.Pr (OComp.pure (a, []) : OComp (rom 256) (AskedE × Trace (rom 256)))
        (fun g => {y | verifyEntrySmall cfg y.1 g = true}) ≤
      entryB (((2 : ℝ≥0∞)⁻¹) ^ 128) 0 101 smallV 0 + ((0 ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  le_trans (Pr_pure_mono (F := EntryFailSmall cfg) (a, []) fun g hy =>
      (entryFailSmall_iff cfg g a []).2 ⟨hy, entryLangSmall_fails cfg g a h⟩)
    (verifyEntrySmall_copyBound cfg (OComp.pure a) 0 trivial)

/-- **The like for "read, then check", at the full size.** Five files d are fixed first; then the
function is drawn. That the reader makes of d a value whose first answers read as 0 and whose
further answers do not, and the closed check says yes on it, has probability at most
`entryB (2⁻¹)^128 41622 142 fullV 0` + 0. -/
theorem verifyEntryFilesFull_rare (cfg : Cfg) (d : Slice.Shapes.Files) :
    Rom.Pr (OComp.pure (d, []) : OComp (rom 256) (Slice.Shapes.Files × Trace (rom 256)))
        (fun g => {x | ∃ a, readEntry recordGround cfg g x.1 = some a ∧
          verifyEntryFull cfg a g = true ∧ ZeroThenNot zFull.v zFull.s a}) ≤
      entryB (((2 : ℝ≥0∞)⁻¹) ^ 128) 41622 142 fullV 0 + ((0 ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  le_trans (Pr_pure_mono (F := EntryFailFilesFull cfg) (d, []) fun g ⟨a, ha, hy, hz⟩ =>
      ⟨a, ha, (entryFailFull_iff cfg g a []).2 ⟨hy, entryLangFull_fails cfg g a hz⟩⟩)
    (verifyEntryFilesFull_copyBound cfg (OComp.pure d) 0 trivial)

/-- The same at the small example. -/
theorem verifyEntryFilesSmall_rare (cfg : Cfg) (d : Slice.Shapes.Files) :
    Rom.Pr (OComp.pure (d, []) : OComp (rom 256) (Slice.Shapes.Files × Trace (rom 256)))
        (fun g => {x | ∃ a, readEntry smallRecordGround cfg g x.1 = some a ∧
          verifyEntrySmall cfg a g = true ∧ ZeroThenNot zSmall.v zSmall.s a}) ≤
      entryB (((2 : ℝ≥0∞)⁻¹) ^ 128) 26222 101 smallV 0 + ((0 ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 :=
  le_trans (Pr_pure_mono (F := EntryFailFilesSmall cfg) (d, []) fun g ⟨a, ha, hy, hz⟩ =>
      ⟨a, ha, (entryFailSmall_iff cfg g a []).2 ⟨hy, entryLangSmall_fails cfg g a hz⟩⟩)
    (verifyEntryFilesSmall_copyBound cfg (OComp.pure d) 0 trivial)

/-- A ceiling of that bound: at most 2^-104. -/
theorem verifyEntryFull_rare_104 (cfg : Cfg) (a : AskedE) (h : ZeroThenNot zFull.v zFull.s a) :
    Rom.Pr (OComp.pure (a, []) : OComp (rom 256) (AskedE × Trace (rom 256)))
        (fun g => {y | verifyEntryFull cfg y.1 g = true}) ≤ ((2 : ℝ≥0∞)⁻¹) ^ 104 := by
  refine le_trans (verifyEntryFull_rare cfg a h) ?_
  rw [fullV_eq]
  exact entryB_le 0 142 13545 0 0 (0 + 13545 * 142) 104 (by norm_num) le_rfl le_rfl
    (by norm_num)

/-- A ceiling of that bound: at most 2^-105. -/
theorem verifyEntrySmall_rare_105 (cfg : Cfg) (a : AskedE) (h : ZeroThenNot zSmall.v zSmall.s a) :
    Rom.Pr (OComp.pure (a, []) : OComp (rom 256) (AskedE × Trace (rom 256)))
        (fun g => {y | verifyEntrySmall cfg y.1 g = true}) ≤ ((2 : ℝ≥0∞)⁻¹) ^ 105 := by
  refine le_trans (verifyEntrySmall_rare cfg a h) ?_
  rw [smallV_eq]
  exact entryB_le 0 101 7975 0 0 (0 + 7975 * 101) 105 (by norm_num) le_rfl le_rfl
    (by norm_num)

/-- A ceiling of that bound: at most 2^-104. -/
theorem verifyEntryFilesFull_rare_104 (cfg : Cfg) (d : Slice.Shapes.Files) :
    Rom.Pr (OComp.pure (d, []) : OComp (rom 256) (Slice.Shapes.Files × Trace (rom 256)))
        (fun g => {x | ∃ a, readEntry recordGround cfg g x.1 = some a ∧
          verifyEntryFull cfg a g = true ∧ ZeroThenNot zFull.v zFull.s a}) ≤
      ((2 : ℝ≥0∞)⁻¹) ^ 104 := by
  refine le_trans (verifyEntryFilesFull_rare cfg d) ?_
  rw [fullV_eq]
  exact entryB_le 41622 142 13545 0 0 (41622 + 13545 * 142) 104 (by norm_num) le_rfl le_rfl
    (by norm_num)

/-- A ceiling of that bound: at most 2^-105. -/
theorem verifyEntryFilesSmall_rare_105 (cfg : Cfg) (d : Slice.Shapes.Files) :
    Rom.Pr (OComp.pure (d, []) : OComp (rom 256) (Slice.Shapes.Files × Trace (rom 256)))
        (fun g => {x | ∃ a, readEntry smallRecordGround cfg g x.1 = some a ∧
          verifyEntrySmall cfg a g = true ∧ ZeroThenNot zSmall.v zSmall.s a}) ≤
      ((2 : ℝ≥0∞)⁻¹) ^ 105 := by
  refine le_trans (verifyEntryFilesSmall_rare cfg d) ?_
  rw [smallV_eq]
  exact entryB_le 26222 101 7975 0 0 (26222 + 7975 * 101) 105 (by norm_num) le_rfl le_rfl
    (by norm_num)

end OnBytes.K.Oracle

#print axioms OnBytes.K.Oracle.dcd_words_iff
#print axioms OnBytes.K.Oracle.not_langE_noWord
#print axioms OnBytes.K.Oracle.rdC_nil
#print axioms OnBytes.K.Oracle.zeroOne_family
#print axioms OnBytes.K.Oracle.one32_ok
#print axioms OnBytes.K.Oracle.zeroOne_fit
#print axioms OnBytes.K.Oracle.entryLangFull_fails
#print axioms OnBytes.K.Oracle.entryLangSmall_fails
#print axioms OnBytes.K.Oracle.verifyEntryFull_rare
#print axioms OnBytes.K.Oracle.verifyEntrySmall_rare
#print axioms OnBytes.K.Oracle.verifyEntryFilesFull_rare
#print axioms OnBytes.K.Oracle.verifyEntryFilesSmall_rare
#print axioms OnBytes.K.Oracle.verifyEntryFull_rare_104
#print axioms OnBytes.K.Oracle.verifyEntrySmall_rare_105
#print axioms OnBytes.K.Oracle.verifyEntryFilesFull_rare_104
#print axioms OnBytes.K.Oracle.verifyEntryFilesSmall_rare_105
