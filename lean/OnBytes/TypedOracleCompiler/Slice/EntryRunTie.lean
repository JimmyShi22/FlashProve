-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryRunTie.lean: THE RUN'S "YES" IS A SENTENCE ON THE CHECKER OF WHICH THE BOUND
SPEAKS. The run's function on a typed value (`whyOutE`, OnBytes/TypedOracleCompiler/Slice/EntryRunMain.lean: "YES",
or the stage that refuses) is tied to the run of the judge of the entry's part, to the checker
"pre-process by a converter, then the compiled verifier" (OnBytes/TypedOracleCompiler/Slice/EntryHome.lean; a
converter that knows of the oracle the configuration's digest alone: `HomeData.ConvC`, `convOf`,
OnBytes/TypedOracleCompiler/Slice/EntryHomeRun.lean), and, at the oracle made from the format's hash, to the family
of typed oracle functions that a run can evaluate (OnBytes/TypedOracleCompiler/Slice/EntryRunTop.lean).

Main definition.
 `HomeData.PinsAt sh c pd`   the pins that a run computes off the description are the pins of the
                        part at written terms, at a digest c: 5 equations.
Main theorems.
 `whyOutE_iff_F`        the run's function says "YES" exactly if the value has two roots and
                        `judgeRunELF` (OnBytes/TypedOracleCompiler/Slice/EntryRunForm.lean) is true.
 `atPage_why`, `HomeData.at_why`   so exactly if it has two roots and the judge's run says yes under
                        F: at the part at the page; at the part at written terms, at any two tables.
                        Every F, every output.
 `HomeData.chk_iff_why` THE CHECKER RETURNS o UNDER g EXACTLY IF THE CONVERTER MAKES o OF THE FILES
                        AND THE RUN'S FUNCTION SAYS "YES" ON o under the family read out of g
                        through the page. Every converter, every oracle, all files.
 `HomeData.famOf_at`    where the pins agree, the family that a run evaluates (`EntryRunTop.famOf`)
                        is the family read out of the oracle made from the format's hash through the
                        part's page.
 `HomeData.yes_of_run`  THE RUN'S "YES" IS A YES OF THAT CHECKER AT THAT ORACLE, WITH THE SAME
                        STATEMENT (the two roots, both tables' answers): if the digest c that the
                        run has computed is the digest that the oracle's own first table holds, the
                        pins agree at c, the converter makes o of the files at c, and the run's
                        function says "YES" on o under the family that the run evaluates.
 `HomeData.pd_own₁`, `HomeData.yes_of_run_files`   the value that the oracle's own second table
                        holds at the string of the parameter bytes is the pin that a run computes;
                        THE SAME AT THE DIGEST OF THE THREE CONFIGURATION FILES, with both
                        hypotheses on digests paid.

THE TWO HYPOTHESES ON DIGESTS ARE PAID in `HomeData.yes_of_run_files`, at the digest of the three
configuration files: the first by `dgOf_own₀`, the second by `HomeData.pd_own₁`, which goes by
`own₁_at` (both OnBytes/TypedOracleCompiler/Slice/ShapesPub.lean) and asks that the parameter bytes are the
description's; each under a bound on sizes.

Not claimed. THAT THE HYPOTHESES OF `yes_of_run` ARE MET AT ANY DATA: no instance of `HomeData`, no
converter, no shape is given here; the five equations are hypotheses. They are given and met in
OnBytes/TypedOracleCompiler/Slice/EntryRunPlay.lean, at a variable digest; `yes_of_run_files` is the same at the
digest of the files, for a reader, and is called by nothing. That a program's printed word is
`whyOutE`'s value: a program may print more behind it. That a "YES" has ever been seen. What a
refusal's name says. ONE WAY at the last theorems: from the run's yes to the checker's; both ways:
`HomeData.run_iff_checker` (OnBytes/TypedOracleCompiler/Slice/EntryRunAny.lean). A yes of the checker says nothing
by itself: what it is worth is what the bound says, under that bound's own hypotheses, over a
uniformly random oracle, not at a fixed hash. NOTHING ON SOUNDNESS IS SHOWN HERE.
`HomeData.chk_eq_run_oBits` (EntryHomeRun.lean) says the checker's value at that oracle as an
equation, with the family read out through the page; what is added here is the run's own function
and the family that a run evaluates. What the heads of EntryRunMain.lean, EntryRunForm.lean,
EntryHome.lean, EntryHomeRun.lean and EntryRunTop.lean do not claim. The compiler under OnBytes/TypedOracleCompiler/
is the one that `innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryRunMain
import OnBytes.TypedOracleCompiler.Slice.EntryHomeRun

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (SgX View)
open TypedOracleCompiler.Run.PQ (XD bodyS)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open OnBytes.Slice (decRec GE NZ seedEntry seedOfDrawnC Tab s0Of)
open OnBytes.Slice.Shapes (Files FileSpec Size Cfg dgOf dgOf_size pubS₀ pubS₁)
open OnBytes.Slice.Shapes.FileSpec (own₀ own₁)
open scoped ENNReal

/-! ## The run's function says "YES" exactly if there are two roots and the judge's run says yes -/

section
variable {lg s : ℕ} [DecidableEq (Sd1 lg s)] (D : XD) (hok : TypedOracleCompiler.Run.PQ.ok D.base = true)
  (d₁ : Sd1 lg s) (dec : XE AnsT lg s → View → Bool)
  (F : Fam (typedOracleFamily 256 (D.K + 1)
    (LXE (Bd := List Bool) D (earlyTwo (A := AnsT × AnsT) d₁) (TSE D (seedEntry lg s)))))

/-- THE RUN'S FUNCTION ON A TYPED VALUE SAYS "YES" EXACTLY IF THE VALUE HAS TWO ROOTS AND THE
JUDGE'S RUN, AS A TRUTH VALUE, IS TRUE. `whyOutE`: OnBytes/TypedOracleCompiler/Slice/EntryRunMain.lean;
`judgeRunELF`: OnBytes/TypedOracleCompiler/Slice/EntryRunForm.lean. -/
theorem whyOutE_iff_F
    (o : List (Dig 256) × XE AnsT lg s × OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto (LinkX D dec))) :
    whyOutE D hok d₁ dec F o.1 o.2.1 (toPS D dec o.2.2) = "YES" ↔
      o.1.length = 2 ∧
        judgeRunELF D dec (bodyS D.a D.base.plan.salt) (ownES D hok) (earlyTwo d₁)
          (seedEntry lg s) (seedOfDrawnC lg s) F o = true := by
  rw [whyOutE_yes]
  unfold judgeRunELF
  rw [Bool.and_eq_true]
  constructor
  · rintro ⟨h2, hc, hl⟩
    have ht : o.1.take 2 = o.1 := List.take_of_length_le (le_of_eq h2)
    exact ⟨h2, by rw [ht]; exact hc, hl⟩
  · rintro ⟨h2, hc, hl⟩
    have ht : o.1.take 2 = o.1 := List.take_of_length_le (le_of_eq h2)
    exact ⟨h2, by rw [ht] at hc; exact hc, hl⟩

end

/-! ## At the entry's part at the page -/

section
variable {lg s : ℕ} [DecidableEq (Sd1 lg s)] {d₁ : Sd1 lg s} (D : XD)
  (hok : TypedOracleCompiler.Run.PQ.ok D.base = true) (dec : XE (List T3) lg s → View → Bool)
  (R : Reading (EntryFill.Ls D d₁) (bodyS D.a D.base.plan.salt).embE)
  (rts : Files → List (Dig 256)) (cfg : ByteArray) (hcfg : cfg.size = 32) (pd : Dig 256)
  (rest : ByteArray) (n : ℕ) (back : StrCode (AllPts 256 (D.K + 1) (EntryFill.Ls D d₁)))
  (T : _root_.Fmt.M1.Code) (v eM : ℕ)
  (an : List T3 → (decRec T v eM lg s).ix.Row × (decRec T v eM lg s).Z.S → GE) (εs : ℝ≥0∞)

/-- THE RUN'S "YES" IS A SENTENCE ON THE JUDGE OF THE ENTRY'S PART: at the part at the page,
with bodies that are strings (`EntryClean.atPage`, OnBytes/TypedOracleCompiler/Slice/EntryClean.lean), under every
family F of oracle functions and for every output: the run's function says "YES" exactly if the
output has two roots and the judge's run on it says yes under F. -/
theorem atPage_why
    (F : Fam (typedOracleFamily 256 (D.K + 1) (EntryFill.Ls D d₁)))
    (o : OutE (EntryClean.atPage D (bodyS D.a D.base.plan.salt) (ownES D hok) dec R rts cfg hcfg pd
      rest n back).Z) :
    whyOutE D hok d₁ dec F o.1 o.2.1 (toPS D dec o.2.2) = "YES" ↔
      o.1.length = 2 ∧
        (((EntryClean.atPage D (bodyS D.a D.base.plan.salt) (ownES D hok) dec R rts cfg hcfg pd
          rest n back).base T v eM an εs).J.run o).det F = true := by
  have e := EntryAt.run_eq T v eM an (EntryClean.atPage D (bodyS D.a D.base.plan.salt)
    (ownES D hok) dec R rts cfg hcfg pd rest n back) εs F o
  exact (whyOutE_iff_F D hok d₁ dec F o).trans
    ⟨fun h => ⟨h.1, e.trans h.2⟩, fun h => ⟨h.1, e.symm.trans h.2⟩⟩

end

/-! ## At the checker of which the bound speaks -/

namespace HomeData
variable {z : Size} {d₁ : Sd1 z.lg z.s} [DecidableEq (Sd1 z.lg z.s)] (H : HomeData z d₁)
  (cfg : Cfg)

/-- AT THE ENTRY'S PART AT WRITTEN TERMS (`HomeData.at`, OnBytes/TypedOracleCompiler/Slice/EntryHome.lean), at
any two tables, under every family F and for every output: the run's function says "YES" exactly if
the output has two roots and the judge's run on it says yes under F. -/
theorem at_why (conv : H.Conv cfg) (εs : ℝ≥0∞) (T₀ T₁ : Tab)
    (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 ((H.DX (dgOf cfg T₀)).K + 1)
      (EntryFill.Ls (H.DX (dgOf cfg T₀)) d₁)))
    (o : H.Out cfg T₀ T₁) :
    whyOutE (H.DX (dgOf cfg T₀)) (H.ok _ (dgOf_size cfg T₀)) d₁ (H.dec (dgOf cfg T₀)) F o.1 o.2.1
        (toPS _ _ o.2.2) = "YES" ↔
      o.1.length = 2 ∧
        (((H.at cfg conv T₀ T₁).base z.T z.v z.eM (anT z.v z.s) εs).J.run o).det F = true := by
  have e := EntryAt.run_eq z.T z.v z.eM (anT z.v z.s) (H.at cfg conv T₀ T₁) εs F o
  exact (whyOutE_iff_F (H.DX (dgOf cfg T₀)) (H.ok _ (dgOf_size cfg T₀)) d₁ (H.dec (dgOf cfg T₀)) F
    o).trans ⟨fun h => ⟨h.1, e.trans h.2⟩, fun h => ⟨h.1, e.symm.trans h.2⟩⟩

/-- THE CHECKER OF WHICH THE BOUND SPEAKS RETURNS o UNDER g EXACTLY IF THE CONVERTER MAKES o OF
THE FILES AND THE RUN'S FUNCTION SAYS "YES" ON o, under the family that is read out of g through
the page; all at g's own values at the public strings. For every converter, every oracle, all files.
-/
theorem chk_iff_why (conv : H.Conv cfg) (εs : ℝ≥0∞) (Bk : ℕ) (g : Fam (rom 256)) (d : Files)
    (o : H.Out cfg (own₀ (pubS₀ cfg) g) (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g)) :
    (((H.spec cfg conv εs Bk).toO (pubS₀ cfg) (pubS₁ [H.prm] cfg) (own₀ (pubS₀ cfg) g)
      (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g)).chk d).det g = some o ↔
      conv (own₀ (pubS₀ cfg) g) (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g) d = some o ∧
        whyOutE (H.DX (dgOf cfg (own₀ (pubS₀ cfg) g)))
          (H.ok _ (dgOf_size cfg (own₀ (pubS₀ cfg) g))) d₁
          (H.dec (dgOf cfg (own₀ (pubS₀ cfg) g)))
          (readBlocks (H.at cfg conv (own₀ (pubS₀ cfg) g)
            (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g)).m g) o.1 o.2.1
          (toPS _ _ o.2.2) = "YES" := by
  have hw := fun o' => H.at_why cfg conv εs (own₀ (pubS₀ cfg) g)
    (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g)
    (readBlocks (H.at cfg conv (own₀ (pubS₀ cfg) g)
      (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g)).m g) o'
  rw [chk_eq_run]
  unfold conv2
  cases hc : conv (own₀ (pubS₀ cfg) g) (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g) d with
  | none =>
    constructor
    · intro h
      cases h
    · rintro ⟨h, -⟩
      cases h
  | some o' =>
    by_cases h2 : o'.1.length = 2
    · rw [Option.filter_some, if_pos (decide_eq_true h2)]
      show (if _ = true then some o' else none) = some o ↔ _
      constructor
      · intro h
        split_ifs at h with hr
        obtain rfl := Option.some.inj h
        exact ⟨rfl, (hw o').2 ⟨h2, hr⟩⟩
      · rintro ⟨h, hy⟩
        obtain rfl := Option.some.inj h
        exact if_pos ((hw o').1 hy).2
    · rw [Option.filter_some, if_neg (by rw [decide_eq_true_iff]; exact h2)]
      constructor
      · intro h
        cases h
      · rintro ⟨h, hy⟩
        obtain rfl := Option.some.inj h
        exact absurd ((hw o').1 hy).1 h2

/-! ## At the oracle made from the format's hash, with the page's family that a run can evaluate -/

/-- The entry's page does not hang on how its arguments are written. -/
theorem pageForE_congr {lg s : ℕ} (D : XD) (d₁ : Sd1 lg s) {c c' : ByteArray} (hc : c = c')
    (h : c.size = 32) (h' : c'.size = 32) {pd pd' : Dig 256} (hp : pd = pd')
    {r r' : ByteArray} (hr : r = r') {n n' : ℕ} (hn : n = n')
    {b b' : StrCode (AllPts 256 (D.K + 1) (EntryFill.Ls D d₁))} (hb : b = b') :
    EntryFill.pageForE D d₁ c h pd r n b = EntryFill.pageForE D d₁ c' h' pd' r' n' b' := by
  subst hc hp hr hn hb
  rfl

/-- THE PINS THAT A RUN COMPUTES OFF THE DESCRIPTION ARE THE PINS OF THE PART AT WRITTEN TERMS,
at a digest c and a table's shape sh: five equations. pd: the value that the second table holds at
the string of the parameter bytes. -/
structure PinsAt (sh : OnBytes.Params.IndexShape) (c : ByteArray) (pd : Dig 256) : Prop where
  /-- the description holds the digest -/
  cfgIs : (H.DX c).base.cfg = c
  /-- the second table's value is the format's digest of the description's parameter bytes -/
  pdIs : pd = EntryRunTop.pdOf (H.DX c)
  /-- what stands behind a root in a table's name -/
  restIs : TypedOracleCompiler.Run.FirstName.restOf c z.T.a z.T.l z.T.r z.v z.s z.shape.saltBytes =
    EntryRunTop.restAt (H.DX c) sh
  /-- the sizes' length of a salt is the plan's -/
  saltIs : z.shape.saltBytes = (H.DX c).base.plan.salt
  /-- the code behind the escape -/
  backIs : H.back c = EntryRunTop.backOf (H.DX c) d₁

/-- THEN THE FAMILY THAT A RUN EVALUATES IS THE FAMILY THAT IS READ OUT OF THE ORACLE MADE FROM
THE FORMAT'S HASH THROUGH THE PART'S PAGE (`EntryRunTop.famOf`, `famOf_eq`,
OnBytes/TypedOracleCompiler/Slice/EntryRunTop.lean). -/
theorem famOf_at (conv : H.Conv cfg) (sh : OnBytes.Params.IndexShape) (T₀ T₁ : Tab)
    (hp : H.PinsAt sh (dgOf cfg T₀) (T₁ (s0Of (H.prm (dgOf cfg T₀)))))
    (hcfg : (H.DX (dgOf cfg T₀)).base.cfg.size = 32) :
    EntryRunTop.famOf (H.DX (dgOf cfg T₀)) hcfg d₁ sh =
      readBlocks (H.at cfg conv T₀ T₁).m _root_.Run.oBits := by
  rw [EntryRunTop.famOf_eq (H.DX (dgOf cfg T₀)) (H.ok _ (dgOf_size cfg T₀)) hcfg d₁ sh
    (H.dec (dgOf cfg T₀))]
  congr 1
  show EntryFillRun.pageRunE _ _ _ _ _ _ _ _ = EntryFill.pageForE _ _ _ _ _ _ _ _
  rw [EntryFillRun.pageRunE_eq]
  exact pageForE_congr _ d₁ hp.cfgIs _ _ hp.pdIs.symm hp.restIs.symm
    (congrArg (8 * ·) hp.saltIs.symm) hp.backIs.symm

set_option maxRecDepth 20000 in
/-- THE RUN'S "YES" IS A YES OF THE CHECKER OF WHICH THE BOUND SPEAKS, AT THE ORACLE MADE FROM THE
FORMAT'S HASH, WITH THE SAME STATEMENT. c: the digest that the run has computed off the three
configuration files. IF c is the digest that the oracle's own first table holds, the pins agree at
c, the converter makes o of the files at c, and the run's function says "YES" on o under the family
that the run evaluates, THEN the checker (pre-process by that converter, then the compiled verifier)
returns a value on these files under that oracle, AND THE STATEMENT IN THAT VALUE (`HomeData.stmt`,
OnBytes/TypedOracleCompiler/Slice/EntryHomeRun.lean: the two roots, both tables' answers) IS o's. -/
theorem yes_of_run (convC : H.ConvC) (sh : OnBytes.Params.IndexShape)
    (εs : ℝ≥0∞) (Bk : ℕ) (d : Files) (c : ByteArray) (h32 : c.size = 32)
    (hc : c = dgOf cfg (own₀ (pubS₀ cfg) _root_.Run.oBits))
    (hp : H.PinsAt sh c (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) _root_.Run.oBits
      (s0Of (H.prm c))))
    (hcfg : (H.DX c).base.cfg.size = 32) (o : H.OutC c h32) (ho : convC c h32 d = some o)
    (hy : whyOutE (H.DX c) (H.ok c h32) d₁ (H.dec c) (EntryRunTop.famOf (H.DX c) hcfg d₁ sh) o.1
      o.2.1 (toPS _ _ o.2.2) = "YES") :
    ((((H.spec cfg (H.convOf cfg convC) εs Bk).toO (pubS₀ cfg) (pubS₁ [H.prm] cfg)
      (own₀ (pubS₀ cfg) _root_.Run.oBits)
      (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) _root_.Run.oBits)).chk d).det
        _root_.Run.oBits).map
          (fun o' : H.Out cfg (own₀ (pubS₀ cfg) _root_.Run.oBits)
            (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) _root_.Run.oBits) => stmt o') =
      some (stmt o) := by
  subst hc
  have ef := H.famOf_at cfg (H.convOf cfg convC) sh _ _ hp hcfg
  have h := (H.chk_iff_why cfg (H.convOf cfg convC) εs Bk _root_.Run.oBits d o).2
    ⟨ho, (congrArg (fun F => whyOutE _ _ d₁ _ F o.1 o.2.1 (toPS _ _ o.2.2)) ef).symm.trans hy⟩
  rw [h]
  rfl

omit [DecidableEq (Sd1 z.lg z.s)] in
/-- THE VALUE THAT THE ORACLE'S OWN SECOND TABLE HOLDS AT THE STRING OF THE PARAMETER BYTES IS THE
PIN THAT A RUN COMPUTES, at the digest of the three configuration files. Asked: two bounds on
sizes; the parameter bytes are the description's. By `own₁_at` (OnBytes/TypedOracleCompiler/Slice/ShapesPub.lean).
-/
theorem pd_own₁ (hb : (_root_.Fmt.configBytes [cfg.pol, cfg.lay, cfg.KL]).size ≤ 2 ^ 32 - 144)
    (hb' : (H.prm (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])).size ≤
      2 ^ 32 - 144)
    (hprm : H.prm (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]) =
      (H.DX (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])).base.params) :
    own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) _root_.Run.oBits
        (s0Of (H.prm (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))) =
      EntryRunTop.pdOf (H.DX (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])) := by
  have h := OnBytes.Slice.Shapes.own₁_at cfg [H.prm] H.prm (List.mem_singleton.2 rfl) hb hb'
  have h2 := congrArg _root_.Run.bytesToDig h
  rw [_root_.Run.TieTree.bytes_dig] at h2
  rw [h2, hprm]
  rfl

/-- THE SAME AT THE DIGEST OF THE THREE CONFIGURATION FILES, WITH BOTH HYPOTHESES ON DIGESTS
PAID: what is left: two bounds on sizes; the parameter bytes are the description's; the
description holds the digest; the bytes behind a root, the length of a salt and the code behind the
escape agree; the converter makes o of the files; the run's function says "YES". -/
theorem yes_of_run_files (convC : H.ConvC)
    (sh : OnBytes.Params.IndexShape) (εs : ℝ≥0∞) (Bk : ℕ) (d : Files)
    (hb : (_root_.Fmt.configBytes [cfg.pol, cfg.lay, cfg.KL]).size ≤ 2 ^ 32 - 144)
    (hb' : (H.prm (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])).size ≤
      2 ^ 32 - 144)
    (hprm : H.prm (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]) =
      (H.DX (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])).base.params)
    (cfgIs : (H.DX (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])).base.cfg =
      OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
    (restIs : TypedOracleCompiler.Run.FirstName.restOf
        (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]) z.T.a z.T.l z.T.r z.v z.s
        z.shape.saltBytes =
      EntryRunTop.restAt (H.DX (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])) sh)
    (saltIs : z.shape.saltBytes =
      (H.DX (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])).base.plan.salt)
    (backIs : H.back (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]) =
      EntryRunTop.backOf (H.DX (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])) d₁)
    (h32 : (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]).size = 32)
    (hcfg : (H.DX (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])).base.cfg.size =
      32)
    (o : H.OutC (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]) h32)
    (ho : convC (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]) h32 d = some o)
    (hy : whyOutE (H.DX (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))
      (H.ok _ h32) d₁ (H.dec _)
      (EntryRunTop.famOf (H.DX (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))
        hcfg d₁ sh) o.1 o.2.1 (toPS _ _ o.2.2) = "YES") :
    ((((H.spec cfg (H.convOf cfg convC) εs Bk).toO (pubS₀ cfg) (pubS₁ [H.prm] cfg)
      (own₀ (pubS₀ cfg) _root_.Run.oBits)
      (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) _root_.Run.oBits)).chk d).det
        _root_.Run.oBits).map
          (fun o' : H.Out cfg (own₀ (pubS₀ cfg) _root_.Run.oBits)
            (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) _root_.Run.oBits) => stmt o') =
      some (stmt o) :=
  H.yes_of_run cfg convC sh εs Bk d _ h32 (OnBytes.Slice.Shapes.dgOf_own₀ cfg hb).symm
    ⟨cfgIs, H.pd_own₁ cfg hb hb' hprm, restIs, saltIs, backIs⟩ hcfg o ho hy

end HomeData

end TypedOracleCompiler.Slice
