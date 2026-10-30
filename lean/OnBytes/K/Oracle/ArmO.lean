-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Oracle/ArmO.lean: THE ENTRY FILE: TWO STATEMENTS ON ONE CHECKER THAT READS THE FILES
THROUGH THE ORACLE: the statement, and the first of the two from the left half.

Why. `EntryArm` (OnBytes/K/Left/Arm.lean) has two statements on a checker with one form for each
converter: its first speaks of the form at the strict converter, which hashes by the fixed hash, and
there its second says next to nothing. Here the checker has ONE form: it parses the key file's
table, reads the entry file by a twin of the program's reader that asks the oracle for every hash
but one, then runs the compiled verifier. (The one: the digest of the three public files is not
asked: it is handed in as the oracle's own value at their string, with the parameters' digest, in
two tables; in both statements the tables are those of the oracle under which the checker runs, and
a question at either string is answered from them.) At the oracle made from the format's hash that
is a reading at the format's hash; under a drawn oracle the reader asks the drawn oracle, and its
queries are counted.

 `EntryArmO` `zero`: where the parameter file has the setting's lines, exit code 0 of the Lean
     verifier program is a yes of THIS checker on the call's own key file and entry file, at the
     oracle made from the format's hash, with the two tables of the program's own yes and the user's
     ID, as in `EntryArm.zero`. `sound`: THE SAME checker, over one uniformly random oracle: at most
     2^-61 up to 2^64 queries of the maker. `same`: it is one checker, by unfolding alone; no third
     result.
 `ReturnsO`, `returnsO_of_returns`, `conv_of_returns`, `ty_of_conv`, `returnsO_of_verifyE`,
     `zeroO_of_left` the steps: where the program said yes, the asking half at the format's hash
     makes of the files what the strict converter makes of them (`asked_conv`,
     OnBytes/K/Oracle/AskedAt.lean).

WHAT STILL PARTS THE TWO, AND IS NO THEOREM. `zero` is at one fixed hash, `sound` over a drawn
oracle: to pass from one to the other the fixed hash is taken for a drawn oracle: the step of every
argument in the random-oracle model. No theorem here has both a call and a probability in it, and NO
PROBABILITY IS SAID OF THE PROGRAM's YES. `sound` concludes of strings read off a maker's log; in
`zero` there is no maker and no log.

What else is not claimed. THE READER IS A TWIN OF THE PROGRAM's: the program does not call the
reader, and whether it runs that twin's own text on a model's entry file follows from what
OnBytes/Main.lean calls (OnBytes/K/Oracle/ReaderAt.lean says how the two are tied). The checker is
still a SECOND checker: behind the reader stands the verifier made by a second form of the compiler,
with a hand-written step for the seeds; not the program's own check of an entry file and not
`innerCompiledVerifier`. That under a drawn oracle the checker accepts anything is not shown. The ID
stands in `zero` alone, and it and the three public files' digest in `zero` are by the fixed hash.
ONE file of three. No theorem says that the program's own check, with an oracle for its hash, says
yes only where this checker does under that oracle: `zero` is at one oracle. The three public files
are fixed before the oracle is drawn: a maker who picks them after asking the oracle is not covered.
The bound holds of EVERY reader with the four laws of OnBytes/K/Oracle/Frame.lean: the reader is
trusted for nothing, and that the bound has force at this reader is a reading of its text. All else
that the head of OnBytes/K/Left/Arm.lean does not claim (that head is written for the checker with
one form for each converter; its sentence on the strict converter is what this file answers): the
setting; the ways out; the figure, which counts 32 of the 128 bits as proof of work; exit code 0 for
`YES` and `WITHIN LIMITS` alike; no call is shown to end with exit code 0. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Oracle.ReaderAt
import OnBytes.K.Oracle.AskedAt
import OnBytes.K.Left.Arm

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Oracle
open Rom Prob Cb _root_.Compile TypedOracleCompiler.Slice OnBytes.K.Left
open OnBytes.Tie (EntryGround linkAtCfg keyAt AskedE askedAt typedT)
open OnBytes.Slice (GE GF s0Of)
open OnBytes.Slice.Shapes (Size Cfg dgOf dgOf_size pubS₀ pubS₁)
open OnBytes.Slice.Shapes.FileSpec (own₀ own₁)
open OnBytes.Shell (World)
open scoped ENNReal

section
variable {z : Size} {d₁ : Sd1 z.lg z.s} [DecidableEq (Sd1 z.lg z.s)] {H : HomeData z d₁}
  {cfg : Cfg} {tT : ℕ}

/-- **THE CHECKER THAT READS THROUGH THE ORACLE RETURNS o ON THE FILES d**, under the oracle made
from the format's hash. -/
def ReturnsO (Y : H.Reader cfg tT) (Bk : ℕ) (d : OnBytes.Slice.Shapes.Files) (o : H.OutB cfg) :
    Prop :=
  (((HomeData.specO Y (((2 : ℝ≥0∞)⁻¹) ^ 128) Bk).toO (pubS₀ cfg) (pubS₁ [H.prm] cfg)
    (own₀ (pubS₀ cfg) _root_.Run.oBits)
    (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) _root_.Run.oBits)).chk d).det _root_.Run.oBits = some o

/-- **From the checker at a plain converter to the checker that reads through the oracle**: where
the first returns o on the files d at the format's hash, and the reader makes o of d at that hash,
the second returns o on d. -/
theorem returnsO_of_returns (Y : H.Reader cfg tT) (Bk : ℕ) (conv : H.Conv cfg)
    (d : OnBytes.Slice.Shapes.Files) (o : H.OutB cfg) (h : H.Returns cfg Bk conv d o)
    (hty : (Y.ty (own₀ (pubS₀ cfg) _root_.Run.oBits)
      (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) _root_.Run.oBits) d).det _root_.Run.oBits = some o) :
    ReturnsO Y Bk d o := by
  unfold ReturnsO
  unfold HomeData.Returns at h
  rw [HomeData.chk_eq_run] at h
  rw [HomeData.chk_eq_runO, hty]
  obtain ⟨o', -, h2⟩ := Option.bind_eq_some_iff.1 h
  by_cases hc : (((H.at cfg conv (own₀ (pubS₀ cfg) _root_.Run.oBits)
      (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) _root_.Run.oBits)).base z.T z.v z.eM (anT z.v z.s)
        (((2 : ℝ≥0∞)⁻¹) ^ 128)).J.run o').det (readBlocks (H.at cfg conv
          (own₀ (pubS₀ cfg) _root_.Run.oBits)
          (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) _root_.Run.oBits)).m _root_.Run.oBits) = true
  · rw [if_pos hc] at h2
    obtain rfl := Option.some.inj h2
    exact if_pos hc
  · rw [if_neg hc] at h2
    cases h2

/-- Where the checker at a plain converter returns o, the converter has made o. -/
theorem conv_of_returns (Bk : ℕ) (conv : H.Conv cfg) (d : OnBytes.Slice.Shapes.Files)
    (o : H.OutB cfg) (h : H.Returns cfg Bk conv d o) :
    conv (own₀ (pubS₀ cfg) _root_.Run.oBits)
      (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) _root_.Run.oBits) d = some o := by
  unfold HomeData.Returns at h
  rw [HomeData.chk_eq_run] at h
  obtain ⟨o', h1, h2⟩ := Option.bind_eq_some_iff.1 h
  have h1' := (Option.filter_eq_some_iff.1 h1).1
  split at h2
  · obtain rfl := Option.some.inj h2
    exact h1'
  · cases h2

/-- **TWO STATEMENTS ON ONE CHECKER THAT READS THE FILES THROUGH THE ORACLE**, at one size. Y: the
reader, at every three public files. -/
structure EntryArmO (G : EntryGround) (H : HomeData z d₁) (Y : ∀ cfg, H.Reader cfg tT) (Bk : ℕ) :
    Prop where
  /-- **WHERE THE PARAMETER FILE HAS THE SETTING's LINES, EXIT CODE 0 OF THE LEAN VERIFIER PROGRAM
  IS A YES OF THE CHECKER ON THE CALL's OWN FILES**, at the oracle made from the format's hash: as
  `EntryArm.zero` (OnBytes/K/Left/Arm.lean), with the checker that reads through the oracle in the
  place of the checker at the strict converter. -/
  zero : ∀ (args : List String) (s s' : World), Shell.Run (_root_.main args) s 0 s' →
    ∃ (F : Files) (id : String) (table further : Params.TableName), CallRead args s s' F id ∧
      PortYesAt F id table further ∧
      (G.SaysLines F.pol →
        ∃ o : H.OutB (cfgOf F),
          ReturnsO (Y (cfgOf F)) Bk (filesOf F) o ∧
          o.1 = [_root_.Run.bytesToDig table.root, _root_.Run.bytesToDig further.root] ∧
          o.2.1.1 = (table.answers.map E.triple, further.answers.map E.triple) ∧
          Model.Verify.idAsked id =
            some (stmtId G.q.link.table (digOf F) (o.1.getD 0 default) o.2.1.2.1 o.2.1.1.1))
  /-- **THAT SAME CHECKER IS SOUND.** The three public files and the maker are fixed first. This is
  said under the hypotheses that stand in the statement itself, which this comment does not list; it
  is no claim that they hold. Then,
  over one uniformly random oracle, WHICH THE CHECKER ASKS AS THE MAKER DOES, for a maker of
  files with at most t queries, t up to 2^64: with probability at most 2^-61 the checker returns
  a value while the entry's language fails of the two strings that are read off the maker's log
  under that value's roots, with its records. -/
  sound : ∀ (cfg : Cfg) (A : OComp (rom 256) OnBytes.Slice.Shapes.Files) (t : ℕ),
    A.QueryBound t → t ≤ 2 ^ 64 →
      Rom.Pr A.withTrace (HomeData.LoseO (Y cfg) (((2 : ℝ≥0∞)⁻¹) ^ 128) Bk) ≤ ((2 : ℝ≥0∞)⁻¹) ^ 61
  /-- **IT IS ONE CHECKER**, by unfolding alone; no third result. -/
  same : ∀ (cfg : Cfg) (d : OnBytes.Slice.Shapes.Files) (σ : Trace (rom 256)),
    (d, σ) ∈ HomeData.LoseO (Y cfg) (((2 : ℝ≥0∞)⁻¹) ^ 128) Bk _root_.Run.oBits ↔
      ∃ (o : H.OutB cfg) (r₀ r₁ : _root_.Iop.Dig 256),
        ReturnsO (Y cfg) Bk d o ∧ o.1 = [r₀, r₁] ∧ ¬ H.LangAt cfg o σ r₀ r₁

end

section
variable (G : EntryGround)
  (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)

/-- Where the asking half, under an oracle g, makes of the files what the strict converter makes of
them, the reader's value under g is the strict converter's typed value. T₀, T₁: any tables. -/
theorem ty_of_conv (eM : ℕ) (cfg : Cfg) (T₀ T₁ : OnBytes.Slice.Tab) (g : Fam (rom 256))
    (d : OnBytes.Slice.Shapes.Files) (a : AskedE) (c : ByteArray) (hc : c = dgOf cfg T₀)
    (hcv : convE (linkAtCfg G.q c) (keyAt G.q.link.table c d.key).2.2 d.ent = some a)
    (hask : askedAt (_root_.Run.oB (g ())) (linkAtCfg G.q c)
      (keyAt G.q.link.table c d.key).2.2 d.ent = some a) :
    ((readerOf G hok eM cfg).ty T₀ T₁ d).det g =
      (homeOf G hok eM).convOf cfg (convPlay G hok eM false) T₀ T₁ d := by
  subst hc
  show (tyAt G hok eM (dgOf cfg T₀) (dgOf_size cfg T₀) d).det g =
    convPlay G hok eM false (dgOf cfg T₀) (dgOf_size cfg T₀) d
  rw [tyAt_det, hask]
  exact (convPlay_of_convE G hok eM _ _ d a hcv).symm

/-- **From the trusted function's yes on what the strict converter makes of the files, which is
also what the asking half makes of them at the format's hash, to the yes of the checker that reads
through the oracle.** -/
theorem returnsO_of_verifyE (eM Bk : ℕ) (cfg : Cfg) (id : String)
    (d : OnBytes.Slice.Shapes.Files) (a : AskedE) (c : ByteArray) (h32 : c.size = 32)
    (hc : c = dgOf cfg (own₀ (pubS₀ cfg) _root_.Run.oBits))
    (hpd : own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) _root_.Run.oBits
      (s0Of ((homeOf G hok eM).prm c)) = EntryRunTop.pdOf ((homeOf G hok eM).DX c))
    (hcv : convE (linkAtCfg G.q c) (keyAt G.q.link.table c d.key).2.2 d.ent = some a)
    (hask : askedAt (_root_.Run.oB (_root_.Run.oBits ())) (linkAtCfg G.q c)
      (keyAt G.q.link.table c d.key).2.2 d.ent = some a)
    (h : verifyE G hok ⟨id, c, h32⟩ a = true) :
    ∃ o : (homeOf G hok eM).OutB cfg,
      ReturnsO (readerOf G hok eM cfg) Bk d o ∧
      o.1 = [_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root] ∧
      o.2.1.1 = (a.first.answers.map E.triple, a.further.answers.map E.triple) ∧
      id = stmtId G.q.link.table c (o.1.getD 0 default) o.2.1.2.1 o.2.1.1.1 := by
  obtain ⟨o, hR, h1, h2, h3, -⟩ := returns_of_verifyE G hok eM Bk cfg id d a c h32 hc hpd hcv h
  refine ⟨o, returnsO_of_returns _ Bk _ d o hR ?_, h1, h2, h3⟩
  have hconv := conv_of_returns Bk _ d o hR
  exact (ty_of_conv G hok eM cfg _ _ _root_.Run.oBits d a c hc hcv hask).trans hconv

/-- From the left half to the first clause, general in the ground. -/
theorem zeroO_of_left (hA : (G.q.link.table.answers == 0) = false) (zS : Params.StdSize)
    (eM Bk : ℕ) (hL : EntryLeft G hok zS) (args : List String) (s s' : World)
    (h : Shell.Run (_root_.main args) s 0 s') :
    ∃ (F : Files) (id : String) (table further : Params.TableName), CallRead args s s' F id ∧
      PortYesAt F id table further ∧
      (G.SaysLines F.pol →
        ∃ o : (homeOf G hok eM).OutB (cfgOf F),
          ReturnsO (readerOf G hok eM (cfgOf F)) Bk (filesOf F) o ∧
          o.1 = [_root_.Run.bytesToDig table.root, _root_.Run.bytesToDig further.root] ∧
          o.2.1.1 = (table.answers.map E.triple, further.answers.map E.triple) ∧
          Model.Verify.idAsked id =
            some (stmtId G.q.link.table (digOf F) (o.1.getD 0 default) o.2.1.2.1 o.2.1.1.1)) := by
  obtain ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, h1, h2, h3, h4, h5, hp⟩ :=
    main_zero_port h
  obtain ⟨table, further, hat⟩ := hp
  refine ⟨F, id, table, further,
    ⟨config, ivk, request, y, proof, a, t, pre, post, h1, h2, h3, h4, h5⟩, hat, fun hs => ?_⟩
  obtain ⟨v, nid, hn, hv1, hv2, hpre, hv⟩ := hL F id table further hat hs
  obtain ⟨hstd, -, hcv⟩ := prepE_ok G zS _ _ _ _ _ _ hpre
  have hb := Params.stdEntry_bytes hstd
  have hpd := (homeOf G hok eM).pd_own₁ (cfgOf F) hb
    (params_le_of_ok _ (hok _ (Params.configurationDigest_size _))) (homeOf_prm G hok eM _)
  have htab := table_at G hat hs (digOf F)
  have hask : askedAt (_root_.Run.oB (_root_.Run.oBits ())) (linkAtCfg G.q (digOf F))
      (keyAt G.q.link.table (digOf F) (filesOf F).key).2.2 (filesOf F).ent = some v := by
    have e := asked_conv G hA hat hs
    have hcv' : convE (linkAtCfg G.q (digOf F)) (keyAt G.q.link.table (digOf F) F.key).2.2 F.ent =
      some v := hcv
    rw [htab] at hcv'
    show askedAt _ _ (keyAt G.q.link.table (digOf F) F.key).2.2 F.ent = some v
    rw [htab]
    exact e.trans hcv'
  obtain ⟨o, h1', h2', h2'', h3'⟩ := returnsO_of_verifyE G hok eM Bk (cfgOf F) nid (filesOf F) v
    (digOf F) (Params.configurationDigest_size _)
    (OnBytes.Slice.Shapes.dgOf_own₀ (cfgOf F) hb).symm hpd hcv hask hv
  rw [hv1, hv2] at h2' h2''
  exact ⟨o, h1', h2', h2'', hn.trans (congrArg some h3')⟩

end

end OnBytes.K.Oracle
