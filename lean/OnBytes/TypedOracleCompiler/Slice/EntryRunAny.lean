-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryRunAny.lean: THE VERDICT IS ON THE TYPED VALUE; AND, WHERE A PLAY'S TWO TESTS
ON THE PUBLIC FILES PASS, AN UNDAMAGED PLAY'S WORD IS THE CHECKER'S VERDICT BOTH WAYS. Additions to
OnBytes/TypedOracleCompiler/Slice/EntryRunTie.lean and EntryRunPlay.lean, of four kinds.

WHY. `playSmall_yes_checker` (EntryRunPlay.lean) carries a play's "YES" to the checker at the play's
own converter. The bound (`small_one_world`, OnBytes/TypedOracleCompiler/Slice/EntrySmallTop.lean) is for every
converter, and at that one converter it says next to nothing. The checker's verdict does not hang on
who made the typed value: so a play's yes is a yes of the checker at every converter that makes that
value at that oracle's two tables. THAT CARRIES NO PROBABILITY TO THE YES: under a drawn oracle the
tables are others. And EntryRunPlay.lean carries a yes alone: here a refusal of an undamaged play is
a refusal of the checker at the play's converter.

Main definition.
 `PlayFacts G hok eM lax d c`   what a play tests behind its two tests on the public files, as a
                        statement on a digest c.
Main theorems.
 `HomeData.any_conv`    THE VERDICT IS ON THE TYPED VALUE: under every oracle g: if the checker at
                        one converter returns o, then o has two roots, and the checker at EVERY
                        converter returns o on all files of which that converter makes o.
 `HomeData.none_any`    A REFUSAL ON THE TYPED VALUE: if the checker at one converter returns
                        nothing on files of which that converter makes o, the checker at no
                        converter returns o.
 `HomeData.const_conv`  some converter makes o of all files at two given tables: o is written into
                        it.
 `HomeData.run_iff_checker`   the run's "YES" and the checker's value, BOTH WAYS, at the oracle made
                        from the format's hash, where the pins agree at c and the description at c
                        holds a digest of 32 bytes (hcfg).
 `play_yes_any`, `playSmall_yes_any`   A PLAY'S "YES", FREE OF ITS CONVERTER: there is a typed value
                        o with two roots, which the play's converter makes of these files, of whose
                        roots, seeds and answers the play's second word is made, and which the
                        checker at every converter returns on all files of which that converter
                        makes o.
 `playE_iff_facts`, `facts_iff_checker`   the two halves of the next.
 `play_iff_checker`, `playSmall_iff_checker`   where the play's two tests on the public files pass,
                        the play says "YES" exactly if the checker at the play's converter returns a
                        value.
 `play_no_of_yes`, `playSmall_no_of_yes`   a refusal beside a yes at the same public files is the
                        checker's: the two tests are had from the yes.
 `homeOf_full`          the letters of a play at the full-size ground are the part of the full
                        size's bound (`homeFull`, OnBytes/TypedOracleCompiler/Slice/EntryFullTop.lean).

Not claimed. ALL OF THIS IS AT ONE FIXED ORACLE; NO PROBABILITY STANDS HERE. The bound is over a
uniformly random oracle; a play runs at a fixed hash: what joins the two is the usual step of an
argument in the random oracle model, and no theorem. In `any_conv` and `none_any` the other
converter is asked at g's own two tables alone, and o's type is the type at the digest that g gives:
no converter is shown in this file at which the bound says more of this value. A REFUSAL IS A
REFUSAL OF THE CHECKER AT THE PLAY'S CONVERTER, NOT OF THE FILES: at another converter the checker
may return a value on the same files. That a play says "YES" or refuses on any files: a matter of a
run. NOTHING ON PLAYS WITH DAMAGE behind the converter: such a play is the checker at another
converter, for which no term is written. Where one of the play's two tests on the public files fails
the play refuses and nothing is said of the checker. Nothing on the name of the stage that refuses.
Nothing on a play at the other family (`safe := false`). No play at the full size is spoken of.
NOTHING ON SOUNDNESS IS SHOWN HERE. What the heads of EntryRunTie.lean, EntryRunPlay.lean,
EntrySmallTop.lean and EntryHome.lean do not claim. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntrySmallTop

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD bodyS)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open OnBytes.Tie (EntryGround linkAtCfg keyAt)
open OnBytes.Slice (Tab s0Of)
open OnBytes.Slice.Shapes (Files FileSpec Size Cfg dgOf dgOf_size pubS₀ pubS₁)
open OnBytes.Slice.Shapes.FileSpec (own₀ own₁)
open scoped ENNReal

/-! ## The verdict is on the typed value: whichever converter makes it -/

namespace HomeData
variable {z : Size} {d₁ : Sd1 z.lg z.s} [DecidableEq (Sd1 z.lg z.s)] (H : HomeData z d₁)
  (cfg : Cfg)

/-- THE VERDICT IS ON THE TYPED VALUE. Under every oracle g: if the checker at one converter
returns o on some files, then o has two roots, and the checker at EVERY converter returns o on all
files of which that converter makes o. -/
theorem any_conv (conv : H.Conv cfg) (εs : ℝ≥0∞) (Bk : ℕ) (g : Fam (rom 256)) (d : Files)
    (o : H.Out cfg (own₀ (pubS₀ cfg) g) (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g))
    (h : (((H.spec cfg conv εs Bk).toO (pubS₀ cfg) (pubS₁ [H.prm] cfg) (own₀ (pubS₀ cfg) g)
      (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g)).chk d).det g = some o) :
    o.1.length = 2 ∧ ∀ (conv' : H.Conv cfg) (d' : Files),
      conv' (own₀ (pubS₀ cfg) g) (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g) d' = some o →
      (((H.spec cfg conv' εs Bk).toO (pubS₀ cfg) (pubS₁ [H.prm] cfg) (own₀ (pubS₀ cfg) g)
        (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g)).chk d').det g = some o := by
  have hy := ((H.chk_iff_why cfg conv εs Bk g d o).1 h).2
  exact ⟨((H.at_why cfg conv εs _ _ _ o).1 hy).1,
    fun conv' d' h' => (H.chk_iff_why cfg conv' εs Bk g d' o).2 ⟨h', hy⟩⟩

/-- A REFUSAL ON THE TYPED VALUE. Under every oracle g: if the checker at one converter returns
nothing on files of which that converter makes o, then the checker at no converter returns o on any
files. -/
theorem none_any (conv : H.Conv cfg) (εs : ℝ≥0∞) (Bk : ℕ) (g : Fam (rom 256)) (d : Files)
    (o : H.Out cfg (own₀ (pubS₀ cfg) g) (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g))
    (ho : conv (own₀ (pubS₀ cfg) g) (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g) d = some o)
    (hn : (((H.spec cfg conv εs Bk).toO (pubS₀ cfg) (pubS₁ [H.prm] cfg) (own₀ (pubS₀ cfg) g)
      (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g)).chk d).det g = none)
    (conv' : H.Conv cfg) (d' : Files) :
    (((H.spec cfg conv' εs Bk).toO (pubS₀ cfg) (pubS₁ [H.prm] cfg) (own₀ (pubS₀ cfg) g)
      (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g)).chk d').det g ≠ some o := fun h' => by
  have h := (H.any_conv cfg conv' εs Bk g d' o h').2 conv d ho
  rw [hn] at h
  cases h

omit [DecidableEq (Sd1 z.lg z.s)] in
/-- Some converter makes o of all files at two given tables: o is written into it. So "every
converter that makes o" is not said of one converter alone; and so little can such a converter be.
-/
theorem const_conv (T₀ T₁ : Tab) (o : H.Out cfg T₀ T₁) :
    ∃ conv' : H.Conv cfg, ∀ d', conv' T₀ T₁ d' = some o := by
  classical
  exact ⟨fun T₀' T₁' _ => if h : T₀' = T₀ ∧ T₁' = T₁ then some (h.1 ▸ h.2 ▸ o) else none,
    fun _ => by simp⟩

set_option maxRecDepth 20000 in
/-- THE RUN'S "YES" AND THE CHECKER'S VALUE, BOTH WAYS, at the oracle made from the format's
hash: where c is the digest that the oracle's own first table holds, the pins agree at c, and the
description at c holds a digest of 32 bytes (hcfg): the converter makes of the files at c a typed
value on which the run's function says "YES" under the family that a run evaluates, EXACTLY IF the
checker at that converter returns a value. -/
theorem run_iff_checker (convC : H.ConvC) (sh : OnBytes.Params.IndexShape) (εs : ℝ≥0∞) (Bk : ℕ)
    (d : Files) (c : ByteArray) (h32 : c.size = 32)
    (hc : c = dgOf cfg (own₀ (pubS₀ cfg) _root_.Run.oBits))
    (hp : H.PinsAt sh c (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) _root_.Run.oBits
      (s0Of (H.prm c))))
    (hcfg : (H.DX c).base.cfg.size = 32) :
    (∃ o : H.OutC c h32, convC c h32 d = some o ∧
      whyOutE (H.DX c) (H.ok c h32) d₁ (H.dec c) (EntryRunTop.famOf (H.DX c) hcfg d₁ sh) o.1 o.2.1
        (toPS _ _ o.2.2) = "YES") ↔
      ((((H.spec cfg (H.convOf cfg convC) εs Bk).toO (pubS₀ cfg) (pubS₁ [H.prm] cfg)
        (own₀ (pubS₀ cfg) _root_.Run.oBits)
        (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) _root_.Run.oBits)).chk d).det
          _root_.Run.oBits).isSome = true := by
  constructor
  · rintro ⟨o, ho, hy⟩
    have h := H.yes_of_run cfg convC sh εs Bk d c h32 hc hp hcfg o ho hy
    obtain ⟨o', ho', -⟩ := Option.map_eq_some_iff.1 h
    rw [ho']
    rfl
  · intro h
    subst hc
    have ef := H.famOf_at cfg (H.convOf cfg convC) sh _ _ hp hcfg
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 h
    obtain ⟨h1, h2⟩ := (H.chk_iff_why cfg (H.convOf cfg convC) εs Bk _root_.Run.oBits d o).1 ho
    exact ⟨o, h1,
      (congrArg (fun F => whyOutE _ _ d₁ _ F o.1 o.2.1 (toPS _ _ o.2.2)) ef).trans h2⟩

end HomeData

/-! ## A play's yes, free of its converter -/

variable (G : EntryGround)
  (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)

/-- A PLAY'S "YES", FREE OF ITS CONVERTER. If the play without damage, at the page's own family,
says "YES", then there is a typed value o with two roots, which the play's converter makes of these
files, of whose roots, seeds and answers the play's second word is made, such that THE CHECKER AT
EVERY CONVERTER returns o, under the oracle made from the format's hash, on all files of which that
converter makes o. -/
theorem play_yes_any (eM : ℕ) (zS : OnBytes.Params.StdSize) (lax : Bool) (cfg : Cfg) (d : Files)
    (εs : ℝ≥0∞) (Bk : ℕ)
    (h : (playE G hok zS true lax .none cfg.pol cfg.lay cfg.KL d.key d.ent).1 = "YES") :
    ∃ o : (homeOf G hok eM).Out cfg (own₀ (pubS₀ cfg) _root_.Run.oBits)
        (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) _root_.Run.oBits),
      o.1.length = 2 ∧
      (homeOf G hok eM).convOf cfg (convPlay G hok eM lax) (own₀ (pubS₀ cfg) _root_.Run.oBits)
        (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) _root_.Run.oBits) d = some o ∧
      (playE G hok zS true lax .none cfg.pol cfg.lay cfg.KL d.key d.ent).2 =
        "first " ++ stmtId G.q.link.table
            (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
            (o.1.getD 0 default) o.2.1.2.1 o.2.1.1.1 ++ " copy " ++
          stmtId G.q.link.table (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
            (o.1.getD 1 default) o.2.1.2.2 o.2.1.1.2 ∧
      ∀ (conv' : (homeOf G hok eM).Conv cfg) (d' : Files),
        conv' (own₀ (pubS₀ cfg) _root_.Run.oBits)
          (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) _root_.Run.oBits) d' = some o →
        ((((homeOf G hok eM).spec cfg conv' εs Bk).toO (pubS₀ cfg)
          (pubS₁ [(homeOf G hok eM).prm] cfg) (own₀ (pubS₀ cfg) _root_.Run.oBits)
          (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) _root_.Run.oBits)).chk d').det
            _root_.Run.oBits = some o := by
  obtain ⟨st, h1, h2⟩ := play_yes_checker G hok eM zS lax cfg d εs Bk h
  obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 h1
  obtain ⟨hl, ha⟩ := (homeOf G hok eM).any_conv cfg _ εs Bk _root_.Run.oBits d o ho
  exact ⟨o, hl, (((homeOf G hok eM).chk_iff_why cfg _ εs Bk _root_.Run.oBits d o).1 ho).1, h2, ha⟩

/-! ## The other way: an undamaged play's word and the checker's value -/

/-- WHAT A PLAY TESTS BEHIND ITS TWO TESTS ON THE PUBLIC FILES, as a statement on a digest c:
the converter makes a typed value of the files at c, and the run's function says "YES" on it under
the family that a run evaluates. -/
def PlayFacts (eM : ℕ) (lax : Bool) (d : Files) (c : ByteArray) : Prop :=
  ∃ (h32 : c.size = 32) (o : (homeOf G hok eM).OutC c h32),
    convPlay G hok eM lax c h32 d = some o ∧
      whyOutE (entryXD G c) (hok c h32) (d1Run _ _)
        (decRun (linkAtCfg G.q c) G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers)
        (EntryRunTop.famOf (entryXD G c) h32 (d1Run _ _) G.q.link.table) o.1 o.2.1
        (toPS _ _ o.2.2) = "YES"

/-- Where the two tests on the public files pass, the play says "YES" exactly if these facts hold
at the digest of the three public files. -/
theorem playE_iff_facts (eM : ℕ) (zS : OnBytes.Params.StdSize) (lax : Bool) (cfg : Cfg) (d : Files)
    (hs : OnBytes.Params.stdEntry zS ⟨cfg.pol, cfg.lay, cfg.KL⟩ = true)
    (hp : pinsFit (entryXD G (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))
      G.q.link.table = true) :
    (playE G hok zS true lax .none cfg.pol cfg.lay cfg.KL d.key d.ent).1 = "YES" ↔
      PlayFacts G hok eM lax d (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]) := by
  constructor
  · intro h
    obtain ⟨-, -, o, ho, hy, -⟩ := playE_yes G hok eM zS lax cfg d h
    exact ⟨OnBytes.Params.configurationDigest_size _, o, ho, hy⟩
  · rintro ⟨h32, o, ho, hy⟩
    unfold convPlay at ho
    obtain ⟨a, hcv, ho⟩ := Option.bind_eq_some_iff.1 ho
    obtain ⟨π, has, rfl⟩ := Option.map_eq_some_iff.1 ho
    unfold playE prepE
    rw [if_pos hs, hcv]
    dsimp only
    rw [hp]
    simpa [Dmg.applies, Dmg.onO, Dmg.onC, Dmg.onX, Dmg.onS, has, famAt] using hy

set_option maxRecDepth 20000 in
/-- At the digest that the oracle's own first table holds, where its second table holds the pin
that a run computes and the play's test of the pins passes, these facts hold exactly if the checker
at the play's converter returns a value under the oracle made from the format's hash. -/
theorem facts_iff_checker (eM : ℕ) (lax : Bool) (cfg : Cfg) (d : Files) (εs : ℝ≥0∞) (Bk : ℕ)
    (c : ByteArray) (hc : c = dgOf cfg (own₀ (pubS₀ cfg) _root_.Run.oBits))
    (hpd : own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) _root_.Run.oBits
      (s0Of ((homeOf G hok eM).prm c)) = EntryRunTop.pdOf ((homeOf G hok eM).DX c))
    (hp : pinsFit (entryXD G c) G.q.link.table = true) :
    PlayFacts G hok eM lax d c ↔
      (((((homeOf G hok eM).spec cfg ((homeOf G hok eM).convOf cfg (convPlay G hok eM lax)) εs
        Bk).toO (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg)
        (own₀ (pubS₀ cfg) _root_.Run.oBits)
        (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) _root_.Run.oBits)).chk d).det
          _root_.Run.oBits).isSome = true := by
  have h32 : c.size = 32 := hc ▸ dgOf_size cfg _
  have hr := (homeOf G hok eM).run_iff_checker cfg (convPlay G hok eM lax) G.q.link.table εs Bk d c
    h32 hc ⟨rfl, hpd, rfl, salt_of_pinsFit _ _ hp, rfl⟩ h32
  exact ⟨fun ⟨_, o, ho, hy⟩ => hr.1 ⟨o, ho, hy⟩, fun h => by
    obtain ⟨o, ho, hy⟩ := hr.2 h
    exact ⟨h32, o, ho, hy⟩⟩

/-- AN UNDAMAGED PLAY'S WORD IS THE CHECKER'S VERDICT, BOTH WAYS. Where the play's two tests on
the public files pass: the play without damage, at the page's own family, says "YES" EXACTLY IF the
checker "pre-process by that play's converter, then the compiled verifier" returns a value on these
files under the oracle made from the format's hash. So there a refusal of the play is a refusal of
that checker. -/
theorem play_iff_checker (eM : ℕ) (zS : OnBytes.Params.StdSize) (lax : Bool) (cfg : Cfg)
    (d : Files) (εs : ℝ≥0∞) (Bk : ℕ)
    (hs : OnBytes.Params.stdEntry zS ⟨cfg.pol, cfg.lay, cfg.KL⟩ = true)
    (hp : pinsFit (entryXD G (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))
      G.q.link.table = true) :
    (playE G hok zS true lax .none cfg.pol cfg.lay cfg.KL d.key d.ent).1 = "YES" ↔
      (((((homeOf G hok eM).spec cfg ((homeOf G hok eM).convOf cfg (convPlay G hok eM lax)) εs
        Bk).toO (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg)
        (own₀ (pubS₀ cfg) _root_.Run.oBits)
        (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) _root_.Run.oBits)).chk d).det
          _root_.Run.oBits).isSome = true :=
  have hb := OnBytes.Params.stdEntry_bytes hs
  (playE_iff_facts G hok eM zS lax cfg d hs hp).trans
    (facts_iff_checker G hok eM lax cfg d εs Bk _ (OnBytes.Slice.Shapes.dgOf_own₀ cfg hb).symm
      ((homeOf G hok eM).pd_own₁ cfg hb
        (params_le_of_ok _ (hok _ (OnBytes.Params.configurationDigest_size _)))
        (homeOf_prm G hok eM _)) hp)

/-- A REFUSAL BESIDE A YES AT THE SAME PUBLIC FILES IS THE CHECKER'S. If the play without
damage, at the page's own family, says "YES" on the public files cfg and some files d₀ (at either
converter), and at the converter lax its first word on cfg and the files d is another than "YES",
then the checker at that converter returns nothing on d under the oracle made from the format's
hash. The play's two tests on the public files are had from the yes. -/
theorem play_no_of_yes (eM : ℕ) (zS : OnBytes.Params.StdSize) (lax₀ lax : Bool) (cfg : Cfg)
    (d₀ d : Files) (εs : ℝ≥0∞) (Bk : ℕ)
    (h₀ : (playE G hok zS true lax₀ .none cfg.pol cfg.lay cfg.KL d₀.key d₀.ent).1 = "YES")
    (hn : (playE G hok zS true lax .none cfg.pol cfg.lay cfg.KL d.key d.ent).1 ≠ "YES") :
    ((((homeOf G hok eM).spec cfg ((homeOf G hok eM).convOf cfg (convPlay G hok eM lax)) εs
      Bk).toO (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg)
      (own₀ (pubS₀ cfg) _root_.Run.oBits)
      (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) _root_.Run.oBits)).chk d).det
        _root_.Run.oBits = none := by
  obtain ⟨hs, hp, -⟩ := playE_yes G hok eM zS lax₀ cfg d₀ h₀
  have hi := play_iff_checker G hok eM zS lax cfg d εs Bk hs hp
  rw [← Option.not_isSome_iff_eq_none]
  exact fun h => hn (hi.2 h)

/-! ## At the small example; the full size's instance -/

/-- AT THE SMALL EXAMPLE: A PLAY'S "YES", FREE OF ITS CONVERTER. -/
theorem playSmall_yes_any (lax : Bool) (cfg : Cfg) (d : Files) (εs : ℝ≥0∞) (Bk : ℕ)
    (h : (playSmall true lax .none cfg.pol cfg.lay cfg.KL d.key d.ent).1 = "YES") :
    ∃ o : homeSmall.Out cfg (own₀ (pubS₀ cfg) _root_.Run.oBits)
        (own₁ (pubS₀ cfg) (pubS₁ [homeSmall.prm] cfg) _root_.Run.oBits),
      o.1.length = 2 ∧
      homeSmall.convOf cfg (convSmall lax) (own₀ (pubS₀ cfg) _root_.Run.oBits)
        (own₁ (pubS₀ cfg) (pubS₁ [homeSmall.prm] cfg) _root_.Run.oBits) d = some o ∧
      (playSmall true lax .none cfg.pol cfg.lay cfg.KL d.key d.ent).2 =
        "first " ++ stmtId OnBytes.Tie.smallRecordGround.q.link.table
            (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
            (o.1.getD 0 default) o.2.1.2.1 o.2.1.1.1 ++ " copy " ++
          stmtId OnBytes.Tie.smallRecordGround.q.link.table
            (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
            (o.1.getD 1 default) o.2.1.2.2 o.2.1.1.2 ∧
      ∀ (conv' : homeSmall.Conv cfg) (d' : Files),
        conv' (own₀ (pubS₀ cfg) _root_.Run.oBits)
          (own₁ (pubS₀ cfg) (pubS₁ [homeSmall.prm] cfg) _root_.Run.oBits) d' = some o →
        (((homeSmall.spec cfg conv' εs Bk).toO (pubS₀ cfg) (pubS₁ [homeSmall.prm] cfg)
          (own₀ (pubS₀ cfg) _root_.Run.oBits)
          (own₁ (pubS₀ cfg) (pubS₁ [homeSmall.prm] cfg) _root_.Run.oBits)).chk d').det
            _root_.Run.oBits = some o :=
  play_yes_any OnBytes.Tie.smallRecordGround small_record_ok OnBytes.Params.smallRecordRadius
    OnBytes.Params.stdSmall lax cfg d εs Bk h

/-- AT THE SMALL EXAMPLE: AN UNDAMAGED PLAY'S WORD IS THE CHECKER'S VERDICT, BOTH WAYS, where
the play's two tests on the public files pass. -/
theorem playSmall_iff_checker (lax : Bool) (cfg : Cfg) (d : Files) (εs : ℝ≥0∞) (Bk : ℕ)
    (hs : OnBytes.Params.stdEntry OnBytes.Params.stdSmall ⟨cfg.pol, cfg.lay, cfg.KL⟩ = true)
    (hp : pinsFit (entryXD OnBytes.Tie.smallRecordGround
        (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))
      OnBytes.Tie.smallRecordGround.q.link.table = true) :
    (playSmall true lax .none cfg.pol cfg.lay cfg.KL d.key d.ent).1 = "YES" ↔
      ((((homeSmall.spec cfg (homeSmall.convOf cfg (convSmall lax)) εs Bk).toO (pubS₀ cfg)
        (pubS₁ [homeSmall.prm] cfg) (own₀ (pubS₀ cfg) _root_.Run.oBits)
        (own₁ (pubS₀ cfg) (pubS₁ [homeSmall.prm] cfg) _root_.Run.oBits)).chk d).det
          _root_.Run.oBits).isSome = true :=
  play_iff_checker OnBytes.Tie.smallRecordGround small_record_ok OnBytes.Params.smallRecordRadius
    OnBytes.Params.stdSmall lax cfg d εs Bk hs hp

/-- AT THE SMALL EXAMPLE: A REFUSAL BESIDE A YES AT THE SAME PUBLIC FILES IS THE CHECKER'S. -/
theorem playSmall_no_of_yes (lax₀ lax : Bool) (cfg : Cfg) (d₀ d : Files) (εs : ℝ≥0∞) (Bk : ℕ)
    (h₀ : (playSmall true lax₀ .none cfg.pol cfg.lay cfg.KL d₀.key d₀.ent).1 = "YES")
    (hn : (playSmall true lax .none cfg.pol cfg.lay cfg.KL d.key d.ent).1 ≠ "YES") :
    (((homeSmall.spec cfg (homeSmall.convOf cfg (convSmall lax)) εs Bk).toO (pubS₀ cfg)
      (pubS₁ [homeSmall.prm] cfg) (own₀ (pubS₀ cfg) _root_.Run.oBits)
      (own₁ (pubS₀ cfg) (pubS₁ [homeSmall.prm] cfg) _root_.Run.oBits)).chk d).det
        _root_.Run.oBits = none :=
  play_no_of_yes OnBytes.Tie.smallRecordGround small_record_ok OnBytes.Params.smallRecordRadius
    OnBytes.Params.stdSmall lax₀ lax cfg d₀ d εs Bk h₀ hn

set_option maxRecDepth 20000 in
/-- THE LETTERS OF A PLAY AT THE FULL-SIZE GROUND ARE THE PART OF THE FULL SIZE'S BOUND
(`homeFull`, OnBytes/TypedOracleCompiler/Slice/EntryFullTop.lean), at the fixed value that a play takes in the
seeds' place. No play at the full size is spoken of. -/
theorem homeOf_full :
    homeOf OnBytes.Tie.recordGround record_ok OnBytes.Params.recordRadius =
      homeFull (d1Run OnBytes.Slice.Shapes.zFull.lg OnBytes.Slice.Shapes.zFull.s) := rfl

end TypedOracleCompiler.Slice
