-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryRunPlay.lean: A PLAY'S "YES" IS A YES OF THE CHECKER OF WHICH THE BOUND
SPEAKS. A play (`playE`, `playSmall`, OnBytes/TypedOracleCompiler/Slice/EntryRunMain.lean) takes five byte strings:
the three public files, a key file, an entry file; it converts them and runs the run's function on
the typed value. Here its letters are written as an instance of the entry's part at written terms
(OnBytes/TypedOracleCompiler/Slice/EntryHome.lean), its converter as a converter of that part, and its "YES" is
carried to that part's checker at the oracle made from the format's hash.

Main definitions.
 `groundSize G eM`, `homeOf G hok eM`   the sizes of a ground; THE LETTERS OF THE ENTRY'S PART AT A
                        GROUND: description, parameter bytes, the decision that a play takes, the
                        code behind the escape that the run's family takes.
 `convPlay G hok eM lax`   THE CONVERTER OF A PLAY, as a function of the configuration's digest and
                        the files: strict or lenient. Trusted for nothing.
 `homeSmall`, `convSmall`   the same at the small example: `HomeData.ofGround` at the small ground
                        and the small sizes: the instance of `left_small`
                        (OnBytes/TypedOracleCompiler/Slice/EntryHomeSmall.lean).
Main theorems.
 `homeOf_ofGround`, `homeOf_small`, `groundSize_small`   the instances are one, by unfolding: so
                        that what is shown of `HomeData.ofGround` at a ground
                        (OnBytes/TypedOracleCompiler/Slice/EntryHomeSmall.lean, EntryHomeFull.lean) is shown of a
                        play's letters.
 `playE_yes`            WHAT A PLAY'S "YES" SAYS, UNFOLDED: the public files pass the test; the pins
                        fit; the converter makes a typed value of the files at the digest of the
                        three public files; the run's function says "YES" on it; the play's second
                        word is made of its roots, seeds and answers.
 `params_le_of_ok`, `salt_of_pinsFit`   a description that passes the second compiler's test has
                        parameter bytes within the bound of the format's hash; from the test of the
                        pins: the shape's length of a salt is the plan's.
 `checker_of_facts`     from these facts to the checker, at any digest of 32 bytes.
 `play_yes_checker`     A PLAY'S "YES" IS A YES OF THE CHECKER, AT THE ORACLE MADE FROM THE FORMAT'S
                        HASH, ON THE STATEMENT THAT THE PLAY GIVES OUT: for every ground whose
                        descriptions pass the test, every radius, either converter, all files: the
                        checker returns a value whose statement (two roots, both tables' answers and
                        seeds) is the one of which the play's second word is made. No other
                        hypothesis.
 `playSmall_yes_checker`   THE SAME AT THE SMALL EXAMPLE, at `homeSmall` and `convSmall`.

Not claimed. THAT A PLAY SAYS "YES" ON ANY FILES: that is a matter of a run, and no theorem; a run
by an evaluator or by compiled code is trusted as far as these are. ONE WAY HERE: from the play's
yes to the checker's; the other way, for a play without damage: OnBytes/TypedOracleCompiler/Slice/EntryRunAny.lean;
nothing here on a play's refusals, nor on plays with damage, nor on a play at the other family
(`safe := false`). The play's second word holds the first table's commitment ID, and the same hash
of the copy's root, seeds and answers: that two statements have two such words is a matter of the
hash, not shown. THE TOP THEOREMS ARE THE INSTANCE AT ONE CONVERTER, of which the bound says next to
nothing (the head of EntryHome.lean); what it shares with the other instances is the verdict on the
typed value (`HomeData.chk_iff_why`; OnBytes/TypedOracleCompiler/Slice/EntryRunAny.lean). The checker takes of the
three public files their digest alone; the play's two tests (`stdEntry`, `pinsFit`) are no part of
it; of their clauses the proof uses two. The first table's root and answers are read off the key
file, which nobody checks here. The seeds in the value are those that a play's converter draws at
the two tables' names by the program's own function at the format's hash (`recordSeeds`,
OnBytes/Entry/Table.lean; `convE`, `convLax`, OnBytes/TypedOracleCompiler/Slice/EntryConv.lean); the run's function
says "S" where its comparison of the value's seeds fails (`cmpE`,
OnBytes/TypedOracleCompiler/Slice/EntryJudgeRun.lean; `whyOutE`, EntryRunMain.lean). WHAT A YES OF THE CHECKER IS
WORTH is what the bound says (`HomeData.Left.one_world`, EntryHome.lean): over a uniformly random
oracle, for every converter, under what is left of its debts; OnBytes/TypedOracleCompiler/Slice/EntrySmallTop.lean
discharges them at `homeSmall`, under one hypothesis on codes; at a fixed hash it is a heuristic
step, as with every argument in the random oracle model. NOTHING ON SOUNDNESS IS SHOWN HERE. Nothing
on any hash function. What the heads of EntryRunTie.lean, EntryRunMain.lean, EntryHome.lean,
EntryHomeRun.lean, EntryHomeSmall.lean and EntryRunTop.lean do not claim. The compiler under
OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on definitions of
Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryRunTieX
import OnBytes.TypedOracleCompiler.Slice.EntryHomeSmall

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (SgX View)
open TypedOracleCompiler.Run.PQ (XD bodyS)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open OnBytes.Tie (EntryGround linkAtCfg keyAt)
open OnBytes.Slice (Tab)
open OnBytes.Slice.Shapes (Files FileSpec Size Cfg pubS₀ pubS₁)
open OnBytes.Slice.Shapes.FileSpec (own₀ own₁)
open scoped ENNReal

variable (G : EntryGround)
  (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)

/-- The sizes of a ground: its tables' shape, with a radius. -/
def groundSize (eM : ℕ) : Size := ⟨G.q.link.table, eM⟩

/-- THE LETTERS OF THE ENTRY'S PART, AT A GROUND: the description, the parameter bytes and the
decision that a play takes; the code behind the escape that the run's family takes. -/
def homeOf (eM : ℕ) :
    HomeData (groundSize G eM) (d1Run G.q.link.table.cubeBits G.q.link.table.answers) where
  DX := entryXD G
  ok := hok
  prm := G.bytesAt
  dec := fun c => decRun (linkAtCfg G.q c) G.q.link.table.v G.q.link.table.cubeBits
    G.q.link.table.answers
  back := fun c => EntryRunTop.backOf (entryXD G c) (d1Run _ _)

/-- They are the entry's letters at a ground (`HomeData.ofGround`,
OnBytes/TypedOracleCompiler/Slice/EntryHomeGround.lean), at that decision and that code. -/
theorem homeOf_ofGround (eM : ℕ)
    (hb : (OnBytes.Params.entrySpecOf G.q G.rs ByteArray.empty).base.ok = true) :
    homeOf G hok eM = HomeData.ofGround G (groundSize G eM) (d1Run _ _) hb
      (fun c => decRun (linkAtCfg G.q c) G.q.link.table.v G.q.link.table.cubeBits
        G.q.link.table.answers)
      (fun c => EntryRunTop.backOf (entryXD G c) (d1Run _ _)) := rfl

/-- THE CONVERTER OF A PLAY, as a function of the configuration's digest and the files: the
reading of key file and entry file (strict, or lenient), both tables' seeds, then the typed string.
It is trusted for nothing. It is the play's own text written again, as a term of the part's type of
converters (which has no code); `playE_yes` ties the two. -/
noncomputable def convPlay (eM : ℕ) (lax : Bool) : (homeOf G hok eM).ConvC :=
  fun c _ d =>
    ((if lax then convLax else convE) (linkAtCfg G.q c) (keyAt G.q.link.table c d.key).2.2
      d.ent).bind fun a =>
      (assembleS (entryXD G c)
        (decRun (linkAtCfg G.q c) G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers)
        a.out).map fun π =>
        ([_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root],
          xOfAskedC _ _ a, ofPS _ _ π)

/-- WHAT A PLAY'S "YES" SAYS, UNFOLDED: without damage, at the page's own family: the public
files pass the test; the pins fit; the converter makes a typed value o of the files at the digest of
the three public files; the run's function says "YES" on o; AND THE PLAY'S SECOND WORD IS MADE OF
o's ROOTS, SEEDS AND ANSWERS: the first table's commitment ID, as the format makes it of the digest,
the shape, the root, the seeds and the answers (`stmtId`), and the same hash of the copy's root,
seeds and answers. -/
theorem playE_yes (eM : ℕ) (zS : OnBytes.Params.StdSize) (lax : Bool) (cfg : Cfg) (d : Files)
    (h : (playE G hok zS true lax .none cfg.pol cfg.lay cfg.KL d.key d.ent).1 = "YES") :
    OnBytes.Params.stdEntry zS ⟨cfg.pol, cfg.lay, cfg.KL⟩ = true ∧
      pinsFit (entryXD G (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))
        G.q.link.table = true ∧
      ∃ o, convPlay G hok eM lax (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
          (OnBytes.Params.configurationDigest_size _) d = some o ∧
        whyOutE (entryXD G (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))
          (hok _ (OnBytes.Params.configurationDigest_size _)) (d1Run _ _)
          (decRun (linkAtCfg G.q (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))
            G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers)
          (EntryRunTop.famOf
            (entryXD G (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))
            (OnBytes.Params.configurationDigest_size _) (d1Run _ _) G.q.link.table)
          o.1 o.2.1 (toPS _ _ o.2.2) = "YES" ∧
        (playE G hok zS true lax .none cfg.pol cfg.lay cfg.KL d.key d.ent).2 =
          "first " ++ stmtId G.q.link.table
              (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
              (o.1.getD 0 default) o.2.1.2.1 o.2.1.1.1 ++ " copy " ++
            stmtId G.q.link.table (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
              (o.1.getD 1 default) o.2.1.2.2 o.2.1.1.2 := by
  have h0 := h
  unfold playE prepE at h
  by_cases hs : OnBytes.Params.stdEntry zS ⟨cfg.pol, cfg.lay, cfg.KL⟩ = true
  swap
  · rw [if_neg hs] at h
    have h' : ("C:" ++ "std" : String) = "YES" := h
    exact absurd h' (by decide)
  rw [if_pos hs] at h
  cases hcv : (if lax then convLax else convE)
      (linkAtCfg G.q (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))
      (keyAt G.q.link.table (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
        d.key).2.2 d.ent with
  | none =>
    rw [hcv] at h
    have h' : ("C:" ++ "converter" : String) = "YES" := h
    exact absurd h' (by decide)
  | some a =>
    rw [hcv] at h
    dsimp only at h
    by_cases hp : pinsFit
        (entryXD G (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))
        G.q.link.table = true
    swap
    · rw [Bool.not_eq_true] at hp
      rw [hp] at h
      have h' : ("P" : String) = "YES" := h
      exact absurd h' (by decide)
    rw [hp] at h
    cases has : assembleS
        (entryXD G (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))
        (decRun (linkAtCfg G.q (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]))
          G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers) a.out with
    | none =>
      simp [Dmg.applies, Dmg.onO, has] at h
    | some π =>
      refine ⟨hs, hp, ⟨[_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root],
        xOfAskedC _ _ a, ofPS _ _ π⟩, ?_, ?_, ?_⟩
      · unfold convPlay
        rw [hcv]
        exact congrArg (Option.map fun π =>
          ([_root_.Run.bytesToDig a.first.root, _root_.Run.bytesToDig a.further.root],
            xOfAskedC _ _ a, ofPS _ _ π)) has
      · simpa [Dmg.applies, Dmg.onO, Dmg.onC, Dmg.onX, Dmg.onS, has, famAt] using h
      · clear h h0
        unfold playE prepE
        rw [if_pos hs, hcv]
        dsimp only
        rw [hp]
        simp [Dmg.applies, Dmg.onO, Dmg.onC, Dmg.onX, has]
        rfl

/-- A description that passes the second compiler's test has parameter bytes within the bound of the
format's hash. -/
theorem params_le_of_ok (S : _root_.Fmt.Spec) (h : TypedOracleCompiler.Run.PQ.ok S = true) :
    S.params.size ≤ 2 ^ 32 - 144 := by
  by_contra hn
  have e : decide (S.params.size ≤ 2 ^ 32 - 144) = false := decide_eq_false hn
  unfold TypedOracleCompiler.Run.PQ.ok _root_.Fmt.Spec.ok _root_.Fmt.Spec.small at h
  rw [e] at h
  simp at h

/-- From the test of the pins: the shape's length of a salt is the plan's. -/
theorem salt_of_pinsFit (D : XD) (sh : OnBytes.Params.IndexShape) (h : pinsFit D sh = true) :
    sh.saltBytes = D.base.plan.salt := by
  by_contra hn
  have e : (sh.saltBytes == D.base.plan.salt) = false := beq_false_of_ne hn
  unfold pinsFit at h
  rw [e] at h
  simp at h

/-- At a ground the parameter bytes are the description's, at every digest. -/
theorem homeOf_prm (eM : ℕ) (c : ByteArray) :
    (homeOf G hok eM).prm c = ((homeOf G hok eM).DX c).base.params := rfl

/-- FROM THE FACTS THAT A PLAY'S "YES" HOLDS TO THE CHECKER, at any digest c of 32 bytes: c is
the digest that the oracle's own first table holds; its second table holds the pin that a run
computes; the pins fit; the converter makes o of the files; the run's function says "YES" on o. Then
the checker returns a value whose statement with the seeds (`HomeData.stmtX`,
OnBytes/TypedOracleCompiler/Slice/EntryRunTieX.lean: the two roots, both tables' answers and seeds) is o's. -/
theorem checker_of_facts (eM : ℕ) (lax : Bool) (cfg : Cfg) (d : Files) (εs : ℝ≥0∞) (Bk : ℕ)
    (c : ByteArray) (h32 : c.size = 32)
    (hc : c = OnBytes.Slice.Shapes.dgOf cfg (own₀ (pubS₀ cfg) _root_.Run.oBits))
    (hpd : own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) _root_.Run.oBits
      (OnBytes.Slice.s0Of ((homeOf G hok eM).prm c)) =
        EntryRunTop.pdOf ((homeOf G hok eM).DX c))
    (hp : pinsFit (entryXD G c) G.q.link.table = true) (o : (homeOf G hok eM).OutC c h32)
    (ho : convPlay G hok eM lax c h32 d = some o)
    (hy : whyOutE (entryXD G c) (hok c h32) (d1Run _ _)
      (decRun (linkAtCfg G.q c) G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers)
      (EntryRunTop.famOf (entryXD G c) h32 (d1Run _ _) G.q.link.table) o.1 o.2.1
      (toPS _ _ o.2.2) = "YES") :
    (((((homeOf G hok eM).spec cfg ((homeOf G hok eM).convOf cfg (convPlay G hok eM lax)) εs
      Bk).toO (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg)
      (own₀ (pubS₀ cfg) _root_.Run.oBits)
      (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) _root_.Run.oBits)).chk d).det
        _root_.Run.oBits).map
          (fun o' : (homeOf G hok eM).Out cfg (own₀ (pubS₀ cfg) _root_.Run.oBits)
            (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) _root_.Run.oBits) =>
              HomeData.stmtX o') = some (HomeData.stmtX o) :=
  (homeOf G hok eM).yes_of_runX cfg (convPlay G hok eM lax) G.q.link.table εs Bk d c h32 hc
    ⟨rfl, hpd, rfl, salt_of_pinsFit _ _ hp, rfl⟩ h32 o ho hy

/-- A PLAY'S "YES" IS A YES OF THE CHECKER OF WHICH THE BOUND SPEAKS, AT THE ORACLE MADE FROM THE
FORMAT'S HASH, ON THE STATEMENT THAT THE PLAY GIVES OUT. For every ground G whose descriptions
pass the second compiler's test, every radius, either converter, all public files and all files: IF
the play without damage, at the page's own family, says "YES", THEN there is a statement st (two
roots, both tables' answers and seeds) such that the checker "pre-process by that play's converter,
then the compiled verifier", at the ground's sizes, returns under that oracle a value on these files
whose statement with the seeds (`HomeData.stmtX`) is st, and the play's second word is made of st:
the first table's commitment ID, and the same hash of the copy's root, seeds and answers. NO OTHER
HYPOTHESIS. Of the checker at this one converter the bound says next to nothing (the head). -/
theorem play_yes_checker (eM : ℕ) (zS : OnBytes.Params.StdSize) (lax : Bool) (cfg : Cfg)
    (d : Files) (εs : ℝ≥0∞) (Bk : ℕ)
    (h : (playE G hok zS true lax .none cfg.pol cfg.lay cfg.KL d.key d.ent).1 = "YES") :
    ∃ st : List (Dig 256) × XE (List T3) G.q.link.table.cubeBits G.q.link.table.answers,
      (((((homeOf G hok eM).spec cfg ((homeOf G hok eM).convOf cfg (convPlay G hok eM lax)) εs
        Bk).toO (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg)
        (own₀ (pubS₀ cfg) _root_.Run.oBits)
        (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) _root_.Run.oBits)).chk d).det
          _root_.Run.oBits).map
            (fun o' : (homeOf G hok eM).Out cfg (own₀ (pubS₀ cfg) _root_.Run.oBits)
              (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) _root_.Run.oBits) =>
                HomeData.stmtX o') = some st ∧
      (playE G hok zS true lax .none cfg.pol cfg.lay cfg.KL d.key d.ent).2 =
        "first " ++ stmtId G.q.link.table
            (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
            (st.1.getD 0 default) st.2.2.1 st.2.1.1 ++ " copy " ++
          stmtId G.q.link.table (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
            (st.1.getD 1 default) st.2.2.2 st.2.1.2 := by
  obtain ⟨hs, hp, o, ho, hy, h2⟩ := playE_yes G hok eM zS lax cfg d h
  have hb := OnBytes.Params.stdEntry_bytes hs
  refine ⟨HomeData.stmtX o, ?_, h2⟩
  exact checker_of_facts G hok eM lax cfg d εs Bk _ (OnBytes.Params.configurationDigest_size _)
    (OnBytes.Slice.Shapes.dgOf_own₀ cfg hb).symm
    ((homeOf G hok eM).pd_own₁ cfg hb
      (params_le_of_ok _ (hok _ (OnBytes.Params.configurationDigest_size _)))
      (homeOf_prm G hok eM _)) hp o ho hy

/-! ## At the small example -/

/-- The sizes of the small example's ground, at the small radius, are the small sizes
(OnBytes/TypedOracleCompiler/Slice/ShapesAtSmall.lean). -/
theorem groundSize_small :
    groundSize OnBytes.Tie.smallRecordGround OnBytes.Params.smallRecordRadius =
      OnBytes.Slice.Shapes.zSmall := rfl

/-- THE ENTRY'S LETTERS AT THE SMALL EXAMPLE: `HomeData.ofGround` at the small ground and the
small sizes: the instance at which OnBytes/TypedOracleCompiler/Slice/EntryHomeSmall.lean discharges the fields on
numbers of what is left of the bound's debts (`left_small`); with the decision and the code that a
play takes. -/
def homeSmall : HomeData OnBytes.Slice.Shapes.zSmall
    (d1Run OnBytes.Slice.Shapes.zSmall.lg OnBytes.Slice.Shapes.zSmall.s) :=
  HomeData.ofGround OnBytes.Tie.smallRecordGround OnBytes.Slice.Shapes.zSmall (d1Run _ _)
    small_base_ok
    (fun c => decRun (linkAtCfg OnBytes.Tie.smallRecordGround.q c) OnBytes.Slice.Shapes.zSmall.v
      OnBytes.Slice.Shapes.zSmall.lg OnBytes.Slice.Shapes.zSmall.s)
    (fun c => EntryRunTop.backOf (entryXD OnBytes.Tie.smallRecordGround c) (d1Run _ _))

/-- It is `homeOf` at the small ground and the small radius. -/
theorem homeOf_small :
    homeOf OnBytes.Tie.smallRecordGround small_record_ok OnBytes.Params.smallRecordRadius =
      homeSmall := rfl

/-- The converter of a play at the small example. -/
noncomputable def convSmall (lax : Bool) : homeSmall.ConvC :=
  convPlay OnBytes.Tie.smallRecordGround small_record_ok OnBytes.Params.smallRecordRadius lax

/-- AT THE SMALL EXAMPLE: IF THE PLAY WITHOUT DAMAGE, AT THE PAGE'S OWN FAMILY, SAYS "YES" ON THE
PUBLIC FILES cfg, THE KEY FILE AND THE ENTRY FILE, THEN THE CHECKER OF WHICH THE BOUND SPEAKS, at
the small sizes and at that play's converter, RETURNS UNDER THE ORACLE MADE FROM THE FORMAT'S HASH A
VALUE ON THESE FILES WHOSE STATEMENT st (two roots, both tables' answers and seeds) IS THE ONE OF
WHICH THE PLAY'S SECOND WORD IS MADE. No other hypothesis. Of the checker at this one converter the
bound says next to nothing (the head). -/
theorem playSmall_yes_checker (lax : Bool) (cfg : Cfg) (d : Files) (εs : ℝ≥0∞) (Bk : ℕ)
    (h : (playSmall true lax .none cfg.pol cfg.lay cfg.KL d.key d.ent).1 = "YES") :
    ∃ st : List (Dig 256) ×
        XE (List T3) OnBytes.Slice.Shapes.zSmall.lg OnBytes.Slice.Shapes.zSmall.s,
      ((((homeSmall.spec cfg (homeSmall.convOf cfg (convSmall lax)) εs Bk).toO (pubS₀ cfg)
        (pubS₁ [homeSmall.prm] cfg) (own₀ (pubS₀ cfg) _root_.Run.oBits)
        (own₁ (pubS₀ cfg) (pubS₁ [homeSmall.prm] cfg) _root_.Run.oBits)).chk d).det
          _root_.Run.oBits).map
            (fun o' : homeSmall.Out cfg (own₀ (pubS₀ cfg) _root_.Run.oBits)
              (own₁ (pubS₀ cfg) (pubS₁ [homeSmall.prm] cfg) _root_.Run.oBits) =>
                HomeData.stmtX o') = some st ∧
      (playSmall true lax .none cfg.pol cfg.lay cfg.KL d.key d.ent).2 =
        "first " ++ stmtId OnBytes.Tie.smallRecordGround.q.link.table
            (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
            (st.1.getD 0 default) st.2.2.1 st.2.1.1 ++ " copy " ++
          stmtId OnBytes.Tie.smallRecordGround.q.link.table
            (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
            (st.1.getD 1 default) st.2.2.2 st.2.1.2 :=
  play_yes_checker OnBytes.Tie.smallRecordGround small_record_ok OnBytes.Params.smallRecordRadius
    OnBytes.Params.stdSmall lax cfg d εs Bk h

end TypedOracleCompiler.Slice
