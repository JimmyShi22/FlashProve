-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntrySpells.lean: the field `spells` of what is left of the entry's bound's debts
(`HomeData.Left`, OnBytes/TypedOracleCompiler/Slice/EntryHome.lean) IS PAID: the page of the entry's part at written
terms spells vertices and stored leaves as the one written reading reads them; general in the
letters, at a ground, at the full size and at the small sizes.

WHICH CODE BEHIND THE ESCAPE. `atRead_spells` (OnBytes/TypedOracleCompiler/Slice/EntryReadsAt.lean) shows the
spelling at one code behind the escape, `EntryReadsAt.bk`, at any serialiser of what stands in the
seeds' place. The code that a run's family takes (`EntryRunTop.backOf`,
OnBytes/TypedOracleCompiler/Slice/EntryRunTop.lean) is that code, at the plan's length of a salt and the written
serialiser `PageESer.serSd2`: by unfolding. SO THE BOUND AND A RUN STAND AT ONE CODE: `fun c =>
EntryRunTop.backOf (entryXD G c) d₁`.

Main theorems.
 `backOf_bk`            the two codes are one.
 `HomeData.spells_of`   THE FIELD, from three equations at digests of 32 bytes: the sizes' length of
                        a salt is the plan's; the depth of the description's stored tables is the
                        code's; the code behind the escape is `bk` at the plan's length of a salt.
 `spells_ground`        at a ground, with the code that a run's family takes: from the first two
                        equations.
 `full_spells`, `small_spells`   THE HYPOTHESIS `spells` OF `left_full` AND OF `left_small`
                        (OnBytes/TypedOracleCompiler/Slice/EntryHomeFull.lean, EntryHomeSmall.lean), at that code,
                        for every decision, every fixed value in the seeds' place, all configuration
                        files, all tables. No hypothesis.

Not claimed. The two other hypotheses of `left_full` and `left_small`: soundness record by record;
the typed verifier's count. At another code behind the escape nothing is said. NOTHING ON SOUNDNESS
IS SHOWN. What the heads of EntryReadsAt.lean, ShapesReads.lean, EntryHome.lean, EntryHomeFull.lean
and EntryHomeSmall.lean do not claim. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryHomeFull
import OnBytes.TypedOracleCompiler.Slice.EntryHomeSmall
import OnBytes.TypedOracleCompiler.Slice.EntryReadsAt
import OnBytes.TypedOracleCompiler.Slice.EntryRunTop

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (SgX View)
open TypedOracleCompiler.Run.PQ (XD bodyS)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open OnBytes.Tie (EntryGround recordGround smallRecordGround)
open OnBytes.Slice (Tab)
open OnBytes.Slice.Shapes (Files Size Cfg dgOf dgOf_size Spells zFull zSmall)
open scoped ENNReal

/-- The code behind the escape that a run's family takes is the code at which the page is shown to
spell: at the plan's length of a salt and the written serialiser of both tables' seeds. -/
theorem backOf_bk {lg s : ℕ} (D : XD) (d₁ : Sd1 lg s) :
    EntryRunTop.backOf D d₁ =
      EntryReadsAt.bk (d₁ := d₁) D D.base.plan.salt (PageESer.serSd2 lg s) := rfl

namespace HomeData
variable {z : Size} {d₁ : Sd1 z.lg z.s} [DecidableEq (Sd1 z.lg z.s)] (H : HomeData z d₁)
  (cfg : Cfg)

/-- THE FIELD `spells` OF WHAT IS LEFT OF THE BOUND'S DEBTS (`HomeData.Left`,
OnBytes/TypedOracleCompiler/Slice/EntryHome.lean), from three equations at digests of 32 bytes: the sizes' length of
a salt is the plan's; the depth of the description's stored tables is the code's; the code behind
the escape is `EntryReadsAt.bk` at the plan's length of a salt, at some serialiser ss of what stands
in the seeds' place. By `atRead_spells` (OnBytes/TypedOracleCompiler/Slice/EntryReadsAt.lean). -/
theorem spells_of (ss : Ser (Sd1 z.lg z.s × Sd1 z.lg z.s))
    (hsalt : ∀ c, c.size = 32 → z.shape.saltBytes = (H.DX c).base.plan.salt)
    (hdepth : ∀ c, c.size = 32 → (H.DX c).a = z.T.a)
    (hback : ∀ c, c.size = 32 →
      H.back c = EntryReadsAt.bk (d₁ := d₁) (H.DX c) (H.DX c).base.plan.salt ss)
    (T₀ T₁ : Tab) :
    Spells (H.atR cfg (fun _ => []) T₀ T₁).m
      (bodyS (H.DX (dgOf cfg T₀)).a (H.DX (dgOf cfg T₀)).base.plan.salt).embE (dgOf cfg T₀) z.T.a
      z.shape.saltBytes := by
  have hc := dgOf_size cfg T₀
  show Spells (EntryFill.pageForE (H.DX (dgOf cfg T₀)) d₁ (dgOf cfg T₀) hc _ _
    (8 * z.shape.saltBytes) (H.back (dgOf cfg T₀))) _ _ _ _
  rw [hback _ hc, hsalt _ hc, ← hdepth _ hc]
  exact EntryReadsAt.atRead_spells (d₁ := d₁) (H.DX (dgOf cfg T₀))
    (H.DX (dgOf cfg T₀)).base.plan.salt (ownES (H.DX (dgOf cfg T₀)) (H.ok _ hc))
    (H.dec (dgOf cfg T₀))
    (EntryReadsAt.rdW (d₁ := d₁) (H.DX (dgOf cfg T₀)) (H.DX (dgOf cfg T₀)).base.plan.salt
      (ownES (H.DX (dgOf cfg T₀)) (H.ok _ hc)))
    (fun _ => []) (dgOf cfg T₀) hc _ _ ss z.T z.v z.eM (anT z.v z.s) 0

end HomeData

/-- AT A GROUND, with the code behind the escape that a run's family takes
(`EntryRunTop.backOf`): from two equations: the sizes' length of a salt is the ground's plan's; the
depth of the description's stored tables is the code's. -/
theorem spells_ground (G : EntryGround) (z : Size) (d₁ : Sd1 z.lg z.s)
    [DecidableEq (Sd1 z.lg z.s)]
    (hb : (OnBytes.Params.entrySpecOf G.q G.rs ByteArray.empty).base.ok = true)
    (dec : ByteArray → XE (List T3) z.lg z.s → View → Bool) (cfg : Cfg)
    (hsalt : z.shape.saltBytes = G.q.given.plan.salt)
    (hdepth : ∀ c, (entryXD G c).a = z.T.a) (T₀ T₁ : Tab) :
    Spells ((HomeData.ofGround G z d₁ hb dec fun c => EntryRunTop.backOf (entryXD G c) d₁).atR cfg
        (fun _ => []) T₀ T₁).m
      (bodyS (entryXD G (dgOf cfg T₀)).a (entryXD G (dgOf cfg T₀)).base.plan.salt).embE
      (dgOf cfg T₀) z.T.a z.shape.saltBytes :=
  (HomeData.ofGround G z d₁ hb dec fun c => EntryRunTop.backOf (entryXD G c) d₁).spells_of cfg
    (PageESer.serSd2 z.lg z.s) (fun _ _ => hsalt) (fun c _ => hdepth c)
    (fun c _ => backOf_bk (entryXD G c) d₁) T₀ T₁

/-- AT THE FULL SIZE: the hypothesis `spells` of `left_full`
(OnBytes/TypedOracleCompiler/Slice/EntryHomeFull.lean), at that code, for every decision. -/
theorem full_spells (d₁ : Sd1 zFull.lg zFull.s) [DecidableEq (Sd1 zFull.lg zFull.s)]
    (dec : ByteArray → XE (List T3) zFull.lg zFull.s → View → Bool) (cfg : Cfg) (T₀ T₁ : Tab) :
    Spells ((HomeData.ofGround recordGround zFull d₁ full_base_ok dec
        fun c => EntryRunTop.backOf (entryXD recordGround c) d₁).atR cfg (fun _ => []) T₀ T₁).m
      (bodyS (entryXD recordGround (dgOf cfg T₀)).a
        (entryXD recordGround (dgOf cfg T₀)).base.plan.salt).embE (dgOf cfg T₀) zFull.T.a
      zFull.shape.saltBytes :=
  spells_ground recordGround zFull d₁ full_base_ok dec cfg rfl full_depthIs T₀ T₁

/-- AT THE SMALL SIZES: the hypothesis `spells` of `left_small`
(OnBytes/TypedOracleCompiler/Slice/EntryHomeSmall.lean). -/
theorem small_spells (d₁ : Sd1 zSmall.lg zSmall.s) [DecidableEq (Sd1 zSmall.lg zSmall.s)]
    (dec : ByteArray → XE (List T3) zSmall.lg zSmall.s → View → Bool) (cfg : Cfg)
    (T₀ T₁ : Tab) :
    Spells ((HomeData.ofGround smallRecordGround zSmall d₁ small_base_ok dec
        fun c => EntryRunTop.backOf (entryXD smallRecordGround c) d₁).atR cfg (fun _ => []) T₀
        T₁).m
      (bodyS (entryXD smallRecordGround (dgOf cfg T₀)).a
        (entryXD smallRecordGround (dgOf cfg T₀)).base.plan.salt).embE (dgOf cfg T₀) zSmall.T.a
      zSmall.shape.saltBytes :=
  spells_ground smallRecordGround zSmall d₁ small_base_ok dec cfg rfl small_depthIs T₀ T₁

end TypedOracleCompiler.Slice
