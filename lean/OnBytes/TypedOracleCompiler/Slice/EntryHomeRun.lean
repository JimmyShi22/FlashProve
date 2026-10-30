-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryHomeRun.lean: the checker of the bound gives out the value of one written
term, the pipeline at the two digests as they are computed.

OnBytes/TypedOracleCompiler/Slice/EntryHome.lean has the entry file's checker "pre-process, then the judge's run" at
written terms, its bound for every converter, and the checker's value under an oracle
(`chk_eq_runF`). There the part stands at the digests that the oracle's own public values hold:
terms that hang on the oracle, and on which the description, the type of typed values and the page
hang by type. This file says the part as a function of two digests, and carries the checker's value
to them.

Main definitions.
 `HomeData.atC c hc pd rts` the part but for its checker, at a configuration's digest c of 32 bytes
     and a parameter digest pd. `atR_eq`: `atR` is this at the digests that two tables hold, by
     unfolding.
 `HomeData.ConvC`, `convOf` a converter that knows of the oracle the configuration's digest alone;
     it as a converter over two tables.
 `HomeData.stmt` THE STATEMENT in an accepted value: the two roots, both tables' answers. Its type
     hangs on no digest.
 `HomeData.runC k g c hc pd d` the pipeline as one written term: convert; refuse unless there are
     two roots; the judge's run as a plain truth value (`judgeRunELF`) under the family read out of
     g through the page at (c, pd); give out the statement.
Main theorems.
 `chk_eq_runC` under every oracle g, at whatever two digests g's own public values hold, the checker
     of which the bound speaks gives out `runC`'s value.
 `chk_eq_run_oBits` at the oracle made from the format's hash these are the format's own
     configuration digest and parameter digest (`dgOf_own₀`, `own₁_at`,
     OnBytes/TypedOracleCompiler/Slice/ShapesPub.lean).

What is not claimed. THAT ANY PROGRAM THAT HAS BEEN RUN EVALUATES `runC`: no `HomeData` and no
converter is defined here, and no theorem here has a program's function on one side. That `runC` can
be evaluated: `readBlocks`, the page and the oracle made from the format's hash are no programs
here, and the five letters of `HomeData` and the converter must have code. That it returns a value
on anything. The bound is for every converter over two tables; the converters here are some of
these. The two bounds on sizes are asked, not shown. The limits of OnBytes/TypedOracleCompiler/Slice/EntryHome.lean
stand.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryHome

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open Rom Prob Cb _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (SgX View)
open TypedOracleCompiler.Run.PQ (XD bodyS)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open OnBytes.Slice (seedEntry Tab s0Of)
open OnBytes.Slice.Shapes (Files FileSpec Size Cfg dgOf dgOf_size pubS₀ pubS₁)
open OnBytes.Slice.Shapes.FileSpec (own₀ own₁)
open scoped ENNReal

namespace HomeData
variable {z : Size} {d₁ : Sd1 z.lg z.s} [DecidableEq (Sd1 z.lg z.s)] (H : HomeData z d₁)

/-- THE ENTRY's PART BUT FOR ITS CHECKER, AS A FUNCTION OF TWO DIGESTS: c, the configuration's,
of 32 bytes; pd, the entry's parameter bytes'. `HomeData.atR` is this at the digests that two tables
hold (`atR_eq`). -/
def atC (c : ByteArray) (hc : c.size = 32) (pd : Dig 256) (rts : Files → List (Dig 256)) :
    EntryAt (List T3) z.lg z.s d₁ :=
  EntryClean.atPage (H.DX c) (bodyS (H.DX c).a (H.DX c).base.plan.salt)
    (ownES (H.DX c) (H.ok c hc)) (H.dec c)
    (entryR (H.DX c) _ (ownES (H.DX c) (H.ok c hc)) (earlyTwo d₁)
      (TSE (H.DX c) (seedEntry z.lg z.s)) (wTSE (H.DX c) (seedEntry z.lg z.s))
      (embST (H.DX c).C (seedEntry z.lg z.s) _) (prjST (H.DX c).C (seedEntry z.lg z.s) _))
    rts c hc pd
    (TypedOracleCompiler.Run.FirstName.restOf c z.T.a z.T.l z.T.r z.v z.s z.shape.saltBytes)
    (8 * z.shape.saltBytes) (H.back c)

omit [DecidableEq (Sd1 z.lg z.s)] in
/-- `atR` is `atC` at the digests that the two tables hold. -/
theorem atR_eq (cfg : Cfg) (rts : Files → List (Dig 256)) (T₀ T₁ : Tab) :
    H.atR cfg rts T₀ T₁ =
      H.atC (dgOf cfg T₀) (dgOf_size cfg T₀) (T₁ (s0Of (H.prm (dgOf cfg T₀)))) rts := rfl

/-- What the typed verifier takes in, at a configuration's digest. -/
abbrev OutC (c : ByteArray) (hc : c.size = 32) : Type := OutE (H.atC c hc default fun _ => []).Z

/-- A converter that knows of the oracle the configuration's digest alone. -/
abbrev ConvC : Type := ∀ c (hc : c.size = 32), Files → Option (H.OutC c hc)

/-- It as a converter over two tables. -/
def convOf (cfg : Cfg) (k : H.ConvC) : H.Conv cfg :=
  fun T₀ _ => k (dgOf cfg T₀) (dgOf_size cfg T₀)

/-- THE STATEMENT IN AN ACCEPTED VALUE: the two roots; both tables' answers. -/
def stmt {γ δ : Type} (o : List (Dig 256) × ((List T3 × List T3) × γ) × δ) :
    List (Dig 256) × (List T3 × List T3) := (o.1, o.2.1.1)

/-- THE PIPELINE AS ONE WRITTEN TERM, AT TWO DIGESTS AND AN ORACLE g: convert; refuse unless
there are two roots; run the judge (both tables' seeds against the seeds' chain, then the lax
verifier) under the family that is read out of g through the page at the two digests; GIVE OUT THE
STATEMENT of what was accepted. A definition: that any program evaluates this term is not said here.
-/
def runC (k : H.ConvC) (g : Fam (rom 256)) (c : ByteArray) (hc : c.size = 32) (pd : Dig 256)
    (d : Files) : Option (List (Dig 256) × (List T3 × List T3)) :=
  ((((k c hc d).filter fun o => decide (o.1.length = 2)).bind fun o =>
    if judgeRunELF (H.DX c) (H.dec c) (bodyS (H.DX c).a (H.DX c).base.plan.salt)
        (ownES (H.DX c) (H.ok c hc)) (earlyTwo d₁) (seedEntry z.lg z.s)
        (OnBytes.Slice.seedOfDrawnC z.lg z.s)
        (readBlocks (H.atC c hc pd fun _ => []).m g) o = true then some o else none).map stmt)

set_option maxRecDepth 20000 in
/-- THE CHECKER OF WHICH THE BOUND SPEAKS GIVES OUT `runC`'s VALUE, under every oracle g,
at whatever two digests g's own public values hold. -/
theorem chk_eq_runC (cfg : Cfg) (k : H.ConvC) (εs : ℝ≥0∞) (Bk : ℕ) (g : Fam (rom 256)) (d : Files)
    (c : ByteArray) (hc : c.size = 32) (pd : Dig 256)
    (h₀ : dgOf cfg (own₀ (pubS₀ cfg) g) = c)
    (h₁ : own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g (s0Of (H.prm c)) = pd) :
    ((((H.spec cfg (H.convOf cfg k) εs Bk).toO (pubS₀ cfg) (pubS₁ [H.prm] cfg)
      (own₀ (pubS₀ cfg) g) (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g)).chk d).det g).map
        (fun o : H.Out cfg (own₀ (pubS₀ cfg) g) (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) g) =>
          stmt o) = H.runC k g c hc pd d := by
  subst h₀
  subst h₁
  unfold runC
  rw [chk_eq_runF]
  rfl

omit [DecidableEq (Sd1 z.lg z.s)] in
/-- The configuration's digest has 32 bytes. -/
theorem cfgDigest_size (cfg : Cfg)
    (hb : (_root_.Fmt.configBytes [cfg.pol, cfg.lay, cfg.KL]).size ≤ 2 ^ 32 - 144) :
    (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL]).size = 32 := by
  rw [← OnBytes.Slice.Shapes.dgOf_own₀ cfg hb]
  exact dgOf_size cfg _

/-- AT THE ORACLE MADE FROM THE FORMAT's HASH THE TWO DIGESTS ARE THE FORMAT's OWN: the
configuration's digest of the three configuration files, and the parameter digest of the entry's
parameter bytes at it. So the written term `runC` at that hash, at these two digests as they are
computed, gives out what the checker of the bound gives out. Asked: what is hashed for the
two digests has at most 2^32 - 144 bytes. -/
theorem chk_eq_run_oBits (cfg : Cfg) (k : H.ConvC) (εs : ℝ≥0∞) (Bk : ℕ) (d : Files)
    (hb : (_root_.Fmt.configBytes [cfg.pol, cfg.lay, cfg.KL]).size ≤ 2 ^ 32 - 144)
    (hb' : (H.prm (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])).size ≤
      2 ^ 32 - 144) :
    ((((H.spec cfg (H.convOf cfg k) εs Bk).toO (pubS₀ cfg) (pubS₁ [H.prm] cfg)
      (own₀ (pubS₀ cfg) _root_.Run.oBits)
      (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) _root_.Run.oBits)).chk d).det _root_.Run.oBits).map
        (fun o : H.Out cfg (own₀ (pubS₀ cfg) _root_.Run.oBits)
          (own₁ (pubS₀ cfg) (pubS₁ [H.prm] cfg) _root_.Run.oBits) => stmt o) =
      H.runC k _root_.Run.oBits (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])
        (cfgDigest_size cfg hb)
        (_root_.Run.bytesToDig (_root_.Fmt.paramsDigest
          (H.prm (OnBytes.Params.configurationDigest [cfg.pol, cfg.lay, cfg.KL])))) d :=
  H.chk_eq_runC cfg k εs Bk _root_.Run.oBits d _ (cfgDigest_size cfg hb) _
    (OnBytes.Slice.Shapes.dgOf_own₀ cfg hb) (by
      rw [← OnBytes.Slice.Shapes.own₁_at cfg [H.prm] H.prm (List.mem_singleton.2 rfl) hb hb',
        _root_.Run.TieTree.bytes_dig])

end HomeData

end TypedOracleCompiler.Slice
