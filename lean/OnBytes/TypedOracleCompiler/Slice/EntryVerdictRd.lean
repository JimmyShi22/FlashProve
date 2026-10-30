-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryVerdictRd.lean: "parse, then check" for an entry file, the hash function an
argument, and that at every hash function and every parser its yes is a yes of the checker of the
entry's part at the converter made of that parser.

Definitions, and one statement with its proof. In `verifyEntryG_iff`
(OnBytes/TypedOracleCompiler/Slice/EntryVerdictG.lean) the converter holds the parsed value a, so a is fixed before
the function. Here a is read off the files by a parser rd : `Files → Option AskedE`, a letter: any
plain function that is not given g. The files may then be made by whoever has asked the function
first.

Main names (namespace `TypedOracleCompiler.Slice`):
  `verifyEntryOf G hok rd cfg d g` : Bool: no where rd refuses d; else `verifyEntryG` at what rd
    returns.
  `convRd G hok eM rd`: the converter made of rd: parse, then the typing of `valueOf`
    (OnBytes/TypedOracleCompiler/Slice/EntryVerdict.lean). It has no code; it stands in the statement alone.
  `verifyEntryOf_iff`: at every g, rd and all files d: `verifyEntryOf` says yes exactly if the pins
    fit and the checker "convert; two roots; the judge's run" of the entry's part `homeOf G hok eM`,
    at `convRd`, returns a value on d under g.

Limits.
  1. rd is not given g, nor g's digest of the three public files (a converter of type
     `HomeData.ConvC` is given that digest; `convPlay` uses it and is not of this form). By its type
     rd may still hold a fixed hash function as a constant: `convE`
     (OnBytes/TypedOracleCompiler/Slice/EntryConv.lean) at a written digest is such an rd. At such an rd a bound
     over a random function says next to nothing: the seeds in what rd returns are that fixed
     function's, and the check compares them with g's. The form is worth something at an rd that
     only decodes. A parser that asks g is not of this form: its asking belongs to whoever makes the
     files and counts among that maker's queries, and what it hands over has to stand in the files.
  2. G, hok and eM are letters; no bound is joined here (OnBytes/TypedOracleCompiler/Slice/EntryVerdictBound.lean).
     No yes is shown.
  3. `verifyEntryOf` stands on `verifyEntryG`, not on the form for a run, and has none of the tests
     on the parsed value (`verifyEntryO`, `askedFit`: OnBytes/TypedOracleCompiler/Slice/EntryVerdictRun.lean). No
     closed term that takes rd and the files is given here.
  4. All that the head of EntryVerdictG.lean does not claim. No probability stands here. Nothing on
     soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryVerdictG

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD bodyS)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open OnBytes.Tie (EntryGround linkAtCfg keyAt AskedE)
open OnBytes.Slice (Tab s0Of)
open OnBytes.Slice.Shapes (Files FileSpec Size Cfg dgOf dgOf_size pubS₀ pubS₁)
open OnBytes.Slice.Shapes.FileSpec (own₀ own₁)
open scoped ENNReal

variable (G : EntryGround)
  (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)

/-- Parse, then check: rd is any plain function from the files to the plain data that the check
reads; it is not given g. -/
def verifyEntryOf (rd : Files → Option AskedE) (cfg : Cfg) (d : Files) (g : Fam (rom 256)) : Bool :=
  match rd d with
  | none => false
  | some a => verifyEntryG G hok cfg a g

/-- The converter that is made of rd: parse, then the typing of `valueOf`. -/
noncomputable def convRd (eM : ℕ) (rd : Files → Option AskedE) : (homeOf G hok eM).ConvC :=
  fun c hc d => (rd d).bind fun a => valueOf G hok eM a c hc d

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- At every g, every rd and all files d: "parse, then check" says yes exactly if the pins fit and
the checker of the entry's part at the ground G, at the converter made of rd, returns a value on d
under g. -/
theorem verifyEntryOf_iff (eM : ℕ) (rd : Files → Option AskedE) (cfg : Cfg) (εs : ℝ≥0∞) (Bk : ℕ)
    (g : Fam (rom 256)) (d : Files) :
    verifyEntryOf G hok rd cfg d g = true ↔
      pinsFit (entryXD G (dgOf cfg (own₀ (pubS₀ cfg) g))) G.q.link.table = true ∧
        ∃ o, ((((homeOf G hok eM).spec cfg ((homeOf G hok eM).convOf cfg (convRd G hok eM rd)) εs
          Bk).toO (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) (own₀ (pubS₀ cfg) g)
          (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) g)).chk d).det g = some o := by
  have pins : pinsFit (entryXD G (dgOf cfg (own₀ (pubS₀ cfg) g))) G.q.link.table = true →
      (homeOf G hok eM).PinsAtG G.q.link.table (dgOf cfg (own₀ (pubS₀ cfg) g)) := fun hp =>
    ⟨rfl, rfl, salt_of_pinsFit _ _ hp, rfl⟩
  unfold verifyEntryOf
  cases hr : rd d with
  | none =>
    constructor
    · intro h
      exact absurd h Bool.false_ne_true
    · rintro ⟨hp, o, ho⟩
      have h1 := (((homeOf G hok eM).chk_iff_whyG cfg
        ((homeOf G hok eM).convOf cfg (convRd G hok eM rd)) εs Bk g d o G.q.link.table (pins hp)
        (dgOf_size cfg (own₀ (pubS₀ cfg) g))).1 ho).1
      have h2 : (rd d).bind (fun a => valueOf G hok eM a (dgOf cfg (own₀ (pubS₀ cfg) g))
          (dgOf_size cfg (own₀ (pubS₀ cfg) g)) d) = some o := h1
      rw [hr] at h2
      cases h2
  | some a =>
    dsimp only
    rw [verifyEntryG_iff G hok eM cfg a εs Bk g d]
    refine and_congr_right fun hp => exists_congr fun o => ?_
    have e : (homeOf G hok eM).convOf cfg (convRd G hok eM rd) (own₀ (pubS₀ cfg) g)
        (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) g) d =
        (homeOf G hok eM).convOf cfg (valueOf G hok eM a) (own₀ (pubS₀ cfg) g)
        (own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) g) d := by
      show (rd d).bind _ = _
      rw [hr]
      rfl
    refine ((homeOf G hok eM).chk_iff_whyG cfg ((homeOf G hok eM).convOf cfg (valueOf G hok eM a))
      εs Bk g d o G.q.link.table (pins hp) (dgOf_size cfg (own₀ (pubS₀ cfg) g))).trans
      (Iff.trans ?_ ((homeOf G hok eM).chk_iff_whyG cfg
        ((homeOf G hok eM).convOf cfg (convRd G hok eM rd)) εs Bk g d o G.q.link.table (pins hp)
        (dgOf_size cfg (own₀ (pubS₀ cfg) g))).symm)
    rw [e]

end TypedOracleCompiler.Slice
