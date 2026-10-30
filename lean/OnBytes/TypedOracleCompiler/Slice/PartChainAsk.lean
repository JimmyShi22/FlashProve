-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/PartChainAsk.lean: the entry's checker that asks, with the sibling's compiled Link
verifier behind it, as one part of a join: `Part.OK` over the sibling, and so the line's `PartO.OK`;
for every description. The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is
made with; it builds on definitions of Compile/.

"The line": the files of OnBytes/Slice/ and OnBytes/Tie/, over the library's compiler.

After OnBytes/Slice/TopAny.lean (`SoundLAny`, `linkAt_any`) and OnBytes/Slice/JudgeLink.lean
(`partChain`, `partChain_bound`).
`Part`, `Part.OK`,
`Part.toO`, `Part.toO_ok`, `Part.on`, `Part.on_ok_of` are those of OnBytes/TypedOracleCompiler/Slice/Part.lean and
PartOn.lean; `Part.toO` goes into the line's `PartO`, which names no typed family.

AS TEXT but for names and the arguments on bodies (2). `SoundLT` (the original's `SoundLAny`),
`linkAt_any` (the condition on work is said member by member, where the original has the library's
test on its list).
THE PART (6). `partChainAsk_chk_det`, `partChainAsk_roots`, and:
 `partChainAsk0`      written out; the two conditions of
                      `okgAny` are arguments.
 `partChainAsk`       at B, Lf, E.
 `partChainAsk_ok`    `FitsS`, `OwnFits` and `hi` are asked;
                      that statements are short is not asked: it follows
                      from the checker's own test.
 `partChainAsk_bound` the bound written out.
NEW (3).
 `LangT`, `tVAny`     short names: the type of a language at a description's interface; the
                      sibling's bound on the Link verifier's queries at the description's wiring.
 `partChainAskO_ok`   `PartO.OK` of the line, by `Part.toO_ok`.

WHAT IS NOT SAID. SOUNDNESS OF THE SIBLING'S LINK IS A HYPOTHESIS (`SoundLT`). NO INSTANCE: that any
type of bodies has B, Lf, E with `OwnFits` and `hi`, and any description the bounds, is not shown
here; so the theorem is shown to be non-empty by nothing in this file. `tVAny` is evaluated at no
description. ONE PART OF THREE: no part for a key file or a proof file; `SameRaw`, stability, the
language's lemma and one bound at all tables are not treated. That the checker ever returns
something. The bound says nothing once it reaches 1.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.ChainAsk
import OnBytes.TypedOracleCompiler.Slice.PartOn

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop MeasureTheory
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (View SgX)
open TypedOracleCompiler.Run (IsCall169 OneBlock oneBlock_impl)
open TypedOracleCompiler.Run.PQ (XD xdOf BodyD LeafD StmInv OwnE OwnFits FitsS WkAny okgAny implAtPd leafSL
  okX psofX_local)
open OnBytes.Slice (RootsIn chainRoots s0Of over det_pinOn)
open scoped ENNReal

/-! ## From the one hypothesis to the compiler's conclusion, at the wiring of a description -/

section
variable {Bd : Type} (B : BodyD Bd) (D : XD) (dec : View → Bool) (E : OwnE Bd D)

/-- The type of a language of pairs of external strings, at the interface of a description. -/
abbrev LangT (Bd : Type) (D : XD) (dec : View → Bool) : Type :=
  Unit → (twoExternalStrings (D.L Bd dec).wordLength (D.L Bd dec).Symbol).Str → Prop

/-- The one hypothesis, over the sibling. The protocol that the sibling makes from the
description D and the decision dec is round-by-round sound for the language Lg, with error counts
that are each, as a share of the round's challenge values, at most e. The type of bodies stands in
the interface and plays no part. -/
def SoundLT (Bd : Type) (D : XD) (dec : View → Bool)
    (Lg : LangT Bd D dec) (εs : ℝ≥0∞) : Prop :=
  ∃ εL : Err (D.L Bd dec).link.shape, Err.Below εL εs ∧ (D.L Bd dec).link.Sound Lg εL

/-- The sibling's compiler's conclusion at the protocol and wiring of a description. -/
theorem linkAt_any (hwork : ∀ d ∈ D.ds, d.entry.work ≤ 64) (hokx : okX D.ds D.a D.xs = true)
    (Lg : LangT Bd D dec) (εs : ℝ≥0∞)
    (h : SoundLT Bd D dec Lg εs) : LinkAt (WkAny B D dec E) Lg εs :=
  let ⟨εL, hb, hs⟩ := h
  linkAt (WkAny B D dec E) Lg εs () εL () (fun _ _ _ => true) trivial hb trivial
    (fun _ _ => trivial) hs (psofX_local D.C D.ds D.a D.xs dec) (okgAny B D dec E hwork hokx) rfl
    rfl

end

/-! ## The part -/

section
variable {γ Bd : Type} (B : BodyD Bd) (S0 : _root_.Fmt.SpecX)
  (stm : ByteArray → ByteArray → ByteArray) (Lf : LeafD (xdOf S0 stm) B) (dec : View → Bool)
  (hcfg : S0.base.cfg.size = 32) (V : StmInv (xdOf S0 stm)) (E : OwnE Bd (xdOf S0 stm))
  (hwork : ∀ d ∈ (xdOf S0 stm).ds, d.entry.work ≤ 64)
  (hokx : okX (xdOf S0 stm).ds (xdOf S0 stm).a (xdOf S0 stm).xs = true)

/-- The sibling's bound on the queries of the compiled Link verifier at the wiring of the
description. -/
abbrev tVAny : ℕ := tVQB (WkAny B (xdOf S0 stm) dec E).Lk (WkAny B (xdOf S0 stm) dec E).depthReqL

/-- The checker that asks, with the sibling's compiled Link verifier behind it, at an implementation
m. It serves `partChainAsk` alone: by itself it need not meet `Part.OK`. -/
noncomputable def partChainAsk0 (Lg : LangT Bd (xdOf S0 stm) dec) (εs : ℝ≥0∞)
    (m : OracleCoding (typedOracleFamily 256 (WkAny B (xdOf S0 stm) dec E).K ((xdOf S0 stm).L Bd dec)) 256)
    (pre : Pre γ) : Part 256 γ SgX where
  I := Unit
  X := Unit
  L := (xdOf S0 stm).L Bd dec
  W := WkAny B (xdOf S0 stm) dec E
  Out := LinkOut 256 ((xdOf S0 stm).L Bd dec)
  J := judgeL (WkAny B (xdOf S0 stm) dec E) (okgAny B (xdOf S0 stm) dec E hwork hokx)
    (256 + 8 * S0.base.plan.salt) 256 Lg
  e := εs
  m := m
  chk := chainChkAsk Bd S0 stm dec pre
  rts := fun x => match chainRoots pre x with
    | some r => [r.1, r.2]
    | none => []
  tR := OnBytes.Tie.CostX.fileNX S0 * 2
  a := 2
  u := Equiv.refl SgX

/-- The checker that asks the oracle for every hash of the chain's reader, answered by the table T
at the strings of S, as one part of a join, over the sibling. The implementation is `implAtPd` at
the table's value at `s0Of S0.base.params`. -/
noncomputable def partChainAsk (S : Finset (List Bool)) (T : List Bool → Dig 256)
    (Lg : LangT Bd (xdOf S0 stm) dec) (εs : ℝ≥0∞) (pre : Pre γ) : Part 256 γ SgX :=
  (partChainAsk0 B S0 stm dec E hwork hokx Lg εs
    (implAtPd B S0 stm Lf dec hcfg V (T (s0Of S0.base.params))) pre).on S T

variable (S : Finset (List Bool)) (T : List Bool → Dig 256) (Lg : LangT Bd (xdOf S0 stm) dec)
  (εs : ℝ≥0∞) (pre : Pre γ)

/-- The part's checker has under g the value that the asking checker has under g with the table put
over it. -/
theorem partChainAsk_chk_det (g : Fam (rom 256)) (x : γ) :
    ((partChainAsk B S0 stm Lf dec hcfg V E hwork hokx S T Lg εs pre).chk x).det g =
      (chainChkAsk Bd S0 stm dec pre x).det (over S T g) :=
  det_pinOn S T g _

/-- That part meets what the step to one oracle asks of a part, over the sibling. The definition
takes: the configuration's digest has 32 bytes; a reader for the statement; the bodies' data B, Lf,
E; no round asks more than 64 bits of work; the limits `okX`. Asked beside: the string at which the
checker asks for the digest of the parameter bytes lies in S; all strings of S are strings of calls
with the number 169; ROUND-BY-ROUND SOUNDNESS OF THE SIBLING'S LINK FOR THE LANGUAGE, WITH ERROR e
(`SoundLT`: A HYPOTHESIS); the statement holds the roots; the bounds `FitsS`; of bodies `OwnFits`
and `hi`. By `Part.on_ok_of`, with `chainChkAsk_fit_over` for `fit`. -/
theorem partChainAsk_ok (h0S : s0Of S0.base.params ∈ S) (hS : ∀ s ∈ S, IsCall169 s)
    (hs : SoundLT Bd (xdOf S0 stm) dec Lg εs) (hroots : RootsIn S0 stm)
    (F : FitsS (xdOf S0 stm).base (xdOf S0 stm).K) (hOwn : OwnFits B (xdOf S0 stm) Lf E.emb)
    (hi : ∀ p a, B.own (E.emb (.inr p) a) =
      some (leafSL (xdOf S0 stm).C S0.base.plan.salt (xdOf S0 stm).ds ⟨p, a⟩)) :
    (partChainAsk B S0 stm Lf dec hcfg V E hwork hokx S T Lg εs pre).OK :=
  Part.on_ok_of _ S T
    (judgeAt_L (WkAny B (xdOf S0 stm) dec E) (okgAny B (xdOf S0 stm) dec E hwork hokx)
      (256 + 8 * S0.base.plan.salt) 256 Lg εs
      (linkAt_any B (xdOf S0 stm) dec E hwork hokx Lg εs hs))
    (oneBlock_impl _)
    (fun x => (chainChkAsk_bound Bd S0 stm dec pre x).1)
    (fun x => (chainChkAsk_bound Bd S0 stm dec pre x).2)
    (fun x => by
      show (match chainRoots pre x with
        | some r => [r.1, r.2]
        | none => []).length ≤ 2
      cases chainRoots pre x <;> simp)
    (fun g x o h r hr => by
      show r ∈ (match chainRoots pre x with
        | some r => [r.1, r.2]
        | none => [])
      rw [chainChkAsk_roots Bd S0 stm dec pre g x o h]
      exact hr)
    (fun g x o h => ⟨chainChkAsk_fit_over B S0 stm Lf dec hcfg V E F hOwn hi hroots S T h0S hS
      pre g x o h, trivial⟩)

/-- So it meets what the join asks of a part over the one oracle: `PartO.OK` of the line. -/
theorem partChainAskO_ok (h0S : s0Of S0.base.params ∈ S) (hS : ∀ s ∈ S, IsCall169 s)
    (hs : SoundLT Bd (xdOf S0 stm) dec Lg εs) (hroots : RootsIn S0 stm)
    (F : FitsS (xdOf S0 stm).base (xdOf S0 stm).K) (hOwn : OwnFits B (xdOf S0 stm) Lf E.emb)
    (hi : ∀ p a, B.own (E.emb (.inr p) a) =
      some (leafSL (xdOf S0 stm).C S0.base.plan.salt (xdOf S0 stm).ds ⟨p, a⟩)) :
    (partChainAsk B S0 stm Lf dec hcfg V E hwork hokx S T Lg εs pre).toO.OK :=
  Part.toO_ok _ (partChainAsk_ok B S0 stm Lf dec hcfg V E hwork hokx S T Lg εs pre h0S hS hs hroots
    F hOwn hi)

/-- The part's bound, for a maker with at most t queries: no table stands in it. -/
theorem partChainAsk_bound (t : ℕ) :
    (partChainAsk B S0 stm Lf dec hcfg V E hwork hokx S T Lg εs pre).bound t =
      ((t + 2 + OnBytes.Tie.CostX.fileNX S0 * 2 + tVAny B S0 stm dec E : ℕ) : ℝ≥0∞) * εs +
        2 * ((t + 2 + OnBytes.Tie.CostX.fileNX S0 * 2 + tVAny B S0 stm dec E + 1 : ℕ) : ℝ≥0∞) ^ 2 /
          2 ^ 256 :=
  rfl

/-- The roots in what the part's checker returns are its first two components. -/
theorem partChainAsk_roots
    (o : (partChainAsk B S0 stm Lf dec hcfg V E hwork hokx S T Lg εs pre).toO.Out) :
    (partChainAsk B S0 stm Lf dec hcfg V E hwork hokx S T Lg εs pre).toO.roots o = [o.1, o.2.1] :=
  rfl

end

end TypedOracleCompiler.Slice
