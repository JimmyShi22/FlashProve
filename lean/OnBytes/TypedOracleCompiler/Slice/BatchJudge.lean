-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/BatchJudge.lean: the compiled verifier of one slot of a written batch protocol as
a judge, over the sibling's types.

OnBytes/TypedOracleCompiler/Slice/OneWorldJ.lean makes the step from the typed oracles to one oracle for any
compiled verifier that is given as a `Judge` with `JudgeAt`. OnBytes/TypedOracleCompiler/Slice/BatchClause.lean has
the compiler's conclusion on a written batch protocol, `BatchAt`. This file fills the one form with
the other, as a file of this project that is not in this library does for a protocol without an
instance.
 - `judgeB Z R Lg`: the judge: the run is `Z.verifier` on a root, an instance and an argument
   string; the bound on its queries is the sibling's; one root; the reading R; the language Lg at
   the instance and the one string; what a checker owes of its output beside the run's yes: that R
   keeps every external opening that the argument string holds;
 - `judgeAt_B`: `BatchAt Z R Lg e` gives `JudgeAt` of that judge, clause for clause;
 - `judgeBS`, `judgeAt_BS`: the same for the verifier with the strict format, if `Z.OK` holds.

Main definitions: `BatchOut`, `judgeB`, `judgeBS`.
Main theorems: `judgeAt_B`, `judgeAt_BS`.

Not claimed. No written batch protocol, reading, language or state function is given. `BatchAt` is a
hypothesis. The language holds for free of a list of other than one string; the list of roots always
has one. No `Part` of OnBytes/TypedOracleCompiler/Slice/Part.lean is made of the judge. Nothing on soundness beyond
the hypothesis.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.OneWorldJ
import OnBytes.TypedOracleCompiler.Slice.BatchClause

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- What a checker returns for one slot of a written batch protocol: the root, the instance and the
argument string. -/
abbrev BatchOut {W : QueryLayout lam L} (Z : WrittenB W) : Type := Dig lam × X × OneProtocolProof lam Z.Q

/-- The compiled verifier of one slot of a written batch protocol as a judge. -/
noncomputable def judgeB {W : QueryLayout lam L} (Z : WrittenB W) (R : Reading L W.embE)
    (Lg : X → (oneExternalString L.wordLength L.Symbol).Str → Prop) : Judge W (BatchOut Z) where
  run := fun o => Z.verifier o.1 o.2.1 o.2.2
  tV := tVQB Z.wq (W.dReq Z.t)
  bound := fun _ => detBound_verifyB _ _ _ _ _ _ _ _ _ _ _
  roots := fun o => [o.1]
  R := R
  Lang := fun o ys => ∀ y, ys = [y] → Lg o.2.1 y
  ok := fun o => ∀ p op, o.2.2.ext p = some op → R.keeps p op.sym op.salt

/-- The compiler's conclusion on a written batch protocol is the judge's. -/
theorem judgeAt_B {W : QueryLayout lam L} (Z : WrittenB W) (R : Reading L W.embE)
    (Lg : X → (oneExternalString L.wordLength L.Symbol).Str → Prop) (εs : ℝ≥0∞) (h : BatchAt Z R Lg εs) :
    JudgeAt W (judgeB Z R Lg) εs := by
  obtain ⟨Bad, hrare, hmono, hL, hst⟩ := h
  refine ⟨Bad, hrare, hmono, fun tr o hnb hok hrun y hy => ?_, hst⟩
  have e : [R.at W tr o.1] = [y] := hy
  rw [← (List.cons.inj e).1]
  exact hL tr o.1 o.2.1 o.2.2 hnb hok hrun

/-- The same judge with the strict format; sMT and sFS are the strict verifier's two lengths of
salts, in bits. -/
noncomputable def judgeBS {W : QueryLayout lam L} (Z : WrittenB W) (R : Reading L W.embE)
    (Lg : X → (oneExternalString L.wordLength L.Symbol).Str → Prop) (sMT sFS : ℕ) : Judge W (BatchOut Z) where
  run := fun o => Z.verifierS sMT sFS o.1 o.2.1 o.2.2
  tV := tVQB Z.wq (W.dReq Z.t)
  bound := fun _ => detBound_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _
  roots := fun o => [o.1]
  R := R
  Lang := fun o ys => ∀ y, ys = [y] → Lg o.2.1 y
  ok := fun o => ∀ p op, o.2.2.ext p = some op → R.keeps p op.sym op.salt

/-- The compiler's conclusion is that judge's too, if `Z.OK` holds (of it the laws of the wiring are
used): a run of the verifier with the strict format that says yes is one of the plain verifier on
the argument string with paths put in. -/
theorem judgeAt_BS {W : QueryLayout lam L} (Z : WrittenB W) (R : Reading L W.embE)
    (Lg : X → (oneExternalString L.wordLength L.Symbol).Str → Prop) (sMT sFS : ℕ) (hZ : Z.OK) (εs : ℝ≥0∞)
    (h : BatchAt Z R Lg εs) : JudgeAt W (judgeBS Z R Lg sMT sFS) εs := by
  obtain ⟨Bad, hrare, hmono, hL, hst⟩ := h
  refine ⟨Bad, hrare, hmono, fun tr o hnb hok hrun y hy => ?_, hst⟩
  have e : [R.at W tr o.1] = [y] := hy
  rw [← (List.cons.inj e).1]
  obtain ⟨P1, P2, h2⟩ := runsIn_verifyB_of_strict hZ.wire hrun
  exact hL tr o.1 o.2.1 (o.2.2.withPaths P1 P2) hnb (keeps_withPaths R o.2.2 P1 P2 hok) h2

end TypedOracleCompiler.Slice
