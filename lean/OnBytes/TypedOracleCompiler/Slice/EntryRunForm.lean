-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryRunForm.lean: the run of the entry's judge, under any family of oracle
functions, AS A TRUTH VALUE THAT HAS CODE WHEREVER ITS LETTERS HAVE, with the equation: so that what
a run computes is the value of the very term of which the statement on soundness speaks.

The entry's checker is "the typing, then the judge's run over the one oracle through the page"
(`chkT`, OnBytes/TypedOracleCompiler/Slice/ShapesTyping.lean). Its value under an oracle g hangs on `(J.run o).det
(readBlocks m g)`. `OComp.det` of an algorithm is a mathematical value.
OnBytes/TypedOracleCompiler/Slice/EntryJudgeRun.lean and OnBytes/TypedOracleCompiler/Slice/EntryRun.lean have run forms of the two
halves: `cmpE` for the seeds' chains and the comparisons, `laxE` for the compiled verifier without
the strict format, each with its equation. Here they are put together for an output o as the judge
takes it.

Main definition.
 `judgeRunELF`          THE RUN ON AN OUTPUT, AS A TRUTH VALUE: `cmpE` on the first two outer roots,
                        and `laxE`. A plain definition, general in the description, the decision,
                        the bodies, what a first query holds, the seeds' entry, and the value off
                        what was drawn.
Main theorems.
 `judgeRunEL_det_and`   general: the value of the judge's run under F is the comparisons' value and
                        the compiled verifier's.
 `judgeRunEL_eq_F`      `judgeRunELF` IS THE VALUE OF `judgeRunEL` UNDER F: every F, every output,
                        no hypothesis.
 `EntryAt.run_eq`       AT THE ENTRY'S PART (OnBytes/TypedOracleCompiler/Slice/EntryDelivers.lean): `((x.base
                        ..).J.run o).det F = judgeRunELF .. (seedOfDrawnC lg s) F o`, with
                        `seedOfDrawnC` (OnBytes/Slice/SeedDrawnCode.lean), which has code.

Not claimed. That it comes home at any size; how long it takes. That a family F has code:
`readBlocks m g` at a page and an oracle is another file's matter. That the letters' values
(description, decision, bodies, THE TEST OF EQUALITY ON SEEDS, which is an argument here and in the
statement on soundness) have code. That an output has two roots: the judge's run does not test it.
WHERE THE CHECKER'S VALUE IS WRITTEN WITH THIS TRUTH VALUE (`HomeData.chk_eq_runF`) THE LETTERS
STAND AT THE ORACLE'S OWN PUBLIC VALUES: a run that takes the configuration's digest off the files
evaluates another term, unless the two digests are shown or evaluated to be one. No typing, no
converter. That the value is ever true. NOTHING ON SOUNDNESS IS SHOWN. What the heads of
EntryJudgeRun.lean, EntryPS.lean, EntryRun.lean and EntryDelivers.lean do not claim. The compiler
under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on definitions of
Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryJudgeRun
import OnBytes.TypedOracleCompiler.Slice.EntryDelivers
import OnBytes.Slice.SeedDrawnCode

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD BodyD OwnE)
open _root_.Run.PQ (View SgX)
open OnBytes.Slice (decRec GE NZ seedEntry seedOfDrawn seedOfDrawnC seedOfDrawnC_eq)
open scoped ENNReal

/-! ## The judge's run under a family of oracle functions, as a value -/

section
variable {I A Sd S : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I (A × Sd)} {W : QueryLayout lam L} {Ex : ExtRd L}
  [DecidableEq S] (ZT : Written W) (saltT : Bits) (rtT : Dig lam) (rootsT : List (Dig lam))
  (plainsT : Plains ZT.P.shape) (seedOf : Rho ZT.P.shape → S) (Pk : Pack Ex.k S Sd)

/-- The value of the judge's run without the strict format under F: the comparisons' value and the
compiled verifier's. The equation of which `judgeRunEL_det` (OnBytes/TypedOracleCompiler/Slice/EntryXRun.lean) is
the yes. -/
theorem judgeRunEL_det_and (Z : WrittenE W Ex) (F : Fam (typedOracleFamily lam W.K L)) (o : OutE Z) :
    (judgeRunEL Z ZT saltT rtT rootsT plainsT seedOf Pk o).det F =
      ((cmpT ZT saltT rtT rootsT plainsT seedOf Pk (o.1.take Ex.k) 0 o.2.1.2).det F &&
        (Z.verifier o.1 o.2.1 o.2.2).det F) := by
  unfold judgeRunEL
  rw [OComp.det_bind]
  cases (cmpT ZT saltT rtT rootsT plainsT seedOf Pk (o.1.take Ex.k) 0 o.2.1.2).det F with
  | true =>
    rw [if_pos rfl]
    rfl
  | false =>
    rw [if_neg Bool.false_ne_true]
    rfl

end

/-! ## At the entry's frame: a value that has code wherever its letters have -/

section
variable {A S : Type} [DecidableEq S] (D : XD) (dec : A × (S × S) → View → Bool) {Bd : Type}
  (B : BodyD Bd) (E : OwnE Bd D) (early : A × (S × S) → A × (S × S)) (e : _root_.Fmt.Entry)
  (sOf : List _root_.Fmt.Drawn → S)

/-- THE ENTRY'S JUDGE'S RUN ON AN OUTPUT, AS A TRUTH VALUE WITH CODE: the seeds' chain under
each of the first two outer roots, compared with the seeds in the instance (`cmpE`,
OnBytes/TypedOracleCompiler/Slice/EntryJudgeRun.lean); then the run form of the compiled verifier without the strict
format at the link's skeleton (`laxE`, OnBytes/TypedOracleCompiler/Slice/EntryRun.lean). A plain definition. The
seeds' protocol stands behind a function of no argument: no protocol, shape or interface is an
argument that a run evaluates. IT DOES NOT TEST THAT THERE ARE TWO ROOTS: on fewer it compares fewer
seeds. The checker's cut to two roots (`HomeData.conv2`, OnBytes/TypedOracleCompiler/Slice/EntryHome.lean) does. -/
def judgeRunELF (F : Fam (typedOracleFamily 256 (D.K + 1) (LXE (Bd := Bd) D early (TSE D e))))
    (o : List (Dig 256) × (A × (S × S)) × OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto (LinkX D dec))) : Bool :=
  cmpE D early e sOf F (o.1.take 2) 0 o.2.1.2 &&
    laxE D dec B E early (fun _ => TSE D e) F o.1 o.2.1 (toPS D dec o.2.2)

/-- IT IS THE VALUE OF THE JUDGE'S RUN UNDER F, for every family F of oracle functions and every
output. No hypothesis. -/
theorem judgeRunEL_eq_F (F : Fam (typedOracleFamily 256 (D.K + 1) (LXE (Bd := Bd) D early (TSE D e))))
    (o : OutE (ZXE D dec B E early (TSE D e) (wTSE D e) (embST D.C e _) (prjST D.C e _))) :
    (judgeRunEL (ZXE D dec B E early (TSE D e) (wTSE D e) (embST D.C e _) (prjST D.C e _))
      (testXE D B E early (TSE D e) (wTSE D e) (embST D.C e _) (prjST D.C e _)) [] default []
      (plainsT D.C (dSeed e) (oneExternalString (2 ^ D.a) SgX)) (seedOfE D e sOf) (pack2 S) o).det F =
      judgeRunELF D dec B E early e sOf F o := by
  refine (judgeRunEL_det_and (Ex := ext2R (LXE (Bd := Bd) D early (TSE D e)))
    (testXE D B E early (TSE D e) (wTSE D e) (embST D.C e _) (prjST D.C e _)) [] default []
    (plainsT D.C (dSeed e) (oneExternalString (2 ^ D.a) SgX)) (seedOfE D e sOf) (pack2 S)
    (ZXE D dec B E early (TSE D e) (wTSE D e) (embST D.C e _) (prjST D.C e _)) F o).trans ?_
  have e1 := cmpE_eq D B E early e sOf F (o.1.take 2) 0 o.2.1.2
  have e2 := laxE_eq D dec B E early (TSE D e) (wTSE D e) (embST D.C e _) (prjST D.C e _) F o.1
    o.2.1 (toPS D dec o.2.2)
  exact congrArg₂ (· && ·) e1 e2.symm

end

/-! ## At the entry's part -/

section
variable {An : Type} {lg s : ℕ} [DecidableEq (Sd1 lg s)] {d₁ : Sd1 lg s}
  (T : _root_.Fmt.M1.Code) (v eM : ℕ)
  (an : An → (decRec T v eM lg s).ix.Row × (decRec T v eM lg s).Z.S → GE)

/-- THE RUN OF THE JUDGE OF THE ENTRY'S PART, UNDER ANY FAMILY F, IS THAT TRUTH VALUE, at the
seeds' entry and at `seedOfDrawnC` (OnBytes/Slice/SeedDrawnCode.lean), which has code. -/
theorem EntryAt.run_eq (x : EntryAt An lg s d₁) (εs : ℝ≥0∞)
    (F : Fam (typedOracleFamily 256 (x.D.K + 1) (LXEs (An := An) (Bd := x.Bd) lg s x.D d₁))) (o : OutE x.Z) :
    ((x.base T v eM an εs).J.run o).det F =
      judgeRunELF x.D x.dec x.B x.E (earlyTwo d₁) (seedEntry lg s) (seedOfDrawnC lg s) F o := by
  rw [seedOfDrawnC_eq]
  exact judgeRunEL_eq_F x.D x.dec x.B x.E (earlyTwo d₁) (seedEntry lg s) (seedOfDrawn lg s) F o

end

end TypedOracleCompiler.Slice
