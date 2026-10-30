-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryProbe.lean: THE WORK's TEST OF THE ENTRY's TYPED VERIFIER,
EVALUATED BY ITSELF. A tool for tests; NOTHING IS PROVED.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
WHY. Does the typed verifier test work? passSL stands in accept: that is to be SEEN in a run. A
turned nonce changes its own round's draws, so the lax verifier ends at "own" | "ext", before accept
is evaluated: the work's test is not reached. Here: the chain is run on the string (chainP, as
verifyLX runs it); then PQ.passSL D.C D.ds, THE VERY CONJUNCT OF skeletonOverBothExternalStrings's accept
(Run/PlanQX.lean:146), on the verifier's messages that the chain yields.
  workE D dec early Tf F cms x π : Option Bool     none: the chain refuses
WHAT IT ALLOWS TO SAY: "on this string the decision's conjunct passSL is false". NOT: "the
verifier's run ended there".

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryRun

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD SOf)
open _root_.Run.PQ (View SgX)
open TypedOracleCompiler.Run.Thin (chainP)

variable {X : Type} (D : XD) (dec : X → View → Bool) {Bd : Type} (early : X → X)
  (Tf : Unit → InteractiveOracleProof Unit (oneExternalString (2 ^ D.a) SgX))

/-- The work's test, by itself. -/
def workE (F : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (D.K + 1) (LXE (Bd := Bd) D early (Tf ()))))
    (cms : List (Dig 256)) (x : X)
    (π : OneProtocolProof 256 (PSXE D dec).up) : Option Bool :=
  (chainP (fun _ => LXE (Bd := Bd) D early (Tf ())) F early none .link cms (some x) π.salt π.rtreq
      (PSXE D dec).S (PSXE D dec).ann
    (wqXE D dec).sh (embPXE D early (Tf ())) 0 .first π.roots π.plains).map fun z =>
        PQ.passSL D.C D.ds z.1.2

end TypedOracleCompiler.Slice
