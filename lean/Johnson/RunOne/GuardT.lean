-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/GuardT.lean: the guarded run (OnBytes/Maker/Page/Guard.lean, runGuard) and the
guarded verdict of the verifier of a whole file along lists (OnBytes/Maker/ListedWholeGuard.lean,
verifyGuardC) in a form made for a run, each with its equation.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

Why. runGuard P O asks two things at every query: does the page write a string (okJ P), and what is
the answer (gJ P O). As terms to run both are dear: okJ builds every block's string of a chain query
only to ask whether there is one, and gJ hands an answer on as a function of its bits. There are
running forms of both, each proved equal: okJF (OnBytes/Maker/Page/GuardFast.lean; okJF_eq:
OnBytes/Maker/Page/GuardFastLaws.lean) and famT (Johnson/RunOne/FamT.lean, famT_eq). Here they are
laid into detG.

Main definitions.
  runGuardT P R O: detG at okJF P and famT P R O.
  verifyGuardCT … P R O: verifyGuardCG at P.sR, okJF P and famT P R O.
  verifyGuardCFitT … P R O fit: the same with a second test fit on each query.
Main theorems.
  runGuardT_eq: runGuardT P R O c = runGuard P O c, for every tree of queries c. No premise.
  verifyGuardCT_eq: verifyGuardCT … P R O = verifyGuardC … P O. No premise.
  verifyGuardCFitT_eq: verifyGuardCFitT … P R O fit = verifyGuardCFit … P O fit. No premise.

Limits. Those of ListedWholeGuard.lean, GuardFast.lean and FamT.lean. What an evaluator computes how
often is a fact about the compiler: nothing on time or memory is a theorem. detG goes down the tree
of queries by recursion, a step a query: how deep a stack a file of some thousand rounds wants is
not looked at here. Nothing has been run here. Nothing on soundness.
The program does not import this file.


-/
import Johnson.RunOne.FamT
import OnBytes.Maker.ListedWholeGuardFast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne

open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol
open _root_.Run
open OnBytes OnBytes.Maker OnBytes.Maker.Page

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

/-- **The guarded run, for a run**: the page's test by conditions; the answers as bytes first. -/
def runGuardT {α : Type} (P : PageJ L K) (R : RunJ P) (O : ByteArray → ByteArray) :
    OComp (typedOracleFamily 256 K L) α → Option α :=
  detG (S := typedOracleFamily 256 K L) (okJF P) (famT P R O)

/-- **It is runGuard.** No premise. -/
theorem runGuardT_eq {α : Type} (P : PageJ L K) (R : RunJ P) (O : ByteArray → ByteArray)
    (c : OComp (typedOracleFamily 256 K L) α) : runGuardT P R O c = runGuard P O c := by
  unfold runGuardT
  rw [famT_eq]
  exact runGuardF_eq P O c

end Johnson.RunOne

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (D : WholeD)
  {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) {I X : Type} {L : BatchProtocolWithLeafBody I X} {Xi : Type}
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)
  (sMT sFS : ℕ) (t : _root_.Compile.Tag)
  (embS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L)
  (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
    PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
  (xin : Xi → Option X) (embE : SgX → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Xi)
  (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) (own : Leaves)
  (listed : List (oneExternalString (2 ^ D.a) SgX).Pos)

/-- **The guarded verdict, for a run.** -/
def verifyGuardCT (P : Page.PageJ L (K + 1)) (R : Johnson.RunOne.RunJ P)
    (O : ByteArray → ByteArray) : Bool :=
  verifyGuardCG C K chal D tF tJ t3 silent run P.sR sMT sFS t embS embP xin embE depthReq cms x π
    own listed (Page.okJF P) (Johnson.RunOne.famT P R O)

/-- **It is verifyGuardC.** No premise. -/
theorem verifyGuardCT_eq (P : Page.PageJ L (K + 1)) (R : Johnson.RunOne.RunJ P)
    (O : ByteArray → ByteArray) :
    verifyGuardCT C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π own
        listed P R O =
      verifyGuardC C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π own
        listed P O := by
  unfold verifyGuardCT
  rw [Johnson.RunOne.famT_eq]
  exact verifyGuardCF_eq C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x
    π own listed P O

/-- **The guarded verdict with a second test on each query, for a run.** -/
def verifyGuardCFitT (P : Page.PageJ L (K + 1)) (R : Johnson.RunOne.RunJ P)
    (O : ByteArray → ByteArray)
    (fit : (o : TypedOracleCompiler.Compile.Batch.OracleName) → domOf 256 L o → Bool) : Bool :=
  verifyGuardCG C K chal D tF tJ t3 silent run P.sR sMT sFS t embS embP xin embE depthReq cms x π
    own listed (fun o q => Page.okJF P o q && fit o q) (Johnson.RunOne.famT P R O)

/-- **It is verifyGuardCFit.** No premise. -/
theorem verifyGuardCFitT_eq (P : Page.PageJ L (K + 1)) (R : Johnson.RunOne.RunJ P)
    (O : ByteArray → ByteArray)
    (fit : (o : TypedOracleCompiler.Compile.Batch.OracleName) → domOf 256 L o → Bool) :
    verifyGuardCFitT C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π
        own listed P R O fit =
      verifyGuardCFit C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π
        own listed P O fit := by
  unfold verifyGuardCFitT
  rw [Johnson.RunOne.famT_eq]
  exact congrArg (fun r : Option Bool => r.getD false)
    (Page.runGuardFitF_eq P O fit (verifyWholeCR C K chal D tF tJ t3 silent run P.sR sMT sFS t embS
      embP xin embE depthReq cms x π own listed))

end OnBytes.Maker

#print axioms OnBytes.Maker.verifyGuardCFitT_eq
#print axioms Johnson.RunOne.runGuardT_eq
#print axioms OnBytes.Maker.verifyGuardCT_eq
