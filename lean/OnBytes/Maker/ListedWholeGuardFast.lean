-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ListedWholeGuardFast.lean: two other ways to compute the guarded verdict of the
verifier of a whole file along lists (OnBytes/Maker/ListedWholeGuard.lean, verifyGuardC,
verifyGuardCG), each with its equation; and that verdict with a second test on each query.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

Why. The test okJ P builds, at every query of a chain, each block's string only to ask whether there
is one. OnBytes/Maker/Page/GuardFast.lean has the same test by conditions (okJF; okJF_eq:
OnBytes/Maker/Page/GuardFastLaws.lean). And a runner that keeps what was asked can give the verdict
from the library's test on the queries asked and the plain run (Rom.OComp.askedOK,
Run/DetAlong.lean; detG_eq_asked, OnBytes/Maker/Page/GuardLaws.lean).

Main definitions.
  verifyGuardCF P O: verifyGuardCG at P.sR, okJF P and gJ P O.
  verifyGuardCFit P O fit: verifyGuardCG at P.sR, okFitJ P fit and gJ P O: a query must pass okJ P
    and fit, a letter (OnBytes/Maker/Page/GuardFit.lean).
Main theorems.
  verifyGuardCFit_eq: verifyGuardCFit P O fit is verifyGuardFit P O fit at wqWhole and the cut
    string. No premise.
  verifyGuardCF_eq: verifyGuardCF P O = verifyGuardC P O. No premise.
  verifyGuardCG_asked: verifyGuardCG ok g is: every query asked under g passes ok, and the plain run
    under g says yes. No premise.

Limits. Those of ListedWholeGuard.lean. The oracle functions are still gJ P O: how often a hash is
made in a run is not looked at here. Nothing on time or memory is a theorem. Nothing on soundness.
The program does not import this file.


-/
import OnBytes.Maker.ListedWholeGuard
import OnBytes.Maker.Page.GuardFastVerify

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (D : WholeD)
  {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) {I X : Type} {L : BatchProtocolWithLeafBody I X} {Xi : Type}
  (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)
  (sR sMT sFS : ℕ) (t : _root_.Compile.Tag)
  (embS : (p : OPos (chainsOf C D tF tJ t3).sh) → OSym (chainsOf C D tF tJ t3).sh p → Body L)
  (embP : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann →
    PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
  (xin : Xi → Option X) (embE : SgX → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Xi)
  (π : OneProtocolProof 256 (wholeDesc C D tF tJ t3 silent run).batch) (own : Leaves)
  (listed : List (oneExternalString (2 ^ D.a) SgX).Pos)

/-- **The guarded verdict with the page's test by conditions.** -/
def verifyGuardCF (P : Page.PageJ L (K + 1)) (O : ByteArray → ByteArray) : Bool :=
  verifyGuardCG C K chal D tF tJ t3 silent run P.sR sMT sFS t embS embP xin embE depthReq cms x π
    own listed (Page.okJF P) (Page.gJ P O)

/-- **It is verifyGuardC.** No premise. -/
theorem verifyGuardCF_eq (P : Page.PageJ L (K + 1)) (O : ByteArray → ByteArray) :
    verifyGuardCF C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π own
        listed P O =
      verifyGuardC C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π own
        listed P O :=
  congrArg (fun r : Option Bool => r.getD false)
    (Page.runGuardF_eq P O (verifyWholeCR C K chal D tF tJ t3 silent run P.sR sMT sFS t embS embP
      xin embE depthReq cms x π own listed))

/-- **The guarded verdict is: every query asked passes the test, and the plain run says yes.** -/
theorem verifyGuardCG_asked
    (ok : ∀ o : (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1) L).ι,
      (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1) L).Dom o → Bool)
    (g : Rom.Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1) L)) :
    verifyGuardCG C K chal D tF tJ t3 silent run sR sMT sFS t embS embP xin embE depthReq cms x π
        own listed ok g =
      ((verifyWholeCR C K chal D tF tJ t3 silent run sR sMT sFS t embS embP xin embE depthReq cms x
          π own listed).askedOK g ok &&
        (verifyWholeCR C K chal D tF tJ t3 silent run sR sMT sFS t embS embP xin embE depthReq cms x
          π own listed).det g) := by
  unfold verifyGuardCG
  rw [Page.detG_eq_asked]
  cases (verifyWholeCR C K chal D tF tJ t3 silent run sR sMT sFS t embS embP xin embE depthReq cms x
    π own listed).askedOK g ok <;> rfl

/-- **The guarded verdict with a second test on each query.** -/
def verifyGuardCFit (P : Page.PageJ L (K + 1)) (O : ByteArray → ByteArray)
    (fit : (o : TypedOracleCompiler.Compile.Batch.OracleName) → domOf 256 L o → Bool) : Bool :=
  verifyGuardCG C K chal D tF tJ t3 silent run P.sR sMT sFS t embS embP xin embE depthReq cms x π
    own listed (Page.okFitJ P fit) (Page.gJ P O)

/-- **It is verifyGuardFit at the file's wire record and the cut string.** No premise. -/
theorem verifyGuardCFit_eq (P : Page.PageJ L (K + 1)) (O : ByteArray → ByteArray)
    (fit : (o : TypedOracleCompiler.Compile.Batch.OracleName) → domOf 256 L o → Bool) :
    verifyGuardCFit C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π own
        listed P O fit =
      Page.verifyGuardFit P O fit sMT sFS t (wholeDesc C D tF tJ t3 silent run).batch
        (wqWhole C K chal D tF tJ t3 silent run) embS embP xin embE depthReq cms x
        (π.cutTo (wiresOf C K chal D tF tJ t3).sh (wlOne D.a) own listed) :=
  verifyGuardCG_eq C K chal D tF tJ t3 silent run P.sR sMT sFS t embS embP xin embE depthReq cms x
    π own listed (Page.okFitJ P fit) (Page.gJ P O)

end OnBytes.Maker

#print axioms OnBytes.Maker.verifyGuardCFit_eq
#print axioms OnBytes.Maker.verifyGuardCF_eq
#print axioms OnBytes.Maker.verifyGuardCG_asked
