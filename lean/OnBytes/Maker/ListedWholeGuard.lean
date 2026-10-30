-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ListedWholeGuard.lean: at the description of a whole file: the verifier along lists on
the cut string (OnBytes/Maker/ListedWholeCut.lean, verifyWholeC) behind the test of the field rsalt
(OnBytes/Maker/Page/GuardVerify.lean, rsaltFit), with its verdict by the run that refuses at the
first query which a test turns away (OnBytes/Maker/Page/Guard.lean, detG). The definitions have
code. Their verdict is that of verifyGuard at the file's wire record and the cut string.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

Why. verifyGuard stands over verifyOneProtocol at a wire record ProtocolQueryLayout. At a whole file that record holds the
list of all positions of the stored table, and verifyOneProtocol walks all leaves of every tree: it is a term
to prove things of, not one to run. verifyWholeC is the same tree of queries at the cut string
(verifyWholeC_eq0, OnBytes/Maker/ListedWholePlaces.lean) and goes along lists. So the guarded run of
the one is the guarded run of the other.

Main definitions.
  verifyWholeCR: verifyWholeC where rsaltFit says yes; else no, with no query. An oracle algorithm.
  verifyGuardCG ok g: its verdict by detG at a test ok and oracle functions g; no value is a no.
  verifyGuardC P O: that verdict at the page's own test, family and sR (okJ P, gJ P O, P.sR).
Main theorems.
  verifyWholeCR_eq: verifyWholeCR is verifyBSR at wqWhole and the cut string. No premise.
  verifyGuardCG_eq: so their guarded runs have one verdict, at every test and every family.
  verifyGuardC_eq: **verifyGuardC P O at π, own, listed is verifyGuard P O at wqWhole and π.cutTo**,
    for every argument string and every two lists. No premise.
  verifyGuardC_iff: its yes says two things: rsaltFit passes, and the guarded run of verifyWholeC
    has the value true. So a sheet can print the two apart. verifyGuardC_iffB: the same with
    verifyOneProtocol at the cut string.
  verifyGuardC_yes: its yes is a yes of verifyOneProtocol at the cut string under gJ P O. It says less than
    verifyGuardC_iff: it drops the test of rsalt and that no query was turned away.
  verifyGuardC_eq_self: where the openings of π stand at listed places alone: verifyGuard at π.

Limits. WHAT IS JUDGED IS THE CUT STRING, NOT π: an opening outside the lists is dropped, not
refused, so this is laxer than the strict format unless the lists hold every place with an opening;
and lists that leave out a read place turn a yes at π into a no.
The cut leaves rsalt and slot as they are. The limits of Guard.lean and GuardVerify.lean hold here:
a yes is a yes under the page's family; that an honest file's queries all have strings is not shown.
No law from the page's family to another is stated here. By reading, not shown here: at a page
whose sR is not the length of the binding leaf's salt no honest string passes, and at a page that
writes no leaves the verdict is no wherever a leaf is read; the verdict folds three kinds of no
into one (the test of rsalt; a query turned away; the verifier's own). C, K, chal, D and the other
letters are the caller's: that they are the data of a description of which another theorem speaks is
not said here. Each round's wire record still holds the list of all its positions
(ListedVerifier.lean).
Nothing on time or memory is a theorem. Nothing on soundness.
The program does not import this file.


-/
import OnBytes.Maker.ListedWholePlaces
import OnBytes.Maker.Page.GuardLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch _root_.Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

/-- The cut turns neither rsalt nor slot: the test of rsalt says the same of both strings. -/
theorem rsaltFit_cutTo {K : ℕ} {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (sR depthReq : ℕ)
    (π : OneProtocolProof 256 Q) (sh : RoundsQueryLayout 256 K Q.loc.shape Q.ann) (wl : WireELess E) (own : Leaves)
    (listed : List E.Pos) :
    Page.rsaltFit sR depthReq (π.cutTo sh wl own listed) = Page.rsaltFit sR depthReq π := rfl

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

/-- **The verifier of a whole file along the lists, on the cut string, behind the test of rsalt.**
-/
def verifyWholeCR : TypedOracleComputation 256 (K + 1) L Bool :=
  if Page.rsaltFit sR depthReq π then
    verifyWholeC C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π own
      listed
  else pure false

/-- Its verdict by the run that refuses at the first query which ok turns away. A no folds three
causes into one: the test of rsalt, a query turned away, the verifier's own no. -/
def verifyGuardCG
    (ok : ∀ o : (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1) L).ι,
      (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1) L).Dom o → Bool)
    (g : Rom.Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1) L)) : Bool :=
  (Page.detG ok g (verifyWholeCR C K chal D tF tJ t3 silent run sR sMT sFS t embS embP xin embE
    depthReq cms x π own listed)).getD false

/-- **Its verdict under the page's family, with no query that okJ P turns away.** At a chain's first
call that string is the tail's block's alone, and the blocks in front are zeros; that the file's
wire reads none of them is not shown. -/
def verifyGuardC (P : Page.PageJ L (K + 1)) (O : ByteArray → ByteArray) : Bool :=
  verifyGuardCG C K chal D tF tJ t3 silent run P.sR sMT sFS t embS embP xin embE depthReq cms x π
    own listed (Page.okJ P) (Page.gJ P O)

/-- It is the compiled verifier behind the test of rsalt, at the file's wire record and the cut
string. -/
theorem verifyWholeCR_eq :
    verifyWholeCR C K chal D tF tJ t3 silent run sR sMT sFS t embS embP xin embE depthReq cms x π
        own listed =
      Page.verifyBSR sR sMT sFS t (wholeDesc C D tF tJ t3 silent run).batch
        (wqWhole C K chal D tF tJ t3 silent run) embS embP xin embE depthReq cms x
        (π.cutTo (wiresOf C K chal D tF tJ t3).sh (wlOne D.a) own listed) := by
  unfold verifyWholeCR Page.verifyBSR
  rw [rsaltFit_cutTo, verifyWholeC_eq0 C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE
    depthReq cms x π own listed]

/-- The two guarded runs have one verdict, at every test and all oracle functions. -/
theorem verifyGuardCG_eq
    (ok : ∀ o : (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1) L).ι,
      (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1) L).Dom o → Bool)
    (g : Rom.Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1) L)) :
    verifyGuardCG C K chal D tF tJ t3 silent run sR sMT sFS t embS embP xin embE depthReq cms x π
        own listed ok g =
      (Page.detG ok g (Page.verifyBSR sR sMT sFS t (wholeDesc C D tF tJ t3 silent run).batch
        (wqWhole C K chal D tF tJ t3 silent run) embS embP xin embE depthReq cms x
        (π.cutTo (wiresOf C K chal D tF tJ t3).sh (wlOne D.a) own listed))).getD false := by
  unfold verifyGuardCG
  rw [verifyWholeCR_eq]

/-- **The guarded verdict along the lists is verifyGuard at the file's wire record and the cut
string**: for every argument string and every two lists; no premise. -/
theorem verifyGuardC_eq (P : Page.PageJ L (K + 1)) (O : ByteArray → ByteArray) :
    verifyGuardC C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π own
        listed P O =
      Page.verifyGuard P O sMT sFS t (wholeDesc C D tF tJ t3 silent run).batch
        (wqWhole C K chal D tF tJ t3 silent run) embS embP xin embE depthReq cms x
        (π.cutTo (wiresOf C K chal D tF tJ t3).sh (wlOne D.a) own listed) :=
  verifyGuardCG_eq C K chal D tF tJ t3 silent run P.sR sMT sFS t embS embP xin embE depthReq cms x
    π own listed (Page.okJ P) (Page.gJ P O)

/-- **What its yes says**: the test of rsalt passes, and the guarded run of the verifier along the
lists has the value true. -/
theorem verifyGuardC_iff (P : Page.PageJ L (K + 1)) (O : ByteArray → ByteArray) :
    verifyGuardC C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π own
        listed P O = true ↔
      Page.rsaltFit P.sR depthReq π = true ∧
        Page.runGuard P O (verifyWholeC C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE
          depthReq cms x π own listed) = some true := by
  rw [verifyGuardC_eq, Page.verifyGuard_iff, rsaltFit_cutTo, verifyWholeC_eq0]

/-- The same with the compiled verifier at the cut string. -/
theorem verifyGuardC_iffB (P : Page.PageJ L (K + 1)) (O : ByteArray → ByteArray) :
    verifyGuardC C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π own
        listed P O = true ↔
      Page.rsaltFit P.sR depthReq π = true ∧
        Page.runGuard P O (verifyOneProtocol sMT sFS t (wholeDesc C D tF tJ t3 silent run).batch
          (wqWhole C K chal D tF tJ t3 silent run) embS embP xin embE depthReq cms x
          (π.cutTo (wiresOf C K chal D tF tJ t3).sh (wlOne D.a) own listed)) = some true := by
  rw [verifyGuardC_eq, Page.verifyGuard_iff, rsaltFit_cutTo]

/-- Its yes is a yes of the compiled verifier at the cut string under the page's family. -/
theorem verifyGuardC_yes (P : Page.PageJ L (K + 1)) (O : ByteArray → ByteArray)
    (h : verifyGuardC C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π
      own listed P O = true) :
    (verifyOneProtocol sMT sFS t (wholeDesc C D tF tJ t3 silent run).batch
      (wqWhole C K chal D tF tJ t3 silent run) embS embP xin embE depthReq cms x
      (π.cutTo (wiresOf C K chal D tF tJ t3).sh (wlOne D.a) own listed)).det (Page.gJ P O) = true :=
  Page.verifyGuard_yes sMT sFS t (wholeDesc C D tF tJ t3 silent run).batch
    (wqWhole C K chal D tF tJ t3 silent run) embS embP xin embE depthReq cms x
    (π.cutTo (wiresOf C K chal D tF tJ t3).sh (wlOne D.a) own listed) P O
    ((verifyGuardC_eq C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π
      own listed P O).symm.trans h)

/-- **Where the openings of the string stand at listed places alone, it is verifyGuard at the string
itself.** -/
theorem verifyGuardC_eq_self (P : Page.PageJ L (K + 1)) (O : ByteArray → ByteArray)
    (hO : ListedOK (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann
      (wiresOf C K chal D tF tJ t3).sh π.opens own)
    (hE : ∀ p, π.ext p ≠ none → p ∈ listed) :
    verifyGuardC C K chal D tF tJ t3 silent run sMT sFS t embS embP xin embE depthReq cms x π own
        listed P O =
      Page.verifyGuard P O sMT sFS t (wholeDesc C D tF tJ t3 silent run).batch
        (wqWhole C K chal D tF tJ t3 silent run) embS embP xin embE depthReq cms x π := by
  rw [verifyGuardC_eq]
  exact congrArg _ (cutTo_of_listed π (wiresOf C K chal D tF tJ t3).sh (wlOne D.a) own listed
    (seatsOK_wiresOf C K chal D tF tJ t3) hO hE)

end OnBytes.Maker

#print axioms OnBytes.Maker.verifyWholeCR_eq
#print axioms OnBytes.Maker.verifyGuardCG_eq
#print axioms OnBytes.Maker.verifyGuardC_eq
#print axioms OnBytes.Maker.verifyGuardC_iff
#print axioms OnBytes.Maker.verifyGuardC_iffB
#print axioms OnBytes.Maker.verifyGuardC_yes
#print axioms OnBytes.Maker.verifyGuardC_eq_self
