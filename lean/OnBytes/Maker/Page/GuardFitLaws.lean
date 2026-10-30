-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/GuardFitLaws.lean: laws of the run with a second test on each query
(OnBytes/Maker/Page/GuardFit.lean).

Main names:
  `detG_mono`: a value of the guarded run under a stricter test is its value under a laxer one.
  `runGuardFit_guard`: so a value of `runGuardFit` is the value of `runGuard`.
  `verifyGuardFit_yes`: a yes of `verifyGuardFit` is a yes of `verifyGuard`: every law on that yes
    (OnBytes/Maker/Page/GuardLaws.lean) serves.
  `verifyGuardFit_agree`: and a yes of `verifyOneProtocol` under every family that agrees with the page's at
    the queries that `okJ P` and `fit` pass. At the page's own family it says no more than
    verifyGuardFit_yes with verifyGuard_yes. At every first call of a chain that passes both tests
    such a family must answer zeros in the K front blocks, as no drawn family and no encoding behind
    an escape does (the docstring of verifyGuard_agree, GuardLaws.lean): it is no bridge to another
    family, and is not to be cited as one.
  `runGuardFit_all`: at the test that passes everything it is `runGuard`.
No law of this file says that a yes has passed `fit` at every query asked. No
letter stands under "there is".

What is not claimed. What the head of OnBytes/Maker/Page/GuardFit.lean does not claim. A yes under
the tag `.link`, or where the chain does not join: `verifyGuardFit` is the constant no there (that
head, "To be minded"), so `verifyGuardFit_yes` and `verifyGuardFit_agree` are empty there. Nothing
on soundness.


-/
import OnBytes.Maker.Page.GuardFit
import OnBytes.Maker.Page.GuardLaws

set_option autoImplicit false

namespace OnBytes.Maker.Page

open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol ProtocolQueryLayout
open _root_.Run

/-- **A value under a stricter test is the value under a laxer one.** -/
theorem detG_mono {S : OSpec} {α : Type} {ok ok' : ∀ o : S.ι, S.Dom o → Bool}
    (hk : ∀ o q, ok' o q = true → ok o q = true) (g : Fam S) (c : OComp S α) {a : α}
    (h : detG ok' g c = some a) : detG ok g c = some a := by
  induction c with
  | pure b => exact h
  | query o q k ih =>
    have h' : (if ok' o q then detG ok' g (k (g o q)) else none) = some a := h
    show (if ok o q then detG ok g (k (g o q)) else none) = some a
    by_cases e : ok' o q = true
    · rw [if_pos e] at h'
      rw [if_pos (hk o q e)]
      exact ih _ h'
    · rw [if_neg e] at h'
      cases h'
  | sample n k ih => exact ih _ h

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

/-- A value of the run with the second test is the value of the run without it. -/
theorem runGuardFit_guard {α : Type} (P : PageJ L K) (O : ByteArray → ByteArray)
    (fit : (o : OracleName) → domOf 256 L o → Bool) (c : OComp (typedOracleFamily 256 K L) α) {a : α}
    (h : runGuardFit P O fit c = some a) : runGuard P O c = some a :=
  detG_mono (S := typedOracleFamily 256 K L) (ok := okJ P) (ok' := okFitJ P fit)
    (fun _ _ e => (Bool.and_eq_true_iff.1 e).1) (gJ P O) c h

/-- At the test that passes everything it is the run without a second test. -/
theorem runGuardFit_all {α : Type} (P : PageJ L K) (O : ByteArray → ByteArray)
    (c : OComp (typedOracleFamily 256 K L) α) : runGuardFit P O (fun _ _ => true) c = runGuard P O c := by
  have e : okFitJ P (fun _ _ => true) = okJ P := by
    funext o q
    exact Bool.and_true _
  unfold runGuardFit runGuard
  rw [e]

section V
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
  (wq : ProtocolQueryLayout 256 K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Y) (π : OneProtocolProof 256 Q)

/-- **A yes with the second test is a yes of `verifyGuard`.** -/
theorem verifyGuardFit_yes (P : PageJ L K) (O : ByteArray → ByteArray)
    (fit : (o : OracleName) → domOf 256 L o → Bool)
    (h : verifyGuardFit P O fit sMT sFS t Q wq embS embP xin embE depthReq cms x π = true) :
    verifyGuard P O sMT sFS t Q wq embS embP xin embE depthReq cms x π = true := by
  unfold verifyGuardFit at h
  unfold verifyGuard
  cases e : runGuardFit P O fit
      (verifyBSR P.sR sMT sFS t Q wq embS embP xin embE depthReq cms x π) with
  | none =>
    rw [e] at h
    cases h
  | some b =>
    rw [e] at h
    rw [runGuardFit_guard P O fit _ e]
    exact h

/-- **A yes with the second test is a yes of `verifyOneProtocol` under every family that agrees with the
page's at the queries that `okJ P` and `fit` pass.** At the page's own family it says no more than
verifyGuardFit_yes with verifyGuard_yes. At every first call of a chain that passes both tests such
a family must answer zeros in the K front blocks, as no drawn family and no encoding behind an
escape does (the docstring of verifyGuard_agree, GuardLaws.lean): it is no bridge to another family,
and is not to be cited as one. -/
theorem verifyGuardFit_agree (P : PageJ L K) (O : ByteArray → ByteArray)
    (fit : (o : OracleName) → domOf 256 L o → Bool) (g : Fam (typedOracleFamily 256 K L))
    (hg : ∀ o q, okFitJ P fit o q = true → gJ P O o q = g o q)
    (h : verifyGuardFit P O fit sMT sFS t Q wq embS embP xin embE depthReq cms x π = true) :
    (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π).det g = true := by
  unfold verifyGuardFit at h
  cases e : runGuardFit P O fit
      (verifyBSR P.sR sMT sFS t Q wq embS embP xin embE depthReq cms x π) with
  | none =>
    rw [e] at h
    cases h
  | some b =>
    rw [e] at h
    have hb : b = true := h
    rw [hb] at e
    exact (verifyBSR_det sMT sFS t Q wq embS embP xin embE depthReq cms x π P.sR g
      (detG_det_of_agree (S := typedOracleFamily 256 K L) (okFitJ P fit) hg _ e)).2

end V

end OnBytes.Maker.Page

#print axioms OnBytes.Maker.Page.detG_mono
#print axioms OnBytes.Maker.Page.runGuardFit_guard
#print axioms OnBytes.Maker.Page.runGuardFit_all
#print axioms OnBytes.Maker.Page.verifyGuardFit_yes
#print axioms OnBytes.Maker.Page.verifyGuardFit_agree
