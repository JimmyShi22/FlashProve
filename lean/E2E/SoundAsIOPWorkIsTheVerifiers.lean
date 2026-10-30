-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/SoundAsIOPWorkIsTheVerifiers.lean: THE BITS OF PROOF OF WORK THAT THE WIRES AT Z DECLARE ARE THE BITS THAT
THE THREE VERIFIERS TEST: at every Z and for any provers P, the offline, the link's and the online
verifier accept only a transcript whose challenges pass every test of the wires (RoundsQueryLayout.pass at
(wTC W).sh, (wLC W).sh, (wBC W).sh; W the verifier's wiring at Z). The proof of
Statements.verifiersAskTheWork (E2E/SoundAsIOPProbabilityAtFiles.lean).

Why. The probability of E2E/SoundAsIOPProbabilityAtFiles.lean is taken over "the challenges that pass". The
wires are data of the compiler. With this theorem the challenges that pass are the verifiers' own: the
only ones at which they accept.

CALLS ALONE. What is spent: wholeIOR_out_iff (OnBytes/Maker/WholeViews.lean: a whole file's verifier says
yes exactly where its nine tests do, the three chains' tests of work among them), LPFFrame.pass_whole
(Johnson/LPFFrame/Proofs.lean: the wires' tests of a whole file are these three), pass_wiresSL
(Johnson/Prover/Link/LinkFrame.lean: the like for the link).

  wholeFile_asksTheWork     a whole file's verifier (the offline and the online part are such).
  link_asksTheWork          the link's.
  offline_asksTheWork | linkAtFrame_asksTheWork | online_asksTheWork   at the wiring wireOfFullD, at any data
                            of rounds; the provers of the object and those in the wiring are two letters.
  verifiersAskTheWork       at every Z and P.

Limits. One direction: that a verifier accepts anything is not said. Nothing on soundness.
-/
import E2E.SoundAsIOPProbabilityAtFiles
import Johnson.Flat.Dec.WiresAtSizes
import Johnson.LPFFrame.Proofs
import Johnson.Prover.Link.LinkFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Prover
open _root_.Iop (Tr Tr.rho Rho Dig oneExternalString)
open _root_.Run.PQ (CK View XO SgX)
open OnBytes.Maker (WholeD chainsOf reductionOfWholeFile wqWhole wholeIOR_out_iff)
open TypedOracleCompiler.Iop (RoundsQueryLayout.pass)
open TypedOracleCompiler.Run.PQ (RD uL passSL rhoSL)
open OnBytes.Flat (linkSkeletonOfRoundData linkProtocolOfRoundData)
open Johnson.RunOne.StrictW (wqW)

/-! ## The two kinds of verifier -/

section Whole
variable (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (D : WholeD)
  {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- **A whole file's verifier says yes only where the wires' tests pass.** -/
theorem wholeFile_asksTheWork (x : Xi) (y : (oneExternalString (2 ^ D.a) SgX).Str)
    (τ : Tr (chainsOf C D tF tJ t3).sh)
    (h : ((reductionOfWholeFile C D tF tJ t3 silent run).out x y τ).isSome = true) :
    RoundsQueryLayout.pass _ _ (wqWhole C K chal D tF tJ t3 silent run).sh τ.rho = true := by
  rw [wholeIOR_out_iff] at h
  rw [LPFFrame.pass_whole C K chal D tF tJ t3 silent run τ, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨h.1.1, h.1.2.1⟩, h.1.2.2⟩

end Whole

/-- The link's reading of a transcript's challenges is the transcript's challenges. -/
theorem rhoSL_eq_rho (C : CK) : ∀ (ds : List RD) (τ : Tr (uL C ds)), rhoSL C ds τ = τ.rho
  | [], _ => rfl
  | d :: ds, (_, c, τ) => by
      show ((c, rhoSL C ds τ) : Rho (uL C (d :: ds))) = (c, τ.rho)
      rw [rhoSL_eq_rho C ds τ]

/-- **The link's verifier accepts only where the wires' tests pass.** -/
theorem link_asksTheWork (C : CK) (ds : List RD) (a : ℕ) (xs : List XO) {X : Type}
    (dec : X → View → Bool) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (x : X) (y) (τ : Tr (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape)
    (h : (linkProtocolOfRoundData C ds a xs dec).accept x y τ = true) :
    RoundsQueryLayout.pass (linkSkeletonOfRoundData C ds a xs dec).up.loc.shape (linkSkeletonOfRoundData C ds a xs dec).up.ann
      (wqW C ds a xs dec K chal).sh τ.rho = true := by
  obtain ⟨m0, c0, τ⟩ := τ
  have h' : (passSL C ds (rhoSL C ds τ) && _ && _ && _) = true := h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h'
  refine Bool.and_eq_true_iff.2 ⟨rfl, ?_⟩
  exact (Johnson.Prover.Link.pass_wiresSL C K chal ds τ.rho).trans
    ((congrArg _ (rhoSL_eq_rho C ds τ)).symm.trans h'.1.1.1)

/-! ## The wiring of the three files at the full size -/

section Frame
open _root_.Run
open TypedOracleCompiler.Compile.Batch.Cms (wTC wLC wBC)
open VerifiableInference.OnPublicFiles OnBytes.Flat OnBytes.Slice

variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD)
  (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
  (dec : RecFull × RecFull → PQ.View → Bool) (rK rP : RecFull) (depthReq : ℕ)
  (early : X → X) (salt : ℕ)
  (P P' : (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt).Provers)
  (K depthReqT : ℕ)

local notation "WW" =>
  wireOfFullD A R DK DP runK runP ds xs dec rK rP depthReq early salt P' K depthReqT
set_option quotPrecheck false in
local notation "LL" =>
  (Files.withProvers (threeProtocolsAtFullSize A R DK DP runK runP ds xs dec rK rP depthReq early salt) P)

theorem offline_asksTheWork (x) (y) (τ : Tr (LL).offline.shape)
    (h : (LL).offline.accept x y τ = true) : RoundsQueryLayout.pass _ _ (wTC WW).sh τ.rho = true :=
  wholeFile_asksTheWork (ckP .two) K (chalP .two K) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
    ByteArray.empty silK runK x y τ h

theorem linkAtFrame_asksTheWork (x) (y) (τ : Tr (LL).link.shape)
    (h : (LL).link.accept x y τ = true) : RoundsQueryLayout.pass _ _ (wLC WW).sh τ.rho = true :=
  link_asksTheWork (ckP .two) ds frS.P.T.a xs dec K (chalP .two K) x y τ h

theorem online_asksTheWork (x) (y) (τ : Tr (LL).onlineBatch.loc.shape)
    (h : (LL).onlineBatch.loc.accept x y τ = true) : RoundsQueryLayout.pass _ _ (wBC WW).sh τ.rho = true :=
  wholeFile_asksTheWork (ckP .two) K (chalP .two K) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
    ByteArray.empty silP runP x y τ h

end Frame

end OnBytes.Prover

namespace AtPublicFiles.AtFiles

theorem verifiersAskTheWork : Statements.verifiersAskTheWork := fun _ P =>
  ⟨fun x y τ h =>
      OnBytes.Prover.offline_asksTheWork _ _ _ _ _ _ _ _ _ _ _ _ _ _ P _ _ _ x y τ h,
    fun x y τ h =>
      OnBytes.Prover.linkAtFrame_asksTheWork _ _ _ _ _ _ _ _ _ _ _ _ _ _ P _ _ _ x y τ h,
    fun x y τ h =>
      OnBytes.Prover.online_asksTheWork _ _ _ _ _ _ _ _ _ _ _ _ _ _ P _ _ _ x y τ h⟩

end AtPublicFiles.AtFiles

#print axioms OnBytes.Prover.wholeFile_asksTheWork
#print axioms OnBytes.Prover.link_asksTheWork
#print axioms AtPublicFiles.AtFiles.verifiersAskTheWork
