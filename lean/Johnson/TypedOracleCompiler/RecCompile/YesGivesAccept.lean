-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/TypedOracleCompiler/RecCompile/YesGivesAccept.lean: where the compiled verifier says yes at fixed oracle
functions, the slot's own decision has said yes at the transcript that the verifier has made of the
proof string and of the verifier messages that its chain has drawn from these oracle functions.

Why. A law on a typed reduction speaks of a typed transcript τ ("where the reduction says yes at τ,
every written round's test of work has passed": `verify_asks_work`,
OnBytes/Flat/VerifyAsksWork.lean [not in this library]). A run calls the compiled verifier. The compiler's text ends in
the conjunct `Q.loc.accept x _ (mkTr … ρ …)` (`afterF`, OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean), ρ
being what the chain (`recomputeChainOfProof`) returns. The library's proof of soundness takes that conjunct out
in passing (`mem_of_accepted`, OnBytes/TypedOracleCompiler/Compile/Batch/Sound.lean); here it is a statement of its
own, on values
(`OComp.det`, Rom/Cache.lean: the result under fixed oracle functions).
  `verifyBS_yes`: one slot, general in the slot.
  `YesAt`: its conclusion, as a name.
  `VCA_yes`: the verifier for an object with records (`verifyAtFullKey`, CmsAns.lean): the key's test, the link
  and the session, each with its own chain and transcript.
  By `mkTr_rho` (OnBytes/TypedOracleCompiler/Compile/Batch/Runs.lean) the verifier messages of that transcript are
  ρ.
Limits. One direction. Nothing on the openings, the roots or the request tree, which the verifier
checks as well. Nothing on probabilities: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.CmsAns
import Rom.Cache

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- At the oracle functions g the slot's chain returns verifier messages, and the slot's decision
says yes at the transcript made of the proof string and of them. -/
def YesAt (g : Fam (typedOracleFamily lam K L)) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t))
    (xin : Y → Option X) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) : Prop :=
  ∃ ρ rts ph, (recomputeChainOfProof t Q wq embP xin cms x π).det g = some (ρ, rts, ph) ∧
    Q.loc.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
      (mkTr Q.loc.shape Q.ann wq.sh rts π.plains ρ π.opens) = true

/-- **A yes of the compiled verifier of a slot.** -/
theorem verifyBS_yes (g : Fam (typedOracleFamily lam K L)) (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec}
    (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)
    (h : (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π).det g = true) :
    YesAt g t Q wq embP xin cms x π := by
  unfold verifyOneProtocol at h
  rw [OComp.det_bind] at h
  cases hr : (recomputeChainOfProof t Q wq embP xin cms x π).det g with
  | none =>
    rw [hr] at h
    exact absurd h (by show ¬ (false = true); decide)
  | some z =>
    obtain ⟨ρ, rts, ph⟩ := z
    rw [hr] at h
    refine ⟨ρ, rts, ph, hr, ?_⟩
    dsimp only at h
    split at h
    · unfold checkPrunedOpenings at h
      split at h
      · split at h
        · unfold afterF at h
          rw [OComp.det_bind, OComp.det_bind] at h
          exact (Bool.and_eq_true_iff.1 h).2
        · exact absurd h (by show ¬ (false = true); decide)
      · exact absurd h (by show ¬ (false = true); decide)
    · exact absurd h (by show ¬ (false = true); decide)

end TypedOracleCompiler.Compile.Batch

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec)

/-- **A yes of the verifier for an object with records**: the key's test, the link, the session. -/
theorem VCA_yes (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (p : Params)
    (v : FullKey lam L aT aL) (x : X) (π : RequestProof lam L)
    (h : (verifyAtFullKey W S cA r₀ p v x π).det g = true) :
    ∃ πT cmj recj πL πB, v.piT = some πT ∧ v.links[π.leaf]? = some (cmj, recj, some πL) ∧
      π.piB = some πB ∧
      YesAt g Tag.test (batTC L aT) (wTC W) id (fun _ => none) (cmsTA cA v.cm v.rcd.2) v.rcd πT ∧
      YesAt g Tag.link (batLC L aL) (wLC W) id (fun _ => none)
        (cmsLA cA v.cm cmj v.rcd.2 recj.2) (v.rcd, recj) πL ∧
      YesAt g Tag.onl L.onlineBatch (wBC W) id (xinBA r₀) (cmsBA cA cmj recj.2) (x, recj) πB := by
  unfold verifyAtFullKey at h
  split at h
  · rename_i πT cmj recj πL πB e1 e2 e3
    rw [OComp.det_bind, OComp.det_bind, OComp.det_bind, OComp.det_bind, OComp.det_bind] at h
    have h' := h
    simp only [OComp.det, Bool.and_eq_true] at h'
    obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, ha⟩, hb⟩, hc⟩ := h'
    exact ⟨πT, cmj, recj, πL, πB, e1, e2, e3,
      verifyBS_yes g p.sMT p.sFS Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none) W.embE
        W.depthReqT (cmsTA cA v.cm v.rcd.2) v.rcd πT ha,
      verifyBS_yes g p.sMT p.sFS Tag.link (batLC L aL) (wLC W) W.embL id (fun _ => none) W.embE
        W.depthReqL (cmsLA cA v.cm cmj v.rcd.2 recj.2) (v.rcd, recj) πL hb,
      verifyBS_yes g p.sMT p.sFS Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀) W.embE W.depthReq
        (cmsBA cA cmj recj.2) (x, recj) πB hc⟩
  · exact absurd h (by show ¬ (false = true); decide)

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms TypedOracleCompiler.Compile.Batch.verifyBS_yes
#print axioms TypedOracleCompiler.Compile.Batch.Cms.VCA_yes
