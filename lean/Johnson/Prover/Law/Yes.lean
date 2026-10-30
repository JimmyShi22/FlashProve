-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Law/Yes.lean: HOW LIKELY IT IS THAT THE COMPILED VERIFIER SAYS YES TO WHAT THE
COMPILED PROVER HANDS OVER: OVER THE LAW OF THE PROVER's OUTCOME AS A HYPOTHESIS. One file, one
slot.

From any table that is fresh for this chain, over the rest of the oracles uniform: the prover hands
over nothing, or a string to which verifyOneProtocol says no UNDER THE SAME ORACLES, with probability at most
(the searches' failure) + (the uniform measure of B, the test bits set to 0): if the accept law
holds outside B.

Main name: yes_law.

How. Pointwise in the oracle functions g, by (T1) yes_of_prove and (T3) proveX_returns
(OnBytes/Prover/Main.lean) and the accept law: "hands over nothing, or the verifier says no under g"
lies in "the search ran out, or the verifier messages lie in B": an event that does not read g. The
prover has no coins (T2): under g it has one outcome. So the integrand is bounded pointwise, and
Spec.prove_law bounds the rest. No step reads the table that a lazy run returns.

Limits. Spec.prove_law (Johnson/Prover/Law/Defs.lean) IS A HYPOTHESIS HERE: it is proved in another
file: Johnson/Prover/Law/Chain.lean. AccLaw IS A HYPOTHESIS: owed by the accept laws of the
protocol's steps; B is a letter beside σ, x and y, and nothing bounds its measure here: without such
a bound the right side says little. hx: the outer trees are kept rightly under EVERY completion of
the table T: owed by whoever writes the committer (its queries then have entries in T). A typed
proof string: nothing on bytes. One slot, one chain: the three files and the seeds are joined
elsewhere. No completeness of any goal's form follows from this file alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Law.Defs

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- **The compiled verifier says yes to what the compiled prover hands over, but for the searches'
failure and B's measure.** -/
theorem yes_law (H : Spec.prove_law) (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec}
    (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (y : E.Str)
    (xt : ℕ → TreeK lam L) (σ : Strat Q.loc.shape Unit) (co : Coins lam L) (cap : ℕ → ℕ)
    (T : Table (typedOracleFamily lam K L)) (hT : FreshFrom t Q.loc.shape Q.ann embP 0 T) (hw : wq.OKG)
    (hJ : FewJ Q.loc.shape Q.ann wq.sh) (h0 : Few0 Q.loc.shape Q.ann wq.sh)
    (hloc : Q.loc.IsLocal) (hC : Q.ann.Coherent) (hF : Q.ann.Fmt)
    (hDe : wq.ext.depth ≤ wq.maxDepth) (hfit : co.Fit sMT sFS depthReq)
    (hP : PutsApart Q.loc.shape Q.ann wq.sh cap 0) (hE : Function.Injective embP)
    (hx : ∀ f, ExtAt (T.over f) sMT wq.ext embE cms y xt) (B : Set (Rho Q.loc.shape))
    (acc : AccLaw Q wq x y σ B) :
    ∫⁻ f, PrCoins (T.over f) (proveX t Q wq embS embP xin cms x y xt σ co cap)
        {r | ∀ π τ, r = .ok (π, τ) →
          (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π).det (T.over f) ≠ true}
        ∂(U (typedOracleFamily lam K L)) ≤
      capFail Q.loc.shape Q.ann wq.sh cap 0 +
        pr (unif (Rho Q.loc.shape)) {ρ | RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh ρ ∈ B} := by
  have h := H t Q wq embS embP xin cms x y xt σ co cap T hT hw hF hP hE B
  unfold PrFrom at h
  refine le_trans (MeasureTheory.lintegral_mono fun f => ?_) h
  unfold PrCoins
  refine pr_mono_support _ fun r hr hbad => ?_
  rw [(noCoin_proveX t Q wq embS embP xin cms x y xt σ co cap).runEager, PMF.support_pure,
    Set.mem_singleton_iff] at hr
  rcases proveX_returns t Q wq embS embP xin cms x y xt σ co cap (T.over f) hF with
    ⟨⟨π, τ⟩, hz⟩ | ⟨j, hj, -⟩
  · refine Or.inr ⟨π, τ, hr.trans hz, ?_⟩
    by_contra hn
    obtain ⟨hp, hq, -, hy⟩ := yes_of_prove sMT sFS t Q wq embS embP xin embE depthReq cms x y xt σ
      co cap (T.over f) hw hJ h0 hloc hC hF hDe hfit (hx f) π τ hz
    exact hbad π τ (hr.trans hz) (hy (acc τ hp hq hn))
  · exact Or.inl ⟨j, hr.trans hj⟩

end OnBytes.Prover

#print axioms OnBytes.Prover.yes_law
