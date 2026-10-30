-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Law/YesProved.lean: yes_law (Johnson/Prover/Law/Yes.lean) AT THE PROVED LAW OF THE
PROVER's OUTCOME (prove_law, Johnson/Prover/Law/Chain.lean): no hypothesis on that law is left. One
theorem: one call. Its statement is yes_law's, made by program out of that file's text.

Limits. Yes.lean's, but for the first: AccLaw IS A HYPOTHESIS, and nothing bounds B's measure here;
hx is owed by whoever writes the committer; one slot, one chain; a typed proof string. No
completeness of any goal's form follows from this file alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Law.Yes
import Johnson.Prover.Law.Chain

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- **The compiled verifier says yes to what the compiled prover hands over, but for the searches'
failure and B's measure.** -/
theorem yes_bound (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec}
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
        pr (unif (Rho Q.loc.shape)) {ρ | RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh ρ ∈ B} :=
  yes_law prove_law sMT sFS t Q wq embS embP xin embE depthReq cms x y xt σ co cap T hT hw hJ h0
    hloc hC hF hDe hfit hP hE hx B acc

end OnBytes.Prover

#print axioms OnBytes.Prover.yes_bound
