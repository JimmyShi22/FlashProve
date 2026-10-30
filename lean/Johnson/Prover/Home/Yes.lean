-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Home/Yes.lean: THE POINTWISE JOIN FROM ITS PAYERS, AT LETTERS: JoinFits gives HomeYes
(Johnson/Prover/Home/Letters.lean).

How. At a hash function: the prover's value is the print of the typed runs' value (det_proveForm,
Johnson/Prover/Home/Defs.lean); outside the event the runs' value is good (all_good,
Johnson/Prover/All/Good.lean): a proof, its ends, and the compiled verifier's yes at the committer's
own key; the commitment is the hash function's answer at that key's code (JoinFits.commit); the rest
is JoinFits.printed.

Main names.
  evaluate_pd   the prover's value at a hash function.
  home_yes      THE STATEMENT.

Limits. Pointwise in the hash function: no probability. JoinFits' fields are premises; the field
"printed" holds all that is said of bytes.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Home.Letters
import Johnson.Top.InnerCompiledVerifierYes
import Run.RunIsVProofs

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open VerifiableInference VerifiableInference.OnPublicFiles
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {system : ArgumentSystem} {R : InnerCompilerInput} {T : LayoutsByPublicReading R} (H : HomeLetters system T)

/-- The prover's value at a hash function: the print of the typed runs' value. -/
theorem evaluate_pd
    (hc : ∀ w ρ p o a d g,
      (H.carry d (runsAt T H.b₀ H.st H.capT H.capL H.capB d (H.isk w ρ d) (H.xOf p o)
        (H.drawOf d ρ a))).det g =
      (runsAt T H.b₀ H.st H.capT H.capL H.capB d (H.isk w ρ d) (H.xOf p o)
        (H.drawOf d ρ a)).det (readBlocks (T.m d) g))
    (w : system.Weights) (ρ : system.CommitmentRandomness) (p o : List Token) (a : Fin (H.N + 1))
    (hash : Hash) :
    (H.pd w ρ p o a).evaluate hash =
      H.print w ρ p o a (T.Pub.det (Run.famOne hash)) (H.Y w ρ p o a hash) := by
  unfold HomeLetters.pd
  rw [evaluate_deterministicOf_det, Run.det_ofRom]
  exact det_proveForm T H.b₀ H.st H.capT H.capL H.capB H.carry (H.isk w ρ) (H.xOf p o)
    (fun d => H.drawOf d ρ a) (H.print w ρ p o a) (Run.famOne hash)
    (hc w ρ p o a (T.Pub.det (Run.famOne hash)) (Run.famOne hash))

/-- **The pointwise join.** -/
theorem home_yes (domain : system.Weights → List Token → List Token → Prop)
    (J : JoinFits H domain) : HomeYes H domain := by
  intro w p o hd hm t a hash hn
  obtain ⟨π, e₁, e₂, τT, τL, τB, hx, E, aT', aL', aB', hnum, hy⟩ :=
    all_good R.queryLayout (T.Sd (T.Pub.det (Run.famOne hash))) (T.cA (T.Pub.det (Run.famOne hash))) R.fixedSample R.compilerParameters
      H.b₀ H.st H.capT H.capL H.capB (readBlocks (T.m (T.Pub.det (Run.famOne hash))) (Run.famOne
          hash))
      (J.wires _) (H.back w) (H.r₁ (H.ρOf t)) (H.s₁ (T.Pub.det (Run.famOne hash)) (H.ρOf t))
      (H.xOf p o) (H.drawOf (T.Pub.det (Run.famOne hash)) (H.ρOf t) a) (J.salts _ _) (J.draw _ _ _)
      (H.Bs w p o t a (T.Pub.det (Run.famOne hash))) (J.acc w p o hd hm t a _) hn
  rw [evaluate_pd H J.carry_det, J.commit]
  refine J.printed w p o hd hm t a hash π e₁ e₂ τT τL τB ?_ E aT' aL' aB' hnum hy
  rw [← hx, det_allX]
  rfl

end OnBytes.Prover
