-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/ChainLink.lean: THE DECISION's YES AT THE VIEW OF THE COPY's FILE's FRAME, from
the blocks' decisions in a row. General in the one-chain description F and in the protocol's letters
(the rounds' data ds, the stored strings' depth a, the external openings xs), at the library's
challenge kit ckP .two. One statement and its proof.

  run_viewOf   the tests on the plan and on the instance · the words' test at the view · two closed
               ties of the protocol's letters to F's declared rounds (IsOf2 round by round; wantTie)
               · no entry asks more elements other than 0 than elements · all that is wanted is
               served · the blocks' decisions in a row (Walks) · the last test: so
               F.run x (viewOf ds a xs next y (drawnSL (ckP .two) ds rho)) = true: the premise on
               the decision of accLaw_link (Johnson/Prover/Link/LinkFrame.lean)

By: run_of_walks (ChainYes.lean), roundsFit_rvOf, drawn_rvOf, fitsDrawn_run (ChainRounds.lean),
opened_colsFor (ChainCols.lean).

Limits. Every premise is a premise: none is shown at any letters here. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.ChainYes
import Johnson.Prover.Link.ChainRounds
import Johnson.Prover.Link.ChainCols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open VerifiableInference.Desc
open _root_.Run.PQ (XO SgX)
open _root_.Run (ckP)
open TypedOracleCompiler.Run.PQ (RD drawnSL uL)
open _root_.Iop (twoExternalStrings Rho)

/-- **The decision's yes at the frame's view.** -/
theorem run_viewOf {Xi : Type} (F : OneChainFileDescription Xi) (x : Xi) (ds : List RD) (a : ℕ) (xs : List XO)
    (next : ℕ → List Fmt.Drawn → MsgV) (y : (twoExternalStrings (2 ^ a) SgX).Str) (ρ : Rho (uL (ckP .two) ds))
    (e : F.S) (hp : F.planWord = none) (ho : F.okStart x = true)
    (hv : viewWordsBelowPrime (viewOf ds a xs next y (drawnSL (ckP .two) ds ρ)) = true)
    (h2 : List.Forall₂ IsOf2 F.roundsDeclaredByBlocks ds) (hz : ∀ d ∈ F.roundsDeclaredByBlocks, d.entry.drawNZ ≤ d.entry.drawE)
    (ht : wantTie a ds xs F.roundsDeclaredByBlocks = true)
    (hs : Served (lookV ds a next y (drawnSL (ckP .two) ds ρ))
      ((groupsOf 0 F.roundsDeclaredByBlocks (drawnSL (ckP .two) ds ρ)).flatMap id))
    (hw : Walks 0 (lookV ds a next y (drawnSL (ckP .two) ds ρ)) F.chain.blocksInOrder (F.start x)
      (rvOf ds 0 [] next (drawnSL (ckP .two) ds ρ)) e)
    (he : F.fin x e = true) :
    F.run x (viewOf ds a xs next y (drawnSL (ckP .two) ds ρ)) = true := by
  have hd : (viewOf ds a xs next y (drawnSL (ckP .two) ds ρ)).rounds.map (·.drawn) =
      drawnSL (ckP .two) ds ρ :=
    drawn_rvOf next ds 0 [] _ (fitsDrawn_run ds ρ).length_eq.symm
  refine run_of_walks F x (lookV ds a next y (drawnSL (ckP .two) ds ρ)) e _ hp ho hv
    (roundsFit_rvOf next F.roundsDeclaredByBlocks ds h2 hz 0 [] ρ) ?_ ?_ hw he
  · rw [hd]
    exact hs
  · rw [hd]
    exact opened_colsFor ds a xs F.roundsDeclaredByBlocks next y _ ht hs

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.run_viewOf
