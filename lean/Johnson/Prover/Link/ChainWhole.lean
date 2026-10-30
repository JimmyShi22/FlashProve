-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/ChainWhole.lean: THE DECISION's YES AT THE VIEW OF THE COPY's FILE's FRAME, WITH
"ALL THAT IS WANTED IS SERVED" PAID: from widths and closed tests. Statements and proofs.

  served_viewOf   Served at the frame's view, at draws as many as the rounds: from wantTie, wideTie,
                  "an opened tree's number is below 2 ^ 16", the widths of next's columns and of the
                  two stored strings' columns
  run_viewOf_at   run_viewOf (ChainLink.lean) with that premise paid

By: look_wanted (Johnson/Prover/Link/LinkFrameServed.lean), served_of_look (ChainServed.lean),
run_viewOf (ChainLink.lean).

Limits. The blocks' decisions in a row (Walks), the words' test at the view, the tests on the plan
and the instance, the last test, and four closed facts on public data stay premises. Nothing on
soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.ChainLink
import Johnson.Prover.Link.ChainServed
import Johnson.Prover.Link.LinkFrameServed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open VerifiableInference.Desc
open _root_.Run.PQ (XO SgX)
open _root_.Run (ckP)
open TypedOracleCompiler.Run.PQ (RD drawnSL uL)
open _root_.Iop (twoExternalStrings Rho)

/-- **All that is wanted is served**, at the frame's view. -/
theorem served_viewOf (ds : List RD) (a : ℕ) (xs : List XO) (decls : List Fmt.DeclaredRound)
    (next : ℕ → List Fmt.Drawn → MsgV) (y : (twoExternalStrings (2 ^ a) SgX).Str) (Ds : List Fmt.Drawn)
    (W : Bool → ℕ) (ht : wantTie a ds xs decls = true) (hw : wideTie ds W decls = true)
    (hop : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16) (hl : Ds.length = ds.length)
    (hW : ∀ j k d s, ds[j]? = some d → d.trees[k]? = some s →
      ∀ h x, ((next j h).col k x).length = s.W)
    (hy : ∀ (w : Bool) (x : ℕ) (h : x < 2 ^ a),
      ((twoExternalStrings (2 ^ a) SgX).rd y (if w then .inr ⟨x, h⟩ else .inl ⟨x, h⟩)).2.length = W w) :
    Served (lookV ds a next y Ds) ((groupsOf 0 decls Ds).flatMap id) :=
  served_of_look ds a xs decls next y Ds W ht hw fun kx hk =>
    look_wanted next ds a xs y Ds W hop hl hW hy kx hk

/-- **The decision's yes at the frame's view**, with that premise paid. -/
theorem run_viewOf_at {Xi : Type} (F : OneChainFileDescription Xi) (x : Xi) (ds : List RD) (a : ℕ) (xs : List XO)
    (next : ℕ → List Fmt.Drawn → MsgV) (y : (twoExternalStrings (2 ^ a) SgX).Str) (ρ : Rho (uL (ckP .two) ds))
    (e : F.S) (W : Bool → ℕ) (hp : F.planWord = none) (ho : F.okStart x = true)
    (hv : viewWordsBelowPrime (viewOf ds a xs next y (drawnSL (ckP .two) ds ρ)) = true)
    (h2 : List.Forall₂ IsOf2 F.roundsDeclaredByBlocks ds) (hz : ∀ d ∈ F.roundsDeclaredByBlocks, d.entry.drawNZ ≤ d.entry.drawE)
    (ht : wantTie a ds xs F.roundsDeclaredByBlocks = true) (hw : wideTie ds W F.roundsDeclaredByBlocks = true)
    (hop : ∀ d ∈ ds, ∀ n ∈ d.opens, n < 2 ^ 16)
    (hW : ∀ j k d s, ds[j]? = some d → d.trees[k]? = some s →
      ∀ h x, ((next j h).col k x).length = s.W)
    (hy : ∀ (w : Bool) (x : ℕ) (h : x < 2 ^ a),
      ((twoExternalStrings (2 ^ a) SgX).rd y (if w then .inr ⟨x, h⟩ else .inl ⟨x, h⟩)).2.length = W w)
    (hk : Walks 0 (lookV ds a next y (drawnSL (ckP .two) ds ρ)) F.chain.blocksInOrder (F.start x)
      (rvOf ds 0 [] next (drawnSL (ckP .two) ds ρ)) e)
    (he : F.fin x e = true) :
    F.run x (viewOf ds a xs next y (drawnSL (ckP .two) ds ρ)) = true :=
  run_viewOf F x ds a xs next y ρ e hp ho hv h2 hz ht
    (served_viewOf ds a xs F.roundsDeclaredByBlocks next y _ W ht hw hop (fitsDrawn_run ds ρ).length_eq.symm hW hy)
    hk he

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.served_viewOf
#print axioms Johnson.Prover.Link.run_viewOf_at
