-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FoldRun.lean: THE FOLD's ROUNDS IN A FORM THAT RUNS. foldQ
(Johnson/Prover/Link/FoldHolds.lean) is the sumcheck library's honQ at the structure Sg.par
(OnBytes/Slice/FoldPeel.lean), whose set of challenges is the whole field: the structure holds an
instance that lists the field's elements, and compiled code builds it. In trials a run of foldQ, and
of whatever calls it, was aborted and returned no value; that this instance is the cause is read off
the texts, and the form below, which has none, runs. Here honQ's own body is written out at the
stage's letters, without that structure; Lean takes the two for one by unfolding. Two definitions
with code: they define part of the honest prover; they read what foldQ and foldRV read, and no more.

Main names (namespace Johnson.Prover.Link).
  foldQc, foldQ_eq   the honest round polynomials in the form that runs; foldQ IS foldQc (by rfl).
  foldRVc, foldRV_eq   a fold's rounds (foldRV, Johnson/Prover/Link/FoldSay.lean) at foldQc; foldRV
      IS foldRVc (by rfl).

Limits. A definition that was compiled before this file (foldRV, and what calls it in
Johnson/Prover/Link/BodyAll.lean) keeps calling foldQ's own code: an equation does not turn compiled
code. What runs is foldRVc. The answer to a switch's sample (ansAt, BodyAll.lean) has no code and is
not touched here. COST: the closed form folds whole tables over functions on the cube: for tests.
Tests: Johnson/Prover/Link/FoldRunToy.lean [not in this library]. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Prover.Link.FoldSay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Slice Cb

/-- **The honest round polynomials, in a form that runs**: the sumcheck library's honQ
(Cb/Ld/LdSum.lean), its two tables written out at the stage's own letters. -/
def foldQc (s : Sg) (v μ : s.cIn.J → GE) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE) (ε : GE)
    (γ : HPt (sVars GE 2 (s.h + s.g))) : RIdx (sVars GE 2 (s.h + s.g)) → GE :=
  fun i => hTr (sVars GE 2 (s.h + s.g)) 0 W γ i +
    ε * sTr (J := s.cM.J ⊕ s.cZ.J) 2 (s.h + s.g)
      (fun b => Sum.elim (fun c => v (.inl (b, c))) fun c =>
        v (.inr (fun i => b (Fin.castAdd s.g i), c)) *
          ∏ t : Fin s.g, if b (Fin.natAdd s.h t) then 1 else 0)
      (fun b => Sum.elim (fun c => μ (.inl (b, c))) fun c =>
        μ (.inr (fun i => b (Fin.castAdd s.g i), c))) γ i

theorem foldQ_eq (s : Sg) (v μ : s.cIn.J → GE) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE) (ε : GE)
    (γ : HPt (sVars GE 2 (s.h + s.g))) : foldQ s v μ W ε γ = foldQc s v μ W ε γ := rfl

/-- **A fold's rounds, in a form that runs**: foldRV (Johnson/Prover/Link/FoldSay.lean) at
foldQc. -/
def foldRVc (s : Sg) (v μ : s.cIn.J → GE) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE)
    (D : ℕ → Fmt.Drawn) : List Fmt.RoundView :=
  ⟨[.e (ofE (hMu (sVars GE 2 (s.h + s.g)) W))], D 0⟩ ::
    showRV (s.h + s.g)
      (foldQc s v μ W (drawnE (D 0)) (ptK (s.h + s.g) fun n => drawnE (D (n + 1))))
      fun n => D (n + 1)

theorem foldRV_eq (s : Sg) (v μ : s.cIn.J → GE) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE)
    (D : ℕ → Fmt.Drawn) : foldRV s v μ W D = foldRVc s v μ W D := rfl

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.foldQ_eq
#print axioms Johnson.Prover.Link.foldRV_eq
