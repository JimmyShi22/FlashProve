-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/RoundsTView.lean: a written transcript over rounds that may send several roots, read as
a written transcript over rounds with at most one tree; what a view's rounds, the draws and the
tests of work are is the same on both.

OnBytes/Slice/ states what a verifier's run reads of a written transcript over `PQ.uL (ckP .two) ds`
(`PQ.rvSL`, `PQ.drawnSL`, `PQ.passSL`, Run/PlanQS.lean; `rsOf`, OnBytes/Slice/Stage.lean). A file's
chains are written over `uLT (ckP .two) ds` (`rvT`, `drawnT`, `passT`, OnBytes/Maker/Trees.lean).
Here a transcript of the second kind is mapped to one of the first, and these readings agree.
Definitions and proofs, each by induction on the list with `rfl` at a round.

Main names:
  `trRD ds τ`: each prover message by `msgRD` (OnBytes/Flat/RoundsT.lean): its plain part is kept,
    its oracle is the round's fixed one; each verifier message as it is.
  `rhoRD ds ρ`: the verifier's messages alone. `rhoSL_trRD`.
  `rvT_eq`, `drawnT_eq`, `passT_eq`: the rounds of a view, what was drawn, the tests of work.
  `rsT ds τ`, `rsT_cons`: what the format's decision reads of the rounds.
Limits: nothing that reads the oracles of a written round is carried: `trRD` drops them. So nothing
here speaks of a column, a position or a tree.
-/
import OnBytes.Flat.RoundsT
import OnBytes.Slice.Stage

set_option autoImplicit false

namespace OnBytes.Flat
open Iop Run Run.PQ OnBytes.Maker OnBytes.Slice

/-- A written transcript, read over the rounds with at most one tree. -/
def trRD : (ds : List RDT) → Tr (uLT (ckP .two) ds) → Tr (PQ.uL (ckP .two) (ds.map toRD))
  | [], _ => ()
  | d :: ds, (m, c, τ) => (msgRD d m, c, trRD ds τ)

/-- The verifier's messages alone. -/
def rhoRD : (ds : List RDT) → Rho (uLT (ckP .two) ds) → Rho (PQ.uL (ckP .two) (ds.map toRD))
  | [], _ => ()
  | _ :: ds, (c, ρ) => (c, rhoRD ds ρ)

theorem rhoSL_trRD : ∀ (ds : List RDT) (τ : Tr (uLT (ckP .two) ds)),
    PQ.rhoSL (ckP .two) (ds.map toRD) (trRD ds τ) = rhoRD ds (rhoT (ckP .two) ds τ)
  | [], _ => rfl
  | _ :: ds, (_, c, τ) => congrArg (Prod.mk c) (rhoSL_trRD ds τ)

/-- The rounds of a view. -/
theorem rvT_eq : ∀ (ds : List RDT) (τ : Tr (uLT (ckP .two) ds)),
    rvT (ckP .two) ds τ = PQ.rvSL (ckP .two) (ds.map toRD) (trRD ds τ)
  | [], _ => rfl
  | _ :: ds, (_, _, τ) => congrArg (List.cons _) (rvT_eq ds τ)

/-- What was drawn. -/
theorem drawnT_eq : ∀ (ds : List RDT) (ρ : Rho (uLT (ckP .two) ds)),
    drawnT (ckP .two) ds ρ = PQ.drawnSL (ckP .two) (ds.map toRD) (rhoRD ds ρ)
  | [], _ => rfl
  | _ :: ds, (_, ρ) => congrArg (List.cons _) (drawnT_eq ds ρ)

/-- The tests of work. -/
theorem passT_eq : ∀ (ds : List RDT) (ρ : Rho (uLT (ckP .two) ds)),
    passT (ckP .two) ds ρ = PQ.passSL (ckP .two) (ds.map toRD) (rhoRD ds ρ)
  | [], _ => rfl
  | _ :: ds, (c, ρ) => congrArg (fun b => GChal.pass c && b) (passT_eq ds ρ)

/-- What the format's decision reads of the rounds. -/
def rsT (ds : List RDT) (τ : Tr (uLT (ckP .two) ds)) : Fmt.M1.Rs := rsOf (ds.map toRD) (trRD ds τ)

theorem rsT_cons (d : RDT) (ds : List RDT) (m : (wT d).Msg) (c : (wT d).Chal)
    (τ : Tr (uLT (ckP .two) ds)) :
    rsT (d :: ds) (m, c, τ) = rvOf (toRD d) (msgRD d m) c :: rsT ds τ := rfl

end OnBytes.Flat

#print axioms OnBytes.Flat.rvT_eq
#print axioms OnBytes.Flat.drawnT_eq
#print axioms OnBytes.Flat.passT_eq
