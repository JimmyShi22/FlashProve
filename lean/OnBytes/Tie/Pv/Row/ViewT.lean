-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Row/ViewT.lean: a stretch of a file's written rounds, read as the rounds of the view
that the Lean verifier's routines take, and the condition that all its tests of work pass.

A chain of a file has the written rounds uLT C ds, for a list ds of rounds' data
(OnBytes/Maker/Trees.lean). Of a written transcript that file makes the list of rounds that the
verifier's routines read (rvT) and the test that every round's proof of work is met (passT). A law
that ties a routine's run to a typed block speaks of one stretch of rounds. This file fixes the two
readings of a stretch at the kit in which a verifier message is hash blocks, with their laws at a
first round, so that all such laws are stated in the same words. Definitions, statements and proofs.

Main names:
  `vT ds τ`: the rounds of the view that is made of the written transcript τ of the stretch ds.
  `okT ds τ`: every round's test of work passes.
  `vT_nil`, `vT_cons`, `vT_one`, `vT_two`: the view round by round: a round's items are those of
    the prover's plain part; what it drew is what the kit makes of the verifier message.
  `okT_nil`, `okT_cons`, `okT_one`, `okT_two`: the condition round by round.
  `vT_length`: a view has as many rounds as the stretch.

Limits: the view forgets a written round's oracle part, its nonce and its test bits, and of the
hash blocks all but what the sampler makes of them: a view does not determine the written
transcript. Nothing on two stretches in a row.
-/
import OnBytes.Maker.Trees
import Run.PlanPull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Row

open Iop OnBytes.Maker

/-- The rounds of the view that is made of a written transcript of the stretch ds. -/
def vT (ds : List RDT) (τ : Tr (uLT (Run.ckP .two) ds)) : List Fmt.RoundView := rvT (Run.ckP .two) ds τ

/-- Every round's test of work passes. -/
def okT (ds : List RDT) (τ : Tr (uLT (Run.ckP .two) ds)) : Prop :=
  passT (Run.ckP .two) ds (rhoT (Run.ckP .two) ds τ) = true

/-- One round of the view. -/
def rvOne (d : RDT) (m : (roundT (Run.ckP .two) d).up.Msg)
    (c : (roundT (Run.ckP .two) d).up.Chal) : Fmt.RoundView :=
  ⟨Run.PQ.PlainOf.gots d.items (GPlain.old (b := d.entry.work) m.2),
    (Run.ckP .two).dr d.entry d.kind (GChal.old (b := d.entry.work) c)⟩

theorem vT_nil (τ : Tr (uLT (Run.ckP .two) [])) : vT [] τ = [] := rfl

theorem vT_cons (d : RDT) (ds : List RDT) (m : (roundT (Run.ckP .two) d).up.Msg)
    (c : (roundT (Run.ckP .two) d).up.Chal) (τ : Tr (uLT (Run.ckP .two) ds)) :
    vT (d :: ds) ((m, c, τ) : Tr (uLT (Run.ckP .two) (d :: ds))) = rvOne d m c :: vT ds τ := rfl

theorem vT_one (d : RDT) (m : (roundT (Run.ckP .two) d).up.Msg)
    (c : (roundT (Run.ckP .two) d).up.Chal) :
    vT [d] ((m, c, ()) : Tr (uLT (Run.ckP .two) [d])) = [rvOne d m c] := rfl

theorem vT_two (d₁ d₂ : RDT) (m₁ : (roundT (Run.ckP .two) d₁).up.Msg)
    (c₁ : (roundT (Run.ckP .two) d₁).up.Chal) (m₂ : (roundT (Run.ckP .two) d₂).up.Msg)
    (c₂ : (roundT (Run.ckP .two) d₂).up.Chal) :
    vT [d₁, d₂] ((m₁, c₁, m₂, c₂, ()) : Tr (uLT (Run.ckP .two) [d₁, d₂])) =
      [rvOne d₁ m₁ c₁, rvOne d₂ m₂ c₂] := rfl

theorem okT_nil (τ : Tr (uLT (Run.ckP .two) [])) : okT [] τ := rfl

theorem okT_cons (d : RDT) (ds : List RDT) (m : (roundT (Run.ckP .two) d).up.Msg)
    (c : (roundT (Run.ckP .two) d).up.Chal) (τ : Tr (uLT (Run.ckP .two) ds)) :
    okT (d :: ds) ((m, c, τ) : Tr (uLT (Run.ckP .two) (d :: ds))) ↔
      GChal.pass (b := d.entry.work) c = true ∧ okT ds τ := by
  show (GChal.pass (b := d.entry.work) c &&
    passT (Run.ckP .two) ds (rhoT (Run.ckP .two) ds τ)) = true ↔ _
  rw [Bool.and_eq_true]
  rfl

theorem okT_one (d : RDT) (m : (roundT (Run.ckP .two) d).up.Msg)
    (c : (roundT (Run.ckP .two) d).up.Chal) :
    okT [d] ((m, c, ()) : Tr (uLT (Run.ckP .two) [d])) ↔
      GChal.pass (b := d.entry.work) c = true :=
  (okT_cons d [] m c ()).trans ⟨fun h => h.1, fun h => ⟨h, okT_nil ()⟩⟩

theorem okT_two (d₁ d₂ : RDT) (m₁ : (roundT (Run.ckP .two) d₁).up.Msg)
    (c₁ : (roundT (Run.ckP .two) d₁).up.Chal) (m₂ : (roundT (Run.ckP .two) d₂).up.Msg)
    (c₂ : (roundT (Run.ckP .two) d₂).up.Chal) :
    okT [d₁, d₂] ((m₁, c₁, m₂, c₂, ()) : Tr (uLT (Run.ckP .two) [d₁, d₂])) ↔
      GChal.pass (b := d₁.entry.work) c₁ = true ∧ GChal.pass (b := d₂.entry.work) c₂ = true :=
  (okT_cons d₁ [d₂] m₁ c₁ (m₂, c₂, ())).trans (and_congr_right fun _ => okT_one d₂ m₂ c₂)

theorem vT_length : ∀ (ds : List RDT) (τ : Tr (uLT (Run.ckP .two) ds)), (vT ds τ).length = ds.length
  | [], _ => rfl
  | _ :: ds, (_, _, τ) => congrArg (· + 1) (vT_length ds τ)

end OnBytes.Tie.Pv.Row

#print axioms OnBytes.Tie.Pv.Row.vT_cons
#print axioms OnBytes.Tie.Pv.Row.okT_cons
#print axioms OnBytes.Tie.Pv.Row.okT_two
#print axioms OnBytes.Tie.Pv.Row.vT_length
