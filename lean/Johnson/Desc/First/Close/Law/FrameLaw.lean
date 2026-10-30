-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/FrameLaw.lean: THE LAW OF K10 OVER ITS WRITTEN ROUNDS, AT THE FRAME's
CLOSING. Definitions, a statement and its proof.

`k10_leads` and `k10_front` (Leads.lean, Front.lean, beside this file) speak of the function
`closing` at a plan, a group's number and a mask's number that stand in front of all statements. The
kind's block decides by `closeFrame` (Johnson/Desc/First/Close/Closing.lean), which takes these
three off the frame in the record.
  `frameRed ρ es rec`: `closeFrame` as a reduction over the same k + 2 written rounds: at a
    statement a it reads what is owed, the frame and the statement off a by `rec`; it puts out a,
    the frame behind and the statement behind.
  `AtPlace P g mask es x`: the record stands at the place for which the typed data are made: the
    frame's group is g, its mask is mask, and the plan that `closeFrame` makes of the frame's shape
    and of the link's numbers is P.
  `frame_leads`: any law of `closeRed` with an end Q gives the law of `frameRed`, on the statements
    that also stand at the place, at the same errors, with the end: a rides along; THE FRAME BEHIND
    IS THE FRAME IN FRONT WITH THE CLAIM LAID INTO `rows`, no mask, the next link, "first"; and Q of
    that claim and of the statement behind.
Limits. `AtPlace` is a premise on the record: who shows it of the record at K10's place owes it (a
test on the plan's walk). Not yet the block under `Block.step`, nor a lift to the chain's record.
Those of Leads.lean. Nothing on an honest prover or on hiding.

-/
import Johnson.Desc.First.Close.Law.Front
import Johnson.Desc.First.Close.Law.Lays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold Iop IOR KObj OnBytes.Flat
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H

/-- The frame's closing as a reduction over its written rounds. -/
noncomputable def frameRed {c : BatFoldCaller GE} {rB rE rR : Round} (ρ : Rd c rB rE rR)
    (es : List Fmt.Entry) {A : Type} (rec : A → Option Nat × ReqFrame × Statement) :
    Reduction A (A × ReqFrame × Statement) where
  shape := rB :: rE :: List.replicate (Yc c).k rR
  out a τ := match closeFrame (rec a).1 (rec a).2.1 (rec a).2.2 es (ρ.V τ) with
    | .ok x => some (a, x.1, x.2)
    | .error _ => none

/-- The record stands at the place for which the typed data are made. -/
def AtPlace (P : Plan) (g : Nat) (mask : Option Nat) (es : List Fmt.Entry)
    (x : Option Nat × ReqFrame × Statement) : Prop :=
  x.2.1.group = g ∧ x.2.1.mask = mask ∧
    ∀ G, x.2.1.groups[x.2.1.link]? = some G →
      (⟨x.2.1.shape.code, x.2.1.shape.maskCode, G.k, G.h, es⟩ : Plan) = P

/-- **From `closing` to the frame's closing.** -/
theorem frame_leads {c : BatFoldCaller GE} {rB rE rR : Round} (ρ : Rd c rB rE rR) (P : Plan)
    (g : Nat) (mask : Option Nat) (es : List Fmt.Entry) {A : Type}
    (rec : A → Option Nat × ReqFrame × Statement) (on : A → Prop)
    (Q : A → A × SingleRows × Statement → Prop)
    (ε' : Err (rB :: rE :: List.replicate (Yc c).k rR))
    (h : (closeRed ρ P g mask fun a => (rec a).2.2).Leads on Q ε') :
    (frameRed ρ es rec).Leads (fun a => on a ∧ AtPlace P g mask es (rec a))
      (fun a b => b.1 = a ∧
        b.2.1 = { (rec a).2.1 with
          rows := b.2.1.rows, mask := none, link := (rec a).2.1.link + 1, next := .first } ∧
        Q a (a, b.2.1.rows, b.2.2)) ε' := fun a ha =>
  Doomed.mono _ _ (fun τ hτ b hb => by
    have hb' : (match closeFrame (rec a).1 (rec a).2.1 (rec a).2.2 es (ρ.V τ) with
      | .ok x => some (a, x.1, x.2)
      | .error _ => none) = some b := hb
    split at hb'
    · next x hx =>
      obtain rfl := Option.some.inj hb'
      obtain ⟨G, rows, hG, hc, hf⟩ := closeFrame_lays (f' := x.1) (S' := x.2) hx
      obtain ⟨h1, h2, h3⟩ := ha.2
      rw [h3 G hG, h1, h2] at hc
      have hr : x.1.rows = rows := by rw [hf]
      refine ⟨rfl, closeFrame_rows (f' := x.1) (S' := x.2) hx, ?_⟩
      refine hτ (a, x.1.rows, x.2) ?_
      show (match closing P (rec a).2.2 g mask (ρ.V τ) with
        | .ok y => some (a, y.1, y.2)
        | .error _ => none) = _
      rw [hc, hr]
    · cases hb') (h a ha.1)

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.frame_leads
