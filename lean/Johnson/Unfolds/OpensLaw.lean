-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/OpensLaw.lean: where as many rounds draw positions as there are lists, what the
declared rounds `fillL es plan` (Johnson/Unfolds/FillLaw.lean) open, all together, is the plan's
lists in order; so `Johnson.G.OfPlan.toldIn` at three such lists of rounds walks no round.

Why. `fileOf` asks of each tree that a chain sends whether some round of the file opens it: `toldIn`
gathers what ALL the rounds open: at the proof file's first chain a walk over 48,293 rounds
(`dryProofFull_length`, Johnson/G/DryProofLit.lean), of which only those that draw positions can
open anything.

Definition.
  `toldW o0 o1 o2`: `toldIn`'s text over three lists of opened trees.
Statements. General.
  **`fillL_opens`**: where as many rounds draw positions as there are lists:
    `(fillL es plan).flatMap (·.opens) = plan.flatMap (·.1)`.
  **`toldIn_fill`**: where in each of the three as many rounds draw positions as there are lists:
    `toldIn` at three lists `fillL es plan` is `toldW` over the plans' lists alone.
Whose text. `toldW` follows `toldIn` (Johnson/G/RoundsOfPlan.lean): this tree's own file.

Limits. The equations of numbers are premises. No closed fact. Nothing on soundness.

-/
import Johnson.Unfolds.FillLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds
open Johnson.G Johnson.G.OfPlan

/-- **Where as many rounds draw positions as there are lists, what the rounds of `fillL es plan`
open is the plan's lists, in order.** -/
theorem fillL_opens : ∀ (es : List Fmt.Entry) (plan : List (List Told × List Fmt.Stored)),
    (es.filter fun e => Fmt.kindOf e.name == some .positions).length = plan.length →
      (fillL es plan).flatMap (·.opens) = plan.flatMap (·.1)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | e :: es, plan, h => by
    cases hb : (Fmt.kindOf e.name == some .positions) with
    | false =>
      have h' : (es.filter fun e => Fmt.kindOf e.name == some .positions).length = plan.length := by
        simpa [List.filter_cons, hb] using h
      simp only [fillL, hb]
      rw [List.flatMap_cons, fillL_opens es plan h']
      rfl
    | true =>
      cases plan with
      | nil => simp [hb] at h
      | cons x rest =>
        have h' : (es.filter fun e => Fmt.kindOf e.name == some .positions).length =
            rest.length := by
          simpa [List.filter_cons, hb] using h
        simp only [fillL, hb]
        rw [List.flatMap_cons, List.flatMap_cons, fillL_opens es rest h']

/-- `toldIn`'s text over three lists of opened trees. -/
def toldW (o0 o1 o2 : List Told) : List (Nat × Nat) :=
  [o0, o1, o2].zipIdx.flatMap fun c => c.1.map fun o =>
    match o.2 with
    | .own n => (c.2, n)
    | .taken k p => (k, p)

/-- **`toldIn` at three lists `fillL es plan`: over the plans' lists alone**, where in each of the
three as many rounds draw positions as there are lists. -/
theorem toldIn_fill {e0 e1 e2 : List Fmt.Entry} {p0 p1 p2 : List (List Told × List Fmt.Stored)}
    (h0 : (e0.filter fun e => Fmt.kindOf e.name == some .positions).length = p0.length)
    (h1 : (e1.filter fun e => Fmt.kindOf e.name == some .positions).length = p1.length)
    (h2 : (e2.filter fun e => Fmt.kindOf e.name == some .positions).length = p2.length) :
    toldIn (fillL e0 p0, fillL e1 p1, fillL e2 p2) =
      toldW (p0.flatMap (·.1)) (p1.flatMap (·.1)) (p2.flatMap (·.1)) := by
  rw [← fillL_opens e0 p0 h0, ← fillL_opens e1 p1 h1, ← fillL_opens e2 p2 h2]
  rfl

end Johnson.Unfolds

#print axioms Johnson.Unfolds.fillL_opens
#print axioms Johnson.Unfolds.toldIn_fill
