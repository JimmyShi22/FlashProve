-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoStaysTop.lean.
The whole routines of the three kinds of sub-proof stay on the view.

`DryL` (OnBytes/Tie/Pv/Lookup/Ends/FoChanUp.lean) of a link's routine: from every state, a run on a
view that returns is still on the view.

 * `stays_head`: a step of the tactic `stays` that is read off the routine's head.
 * `stays_coefficientsF`, `stays_coefficients`, `staysL_selfTests`, `stays_hearH`: four routines
   that the files OnBytes/Tie/Pv/Lookup/Ends/FoStays*.lean leave out.
 * `staysL_runA`, `staysL_runG`, `staysL_runH`: attention (`OnBytes.Attention.run`), a group of
   layers (`Layer.runForkHidG2`), the output head (`Head.runForkHidH2`), from the first line to the
   link's closing.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoSiteFirst
import OnBytes.Tie.Pv.Lookup.Ends.FoStaysLayer
import OnBytes.Tie.Pv.Lookup.Ends.FoStaysAttention
import OnBytes.Tie.Pv.Lookup.Ends.FoStaysHead
import OnBytes.Tie.Pv.Lookup.Ends.FoStaysPlace

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

open Lean Meta Elab Tactic in
/-- One step that is read off the routine's head as it is written: bind, pure, a sub-proof's
routine used inside a link, or a named routine that has its statement. It spares the long routines
the search through all rules. -/
elab "stays_head" : tactic => do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  unless t.isApp do throwError "no routine"
  let some w := t.getAppFn.constName? | throwError "no word"
  let some n := t.appArg!.getAppFn.constName? | throwError "no constant at the head"
  if n == ``Bind.bind then
    if w == ``Fo.DryL then evalTactic (← `(tactic| with_reducible apply DryL.bind))
    else if w == ``Fo.DryS then evalTactic (← `(tactic| with_reducible apply DryS.bind))
    else if w == ``Fo.Dry then evalTactic (← `(tactic| with_reducible apply Dry.bind))
    else throwError "no rule"
  else if n == ``Pure.pure then
    if w == ``Fo.DryL then evalTactic (← `(tactic| with_reducible exact DryL.pure _))
    else if w == ``Fo.DryS then evalTactic (← `(tactic| with_reducible exact DryS.pure _))
    else if w == ``Fo.Dry then evalTactic (← `(tactic| with_reducible exact Dry.pure _))
    else throwError "no rule"
  else if n == ``LinkM.sub && w == ``Fo.DryL then
    evalTactic (← `(tactic| with_reducible apply DryL.sub))
  else
    -- the statement on a named routine, by its name: OnBytes.A.b has Fo.stays_A_b
    let s := n.toString
    unless s.startsWith "OnBytes." do throwError "no rule"
    let lem := `Fo ++ Name.mkSimple ("stays_" ++ (s.drop 8).replace "." "_")
    unless (← getEnv).contains lem do throwError "no rule"
    evalTactic (← `(tactic| with_reducible apply $(mkIdent lem)))

macro_rules | `(tactic| stays_rule) => `(tactic| stays_head)

theorem stays_coefficientsF (tl : HTailF2) : DryS tl.coefficientsF := by
  unfold HTailF2.coefficientsF
  exact DryS.bind (DryS.getO _) fun _ => DryS.modify _
theorem stays_coefficients (tl : HTailF2) : DryS tl.coefficients := stays_coefficientsF tl
macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible exact stays_coefficients _)

theorem staysL_selfTests (R : Head.Run) (tl : HTailF2) (wo : WsForkOut) :
    DryL (Head.selfTests R tl wo) := by stays
macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible exact staysL_selfTests _ _ _)

theorem stays_hearH (s : Head.Shape) (Y : Head.HL) (hp : Head.HPlanH2) (cov : Head.Covered)
    (plain : Array E) : DryS (Head.hear s Y hp cov plain) := by stays
macro_rules | `(tactic| stays_rule) => `(tactic| with_reducible exact stays_hearH _ _ _ _ _)

theorem staysL_runA (P : Attention.Plan) : DryL (Attention.run P) := by stays
theorem staysL_runG (P : Layer.Pub) (hp : Layer.HPlan2) (g : Nat) :
    DryL (Layer.runForkHidG2 P hp g) := by stays
theorem staysL_runH (s : Head.Shape) (Y : Head.HL) (b : Head.Border) (hp : Head.HPlanH2)
    (O : Head.Owner) (cov : Head.Covered) (wsLay : WsLay) :
    DryL (Head.runForkHidH2 s Y b hp O cov wsLay) := by stays

end Fo
