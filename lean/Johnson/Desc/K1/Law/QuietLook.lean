-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- A copy of a working file of this project that is not in this repository: as copied, it parted
-- from it in its import lines alone.
/-
Johnson/Desc/K1/Law/QuietLook.lean: the three quiet steps that stand behind a sending of the reads
(Johnson/Desc/K8/ReadsQuiet.lean: `layers`, `head`; Johnson/Desc/First/Att/ReadsO.lean:
`readsAtSO`): what each leaves (`LookSame`, Johnson/Desc/K1/Law/LookSame.lean), and WHAT EACH LAYS
AT THE DIGITS' SEAT, the field `heard` of the state's part `tl`.

  `lookSame_layers`, `lookSame_head`, `lookSame_att`: each leaves the four readers.
  `tlHeard_att`: at an attention segment the field is the state's own, as it was.
  `tlHeard_layers`, `tlHeard_head`: AT A LAYERS' SEGMENT AND AT THE HEAD's THE STEP LAYS THE PLAN's
    `tl` WITH ITS LIST OF TABLES CLOSED, NOT THE STATE's: behind the step the field is THE PLAN's
    (`P.tl.heard`, `P.hp.tl.heard`), whatever it was in front.

What is not claimed. That the plan's field is empty: no test of these blocks asks it (`planned` asks
two other things). Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.LookSame
import Johnson.Desc.K8.ReadsQuietLaws
import Johnson.Goal.Meaning.RecReadsAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K8.ReadsQuiet (PG PH layers head closed layers_ok head_ok)
open VerifiableInference.Desc.First.Att (readsAtSO readsStepO)
open Meaning.K2 (bindE)

/-- Closing the list of tables leaves the field. -/
theorem close_heard {tl tl' : HTailF2} {funs : Array HFun}
    (h : First.K8.Order.close tl funs = .ok tl') : tl'.heard = tl.heard := by
  unfold First.K8.Order.close at h
  split at h
  · cases h
  · cases h
    rfl

theorem closed_heard {tl tl' : HTailF2} {funs : Array HFun} {L : LinkCtx} {st : Statement}
    (h : closed tl funs L st = .ok tl') : tl'.heard = tl.heard := by
  unfold closed at h
  obtain ⟨t, h1, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  cases h
  exact close_heard h1

theorem lookSame_layers {P : PG} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (layers P).decide s rs gs = .ok s') :
    LookSame s s' := by
  obtain ⟨a, own, tl', ha, _, _, rfl⟩ := layers_ok h
  refine ⟨?_, ?_, rfl, ?_⟩ <;> simp [S.fork?, S.link?, S.lookHeard?, ha]

/-- **Behind the step at a layers' segment the field is the plan's.** -/
theorem tlHeard_layers {P : PG} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (layers P).decide s rs gs = .ok s') :
    s'.tl?.bind (·.heard) = P.tl.heard := by
  obtain ⟨a, own, tl', ha, _, hc, rfl⟩ := layers_ok h
  simp [S.tl?, closed_heard hc]

theorem lookSame_head {P : PH} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (head P).decide s rs gs = .ok s') :
    LookSame s s' := by
  obtain ⟨a, cov, x, t, tl', ha, ho, _, _, _, _, rfl⟩ := head_ok h
  refine ⟨?_, ?_, rfl, ?_⟩ <;> simp [S.fork?, S.link?, S.lookHeard?, ha, ho]

/-- **Behind the step at the head's segment the field is the plan's.** -/
theorem tlHeard_head {P : PH} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (head P).decide s rs gs = .ok s') :
    s'.tl?.bind (·.heard) = P.hp.tl.heard := by
  obtain ⟨a, cov, x, t, tl', ha, ho, _, _, _, hc, rfl⟩ := head_ok h
  simp [S.tl?, ho, closed_heard hc]

/-- The step at an attention segment, with what it lays at `tl`. -/
theorem readsAtSO_tl {A : Attention.Plan} {s s' : S} (h : readsAtSO A s = .ok s') :
    ∃ a t tl, s.here = .att a ∧ tl.heard = a.tl.heard ∧
      s' = { s with here := .att { a with t := some t, tl := tl } } := by
  unfold readsAtSO at h
  dsimp only at h
  split at h
  · rename_i a ha
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨r, hr, h⟩ := bindE h
    cases h
    refine ⟨a, r.1, r.2.1, ha, ?_, rfl⟩
    unfold readsStepO at hr
    obtain ⟨_, _, hr⟩ := bindE hr
    obtain ⟨_, _, hr⟩ := bindE hr
    obtain ⟨_, _, hr⟩ := bindE hr
    obtain ⟨tl', hc, hr⟩ := bindE hr
    obtain ⟨_, _, hr⟩ := bindE hr
    cases hr
    exact close_heard hc
  · cases h

theorem lookSame_att {A : Attention.Plan} {s s' : S} (h : readsAtSO A s = .ok s') :
    LookSame s s' := by
  obtain ⟨a, t, tl, ha, _, rfl⟩ := readsAtSO_tl h
  refine ⟨?_, ?_, rfl, ?_⟩ <;> simp [S.fork?, S.link?, S.lookHeard?, ha]

/-- At an attention segment the field is as it was. -/
theorem tlHeard_att {A : Attention.Plan} {s s' : S} (h : readsAtSO A s = .ok s') :
    s'.tl?.bind (·.heard) = s.tl?.bind (·.heard) := by
  obtain ⟨a, t, tl, ha, e, rfl⟩ := readsAtSO_tl h
  simp [S.tl?, ha, e]

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.lookSame_layers
#print axioms VerifiableInference.Desc.K1.tlHeard_layers
#print axioms VerifiableInference.Desc.K1.lookSame_head
#print axioms VerifiableInference.Desc.K1.tlHeard_head
#print axioms VerifiableInference.Desc.K1.lookSame_att
#print axioms VerifiableInference.Desc.K1.tlHeard_att
