-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/RunPays.lean: THE LAYERS' OWN ROUNDS (K4): WHO PAYS THE PREMISE OF ITS
TWO RUNS OF CLAIMS ON SHAPES (PlanEnv, Johnson/Desc/First/K4/Returns/RunShape.lean): K4's own
accepting decision. General laws: nothing is evaluated.

  heardAt_env     what the hearing returns at a state has the plan's layout and table of scales in
                  its environment: over the library's hear_public
                  (OnBytes/Desc/First/K4/HearPublic.lean).
  decide_lays     a yes of the block at the state: what it lays, as a state: the ledger and what was
                  heard, as heardAt names them; no count of rows owed.
  **k4_planEnv**  behind a yes of the block at the state PlanEnv holds. No premise.

Limits. At the state right behind K4's decision alone: that the members between it and the batching
keep what was heard is not said here. At a state in which nothing was heard (s.own? = none) PlanEnv
P s holds and says nothing. k4_planEnv does say something: by decide_lays the state behind the yes
has what was heard laid. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.K4.Returns.RunShape
import OnBytes.Desc.First.K4.HearPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc D6.Ret
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer (Pub HPlan2 Own)
open VerifiableInference.Desc.First (S LayOwn)

/-- What the hearing returns has the plan's layout and table of scales in its environment. -/
theorem heardAt_env {p : Par} {s : S} {rs : List Fmt.RoundView} {o : Own} {G : Fork}
    (h : heardAt p s rs = some (o, G)) : o.v.y = p.P.y ∧ o.v.sc = p.P.sc := by
  unfold heardAt at h
  cases hh : s.here with
  | lay a =>
    rw [hh] at h
    obtain ⟨fo, -, h⟩ := Option.bind_eq_some_iff.1 h
    cases e : hearFl { p.P with tokv := s.tokv } p.hp p.g fo a.F
        (paired rs (entries p.P p.hp p.g)) with
    | none =>
      rw [e] at h
      cases h
    | some x =>
      obtain ⟨o', G', u⟩ := x
      rw [e] at h
      cases u with
      | cons _ _ => cases h
      | nil =>
        obtain ⟨rfl, rfl⟩ : o' = o ∧ G' = G := by
          have k : (o', G') = (o, G) := Option.some.inj h
          exact ⟨congrArg (·.1) k, congrArg (·.2) k⟩
        obtain ⟨-, -, iU3, tab, laid, nU3, TS, claimsP, pts, hd2, -, -, -, -, ev, -⟩ :=
          hear_public e
        rw [ev]
        exact ⟨rfl, rfl⟩
  | _ =>
    rw [hh] at h
    cases h

/-- **A yes of the block at the state: what it lays.** -/
theorem decide_lays {p : Par} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (blockAtC p).decide s rs gs = .ok s') :
    ∃ a o G, s.here = .lay a ∧ heardAt p s rs = some (o, G) ∧
      s' = { s with here := .lay { a with F := G, own := some o }, rowsOwed := none } := by
  cases hh : s.here with
  | lay a =>
    have hd : (blockAtC p).decide s rs gs =
        (hearAt seatOwn p (a, (if s.noneWaits = true then none else s.rowsOwed), s.tokv) rs).map
          (setPart s) := by
      show ((VerifiableInference.Desc.named "the part is not there" (part? s)).bind fun x =>
        (hearAt seatOwn p x rs).map (setPart s)) = _
      unfold part?
      rw [hh]
      rfl
    have k := hearAt_part p a (if s.noneWaits = true then none else s.rowsOwed) s.tokv rs
      (setPart s)
    rw [← hd, h] at k
    have hv : heardAt p s rs = a.fo.bind fun fo =>
        match hearFl { p.P with tokv := s.tokv } p.hp p.g fo a.F
            (paired rs (entries p.P p.hp p.g)) with
        | some (o, G, []) => some (o, G)
        | _ => none := by
      unfold heardAt
      rw [hh]
      rfl
    have k' : some s' = _ := k
    by_cases hc : ((if s.noneWaits = true then none else s.rowsOwed : Option Nat).isNone &&
        fitsAll (rounds p.P p.hp p.g) (entries p.P p.hp p.g) rs &&
        Kit.plainStretchWith rowsTabled (entries p.P p.hp p.g) rs) = true
    case neg =>
      rw [if_neg hc] at k'
      cases k'
    case pos =>
      rw [if_pos hc] at k'
      obtain ⟨fo, hfo, k⟩ := Option.bind_eq_some_iff.1 k'.symm
      cases e : hearFl { p.P with tokv := s.tokv } p.hp p.g fo a.F
          (paired rs (entries p.P p.hp p.g)) with
      | none =>
        rw [e] at k
        cases k
      | some x =>
        obtain ⟨o, G, u⟩ := x
        rw [e] at k
        cases u with
        | cons _ _ => cases k
        | nil =>
          refine ⟨a, o, G, rfl, ?_, (Option.some.inj k).symm⟩
          rw [hv, hfo]
          show (match hearFl { p.P with tokv := s.tokv } p.hp p.g fo a.F
              (paired rs (entries p.P p.hp p.g)) with
            | some (o, G, []) => some (o, G)
            | _ => none) = _
          rw [e]
  | _ =>
    exfalso
    have hd : ((blockAtC p).decide s rs gs).toOption = none := by
      show ((VerifiableInference.Desc.named "the part is not there" (part? s)).bind fun x =>
        (hearAt seatOwn p x rs).map (setPart s)).toOption = none
      unfold part?
      rw [hh]
      rfl
    rw [h] at hd
    cases hd

/-- **Behind a yes of the block at the state, what was heard has the plan's layout and table of
scales.** -/
theorem k4_planEnv {p : Par} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (blockAtC p).decide s rs gs = .ok s') :
    PlanEnv p.P s' := by
  obtain ⟨a, o, G, -, hv, rfl⟩ := decide_lays h
  intro o' ho'
  obtain rfl : o = o' := Option.some.inj ho'
  exact heardAt_env hv

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.heardAt_env
#print axioms OnBytes.Desc.First.K4.Rt.decide_lays
#print axioms OnBytes.Desc.First.K4.Rt.k4_planEnv
