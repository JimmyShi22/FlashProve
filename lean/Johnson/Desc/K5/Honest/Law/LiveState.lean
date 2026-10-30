-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/LiveState.lean: CONDITIONAL: an attention segment's own rounds: the
statements on the slots that the runs "first" and "second" name with a coefficient that does not
read 0 (Johnson/Desc/K5/Honest/Law/LiveClaims.lean), said AT A STATE of the first chain, of the
kind's three named runs as runs of claims (runFirst, runKeys, runSecond,
Johnson/Desc/First/Att/Claims/K5Still.lean). Definitions of propositions, and statements with their
proofs ON THE VERIFIER'S OWN DATA: no prover is in this file.

What for. The test with code "the claims are good on the slots" of a whole segment's list of claims
(slotsLive, Johnson/Desc/K9/Honest/SlotsLive.lean) is meant to be put together run by run, under one
proposition on states that every run hands on. Here stand this kind's proposition and this kind's
three runs' shares.

Main names:
  HeldLive x k u  **the proposition on a state**: what the state holds of the segment's own rounds
                  was returned by the hearing at the plan x, from a ledger whose arrays have their
                  length and whose next slot was k; and the test on the drawn elements says yes
  heldLive_congr  it reads of a state what the state holds of these rounds, and nothing else
  inAt_spec       what the structure that the runs read is made of
  first_at, second_at   the two statements at the forms that the state's ledger and what was heard
                  yield
  runs_unturned   each of the three runs returns the state unturned: it hands on every proposition
                  on states
  first_state, keys_state, second_state   **wherever the run returns at a state with HeldLive: the
                  slots of its share are live in its list, every slot is plain in its list, and the
                  state behind has HeldLive**; the list of "keys" is empty

The three are CONDITIONAL on: HeldLive at the state in front: whoever follows the state from the
hearing to the runs shows it; LiveFits and the plan's number of calls: public.
Limits. The share is the slots from k up to k5End x k, those that the kind's hearing takes: the
slots in front and behind are other kinds'. That a reached state has HeldLive is not shown. That the
runs of OTHER kinds in the segment's order hand HeldLive on is not shown (by heldLive_congr it is
enough that they leave what the state holds of these rounds). The runs here are the kind's own at
its seat on the first chain's state; the road from them to the runs in a description's list is not
walked here. Nothing on the merge's slot: the kind's lists are not shown to leave any slot unnamed.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.LiveClaims
import Johnson.Desc.First.Att.Claims.K5Still

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes (E)
open OnBytes.Model (Reading Aff Fork)
open VerifiableInference.Desc (Claim First.S named)
open VerifiableInference.Desc.K9H (liveAt plainAt)
open VerifiableInference.Desc.First.Att.P (ParC parCOf geoOf Heard hear leftP leftP_spec pointsOf
  ptsFrom kB kV)
open K5Law (inAt firstAt secondAt firstK_isAt secondK_isAt runFirst runKeys runSecond rFirst rKeys
  rSecond rFirst_mem rKeys_mem rSecond_mem runOfForms_hands att_of_inOf)

/-- **What a state holds of the segment's own rounds**: it was returned by the hearing at the plan
x, from a ledger whose arrays have their length and whose next slot was k; and the test on the drawn
elements says yes. -/
def HeldLive (x : OnBytes.Params.AttentionRounds) (k : ℕ) (u : First.S) : Prop :=
  ∃ (h : Heard) (F G : Fork) (rs rest : List Fmt.RoundView) (lead : ℕ), u.heard5? = some h ∧
    hear x (F, rs, 0) = some (h, G, rest, lead) ∧ OnBytes.Model.Road.Sized F ∧ F.next = k ∧
    heardLive h = true

/-- The proposition reads of a state what it holds of the segment's own rounds, and nothing else: so
whatever leaves that leaves the proposition. -/
theorem heldLive_congr {x : OnBytes.Params.AttentionRounds} {k : ℕ} {u u' : First.S}
    (e : u'.heard5? = u.heard5?) (h : HeldLive x k u) : HeldLive x k u' := by
  obtain ⟨h5, F, G, rs, rest, lead, a, b⟩ := h
  exact ⟨h5, F, G, rs, rest, lead, e.trans a, b⟩

/-- What the structure that the runs read is made of. -/
theorem inAt_spec {c : ParC} {g : OnBytes.Model.Forest.Heard} {h : Heard} {U : Fork}
    {y : VerifiableInference.Desc.First.Att.P.Runs.In × ℕ} (e : inAt c g h U = some y) :
    y.1.g = c.geo ∧ y.1.zk = g.zk ∧ ∃ L, leftP c.geo g.zk h U = some L ∧
      pointsOf c.geo g.zk h L = some y.1.p := by
  unfold inAt at e
  obtain ⟨p, hp, e⟩ := Option.bind_eq_some_iff.1 e
  obtain ⟨t, _, e⟩ := Option.bind_eq_some_iff.1 e
  obtain ⟨K, _, e⟩ := Option.bind_eq_some_iff.1 e
  obtain rfl := Option.some.inj e
  unfold ptsFrom at hp
  obtain ⟨L, hL, hp⟩ := Option.bind_eq_some_iff.1 hp
  exact ⟨rfl, rfl, L, hL, hp⟩

section At
variable {A : OnBytes.Attention.Plan} {x : OnBytes.Params.AttentionRounds} {F G U : Fork}
  {rs rest : List Fmt.RoundView} {lead : ℕ} {h : Heard} {g : OnBytes.Model.Forest.Heard} {l : List Aff}

/-- The run "first", at the forms that a ledger and what was heard yield. -/
theorem first_at (hh : hear x (F, rs, 0) = some (h, G, rest, lead))
    (hz : OnBytes.Model.Road.Sized F) (gf : LiveFits (geoOf A.S) x) (hN : A.NC = A.S.calls.size)
    (hL : heardLive h = true) (e : firstAt (parCOf A) g h U = some l) :
    ∀ j, F.next ≤ j → j < kV x F.next → j ≠ kB x F.next →
      liveAt (l.map fun f => ({ form := f } : Claim)) j = true := by
  unfold firstAt at e
  obtain ⟨y, hy, e⟩ := Option.bind_eq_some_iff.1 e
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 e
  obtain ⟨e1, e2, L, hl, hp⟩ := inAt_spec hy
  have e1' : y.1.g = geoOf A.S := e1
  exact k5_first_liveAt A A.S g hh hz (by rw [e1']; exact leftP_spec hl) (by rw [e1']; exact hp)
    (by rw [e1']; exact gf) e1' e2 hN (show _ = some (w.1, w.2) from hw) hL

/-- The run "second", likewise. -/
theorem second_at (hh : hear x (F, rs, 0) = some (h, G, rest, lead))
    (hz : OnBytes.Model.Road.Sized F) (gf : LiveFits (geoOf A.S) x) (hL : heardLive h = true)
    (e : secondAt (parCOf A) g h U = some l) :
    ∀ j, j = kB x F.next ∨ (kV x F.next ≤ j ∧ j < k5End x F.next) →
      liveAt (l.map fun f => ({ form := f } : Claim)) j = true := by
  unfold secondAt at e
  obtain ⟨y, hy, e⟩ := Option.bind_eq_some_iff.1 e
  obtain ⟨e1, e2, L, hl, hp⟩ := inAt_spec hy
  have e1' : y.1.g = geoOf A.S := e1
  exact k5_second_liveAt A.S g hh hz (by rw [e1']; exact leftP_spec hl) (by rw [e1']; exact hp)
    (by rw [e1']; exact gf) e1' e2 e hL

end At

private theorem named_ok {α : Type} {n : String} {o : Option α} {v : α} (h : named n o = .ok v) :
    o = some v := by
  cases o with
  | none => exact nomatch h
  | some a => exact congrArg some (Except.ok.inj h)

section State
variable (A : OnBytes.Attention.Plan) {x : OnBytes.Params.AttentionRounds} {k : ℕ}

/-- **Each of the kind's three runs returns the state unturned**: so it hands on every proposition
on states whatsoever. -/
theorem runs_unturned (m : ℕ) (u : First.S) (z : List Claim × First.S)
    (hr : runFirst (parCOf A) m u = .ok z ∨ runKeys (parCOf A) m u = .ok z ∨
      runSecond (parCOf A) m u = .ok z) : z.2 = u := by
  rcases hr with hr | hr | hr
  · exact (runOfForms_hands _ (parCOf A) _ (rFirst_mem (parCOf A)) m u z.1 z.2 hr).1
  · exact (runOfForms_hands _ (parCOf A) _ (rKeys_mem (parCOf A)) m u z.1 z.2 hr).1
  · exact (runOfForms_hands _ (parCOf A) _ (rSecond_mem (parCOf A)) m u z.1 z.2 hr).1

/-- **The run "first" at a state.** -/
theorem first_state (gf : LiveFits (geoOf A.S) x) (hN : A.NC = A.S.calls.size) (m : ℕ)
    (u : First.S) (z : List Claim × First.S) (hI : HeldLive x k u)
    (hr : runFirst (parCOf A) m u = .ok z) :
    (∀ j, k ≤ j → j < kV x k → j ≠ kB x k → liveAt z.1 j = true) ∧
      (∀ j, plainAt z.1 j = true) ∧ HeldLive x k z.2 := by
  obtain ⟨h, F, G, rs, rest, lead, h5, hh, hz, rfl, hL⟩ := hI
  obtain ⟨e1, l, hl, e2⟩ := runOfForms_hands _ (parCOf A) _ (rFirst_mem (parCOf A)) m u z.1 z.2 hr
  have hk := named_ok (show named "K5.first" _ = .ok (l, u) from hl)
  rw [e1, e2]
  refine ⟨?_, plainAt_forms l, h, F, G, rs, rest, lead, h5, hh, hz, rfl, hL⟩
  cases he : u.here with
  | att a =>
    rw [firstK_isAt he] at hk
    have h5' : a.heard5 = some h := by
      unfold First.S.heard5? at h5
      rw [he] at h5
      exact h5
    obtain ⟨l', hl', e3⟩ := Option.map_eq_some_iff.1 hk
    obtain rfl : l' = l := (Prod.mk.inj e3).1
    obtain ⟨g, _, hl'⟩ := Option.bind_eq_some_iff.1 hl'
    rw [h5'] at hl'
    exact first_at hh hz gf hN hL hl'
  | _ =>
    unfold First.S.heard5? at h5
    rw [he] at h5
    exact nomatch h5

/-- **The run "second" at a state.** -/
theorem second_state (gf : LiveFits (geoOf A.S) x) (m : ℕ) (u : First.S)
    (z : List Claim × First.S) (hI : HeldLive x k u) (hr : runSecond (parCOf A) m u = .ok z) :
    (∀ j, j = kB x k ∨ (kV x k ≤ j ∧ j < k5End x k) → liveAt z.1 j = true) ∧
      (∀ j, plainAt z.1 j = true) ∧ HeldLive x k z.2 := by
  obtain ⟨h, F, G, rs, rest, lead, h5, hh, hz, rfl, hL⟩ := hI
  obtain ⟨e1, l, hl, e2⟩ := runOfForms_hands _ (parCOf A) _ (rSecond_mem (parCOf A)) m u z.1 z.2 hr
  have hk := named_ok (show named "K5.second" _ = .ok (l, u) from hl)
  rw [e1, e2]
  refine ⟨?_, plainAt_forms l, h, F, G, rs, rest, lead, h5, hh, hz, rfl, hL⟩
  cases he : u.here with
  | att a =>
    rw [secondK_isAt he] at hk
    have h5' : a.heard5 = some h := by
      unfold First.S.heard5? at h5
      rw [he] at h5
      exact h5
    obtain ⟨l', hl', e3⟩ := Option.map_eq_some_iff.1 hk
    obtain rfl : l' = l := (Prod.mk.inj e3).1
    obtain ⟨g, _, hl'⟩ := Option.bind_eq_some_iff.1 hl'
    rw [h5'] at hl'
    exact second_at hh hz gf hL hl'
  | _ =>
    unfold First.S.heard5? at h5
    rw [he] at h5
    exact nomatch h5

/-- **The run "keys" at a state**: its list is empty, so every slot is plain in it; and it hands the
proposition on. -/
theorem keys_state (m : ℕ) (u : First.S) (z : List Claim × First.S) (hI : HeldLive x k u)
    (hr : runKeys (parCOf A) m u = .ok z) :
    z.1 = [] ∧ (∀ j, plainAt z.1 j = true) ∧ HeldLive x k z.2 := by
  obtain ⟨e1, l, hl, e2⟩ := runOfForms_hands _ (parCOf A) _ (rKeys_mem (parCOf A)) m u z.1 z.2 hr
  have hk := named_ok (show named "K5.keys" _ = .ok (l, u) from hl)
  unfold VerifiableInference.Desc.First.Att.P.keysK at hk
  obtain ⟨_, _, e3⟩ := Option.map_eq_some_iff.1 hk
  obtain rfl : [] = l := (Prod.mk.inj e3).1
  rw [e1, e2]
  exact ⟨rfl, plainAt_forms [], hI⟩

end State

end H2K5.Honest

#print axioms H2K5.Honest.heldLive_congr
#print axioms H2K5.Honest.inAt_spec
#print axioms H2K5.Honest.first_at
#print axioms H2K5.Honest.second_at
#print axioms H2K5.Honest.runs_unturned
#print axioms H2K5.Honest.first_state
#print axioms H2K5.Honest.second_state
#print axioms H2K5.Honest.keys_state
