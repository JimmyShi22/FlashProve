-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/HeadSlots.lean: the order of the slots that the routine hear returns behind those of
the lookup.

The check of the output head's sub-proof receives the prover's messages in one routine (hear in
OnBytes/Model/HeadHeard.lean). Each hidden scalar gets a slot. The state of the sub-proof holds the
number of the next free slot (Fork.next). Among the routines that hear calls, one alone moves it
(SubM.takeSlots). This file follows that number through the routines that hear calls after the
lookup's, and concludes in which order the slots lie that these return.

Main theorems: ok_stLift, ok_changeBy, ok_ask (when a routine that is made in one of three ways
succeeds); foldlM_stay; hideRun_next; takeSlots_ok, claimsIn_ok, pscBeginAt_ok, pscBegin_ok,
pscRound_ok, roundIn_ok, pscEnds_ok, pscRow_ok, levelIn_ok, tscRounds_ok, tscIn_ok, shownRun_ok
(what each routine does to the number of the next free slot, and where the slots lie that it
returns); hearSquares_ok, hearProducts_ok, hearStream_ok, hearLogits_ok; hear_slots,
hear_slots_five, hear_apart. The last three rest on hear_steps (Johnson/Road/HeadPoint.lean), which
takes the routine hear apart into its steps.

What is not claimed. Every theorem begins "if the routine succeeds": none says that it does. The
lookup's routine runs before the routines that are followed here and takes slots of its own, which
hear returns too: nothing is said of them here. Nor is it said that a slot is below the number of
slots that was set up, where the first slot of a sumcheck's hiding polynomial lies, or that these
coefficients fill the slots up to the end values. Nothing is said about what a slot holds, or about
what a verifier's acceptance shows. The program does not import this file.
-/
import Johnson.Road.HeadKit
import Johnson.Road.HeadPoint

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open OnBytes.Model (Fork SubM Aff)

/-! ## Routines made from a block, from a step on the state, from a reading of the state -/

/-- A block that is run inside a routine does not see the state. -/
theorem ok_stLift {α : Type} (x : Blk α) (F G : Fork) (C D : Ctx) (a : α) :
    Ok (StateT.lift x : SubM α) F C a G D ↔ x C = .ok (a, D) ∧ G = F :=
  ok_lift x F G C D a

/-- Such a routine leaves the state. -/
theorem lift_stay {α : Type} {x : Blk α} {F G : Fork} {C D : Ctx} {a : α}
    (h : Ok (StateT.lift x : SubM α) F C a G D) : G = F :=
  ((ok_stLift x F G C D a).mp h).2

/-- A step on the state that may refuse. -/
theorem ok_changeBy (f : Fork → Option Fork) (F G : Fork) (C D : Ctx) (u : Unit) :
    Ok (SubM.change f) F C u G D ↔ f F = some G ∧ D = C := by
  unfold Ok
  simp only [SubM.change]
  cases f F with
  | none => simp [liftOption_none]
  | some H => simp [liftOption_some, eq_comm]

/-- A value that is read off the state by a function that may refuse. -/
theorem ok_ask {α : Type} (f : Fork → Option α) (F G : Fork) (C D : Ctx) (a : α) :
    Ok (SubM.ask f) F C a G D ↔ f F = some a ∧ G = F ∧ D = C := by
  unfold Ok
  simp only [SubM.ask]
  cases f F with
  | none => simp [liftOption_none]
  | some y => simp [liftOption_some, eq_comm, and_assoc]

/-- Such a routine leaves the state. -/
theorem ask_stay {α : Type} {f : Fork → Option α} {F G : Fork} {C D : Ctx} {a : α}
    (h : Ok (SubM.ask f) F C a G D) : G = F :=
  ((ok_ask f F G C D a).mp h).2.1

/-! ## Putting values under slots does not move the number of the next free slot -/

/-- One value under one slot. -/
theorem hide_next {F G : Fork} {j : ℕ} {y k : E} (h : F.hide j y k = some G) :
    G.next = F.next := by
  unfold Fork.hide at h
  split at h
  · cases h
    rfl
  · cases h

/-- A list of values under a run of slots. -/
theorem hideSteps_next (k : E) : ∀ (l : List E) (j : ℕ) (F : Fork) (x : ℕ × Fork),
    l.foldlM (Fork.hideStep k) (j, F) = some x → x.2.next = F.next
  | [], j, F, x, h => by
    have e : (j, F) = x := by simpa using h
    rw [← e]
  | y :: l, j, F, x, h => by
    rw [List.foldlM_cons] at h
    cases hq : F.hide j y k with
    | none => simp [Fork.hideStep, hq] at h
    | some H =>
      have h2 : l.foldlM (Fork.hideStep k) (j + 1, H) = some x := by
        simpa [Fork.hideStep, hq] using h
      rw [hideSteps_next k l (j + 1) H x h2, hide_next hq]

/-- An array of values under a run of slots. -/
theorem hideRun_next {F G : Fork} {first : ℕ} {v : Array E} {k : E}
    (h : F.hideRun first v k = some G) : G.next = F.next := by
  cases hq : v.foldlM (Fork.hideStep k) (first, F) with
  | none => simp [Fork.hideRun, hq] at h
  | some x =>
    have e : x.2 = G := by simpa [Fork.hideRun, hq] using h
    rw [← Array.foldlM_toList] at hq
    rw [← e]
    exact hideSteps_next k _ _ _ _ hq

/-! ## Taking slots -/

/-- The routine that takes n slots returns the number of the next free slot and adds n to it. -/
theorem takeSlots_ok {n j : ℕ} {F G : Fork} {C D : Ctx} (h : Ok (SubM.takeSlots n) F C j G D) :
    j = F.next ∧ G.next = F.next + n := by
  have e : SubM.takeSlots n F C = .ok ((F.next, { F with next := F.next + n }), C) := rfl
  unfold Ok at h
  rw [e] at h
  cases h
  exact ⟨rfl, rfl⟩

/-- Hidden values that are sent outside a sumcheck: the first one's slot is the next free slot, and
n slots are taken. -/
theorem claimsIn_ok {n j : ℕ} {F G : Fork} {C D : Ctx} (h : Ok (SubM.claimsIn n) F C j G D) :
    j = F.next ∧ G.next = F.next + n := by
  unfold SubM.claimsIn at h
  rw [ok_bind] at h
  obtain ⟨v, F1, C1, h1, h⟩ := h
  have e1 := lift_stay h1
  rw [ok_bind] at h
  obtain ⟨_, F2, C2, h2, h⟩ := h
  have e2 := lift_stay h2
  rw [ok_bind] at h
  obtain ⟨j', F3, C3, h3, h⟩ := h
  obtain ⟨e3, e4⟩ := takeSlots_ok h3
  rw [ok_bind] at h
  obtain ⟨_, F4, C4, h4, h⟩ := h
  rw [ok_changeBy] at h4
  have e5 := hideRun_next h4.1
  rw [ok_pure] at h
  obtain ⟨e6, e7, _⟩ := h
  refine ⟨?_, ?_⟩
  · rw [e6, e3, e2, e1]
  · rw [e7, e5, e4, e2, e1]

/-! ## A sumcheck -/

/-- The beginning of a sumcheck takes one slot, its first. -/
theorem pscBeginAt_ok {t : E} {p : Model.Psc} {F G : Fork} {C D : Ctx}
    (h : Ok (Model.pscBeginAt t) F C p G D) : p.first = F.next ∧ G.next = F.next + 1 := by
  unfold Model.pscBeginAt at h
  rw [ok_bind] at h
  obtain ⟨first, F1, C1, h1, h⟩ := h
  obtain ⟨e1, e2⟩ := takeSlots_ok h1
  rw [ok_bind] at h
  obtain ⟨mu, F2, C2, h2, h⟩ := h
  have e3 := congrArg Fork.next (lift_stay h2)
  rw [ok_bind] at h
  obtain ⟨eps, F3, C3, h3, h⟩ := h
  have e4 := congrArg Fork.next (lift_stay h3)
  rw [ok_pure] at h
  obtain ⟨e5, e6, _⟩ := h
  have e7 := congrArg Fork.next e6
  subst e5
  exact ⟨e1, by omega⟩

/-- The same for the beginning of a sumcheck whose sum must equal a form. -/
theorem pscBegin_ok {c : Aff} {p : Model.Psc} {F G : Fork} {C D : Ctx}
    (h : Ok (Model.pscBegin c) F C p G D) : p.first = F.next ∧ G.next = F.next + 1 := by
  unfold Model.pscBegin at h
  rw [ok_bind] at h
  obtain ⟨t, F1, C1, h1, h⟩ := h
  have e1 := congrArg Fork.next (ask_stay h1)
  rw [ok_bind] at h
  obtain ⟨p0, F2, C2, h2, h⟩ := h
  obtain ⟨e2, e3⟩ := pscBeginAt_ok h2
  rw [ok_pure] at h
  obtain ⟨e4, e5, _⟩ := h
  have e6 := congrArg Fork.next e5
  subst e4
  exact ⟨e2.trans e1, by omega⟩

/-- A round takes as many slots as scalars are sent in it. The slots are those of the hiding
polynomial's coefficients in the round's variable. Nothing is put under them here. -/
theorem pscRound_ok {p : Model.Psc} {w : OnBytes.Psc.Weight} {draw : Blk E} {x : E × Model.Psc}
    {F G : Fork} {C D : Ctx} (h : Ok (Model.pscRound p w draw) F C x G D) :
    G.next = F.next + (w.d - 1) := by
  unfold Model.pscRound at h
  rw [ok_bind] at h
  obtain ⟨_, F1, C1, h1, h⟩ := h
  have e1 := congrArg Fork.next (lift_stay h1)
  rw [ok_bind] at h
  obtain ⟨sent, F2, C2, h2, h⟩ := h
  have e2 := congrArg Fork.next (lift_stay h2)
  rw [ok_bind] at h
  obtain ⟨_, F3, C3, h3, h⟩ := h
  have e3 := congrArg Fork.next (lift_stay h3)
  try dsimp only at h
  rw [ok_bind] at h
  obtain ⟨r, F4, C4, h4, h⟩ := h
  have e4 := congrArg Fork.next (lift_stay h4)
  rw [ok_bind] at h
  obtain ⟨j, F5, C5, h5, h⟩ := h
  obtain ⟨_, e5⟩ := takeSlots_ok h5
  try dsimp only at h
  rw [ok_pure] at h
  obtain ⟨_, e6, _⟩ := h
  have e7 := congrArg Fork.next e6
  omega

/-- A round of a given form does not lower the number of the next free slot. -/
theorem roundIn_ok {form : Model.RoundForm} {p : Model.Psc} {z : E} {degree : ℕ}
    {x : E × Model.Psc} {F G : Fork} {C D : Ctx}
    (h : Ok (Model.roundIn form p z degree) F C x G D) : F.next ≤ G.next := by
  unfold Model.roundIn at h
  rw [ok_bind] at h
  obtain ⟨_, F1, C1, h1, h⟩ := h
  have e1 := congrArg Fork.next (lift_stay h1)
  rw [ok_bind] at h
  obtain ⟨w, F2, C2, h2, h⟩ := h
  have e2 := congrArg Fork.next (lift_stay h2)
  have e3 := pscRound_ok h
  omega

/-- The end of a sumcheck: the n end values get the last n slots that are taken. -/
theorem pscEnds_ok {p : Model.Psc} {dY n : ℕ} {x : ℕ × Model.Psc} {F G : Fork} {C D : Ctx}
    (h : Ok (Model.pscEnds p dY n) F C x G D) : F.next ≤ x.1 ∧ G.next = x.1 + n := by
  unfold Model.pscEnds at h
  rw [ok_bind] at h
  obtain ⟨_, F1, C1, h1, h⟩ := h
  have e1 := congrArg Fork.next (lift_stay h1)
  rw [ok_bind] at h
  obtain ⟨⟨beta, p'⟩, F2, C2, h2, h⟩ := h
  have e2 := pscRound_ok h2
  try dsimp only at h
  rw [ok_bind] at h
  obtain ⟨v, F3, C3, h3, h⟩ := h
  have e3 := congrArg Fork.next (lift_stay h3)
  rw [ok_bind] at h
  obtain ⟨_, F4, C4, h4, h⟩ := h
  have e4 := congrArg Fork.next (lift_stay h4)
  rw [ok_bind] at h
  obtain ⟨_, F5, C5, h5, h⟩ := h
  have e5 := congrArg Fork.next (lift_stay h5)
  rw [ok_bind] at h
  obtain ⟨e, F6, C6, h6, h⟩ := h
  obtain ⟨e6, e7⟩ := takeSlots_ok h6
  rw [ok_bind] at h
  obtain ⟨_, F7, C7, h7, h⟩ := h
  rw [ok_changeBy] at h7
  have e8 := hideRun_next h7.1
  rw [ok_pure] at h
  obtain ⟨e9, e10, _⟩ := h
  have e11 := congrArg Fork.next e10
  subst e9
  refine ⟨?_, ?_⟩
  · show F.next ≤ e
    omega
  · show G.next = e + n
    omega

/-- Making the claim that a sumcheck leaves takes no slot. -/
theorem pscRow_ok {p : Model.Psc} {S0 : E} {kept : Aff} {x : Aff × Model.Psc} {F G : Fork}
    {C D : Ctx} (h : Ok (Model.pscRow p S0 kept) F C x G D) : G.next = F.next := by
  unfold Model.pscRow at h
  rw [ok_bind] at h
  obtain ⟨_, F1, C1, h1, h⟩ := h
  have e1 := congrArg Fork.next (lift_stay h1)
  rw [ok_bind] at h
  obtain ⟨_, F2, C2, h2, h⟩ := h
  rw [ok_changeBy] at h2
  have e2 := hideRun_next h2.1
  rw [ok_pure] at h
  obtain ⟨_, e3, _⟩ := h
  have e4 := congrArg Fork.next e3
  omega

/-! ## A layer of a product tree -/

/-- The rounds of a layer do not lower the number of the next free slot. -/
theorem levelRounds_ok (mu : ℕ) (rho : Array E) : ∀ (order : List ℕ) (r : Array E) (p : Model.Psc)
    (F : Fork) (C : Ctx) (x : Array E × Model.Psc) (G : Fork) (D : Ctx),
    Ok (Model.levelRounds mu rho order r p) F C x G D → F.next ≤ G.next
  | [], r, p, F, C, x, G, D, h => by
    unfold Model.levelRounds at h
    rw [ok_pure] at h
    exact Nat.le_of_eq (congrArg Fork.next h.2.1).symm
  | v :: order, r, p, F, C, x, G, D, h => by
    unfold Model.levelRounds at h
    rw [ok_bind] at h
    obtain ⟨_, F1, C1, h1, h⟩ := h
    have e1 := congrArg Fork.next (lift_stay h1)
    rw [ok_bind] at h
    obtain ⟨⟨y, p'⟩, F2, C2, h2, h⟩ := h
    have e2 := roundIn_ok h2
    try dsimp only at h
    have e3 := levelRounds_ok mu rho order _ _ _ _ _ _ _ h
    omega

/-- A layer: its two end values get the last two slots that it takes, after at least one other. -/
theorem levelIn_ok {mu : ℕ} {rho : Array E} {c : Aff} {order : List ℕ} {o : Model.Level}
    {F G : Fork} {C D : Ctx} (h : Ok (Model.levelIn mu rho c order) F C o G D) :
    F.next < o.sL ∧ o.sR = o.sL + 1 ∧ G.next = o.sL + 2 := by
  unfold Model.levelIn at h
  rw [ok_bind] at h
  obtain ⟨_, F1, C1, h1, h⟩ := h
  have e1 := congrArg Fork.next (lift_stay h1)
  rw [ok_bind] at h
  obtain ⟨p, F2, C2, h2, h⟩ := h
  obtain ⟨_, e2⟩ := pscBegin_ok h2
  rw [ok_bind] at h
  obtain ⟨⟨r, p1⟩, F3, C3, h3, h⟩ := h
  have e3 := levelRounds_ok _ _ _ _ _ _ _ _ _ _ h3
  try dsimp only at h
  rw [ok_bind] at h
  obtain ⟨⟨sL, p2⟩, F4, C4, h4, h⟩ := h
  obtain ⟨e4, e5⟩ : F3.next ≤ sL ∧ F4.next = sL + 2 := pscEnds_ok h4
  try dsimp only at h
  rw [ok_bind] at h
  obtain ⟨tau, F5, C5, h5, h⟩ := h
  have e6 := congrArg Fork.next (lift_stay h5)
  rw [ok_bind] at h
  obtain ⟨a, F6, C6, h6, h⟩ := h
  have e7 := congrArg Fork.next (ask_stay h6)
  rw [ok_bind] at h
  obtain ⟨b, F7, C7, h7, h⟩ := h
  have e8 := congrArg Fork.next (ask_stay h7)
  rw [ok_bind] at h
  obtain ⟨⟨row, p3⟩, F8, C8, h8, h⟩ := h
  have e9 := pscRow_ok h8
  try dsimp only at h
  rw [ok_pure] at h
  obtain ⟨e10, e11, _⟩ := h
  have e12 := congrArg Fork.next e11
  subst e10
  refine ⟨?_, rfl, ?_⟩
  · show F.next < sL
    omega
  · show G.next = sL + 2
    omega

/-! ## A token sumcheck -/

/-- The rounds of a token sumcheck do not lower the number of the next free slot. -/
theorem tscLoop_ok : ∀ (zs : List E) (r : Array E) (p : Model.Psc) (F : Fork) (C : Ctx)
    (x : Array E × Model.Psc) (G : Fork) (D : Ctx),
    Ok (Model.tscLoop zs r p) F C x G D → F.next ≤ G.next
  | [], r, p, F, C, x, G, D, h => by
    unfold Model.tscLoop at h
    rw [ok_pure] at h
    exact Nat.le_of_eq (congrArg Fork.next h.2.1).symm
  | z :: zs, r, p, F, C, x, G, D, h => by
    unfold Model.tscLoop at h
    rw [ok_bind] at h
    obtain ⟨⟨y, p'⟩, F1, C1, h1, h⟩ := h
    have e1 := roundIn_ok h1
    try dsimp only at h
    have e2 := tscLoop_ok zs _ _ _ _ _ _ _ h
    omega

/-- The rounds of a token sumcheck: its claimed sum gets the next free slot, and at least one more
slot is taken. -/
theorem tscRounds_ok {P : Array E} {lt : ℕ} {o : Model.Tsc} {F G : Fork} {C D : Ctx}
    (h : Ok (Model.tscRounds P lt) F C o G D) : o.sCl = F.next ∧ o.sCl + 2 ≤ G.next := by
  unfold Model.tscRounds at h
  rw [ok_bind] at h
  obtain ⟨_, F1, C1, h1, h⟩ := h
  have e1 := congrArg Fork.next (lift_stay h1)
  rw [ok_bind] at h
  obtain ⟨sCl, F2, C2, h2, h⟩ := h
  obtain ⟨e2, e3⟩ := claimsIn_ok h2
  rw [ok_bind] at h
  obtain ⟨p, F3, C3, h3, h⟩ := h
  obtain ⟨_, e4⟩ := pscBegin_ok h3
  rw [ok_bind] at h
  obtain ⟨⟨r, p1⟩, F4, C4, h4, h⟩ := h
  have e5 := tscLoop_ok _ _ _ _ _ _ _ _ h4
  try dsimp only at h
  rw [ok_pure] at h
  obtain ⟨e6, e7, _⟩ := h
  have e8 := congrArg Fork.next e7
  subst e6
  refine ⟨?_, ?_⟩
  · show sCl = F.next
    omega
  · show sCl + 2 ≤ G.next
    omega

/-- A whole token sumcheck: its claimed sum gets the next free slot, and its end values the last
slots that it takes. -/
theorem tscIn_ok {P : Array E} {lt n dY : ℕ} {o : Model.Tsc} {F G : Fork} {C D : Ctx}
    (h : Ok (Model.tscIn P lt n dY) F C o G D) :
    o.sCl = F.next ∧ o.sCl + 2 ≤ o.sEnd ∧ G.next = o.sEnd + n := by
  unfold Model.tscIn at h
  rw [ok_bind] at h
  obtain ⟨o1, F1, C1, h1, h⟩ := h
  obtain ⟨e1, e2⟩ := tscRounds_ok h1
  rw [ok_bind] at h
  obtain ⟨⟨sEnd, p⟩, F2, C2, h2, h⟩ := h
  obtain ⟨e3, e4⟩ : F1.next ≤ sEnd ∧ F2.next = sEnd + n := pscEnds_ok h2
  try dsimp only at h
  rw [ok_pure] at h
  obtain ⟨e5, e6, _⟩ := h
  have e7 := congrArg Fork.next e6
  subst e5
  refine ⟨e1, ?_, ?_⟩
  · show o1.sCl + 2 ≤ sEnd
    omega
  · show G.next = sEnd + n
    omega

/-! ## The routines of the output head -/

/-- A fold whose steps leave the state leaves the state. -/
theorem foldlM_stay {β γ : Type} (f : β → γ → SubM β)
    (hf : ∀ b x F C b' G D, Ok (f b x) F C b' G D → G = F) :
    ∀ (l : List γ) (b : β) (F : Fork) (C : Ctx) (b' : β) (G : Fork) (D : Ctx),
      Ok (l.foldlM f b) F C b' G D → G = F
  | [], b, F, C, b', G, D, h => by
    rw [List.foldlM_nil, ok_pure] at h
    exact h.2.1
  | x :: l, b, F, C, b', G, D, h => by
    rw [List.foldlM_cons, ok_bind] at h
    obtain ⟨b1, F1, C1, h1, h2⟩ := h
    rw [foldlM_stay f hf l b1 F1 C1 b' G D h2, hf b x F C b1 F1 C1 h1]

/-- Reading what was shown in a run of slots leaves the state. -/
theorem shownRun_ok {first n : ℕ} {a : Array E} {F G : Fork} {C D : Ctx}
    (h : Ok (Model.Head.shownRun first n) F C a G D) : G = F := by
  unfold Model.Head.shownRun at h
  refine foldlM_stay _ (fun b x F1 C1 b' G1 D1 h1 => ?_) _ _ _ _ _ _ _ h
  try dsimp only at h1
  rw [ok_bind] at h1
  obtain ⟨y, F2, C2, h2, h3⟩ := h1
  rw [ok_pure] at h3
  exact h3.2.1.trans (ask_stay h2)

/-- The sums of limb products and their layer: the sums get the next free slots, the layer's two end
values the last two slots that are taken. -/
theorem hearSquares_ok {h : Model.Head.Shape} {PV gp : Array E} {sW : ℕ} {wpl : Model.Level}
    {F G : Fork} {C D : Ctx} (H : Ok (Model.Head.hearSquares h PV) F C (sW, gp, wpl) G D) :
    sW = F.next ∧ sW + Model.ledNS h.XL < wpl.sL ∧ wpl.sR = wpl.sL + 1 ∧
      G.next = wpl.sL + 2 := by
  unfold Model.Head.hearSquares at H
  try dsimp only at H
  rw [ok_bind] at H
  obtain ⟨s, F1, C1, h1, H⟩ := H
  obtain ⟨e1, e2⟩ := claimsIn_ok h1
  rw [ok_bind] at H
  obtain ⟨g, F2, C2, h2, H⟩ := H
  have e3 := congrArg Fork.next (lift_stay h2)
  try dsimp only at H
  rw [ok_bind] at H
  obtain ⟨o, F3, C3, h3, H⟩ := H
  obtain ⟨e4, e5, e6⟩ := levelIn_ok h3
  rw [ok_pure] at H
  obtain ⟨e7, e8, _⟩ := H
  have e9 := congrArg Fork.next e8
  cases e7
  exact ⟨e1, by omega, e5, by omega⟩

/-- The row products and their token sumcheck. -/
theorem hearProducts_ok {h : Model.Head.Shape} {PV omV : Array E} {sPv : ℕ} {tV : Model.Tsc}
    {F G : Fork} {C D : Ctx} (H : Ok (Model.Head.hearProducts h PV) F C (sPv, omV, tV) G D) :
    sPv = F.next ∧ tV.sCl = sPv + Model.ledNP h.XL ∧ tV.sCl + 2 ≤ tV.sEnd ∧
      G.next = tV.sEnd + Model.ledNO h.XL := by
  unfold Model.Head.hearProducts at H
  rw [ok_bind] at H
  obtain ⟨s, F1, C1, h1, H⟩ := H
  obtain ⟨e1, e2⟩ := claimsIn_ok h1
  rw [ok_bind] at H
  obtain ⟨g, F2, C2, h2, H⟩ := H
  have e3 := congrArg Fork.next (lift_stay h2)
  rw [ok_bind] at H
  obtain ⟨o, F3, C3, h3, H⟩ := H
  obtain ⟨e4, e5, e6⟩ := tscIn_ok h3
  rw [ok_bind] at H
  obtain ⟨sh, F4, C4, h4, H⟩ := H
  have e7 := congrArg Fork.next (shownRun_ok h4)
  rw [ok_bind] at H
  obtain ⟨⟨row, p⟩, F5, C5, h5, H⟩ := H
  have e8 := pscRow_ok h5
  try dsimp only at H
  rw [ok_pure] at H
  obtain ⟨e9, e10, _⟩ := H
  have e11 := congrArg Fork.next e10
  cases e9
  refine ⟨e1, ?_, e5, ?_⟩
  · show o.sCl = _
    omega
  · show G.next = o.sEnd + _
    omega

/-- The token sumcheck of the stream times the reciprocal. -/
theorem hearStream_ok {h : Model.Head.Shape} {zt : Array E} {tN : Model.Tsc} {F G : Fork}
    {C D : Ctx} (H : Ok (Model.Head.hearStream h zt) F C tN G D) :
    tN.sCl = F.next ∧ tN.sCl + 2 ≤ tN.sEnd ∧ G.next = tN.sEnd + 2 := by
  unfold Model.Head.hearStream at H
  rw [ok_bind] at H
  obtain ⟨o, F1, C1, h1, H⟩ := H
  obtain ⟨e1, e2, e3⟩ := tscIn_ok h1
  rw [ok_bind] at H
  obtain ⟨a, F2, C2, h2, H⟩ := H
  have e4 := congrArg Fork.next (ask_stay h2)
  rw [ok_bind] at H
  obtain ⟨b, F3, C3, h3, H⟩ := H
  have e5 := congrArg Fork.next (ask_stay h3)
  rw [ok_bind] at H
  obtain ⟨⟨row, p⟩, F4, C4, h4, H⟩ := H
  have e6 := pscRow_ok h4
  try dsimp only at H
  rw [ok_pure] at H
  obtain ⟨e7, e8, _⟩ := H
  have e9 := congrArg Fork.next e8
  subst e7
  refine ⟨e1, e2, ?_⟩
  show G.next = o.sEnd + 2
  omega

/-- The rounds over the channels do not lower the number of the next free slot. -/
theorem channelRounds_ok : ∀ (n : ℕ) (r : Array E) (p : Model.Psc) (F : Fork) (C : Ctx)
    (x : Array E × Model.Psc) (G : Fork) (D : Ctx),
    Ok (Model.Head.channelRounds n r p) F C x G D → F.next ≤ G.next
  | 0, r, p, F, C, x, G, D, h => by
    unfold Model.Head.channelRounds at h
    rw [ok_pure] at h
    exact Nat.le_of_eq (congrArg Fork.next h.2.1).symm
  | n + 1, r, p, F, C, x, G, D, h => by
    unfold Model.Head.channelRounds at h
    rw [ok_bind] at h
    obtain ⟨⟨y, p'⟩, F1, C1, h1, h⟩ := h
    have e1 := roundIn_ok h1
    try dsimp only at h
    have e2 := channelRounds_ok n _ _ _ _ _ _ _ h
    omega

/-- The token sumcheck of the activations times the head's weights. -/
theorem hearLogits_ok {h : Model.Head.Shape} {lam : ℕ} {zt rs : Array E} {tH : Model.Tsc}
    {F G : Fork} {C D : Ctx} (H : Ok (Model.Head.hearLogits h lam zt) F C (tH, rs) G D) :
    tH.sCl = F.next ∧ tH.sCl + 2 ≤ tH.sEnd ∧ G.next = tH.sEnd + 2 := by
  unfold Model.Head.hearLogits at H
  rw [ok_bind] at H
  obtain ⟨o, F1, C1, h1, H⟩ := H
  obtain ⟨e1, e2⟩ := tscRounds_ok h1
  rw [ok_bind] at H
  obtain ⟨⟨r, p⟩, F2, C2, h2, H⟩ := H
  have e3 := channelRounds_ok _ _ _ _ _ _ _ _ h2
  try dsimp only at H
  rw [ok_bind] at H
  obtain ⟨⟨sEnd, p1⟩, F3, C3, h3, H⟩ := H
  obtain ⟨e4, e5⟩ : F2.next ≤ sEnd ∧ F3.next = sEnd + 2 := pscEnds_ok h3
  try dsimp only at H
  rw [ok_bind] at H
  obtain ⟨a, F4, C4, h4, H⟩ := H
  have e6 := congrArg Fork.next (ask_stay h4)
  rw [ok_bind] at H
  obtain ⟨b, F5, C5, h5, H⟩ := H
  have e7 := congrArg Fork.next (ask_stay h5)
  rw [ok_bind] at H
  obtain ⟨⟨row, p2⟩, F6, C6, h6, H⟩ := H
  have e8 := pscRow_ok h6
  try dsimp only at H
  rw [ok_pure] at H
  obtain ⟨e9, e10, _⟩ := H
  have e11 := congrArg Fork.next e10
  cases e9
  refine ⟨e1, ?_, ?_⟩
  · show o.sCl + 2 ≤ sEnd
    omega
  · show G.next = sEnd + 2
    omega

/-! ## The whole routine -/

/-- **The slots that hear returns behind those of the lookup, in their order.** First the sums of
limb products; after further slots the two end values of their layer; at once the row products; at
once the claimed sum of their token sumcheck; after further slots its end values; at once the
claimed sum of the second token sumcheck, and so on. The last two slots that are taken are the end
values of the third token sumcheck. Of the slots that the lookup's routine has taken before, nothing
is said. -/
theorem hear_slots {h : Model.Head.Shape} {L : Model.Head.HL} {hp : Model.Head.HPlanH2}
    {cov : Model.Head.Covered} {plain : Array E} {x : Model.Head.Heard} {F G : Fork} {C D : Ctx}
    (hx : Ok (Model.Head.hear h L hp cov plain) F C x G D) :
    x.sW + Model.ledNS h.XL < x.wpl.sL ∧ x.wpl.sR = x.wpl.sL + 1 ∧ x.sPv = x.wpl.sL + 2 ∧
      x.tV.sCl = x.sPv + Model.ledNP h.XL ∧ x.tV.sCl + 2 ≤ x.tV.sEnd ∧
      x.tN.sCl = x.tV.sEnd + Model.ledNO h.XL ∧ x.tN.sCl + 2 ≤ x.tN.sEnd ∧
      x.tH.sCl = x.tN.sEnd + 2 ∧ x.tH.sCl + 2 ≤ x.tH.sEnd ∧ G.next = x.tH.sEnd + 2 := by
  obtain ⟨yTok, F1, C1, F2, C2, g1, F3, C3, Zl, F4, C4, PV, F5, C5, sW, gp, wpl, F6, C6, sPv, omV,
    tV, F7, C7, qN, qH, tN, F8, C8, tH, rs, F9, C9, _, _, _, _, _, k6, k7, _, _, k8, k9, eG, ex⟩ :=
    hear_steps hx
  obtain ⟨_, a2, a3, a4⟩ := hearSquares_ok k6
  obtain ⟨b1, b2, b3, b4⟩ := hearProducts_ok k7
  obtain ⟨c1, c2, c3⟩ := hearStream_ok k8
  obtain ⟨d1, d2, d3⟩ := hearLogits_ok k9
  have eG' := congrArg Fork.next eG
  have s1 : sPv = wpl.sL + 2 := by omega
  have s2 : tN.sCl = tV.sEnd + Model.ledNO h.XL := by omega
  have s3 : tH.sCl = tN.sEnd + 2 := by omega
  have s4 : G.next = tH.sEnd + 2 := by omega
  subst ex
  exact ⟨a2, a3, s1, b2, b3, s2, c2, s3, d2, s4⟩

/-- With five limbs. The nine slots of the sums end before the slot sL of the left end value of
their layer. The seven slots of the products begin at sL + 2. The claimed sum of the products'
sumcheck follows them at once. Its four end values begin at least two slots later, and the claimed
sum of the second token sumcheck follows them at once. -/
theorem hear_slots_five {h : Model.Head.Shape} {L : Model.Head.HL} {hp : Model.Head.HPlanH2}
    {cov : Model.Head.Covered} {plain : Array E} {x : Model.Head.Heard} {F G : Fork} {C D : Ctx}
    (hXL : h.XL = 5) (hx : Ok (Model.Head.hear h L hp cov plain) F C x G D) :
    x.sW + 9 < x.wpl.sL ∧ x.sPv = x.wpl.sL + 2 ∧ x.tV.sCl = x.sPv + 7 ∧
      x.tV.sCl + 2 ≤ x.tV.sEnd ∧ x.tN.sCl = x.tV.sEnd + 4 := by
  obtain ⟨a1, _, a3, a4, a5, a6, _⟩ := hear_slots hx
  rw [hXL] at a1 a4 a6
  exact ⟨a1, a3, a4, a5, a6⟩

/-- With five limbs the nine slots of the sums end before the seven slots of the products begin. -/
theorem hear_apart {h : Model.Head.Shape} {L : Model.Head.HL} {hp : Model.Head.HPlanH2}
    {cov : Model.Head.Covered} {plain : Array E} {x : Model.Head.Heard} {F G : Fork} {C D : Ctx}
    (hXL : h.XL = 5) (hx : Ok (Model.Head.hear h L hp cov plain) F C x G D) :
    x.sW + 9 ≤ x.sPv := by
  obtain ⟨a1, a2, _⟩ := hear_slots_five hXL hx
  omega

#print axioms hear_slots
#print axioms hear_slots_five
#print axioms hear_apart
#print axioms claimsIn_ok
#print axioms levelIn_ok
#print axioms tscIn_ok
#print axioms hearSquares_ok
#print axioms hearProducts_ok
#print axioms hearStream_ok
#print axioms hearLogits_ok

end OnBytes.Road.Hd
