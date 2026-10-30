-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/RespectsAttQ.lean: MEMBERS OF Q.Respects (Johnson/Desc/K1/Law/RestQDef.lean: a
run of claims reads nothing of what a later commitment of kind K1 or the reads' quiet step writes):
ALL SEVEN RUNS OF AN ATTENTION SEGMENT, at the kinds' own texts: the lookup's "objects", "guests",
"planes"; K5's "first", "keys", "second" and the lookup's "join" with K5's keys. Statements with
their proofs: Johnson/Desc/K1/Law/RespectsAtt.lean's, lemma for lemma, at the wider cut; its calculus
on ledgers (Markless) is called, not typed again.
Main names (namespace VerifiableInference.Desc.K1.Q): respects_flRun · respects_joinCalls ·
respects_planesCalls · SeatRest · seatCO_rest · respects_firstAt | _keysAt | _secondAt ·
block_respects · runsO_respects · withCaller_respects.
SO: none of the seven reads the approximate range proof's part or the reads' tables.
What is not claimed. That a real chain's link states these runs. Nothing on soundness, on an honest
prover or on hiding.

-/
import Johnson.Desc.K1.Law.ReadersStayQ
import Johnson.Desc.K1.Law.RespectsAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1.Q
open OnBytes OnBytes.Params OnBytes.Model OnBytes.K.Kc Desc.Plain
open VerifiableInference.Desc.First (S Here)
open VerifiableInference.Desc.First.Att.P (seatCO parCOf ParC)
open VerifiableInference.Desc.K9 (Fn RunOf readRun objectsBy guestsNone flRun joinCalls planesCalls
  planesProg firstAt keysAt secondAt asClaimsOf runOfForms ofForm)

/-! ## A run made of such a program -/

theorem respects_flRun {β γ δ : Type} (e0 : String) (pre1 : S → Except String β) (e1 : String)
    (test : β → Fork → Bool) (pre2 : S → Except String γ) (e2 : String) (m : β → γ → Fl δ)
    (out : δ → List Claim) (h1 : ReadsRest pre1) (h2 : ReadsRest pre2)
    (ht : ∀ b F F', forkRest F = forkRest F' → test b F' = test b F)
    (hm : ∀ b c, Markless (m b c)) : Respects (flRun e0 pre1 e1 test pre2 e2 m out) := by
  intro s s' hA cl t e
  unfold flRun at e ⊢
  obtain ⟨F, hF, e⟩ := (bind_ok _ _ _).1 e
  obtain ⟨b, hb, e⟩ := (bind_ok _ _ _).1 e
  obtain ⟨_, hn, e⟩ := (bind_ok _ _ _).1 e
  obtain ⟨c, hc, e⟩ := (bind_ok _ _ _).1 e
  obtain ⟨x, hx, e⟩ := (bind_ok _ _ _).1 e
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj e)
  cases hF0 : s.fork? with
  | none => rw [hF0] at hF; cases hF
  | some F₀ =>
    rw [hF0] at hF
    obtain rfl : F₀ = F := Except.ok.inj hF
    obtain ⟨F', g1, g2⟩ := hA.fork hF0
    cases hm0 : m b c F₀ [] with
    | none => rw [hm0] at hx; cases hx
    | some x₀ =>
      rw [hm0] at hx
      obtain rfl : x₀ = x := Except.ok.inj hx
      have k := hm b c F₀ F' [] g2.symm
      rw [hm0] at k
      obtain ⟨G', k1, k2⟩ := k
      refine ⟨s'.putFork G', ?_, hA.putFork k2⟩
      rw [g1, h1.alike hA, h2.alike hA]
      show (Except.ok F' : Except String Fork).bind _ = _
      simp only [Except.bind]
      rw [hb]
      simp only [bind, Except.bind]
      rw [ht b F₀ F' g2.symm, hn, hc]
      simp only [k1]
      rfl

theorem readsRest_named {α : Type} (e : String) (f : S → Option α) (h : ReadsRest f) :
    ReadsRest fun s => named e (f s) := fun s => by
  show named e (f (restOf s)) = named e (f s)
  rw [h s]

/-- **K3's "join" at the calls**: where the caller's keys read the rest alone. -/
theorem respects_joinCalls (keys : S → Option (Array Aff)) (hk : ReadsRest keys) :
    Respects (joinCalls keys) :=
  respects_flRun _ _ _ _ _ _ _ _ (readsRest_named _ _ readsRest_lookHeard)
    (readsRest_named _ _ hk) (fun g F F' h => unpaid_rest g.owedJoin F F' h)
    fun g KF => joinF_markless g KF

/-- **K3's "planes" at the calls**: where the caller's readers read the rest alone. -/
theorem respects_planesCalls (lm : Nat) (readers : K3.Readers S) (hr : ReadsRest readers) :
    Respects (planesCalls lm readers) :=
  respects_flRun _ _ _ _ _ _ _ _ (readsRest_named _ _ readsRest_lookHeard)
    (readsRest_named _ _ hr) (fun g F F' h => unpaid_rest g.owedPlanes F F' h)
    fun g r => planesProg_markless lm g r

/-! ## K5's claims' seat -/

/-- A seat of K5's claims whose five readers read the rest alone. -/
structure SeatRest (seat : First.Att.P.SeatC S) : Prop where
  pts : ReadsRest seat.pts
  cols : ReadsRest seat.cols
  look : ReadsRest seat.look
  pad : ReadsRest seat.pad
  zk : ReadsRest seat.zk

theorem inOf_rest (seat : First.Att.P.SeatC S) (h : SeatRest seat) (c : ParC) :
    ReadsRest (First.Att.P.inOf seat c) := by
  intro s
  unfold First.Att.P.inOf
  rw [h.pts s, h.look s, h.zk s, h.cols s]

theorem keysOfK_rest (seat : First.Att.P.SeatC S) (h : SeatRest seat) (c : ParC) :
    ReadsRest (First.Att.P.keysOfK seat c) := by
  intro s
  unfold First.Att.P.keysOfK
  rw [inOf_rest seat h c s, h.pad s]

theorem readersOfK_rest (seat : First.Att.P.SeatC S) (h : SeatRest seat) (c : ParC) :
    ReadsRest (First.Att.P.readersOfK seat c) := by
  intro s
  unfold First.Att.P.readersOfK
  rw [inOf_rest seat h c s]

theorem respects_firstAt (seat : First.Att.P.SeatC S) (h : SeatRest seat) (c : ParC) :
    Respects (firstAt seat c) :=
  respects_readRest _ fun s => by
    unfold First.Att.P.firstK
    rw [inOf_rest seat h c s]
    cases First.Att.P.inOf seat c s with
    | none => rfl
    | some x =>
      obtain ⟨i, K⟩ := x
      cases hq : First.Att.P.Runs.firstRun i K <;>
        simp [hq, asClaimsOf, named, Except.map, bind, Option.bind]

theorem respects_keysAt (seat : First.Att.P.SeatC S) (h : SeatRest seat) (c : ParC) :
    Respects (keysAt seat c) :=
  respects_readRest _ fun s => by
    unfold First.Att.P.keysK
    rw [keysOfK_rest seat h c s]
    cases First.Att.P.keysOfK seat c s <;> rfl

theorem respects_secondAt (seat : First.Att.P.SeatC S) (h : SeatRest seat) (c : ParC) :
    Respects (secondAt seat c) :=
  respects_readRest _ fun s => by
    unfold First.Att.P.secondK
    rw [inOf_rest seat h c s]
    cases First.Att.P.inOf seat c s with
    | none => rfl
    | some x =>
      obtain ⟨i, K⟩ := x
      cases hq : First.Att.P.Runs.secondRun i K <;>
        simp [hq, asClaimsOf, named, Except.map, bind, Option.bind]

/-- **The seat that reads what was heard is such a seat.** -/
theorem seatCO_rest (c : ParC) : SeatRest (seatCO c) where
  pts := fun s => by
    have hpt : ∀ (F : Fork) (zk : Array (Array E)) (h : First.Att.P.Heard),
        First.Att.P.ptsFrom c.geo zk h (forkRest F) = First.Att.P.ptsFrom c.geo zk h F :=
      fun F => K9.ptsFrom_of_shown F (forkRest F) (K9.shown_of_quiet F (forkRest F) rfl) c.geo
    cases hh : s.here <;> simp [seatCO, restOf, blank, blankHere, K1.restOf, hereRest, S.heard5?, hh, hpt]
  cols := fun s => by
    cases hh : s.here with
    | att a =>
      simp [seatCO, restOf, blank, blankHere, K1.restOf, hereRest, forkRest, hh]
      rfl
    | _ => simp [seatCO, restOf, blank, blankHere, K1.restOf, hereRest, hh]
  look := fun s => by cases hh : s.here <;> simp [seatCO, restOf, blank, blankHere, K1.restOf, hereRest, hh]
  pad := fun s => by cases hh : s.here <;> simp [seatCO, restOf, blank, blankHere, K1.restOf, hereRest, hh]
  zk := fun s => by cases hh : s.here <;> simp [seatCO, restOf, blank, blankHere, K1.restOf, hereRest, hh]

/-! ## All that an attention segment's blocks state -/

theorem block_respects (digits : Bool) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p : First.Look.P) :
    ∀ r ∈ (K3.block (if digits then K3.seatDigits ofForm else K3.seatCalls ofForm) piece laid
      before p []).claims, digits = false → Respects r.2 := by
  intro r hr hd
  subst hd
  have hr' : r ∈ [("objects", K9.objectsCalls), ("guests", guestsNone)] := hr
  have : r = ("objects", K9.objectsCalls) ∨ r = ("guests", guestsNone) := by
    simpa using hr'
  cases this with
  | inl h => rw [h]; exact respects_objectsCalls
  | inr h => rw [h]; exact respects_guestsNone

theorem runsO_respects (A : Attention.Plan) :
    ∀ r ∈ (First.Att.P.runsO A).map runOfForms, Respects r.2 := by
  intro r hr
  have : r = runOfForms ("first", fun _ s => named "K5.first"
        (First.Att.P.firstK (seatCO (parCOf A)) (parCOf A) s)) ∨
      r = runOfForms ("keys", fun _ s => named "K5.keys"
        (First.Att.P.keysK (seatCO (parCOf A)) (parCOf A) s)) ∨
      r = runOfForms ("join", K3.joinRun (K3.seatCalls (Cl := Aff) id)
        (First.Att.P.keysOfO A)) ∨
      r = runOfForms ("second", fun _ s => named "K5.second"
        (First.Att.P.secondK (seatCO (parCOf A)) (parCOf A) s)) := by
    simpa [First.Att.P.runsO, First.Att.P.runsK] using hr
  rcases this with h | h | h | h
  · rw [h, K9.first_is]; exact respects_firstAt _ (seatCO_rest _) _
  · rw [h, K9.keys_is]; exact respects_keysAt _ (seatCO_rest _) _
  · rw [h, K9.join_is]; exact respects_joinCalls _ (keysOfK_rest _ (seatCO_rest _) _)
  · rw [h, K9.second_is]; exact respects_secondAt _ (seatCO_rest _) _

/-- K3's block at the calls with K5 as its caller: "planes" is stated behind the block's own
runs. -/
theorem withCaller_respects (A : Attention.Plan) (b b₀ : Block S Claim) (p : First.Look.P)
    (h0 : ∀ r ∈ b₀.claims, Respects r.2)
    (hb : b = K3.withCaller (K3.seatCalls ofForm) p (First.Att.P.readersOfO A) b₀) :
    ∀ r ∈ b.claims, Respects r.2 := by
  intro r hr
  rw [hb] at hr
  have : r ∈ b₀.claims ∨ r = ("planes", planesCalls p.lm (First.Att.P.readersOfO A)) := by
    simpa [K3.withCaller, K9.planesCalls_is, ofForm] using hr
  cases this with
  | inl h' => exact h0 r h'
  | inr h' =>
    rw [h']
    exact respects_planesCalls p.lm _ (readersOfK_rest _ (seatCO_rest _) _)

end VerifiableInference.Desc.K1.Q

#print axioms VerifiableInference.Desc.K1.Q.respects_flRun
#print axioms VerifiableInference.Desc.K1.Q.respects_joinCalls
#print axioms VerifiableInference.Desc.K1.Q.respects_planesCalls
#print axioms VerifiableInference.Desc.K1.Q.seatCO_rest
#print axioms VerifiableInference.Desc.K1.Q.respects_firstAt
#print axioms VerifiableInference.Desc.K1.Q.respects_keysAt
#print axioms VerifiableInference.Desc.K1.Q.respects_secondAt
#print axioms VerifiableInference.Desc.K1.Q.block_respects
#print axioms VerifiableInference.Desc.K1.Q.runsO_respects
#print axioms VerifiableInference.Desc.K1.Q.withCaller_respects
