--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Meaning/HKTDrawn.lean: the eps of the second token sumcheck of the layers' own rounds is one
of the elements that the stretch's tape holds as drawn; so the field hinv of Pub34 holds where these
have words below p.

The layers' hearing runs over plain functions on a ledger and a tape of rounds
(OnBytes/K/Kc/Flat.lean); a round of the tape holds the elements sent and the elements drawn. The
test "coin-zero" compares eps's words with 0, which does not say that eps reads as an element other
than 0 (Johnson/Meaning/HKTHear.lean, `coinZero_not_enough`). This file follows eps back to the
tape.

How a statement reads. D is any property of elements. `Good D t`: every element that a round of the
tape t holds as drawn has D. `Walk D x Q`: whenever the routine x returns from a good tape, the tape
that it leaves is good and its value has Q.

Main theorems (namespace `Meaning.HKT`).
  The rules: `walk_pure`, `walk_bind`, `walk_mono`, `walk_still`, `walk_onTape`, `walk_ite`.
  The steps on the tape: `good_recv`, `good_recvLoop`, `good_closeN`, `good_closeOne`,
      `good_closeRows`.
  The library's plain functions: `walk_pscBegin` (eps has D), `walk_pscRound`, `walk_roundIn`,
      `walk_pscEnds`, `walk_pscRow`, `walk_tscLoop` (these keep eps), `walk_tscIn` (eps has D),
      `walk_levelIn`, `walk_claimsIn` and the calls on the rounds.
  The layers' own text: `walk_hearNorms`, `walk_hearTerms`.
  `hear_eps`: in a run of `hearFl` from a good tape, eps of the second token sumcheck has D.
  `hear_three`: hT, hKT and hinv (in the library's field) at what `hearFl` returns, from a tape
      whose drawn elements have words below p.

Limits. That the tape's drawn elements have words below p is a premise. Where a round's elements are
drawn by the format's rule the library's `drawElems_ok` (OnBytes/Tie/Pv/Keeps/KeepsPend.lean) says
it of them; that the tape which the layers' block hands to `hearFl` holds elements so drawn is shown
nowhere here. hinv is given at the library's field (`Reading.gl`) alone. Nothing on a draw's
distribution, on soundness.
-/
import Johnson.Meaning.HKTHear

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.HKT
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env Lay Heard Pub Own HPlan2)
open OnBytes.K.Kc
open OnBytes.Desc.First.K4 (engFl hearFl hear hearTerms hearNorms)

variable (D : E → Prop)

/-- Every element that a round of the tape holds as drawn has the property D. -/
def Good (t : Tape) : Prop := ∀ r ∈ t, ∀ e ∈ r.drawn, D e

/-- From a good tape the routine leaves a good tape, and its value has the property Q. -/
def Walk {α : Type} (x : Fl α) (Q : α → Prop) : Prop :=
  ∀ (F : Fork) (t : Tape) (a : α) (G : Fork) (u : Tape),
    Good D t → x F t = some (a, G, u) → Good D u ∧ Q a

variable {D}

theorem Good.tail {r : FlatRound} {t : Tape} (h : Good D (r :: t)) : Good D t :=
  fun s hs => h s (List.mem_cons_of_mem _ hs)

theorem walk_pure {α : Type} (a : α) {Q : α → Prop} (h : Q a) : Walk D (pure a : Fl α) Q := by
  intro F t b G u g e
  have e' : Fl.ret a F t = some (b, G, u) := e
  unfold Fl.ret at e'
  simp only [Option.some.injEq, Prod.mk.injEq] at e'
  obtain ⟨rfl, _, rfl⟩ := e'
  exact ⟨g, h⟩

theorem walk_bind {α β : Type} {x : Fl α} {f : α → Fl β} {Q1 : α → Prop} {Q : β → Prop}
    (hx : Walk D x Q1) (hf : ∀ a, Q1 a → Walk D (f a) Q) : Walk D (x >>= f) Q := by
  intro F t b G u g e
  obtain ⟨a, G1, u1, e1, e2⟩ := bind_some e
  obtain ⟨g1, q1⟩ := hx F t a G1 u1 g e1
  exact hf a q1 G1 u1 b G u g1 e2

theorem walk_mono {α : Type} {x : Fl α} {Q Q' : α → Prop} (hx : Walk D x Q)
    (h : ∀ a, Q a → Q' a) : Walk D x Q' := fun F t a G u g e =>
  ⟨(hx F t a G u g e).1, h a (hx F t a G u g e).2⟩

/-- A routine that leaves the tape as it was. -/
theorem walk_still {α : Type} {x : Fl α}
    (h : ∀ F t a G u, x F t = some (a, G, u) → u = t) : Walk D x fun _ => True := by
  intro F t a G u g e
  rw [h F t a G u e]
  exact ⟨g, trivial⟩

theorem walk_change (f : Fork → Option Fork) : Walk D (Fl.change f) fun _ => True :=
  walk_still fun F t a G u e => by
    unfold Fl.change at e
    obtain ⟨_, _, e⟩ := Option.map_eq_some_iff.mp e
    simp only [Prod.mk.injEq] at e
    exact e.2.2.symm

theorem walk_take {α : Type} (f : Fork → Option (α × Fork)) : Walk D (Fl.take f) fun _ => True :=
  walk_still fun F t a G u e => by
    unfold Fl.take at e
    obtain ⟨_, _, e⟩ := Option.map_eq_some_iff.mp e
    simp only [Prod.mk.injEq] at e
    exact e.2.2.symm

theorem walk_ask {α : Type} (f : Fork → Option α) : Walk D (Fl.ask f) fun _ => True :=
  walk_still fun F t a G u e => by
    unfold Fl.ask at e
    obtain ⟨_, _, e⟩ := Option.map_eq_some_iff.mp e
    simp only [Prod.mk.injEq] at e
    exact e.2.2.symm

theorem walk_must (b : Bool) : Walk D (Fl.must b) fun _ => True :=
  walk_still fun _ _ _ _ _ e => (Desc.First.K4.must_some e).2.2

theorem walk_need {α : Type} (x : Option α) : Walk D (Fl.need x) fun _ => True :=
  walk_still fun F t a G u e => by
    unfold Fl.need at e
    obtain ⟨_, _, e⟩ := Option.map_eq_some_iff.mp e
    simp only [Prod.mk.injEq] at e
    exact e.2.2.symm

theorem walk_onTape {α : Type} {g : Tape → Option (α × Tape)} {Q : α → Prop}
    (h : ∀ t a u, Good D t → g t = some (a, u) → Good D u ∧ Q a) : Walk D (Fl.onTape g) Q := by
  intro F t a G u gd e
  unfold Fl.onTape at e
  obtain ⟨⟨a', u'⟩, e1, e⟩ := Option.map_eq_some_iff.mp e
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, _, rfl⟩ := e
  exact h t _ _ gd e1

/-! ## The steps on the tape -/

theorem good_recv {t u : Tape} {x : E} (g : Good D t) (e : recv t = some (x, u)) : Good D u := by
  unfold recv at e
  split at e
  · simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨_, rfl⟩ := e
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact fun e he => g _ List.mem_cons_self e he
    · exact g r (List.mem_cons_of_mem _ hr)
  · cases e

theorem good_recvLoop : ∀ (n : Nat) (a : Array E) {t u : Tape} {b : Array E}, Good D t →
    recvLoop n a t = some (b, u) → Good D u
  | 0, a, t, u, b, g, e => by
    unfold recvLoop at e
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    rw [← e.2]
    exact g
  | n + 1, a, t, u, b, g, e => by
    unfold recvLoop at e
    split at e
    · rename_i x u1 h1
      exact good_recvLoop n _ (good_recv g h1) e
    · cases e

theorem good_closeN {name : String} {nz n : Nat} {t u : Tape} {d : List E} (g : Good D t)
    (e : closeN name nz n t = some (d, u)) : Good D u ∧ ∀ x ∈ d, D x := by
  unfold closeN at e
  split at e
  · split at e
    · simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨g.tail, g _ List.mem_cons_self⟩
    · cases e
  · cases e

theorem good_closeOne {name : String} {nz : Nat} {t u : Tape} {x : E} (g : Good D t)
    (e : closeOne name nz t = some (x, u)) : Good D u ∧ D x := by
  unfold closeOne at e
  split at e
  · split at e
    · simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨g.tail, g _ List.mem_cons_self _ (by simp)⟩
    · cases e
  · cases e

theorem good_closeRows {rows : Nat} {t u : Tape} {x : E} (g : Good D t)
    (e : closeRows rows t = some (x, u)) : Good D u ∧ D x := by
  unfold closeRows at e
  split at e
  · split at e
    · simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      exact ⟨g.tail, g _ List.mem_cons_self _ (by simp)⟩
    · cases e
  · cases e

/-! ## The calls on the rounds -/

theorem walk_read (n : Nat) : Walk D (Fl.read n) fun _ => True :=
  walk_onTape fun _ _ _ g e => ⟨good_recvLoop n _ g e, trivial⟩

theorem walk_readSum : Walk D Fl.readSum fun _ => True :=
  walk_onTape fun _ _ _ g e => ⟨good_recv g e, trivial⟩

theorem walk_answer (r : RoundName) : Walk D (Fl.answer r) D :=
  walk_onTape fun _ _ _ g e => good_closeOne g e

theorem walk_point (r : RoundName) (n : Nat) : Walk D (Fl.point r n) fun _ => True :=
  walk_onTape fun t a u g e => by
    unfold Fl.pointOn at e
    obtain ⟨⟨d, u'⟩, e1, e⟩ := Option.map_eq_some_iff.mp e
    simp only [Prod.mk.injEq] at e
    rw [← e.2]
    exact ⟨(good_closeN g e1).1, trivial⟩

theorem walk_batch (rows : Nat) : Walk D (Fl.batch rows) fun _ => True :=
  walk_onTape fun t a u g e => by
    unfold Fl.batchOn at e
    split at e
    · obtain ⟨⟨d, u'⟩, e1, e⟩ := Option.map_eq_some_iff.mp e
      simp only [Prod.mk.injEq] at e
      rw [← e.2]
      exact ⟨(good_closeRows g e1).1, trivial⟩
    · cases e

theorem walk_empty (r : RoundName) : Walk D (Fl.empty r) fun _ => True :=
  walk_onTape fun t a u g e => by
    unfold Fl.emptyOn at e
    obtain ⟨⟨d, u'⟩, e1, e⟩ := Option.map_eq_some_iff.mp e
    simp only [Prod.mk.injEq] at e
    rw [← e.2]
    exact ⟨(good_closeN g e1).1, trivial⟩

theorem walk_claimsIn (n : Nat) : Walk D (Fl.claimsIn n) fun _ => True := by
  unfold Fl.claimsIn
  refine walk_bind (walk_read n) fun v _ => ?_
  refine walk_bind (walk_must _) fun _ _ => ?_
  refine walk_bind (walk_take _) fun j _ => ?_
  refine walk_bind (walk_change _) fun _ _ => ?_
  exact walk_pure _ trivial

/-! ## The masked sumcheck: eps is a drawn element, and the rounds keep it -/

theorem walk_pscBegin (C : Aff) : Walk D (Fl.pscBegin C) fun p => D p.eps := by
  unfold Fl.pscBegin Fl.pscBeginAt
  refine walk_bind (walk_ask _) fun tg _ => ?_
  refine walk_bind (Q1 := fun p => D p.eps) ?_ fun p hp => walk_pure _ hp
  refine walk_bind (walk_take _) fun first _ => ?_
  refine walk_bind walk_readSum fun mu _ => ?_
  refine walk_bind (walk_answer _) fun eps he => ?_
  exact walk_pure _ he

theorem walk_pscRound (p : Psc) (w : OnBytes.Psc.Weight) {draw : Tape → Option (E × Tape)}
    (hd : ∀ t a u, Good D t → draw t = some (a, u) → Good D u) :
    Walk D (Fl.pscRound p w draw) fun x => x.2.eps = p.eps := by
  unfold Fl.pscRound
  refine walk_bind (walk_must _) fun _ _ => ?_
  refine walk_bind (walk_read _) fun sent _ => ?_
  refine walk_bind (walk_must _) fun _ _ => ?_
  refine walk_bind (walk_onTape (Q := fun _ => True) fun t a u g e => ⟨hd t a u g e, trivial⟩)
    fun r _ => ?_
  refine walk_bind (walk_take _) fun _ _ => ?_
  exact walk_pure _ rfl

theorem walk_roundIn (form : RoundForm) (p : Psc) (z : E) (degree : Nat) :
    Walk D (Fl.roundIn form p z degree) fun x => x.2.eps = p.eps := by
  unfold Fl.roundIn
  refine walk_bind (walk_must _) fun _ _ => ?_
  refine walk_bind (walk_need _) fun w _ => ?_
  exact walk_pscRound p w fun _ _ _ g e => (good_closeOne g e).1

theorem walk_pscEnds (p : Psc) (dy n : Nat) :
    Walk D (Fl.pscEnds p dy n) fun x => x.2.eps = p.eps := by
  unfold Fl.pscEnds
  refine walk_bind (walk_must _) fun _ _ => ?_
  refine walk_bind (walk_pscRound p _ fun _ _ _ g e => (good_closeOne g e).1) ?_
  rintro ⟨beta, p'⟩ hp
  refine walk_bind (walk_read _) fun v _ => ?_
  refine walk_bind (walk_must _) fun _ _ => ?_
  refine walk_bind (walk_empty _) fun _ _ => ?_
  refine walk_bind (walk_take _) fun e _ => ?_
  refine walk_bind (walk_change _) fun _ _ => ?_
  exact walk_pure _ hp

theorem walk_pscRow (p : Psc) (S0 : E) (kept : Aff) :
    Walk D (Fl.pscRow p S0 kept) fun x => x.2.eps = p.eps := by
  unfold Fl.pscRow
  refine walk_bind (walk_must _) fun _ _ => ?_
  refine walk_bind (walk_change _) fun _ _ => ?_
  exact walk_pure _ rfl

theorem walk_levelRounds (mu : Nat) (rho : Array E) : ∀ (order : List Nat) (r : Array E) (p : Psc),
    Walk D (Fl.levelRounds mu rho order r p) fun _ => True
  | [], r, p => by
    unfold Fl.levelRounds
    exact walk_pure _ trivial
  | v :: order, r, p => by
    unfold Fl.levelRounds
    refine walk_bind (walk_must _) fun _ _ => ?_
    refine walk_bind (walk_roundIn _ _ _ _) ?_
    rintro ⟨x, p'⟩ _
    exact walk_levelRounds mu rho order _ _

theorem walk_levelIn (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) :
    Walk D (Fl.levelIn mu rho C order) fun _ => True := by
  unfold Fl.levelIn
  refine walk_bind (walk_must _) fun _ _ => ?_
  refine walk_bind (walk_pscBegin C) fun p _ => ?_
  refine walk_bind (walk_levelRounds mu rho order _ _) ?_
  rintro ⟨r, p'⟩ _
  refine walk_bind (walk_pscEnds _ _ _) ?_
  rintro ⟨sL, p''⟩ _
  refine walk_bind (walk_answer _) fun tau _ => ?_
  refine walk_bind (walk_ask _) fun _ _ => ?_
  refine walk_bind (walk_ask _) fun _ _ => ?_
  refine walk_bind (walk_pscRow _ _ _) ?_
  rintro ⟨row, _⟩ _
  exact walk_pure _ trivial

theorem walk_tscLoop : ∀ (zs : List E) (r : Array E) (p : Psc),
    Walk D (Fl.tscLoop zs r p) fun x => x.2.eps = p.eps
  | [], r, p => by
    unfold Fl.tscLoop
    exact walk_pure _ rfl
  | z :: zs, r, p => by
    unfold Fl.tscLoop
    refine walk_bind (walk_roundIn _ _ _ _) ?_
    rintro ⟨x, p'⟩ hp
    exact walk_mono (walk_tscLoop zs _ p') fun a ha => ha.trans hp

theorem walk_tscIn (P : Array E) (lt shown dy : Nat) :
    Walk D (Fl.tscIn P lt shown dy) fun o => D o.p.eps := by
  unfold Fl.tscIn Fl.tscRounds
  refine walk_bind (Q1 := fun o => D o.p.eps) ?_ fun o ho => ?_
  · refine walk_bind (walk_must _) fun _ _ => ?_
    refine walk_bind (walk_claimsIn 1) fun sCl _ => ?_
    refine walk_bind (walk_pscBegin _) fun p hp => ?_
    refine walk_bind (walk_tscLoop _ _ p) ?_
    rintro ⟨r, p'⟩ hp'
    refine walk_pure _ ?_
    show D p'.eps
    have e : p'.eps = p.eps := hp'
    rw [e]
    exact hp
  · refine walk_bind (walk_pscEnds o.p _ _) ?_
    rintro ⟨sEnd, p'⟩ hp'
    refine walk_pure _ ?_
    show D p'.eps
    have e : p'.eps = o.p.eps := hp'
    rw [e]
    exact ho

/-! ## The layers' own text -/

theorem walk_ite {α : Type} {c : Prop} [Decidable c] {a b : Fl α} {Q : α → Prop}
    (ha : Walk D a Q) (hb : Walk D b Q) : Walk D (if c then a else b) Q := by
  split
  · exact ha
  · exact hb

theorem walk_engPoint (r : RoundName) (n : Nat) : Walk D (engFl.point r n) fun _ => True := by
  show Walk D (if r == .batSigma then fun _ _ => none else Fl.point r n) fun _ => True
  refine walk_ite ?_ (walk_point r n)
  intro F t a G u _ e
  cases e

theorem walk_hearNorms (P : Pub) (g : Nat) (fo : Forest.Heard) :
    Walk D (hearNorms engFl P g fo) fun _ => True := by
  unfold hearNorms
  refine walk_bind (walk_engPoint _ _) fun PV _ => ?_
  dsimp only
  split
  all_goals
    refine walk_bind (Q1 := fun _ => True)
      (by first | exact walk_engPoint _ _ | exact walk_pure _ trivial) fun ZE _ => ?_
    refine walk_bind (Q1 := fun _ => True)
      (by first | exact walk_engPoint _ _ | exact walk_pure _ trivial) fun tkh _ => ?_
    refine walk_bind (walk_must _) fun _ _ => ?_
    refine walk_bind (walk_need _) fun Z _ => ?_
    refine walk_bind (walk_need _) fun ends _ => ?_
    refine walk_bind (walk_must _) fun _ _ => ?_
    refine walk_bind (walk_need _) fun ztF _ => ?_
    refine walk_bind (walk_claimsIn _) fun sW _ => ?_
    refine walk_bind (walk_batch _) fun gp _ => ?_
    refine walk_bind (walk_engPoint _ _) fun rhoI _ => ?_
    refine walk_bind (walk_levelIn _ _ _ _) fun wpl _ => ?_
    refine walk_bind (walk_claimsIn _) fun sPv _ => ?_
    refine walk_bind (walk_batch _) fun omV _ => ?_
    refine walk_bind (walk_tscIn _ _ _ _) fun tV _ => ?_
    exact walk_pure _ trivial

theorem walk_hearTerms (P : Pub) (H : Heard) :
    Walk D (hearTerms engFl P H) fun H' => ∀ tT, H'.tT = some tT → D tT.p.eps := by
  unfold hearTerms
  refine walk_bind (walk_tscIn _ _ _ _) fun tT hT => ?_
  refine walk_bind (walk_must _) fun _ _ => ?_
  refine walk_bind (walk_pscRow tT.p zeroE {}) ?_
  rintro ⟨row, p⟩ hp
  refine walk_pure _ ?_
  intro tT' e
  obtain rfl := Option.some.inj e
  show D p.eps
  have e2 : p.eps = tT.p.eps := hp
  rw [e2]
  exact hT

/-- **The eps of the second token sumcheck is one of the elements that the stretch's tape holds as
drawn**: whatever holds of all of these holds of it. -/
theorem hear_eps {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (gd : Good D t) (h : hearFl P hp g fo F t = some (o, F', t')) :
    ∀ tT, o.H.tT = some tT → D tT.p.eps := by
  obtain ⟨H0, F1, t1, F2, t2, hN, hT⟩ := hear_cut h
  exact (walk_hearTerms P H0 F1 t1 _ F2 t2 (walk_hearNorms P g fo F t _ F1 t1 gd hN).1 hT).2

/-- **The three fields hT, hKT and hinv of Pub34** (Johnson/Road/Rows/LayerEnds34.lean), in the
library's field, from a run of the layers' whole hearing on a tape whose drawn elements have words
below p. -/
theorem hear_three {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (ok : ∀ r ∈ t, ∀ e ∈ r.drawn, okE e = true)
    (h : hearFl P hp g fo F t = some (o, F', t')) :
    ∃ tT, o.H.tT = some tT ∧
      o.H.KT = (tT.p.rowForm zeroE {}).scale (negE (invE tT.p.eps)) ∧
      Reading.gl.val (negE (invE tT.p.eps)) * Reading.gl.val tT.p.eps = -1 := by
  obtain ⟨tT, hT, hK, nz⟩ := hear_KT h
  exact ⟨tT, hT, hK, hinv_gl (hear_eps (D := fun e => okE e = true) ok h tT hT) nz⟩

#print axioms walk_tscIn
#print axioms walk_hearNorms
#print axioms walk_hearTerms
#print axioms hear_eps
#print axioms hear_three

end Meaning.HKT
