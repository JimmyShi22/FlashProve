-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Cut/CutKit.lean: the small tools for the cut of the lookup's hearing (`K3.messages`,
Johnson/Desc/First/Look/K3Lookup.lean) into the library's flat pieces. Definitions, and theorems with
their proofs.

A flat function (`Fl`, OnBytes/K/Kc/Flat.lean) goes from a sub-proof's ledger and a tape of rounds
to nothing, or to a value, the ledger behind and the tape left. "It returns" is written here as
the equation x F t = some (a, G, u).

Main names:

  `bindS`, `bindM`, `pureS`, `pureM`, `mustS`, `mustM`: the laws of Johnson/Top/H/FlPort/Kit.lean
    on "x, then f", on a plain value and on a public condition, in that form. Nothing new is
    proved in them.
  `Gives R x y`: wherever x returns, y returns, with the same ledger and the same tape, and the
    two values stand in the relation R. Rules: `Gives.bind`, `Gives.pures`, `Gives.foldRange` (two
    folds over runs of numbers of one length, with a relation that moves with the index).
  `shownS`, `shownM`; `answer_anyLedger`; `pscRow_anyTape`: reading a shown value changes nothing;
    a draw leaves the ledger and goes the same way on any ledger; the making of a row leaves the
    tape and goes the same way on any tape.
  `point_size`: the n drawn elements are n.

Limits. `Gives` goes one way: nothing is said where x refuses, nor that x returns where y does.
These are ties between texts, equations on what they return: they have no error term. No routine
in a context of the verifier program's channel is named.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.K.Kc.FlatHear
import Johnson.Top.H.FlPort.Kit
import Johnson.Top.H.FlPort.PscRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3Cut
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc)

section Ways
variable {α β γ δ : Type}

/-- "x, then f" returns: x returns, and f does from there. -/
theorem bindS {x : Fl α} {f : α → Fl β} {F : Fork} {t : Tape} {r : β × Fork × Tape}
    (h : (x >>= f) F t = some r) :
    ∃ a F1 t1, x F t = some (a, F1, t1) ∧ f a F1 t1 = some r :=
  (Fo.Tp.bind_ok x f F t ((r.1, r.2.1), r.2.2)).1 h

/-- x returns and f does from there: "x, then f" returns. -/
theorem bindM {x : Fl α} {f : α → Fl β} {F : Fork} {t : Tape} {a : α} {F1 : Fork} {t1 : Tape}
    {r : β × Fork × Tape} (h1 : x F t = some (a, F1, t1)) (h2 : f a F1 t1 = some r) :
    (x >>= f) F t = some r :=
  (Fo.Tp.bind_ok x f F t ((r.1, r.2.1), r.2.2)).2 ⟨a, F1, t1, h1, h2⟩

/-- A plain value: ledger and tape stay. -/
theorem pureS {a b : α} {F G : Fork} {t u : Tape} (h : (pure a : Fl α) F t = some (b, G, u)) :
    b = a ∧ G = F ∧ u = t := by
  have e : ((b, G), u) = ((a, F), t) := (Fo.Tp.pure_ok a F t ((b, G), u)).1 h
  cases e
  exact ⟨rfl, rfl, rfl⟩

/-- A plain value returns. -/
theorem pureM (a : α) (F : Fork) (t : Tape) : (pure a : Fl α) F t = some (a, F, t) := rfl

/-- A public condition that passes was true; ledger and tape stay. -/
theorem mustS {b : Bool} {x : Unit} {F G : Fork} {t u : Tape}
    (h : Fl.must b F t = some (x, G, u)) : b = true ∧ G = F ∧ u = t := by
  obtain ⟨hb, e⟩ := (Fo.Tp.must_ok b F t ((x, G), u)).1 h
  cases e
  exact ⟨hb, rfl, rfl⟩

/-- A true public condition passes. -/
theorem mustM {b : Bool} (hb : b = true) (F : Fork) (t : Tape) :
    Fl.must b F t = some ((), F, t) :=
  (Fo.Tp.must_ok b F t (((), F), t)).2 ⟨hb, rfl⟩

/-- **Wherever x returns, y returns, with the same ledger and tape, and the values stand in R.** -/
def Gives (R : α → β → Prop) (x : Fl α) (y : Fl β) : Prop :=
  ∀ F t a G u, x F t = some (a, G, u) → ∃ b, y F t = some (b, G, u) ∧ R a b

theorem Gives.pures {R : α → β → Prop} {a : α} {b : β} (h : R a b) :
    Gives R (Pure.pure a : Fl α) (Pure.pure b : Fl β) := by
  intro F t a' G u e
  obtain ⟨rfl, rfl, rfl⟩ := pureS e
  exact ⟨b, rfl, h⟩

theorem Gives.bind {R : α → β → Prop} {S : γ → δ → Prop} {x : Fl α} {y : Fl β} {f : α → Fl γ}
    {g : β → Fl δ} (h1 : Gives R x y) (h2 : ∀ a b, R a b → Gives S (f a) (g b)) :
    Gives S (x >>= f) (y >>= g) := by
  intro F t c G u e
  obtain ⟨a, F1, t1, e1, e2⟩ := bindS e
  obtain ⟨b, e3, r⟩ := h1 F t a F1 t1 e1
  obtain ⟨d, e4, s⟩ := h2 a b r F1 t1 c G u e2
  exact ⟨d, bindM e3 e4, s⟩

/-- Two folds over runs of n numbers, from s and from s'. R i: the relation in front of step i. -/
theorem Gives.foldRange (f : α → Nat → Fl α) (g : β → Nat → Fl β) :
    ∀ (n : Nat) (R : Nat → α → β → Prop) (s s' : Nat) (a : α) (b : β),
      (∀ i a b, i < n → R i a b → Gives (R (i + 1)) (f a (s + i)) (g b (s' + i))) → R 0 a b →
      Gives (R n) ((List.range' s n).foldlM f a) ((List.range' s' n).foldlM g b)
  | 0, R, s, s', a, b, _, h0 => by
    rw [List.range'_zero, List.range'_zero, List.foldlM_nil, List.foldlM_nil]
    exact Gives.pures h0
  | n + 1, R, s, s', a, b, hs, h0 => by
    rw [List.range'_succ, List.range'_succ, List.foldlM_cons, List.foldlM_cons]
    refine Gives.bind (hs 0 a b (Nat.succ_pos n) h0) fun a1 b1 r1 => ?_
    refine Gives.foldRange f g n (fun i => R (i + 1)) (s + 1) (s' + 1) a1 b1
      (fun i a2 b2 hi r2 => ?_) r1
    have e1 : s + 1 + i = s + (i + 1) := by omega
    have e2 : s' + 1 + i = s' + (i + 1) := by omega
    rw [e1, e2]
    exact hs (i + 1) a2 b2 (Nat.succ_lt_succ hi) r2

end Ways

/-! ## What leaves the ledger, what leaves the tape -/

/-- Reading a shown value changes nothing. -/
theorem shownS {j : Nat} {F G : Fork} {t u : Tape} {v : E}
    (h : Fl.shown j F t = some (v, G, u)) : F.shown j = some v ∧ G = F ∧ u = t := by
  obtain ⟨a, ha, e⟩ := (Fo.Tp.shown_ok j F t ((v, G), u)).1 h
  cases e
  exact ⟨ha, rfl, rfl⟩

theorem shownM {j : Nat} {F : Fork} {v : E} (h : F.shown j = some v) (t : Tape) :
    Fl.shown j F t = some (v, F, t) :=
  (Fo.Tp.shown_ok j F t ((v, F), t)).2 ⟨v, h, rfl⟩

/-- A draw leaves the ledger, and goes the same way on any ledger. -/
theorem answer_anyLedger {r : Model.RoundName} {F G : Fork} {t u : Tape} {x : E}
    (h : Fl.answer r F t = some (x, G, u)) :
    G = F ∧ ∀ F' : Fork, Fl.answer r F' t = some (x, F', u) := by
  unfold Fl.answer at h
  obtain ⟨a, c1, hc, e⟩ := (Fo.Tp.lift_ok _ F t ((x, G), u)).1 h
  cases e
  refine ⟨rfl, fun F' => ?_⟩
  unfold Fl.answer
  exact (Fo.Tp.lift_ok _ F' t ((_, F'), _)).2 ⟨_, _, hc, rfl⟩

/-- The making of a row leaves the tape, and goes the same way on any tape. -/
theorem pscRow_anyTape {p : Psc} {S0 : E} {kept : Aff} {F G : Fork} {t u : Tape} {x : Aff × Psc}
    (h : Fl.pscRow p S0 kept F t = some (x, G, u)) :
    u = t ∧ ∀ t' : Tape, Fl.pscRow p S0 kept F t' = some (x, G, t') := by
  unfold Fl.pscRow at h
  obtain ⟨_, F1, t1, h1, g1⟩ := bindS h
  obtain ⟨hb, e1, e2⟩ := mustS h1
  subst e1 e2
  obtain ⟨_, F2, t2, h2, g2⟩ := bindS g1
  obtain ⟨G', hG, e⟩ := (Fo.Tp.change_ok _ _ _ (((), F2), t2)).1 h2
  cases e
  obtain ⟨e3, e4, e5⟩ := pureS g2
  subst e3 e4 e5
  refine ⟨rfl, fun t' => ?_⟩
  unfold Fl.pscRow
  refine bindM (mustM hb _ t') ?_
  refine bindM ((Fo.Tp.change_ok _ _ t' (((), _), t')).2 ⟨_, hG, rfl⟩) ?_
  rfl

/-- The n drawn elements are n. -/
theorem point_size {r : Model.RoundName} {n : Nat} {F G : Fork} {t u : Tape} {v : Array E}
    (h : Fl.point r n F t = some (v, G, u)) : v.size = n := by
  unfold Fl.point at h
  obtain ⟨a, c1, hc, e⟩ := (Fo.Tp.lift_ok _ F t ((v, G), u)).1 h
  cases e
  exact (Fo.Tp.pointOn_some hc).1

end VerifiableInference.Desc.K3Cut
