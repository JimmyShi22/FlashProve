-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Led/LedRowsLevel.lean: which virtual rows the claims name that a layer of a product
tree and a token sumcheck leave.

The claim of a masked sumcheck (Psc.rowForm, OnBytes/Model/Psc.lean) holds the sumcheck's start
form. This file follows the start form through the routines that read the sumcheck's messages.

Main names.
  Gives r P: whenever the routine r returns, its value has the property P; gives_pure, gives_bind,
    gives_true.
  gives_pscBegin, gives_roundIn, gives_pscEnds, gives_pscRow: the state of a sumcheck keeps the
    start form with which it began.
  gives_levelIn: the claim of a layer that began from the form C is p.rowForm S0 {} for a state p
    with the start form C.
  gives_tscIn: the start form of a token sumcheck is the hidden value under its first slot.
  levelIn_rows, tscIn_rows: so, by rowsIn_rowForm (LedRowsPsc.lean): a layer's claim names the
    virtual rows that C names, and no other; a token sumcheck's claim names those that the kept form
    names, and no other.
  rowsIn_normsStart: the start form of the layer of the squares names no entry of a virtual row.

What this file does not claim. Nothing where a routine does not return.


-/
import OnBytes.Model.Layer
import OnBytes.Tie.Pv.Led.LedRowsPsc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows
open OnBytes.Model

/-- Whenever the routine returns, its value has the property P. -/
def Gives {α : Type} (r : SubM α) (P : α → Prop) : Prop :=
  ∀ (F G : Fork) (c c' : Ctx) (a : α), r F c = .ok ((a, G), c') → P a

theorem gives_true {α : Type} (r : SubM α) : Gives r fun _ => True := fun _ _ _ _ _ _ => trivial

theorem gives_pure {α : Type} {P : α → Prop} (a : α) (h : P a) : Gives (pure a : SubM α) P :=
  fun F G c c' x hr => by
    have e := (PscRun.pure_ok a F c _).1 hr
    simp only [Prod.mk.injEq] at e
    rw [e.1.1]
    exact h

theorem gives_bind {α β : Type} {r : SubM α} {k : α → SubM β} {Q : α → Prop} {P : β → Prop}
    (h1 : Gives r Q) (h2 : ∀ x, Q x → Gives (k x) P) : Gives (r >>= k) P :=
  fun F G c c' y h => by
    obtain ⟨x, F1, c1, e1, e2⟩ := (PscRun.bind_ok _ _ _ _ _).1 h
    exact h2 x (h1 F F1 c c1 x e1) F1 G c1 c' y e2

theorem gives_pscBegin (C : Aff) : Gives (pscBegin C) fun p => p.start = C :=
  fun F G c c' p hr => by
    obtain ⟨_, _, _, -, -, -, rfl⟩ := PscRun.pscBegin_ok _ _ _ _ _ _ hr
    rfl

theorem gives_roundIn (form : RoundForm) (p : Psc) (z : E) (degree : Nat) :
    Gives (roundIn form p z degree) fun x => x.2.start = p.start := fun F G c c' a hr => by
  obtain ⟨r, p'⟩ := a
  obtain ⟨_, _, -, -, -, -, -, -, rfl⟩ := PscRun.roundIn_ok _ _ _ _ _ _ _ _ _ _ hr
  rfl

theorem gives_pscEnds (p : Psc) (degreeInY n : Nat) :
    Gives (pscEnds p degreeInY n) fun x => x.2.start = p.start := fun F G c c' a hr => by
  obtain ⟨e, p'⟩ := a
  obtain ⟨_, _, _, -, -, -, -, -, -, -, -, hp⟩ := PscRun.pscEnds_ok _ _ _ _ _ _ _ _ _ hr
  show p'.start = p.start
  rw [hp]

theorem gives_pscRow (p : Psc) (S0 : E) (kept : Aff) :
    Gives (pscRow p S0 kept) fun x => x.1 = p.rowForm S0 kept := fun F G c c' a hr => by
  obtain ⟨row, p'⟩ := a
  exact (PscRun.pscRow_ok _ _ _ _ _ _ _ _ _ hr).2.2.2.2.2.2.1

theorem gives_levelRounds (mu : Nat) (rho : Array E) : ∀ (order : List Nat) (r : Array E)
    (p : Psc), Gives (levelRounds mu rho order r p) fun x => x.2.start = p.start
  | [], r, p => by
    unfold levelRounds
    exact gives_pure _ rfl
  | v :: order, r, p => by
    unfold levelRounds
    refine gives_bind (gives_true _) fun _ _ => gives_bind (gives_roundIn _ _ _ _) fun x hx => ?_
    intro F G c c' a hr
    exact (gives_levelRounds mu rho order _ _ F G c c' a hr).trans hx

/-- The claim of a layer that began from the form C. -/
theorem gives_levelIn (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) :
    Gives (levelIn mu rho C order) fun lv =>
      ∃ p S0, lv.row = Psc.rowForm p S0 {} ∧ p.start = C := by
  unfold levelIn
  refine gives_bind (gives_true _) fun _ _ => gives_bind (gives_pscBegin C) fun p0 h0 => ?_
  refine gives_bind (gives_levelRounds mu rho order _ p0) fun x hx => ?_
  obtain ⟨r, p1⟩ := x
  refine gives_bind (gives_pscEnds p1 2 2) fun y hy => ?_
  obtain ⟨sL, p2⟩ := y
  refine gives_bind (gives_true _) fun tau _ => gives_bind (gives_true _) fun a _ =>
    gives_bind (gives_true _) fun b _ => gives_bind (gives_pscRow p2 _ {}) fun z hz => ?_
  obtain ⟨row, p3⟩ := z
  exact gives_pure _ ⟨p2, _, hz, hy.trans (hx.trans h0)⟩

theorem gives_tscLoop : ∀ (zs : List E) (r : Array E) (p : Psc),
    Gives (tscLoop zs r p) fun x => x.2.start = p.start
  | [], r, p => by
    unfold tscLoop
    exact gives_pure _ rfl
  | z :: zs, r, p => by
    unfold tscLoop
    refine gives_bind (gives_roundIn _ _ _ _) fun x hx => ?_
    intro F G c c' a hr
    exact (gives_tscLoop zs _ _ F G c c' a hr).trans hx

theorem gives_tscRounds (P : Array E) (lt : Nat) :
    Gives (tscRounds P lt) fun t => t.p.start = Aff.slot t.sCl := by
  unfold tscRounds
  refine gives_bind (gives_true _) fun _ _ => gives_bind (gives_true _) fun sCl _ =>
    gives_bind (gives_pscBegin _) fun p0 h0 => gives_bind (gives_tscLoop _ _ p0) fun x hx => ?_
  obtain ⟨r, p1⟩ := x
  exact gives_pure _ (hx.trans h0)

/-- The start form of a token sumcheck is the hidden value under its first slot. -/
theorem gives_tscIn (P : Array E) (lt shown degreeInY : Nat) :
    Gives (tscIn P lt shown degreeInY) fun t => t.p.start = Aff.slot t.sCl := by
  unfold tscIn
  refine gives_bind (gives_tscRounds P lt) fun o ho => gives_bind (gives_pscEnds o.p _ _)
    fun y hy => ?_
  obtain ⟨sEnd, p⟩ := y
  exact gives_pure _ (hy.trans ho)

variable {Q : Nat → Nat → Prop}

/-- A layer's claim names the virtual rows that its start form names, and no other. -/
theorem levelIn_rows {mu : Nat} {rho : Array E} {C : Aff} {order : List Nat} {F G : Fork}
    {c c' : Ctx} {lv : Level} (h : levelIn mu rho C order F c = .ok ((lv, G), c'))
    (hC : RowsIn Q C) : RowsIn Q lv.row := by
  obtain ⟨p, S0, e, rfl⟩ := gives_levelIn mu rho C order F G c c' lv h
  rw [e]
  exact rowsIn_rowForm p S0 hC rowsIn_empty

/-- A token sumcheck's claim names the virtual rows that the kept form names, and no other. -/
theorem tscIn_rows {P : Array E} {lt shown degreeInY : Nat} {F G : Fork} {c c' : Ctx} {t : Tsc}
    (h : tscIn P lt shown degreeInY F c = .ok ((t, G), c')) (S0 : E) {kept : Aff}
    (hk : RowsIn Q kept) : RowsIn Q (t.p.rowForm S0 kept) := by
  refine rowsIn_rowForm t.p S0 ?_ hk
  rw [gives_tscIn P lt shown degreeInY F G c c' t h]
  exact rowsIn_slot _

/-- The start form of the layer of the squares names no entry of a virtual row. -/
theorem rowsIn_normsStart (y : Layer.Lay) (sW : Nat) (gp rhoI PV : Array E) :
    RowsIn Q (Layer.normsStart y sW gp rhoI PV).1 := by
  unfold Layer.normsStart
  dsimp only
  refine rowsIn_foldl _ (fun f i hf => ?_) _ _ ?_
  · exact rowsIn_foldl _ (fun f' s hf' => rowsIn_addMul _ hf' (rowsIn_slot _)) _ _ hf
  · exact rowsIn_ofConst _

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.levelIn_rows
#print axioms OnBytes.Road.Rows.tscIn_rows
#print axioms OnBytes.Road.Rows.rowsIn_normsStart
