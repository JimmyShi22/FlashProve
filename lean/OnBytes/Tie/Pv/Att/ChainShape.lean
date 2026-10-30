-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/ChainShape.lean: the rounds of a chain of masked sumchecks, draws and sent
scalars (Cb/Pv/Att/Chain.lean), against a list of entries of a plan.

Main names:
  roundIs_draw, roundIs_send: a round with an empty message, or with n scalars, in which v elements
    of E are drawn, in the terms of OnBytes/G4/RoundIs.lean.
  Fit c ds: the list ds of entries fits the chain c, stage by stage. At a sumcheck: its formats are
    cube variables followed by the further variable, and ds begins with pscEntries
    (OnBytes/Tie/Pv/Att/Shape.lean) at its numbers. At a draw: ds begins with an entry without bytes
    whose number drawE of elements of E is what is drawn, none of them barred from 0. At sent
    scalars: the same with 24 n bytes. It is a relation and no function of c, because a chain holds
    no names of rounds, no work and no number of rows, and does not say how many elements of E a
    draw is.
  Ch.shapeIs: if ds fits c then the rounds of c are an instance of ds (ShapeIs). Ch.shapeIs_R: the
    same of the shape of the reduction c.R Ex.
  Ch.planned: so, if a routine of the port's planner adds just rounds with the entries ds (Adds,
    OnBytes/Tie/Pv/Att/PlanOwn.lean), then whenever it ends well the shape of c.R Ex is an instance
    of the entries of the rounds that it has added.
  fit_done, fit_plain, fit_bat, fit_zero, fit_batSend: the steps from which a proof of Fit at a
    value is built: a plain sumcheck whose record fits (PlainSc.Fits) against lPsc; a draw of one
    element against an entry "BAT-sigma"; a draw of v elements against "ZERO"; n scalars and a draw
    of one element against "BAT-sigma" with 24 n bytes.

Limits: as in OnBytes/Tie/Pv/Att/Shape.lean: ShapeIs counts. At a draw and at sent scalars Fit reads
of an entry the three numbers msg, drawE and drawNZ alone; at a sumcheck it asks for the whole
entries of pscEntries, each sumcheck with a work of its own.
-/
import OnBytes.Tie.Pv.Att.PlanJoin
import Cb.Pv.Att.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open Iop Prob Cb Cb.Pv.Att Cb.Pv.Lay TWhole Johnson.L5.Layers OnBytes OnBytes.G4 OnBytes.Params
open OnBytes.Tie.Pv.Att.Plan

variable {E : Type} [Field E] [Fintype E]

omit [Fintype E] in
theorem roundIs_draw (D : Type) [Fintype D] [Nonempty D] (v : ℕ) (e : D ≃ (Fin v → E)) :
    RoundIs E (IOR.drawRound D) ⟨0, v, 0⟩ :=
  ⟨⟨({ toFun := fun _ i => i.elim0, invFun := fun _ => (), left_inv := fun _ => rfl,
        right_inv := fun _ => funext fun i => i.elim0 } : Unit ≃ (Fin 0 → E))⟩,
    ⟨e⟩, inferInstanceAs (IsEmpty Empty)⟩

omit [Fintype E] in
theorem roundIs_send (n : ℕ) (D : Type) [Fintype D] [Nonempty D] (v : ℕ) (e : D ≃ (Fin v → E)) :
    RoundIs E (sendRound E (Fin n) D) ⟨n, v, 0⟩ :=
  ⟨⟨Equiv.refl _⟩, ⟨e⟩, inferInstanceAs (IsEmpty Empty)⟩

variable {M : Type}

/-- The list of entries fits the chain, stage by stage. -/
def Fit : {X : Type} → Ch E M X → List Fmt.Entry → Prop
  | _, .done _, ds => ds = []
  | _, .ride Y n _ _ _ _ _ next, ds =>
    ∃ (w k : ℕ) (deg : Fin k → ℕ) (DY : ℕ) (ds' : List Fmt.Entry),
      Y.fmt = ldPartFmt E k deg ++ [pDummy E DY] ∧
      ds = pscEntries w n (List.ofFn deg) DY (Fintype.card Y.A) ++ ds' ∧ Fit next ds'
  | _, .draw D _ _ next, ds =>
    ∃ (e : Fmt.Entry) (ds' : List Fmt.Entry), Nonempty (D.D ≃ (Fin e.drawE → E)) ∧ e.msg = 0 ∧
      e.drawNZ = 0 ∧ ds = e :: ds' ∧ Fit next ds'
  | _, .send n D _ _ _ next, ds =>
    ∃ (e : Fmt.Entry) (ds' : List Fmt.Entry), Nonempty (D.D ≃ (Fin e.drawE → E)) ∧
      e.msg = 24 * n ∧ e.drawNZ = 0 ∧ ds = e :: ds' ∧ Fit next ds'

/-- The rounds of a chain are an instance of a list of entries that fits it. -/
theorem Ch.shapeIs : ∀ {X : Type} (c : Ch E M X) (ds : List Fmt.Entry), Fit c ds → ShapeIs E c.sh ds
  | _, .done _, _, h => by
    rw [show _ = [] from h]
    exact List.Forall₂.nil
  | _, .ride Y n _ _ _ _ _ next, _, h => by
    obtain ⟨w, k, deg, DY, ds', hf, hd, hn⟩ := h
    rw [hd]
    exact List.rel_append (ride_shape Y w n k deg DY hf) (Ch.shapeIs next ds' hn)
  | _, .draw D _ _ next, _, h => by
    obtain ⟨e, ds', ⟨q⟩, h0, hz, hd, hn⟩ := h
    rw [hd]
    exact List.Forall₂.cons ⟨⟨0, e.drawE, 0⟩, roundIs_draw D.D e.drawE q, h0, rfl, hz⟩
      (Ch.shapeIs next ds' hn)
  | _, .send n D _ _ _ next, _, h => by
    obtain ⟨e, ds', ⟨q⟩, h0, hz, hd, hn⟩ := h
    rw [hd]
    exact List.Forall₂.cons ⟨⟨n, e.drawE, 0⟩, roundIs_send n D.D e.drawE q, h0, rfl, hz⟩
      (Ch.shapeIs next ds' hn)

theorem Ch.shapeIs_R (Ex : ExtSpec) {X : Type} (c : Ch E M X) (ds : List Fmt.Entry) (h : Fit c ds) :
    ShapeIs E (c.R Ex).shape ds := by
  rw [Ch.shape_R]
  exact Ch.shapeIs c ds h

/-- The chain's shape has the three numbers of each entry that a routine of the port's planner
adds, if its entries fit. -/
theorem Ch.planned (Ex : ExtSpec) {X : Type} (c : Ch E M X) (ds : List Fmt.Entry) (h : Fit c ds)
    (s : Setting) (b b' : ℕ) (r : Planning Unit) (hr : Adds s b b' r ds) (p q : PlanState)
    (hp : At s b p) (hq : r p = .ok ((), q)) :
    ∃ l : List PlanRound, q.rounds = p.rounds ++ l.toArray ∧
      ShapeIs E (c.R Ex).shape (l.map (·.entry)) := by
  obtain ⟨_, l, h1, h2⟩ := hr p q hp hq
  exact ⟨l, h1, by rw [h2]; exact Ch.shapeIs_R Ex c ds h⟩

/-! ### The steps of a proof of Fit at a value -/

theorem fit_done (X : Type) : Fit (Ch.done X : Ch E M X) [] := rfl

theorem fit_plain {X : Type} (T : PlainSc E) (x : PscSize) (hx : T.Fits x) (w n : ℕ)
    (F : ∀ st, HFixs (T.our.par.vars st)) (cl : X → (Fin n → E) → E × T.our.par.St)
    (msg : M → T.our.par.J → E) (L : X → (Fin n → E) → M → Prop)
    (Ow : (X × (Fin n → E)) × T.our.par.Out → M → Prop)
    (next : Ch E M ((X × (Fin n → E)) × T.our.par.Out)) (ds : List Fmt.Entry) (h : Fit next ds) :
    Fit (Ch.ride T.our.par n F cl msg L Ow next) (lPsc w (24 * n) x ++ ds) :=
  ⟨w, T.nv, T.deg, T.DY, ds, rfl, by
    rw [lPsc_entries w n x hx.withY, hx.degs, hx.degY, hx.vals]
    rfl, h⟩

theorem fit_bat {X : Type} (w rows err : ℕ) (P : X → M → Prop) (next : Ch E M (X × E))
    (ds : List Fmt.Entry) (h : Fit next ds) :
    Fit (Ch.draw ⟨E⟩ err P next) (eBat w 0 rows :: ds) :=
  ⟨eBat w 0 rows, ds, ⟨(Equiv.funUnique (Fin 1) E).symm⟩, rfl, rfl, rfl, h⟩

theorem fit_zero {X : Type} (w v err : ℕ) (P : X → M → Prop) (next : Ch E M (X × (Fin v → E)))
    (ds : List Fmt.Entry) (h : Fit next ds) :
    Fit (Ch.draw ⟨Fin v → E⟩ err P next) (eDraw "ZERO" w 0 v :: ds) :=
  ⟨eDraw "ZERO" w 0 v, ds, ⟨Equiv.refl _⟩, rfl, rfl, rfl, h⟩

theorem fit_batSend {X : Type} (w n rows err : ℕ) (P : X → M → Prop)
    (L : X → (Fin n → E) → M → Prop) (next : Ch E M ((X × (Fin n → E)) × E))
    (ds : List Fmt.Entry) (h : Fit next ds) :
    Fit (Ch.send n ⟨E⟩ err P L next) (eBat w (24 * n) rows :: ds) :=
  ⟨eBat w (24 * n) rows, ds, ⟨(Equiv.funUnique (Fin 1) E).symm⟩, rfl, rfl, rfl, h⟩

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.Ch.shapeIs
#print axioms OnBytes.Tie.Pv.Att.Ch.shapeIs_R
#print axioms OnBytes.Tie.Pv.Att.Ch.planned
#print axioms OnBytes.Tie.Pv.Att.fit_plain
#print axioms OnBytes.Tie.Pv.Att.fit_bat
#print axioms OnBytes.Tie.Pv.Att.fit_zero
#print axioms OnBytes.Tie.Pv.Att.fit_batSend
