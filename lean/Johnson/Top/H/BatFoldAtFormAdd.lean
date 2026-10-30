-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/BatFoldAtFormAdd.lean: callers of the kind "the round before a proximity test, then
its first fold, at a form F" (Johnson/Top/H/BatFoldAtForm.lean) whose form is the arranged form with
further weights on the rows that hold no member's row; and what the kind's clause on the
arrangement says of such weights.

The arrangement lays the members' rows on the corners of a cube. A corner that holds no member's row
holds a zero row, and the arranged form is 0 there. Johnson/Top/H/ArrAdd.lean shows that the
arrangement is knowledge sound into the joint at the arranged form plus w, under the shape's laws,
if w is 0 off these rows and a codeword near an arranged word is arranged. Here that is spent at a
caller. Definitions, statements and proofs.
Main names:
  `place_free`, `fm_free`, `form_free`: the arranged form is 0 on a free row.
  `free_bat`: weights that are batched row by row, each row's from that row's own state, are 0 off
    the free rows if each row's are.
  `BatFoldCaller.plus c w`: the caller of Johnson/Top/H/BatFold.lean, at the arranged form plus w.
    `plus_zero`: with w := 0 it is the caller at the arranged form.
  `BatFoldOKAt.plus`: its conditions hold, if those of Johnson/Top/H/BatFold.lean do, a codeword
    within the joint radius of an arranged word is arranged (`Reshape.Fix`), and w is 0 off the free
    rows.
  `shape_add_only`, `arrRideInto_add_only`: the other way, under the shape's laws: if the
    arrangement is knowledge sound into the joint at the arranged form plus w, then w gives 0 on
    every arranged message. So the clause is a condition on F: it ties the field F to the caller's
    rows.
  `arrRideInto_add_iff`: under the shape's laws and `Reshape.Fix` the two are equivalent.
Limits: w is a letter: a function of the typed state; that it is any program's weights is not said
here. `Reshape.Fix` is shown of no group here. Nothing on an honest prover.

-/
import Johnson.Top.H.ArrAdd
import Johnson.Top.H.BatFoldAtForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop Cb IOR Cb.Pv Cb.Pv.Tower Johnson.Top.H.ArrAdd

/-! ### the free rows -/

/-- An arrangement lays the coefficient 0 on a row that holds nothing. -/
theorem place_free {R R' X E : Type} [Zero E] [DecidableEq R'] (a : Arr R R') (c : R × X → E)
    (n : R' × X) (h : a.src n.1 = none) : a.place c n = 0 := by
  simp only [Arr.place, h]

section Group
variable {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  (Sh : GShape G) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))

omit [Fintype E] [Nonempty G.P] in
/-- The carried form of any form is 0 on a free row. -/
theorem fm_free (a : G.C.J → E) (j : Sh.Cin.J) (hj : FreeAt Sh j) : Sh.rho.fm a j = 0 := by
  rcases j with ⟨b, o, x⟩ | ⟨b, x⟩
  · exact place_free Sh.am (fun j => Sh.flat.fm a (Sum.inl j)) ((b, o), x) hj
  · exact place_free Sh.az (fun j => Sh.flat.fm a (Sum.inr j)) (b, x) hj

omit [Fintype E] [Nonempty G.P] in
/-- The arranged form is 0 on a free row. -/
theorem form_free (st : BSt Sb Z) (j : Sh.Cin.J) (hj : FreeAt Sh j) :
    Sh.form Sb sl Z st j = 0 :=
  fm_free Sh _ j hj

omit [Fintype E] [Nonempty G.P] in
/-- Weights batched row by row are 0 off the free rows if each row's are. -/
theorem free_bat (fr : ∀ ν, Slf E (G.RowSt Sb ν) Sh.Cin.J)
    (h : ∀ ν x j, ¬ FreeAt Sh j → fr ν x j = 0) (st : BSt Sb Z) (j : Sh.Cin.J)
    (hj : ¬ FreeAt Sh j) : Slf.bat Z.ze fr st j = 0 :=
  Finset.sum_eq_zero fun ν _ => by rw [h ν _ j hj, zero_mul]

end Group

/-! ### what the clause says of added weights -/

section Shape
variable {E P : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P] {C C' : LdCode E P}

/-- Under the reshaping's laws: if it is knowledge sound into the joint at the carried form plus w,
then w gives 0 on every message of the new shape. -/
theorem shape_add_only (ρ : Reshape C C') (hL : ρ.Laws) (e : ℕ) {St : Type} (s : Slf E St C.J)
    (w : Slf E St C'.J)
    (hK : (ldShapeBlock ρ s e).R.red.Know (fun _ => True) (C.rels s e fun _ => ()).relR
      (C'.rels (ρ.sl s + w) e fun _ => ()).relR (fun _ _ w' => ρ.dn w') ()) (st : St)
    (u : (C.J → E) × (C.Q → E)) : ∑ j, w st j * (ρ.up u).1 j = 0 := by
  have hn : C'.Near e (ρ.wd (C.enc u.1 u.2)) (C'.enc (ρ.up u).1 (ρ.up u).2) := by
    rw [hL.enc u]
    exact (Nat.le_of_eq (cnt_false fun _ h => h rfl)).trans (Nat.zero_le e)
  have h := hK ((∑ j, (ρ.sl s st j + w st j) * (ρ.up u).1 j, st), C.enc u.1 u.2) trivial _
    (ρ.up u) rfl ⟨hn, rfl⟩
  have h2 : ∑ j, s st j * (ρ.dn (ρ.up u)).1 j = ∑ j, (ρ.sl s st j + w st j) * (ρ.up u).1 j := h.2
  have h3 : ∑ j, ρ.sl s st j * (ρ.up u).1 j = ∑ j, s st j * (ρ.dn (ρ.up u)).1 j :=
    hL.val (s st) (ρ.up u)
  simp only [add_mul, Finset.sum_add_distrib] at h2
  rw [h3] at h2
  exact (left_eq_add.1 h2)

end Shape

section Group
variable {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  (Sh : GShape G) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))
  (w : Slf E (BSt Sb Z) Sh.Cin.J)

/-- The same at a group's arrangement, under the shape's laws. -/
theorem arrRideInto_add_only (h : Sh.OK) (hA : ArrRideInto Sh Sb sl Z (Sh.form Sb sl Z + w))
    (st : BSt Sb Z) (u : (G.C.J → E) × (G.C.Q → E)) : ∑ j, w st j * (Sh.rho.up u).1 j = 0 :=
  shape_add_only Sh.rho (ldGroup_shape_laws E S G Sh h).1 G.e (Slf.bat Z.ze (G.rows sl)) w
    (arrOwnInto_of_ride Sh Sb sl Z _ hA) st u

/-- Under the shape's laws, and if a codeword within the joint radius of an arranged word is
arranged: the clause at the arranged form plus w says that w gives 0 on every arranged message. -/
theorem arrRideInto_add_iff (h : Sh.OK) (hF : Sh.rho.Fix G.e) :
    ArrRideInto Sh Sb sl Z (Sh.form Sb sl Z + w) ↔
      ∀ st u, ∑ j, w st j * (Sh.rho.up u).1 j = 0 :=
  ⟨arrRideInto_add_only Sh Sb sl Z w h, fun hw =>
    arrRideInto_of_own Sh Sb sl Z _
      (shape_know_add Sh.rho (ldGroup_shape_laws E S G Sh h).1 G.e hF (Slf.bat Z.ze (G.rows sl)) w
        hw)⟩

end Group

/-! ### the callers -/

section Caller
variable {E : Type} [Field E] [Fintype E] (c : BatFoldCaller E)
  (w : Slf E (BSt c.s.Sb c.s.Z) c.Sh.Cin.J)

/-- A caller of Johnson/Top/H/BatFold.lean, at the arranged form plus w. -/
noncomputable def BatFoldCaller.plus : BatFoldCallerAt E :=
  c.atForm (c.Sh.form c.s.Sb c.s.sl c.s.Z + w)

/-- With no weights it is the caller at the arranged form. -/
theorem BatFoldCaller.plus_zero : c.plus 0 = c.toAt :=
  congrArg c.atForm (add_zero (c.Sh.form c.s.Sb c.s.sl c.s.Z))

/-- With the form forgotten it is the caller. -/
theorem BatFoldCaller.forget_plus : (c.plus w).forget = c := rfl

variable {c w}

/-- Its conditions hold if those of Johnson/Top/H/BatFold.lean do, a codeword within the joint
radius of an arranged word is arranged, and w is 0 off the free rows. -/
theorem BatFoldOKAt.plus (h : BatFoldOKAt c) (hF : c.Sh.rho.Fix c.s.G.e)
    (hw : ∀ st j, ¬ FreeAt c.Sh j → w st j = 0) : (c.plus w).OK where
  z := h.z
  list := h.list
  fits := h.fits
  shape := h.shape
  into := arrRide_know_add c.Sh c.s.Sb c.s.sl c.s.Z w h.shape hF hw
  fold := hypK_reform c.Sh.par _ _ h.fold

end Caller

end VerifiableInference.OnPublicFiles
