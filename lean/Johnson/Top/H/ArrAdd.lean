-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/ArrAdd.lean: the arrangement before a proximity test's first fold is knowledge sound
into a joint whose form has further weights on the rows that hold no member's row.

Why it is wanted. A test on a group of oracle messages begins with an arrangement without rounds
(`arrOwn`, `arrRide`, Cb/Pv/Tower/First.lean): the members' rows are laid on the corners of a cube;
a corner that holds no member's row holds a zero row. The batched form, carried along
(`GShape.form`, Cb/Ld/LdGroupFold.lean), is 0 on such rows. A verifier program may compute with a
vector that is not: a member with K rows takes a block of a power of two rows, and a sample row has
weights on all rows of the block. The two claims say the same of every message that is 0 on these
rows, but a verifier that evaluates the vector gets other values. So that a typed verifier can
compute with the program's vector, the form behind the arrangement is allowed further weights w
there. Statements and proofs.

The reduction does not turn: the arrangement does not read the form. Only the joint behind it
turns. A step of its own from the form F to F + w need not be knowledge sound, and none is given: a
joint's relaxed relation speaks of a codeword near the word, and does not say that the word is an
arranged one. Behind the arrangement the word is arranged by construction.

Main names:
  `shape_know_add`: for any reshaping ρ (`Reshape`, Cb/Ld/LdBatShape.lean): the step is knowledge
    sound into the joint at the form `ρ.sl s + w`.
  `FreeAt Sh j`: the coordinate j of the fold's input code is in a row that holds no member's row.
  `up_free`: an arranged message is 0 there.
  `arrOwn_know_add`, `arrRide_know_add`: the arrangement of a group, into the first stage's joint at
    `Sh.form Sb sl Z + w`; the second while the fold's mask is handed on.
What is asked, by name: hL, h: the laws of the reshaping (`Reshape.Laws`; `GShape.OK`). hF: a
codeword within e of a new word is of the new shape (`Reshape.Fix`); for a group's arrangement
`ldGroup_shape_laws` (Cb/Ld/LdGroupFoldProofs.lean) gives it if e is below the distances of the two
codes and it holds of the members' changes of shape. hw: w gives 0 on every message of the new
shape; for a group: w is 0 off the free rows. The joints' conditions (`on`) ask nothing: they are
`True` by unfolding.

Limits: hF is shown of no group here. w is a letter: a function of the typed state; that it is any
program's weights is not said here (Johnson/Top/H/RowsJoin.lean). With w := 0 the statements are
those of Cb/Pv/Tower/First.lean under one more premise. Nothing on an honest prover: with w other
than 0 the honest relation is not looked at. Nothing on the stages behind.
Terms: lean/GLOSSARY.md.
-/
import Cb.Pv.Tower.First
import Cb.Ent.TowerKnowProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H.ArrAdd
open Iop IOR Cb Cb.Pv Cb.Pv.Tower

/-! ## A reshaping into a form with added weights -/

section Shape
variable {E P : Type} [Field E] [Fintype E] [Fintype P] [Nonempty P] {C C' : LdCode E P}

/-- The reshaping, as a step without rounds, is knowledge sound into the joint whose form is the
carried form plus w, if a codeword within e of a new word is of the new shape, and w gives 0 on
every message of the new shape. -/
theorem shape_know_add (ρ : Reshape C C') (hL : ρ.Laws) (e : ℕ) (hF : ρ.Fix e) {St : Type}
    (s : Slf E St C.J) (w : Slf E St C'.J) (hw : ∀ st u, ∑ j, w st j * (ρ.up u).1 j = 0) :
    (ldShapeBlock ρ s e).R.red.Know (fun _ => True) (C.rels s e fun _ => ()).relR
      (C'.rels (ρ.sl s + w) e fun _ => ()).relR (fun _ _ w' => ρ.dn w') () := by
  intro a _ b w' hb hw'
  refine ldEnt_shape_know E P C C' ρ St s e hL a trivial b w' hb ?_
  obtain rfl := Option.some.inj hb
  have hfix : ρ.up (ρ.dn w') = w' := hF a.2 w' hw'.1
  have h0 : ∑ j, w a.1.2 j * w'.1 j = 0 := by
    have h := hw a.1.2 (ρ.dn w')
    rwa [hfix] at h
  refine ⟨hw'.1, ?_⟩
  have h2 : ∑ j, (ρ.sl s a.1.2 j + w a.1.2 j) * w'.1 j = a.1.1 := hw'.2
  simp only [add_mul, Finset.sum_add_distrib, h0, add_zero] at h2
  exact h2

end Shape

/-! ## At a group's arrangement -/

section Group
variable {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  (Sh : GShape G) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))

/-- A coordinate of the fold's input code in a row that holds no row of a member. -/
def FreeAt : Sh.Cin.J → Prop
  | .inl x => Sh.am.src (x.1, x.2.1) = none
  | .inr x => Sh.az.src x.1 = none

omit [Fintype E] [Nonempty G.P] in
/-- An arranged message is 0 there. -/
theorem up_free (u : (G.C.J → E) × (G.C.Q → E)) (j : Sh.Cin.J) (hj : FreeAt Sh j) :
    (Sh.rho.up u).1 j = 0 := by
  rcases j with x | x
  · have hs : Sh.am.src (x.1, x.2.1) = none := hj
    show Sh.am.spread _ ((x.1, x.2.1), x.2.2) = 0
    simp only [Arr.spread, hs]
  · have hs : Sh.az.src x.1 = none := hj
    show Sh.az.spread _ (x.1, x.2) = 0
    simp only [Arr.spread, hs]

variable (w : Slf E (BSt Sb Z) Sh.Cin.J)

/-- **The arrangement is knowledge sound into the first stage's joint at the batched form plus
weights on the free rows.** The reduction is the arrangement's own. -/
theorem arrOwn_know_add (h : Sh.OK) (hF : Sh.rho.Fix G.e)
    (hw : ∀ st j, ¬ FreeAt Sh j → w st j = 0) :
    (arrOwn Sh Sb sl Z).red.Know (firstInOwn Sb sl Z).on (firstInOwn Sb sl Z).relR
      (stageInOwn Sh.par (Sh.form Sb sl Z + w) G.e).relR (fun _ _ w' => Sh.rho.dn w') () :=
  shape_know_add Sh.rho (ldGroup_shape_laws E S G Sh h).1 G.e hF (Slf.bat Z.ze (G.rows sl)) w
    fun st u => Finset.sum_eq_zero fun j _ => by
      by_cases hj : FreeAt Sh j
      · rw [up_free Sh u j hj, mul_zero]
      · rw [hw st j hj, zero_mul]

/-- The same while the fold's mask is handed on. -/
theorem arrRide_know_add (h : Sh.OK) (hF : Sh.rho.Fix G.e)
    (hw : ∀ st j, ¬ FreeAt Sh j → w st j = 0) :
    (arrRide Sh Sb sl Z).red.Know (firstInRide Sh Sb sl Z).on (firstInRide Sh Sb sl Z).relR
      (stageInRide Sh.par (Sh.form Sb sl Z + w) G.e).relR (fun _ _ w' => Sh.rho.dn w') () :=
  know_keepE Sh.par.Cw.nat (arrOwn Sh Sb sl Z) (firstInOwn Sb sl Z)
    (stageInOwn Sh.par (Sh.form Sb sl Z + w) G.e) (fun _ _ w' => Sh.rho.dn w') ()
    (arrOwn_know_add Sh Sb sl Z w h hF hw)

end Group

end Johnson.Top.H.ArrAdd
