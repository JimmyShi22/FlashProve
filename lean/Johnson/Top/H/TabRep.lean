-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/TabRep.lean: a table of rows under a repeated code, on a tree that may be shorter
than the positions at which a group is read, is the group's table with as many rows: the word is
repeated.

In a tree of the programs every leaf holds a copy of the mask rows' symbols, and a verifier reads
the leaf's own copy. So a word of mask rows has a symbol at each position of its tree (`ldRep`,
OnBytes/Slice/LinkAt.lean). A whole tree that is shorter than the list of positions of a test is
opened at the position modulo its length (`modP`, Johnson/Pack/Group.lean). This file has the
change of shape (`Reshape`, Cb/Ld/LdBatShape.lean) from such a table, read modulo, to the table on
the group's positions. Definitions, statements and proofs.
Main names:
  `posIn_modP`: the position modulo a tree's length agrees with the position modulo the length of
    every code that is not longer than the tree.
  `modP_up`: every position of the shorter tree is the position modulo its length of some position
    of the group.
  `tabRep Z a a' n`: the change of shape: the new word's symbol at x is the old word's at x modulo
    2^a'; messages, tails and forms stay.
  `tabRep_T`: the two long words are one.
  `tabRep_laws`: its laws, if the code is not longer than the tree and the tree not longer than
    the group's positions.
  `tabVoid`, `tabVoid_laws`: a table without a row, under any two codes.
Limits: nothing on a radius: that a joint radius implies the shorter tree's own is in
Johnson/Pack/Group.lean. That a program's tree is read so is not shown here.

-/
import Cb.Ld.LdBatShape
import Johnson.Pack.Group

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes.Slice Cb Johnson.Pack

theorem posIn_modP (C : Fmt.M1.Code) (a a' : ℕ) (h : C.a ≤ a') (x : Fin (2 ^ a)) :
    posIn C (modP a' a x) = posIn C x :=
  Fin.ext (Nat.mod_mod_of_dvd x.val (pow_dvd_pow 2 h))

theorem modP_up (a a' : ℕ) (h : a' ≤ a) (p : Fin (2 ^ a')) :
    modP a' a ⟨p.val, lt_of_lt_of_le p.isLt (Nat.pow_le_pow_right (by norm_num) h)⟩ = p :=
  Fin.ext (Nat.mod_eq_of_lt p.isLt)

section
variable (Z : Fmt.M1.Code) (a a' n : ℕ)

/-- The word on the shorter tree, repeated to the group's positions. -/
def tabRep :
    Reshape (((ldRep Z a').il (Fin n)).atPos (modP a' a)) ((ldRep Z a).il (Fin n)) where
  wd := fun f x s => f (modP a' a x) s
  up := fun w => w
  dn := fun w => w
  fm := fun c => c

/-- The two long words are one. -/
theorem tabRep_T (f : (((ldRep Z a').il (Fin n)).atPos (modP a' a)).Word) (x : Fin (2 ^ a)) :
    ((ldRep Z a).il (Fin n)).T ((tabRep Z a a' n).wd f) x =
      (((ldRep Z a').il (Fin n)).atPos (modP a' a)).T f x := by
  funext α
  show f (modP a' a x) (α.1, ()) = f (modP a' a x) (α.1, ())
  rfl

/-- The new word of an encoding is the encoding. -/
theorem tabRep_enc (h : Z.a ≤ a')
    (w : ((((ldRep Z a').il (Fin n)).atPos (modP a' a)).J → GE) ×
      ((((ldRep Z a').il (Fin n)).atPos (modP a' a)).Q → GE)) :
    (tabRep Z a a' n).wd ((((ldRep Z a').il (Fin n)).atPos (modP a' a)).enc w.1 w.2) =
      ((ldRep Z a).il (Fin n)).enc w.1 w.2 := by
  funext x s
  show (ldRep Z a').enc (fun j => w.1 (s.1, j)) (fun q => w.2 (s.1, q)) (modP a' a x) s.2 =
    (ldRep Z a).enc (fun j => w.1 (s.1, j)) (fun q => w.2 (s.1, q)) x s.2
  rw [ldRep_enc, ldRep_enc, posIn_modP Z a a' h x]
  exact ()

theorem tabRep_laws (h : Z.a ≤ a') (h' : a' ≤ a) : (tabRep Z a a' n).Laws where
  loc := fun f g x k => (tabRep_T Z a a' n f x).trans (k.trans (tabRep_T Z a a' n g x).symm)
  enc := fun w => tabRep_enc Z a a' n h w
  off := fun f w' x k =>
    (tabRep_T Z a a' n f x).symm.trans (k.trans
      ((congrArg (fun g => ((ldRep Z a).il (Fin n)).T g x) (tabRep_enc Z a a' n h w').symm).trans
        (tabRep_T Z a a' n _ x)))
  inj := fun _ => rfl
  winj := fun f g k => by
    funext p s
    have e := congrFun (congrFun k
      ⟨p.val, lt_of_lt_of_le p.isLt (Nat.pow_le_pow_right (by norm_num) h')⟩) s
    have e' : f (modP a' a ⟨p.val, lt_of_lt_of_le p.isLt
        (Nat.pow_le_pow_right (by norm_num) h')⟩) s =
      g (modP a' a ⟨p.val, lt_of_lt_of_le p.isLt
        (Nat.pow_le_pow_right (by norm_num) h')⟩) s := e
    rw [modP_up a a' h' p] at e'
    exact e'
  val := fun _ _ => rfl

end

/-! ### a table without a row -/

section
variable {P P' : Type} (A : LdCode GE P') (D : LdCode GE P) (pos : P → P') (n : ℕ)

/-- A table without a row, under any two codes: there is nothing to move. -/
def tabVoid (h0 : n = 0) : Reshape ((A.il (Fin n)).atPos pos) (D.il (Fin n)) where
  wd := fun _ _ s => absurd s.1.isLt (by omega)
  up := fun _ => (fun j => absurd j.1.isLt (by omega), fun q => absurd q.1.isLt (by omega))
  dn := fun _ => (fun j => absurd j.1.isLt (by omega), fun q => absurd q.1.isLt (by omega))
  fm := fun _ j => absurd j.1.isLt (by omega)

theorem tabVoid_laws (h0 : n = 0) : (tabVoid A D pos n h0).Laws where
  loc := fun _ _ _ _ => funext fun α => absurd α.1.isLt (by omega)
  enc := fun _ => funext fun _ => funext fun s => absurd s.1.isLt (by omega)
  off := fun _ _ _ _ => funext fun α => absurd α.1.isLt (by omega)
  inj := fun _ => Prod.ext (funext fun j => absurd j.1.isLt (by omega))
    (funext fun q => absurd q.1.isLt (by omega))
  winj := fun _ _ _ => funext fun _ => funext fun s => absurd s.1.isLt (by omega)
  val := fun _ _ => by
    subst h0
    simp

end

end Johnson.Top.H

#print axioms Johnson.Top.H.tabRep_T
#print axioms Johnson.Top.H.tabRep_enc
#print axioms Johnson.Top.H.tabRep_laws
#print axioms Johnson.Top.H.tabVoid_laws
