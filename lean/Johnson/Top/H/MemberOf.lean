-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/MemberOf.lean: a member of a group of sent oracle messages from a shape of the
programs, and the group's data from the set of members and what is held of each.

A message of the programs has main rows under one code and mask rows under a second (`portCode`,
Johnson/Pack/Port.lean). A word of mask rows has a symbol at each position of the message's tree.
In a group the message is read at the position modulo its tree's length. Each of its two tables
either stands under the code that the test's first stage has for that table, or has no row. A
table of main rows under the stage's code does not move. A table of mask rows under the stage's
code is repeated to the stage's positions (Johnson/Top/H/TabRep.lean). Of a table without a row
there is nothing to move. Definitions, statements and proofs.
Main names:
  `tabSame`, `tabSame_laws`: a table of main rows under the stage's code, read at positions that
    agree modulo the code's length.
  `tabNone`, `tabNone_laws`: a table of main rows without a row, under any code.
  `maskSame`, `maskSame_laws`: a table of mask rows under the stage's code.
  `MembAt o s`: what the group's data hold of a member o: its numbers of rows, the first corners
    of its blocks, where it is read, its change of shape.
  `Rows.ofFn s e mem mb`: the group's data (`Rows`, Johnson/Top/H/GroupRows.lean) from the set of
    members and a function mb that gives `MembAt` for each member.
  `modP_at`: the position modulo a message's length (`modP`, Johnson/Pack/Group.lean) agrees with
    the position modulo the length of every code that is not longer.
  `pairAt`, `pairAt_laws`: a pair of codes read at other positions is the pair of the two codes
    read there.
  `membPort`, `membPort_laws`, `membPort_fits`: the member of a shape of the programs; its change
    of shape has the laws if the tree is not longer than the stage's positions; the joint radius
    implies its own, from an inequality on numbers (`MembAt.Fits`, `Rows.ofFn_fits`).
  `ofFn_G_eq`: at one sending the group is that of Johnson/Pack/Group.lean.
  `apart_inj`: rows have different corners if the members' blocks do not overlap.
Limits: that a shape's tables stand under the stage's codes is a premise of `membPort`. That the
first corners are those of the programs' layout is not shown.

-/
import Johnson.Pack.Group
import Johnson.Top.H.TabRep
import Johnson.Top.H.GroupRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes.Slice Cb Johnson.Pack

section Tables
variable (C C' : Fmt.M1.Code) (a a' n : ℕ) (pos : Fin (2 ^ a) → Fin (2 ^ a'))

/-- A table under the stage's code: nothing moves. -/
def tabSame (e : C' = C) :
    Reshape (((ldOf C' a').il (Fin n)).atPos pos) ((ldOf C a).il (Fin n)) := by
  subst e
  exact ⟨fun f => f, fun w => w, fun w => w, fun c => c⟩

theorem tabSame_laws (e : C' = C) (h : ∀ x, posIn C (pos x) = posIn C x) :
    (tabSame C C' a a' n pos e).Laws := by
  subst e
  have hT : ∀ (f : ((ldOf C' a).il (Fin n)).Word) x,
      (((ldOf C' a').il (Fin n)).atPos pos).T f x = ((ldOf C' a).il (Fin n)).T f x := by
    intro f x
    funext α
    show f (posIn C' (pos x)) (α.1, ()) = f (posIn C' x) (α.1, ())
    rw [h]
  exact
    { loc := fun f g x k => by
        show ((ldOf C' a).il (Fin n)).T f x = ((ldOf C' a).il (Fin n)).T g x
        rw [← hT f x, ← hT g x]
        exact k
      enc := fun _ => rfl
      off := fun f w' x k => by
        rw [hT f x, hT _ x]
        exact k
      inj := fun _ => rfl
      winj := fun _ _ k => k
      val := fun _ _ => rfl }

/-- A table without a row: there is nothing to move. -/
def tabNone (h0 : n = 0) :
    Reshape (((ldOf C' a').il (Fin n)).atPos pos) ((ldOf C a).il (Fin n)) where
  wd := fun _ _ s => absurd s.1.isLt (by omega)
  up := fun _ => (fun j => absurd j.1.isLt (by omega), fun q => absurd q.1.isLt (by omega))
  dn := fun _ => (fun j => absurd j.1.isLt (by omega), fun q => absurd q.1.isLt (by omega))
  fm := fun _ j => absurd j.1.isLt (by omega)

theorem tabNone_laws (h0 : n = 0) : (tabNone C C' a a' n pos h0).Laws where
  loc := fun _ _ _ _ => funext fun α => absurd α.1.isLt (by omega)
  enc := fun _ => funext fun _ => funext fun s => absurd s.1.isLt (by omega)
  off := fun _ _ _ _ => funext fun α => absurd α.1.isLt (by omega)
  inj := fun _ => Prod.ext (funext fun j => absurd j.1.isLt (by omega))
    (funext fun q => absurd q.1.isLt (by omega))
  winj := fun _ _ _ => funext fun _ => funext fun s => absurd s.1.isLt (by omega)
  val := fun _ _ => by
    subst h0
    simp

/-- A table of mask rows under the stage's mask code, on a tree of 2^a' leaves: the word is repeated
to the stage's positions. -/
def maskSame (e : C' = C) :
    Reshape (((ldRep C' a').il (Fin n)).atPos (modP a' a)) ((ldRep C a).il (Fin n)) := by
  subst e
  exact tabRep C' a a' n

theorem maskSame_laws (e : C' = C) (h : C.a ≤ a') (h' : a' ≤ a) :
    (maskSame C C' a a' n e).Laws := by
  subst e
  exact tabRep_laws C' a a' n h h'

end Tables

/-- What the group's data hold of a member. -/
structure MembAt (o : OMsg GE) (s : Sg) where
  nM : ℕ
  nZ : ℕ
  oM : ℕ
  oZ : ℕ
  pos : s.Ps → o.P
  view : Reshape (o.C.atPos pos) ((s.cM.il (Fin nM)).pair (s.cZ.il (Fin nZ)))

/-- The group's data from the set of members and what is held of each member. -/
def Rows.ofFn {S : Sig GE} (s : Sg) (e : ℕ) (mem : S.O → Prop) [DecidablePred mem]
    (mb : ∀ o, mem o → MembAt (S.om o) s) : Rows S where
  s := s
  e := e
  mem := mem
  pos := fun a => (mb a.1 a.2).pos
  nM := fun a => (mb a.1 a.2).nM
  nZ := fun a => (mb a.1 a.2).nZ
  oM := fun a => (mb a.1 a.2).oM
  oZ := fun a => (mb a.1 a.2).oZ
  view := fun a => (mb a.1 a.2).view

/-- The joint radius e implies the member's own. -/
def MembAt.Fits {o : OMsg GE} {s : Sg} (m : MembAt o s) (e : ℕ) : Prop :=
  ∀ f g, (o.C.atPos m.pos).Near e f g → o.C.Near o.e f g

theorem Rows.ofFn_fits {S : Sig GE} (s : Sg) (e : ℕ) (mem : S.O → Prop) [DecidablePred mem]
    (mb : ∀ o, mem o → MembAt (S.om o) s) (h : ∀ o k, (mb o k).Fits e) :
    (Rows.ofFn s e mem mb).G.Fits := fun a f g hn => h a.1 a.2 f g hn

/-- The position modulo a message's length agrees with the position modulo the length of every code
that is not longer. -/
theorem modP_at (C : Fmt.M1.Code) (a a' : ℕ) (h : C.a ≤ a') (x : Fin (2 ^ a)) :
    posIn C (modP a' a x) = posIn C x :=
  Fin.ext (Nat.mod_mod_of_dvd x.val (pow_dvd_pow 2 h))

section PairAt
variable {P P' : Type} (A B : LdCode GE P') (pos : P → P')

/-- A pair read at other positions, and the pair of the two codes read there: nothing moves. -/
def pairAt : Reshape ((A.pair B).atPos pos) ((A.atPos pos).pair (B.atPos pos)) :=
  ⟨fun f => f, fun w => w, fun w => w, fun c => c⟩

theorem pairAt_laws : (pairAt A B pos).Laws := by
  have hT : ∀ (f : (A.pair B).Word) x,
      ((A.pair B).atPos pos).T f x = ((A.atPos pos).pair (B.atPos pos)).T f x := by
    intro f x
    funext α
    rcases α with α | α <;> rfl
  have hE : ∀ m r, ((A.pair B).atPos pos).enc m r = ((A.atPos pos).pair (B.atPos pos)).enc m r := by
    intro m r
    funext p
    rcases p with p | p <;> rfl
  exact
    { loc := fun f g x h => (hT f x).symm.trans (h.trans (hT g x))
      enc := fun w => hE w.1 w.2
      off := fun f w' x h => (hT f x).trans (h.trans
        ((congrArg (fun g => ((A.atPos pos).pair (B.atPos pos)).T g x) (hE w'.1 w'.2).symm).trans
          (hT _ x).symm))
      inj := fun _ => rfl
      winj := fun _ _ h => h
      val := fun _ _ => rfl }

end PairAt

section Port
variable (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) (em : ℕ) (s : Sg) (oM oZ : ℕ)
  (hM : sh.mainRows ≠ 0 → cMain cs sh = s.C) (hZ : sh.maskRows ≠ 0 → cMask cs sh = s.Z)

/-- The main table of a shape as read in the group. -/
def mainAt :
    Reshape (((ldOf (cMain cs sh) (aOf cs sh)).il (Fin sh.mainRows)).atPos
      (modP (aOf cs sh) s.C.a)) (s.cM.il (Fin sh.mainRows)) :=
  if h0 : sh.mainRows = 0 then tabNone _ _ _ _ _ _ h0 else tabSame _ _ _ _ _ _ (hM h0)

/-- The mask table of a shape as read in the group. -/
def maskAt :
    Reshape (((ldRep (cMask cs sh) (aOf cs sh)).il (Fin sh.maskRows)).atPos
      (modP (aOf cs sh) s.C.a)) (s.cZ.il (Fin sh.maskRows)) :=
  if h0 : sh.maskRows = 0 then tabVoid _ _ _ _ h0 else maskSame _ _ _ _ _ (hZ h0)

theorem mainAt_laws : (mainAt cs sh s hM).Laws := by
  unfold mainAt
  split
  · exact tabNone_laws _ _ _ _ _ _ _
  · next h0 =>
    exact tabSame_laws _ _ _ _ _ _ _ fun x =>
      modP_at s.C _ _ (by rw [← hM h0]; exact le_max_left _ _) x

theorem maskAt_laws (hA : aOf cs sh ≤ s.C.a) : (maskAt cs sh s hZ).Laws := by
  unfold maskAt
  split
  · exact tabVoid_laws _ _ _ _ _
  · next h0 =>
    exact maskSame_laws _ _ _ _ _ _ (by rw [← hZ h0]; exact le_max_right _ _) hA

/-- The member of a shape of the programs. -/
noncomputable def membPort : MembAt (portOmZ cs sh em) s where
  nM := sh.mainRows
  nZ := sh.maskRows
  oM := oM
  oZ := oZ
  pos := modP (aOf cs sh) s.C.a
  view := by
    show Reshape ((((ldOf (cMain cs sh) (aOf cs sh)).il (Fin sh.mainRows)).pair
      ((ldRep (cMask cs sh) (aOf cs sh)).il (Fin sh.maskRows))).atPos (modP (aOf cs sh) s.C.a)) _
    exact (((maskAt cs sh s hZ).pairR (s.cM.il (Fin sh.mainRows))).comp
      ((mainAt cs sh s hM).pairL
        (((ldRep (cMask cs sh) (aOf cs sh)).il (Fin sh.maskRows)).atPos
          (modP (aOf cs sh) s.C.a)))).comp (pairAt _ _ _)

theorem membPort_laws (hA : aOf cs sh ≤ s.C.a) : (membPort cs sh em s oM oZ hM hZ).view.Laws :=
  (ldShape_comp GE s.Ps _ _ _ _ _ (pairAt_laws _ _ _)
    (ldShape_comp GE s.Ps _ _ _ _ _
      (ldShape_pairL GE s.Ps _ _ _ _ (mainAt_laws cs sh s hM)).1
      (ldShape_pairR GE s.Ps _ _ _ _ (maskAt_laws cs sh s hZ hA)).1).1).1

/-- The joint radius implies the member's own, from an inequality on numbers. -/
theorem membPort_fits (e : ℕ) (hA : aOf cs sh ≤ s.C.a)
    (he : e ≤ 2 ^ (s.C.a - aOf cs sh) * em + (2 ^ (s.C.a - aOf cs sh) - 1)) :
    (membPort cs sh em s oM oZ hM hZ).Fits e := fun f g hn =>
  Cb.Gl.Bld.bld_near_atPos _ _ (portCode cs sh) (modP (aOf cs sh) s.C.a) _ em
    (Nat.two_pow_pos _) (cnt_modP _ _ hA) f g (le_trans hn he)

end Port

/-- At one sending the group is that of Johnson/Pack/Group.lean. -/
theorem ofFn_G_eq (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
    (mem : Fin l.length → Prop) [DecidablePred mem] (s : Sg) (e : ℕ) (oM oZ : Fin l.length → ℕ)
    (hM : ∀ i, mem i → (l.get i).1.mainRows ≠ 0 → cMain cs (l.get i).1 = s.C)
    (hZ : ∀ i, mem i → (l.get i).1.maskRows ≠ 0 → cMask cs (l.get i).1 = s.Z) :
    (Rows.ofFn (S := sigOf cs l) s e mem fun i k =>
      membPort cs (l.get i).1 (l.get i).2 s (oM i) (oZ i) (hM i k) (hZ i k)).G =
      grpOf cs l mem s.C.a e := rfl

/-- Rows have different corners if the members' blocks do not overlap. -/
theorem apart_inj {A : Type} (n o : A → ℕ)
    (h : ∀ a b, a ≠ b → o a + n a ≤ o b ∨ o b + n b ≤ o a) :
    Function.Injective fun r : Σ a, Fin (n a) => o r.1 + r.2.val := by
  rintro ⟨a, i⟩ ⟨b, j⟩ k
  have k' : o a + i.val = o b + j.val := k
  by_cases e : a = b
  · subst e
    have : i = j := Fin.ext (by omega)
    rw [this]
  · have hi := i.isLt
    have hj := j.isLt
    rcases h a b e with g | g <;> omega

end Johnson.Top.H

#print axioms Johnson.Top.H.tabSame_laws
#print axioms Johnson.Top.H.tabNone_laws
#print axioms Johnson.Top.H.maskSame_laws
#print axioms Johnson.Top.H.membPort_laws
#print axioms Johnson.Top.H.apart_inj
