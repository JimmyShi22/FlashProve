-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/MemberHeld.lean: the way back from the main rows of a member of a group of sent
oracle messages, for a shape of the programs that has main rows and no mask row.

A kept message of the programs has main rows alone (`reqMessageOk`, OnBytes/Iop/Req.lean). As a
member of a group (`membPort`, Johnson/Top/H/MemberOf.lean) its main table stands under the code
of the stage's main rows and does not move, and its mask table has no row. So its native word is
its main rows beside an empty table, and an entry of its message is where it was. Definitions,
statements and proofs.
Main names:
  `undoTab`, `undoTab_laws`: a table of main rows under the stage's code, beside a code B without
    a symbol and without an entry: the record `Undo` (Johnson/Top/H/GroupRowsHeld.lean), and its
    laws at "the main table does not move (`tabSame`); any change of shape of B", if the member is
    read at positions that agree modulo the code's length.
  `undoPort`, `undoPort_laws`: the same at `membPort`, for a shape with mainRows other than 0 and
    maskRows = 0.
Limits: a shape with a mask row has no such record here, and can have none with the laws: they ask
that every entry has a place in a main row. That a kept message of the programs has such a shape
is read off the text named above and not proved. The laws here do not ask that the member's tree
is not longer than the stage's positions; the laws of the change of shape itself
(`membPort_laws`) do.

-/
import Johnson.Top.H.MemberOf
import Johnson.Top.H.GroupRowsHeld

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes.Slice Cb Johnson.Pack

section Tab
variable (C C' : Fmt.M1.Code) (a a' n : ℕ) (B : LdCode GE (Fin (2 ^ a')))
  (hS : ∀ p, IsEmpty (B.NS p)) (hJ : IsEmpty B.J) (hQ : IsEmpty B.Q)

/-- A table under the stage's code beside a code without a symbol: the word is the table. -/
def undoTab (e : C' = C) :
    Undo (((ldOf C' a').il (Fin n)).pair B) ((ldOf C a).il (Fin n)) := by
  subst e
  exact ⟨fun f => LdCode.mkW (C₁ := (ldOf C' a').il (Fin n)) (C₂ := B) f fun p s => (hS p).elim s,
    Sum.elim id fun j => hJ.elim j, Sum.elim id fun q => hQ.elim q⟩

/-- Its laws, whatever the change of shape of the code without a symbol is. -/
theorem undoTab_laws (e : C' = C) (pos : Fin (2 ^ a) → Fin (2 ^ a'))
    (h : ∀ x, posIn C (pos x) = posIn C x) {Z : LdCode GE (Fin (2 ^ a))}
    (z : Reshape (B.atPos pos) Z) :
    (undoTab C C' a a' n B hS hJ hQ e).Laws pos
      (((z.pairR ((ldOf C a).il (Fin n))).comp
        ((tabSame C C' a a' n pos e).pairL (B.atPos pos))).comp
          (pairAt ((ldOf C' a').il (Fin n)) B pos)) := by
  subst e
  exact
    { word := fun f => by
        funext p
        rcases p with p | p
        · rfl
        · funext s
          exact (hS p).elim s
      upJ := fun w j => by
        rcases j with j | j
        · rfl
        · exact hJ.elim j
      upQ := fun w q => by
        rcases q with q | q
        · rfl
        · exact hQ.elim q
      enc := fun m r => by
        funext p
        rcases p with p | p
        · rfl
        · funext s
          exact (hS p).elim s
      loc := fun f g x k => by
        funext α
        rcases α with α | α
        · show f (posIn C' (pos x)) (α.1, ()) = g (posIn C' (pos x)) (α.1, ())
          rw [h x]
          exact congrFun k α
        · rfl }

end Tab

section Port
variable (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) (em : ℕ) (s : Sg) (oM oZ : ℕ)
  (hM : sh.mainRows ≠ 0 → cMain cs sh = s.C) (hZ : sh.maskRows ≠ 0 → cMask cs sh = s.Z)

/-- The way back for a shape of the programs without a mask row. -/
def undoPort (e : cMain cs sh = s.C) (h0 : sh.maskRows = 0) :
    Undo (portCode cs sh) (s.cM.il (Fin sh.mainRows)) :=
  undoTab s.C (cMain cs sh) s.C.a (aOf cs sh) sh.mainRows
    ((ldRep (cMask cs sh) (aOf cs sh)).il (Fin sh.maskRows))
    (fun _ => ⟨fun x => absurd x.1.isLt (by omega)⟩) ⟨fun x => absurd x.1.isLt (by omega)⟩
    ⟨fun x => absurd x.1.isLt (by omega)⟩ e

/-- Its laws at the member of the shape. -/
theorem undoPort_laws (h1 : sh.mainRows ≠ 0) (h0 : sh.maskRows = 0) :
    (undoPort cs sh s (hM h1) h0).Laws (membPort cs sh em s oM oZ hM hZ).pos
      (membPort cs sh em s oM oZ hM hZ).view := by
  have e : mainAt cs sh s hM = tabSame _ _ _ _ _ _ (hM h1) := dif_neg h1
  show (undoPort cs sh s (hM h1) h0).Laws (modP (aOf cs sh) s.C.a)
    ((((maskAt cs sh s hZ).pairR (s.cM.il (Fin sh.mainRows))).comp
      ((mainAt cs sh s hM).pairL
        (((ldRep (cMask cs sh) (aOf cs sh)).il (Fin sh.maskRows)).atPos
          (modP (aOf cs sh) s.C.a)))).comp (pairAt _ _ _))
  rw [e]
  exact undoTab_laws s.C (cMain cs sh) s.C.a (aOf cs sh) sh.mainRows _ _ _ _ (hM h1) _
    (fun x => modP_at s.C _ _ (by rw [← hM h1]; exact le_max_left _ _) x) _

end Port

end Johnson.Top.H
