-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchKept.lean: the caller of the code switch behind the fold of a group of one
signature of the programs' shapes, some of whose members are kept whole: its condition from tests
on numbers alone.

Johnson/Top/H/SwitchBehindFold.lean has the caller `switchOf` at any choice of kept messages, and
its condition under three premises: the test `allMeet` at the family that is sent, the laws of the
choice (`GHeld.Laws`), and `Grp.Fits`. Here the group is `Rows.ofFn` at `membPort`
(Johnson/Top/H/MemberOf.lean) over `sigOf cs l`, whole members are kept (`Rows.keep`,
Johnson/Top/H/GroupRowsKept.lean), and the choice is `Rows.held` (Johnson/Top/H/GroupRowsHeld.lean)
at `undoPort` (Johnson/Top/H/MemberHeld.lean). Then the second premise is a theorem, and the third
follows from an inequality on numbers for each member. Definitions, statements and proofs.
Main names:
  `mbPort`, `rowsPort`: the members; the group's data.
  `undoAt`, `heldPort`, `heldPort_laws`: the way back from a kept member's main rows; the choice of
    kept messages; its laws, with no premise beyond what the data ask: a kept member has a main
    row and no mask row.
  `rowsPort_fits`: `Grp.Fits`, if no member's tree is longer than the stage's positions and the
    joint radius e is at most 2 ^ (A - a) e' + (2 ^ (A - a) - 1) at each member (`membPort_fits`).
  `switchKept`: `switchOf` at `heldPort`.
  `switchKept_ok`: `SendLocRide.OK` of it, from `allMeet` at the family that is sent and these two
    conditions on numbers.
Limits: one signature: the members are messages of one list l. That the members' tables stand under
the stage's codes (hM, hZ) and that a kept member has a main row and no mask row (h1, h0) are
premises, carried in the data. No numbers are written here. That the programs keep these members,
and that a switch of the programs' protocol is a value of `switchKept`, is not said. The limits of
the files named hold here.

-/
import Johnson.Top.H.SwitchBehindFold
import Johnson.Top.H.MemberHeld

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Slice Cb Iop IOR Johnson.Pack

variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (mem : Fin l.length → Prop) [DecidablePred mem] (s : Sg) (e : ℕ) (oM oZ : Fin l.length → ℕ)
  (hM : ∀ i, mem i → (l.get i).1.mainRows ≠ 0 → cMain cs (l.get i).1 = s.C)
  (hZ : ∀ i, mem i → (l.get i).1.maskRows ≠ 0 → cMask cs (l.get i).1 = s.Z)

/-- A member. -/
noncomputable def mbPort (i : Fin l.length) (k : mem i) : MembAt ((sigOf cs l).om i) s :=
  membPort cs (l.get i).1 (l.get i).2 s (oM i) (oZ i) (hM i k) (hZ i k)

/-- The group's data. -/
noncomputable def rowsPort : Rows (sigOf cs l) :=
  Rows.ofFn (S := sigOf cs l) s e mem (mbPort cs l mem s oM oZ hM hZ)

/-- The joint radius implies each member's own, from an inequality on numbers. -/
theorem rowsPort_fits (hA : ∀ i, mem i → aOf cs (l.get i).1 ≤ s.C.a)
    (he : ∀ i, mem i → e ≤ 2 ^ (s.C.a - aOf cs (l.get i).1) * (l.get i).2 +
      (2 ^ (s.C.a - aOf cs (l.get i).1) - 1)) : (rowsPort cs l mem s e oM oZ hM hZ).G.Fits :=
  Rows.ofFn_fits (S := sigOf cs l) s e mem (mbPort cs l mem s oM oZ hM hZ) fun i k =>
    membPort_fits cs (l.get i).1 (l.get i).2 s (oM i) (oZ i) (hM i k) (hZ i k) e (hA i k) (he i k)

variable (kp : {i // mem i} → Prop) [DecidablePred kp]
  (h1 : ∀ a, kp a → (l.get a.1).1.mainRows ≠ 0) (h0 : ∀ a, kp a → (l.get a.1).1.maskRows = 0)
  (kq : Fin l.length → Prop)

/-- The way back from a kept member's main rows. -/
def undoAt (a : {i // mem i}) (k : kp a) :
    Undo (portCode cs (l.get a.1).1) (s.cM.il (Fin (l.get a.1).1.mainRows)) :=
  undoPort cs (l.get a.1).1 s (hM a.1 a.2 (h1 a k)) (h0 a k)

/-- The choice of kept messages. -/
noncomputable def heldPort : GHeld ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).Sh kq :=
  (rowsPort cs l mem s e oM oZ hM hZ).held kp kq (undoAt cs l mem s hM kp h1 h0)

/-- Its laws. -/
theorem heldPort_laws : (heldPort cs l mem s e oM oZ hM hZ kp h1 h0 kq).Laws :=
  Rows.held_laws (rowsPort cs l mem s e oM oZ hM hZ) kp kq (undoAt cs l mem s hM kp h1 h0)
    fun a k => undoPort_laws cs (l.get a.1).1 (l.get a.1).2 s (oM a.1) (oZ a.1) (hM a.1 a.2)
      (hZ a.1 a.2)
      (h1 a k) (h0 a k)

variable [DecidablePred kq] {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) (rowsPort cs l mem s e oM oZ hM hZ).G.C.J)
  (Z : Evader GE ((rowsPort cs l mem s e oM oZ hM hZ).G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf cs l).sub kq).Msg × Wp))
  (cs' : OnBytes.Codes) (l' : List (OnBytes.OracleShape × ℕ))
  (cutN : (sigOf cs' l').Msg →
    ((heldPort cs l mem s e oM oZ hM hZ kp h1 h0 kq).foldD Sb sl Z A₀).Cf.N.Wit) (t : ℕ)
  (w₀ : ((heldPort cs l mem s e oM oZ hM hZ kp h1 h0 kq).foldD Sb sl Z A₀).tgt.W) {Pw : Type}
  (Cw : LdCode GE Pw)

/-- The caller. -/
noncomputable def switchKept : Cb.Pv.SendLocRide.Size GE :=
  switchOf (heldPort cs l mem s e oM oZ hM hZ kp h1 h0 kq) Sb sl Z A₀ cs' l' cutN t w₀ Cw

/-- The kind's condition, from tests on numbers alone. -/
theorem switchKept_ok (h : allMeet cs' l' = true) (hA : ∀ i, mem i → aOf cs (l.get i).1 ≤ s.C.a)
    (he : ∀ i, mem i → e ≤ 2 ^ (s.C.a - aOf cs (l.get i).1) * (l.get i).2 +
      (2 ^ (s.C.a - aOf cs (l.get i).1) - 1)) :
    Cb.Pv.SendLocRide.OK
      (switchKept cs l mem s e oM oZ hM hZ kp h1 h0 kq Sb sl Z A₀ cs' l' cutN t w₀ Cw) :=
  switchOf_ok (heldPort cs l mem s e oM oZ hM hZ kp h1 h0 kq) Sb sl Z A₀ cs' l' cutN t w₀ Cw h
    (heldPort_laws cs l mem s e oM oZ hM hZ kp h1 h0 kq)
    (rowsPort_fits cs l mem s e oM oZ hM hZ hA he)

end Johnson.Top.H

#print axioms Johnson.Top.H.rowsPort_fits
#print axioms Johnson.Top.H.heldPort_laws
#print axioms Johnson.Top.H.switchKept_ok
