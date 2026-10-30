-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Seam.lean: the seam between what a typed masked sumcheck puts out and the claims of
the shipped Lean verifier.

The library's masked sumcheck (Cb/Ld/LdPsc.lean: parameters Y : PscPar K) ends in an output
statement o and two kinds of claim on the entries m : Y.J → K: the row on the hiding polynomial's
coefficients (UHolds o m) and one row for each end value (EHolds o m a). The shipped Lean verifier
(OnBytes/Model/Psc.lean) ends a sumcheck in a record p : Psc and a state F : Fork, and speaks of
forms (Aff) that have a value in a world (OnBytes/Model/HideLaws.lean).

The world is F.worldOf rho (mask m) (entry m): under slot j lies what F holds as shown for j, less
the slot's factor times mask m j. mask and entry are arguments: any functions of m. In use mask m j
is entry j of the sub-proof's mask row and entry m gives the entries of the virtual rows, both read
off m (OnBytes/Tie/Pv/SeamWorld.lean [not in this library]).

RowTie, for any Y : PscPar K, says how o lies against p and F:
  walk, ne   the verifier's weights with its challenges match Y's variables with o's point: as many
             coefficients, the same polynomial psi, the same point (Match);
  eps, fin   o's factor and last value are the readings of p's;
  hid        the hiding polynomial's coefficients are the hidden values under the slots from
             p.first on, in the verifier's order (place);
  inc        the form of the masks that come in with the claim is the target less the start form.
EndTie, for the instance with the further variable (T : PscOur K), one end value a and its slot j:
  vals       the shown end value a is what F holds as shown under slot j;
  beta       the challenge of the further variable is that slot's factor;
  cAt        the mask entry of the end value a is mask m j.

Statements.
  seam_value under RowTie: the value of the form p.rowForm S0 kept, for any S0 and kept.
  seam_row   under RowTie and two equations (S0 is the reading of the summand's public part at o's
             point and values; kept's value is the sum of the kept terms): UHolds o m holds exactly
             if p.rowForm S0 kept has the value 0.
  seam_end   under EndTie: EHolds o m a holds exactly if the hidden value under slot j is the map a
             at o's point.

Which sumchecks. A sumcheck that ends in end values under the sub-proof's own mask row has RowTie
and an EndTie for each end value. The merge has RowTie and no EndTie: the mask of its end value is
no entry of the sub-proof's mask row, and its end value's row leaves the sub-proof
(OnBytes/Model/Pending.lean). A sumcheck without end values is the library's core alone; its end
claim is UHolds at the output without values (Spec.psc_mid_empty), so RowTie serves it.

Not claimed.
That a run of the verifier's routines gives a p and an F with these ties
(OnBytes/Tie/Pv/SeamRun.lean fills some fields).
RowTie and EndTie speak of one record, one state and one output statement: they are facts on one
run's end. Asked of all states or all output statements at once they are false.
That the run adds the form p.rowForm S0 kept to its claims: seam_row speaks of that form's value,
whether or not a claim of the run reads it.
That Y's functionals are the verifier's weights: Match reads no node and no weight of a variable;
that is Fits (OnBytes/Tie/Pv/Psc/PscTie.lean).
That mask m j belongs to a row that is committed before the draws: that is the joint's.
Where the start form names entries of an array that is committed after the sumcheck, m holds entries
that are not fixed when eps is drawn; what the block's soundness then says is not looked at here.
Nothing on soundness or on hiding.

-/
import OnBytes.Tie.Pv.Psc.StepWalk
import OnBytes.Model.Psc
import Cb.Ld.LdPscProofsOur

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv
open Cb OnBytes OnBytes.Model OnBytes.Road.Hd

section Row
variable {K : Type} [Field K] (ρ : Reading K) (Y : PscPar K)

/-- How the output statement o lies against the verifier's record p and state F. -/
structure RowTie (F : Fork) (mask : (Y.J → K) → ℕ → K) (entry : (Y.J → K) → ℕ → ℕ → ℕ → K)
    (p : Psc) (o : Y.Out) : Prop where
  walk : Match ρ (zipT p.vars.toList p.r.toList) (Y.vars o.st) (Y.hp o.st o.pt)
  ne : zipT p.vars.toList p.r.toList ≠ []
  eps : o.eps = ρ.val p.eps
  fin : o.fin = ρ.val p.claim
  hid : ∀ m, Y.W o.st m = place (F.worldOf ρ (mask m) (entry m)).slot (Y.vars o.st) p.first
  inc : ∀ m, Y.inc o.st m = ρ.val p.target - p.start.value ρ (F.worldOf ρ (mask m) (entry m))

variable {ρ Y} {F : Fork} {mask : (Y.J → K) → ℕ → K} {entry : (Y.J → K) → ℕ → ℕ → ℕ → K}
  {p : Psc} {o : Y.Out}

/-- The value of the form that the verifier's sumcheck leaves, whatever the caller passes as the
summand's public part and as the kept terms. -/
theorem seam_value (t : RowTie ρ Y F mask entry p o) (m : Y.J → K) (S0 : E) (kept : Aff) :
    (p.rowForm S0 kept).value ρ (F.worldOf ρ (mask m) (entry m)) =
      hU (Y.vars o.st) (Y.W o.st m) (Y.hp o.st o.pt) +
        o.eps * hPsi (Y.vars o.st) (Y.hp o.st o.pt) * Y.inc o.st m +
        o.eps * kept.value ρ (F.worldOf ρ (mask m) (entry m)) - (o.fin - o.eps * ρ.val S0) := by
  obtain ⟨a1, a2⟩ := walk_hU ρ (F.worldOf ρ (mask m) (entry m)).slot _ _ _ p.first t.ne t.walk
  have b1 : sumFrom (fun j y => ρ.val y * (F.worldOf ρ (mask m) (entry m)).slot j) p.first
      p.walk.1 = hU (Y.vars o.st) (Y.W o.st m) (Y.hp o.st o.pt) := by
    rw [t.hid m]
    exact a1
  have b2 : ρ.val p.walk.2 = hPsi (Y.vars o.st) (Y.hp o.st o.pt) := a2
  rw [Psc.rowForm_value, b1, b2, ← t.inc m, ← t.eps, ← t.fin]

/-- The row on the hiding polynomial's coefficients is the claim that the verifier's sumcheck
leaves. hS: S0 is the reading of the summand's public part at o's point, on o's values. hK: the
value of kept is the sum of the kept terms. -/
theorem seam_row (t : RowTie ρ Y F mask entry p o) (m : Y.J → K) (S0 : E) (kept : Aff)
    (hS : Y.S0 o.st (Y.hp o.st o.pt) o.vals = ρ.val S0)
    (hK : ∑ b, Y.S1 o.st (Y.hp o.st o.pt) o.vals b * Y.Gb o.st m b (Y.hp o.st o.pt) =
      kept.value ρ (F.worldOf ρ (mask m) (entry m))) :
    Y.UHolds o m ↔ (p.rowForm S0 kept).value ρ (F.worldOf ρ (mask m) (entry m)) = 0 := by
  rw [seam_value t m S0 kept, ← hK, ← hS]
  exact sub_eq_zero.symm

end Row

section End
variable {K : Type} [Field K] [Fintype K] (ρ : Reading K) (T : PscOur K)

/-- How the end value a of the output statement o lies against slot j of the state F. -/
structure EndTie (F : Fork) (mask : (T.J → K) → ℕ → K) (o : T.par.Out) (a : T.A) (j : ℕ) :
    Prop where
  vals : o.vals a = ρ.val (F.vp.getD j zeroE)
  beta : T.lst o.st (T.par.hp o.st o.pt) = ρ.val (F.mf.getD j zeroE)
  cAt : ∀ m, m (T.cAt a) = mask m j

variable {ρ T} {F : Fork} {mask : (T.J → K) → ℕ → K} {o : T.par.Out} {a : T.A} {j : ℕ}

/-- The row on an end value says what the hidden value under its slot is. -/
theorem seam_end (t : EndTie ρ T F mask o a j) (entry : (T.J → K) → ℕ → ℕ → ℕ → K)
    (m : T.J → K) :
    T.par.EHolds o m a ↔
      (F.worldOf ρ (mask m) (entry m)).slot j =
        T.F o.st m a (T.ini o.st (T.par.hp o.st o.pt)) := by
  rw [psc_our_val K T o m a]
  show _ ↔ ρ.val (F.vp.getD j zeroE) - ρ.val (F.mf.getD j zeroE) * mask m j = _
  rw [← t.vals, ← t.beta, ← t.cAt m]
  constructor
  · intro h
    rw [← h]
    ring
  · intro h
    rw [← h]
    ring

end End

end OnBytes.Tie.Pv

#print axioms OnBytes.Tie.Pv.seam_value
#print axioms OnBytes.Tie.Pv.seam_row
#print axioms OnBytes.Tie.Pv.seam_end
