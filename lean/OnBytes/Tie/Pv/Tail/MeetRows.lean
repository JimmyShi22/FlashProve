-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/MeetRows.lean: the verifier's own list of the smallness test's single equations
serves as the ties' and reads' share of the one ledger at a link's end.

The last block of a link (Cb/Pv/Tail/DigBatch.lean) lays one ledger and batches it. Its ties and
reads may be any list of forms that gives every tie and every read (Cb/Pv/Tail/ClOf.lean). Here the
list is `rowsLedger` (OnBytes/Tie/Pv/Tail/EndsLedger.lean): the forms of the very rows that the
verifier's routine adds to its total.

A record for each statement. The verifier's record of a smallness test holds the drawn matrix and
the tables' weights, and the rows read both. A link's statement behind the round holds any matrix
that can be drawn and any points that the rounds before can draw. So the list is taken at `rec x'`:
a record for each statement, all with the same sizes t (OnBytes/Tie/Pv/Tail/EndsCut.lean).

Main names:
  `rowsAt`: the list at the statement behind the lookup, carried into the entries of all messages.
  `hrows_port`: it gives every tie and every read: the premise `hrows` of `hlay_rows`.
  `hlay_port`: so the ledger `layR D (rowsAt ..)` gives `layD`: the premise `hlay` of `dig_know`.

Limits: `rec` is a letter: which record belongs to a statement is not said. Premises, at every
statement: the record has the sizes t; `Fits`; every table lies in the third vector; and `AtT` at
every tuple of messages: the letters are read off the cells that the entries give and off that
record: whoever takes the letters from committed messages owes it. `IsT`: the frame's reads are
given by tables. One way alone.

-/
import Cb.Pv.Tail.HostT
import OnBytes.Tie.Pv.Tail.EndsCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Road.Rows OnBytes.Tie.Pv.Tail.Port Cb.Pv.Tail

variable {K J : Type} [Field K] [Fintype J] (ρ : Reading K) (Y : Lay J) {t : TSize}
  {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] {Q : Host K t.size J₁ J₂}
  {U W₀ MM J₃ : Type} [Fintype J₃] [DecidableEq J₃] (T : LateU Q.let U W₀) (left : MM → Q.M)
  (right : MM → U) (D : Tail3 Q MM J₃) (rec : D.X' → HTailF2) (iJ : J → J₃) (pc : ℕ)

/-- The verifier's list at the statement behind the lookup, in the entries of all messages. -/
def rowsAt (x' : D.X') : TWhole.Ledger K J₃ :=
  (rowsLedger ρ Y (rec x') (rec x').funs pc).map (pushF iJ)

variable {phi : Q.Xe → ℕ → ℕ → K} {symN : Q.M₁ → ℕ → ℕ → ℕ → K} {u3N : Q.U₁ → ℕ → K}

/-- The verifier's list gives every tie and every read. -/
theorem hrows_port (hT : IsT Q phi symN u3N) (ht : ∀ x', sizeOf (rec x') = t)
    (hAt : ∀ x' m, AtT ρ (rec x') t (thetaQ Q phi symN u3N) (D.pr x').1 (left m)
      (T.digs (right m)) (D.pr x').2 fun a r c => Y.cellAt (fun j => D.msg₃ m (iJ j)) a r c)
    (hfit : ∀ x', Fits (rec x')) (htree : ∀ x', ∀ Fn ∈ (rec x').funs.toList, Fn.tree = 2) :
    ∀ x' m, TWhole.Ledger.Holds (rowsAt ρ Y D rec iJ pc x') (D.msg₃ m) →
      Late.Eqs (D.pr x').1 (D.pr x').2 (left m) (T.digs (right m)) := by
  intro x' m h
  unfold rowsAt at h
  rw [pushL_holds] at h
  exact eqs_thetaQ hT
    (eqs_cut ρ Y (rec x') (ht x') pc _ (hAt x' m) (hfit x') (htree x') h)

/-- The ledger with the verifier's list gives the one ledger of Cb/Pv/Tail/DigBatch.lean. -/
theorem hlay_port (hT : IsT Q phi symN u3N) (ht : ∀ x', sizeOf (rec x') = t)
    (hs : ∀ m j, D.msg₃ m (D.is j) = vals Q.let (left m) (T.digs (right m)) j)
    (hAt : ∀ x' m, AtT ρ (rec x') t (thetaQ Q phi symN u3N) (D.pr x').1 (left m)
      (T.digs (right m)) (D.pr x').2 fun a r c => Y.cellAt (fun j => D.msg₃ m (iJ j)) a r c)
    (hfit : ∀ x', Fits (rec x')) (htree : ∀ x', ∀ Fn ∈ (rec x').funs.toList, Fn.tree = 2) :
    ∀ x' m, TWhole.Ledger.Holds (layR D (rowsAt ρ Y D rec iJ pc) x') (D.msg₃ m) →
      TWhole.Ledger.Holds (layD D x') (D.msg₃ m) :=
  hlay_rows T left right D _ hs (hrows_port ρ Y T left right D rec iJ pc hT ht hAt hfit htree)

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.hrows_port
#print axioms OnBytes.Tie.Pv.Tail.hlay_port
