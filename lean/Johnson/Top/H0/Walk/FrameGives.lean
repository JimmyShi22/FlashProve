-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameGives.lean: what the link's frame's steps do to the record: statements on
the record alone. Definitions of Props: no theorem stands here. The proofs: FrameTiedRec.lean.

  LaidAdds         what a yes of "laid" gives: the record is handed on; a first call is due; the
                   chain stands at link m
  ClearedRec       what "cleared" leaves and turns of the record
  ClearedGives     "cleared" gives ClearedRec
  OpenedLeaves     what every "opened" leaves
  OpenedAttGives, OpenedLayGives, OpenedZeroGives    "opened" is no block of the flat list: it is
                   joined behind the block at the link's first place: where the chain stands behind
                   it, the link's number, the ledger as it is laid, and all that it leaves

Of the table of joints (Johnson/Desc/First/Borders.lean) this file reads Stand and standOf alone:
it imports neither the promise at a piece nor the chain of promises.
No soundness statement.

-/
import Johnson.Desc.First.Borders
import Johnson.Top.H0.Walk.FrameRow
import Johnson.Top.H0.Walk.FrameSized
import Johnson.Top.H0.Walk.FrameProps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S ModelPart Stand standOf)
open VerifiableInference.Desc.First.Pend (pendingRowO)

/-! ### «laid» -/

/-- What a yes of «laid» adds, which the table's term does not hold: behind it a first call is due
and the chain stands at link m. -/
def LaidAdds : Prop :=
  ∀ (m : Nat) (s t : S), layFront m s = .ok t →
    t = s ∧ firstDue t.check = true ∧ t.check.frame.link = m

/-! ### «cleared» -/

/-- **What «cleared» leaves and turns of the record.** -/
def ClearedRec (X : LinkPub) (left : S → Option WsForkOut) (lay : WsLay) (lin : Params.LinShape)
    (s t : S) : Prop :=
  t.atBetween = true ∧ t.check = s.live ∧ t.live = s.live ∧ t.book = s.book ∧ t.roots = s.roots ∧
    t.rowsOwed = s.rowsOwed ∧ t.failed = s.failed ∧ t.req = s.req ∧
    t.st.codes = s.st.codes ∧ t.st.groups = s.st.groups ∧
    t.st.oracles.size = s.st.oracles.size ∧
    (∀ i : Nat, (t.st.oracles[i]?).map (fun (x : Oracle) => { x with ledger := none }) =
      (s.st.oracles[i]?).map fun (x : Oracle) => { x with ledger := none }) ∧
    t.out.reply = s.out.reply ∧ t.out.indexMasks = s.out.indexMasks ∧
    (X.fv = false → t.out = s.out ∧ t.st = s.st) ∧
    (X.fv = true → ∃ r, Law.rowBy left lay X.NCL lin s = some r ∧
      t.out.pending = s.out.pending ++ [r])

/-- «cleared» gives ClearedRec: every clause by a lemma that lies. -/
def ClearedGives : Prop :=
  ∀ (X : LinkPub) (counts : S → Except String Unit) (left : S → Option WsForkOut) (lay : WsLay)
    (lin : Params.LinShape) (s t : S),
    clearWith X counts left (fun im w n os => pendingRowO lay im w n lin os) s = .ok t →
    ClearedRec X left lay lin s t

/-! ### «opened»: the frame's share of the first place's block's tie -/

/-- What every «opened» leaves. -/
def OpenedLeaves (s t : S) : Prop :=
  t.check = s.check ∧ t.live = s.check ∧ t.st = s.st ∧ t.book = s.book ∧ t.roots = s.roots ∧
    t.rowsOwed = s.rowsOwed ∧ t.failed = s.failed ∧ t.req = s.req

def OpenedAttGives : Prop :=
  ∀ (P : AttPar) (s t : S), openAtt P s = .ok t →
    standOf t = Stand.link ModelPart.attention ∧ (∃ L, t.link? = some L ∧ L.link = P.l) ∧
      OpenedLeaves s t ∧ t.out = s.out ∧ Law.SizedAt P.ns t ∧
      t.fork? = some (startFork P.X P.ns) ∧
      t.tl? = some { P.tl₀ with funClosed := false, foldDrawn := 0 }

def OpenedLayGives : Prop :=
  ∀ (P : LayPar) (s t : S), openLay P s = .ok t →
    standOf t = Stand.link ModelPart.layers ∧ (∃ L, t.link? = some L ∧ L.link = P.l) ∧
      OpenedLeaves s t ∧ t.out = s.out ∧ Law.SizedAt P.ns t ∧
      t.fork? = some (startFork P.X P.ns) ∧ t.tl? = some P.tl₀

def OpenedZeroGives : Prop :=
  ∀ (P : LayPar) (fvs : List Bool) (kCol : Nat) (s t : S), openLayZero P fvs kCol s = .ok t →
    standOf t = Stand.link ModelPart.layers ∧ (∃ L, t.link? = some L ∧ L.link = 0) ∧
      OpenedLeaves s t ∧
      (∃ im, Props.IndexMasksAt (roomOf fvs kCol) s.check s.st.oracles im ∧
        t.out = { s.out with indexMasks := im }) ∧
      Law.SizedAt P.ns t ∧ t.fork? = some (startFork P.X P.ns) ∧ t.tl? = some P.tl₀

end Johnson.Desc.First.Walk.Tied
