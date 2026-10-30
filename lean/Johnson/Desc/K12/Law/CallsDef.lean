-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.First.Base.Ground
import Johnson.Desc.Ground.Calls
/-
Johnson/Desc/K12/Law/CallsDef.lean: A RUN OF THE GROUND's PLAIN CALLS, AS A RELATION ON THE GROUND's CARRIED STATE. DEFINITIONS AND THREE SMALL LEMMAS; it stands over the plain ground alone. BOOK-KEEPING. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  Call ft d d'    ONE STEP: a yes of newGroupP · recvP AT ft · admitP OF ROWS THAT rowsFor HAS MADE at the state's codes and the message's own shape, A SHAPE THAT FITS THE CODES, from seeds whose points have at least the cube's coordinates (these two ride in the step, since the law on a sample's row asks their like) · joinP · addRowP · closeLedgerP · spendAsMaskP · beginRunP · or: one tree's count of lists rises by one · or: the opened columns alone turn
  Calls ft d d'   a run of such steps · Calls.one · Calls.trans · Calls.toCols
  Calls.keeps     whatever relation on carried states is reflexive, transitive and kept by each kind of step is kept by a run
No sorry, no axiom of ours; each theorem has its premises.
-/
set_option autoImplicit false
namespace H2K.Out
open OnBytes OnBytes.Params
open VerifiableInference.Desc
open _root_.Desc.Plain (DState rowsFor)

abbrev DS : Type := DState Unit

/-- One step. -/
inductive Call (ft : Nat) : DS → DS → Prop
  | newGroup {d d' : DS} {a b n : Nat} : Ground.newGroupP d a b = some (n, d') → Call ft d d'
  | recv {d d' : DS} {sent : Array OracleNotice} {ids : Array Nat} :
      Ground.recvP ft d sent = some (ids, d') → Call ft d d'
  | admit {d d' : DS} {o : Nat} {rows : Array Row} {s : OracleShape} {seeds : List SampleSeed}
      {ys ys' : List E} : (d.st.oracles[o]?).map (·.shape) = some s →
      Blk.shapeOk d.st.codes s = true →
      (∀ sd ∈ seeds, (Send.cube d.st.codes s).bits ≤ sd.z.length) →
      rowsFor d.st.codes s o seeds (List.range s.answers) ys #[] = some (rows, ys') →
      Ground.admitP d o rows = some d' → Call ft d d'
  | join {d d' : DS} {g o : Nat} {k : Bool} : Ground.joinP d g o k = some d' → Call ft d d'
  | addRow {d d' : DS} {g : Nat} {row : Row} : Ground.addRowP d g row = some d' → Call ft d d'
  | closeLedger {d d' : DS} {o : Nat} : Ground.closeLedgerP d o = some d' → Call ft d d'
  | spend {d d' : DS} {o : Nat} : Ground.spendAsMaskP d o = some d' → Call ft d d'
  | begin {d d' : DS} {g : Nat} {run : RunInput} : Ground.beginRunP d g = some (run, d') → Call ft d d'
  | count (d : DS) (t : Nat) : Call ft d { d with book := { d.book with
      trees := d.book.trees.modify t fun x => { x with lists := x.lists + 1 } } }
  | cols (d : DS) (l : List (Nat × Nat × List UInt64)) : Call ft d { d with opened := l }

/-- A run of steps. -/
inductive Calls (ft : Nat) : DS → DS → Prop
  | nil (d : DS) : Calls ft d d
  | cons {a b c : DS} : Call ft a b → Calls ft b c → Calls ft a c

variable {ft : Nat}

theorem Calls.one {a b : DS} (h : Call ft a b) : Calls ft a b := .cons h (.nil b)

theorem Calls.trans {a b c : DS} (h : Calls ft a b) (k : Calls ft b c) : Calls ft a c := by
  induction h with
  | nil _ => exact k
  | cons s _ ih => exact .cons s (ih k)

/-- Whatever is reflexive, transitive and kept by each step is kept by a run. -/
theorem Calls.keeps {R : DS → DS → Prop} (hr : ∀ d, R d d) (ht : ∀ a b c, R a b → R b c → R a c)
    (hs : ∀ a b, Call ft a b → R a b) {a b : DS} (h : Calls ft a b) : R a b := by
  induction h with
  | nil d => exact hr d
  | cons s _ ih => exact ht _ _ _ (hs _ _ s) ih

/-- The opened columns may be set at will. -/
theorem Calls.toCols (d : DS) (l : List (Nat × Nat × List UInt64)) :
    Calls ft d { d with opened := l } := .one (.cols d l)

end H2K.Out
