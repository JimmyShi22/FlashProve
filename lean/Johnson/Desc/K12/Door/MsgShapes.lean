-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Door/MsgShapes.lean: **"ORACLE MESSAGE o OF THE STATEMENT HAS THE PLAN's SHAPE OF
ITS MESSAGE"**, as a test with code on the record, for the table's door. No Mathlib.
"K12.seatsCarried" (DoorBools.lean) reads the book alone: a message's (tree, part) and a tree's
shape (lengths and symbols a part). What a message IS by the statement (`Oracle.shape`: its codes,
rows, degree, answers) is another field of the record and another type. Whoever takes a message's
shape from the record on one side and from the plan's member on the other wants the two to be one.
  `msgsOf sends`, `msgsOfChain c`: THE PLAN's SIDE: the shapes of the notices of the planner's
    sendings, in the order of their entries: the very list of sendings that `laidOfChain` lays.
  `msgShapesB M st`: the statement's oracle messages' shapes are the first of M, as many as there
    are: the prefix form, as at "K12.seatsCarried".
  `msgShape_at`: WHAT ITS YES GIVES: below the statement's number of messages the shape of message o
    is M's entry number o.
  `atFirstShapes`, `nShapes` ("K12.msgShapes"), `shapesMore`: at the first chain's record; the name;
    the rows: open at the chain's start, dropped by nobody, asked by the proximity test at the
    finish. Whoever else spends it lays its own ask.
NOTHING HERE HAS RUN.

-/
import Johnson.Desc.K12.Door.Door

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Door
open OnBytes OnBytes.Params
open VerifiableInference.Desc.First (S More MoreRow MoreName)

/-- The shapes of the sendings' notices, in turn. -/
def msgsOf (sends : List (List OracleNotice)) : List OracleShape :=
  sends.flatten.map (·.shape)

/-- The same of a chain of the planner's: the sendings in the order of their entries. -/
def msgsOfChain (c : Johnson.G.ChainSends) : List OracleShape :=
  msgsOf ((c.sends.mergeSort fun a b => a.entry ≤ b.entry).map (·.sent))

/-- The statement's messages' shapes are the first of M. -/
def msgShapesB (M : List OracleShape) (st : Statement) : Bool :=
  st.oracles.toList.map (·.shape) == M.take st.oracles.size && decide (st.oracles.size ≤ M.length)

/-- **What its yes gives.** -/
theorem msgShape_at {M : List OracleShape} {st : Statement} (h : msgShapesB M st = true) (o : Nat)
    (ho : o < st.oracles.size) : (st.oracles[o]?).map (·.shape) = M[o]? := by
  unfold msgShapesB at h
  rw [Bool.and_eq_true] at h
  have e : st.oracles.toList.map (·.shape) = M.take st.oracles.size := eq_of_beq h.1
  have e1 : (st.oracles.toList.map (·.shape))[o]? = (st.oracles[o]?).map (·.shape) := by
    rw [List.getElem?_map, Array.getElem?_toList]
  rw [← e1, e, List.getElem?_take_of_lt ho]

/-- At the first chain's record. -/
def atFirstShapes (M : List OracleShape) (s : S) : Bool := msgShapesB M s.st

def nShapes : MoreName := (none, "K12.msgShapes")

/-- The item's rows. -/
def shapesMore : More where
  rows := fun _ p =>
    if p.chain != 1 || p.link.isSome then {}
    else match p.kind with
      | .K12 => { asks := [nShapes] }
      | _ => {}
  start := [nShapes]

end VerifiableInference.Desc.K12.Door

#print axioms VerifiableInference.Desc.K12.Door.msgShape_at
