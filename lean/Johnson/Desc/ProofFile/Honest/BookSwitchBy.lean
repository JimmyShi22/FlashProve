-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookSwitchBy.lean: the two recursions over a chain's code switches,
with the function that reads a test's name off a label as an argument. Two definitions, four lemmas.

  `mainRoomsBy τ`, `switchesDueBy τ`   the texts of `mainRooms` (Honest/BookSwitchRoom.lean) and of
      `switchesDue` (Honest/BookSwitch.lean), to the letter, with `τ` where these have `testOf`
  `mainRooms_by`, `switchesDue_by`     each recursion is its twin at `testOf`
  `mainRoomsBy_congr`, `switchesDueBy_congr`   a twin gives the same at two readers that agree on
      the labels of the list

What it is for. `testOf` calls `String.splitOn`. In trials by the authors of two other parts of this
project `decide +kernel` did not get through a term that holds that call as it stands, and did once
it was rewritten by `Johnson.Unfolds.splitOn_eq`; no such trial is in this file. `testOf` occurs
inside the two recursions' bodies, so a rewriting of `testOf` finds nothing to rewrite in
`mainRooms codes first xs prev`. By these lemmas that term is `mainRoomsBy τ codes first xs prev` at
any `τ` that agrees with `testOf` on the labels of xs: one small fact for each label.

Limits. No text of another file turns. Nothing is evaluated here, and no list of sendings is named.
That a `τ` agrees with `testOf` is the caller's to show. This file proves nothing about soundness,
completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookSwitchRoom

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes (Codes Code OracleNotice)

/-- `mainRooms` (Honest/BookSwitchRoom.lean), with the reader of a label as an argument. -/
def mainRoomsBy (τ : String → String) (codes : Codes) (first : String → Option (Code × Code)) :
    List Johnson.G.Sending → Option (String × Code × Code) →
      Except String (List (String × Nat × Nat))
  | [], _ => .ok []
  | x :: xs, prev =>
    let t := τ x.label
    let old := match prev with
      | some p => if p.1 == t then some p.2 else first t
      | none => first t
    match old, x.sent.head? with
    | some o, some g =>
      match mainRoomOf codes o g, groupCodes codes [g] with
      | some n, some now_ =>
        (mainRoomsBy τ codes first xs (some (t, now_))).map fun l => (x.label, n.1, n.2) :: l
      | _, _ => .error (x.label ++ ": a message names a code that the chain does not have")
    | none, _ => .error (x.label ++ ": the codes of the test's first stage are not laid")
    | _, none => .error (x.label ++ ": the sending holds no message")

/-- `switchesDue` (Honest/BookSwitch.lean), with the reader of a label as an argument. -/
def switchesDueBy (τ : String → String) (codes : Codes) (rounds : List Fmt.DeclaredRound)
    (first : String → Option (Code × Code)) :
    List (Nat × Johnson.G.Sending) → Option (String × Code × Code) →
      Except String (List (String × Nat × Nat × Due))
  | [], _ => .ok []
  | x :: xs, prev =>
    let t := τ x.2.label
    let old := match prev with
      | some p => if p.1 == t then some p.2 else first t
      | none => first t
    let k := (foldK (rounds.drop (x.1 + 1))).getD 0
    match old, x.2.sent.head? with
    | some o, some g =>
      match roomOf codes o g, switchDue codes k o x.2.sent, groupCodes codes [g] with
      | some room, some d, some now_ =>
        (switchesDueBy τ codes rounds first xs (some (t, now_))).map
          fun l => (x.2.label, x.1, room, d) :: l
      | _, _, _ => .error (x.2.label ++ ": a message names a code that the chain does not have")
    | none, _ => .error (x.2.label ++ ": the codes of the test's first stage are not laid")
    | _, none => .error (x.2.label ++ ": the sending holds no message")

theorem mainRooms_by (codes : Codes) (first : String → Option (Code × Code))
    (xs : List Johnson.G.Sending) (prev : Option (String × Code × Code)) :
    mainRooms codes first xs prev = mainRoomsBy testOf codes first xs prev := by
  induction xs generalizing prev with
  | nil => rfl
  | cons x xs ih =>
    simp only [mainRooms, mainRoomsBy, ih]
    rfl

theorem switchesDue_by (codes : Codes) (rounds : List Fmt.DeclaredRound)
    (first : String → Option (Code × Code)) (xs : List (Nat × Johnson.G.Sending))
    (prev : Option (String × Code × Code)) :
    switchesDue codes rounds first xs prev = switchesDueBy testOf codes rounds first xs prev := by
  induction xs generalizing prev with
  | nil => rfl
  | cons x xs ih =>
    simp only [switchesDue, switchesDueBy, ih]
    rfl

theorem mainRoomsBy_congr {τ τ' : String → String} (codes : Codes)
    (first : String → Option (Code × Code)) (xs : List Johnson.G.Sending)
    (prev : Option (String × Code × Code)) (h : ∀ x ∈ xs, τ x.label = τ' x.label) :
    mainRoomsBy τ codes first xs prev = mainRoomsBy τ' codes first xs prev := by
  induction xs generalizing prev with
  | nil => rfl
  | cons x xs ih =>
    have h0 : τ x.label = τ' x.label := h x (List.Mem.head _)
    have ih' := fun p => ih p fun y hy => h y (List.Mem.tail _ hy)
    simp only [mainRoomsBy, h0, ih']

theorem switchesDueBy_congr {τ τ' : String → String} (codes : Codes)
    (rounds : List Fmt.DeclaredRound) (first : String → Option (Code × Code))
    (xs : List (Nat × Johnson.G.Sending)) (prev : Option (String × Code × Code))
    (h : ∀ x ∈ xs, τ x.2.label = τ' x.2.label) :
    switchesDueBy τ codes rounds first xs prev = switchesDueBy τ' codes rounds first xs prev := by
  induction xs generalizing prev with
  | nil => rfl
  | cons x xs ih =>
    have h0 : τ x.2.label = τ' x.2.label := h x (List.Mem.head _)
    have ih' := fun p => ih p fun y hy => h y (List.Mem.tail _ hy)
    simp only [switchesDueBy, h0, ih']

end ProofFile.Honest

#print axioms ProofFile.Honest.mainRooms_by
#print axioms ProofFile.Honest.switchesDue_by
#print axioms ProofFile.Honest.mainRoomsBy_congr
#print axioms ProofFile.Honest.switchesDueBy_congr
