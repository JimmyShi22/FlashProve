-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookSwitchRoom.lean: the eleventh of the files that compute the book
of coins (`ProverCoinCounts`, Honest/Frame.lean): a named test on a class of coins that Honest/BookSwitch.lean
does not count: the free room in the main rows of a switch's oracle message. The message g of the
next stage has 2 ^ k main rows over the new base code; what the fold leaves of the old main row
fills as many places as the old code's message has. Where the new rows hold more places than that, a
prover fills the rest with sampled elements, as it does in g's mask table. From public data alone.
Executable definitions, and tests at synthetic lists; no theorem.

The lines that begin with `#guard` are tests, checked by evaluation: Lean's evaluator runs each of
them when the file is compiled, and the build fails if one is false. The kernel does not check them,
and they prove nothing.

  `mainRoomOf`   one switch: the places of g's main rows; the old code's message length
  `mainRooms`   a chain's switches, in order, each under its label
  `mainRoomFault`   the label of the first switch at which the two numbers differ

Why a test and no count. At every switch of the proof file at both example sets the two numbers are
equal, by a computation over the library's written lists (Johnson/G/SendsLit.lean,
Johnson/G/PackLit.lean): so there is no such coin there, and no printout to compare a count with.
The function that builds the whole book returns an error where they differ.

Limits.
  * The codes of a test's first stage are for the caller to supply, by the test's name, as in
    Honest/BookSwitch.lean.
  * That a prover samples that room is read from a script of the release's own tree that lists a
    prover's draws (tools/audit/level1.py: "free room … behind the row"), not from a page of the
    format.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookSwitch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes (Codes Code OracleNotice)

/-- **One switch**: the places of g's main rows; the message length of the base code of the stage
before. `none` where g names a code that the chain does not have. -/
def mainRoomOf (codes : Codes) (old : Code × Code) (g : OracleNotice) : Option (Nat × Nat) :=
  (codes.base[g.shape.code]?).map fun b => (g.shape.mainRows * b.ell, old.1.ell)

/-- **A chain's switches**, in order: the label, the two numbers. `prev`, `first`: as in
`switchesDue`. -/
def mainRooms (codes : Codes) (first : String → Option (Code × Code)) :
    List Johnson.G.Sending → Option (String × Code × Code) →
      Except String (List (String × Nat × Nat))
  | [], _ => .ok []
  | x :: xs, prev =>
    let t := testOf x.label
    let old := match prev with
      | some p => if p.1 == t then some p.2 else first t
      | none => first t
    match old, x.sent.head? with
    | some o, some g =>
      match mainRoomOf codes o g, groupCodes codes [g] with
      | some n, some now_ =>
        (mainRooms codes first xs (some (t, now_))).map fun l => (x.label, n.1, n.2) :: l
      | _, _ => .error (x.label ++ ": a message names a code that the chain does not have")
    | none, _ => .error (x.label ++ ": the codes of the test's first stage are not laid")
    | _, none => .error (x.label ++ ": the sending holds no message")

/-- **The first switch whose main rows have free room**, or fewer places than the old message. -/
def mainRoomFault (c : Johnson.G.ChainSends) (first : String → Option (Code × Code)) :
    Except String (Option String) :=
  (mainRooms c.codes first (c.sends.filter fun s => isSwitch s.label) none).map fun l =>
    (l.find? fun x => x.2.1 != x.2.2).map (·.1)

/-! ### Tests at synthetic lists -/

-- sixteen rows over a code of length 4 hold the 64 places of the old message; eight do not
#guard mainRoomOf ⟨#[⟨6, 64, 3⟩, ⟨4, 4, 3⟩], #[⟨4, 4, 2⟩]⟩ (⟨6, 64, 3⟩, ⟨4, 4, 2⟩)
    ⟨⟨1, 16, 3, 1, 0, 1⟩, 0⟩ == some (64, 64)
#guard mainRoomOf ⟨#[⟨6, 64, 3⟩, ⟨4, 4, 3⟩], #[⟨4, 4, 2⟩]⟩ (⟨6, 64, 3⟩, ⟨4, 4, 2⟩)
    ⟨⟨1, 8, 3, 1, 0, 1⟩, 0⟩ == some (32, 64)
#guard (mainRoomOf ⟨#[⟨6, 64, 3⟩], #[⟨4, 4, 2⟩]⟩ (⟨6, 64, 3⟩, ⟨4, 4, 2⟩)
    ⟨⟨1, 8, 3, 1, 0, 1⟩, 0⟩).isNone

end ProofFile.Honest
