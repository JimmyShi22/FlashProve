-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Print/Items.lean: on a round's items as they are printed (`itemsOf`,
OnBytes/Prover/Print/Carrier.lean): the typing's reader gives the plain part back; which roots stand
among them; how many they are. And: digests and salts that are written come back. (That a plain
part is made of its old part and its nonce is the library's: `GPlain.mk_old_nonce`,
Iop/GrindProofs.lean.)

Why. A whole file's typing and the entry file's end in the same two functions, `PlainOf.ofGots`
(Run/PlanQTypes.lean) and `Fmt.rootsOf` (Fmt/Rules8.lean). These lemmas speak of a list of items
alone, of no file, so both sides call them.

Main names (namespace `OnBytes.Prover.Print`).
  `ofGots_itemsOf`    PlainOf.ofGots l (itemsOf l rts x) = some x, whatever roots rts are laid in
  `rootsOf_itemsOf`   the roots among the items are the first of rts: as many as there are items
                      "root", if so many were given
  `length_itemsOf`    as many items as the list asks
  `map_ofTriple_triple`, `map_triple_ofTriple`   elements as triples of words, and back
  `digs_back`         digests, as bytes, as digests
  `saltFrom_back`     a typed salt is made again of its first 256 bits and its own part
  `slotSalt_rsOf`     what stands in front of the last 64 bits of the string behind a slot's value

Limits. Where fewer roots are given than there are items "root", `itemsOf` lays the string without
a byte, and `rootsOf_itemsOf` says nothing. No file, no bytes, no prover.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Print.Carrier
import Run.Toy1TieTree
import Run.CodingBitsLaws
import Iop.GrindProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Prover.Print
open _root_.Run
open _root_.Iop (GPlain Dig)
open _root_.Run.PQ (PlainOf)
open OnBytes.Maker (rsOf)

/-- The typing's reader of a round's items gives the plain part back, whatever roots are laid in. -/
theorem ofGots_itemsOf : ∀ (l : List _root_.Fmt.Item) (rts : List ByteArray) (x : PlainOf l),
    PlainOf.ofGots l (itemsOf l rts x) = some x
  | [], _, _ => rfl
  | .root :: l, rts, x => ofGots_itemsOf l rts.tail x
  | .f :: l, rts, (x : UInt64 × PlainOf l) => by
    show (PlainOf.ofGots l (itemsOf l rts x.2)).map (fun y => ((x.1, y) : UInt64 × PlainOf l)) = _
    rw [ofGots_itemsOf l rts x.2]
    rfl
  | .word :: l, rts, (x : UInt64 × PlainOf l) => by
    show (PlainOf.ofGots l (itemsOf l rts x.2)).map (fun y => ((x.1, y) : UInt64 × PlainOf l)) = _
    rw [ofGots_itemsOf l rts x.2]
    rfl
  | .e :: l, rts, (x : _root_.Fmt.Ext × PlainOf l) => by
    show (PlainOf.ofGots l (itemsOf l rts x.2)).map
      (fun y => ((x.1, y) : _root_.Fmt.Ext × PlainOf l)) = _
    rw [ofGots_itemsOf l rts x.2]
    rfl
  | .answer :: l, rts, (x : _root_.Fmt.Ext × PlainOf l) => by
    show (PlainOf.ofGots l (itemsOf l rts x.2)).map
      (fun y => ((x.1, y) : _root_.Fmt.Ext × PlainOf l)) = _
    rw [ofGots_itemsOf l rts x.2]
    rfl

/-- The roots among a round's items are the first of those that were laid in: as many as there are
items "root", if so many were given. -/
theorem rootsOf_itemsOf : ∀ (l : List _root_.Fmt.Item) (rts : List ByteArray) (x : PlainOf l),
    l.countP (· == .root) ≤ rts.length →
    _root_.Fmt.rootsOf (itemsOf l rts x) = rts.take (l.countP (· == .root))
  | [], rts, _, _ => by
    show [] = rts.take 0
    rw [List.take_zero]
  | .root :: l, [], _, h => by
    rw [List.countP_cons_of_pos (by rfl)] at h
    exact absurd h (by simp)
  | .root :: l, r :: rts, x, h => by
    rw [List.countP_cons_of_pos (by rfl)] at h ⊢
    show r :: _root_.Fmt.rootsOf (itemsOf l rts x) = _
    rw [rootsOf_itemsOf l rts x (Nat.le_of_succ_le_succ h), List.take_succ_cons]
  | .f :: l, rts, (x : UInt64 × PlainOf l), h => by
    rw [List.countP_cons_of_neg (by decide)] at h ⊢
    exact rootsOf_itemsOf l rts x.2 h
  | .word :: l, rts, (x : UInt64 × PlainOf l), h => by
    rw [List.countP_cons_of_neg (by decide)] at h ⊢
    exact rootsOf_itemsOf l rts x.2 h
  | .e :: l, rts, (x : _root_.Fmt.Ext × PlainOf l), h => by
    rw [List.countP_cons_of_neg (by decide)] at h ⊢
    exact rootsOf_itemsOf l rts x.2 h
  | .answer :: l, rts, (x : _root_.Fmt.Ext × PlainOf l), h => by
    rw [List.countP_cons_of_neg (by decide)] at h ⊢
    exact rootsOf_itemsOf l rts x.2 h

theorem length_itemsOf : ∀ (l : List _root_.Fmt.Item) (rts : List ByteArray) (x : PlainOf l),
    (itemsOf l rts x).length = l.length
  | [], _, _ => rfl
  | .root :: l, rts, x => congrArg (· + 1) (length_itemsOf l rts.tail x)
  | .f :: l, rts, (x : UInt64 × PlainOf l) => congrArg (· + 1) (length_itemsOf l rts x.2)
  | .word :: l, rts, (x : UInt64 × PlainOf l) => congrArg (· + 1) (length_itemsOf l rts x.2)
  | .e :: l, rts, (x : _root_.Fmt.Ext × PlainOf l) => congrArg (· + 1) (length_itemsOf l rts x.2)
  | .answer :: l, rts, (x : _root_.Fmt.Ext × PlainOf l) =>
    congrArg (· + 1) (length_itemsOf l rts x.2)

/-! ## Elements as triples of words

Kin in the library: `OnBytes.G4.map_ofTriple_triple` (OnBytes/G4/FlatLaws.lean) and
`OnBytes.G4.map_triple_ofTriple` (OnBytes/G4/PlainRound.lean [not in this library]) say the same. They stand among the
laws of another program's reader, which nothing here imports; six files of the library prove the
one or the other in place. -/

theorem map_ofTriple_triple : ∀ l : List OnBytes.E,
    (l.map OnBytes.E.triple).map OnBytes.E.ofTriple = l
  | [] => rfl
  | x :: l => congrArg (x :: ·) (map_ofTriple_triple l)

theorem map_triple_ofTriple : ∀ l : List (UInt64 × UInt64 × UInt64),
    (l.map OnBytes.E.ofTriple).map OnBytes.E.triple = l
  | [] => rfl
  | x :: l => congrArg (x :: ·) (map_triple_ofTriple l)

/-! ## Digests, salts -/

/-- Digests, as bytes, as digests. -/
theorem digs_back : ∀ l : List (Dig 256), (l.map digToBytes).map bytesToDig = l
  | [] => rfl
  | d :: l => by
    show bytesToDig (digToBytes d) :: (l.map digToBytes).map bytesToDig = _
    rw [TieTree.bytes_dig, digs_back l]

/-- A typed salt is made again of its first 256 bits and its own part. -/
theorem saltFrom_back {start : ByteArray} {s : Rom.Bits} (h : SaltFrom start s) :
    leafSalt start (ownSalt s) = s := by
  unfold leafSalt ownSalt
  rw [bytesToBits_bitsToBytes _ h.2, ← h.1, List.take_append_drop]

/-- what stands in front of the last 64 bits of the string behind the slot's value -/
theorem slotSalt_rsOf (index : ℕ) (sl : ByteArray) :
    bitsToBytes ((rsOf index sl).take ((rsOf index sl).length - 64)) = sl := by
  have h64 : (bytesToBits (_root_.Fmt.u64n index)).length = 64 := by
    rw [length_bytesToBits]
    rfl
  unfold rsOf
  rw [List.length_append, h64, Nat.add_sub_cancel, List.take_left', bitsToBytes_bytesToBits]
  rfl

end OnBytes.Prover.Print
