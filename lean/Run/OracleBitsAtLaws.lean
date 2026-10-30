-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/OracleBitsAtLaws.lean: the laws of `oBitsAt` (Run/OracleBitsAt.lean), and the way back from a
function on bit strings.

One definition and theorems with their proofs. For proofs only; no program imports this file.

Main names.
  `oBitsAt_oracle`: at `Fmt.oracle` it is `oBits`.
  `oBitsAt_bytes`: at the bits of a byte string b that is plain (`plainB`: its first byte is not
    4) it is O's answer at b.
  `oOf g`: for a function g on bit strings, a function on byte strings with `oBitsAt (oOf g) = g`
    (`oBitsAt_oOf`). It undoes `toBytes` by choice: it has no code and is meant to have none: it is
    for statements "at every g"; a program runs at a written O. Its answers have 32 bytes
    (`size_oOf`).
  `forall_oBitsAt`: a property holds of `oBitsAt O` at every O exactly if it holds of every g.
  `oOf_plain`, `HO_oOf`: at a plain byte string `oOf g` is `oB (g ())` (Run/OCompM.lean); so the
    format's hash over the one is the format's hash over the other.
  `oBitsAt_oB`: `oBitsAt (oB (g ()))` agrees with g at plain strings.

To be minded. `toBytes` is not "the bits as bytes": a string that is not whole bytes, or whose first
byte is 4, goes behind an escape. `oB` undoes `bitsToBytes`, not `toBytes`: `oBitsAt (oB (g ()))`
need not agree with g at a string that is not plain.

Not claimed. That `oOf g` is uniform where g is. Nothing on any hash function; nothing on soundness;
no probability.

Terms: lean/GLOSSARY.md.

-/
import Run.OracleBitsAt
import Run.OCompM
import Run.ParserHashProofs

set_option autoImplicit false

namespace Run
open Rom

/-- At the format's realised oracle it is `Run.oBits`. -/
theorem oBitsAt_oracle : oBitsAt _root_.Fmt.oracle = oBits := rfl

/-- At the bits of a plain byte string it is O's answer at that string. -/
theorem oBitsAt_bytes (O : ByteArray → ByteArray) (b : ByteArray)
    (h : plainB (bytesToBits b) = true) : oBitsAt O () (bytesToBits b) = bytesToDig (O b) := by
  show bytesToDig (O (toBytes (bytesToBits b))) = _
  rw [toBytes_plain _ h, bitsToBytes_bytesToBits]

/-- A function on byte strings that gives g: it undoes `toBytes` by choice. At a byte string that
`toBytes` does not reach it is g's answer at some bit string, of which nothing is said. -/
noncomputable def oOf (g : Fam (rom 256)) : ByteArray → ByteArray :=
  fun b => digToBytes (g () (Function.invFun (α := List Bool) toBytes b))

/-- It gives g. -/
theorem oBitsAt_oOf (g : Fam (rom 256)) : oBitsAt (oOf g) = g := by
  funext u s
  cases u
  show bytesToDig (digToBytes (g () (Function.invFun (α := List Bool) toBytes (toBytes s)))) =
    g () s
  rw [Function.leftInverse_invFun (fun a b h => toBytes_inj a b h) s]
  exact TieTree.bytes_dig _

/-- Its answers have 32 bytes. -/
theorem size_oOf (g : Fam (rom 256)) (b : ByteArray) : (oOf g b).size = 32 := size_digToBytes _

/-- Every function on bit strings is `oBitsAt O` for some O: so "at every O" and "at every g" are
one. -/
theorem forall_oBitsAt (p : Fam (rom 256) → Prop) : (∀ O, p (oBitsAt O)) ↔ ∀ g, p g :=
  ⟨fun h g => oBitsAt_oOf g ▸ h (oOf g), fun h _ => h _⟩

/-- At a plain byte string it is `Run.oB (g ())`. -/
theorem oOf_plain (g : Fam (rom 256)) (b : ByteArray) (h : plainB (bytesToBits b) = true) :
    oOf g b = oB (g ()) b := by
  have e : toBytes (bytesToBits b) = b := by rw [toBytes_plain _ h, bitsToBytes_bytesToBits]
  show digToBytes (g () (Function.invFun (α := List Bool) toBytes b)) = _
  conv_lhs => rw [← e]
  rw [Function.leftInverse_invFun (fun a b h => toBytes_inj a b h) (bytesToBits b)]
  rfl

/-- The format's hash over `oOf g` is the format's hash over `Run.oB (g ())`. -/
theorem HO_oOf (g : Fam (rom 256)) : _root_.Fmt.HO (oOf g) = _root_.Fmt.HO (oB (g ())) := by
  funext n t i st bs
  unfold _root_.Fmt.HO
  rw [oOf_plain g _ (plain_oStr 0 n t i st bs (Or.inl rfl)),
    oOf_plain g _ (plain_oStr 1 n t i st bs (Or.inr rfl))]

/-- The function on byte strings that `Run.oB` makes of g gives g at plain strings. -/
theorem oBitsAt_oB (g : Fam (rom 256)) (s : List Bool) (h : plainB s = true) :
    oBitsAt (oB (g ())) () s = g () s := by
  show bytesToDig (digToBytes (g () (bytesToBits (toBytes s)))) = g () s
  rw [bits_toBytes_plain s h]
  exact TieTree.bytes_dig _

end Run

#print axioms Run.oBitsAt_oracle
#print axioms Run.oBitsAt_bytes
#print axioms Run.oBitsAt_oOf
#print axioms Run.size_oOf
#print axioms Run.forall_oBitsAt
#print axioms Run.oOf_plain
#print axioms Run.HO_oOf
#print axioms Run.oBitsAt_oB
