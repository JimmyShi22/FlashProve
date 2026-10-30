-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Shape/Lin.lean: THE SHARED CHAIN's SHAPE: what is left of the chain's state
(Johnson/Desc/K14/Text.lean: St) when every field element is left out: the type and the reader.
Definitions with code, and one small law.

What for. A verifier's step returns .ok where its guards on the structure pass and its tests on
values pass. The shape is for the first half: one Bool and one update on a shape that holds no
field element, so that it can be run without a proof. The other files of this folder do that for the
linear claim's eight sub-protocols in the shared chain. The 2 in Sh2 and sh2: the shared chain is
the second of the three chains of the IOP as written in Lean.

The type. Sh2 has two named fields. core: the shape of statement, book of trees and count of roots
(Johnson/Desc/Ground/Shape/Core.lean: CoreSh, which is general; its head lists its fields' types).
lin: the shape of what this kind notes (Lin): LinSh: psi, gU, gOmega, oU, oOmega, oSp, zFd, record :
Nat; lay : VectorLay (two Nat, one Bool); firstMask : Option Nat; seeds : List Nat. Each leaf field
of the state is read at most once. NO ELEMENT OF A FIELD: that is a reading of the types, no Lean
statement. A number can still be made of a value (a sampled location is a Nat). THAT NONE OF THESE
FIELDS HOLDS SUCH A NUMBER ALONG THE EIGHT IS A READING OF THREE LAWS; NO LEAN STATEMENT SAYS IT.
The three, with their premises. Where the key's sizes fit, the shape of the chain's first state is
that of a written example, whatever the key holds (Johnson/Desc/K14/Shape/Run.lean: first_shape).
Where what goes out with o_u can be said (withU P.S = some sentU), the plan has two codes and the
kind's text makes its eight sub-protocols (Eight P), the shape behind a step of the eight that
returns .ok is a function with code of the plan, of sentU and of the shape in front (Run.lean:
stepCarries; from border to border: Johnson/Desc/K14/Shape/End.lean: upTo_step). THE THREE DO NOT
MEET BY THEMSELVES: between the first state and the eight stands the front sub-protocol (number 0);
that it leaves the state is a reading too: no law here names it (Run.lean: updS). At a plan with one
code stepCarries and upTo_step say nothing.

LEFT OUT of the state: the columns not yet read (opened); a constraint's summands and target, and of
a message's sample constraints all but their number; the two values of a tree whose root is handed
in; the coordinates of the two points; the key's answers, its seeds' factors and the coordinates of
its seeds' points (their lengths are held), and its item.

WHAT THE SHAPE DOES NOT HOLD, THOUGH A LATER SUB-PROTOCOL OF THE CHAIN ASKS IT. The front of a
proximity test asks of ALL constraints that lie open on its group that each could be laid now
(Johnson/Desc/Ground/Ask.lean: openClaimsE). In front of the batching the test asks of these and of
the members' sample constraints that they can be combined (Johnson/Desc/K12/JoinGuarded.lean: combOk).
Sh2 does not hold that. For the first a mark stands beside the shape
(Johnson/Desc/Ground/Shape/Claims.lean; along the eight: Johnson/Desc/K14/Shape/Mark.lean).

Main names:
  LinSh, linSh        the shape of what the kind notes, and its reader
  Sh2, sh2            **the type and the reader**
  keyB, keyB_eq       the library's test that the key's sizes fit, on the shape

What is not claimed. No property of the protocol or of a program: nothing on soundness, on
completeness or on hiding.
-/
import Johnson.Desc.Ground.Shape.Core
import Johnson.Desc.K14.Text
import Johnson.Desc.Own.KeyTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Shape
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Ground (coreOf)
open VerifiableInference.Desc.Ground.Sh (CoreSh coreSh)
open VerifiableInference.Desc.Own (keyFits)

/-- **The shape of what the kind notes** (Lin): lengths and numbers. psi, zFd: how many coordinates
the two points have. Of the key: record: how many entries the array of its OOD answers holds (where
the key's sizes fit: rows × answers of the index's sizes: keyB); seeds: for each OOD seed, how many
coordinates its point has. -/
structure LinSh where
  psi : Nat
  gU : Nat
  gOmega : Nat
  oU : Nat
  lay : VectorLay
  firstMask : Option Nat
  oOmega : Nat
  oSp : Nat
  zFd : Nat
  record : Nat
  seeds : List Nat
  deriving DecidableEq, Repr

/-- The reader. oU and lay are read off one field of Lin (oU, a FoldedRow): its message's number and
its layout. -/
def linSh (l : Lin) : LinSh :=
  { psi := l.psiSh.length, gU := l.gU, gOmega := l.gOmega, oU := l.oU.oracle, lay := l.oU.lay
    firstMask := l.firstMask, oOmega := l.oOmega, oSp := l.oSp, zFd := l.zFd.length
    record := l.key.record.size, seeds := l.key.seeds.map (·.z.length) }

/-- **The shared chain's shape.** core: the shape of statement, book and count of roots; lin: the
shape of what the kind notes. -/
structure Sh2 where
  core : CoreSh
  lin : LinSh
  deriving DecidableEq, Repr

/-- **A state's shape.** -/
def sh2 (d : St) : Sh2 := { core := coreSh (coreOf d), lin := linSh d.loc }

/-- The key's sizes fit, on the shape. -/
def keyB (a : LinSh) (s : IndexShape) : Bool :=
  a.record == s.rows * s.answers && a.seeds.length == s.answers && a.seeds.all (· == s.cubeBits)

/-- It is the library's test on the key. -/
theorem keyB_eq (l : Lin) (s : IndexShape) : keyB (linSh l) s = keyFits l.key s := by
  unfold keyB keyFits
  show (l.key.record.size == _ && (l.key.seeds.map (·.z.length)).length == _ &&
    (l.key.seeds.map (·.z.length)).all (· == s.cubeBits)) = _
  rw [List.length_map, List.all_map]
  rfl

end Desc.K14.Shape

#print axioms Desc.K14.Shape.keyB_eq
