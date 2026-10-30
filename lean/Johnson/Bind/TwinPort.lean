-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/TwinPort.lean: tests that hold the OOD answers of the committer that runs
(Johnson/Bind/Twin.lean) against the text with which this library's verifier on bytes checks such
answers. Tests alone: each is a #guard, which Lean's evaluator runs when the file is compiled; a
#guard leaves no theorem.

Why. The format's known answers have none for an OOD answer, and the small stored example's random
values are not stored. The verifier on bytes (OnBytes/) lays, for the answer i, a row of
coefficients on a folded message (`OnBytes.foldeqRecordRow`, OnBytes/Iop/Foldeq.lean): (`Tensor.eq`
seed.z).entry p before the pads, beta times 1, X, X^2 on the three pads of the answer i, 0 on the
other pads; and it reads the answer of the row r under the seed i at the place r · answers + i. By
this library's README.md that verifier follows the source text of the verifier of the programs (the
C++ implementation that comes with this Lean code) and reads the real files.
What is tested, at small shapes:
   1. `eqAt z p` is (`Tensor.eq` z).entry p at every place p of a cube, and `eqTable` is
      `OnBytes.eqTable`: so bit t of the place goes with the coordinate t in both;
   2. each answer of the committer, at the place r · s + i, is the sum of these coefficients times
      the row's message, computed with the verifier's own field operations;
   3. negative tests: with the point's coordinates reversed, with the pads of another answer, or
      with the places of row and answer swapped, the two part.
   4. the table's name, the OOD seeds and the commitment ID: the committer's are those of
      `OnBytes.Key.nameOf`, `seedsOf`, `commitmentId` (OnBytes/Key/Table.lean) and of
      `OnBytes.TwoPort.M.Key.commitmentId`, the text with which Johnson/RunOne/AskKey.lean tests
      that a table's ID is the user's ("claim 3"; Ask/KeyCompiledSmall.lean starts that run); at the
      three small shapes and at the small stored example's root and answers, with two negative
      tests;
   5. the small stored example's shape and the full size's meet the verifier's own conditions on a
      table's shape (`OnBytes.Params.IndexShape.ok`); a shape without a plain entry does not.
Limits. The coefficients are written here after `foldeqRecordRow`'s text; that function itself is
not called (it returns a row on an oracle message, not a value). Under 1 to 3 no OOD answer was
computed by the programs. Under 4 the small stored example's root, answers and commitment ID are the
programs'. These are read from Johnson/Bind/TwinAnchor.lean, which holds bytes copied from the
repository's examples/accepted-proof: one run of the programs' committer on a small synthetic model
(weights from a generator). No real model's weights enter.

-/
import Johnson.Bind.TwinKnown
import Johnson.Bind.TwinAnchor
import OnBytes.Iop.Foldeq
import OnBytes.ChecksWithHashAsArgument.M.Key.Table

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Twin
namespace Port

open Fmt (Ext)
open OnBytes (E)

/-- A point of three coordinates. -/
def zs : List Ext := [(3, 5, 7), (11, 13, 17), (19, 23, 29)]

/-- The verifier's equality vector at a point. -/
def under (z : List Ext) : OnBytes.Tensor := OnBytes.Tensor.eq (z.map E.ofTriple)

#guard (List.range 8).all fun p => ((under zs).entry p).triple == eqAt zs p
#guard (OnBytes.eqTable (zs.map E.ofTriple)).toList.map E.triple == (eqTable zs 8).toList
-- negative test: the coordinates reversed
#guard !(List.range 8).all fun p => ((under zs.reverse).entry p).triple == eqAt zs p

/-- The coefficient of the verifier's row for the answer i at the place q of a row's message: j is
the answer whose pads get the factor (the verifier lays j := i). -/
def coefficient (S : Shape) (seed : List Ext × Ext) (j q : Nat) : E :=
  if q < S.plain then (under seed.1).entry q
  else if (q - S.plain) / 3 == j then
    OnBytes.mulE (E.ofTriple seed.2) (OnBytes.thetaE ((q - S.plain) % 3))
  else OnBytes.zeroE

/-- The sum of the coefficients times the message of the row b. -/
def byRow (S : Shape) (T : Table) (seed : List Ext × Ext) (j b : Nat) : Ext :=
  ((Fmt.numbered 0 (message S T b)).foldl
    (fun acc w => OnBytes.maddS acc w.2 (coefficient S seed j w.1)) OnBytes.zeroE).triple

/-- Every answer of the commitment at S, read at place(r, i), is the verifier's sum at the pads of
the answer pads(i). -/
def agrees (S : Shape) (place : Nat → Nat → Nat) (pads : Nat → Nat) : Bool :=
  let o := commit S Known.files Known.toy
  (List.range S.rows).all fun r => (Fmt.numbered 0 o.seeds).all fun w =>
    o.answers.getD (place r w.1) Fmt.Fld.zeroE == byRow S Known.toy w.2 (pads w.1) r

#guard [Known.shapeA, Known.shapeB, Known.shapeC].all fun S => agrees S (fun r i => r * S.s + i) id
-- negative tests, at the shape with two seeds: another answer's pads; row and answer swapped
#guard !agrees Known.shapeB (fun r i => r * 2 + i) (fun i => 1 - i)
#guard !agrees Known.shapeB (fun r i => i * 8 + r) id

/-! ### The name, the seeds and the ID -/

/-- The shape as the verifier on bytes has it. -/
def indexShape (S : Shape) : OnBytes.Params.IndexShape := ⟨⟨S.a, S.l, S.r⟩, S.v, S.s, S.sigma⟩

/-- The verifier's name, seeds and two texts of the commitment ID, at a root and answers, are those
of o. -/
def closes (S : Shape) (cfg : ByteArray) (o : Out) : Bool :=
  let t : OnBytes.Params.TableName := ⟨o.root, o.answers.map E.ofTriple⟩
  Fmt.hex (OnBytes.Key.nameOf (indexShape S) cfg t) == Fmt.hex o.name &&
    ((OnBytes.Key.seedsOf (indexShape S) cfg t).getD []).map
      (fun y => (y.1.map E.triple, y.2.triple)) == o.seeds &&
    Fmt.hex (OnBytes.Key.commitmentId (indexShape S) cfg t) == Fmt.hex o.id &&
    Fmt.hex (Id.run (OnBytes.TwoPort.M.Key.commitmentId (m := Id) Fmt.formatHash (indexShape S) cfg t)) ==
      Fmt.hex o.id

#guard [Known.shapeA, Known.shapeB, Known.shapeC].all fun S =>
  closes S Known.cfgT (commit S Known.files Known.toy)

/-- The digest of the small stored example's public files. -/
def cfgS : ByteArray := Fmt.configDigest [Anchor.policy, Anchor.layout, Anchor.scales]

/-- The committer's last steps at the small stored example's root and answers. -/
def atAnchor : Out := close Anchor.shape cfgS Anchor.root fun _ => Anchor.stored

#guard closes Anchor.shape cfgS atAnchor && Fmt.hex atAnchor.id == Anchor.idTxt
-- the small stored example's shape and the full size's meet the verifier's conditions on a shape;
-- a shape without a plain entry does not
#guard (indexShape Anchor.shape).ok && (indexShape ⟨32, 402653184, 44040191, 11, 1, 40⟩).ok
#guard !(indexShape Known.shapeF).ok
-- negative tests: another shape on the verifier's side; another ID
#guard !closes { Anchor.shape with r := 65534 } cfgS atAnchor
#guard !closes Anchor.shape cfgS { atAnchor with id := atAnchor.root }

end Port
end Bind.Twin
