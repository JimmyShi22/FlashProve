-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/LookFreeAtHead.lean: UNDER THE HEAD P5J.AtMgA, AT ALL FIFTY ADDRESSES OF THE
LOOKUPS: THE LETTER look OF THE TABLE's RECORD (`lettersOf`, TabLetters.lean) IS A TERM IN THE
READER's STRUCTURE Zp.p.X IN WHICH NO TEST ON A TABLE AND NO TEST ON THE PADDING IS RUN. One short
second text, tied by a law; two general laws; a joining with LettersSpentAtHead.lean. Nothing is
evaluated.

Why. `look_at_head` writes the letter as (Look.placeAt X l d).bind fun p => p.shape.map …. The shape
p.shape (Johnson/Desc/First/Look/LookKind.lean) is shapeOwn's value with the padding's numbers laid,
behind two tests: shapeOwn's first line asks every call's own tests, which walk the calls' tables;
pubOk asks the padding's numbers. Whoever evaluates the letter pays for both. But that p.shape
returns comes by law under the head (`site_is_at`: from the members' own tests on the plan). Where a
text with a guard in front returns, the text without the guard returns the same.

Main names.
* `shapeFree calls lid`: shapeOwn's text (Johnson/Desc/First/Look/ShapeOwn.lean) less its first
  line. `shapeFree_of_own`: shapeOwn calls lid = some h0 gives shapeFree calls lid = some h0.
  `shape_free`: p.shape = some hS gives (shapeFree p.calls p.lid).map (fun h0 => { h0 with pub :=
  p.pub }) = some hS. All general.
* **`look_free_at_head`**: for l < 25 and both d: (lettersOf Zp G).look l d = (Look.placeAt Zp.p.X l
  d).bind fun p => (shapeFree p.calls p.lid).map fun h0 => ({ h0 with pub := p.pub }, p.first).

Limits. A SECOND TEXT of fourteen lines: tied one way only: from shapeOwn's return to shapeFree's:
if shapeOwn's text turns, Lean breaks the tie. shapeFree may return where shapeOwn refuses: it is no
test, and nothing may be read off its return alone. THE LINE THAT IS DROPPED IS ALSO THE ONE THAT
KEEPS THE POWERS OF TWO SMALL (the calls' own tests bound each call's numbers): without it 2 ^ … is
as large as the calls' numbers make it: harmless under the head, where the calls pass these tests by
law; whoever evaluates the right side at a structure of which that is not known has no such bound.
What an evaluation of the right side costs is not measured here. The six tests on numbers and
`places` are still run. That the head has a member is shown in scope, where the reader returns and
`protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at
two named sets of public files, in a side library. The full size alone. At the format's second hash
function. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.LettersSpentAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (placeAt shapeOwn places bitsFor)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

/-- shapeOwn's text (Johnson/Desc/First/Look/ShapeOwn.lean) less its first line, the tests on the
calls' own tables. -/
def shapeFree (calls : Array Call) (lid : Nat) : Option Forest.Shape :=
  let NC := calls.size
  let cK := bitsFor NC
  let dT := calls.foldl (fun m c => min m c.n) lid
  let kT := calls.foldl (fun m c => max m c.k) 0
  let iota := calls.map fun c => c.n - dT
  let NT := iota.foldl (fun s i => s + 2 ^ i) 0
  let rK := bitsFor NT
  if decide (1 ≤ NC) && decide (NC ≤ 16) && decide (10 ≤ dT) && decide (NT ≤ 256) &&
      decide (dT + rK < 32) && decide (2 ^ (kT + cK + 32) < pW.toNat) then
    (places NC NT iota).map fun x =>
      { calls, dT, kT, NT, rK, NC, cK, iota, first := x.1, callOf := x.2 }
  else none

/-- Where shapeOwn returns, the text without the tests on the tables returns the same. General. -/
theorem shapeFree_of_own {calls : Array Call} {lid : Nat} {h0 : Forest.Shape}
    (h : shapeOwn calls lid = some h0) : shapeFree calls lid = some h0 := by
  unfold shapeOwn at h
  split at h
  · cases h
  · exact h

/-- Where the lookup's numbers give a shape, it is the free text's with the padding's numbers laid:
neither the tests on the tables nor the tests on the padding are run. General. -/
theorem shape_free {p : VerifiableInference.Desc.First.Look.P} {hS : Forest.Shape}
    (h : p.shape = some hS) :
    (shapeFree p.calls p.lid).map (fun h0 => { h0 with pub := p.pub }) = some hS := by
  unfold VerifiableInference.Desc.First.Look.P.shape at h
  obtain ⟨h0, e0, e1⟩ := Option.bind_eq_some_iff.1 h
  rw [shapeFree_of_own e0, Option.map_some]
  split at e1
  · exact e1
  · cases e1

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **UNDER THE HEAD, AT ALL FIFTY ADDRESSES: THE LETTER look WITHOUT A TEST ON A TABLE.** -/
theorem look_free_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) (l : Nat)
    (hl : l < 25) (d : Bool) :
    (lettersOf Zp G).look l d =
      (placeAt Zp.p.X l d).bind fun p =>
        (shapeFree p.calls p.lid).map fun h0 => ({ h0 with pub := p.pub }, p.first) := by
  obtain ⟨s, -, -, -, -, f1, f2, -⟩ := site_is_at h l hl d
  rw [look_at_head h G l hl d, f1, Option.bind_some, Option.bind_some, f2]
  obtain ⟨h0, e0, e1⟩ := Option.map_eq_some_iff.1 (shape_free f2)
  rw [e0, Option.map_some, Option.map_some, e1]

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.shapeFree_of_own
#print axioms Johnson.AtFull.Shape.shape_free
#print axioms Johnson.AtFull.Shape.look_free_at_head
#print axioms Johnson.AtFull.Shape.shapeFree
