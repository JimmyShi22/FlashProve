-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/Toy.lean: the premises of Honest/SumLaw/Statement.lean, MET BY
EVALUATION at the three calls of Honest/SumToy.lean. Definitions with code and tests; no theorem.

What the lines show. (a) The rounds of `alone` are the rounds that the frame's own `play` yields for
the part. (b) The call's shape and the challenges pass `shapeOk` and `drawsOk`. (c) The caller's
premise `SumsTo`, as a test with code (`sumsToC`), accepts at each call: from a start value that is
computed apart (the true sum) to the end term: at the first and the third call the product of the
two end values that were shown; at the second, which has no end values, the summand's own value at
the challenge. Negative tests: from a false sum it rejects, at each call; to a false end term, at
the first call alone. AT THE FIRST CALL ALSO: (d) the ledger that Honest/SumToy.lean lays by hand
passes `LedgerReady`, as a test with code (`readyC`), and a ledger whose stated number of slots is
not its arrays' size does not; (e) the mask entries under the sumcheck's own slots are the coins
that the part spent; (f) the start value of (c) IS the hidden value of the claimed form on the
ledger that the verifier's text leaves; (g) the conclusions of `SumEnds` and `SumFirst`. That the
claim which is left is 0 stands in Honest/SumToy.lean's own lines, at the same coins and challenges.

Limits. Evaluations at fixed coins and challenges, with no columns handed (`Seen.bare`): none stands
at `opened = some …`. A `#guard` command is an evaluation by Lean's evaluator at compile time; it is
no theorem. (d) to (g) are held at the first call alone. `sumsToC` and `readyC` compare words below
the prime and marks; that they say what `SumsTo` and `LedgerReady` say is not shown here. Nothing on
any property.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.Statement
import Johnson.Desc.ProofFile.Honest.SumToy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw.Toy
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Slice (toE ofE)
open VerifiableInference.Desc.Part.MaskedSum (Var Call shapeOk valueAt)
open ProofFile.Honest.SumToy

/-- Two elements are read alike. -/
def same (a b : E) : Bool := ofE (toE a.triple) == ofE (toE b.triple)

/-- `SumsTo`, with code. -/
def sumsToC : List Var → (List E → List E) → List E → List E → E → E → Bool
  | [], _, _, [], c, c' => same c c'
  | v :: vs, poly, past, r :: rs, c, c' =>
    same (sumOf v (padTo v.d (poly past))) c &&
      sumsToC vs poly (past ++ [r]) rs (valueAt (padTo v.d (poly past)) r) c'
  | _, _, _, _, _, _ => false

/-- Coins of the extension field, of words. -/
def cs (n : Nat) (f : Nat → UInt64) : Cs ⟨0, n⟩ := ⟨fun i => i.elim0, fun i => toE (f i.val, 0, 0)⟩

/-- The scalars of a round. -/
def scal (r : Fmt.RoundView) : List E := r.vals.filterMap fun g =>
  match g with
  | .e x => some (E.ofTriple x)
  | _ => none

/-! ## The first call: a lead, two plain variables, two end values -/

def c₁' : SumCoins "mask to sum" "mask to ends" (job₁) :=
  (Cs.empty,
    (cs 8 fun i => 100 + 7 * i.toUInt64, (cs 2 fun i => 100 + 7 * (8 + i.toUInt64), ())), ())

def t₁ : State L Nat := ⟨wit, [], 0⟩

def r₁ : Option (List Fmt.RoundView) := alone sumP c₁' t₁ (.bare []) ds₁

-- (a) the rounds of `alone` are the rounds that `play` yields
#guard sig r₁ == sig (played sumP k₁ c₁ ds₁)
#guard r₁.isSome
-- (b)
#guard shapeOk k₁ && drawsOk k₁ ds₁
#guard varsOf k₁ ds₁ == [e 5, e 8, e 9] && epsOf ds₁ == e 11
-- (c) from the true sum to the product of the two SHOWN end values
def shown₁' : List E := ((r₁.getD []).getLast?.map scal).getD []
#guard sumsToC k₁.all (jobPoly job₁ wit (frontOf t₁ (.bare [])) (endRun c₁')) [] (varsOf k₁ ds₁)
  (trueSum tabs) (mulE (shown₁'.getD 0 zeroE) (shown₁'.getD 1 zeroE))
-- negative tests: from a false sum; to a false end term
#guard !sumsToC k₁.all (jobPoly job₁ wit (frontOf t₁ (.bare [])) (endRun c₁')) [] (varsOf k₁ ds₁)
  (addE (trueSum tabs) oneE) (mulE (shown₁'.getD 0 zeroE) (shown₁'.getD 1 zeroE))
#guard !sumsToC k₁.all (jobPoly job₁ wit (frontOf t₁ (.bare [])) (endRun c₁')) [] (varsOf k₁ ds₁)
  (trueSum tabs) (addE (mulE (shown₁'.getD 0 zeroE) (shown₁'.getD 1 zeroE)) oneE)

-- (d) the ledger behind the caller's taking of its lead is ready for the call
/-- `LedgerReady`, with code. -/
def readyC (C : OnBytes.Model.Aff) (k : Call) (n : Nat) (F : OnBytes.Model.Fork) : Bool :=
  let own := VerifiableInference.Desc.Part.MaskedSum.ownSlots k.all
  F.vp.size == F.ns && F.mf.size == F.ns && F.gotF.size == F.ns &&
    C.slots.toList.all (fun x => decide (x.1 < F.ns) && F.gotF.getD x.1 false) &&
    decide (F.next + own + n ≤ F.ns) &&
    (List.range (own + n)).all fun j => !F.gotF.getD (F.next + j) false
#guard ((r₁.bind ledger).map fun F => readyC (OnBytes.Model.Aff.slot 0) k₁ 2 F) == some true
-- the figures of that ledger: its three arrays have ten members, it states ten slots, the next is 1
#guard ((r₁.bind ledger).map fun F => (F.vp.size, F.mf.size, F.gotF.size, F.ns, F.next)) ==
  some (10, 10, 10, 10, 1)
-- a negative test on the sizes: a ledger whose stated number of slots is not its arrays' size is
-- not ready. AT 11 THE THREE CLAUSES ON THE SIZES ALONE REJECT: the clause on room holds there
-- (1 + 7 + 2 = 10 ≤ 11), the claimed form's slot 0 is below 11; no other clause reads the number
#guard ((r₁.bind ledger).map fun F =>
  readyC (OnBytes.Model.Aff.slot 0) k₁ 2 { F with ns := 11 }) == some false
-- at 9 it is not ready either; there the clause on room rejects too (10 ≤ 9 fails), so this line
-- does not tell the sizes' clauses from that one (the clauses on the number of slots, on the
-- claimed form's slots and on free slots: ToyLead.lean)
#guard ((r₁.bind ledger).map fun F =>
  readyC (OnBytes.Model.Aff.slot 0) k₁ 2 { F with ns := 9 }) == some false
-- (e) under the own slots 1 to 7 the mask entries are the first stretch's coins from number 1 on
#guard (List.range 7).all fun i =>
  same (maskOf (fun i => 100 + 7 * i.toUInt64) (1 + i)) ((firstRun c₁').getD (1 + i) zeroE)
-- (f) the start value of (c) is the claimed form's hidden value
#guard (r₁.bind (hiddenAt · (maskOf fun i => 100 + 7 * i.toUInt64) 0)).map (same · (trueSum tabs))
  == some true
-- (g) `SumEnds`: under the slots 8 and 9 lie the job's end values; `SumFirst`: the first scalar
-- is the lead's value plus its coin
#guard (List.range 2).all fun j =>
  (r₁.bind (hiddenAt · (maskOf fun i => 100 + 7 * i.toUInt64) (8 + j))).map
    (same · ((job₁.ends wit (frontOf t₁ (.bare [])) ((varsOf k₁ ds₁).take 2)).getD j zeroE))
        == some true
#guard ((r₁.getD []).head?.map scal).map (fun s => s.length == 2 &&
  same (s.getD 0 zeroE) (addE (trueSum tabs) ((firstRun c₁').getD 0 zeroE))) == some true

/-! ## The second call: one variable, summed at a point that is a challenge in front; no ends -/

def c₂' : SumCoins "mask to sum" "no ends" job₂ :=
  (Cs.empty, (cs 3 fun i => 40 + i.toUInt64, ()), ())

def t₂ : State L Nat := ⟨wit, [dE 9, dE 6], 0⟩

#guard sig
    (alone (sumPart (V := L) "mask to sum" "no ends" job₂) c₂' t₂ (.bare []) [dE 11, dE 5]) ==
  sig (played₂ [dE 9, dE 6] (fun i => 40 + i.toUInt64) [dE 11, dE 5])
#guard shapeOk (job₂.callAt wit (frontOf t₂ (.bare []))) &&
  drawsOk (job₂.callAt wit (frontOf t₂ (.bare []))) [dE 11, dE 5]
#guard sumsToC (job₂.callAt wit (frontOf t₂ (.bare []))).all
    (jobPoly job₂ wit (frontOf t₂ (.bare [])) (endRun c₂'))
    []
  (varsOf (job₂.callAt wit (frontOf t₂ (.bare []))) [dE 11, dE 5]) (sumAt (e 6)) (atL g₂ (e 5))
#guard !sumsToC (job₂.callAt wit (frontOf t₂ (.bare []))).all
    (jobPoly job₂ wit (frontOf t₂ (.bare []))
    (endRun c₂')) []
  (varsOf (job₂.callAt wit (frontOf t₂ (.bare []))) [dE 11, dE 5]) (sumAt (e 7)) (atL g₂ (e 5))

/-! ## The third call: a variable at a point in front of Y; two end values -/

def c₃' : SumCoins "mask to sum" "other to ends" job₃ :=
  (Cs.empty, (cs 5 fun i => 40 + i.toUInt64, (cs 2 fun i => 70 + i.toUInt64, ())), ())

def t₃ : State L Nat := ⟨wit, [dE 6], 0⟩
def ds₃ : List Fmt.Drawn := [dE 11, dE 5, dE 9, d0]
def r₃ : Option (List Fmt.RoundView) :=
  alone (sumPart (V := L) "mask to sum" "other to ends" job₃) c₃' t₃ (.bare []) ds₃
def shown₃' : List E := ((r₃.getD []).getLast?.map scal).getD []

#guard sig r₃ == sig (played₃ (fun i => 70 + i.toUInt64) (fun i => 40 + i.toUInt64) ds₃)
#guard shapeOk (job₃.callAt wit (frontOf t₃ (.bare []))) &&
    drawsOk (job₃.callAt wit (frontOf t₃ (.bare []))) ds₃
#guard sumsToC (job₃.callAt wit (frontOf t₃ (.bare []))).all
    (jobPoly job₃ wit (frontOf t₃ (.bare [])) (endRun c₃'))
    []
  (varsOf (job₃.callAt wit (frontOf t₃ (.bare []))) ds₃) (sumAt (e 6))
  (mulE (shown₃'.getD 0 zeroE) (shown₃'.getD 1 zeroE))
#guard !sumsToC (job₃.callAt wit (frontOf t₃ (.bare []))).all
    (jobPoly job₃ wit (frontOf t₃ (.bare []))
    (endRun c₃')) []
  (varsOf (job₃.callAt wit (frontOf t₃ (.bare []))) ds₃) (addE (sumAt (e 6)) oneE)
  (mulE (shown₃'.getD 0 zeroE) (shown₃'.getD 1 zeroE))

end ProofFile.Honest.SumLaw.Toy

#print axioms ProofFile.Honest.SumLaw.Toy.same
#print axioms ProofFile.Honest.SumLaw.Toy.sumsToC
#print axioms ProofFile.Honest.SumLaw.Toy.cs
#print axioms ProofFile.Honest.SumLaw.Toy.scal
#print axioms ProofFile.Honest.SumLaw.Toy.c₁'
#print axioms ProofFile.Honest.SumLaw.Toy.t₁
#print axioms ProofFile.Honest.SumLaw.Toy.r₁
#print axioms ProofFile.Honest.SumLaw.Toy.shown₁'
#print axioms ProofFile.Honest.SumLaw.Toy.readyC
#print axioms ProofFile.Honest.SumLaw.Toy.c₂'
#print axioms ProofFile.Honest.SumLaw.Toy.t₂
#print axioms ProofFile.Honest.SumLaw.Toy.c₃'
#print axioms ProofFile.Honest.SumLaw.Toy.t₃
#print axioms ProofFile.Honest.SumLaw.Toy.ds₃
#print axioms ProofFile.Honest.SumLaw.Toy.r₃
#print axioms ProofFile.Honest.SumLaw.Toy.shown₃'
