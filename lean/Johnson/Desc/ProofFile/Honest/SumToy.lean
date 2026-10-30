-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumToy.lean: the masked sumcheck's part and the part that sends its
mask row (Honest/Sum.lean), tested at toy examples against the verifier's own definition
(Johnson/Desc/Part/MaskedSum4.lean). Executable definitions and tests; no theorem.

The lines that begin with `#guard` are tests, checked by evaluation: Lean's evaluator runs each of
them when the file is compiled, and the build fails if one is false. The kernel does not check them,
and they prove nothing.

What is tested. The parts' rounds are prepared by `Part.steps`, their coins are given by `lendPart`
at a small book, and they are played by `play` (all three: Honest/Frame.lean). The rounds, as a view
shows them, go to the verifier's `whole` (or `hear` and `row`). The one claim that is left, a form
on hidden values, is evaluated on the ledger that the verifier's definition leaves and on the run's
own coins (the hidden value under a slot is what was shown less the factor times the mask entry): it
is 0. With one of the mask entries that the claim names changed (the lead's; the hiding polynomial's
coefficients), with a sent scalar changed, with a false lead: it is not. The end values' mask
entries are not named by that claim: with one of them changed it stays 0; that each is under its own
slot is checked by the hidden values there. The sent scalars of two calls are also compared with
written numbers.

Three calls. The first: a product of two tables over two variables that are summed plainly, with a
lead and two end values. The second: one variable that is summed at a point, which is a challenge
drawn before the part, without a lead and without ends (once more with a summand that reads, at a
later move, the challenges heard before the part and what was passed on). The third: the same before
Y, with two end values whose block is another owner's.

The book: the owner's row; two entries by which the sumcheck spends the first entries of the mask
row; one by which a part after it carries the whole row. Its tests pass, at places of the
description of Johnson/Desc/BlockToy.lean; which entries `Good.fresh` (Honest/Side.lean) reads is
tested too. The two sides: each fits; at coins that are chosen to fit the simulator outputs what the
part shows; at others not.

Limits.
  * No description is run here: the parts are played alone, at rounds built from the call's own
    entries; the book's addresses are places of the description of Johnson/Desc/BlockToy.lean, whose
    sub-protocols these parts are not; these books state no cut, so `run` would take none of them.
  * The ledger before a call, which is the caller's duty, is written by hand.
  * The mask row's code is a toy example's.
  * Evaluations at fixed coins and challenges.
  * Every state of a run that is laid here by hand has `none` as its columns opened, but for the one
    that is set beside `tells` (`mid₁`, in `shown₁` and `shownM`), which has `some []` (two lines
    test that value against the empty `Before`, at two lists of rounds; that it is so at every list
    rests on reading `readsBefore`, Honest/Side.lean, not on a test): the tests stand where no
    column is handed or none is opened yet, and say nothing where columns are. No part here reads
    them.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Sum
import Johnson.Desc.BlockToy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumToy
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Aff Fork)
open OnBytes.Slice (toE)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.Part.MaskedSum (Var Call entries whole hear row)

/-! ## Helpers -/

def e (n : UInt64) : E := ⟨n, 0, 0⟩

/-- The product of two polynomials. -/
def mulL : List E → List E → List E
  | [], _ => []
  | x :: a, b => addL (scaleL x b) (zeroE :: mulL a b)

/-- The line through t0 at 0 and t1 at 1. -/
def lin (t0 t1 : E) : List E := [t0, subE t1 t0]

/-- Two tables on two bits: the entry at (x1, x2) has the number 2 x1 + x2. -/
structure Tabs where
  a : Nat → E
  b : Nat → E

abbrev L : Type := Local Tabs Unit Nat Unit

def tabs : Tabs := ⟨fun i => e (3 + 2 * i.toUInt64), fun i => e (1 + 5 * i.toUInt64)⟩
def wit : L := ⟨tabs, (), 0, ()⟩

/-- A table with its first variable at r: the entry at x2. -/
def at1 (t : Nat → E) (r : E) (x2 : Nat) : E := addE (t x2) (mulE r (subE (t (2 + x2)) (t x2)))
/-- At both. -/
def at2 (t : Nat → E) (r1 r2 : E) : E :=
  addE (at1 t r1 0) (mulE r2 (subE (at1 t r1 1) (at1 t r1 0)))

def dE (x : UInt64) : Fmt.Drawn := ⟨[(x, 0, 0)], [], [], none⟩
/-- A challenge with all three coordinates. -/
def dE3 (x y z : UInt64) : Fmt.Drawn := ⟨[(x, y, z)], [], [], none⟩
def d0 : Fmt.Drawn := ⟨[], [], [], none⟩

/-! ## The first call: a product, two plain variables, a lead, two end values -/

def k₁ : Call := ⟨1, [.plain 3, .plain 3], some ⟨2, 2⟩⟩

/-- The sum of a(x) b(x) over the four points. -/
def trueSum (t : Tabs) : E :=
  (List.range 4).foldl (fun s i => addE s (mulE (t.a i) (t.b i))) zeroE

def job₁ (off : E := zeroE) : SumJob L Nat :=
  { shape := k₁, points := fun _ _ => []
    lead := fun w _ => [addE (trueSum w.w₀) off]
    round := fun w _ rs =>
      match rs with
      | [] => addL (mulL (lin (w.w₀.a 0) (w.w₀.a 2)) (lin (w.w₀.b 0) (w.w₀.b 2)))
          (mulL (lin (w.w₀.a 1) (w.w₀.a 3)) (lin (w.w₀.b 1) (w.w₀.b 3)))
      | r :: _ =>
        mulL (lin (at1 w.w₀.a r 0) (at1 w.w₀.a r 1)) (lin (at1 w.w₀.b r 0) (at1 w.w₀.b r 1))
    inY := fun w _ rs m =>
      mulL [at2 w.w₀.a (rs.getD 0 zeroE) (rs.getD 1 zeroE), m.getD 0 zeroE]
        [at2 w.w₀.b (rs.getD 0 zeroE) (rs.getD 1 zeroE), m.getD 1 zeroE]
    ends := fun w _ rs =>
      [at2 w.w₀.a (rs.getD 0 zeroE) (rs.getD 1 zeroE),
        at2 w.w₀.b (rs.getD 0 zeroE) (rs.getD 1 zeroE)] }

#guard scalarsOf k₁ == [2, 2, 2, 2, 2] && runOf k₁ == 10 && ownRun k₁ == 8

/-! ## The book -/

/-- Three places of the second chain of the description of Johnson/Desc/BlockToy.lean: the owner's,
the spender's, a carrier's. -/
def pM : Place := ⟨3, some 0, 4, .K1⟩
def pS : Place := ⟨3, some 0, 6, .K10⟩
def pC : Place := ⟨3, some 0, 7, .frame⟩
def aM : Addr := ⟨pM, 0⟩
def aS : Addr := ⟨pS, 0⟩
def aC : Addr := ⟨pC, 0⟩

/-- The mask row: eleven entries, of which the sumcheck spends ten, and a tail of two. -/
def mask : MaskJob :=
  { ell := 11, tail := 2, logLength := 2
    code := fun m t p => valueOf (m ++ t) (e (p.toUInt64 + 1))
    answer := fun m t z => valueOf (m ++ t) z }
where
  valueOf (l : List E) (x : E) : E := l.foldr (fun c r => addE (mulE r x) c) zeroE

abbrev Bs : ProverCoinCounts :=
  { first := [], shared := [], second := [(aM, ⟨0, 13⟩)]
    ahead := [⟨"mask to sum", aM, ⟨0, 0⟩, ⟨0, 8⟩, aS, true⟩,
      ⟨"mask to ends", aM, ⟨0, 8⟩, ⟨0, 2⟩, aS, true⟩,
      ⟨"mask to close", aM, ⟨0, 0⟩, ⟨0, 11⟩, aC, false⟩]
    cuts := [] }

/-- A run's coins: the mask row's coin number i is f i, by its three coordinates. -/
def coinsS3 (f : Nat → UInt64 × UInt64 × UInt64) : Coins Bs :=
  ⟨(), (), (⟨fun i => i.elim0, fun i => toE (f i.val)⟩, ())⟩

/-- The same in the base field. -/
def coinsS (f : Nat → UInt64) : Coins Bs := coinsS3 fun i => (f i, 0, 0)

/-- Thirteen coins, all different. -/
def c₁ : Coins Bs := coinsS fun i => 100 + 7 * i.toUInt64

-- the book's tests pass: the block is spent once; the carrier is after the spender
#guard Bs.word VerifiableInference.Desc.BlockToy.F == none
-- the carrier before the spender: the eighth test fails
#guard ({ Bs with ahead := [⟨"mask to sum", aM, ⟨0, 0⟩, ⟨0, 8⟩, aC, true⟩,
    ⟨"mask to close", aM, ⟨0, 0⟩, ⟨0, 11⟩, aS, false⟩] } : ProverCoinCounts).word
      VerifiableInference.Desc.BlockToy.F ==
  some "a coin that a part spends is handed to a part in front of it, or to itself as carried"
-- which entries `Good.fresh` reads at the owner, for the sumcheck: it spends the two blocks;
-- nothing else of the owner's is given to it or to a part before it; for the carrier: all three
#guard (Bs.spentBy aM aS).map (·.name) == ["mask to sum", "mask to ends"]
#guard (Bs.knownBy (orderOf VerifiableInference.Desc.BlockToy.F) aM aS).map (·.name) == []
#guard (Bs.knownBy (orderOf VerifiableInference.Desc.BlockToy.F) aM aC).map (·.name) ==
  ["mask to sum", "mask to ends", "mask to close"]

/-! ## The play -/

def sumP (off : E := zeroE) : Part L L Nat := sumPart "mask to sum" "mask to ends" (job₁ off)

/-- The call's rounds, built from its own entries. -/
def decls (k : Call) : List (Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle) :=
  (entries k).map fun x => ({ entry := x }, [])

/-- The part's rounds as a view shows them: its coins given by the book, its rounds played, from a
state with no round shown and no column handed (`none`). -/
def played (p : Part L L Nat) (k : Call) (c : Coins Bs) (ds : List Fmt.Drawn) :
    Option (List Fmt.RoundView) :=
  (lendPart Bs (Bs.rowsOf 2) (c.look 2) aS p).toOption.bind fun h =>
    (play (p.steps "sum" aS (decls k) none h) ds []
      ⟨⟨wit, [], 0⟩, [], [], none⟩).toOption.map fun y =>
      roundsOf y.1

/-- Rounds, for a comparison. -/
def sig (x : Option (List Fmt.RoundView)) : Option (List (List Fmt.ItemValue × Fmt.Drawn)) :=
  x.map (·.map fun r => (r.vals, r.drawn))

def ds₁ : List Fmt.Drawn := [dE 11, dE 5, dE 8, dE 9, d0]

/-- The mask entry under a slot: the coin of that number among the run's coins. The first block's
eight are under the slots 0 to 7, the end values' two under 8 and 9. -/
def maskOf (f : Nat → UInt64) (j : Nat) : E := e (f j)

/-- A form on hidden values, on a ledger and mask entries. A slot beyond the ledger counts as shown
0 with factor 0. -/
def formAt (G : Fork) (m : Nat → E) (f : Aff) : E :=
  f.slots.foldl (fun v x =>
    addE v (mulE x.2 (subE (G.vp.getD x.1 zeroE) (mulE (G.mf.getD x.1 zeroE) (m x.1))))) f.const

/-- The ledger after the caller has taken its lead, written by hand here, as a caller would: ten
slots; the lead under slot 0, as shown, with the factor 1; the next slot is 1. -/
def ledger (rs : List Fmt.RoundView) : Option Fork :=
  match rs.head?.bind fun r => r.vals.head? with
  | some (.e x) =>
    ((({} : Fork).slots 10).hide 0 (E.ofTriple x) oneE).map fun F => { F with next := 1 }
  | _ => none

/-- What the verifier's definition leaves, evaluated: the claimed sum is the hidden value under
slot 0. -/
def left (rs : List Fmt.RoundView) (m : Nat → E) : Option E :=
  (ledger rs).bind fun F =>
    (whole (Aff.slot 0) k₁ (fun _ sh => mulE (sh.getD 0 zeroE) (sh.getD 1 zeroE)) F rs).map fun y =>
      formAt y.2.2 m y.2.1

/-- The hidden value under a slot, on the ledger that the verifier's definition leaves. -/
def hiddenAt (rs : List Fmt.RoundView) (m : Nat → E) (j : Nat) : Option E :=
  (ledger rs).bind fun F =>
    (whole (Aff.slot 0) k₁ (fun _ sh => mulE (sh.getD 0 zeroE) (sh.getD 1 zeroE)) F rs).map fun y =>
      formAt y.2.2 m (Aff.slot j)

/-- The scalars of rounds, by their first coordinates. -/
def firsts (x : Option (List Fmt.RoundView)) : Option (List (List UInt64)) :=
  x.map (·.map fun r => r.vals.filterMap fun g =>
    match g with
    | .e y => some y.1
    | _ => none)

-- the part has five rounds, which send two scalars each
#guard (played sumP k₁ c₁ ds₁).map (·.map (·.vals.length)) == some [2, 2, 2, 2, 2]
-- the ten scalars, written: the honest prover of the format's page (docs/format/11-1-machinery.md),
-- computed by sums over all points and interpolation
#guard firsts (played sumP k₁ c₁ ds₁) ==
  some [[354, 1259], [882, 994], [13038, 238], [226225, 279857], [1443, 1558]]
-- the verifier's definition accepts them, and the claim that it leaves is 0 on the run's own coins
#guard (played sumP k₁ c₁ ds₁).bind (left · (maskOf fun i => 100 + 7 * i.toUInt64)) == some zeroE
-- at other challenges too
#guard (played sumP k₁ c₁ [dE 2, dE 4, dE 1, dE 3, d0]).bind
  (left · (maskOf fun i => 100 + 7 * i.toUInt64)) == some zeroE
-- at coins and challenges with all three coordinates
#guard (played sumP k₁ (coinsS3 fun i => (100 + 7 * i.toUInt64, i.toUInt64 + 1, 2 * i.toUInt64 + 3))
    [dE3 11 2 3, dE3 5 1 4, dE3 8 6 2, dE3 9 7 5, d0]).bind
  (left · fun i => ⟨100 + 7 * i.toUInt64, i.toUInt64 + 1, 2 * i.toUInt64 + 3⟩) == some zeroE
-- at the coins 0
#guard (played sumP k₁ (coinsS fun _ => 0) ds₁).bind (left · fun _ => zeroE) == some zeroE
-- each of the eight entries that the claim names matters (the lead's; H's seven coefficients):
-- evaluated with that one mask entry changed, the claim is not 0. The end values' two are not named
-- by it: that an end value is the map's value at the point is a further claim of the caller's
#guard (List.range 8).all fun j =>
  ((played sumP k₁ c₁ ds₁).bind
    (left · (maskOf fun i => 100 + 7 * i.toUInt64 + (if i == j then 1 else 0)))).any (· != zeroE)
#guard (List.range 2).all fun j =>
  (played sumP k₁ c₁ ds₁).bind
    (left · (maskOf fun i => 100 + 7 * i.toUInt64 + (if i == 8 + j then 1 else 0))) == some zeroE
-- the end values' entries are each under its own slot: the hidden values under the slots 8 and 9
-- are the two tables' true values at the point (39 and 91)
#guard (played sumP k₁ c₁ ds₁).bind (hiddenAt · (maskOf fun i => 100 + 7 * i.toUInt64) 8) ==
  some (at2 tabs.a (e 5) (e 8))
#guard (played sumP k₁ c₁ ds₁).bind (hiddenAt · (maskOf fun i => 100 + 7 * i.toUInt64) 9) ==
  some (at2 tabs.b (e 5) (e 8))
#guard at2 tabs.a (e 5) (e 8) == e 39 && at2 tabs.b (e 5) (e 8) == e 91
-- what is sent changes with each of the ten; the eleventh entry and the tail are not read
#guard (List.range 10).all fun j => sig (played sumP k₁ c₁ ds₁) !=
  sig (played sumP k₁ (coinsS fun i => 100 + 7 * i.toUInt64 + (if i == j then 1 else 0)) ds₁)
#guard sig (played sumP k₁ c₁ ds₁) ==
  sig (played sumP k₁ (coinsS fun i => if i < 10 then 100 + 7 * i.toUInt64 else 0) ds₁)
-- a false lead (the sum plus 1): the definition accepts the rounds; the claim is not 0
#guard ((played (sumP oneE) k₁ c₁ ds₁).bind
  (left · (maskOf fun i => 100 + 7 * i.toUInt64))).any (· != zeroE)
-- a sent scalar changed, each of the ten in turn: not 0
def turn (rs : List Fmt.RoundView) (i j : Nat) : List Fmt.RoundView :=
  rs.zipIdx.map fun r => if r.2 != i then r.1 else
    { r.1 with vals := r.1.vals.zipIdx.map fun g => if g.2 != j then g.1 else
        match g.1 with
        | .e x => .e (x.1 + 1, x.2)
        | y => y }
#guard (List.range 5).all fun i => (List.range 2).all fun j =>
  ((played sumP k₁ c₁ ds₁).bind fun rs =>
    left (turn rs i j) (maskOf fun i => 100 + 7 * i.toUInt64)).any (· != zeroE)

/-! ## The second call: one variable, summed at a point that is a challenge drawn before the part -/

/-- The shape: the point is a placeholder. -/
def k₂ : Call := ⟨0, [.point zeroE 3], none⟩
/-- The call as the verifier has it, at a point. -/
def k₂At (z : E) : Call := ⟨0, [.point z 3], none⟩

def atL (g : List E) (x : E) : E := g.foldr (fun c r => addE (mulE r x) c) zeroE

/-- a(x) b(x) on the first two entries. -/
def g₂ : List E := mulL (lin (tabs.a 0) (tabs.a 1)) (lin (tabs.b 0) (tabs.b 1))

/-- The point is the last challenge that was drawn before the part. -/
def job₂ : SumJob L Nat :=
  { shape := k₂, points := fun _ fr => [(drawnE fr.heard).getLastD zeroE], lead := fun _ _ => []
    round := fun _ _ _ => g₂, inY := fun _ _ _ _ => [], ends := fun _ _ _ => [] }

/-- (1 - z) g(0) + z g(1). -/
def sumAt (z : E) : E := addE (mulE (subE oneE z) (atL g₂ zeroE)) (mulE z (atL g₂ oneE))

abbrev B₂ : ProverCoinCounts := { Bs with ahead := [⟨"mask to sum", aM, ⟨0, 0⟩, ⟨0, 3⟩, aS, true⟩] }

/-- `front`: the challenges that the run has heard before the part. -/
def played₂ (front : List Fmt.Drawn) (f : Nat → UInt64) (ds : List Fmt.Drawn) :
    Option (List Fmt.RoundView) :=
  let p : Part L L Nat := sumPart "mask to sum" "no ends" job₂
  let c : Coins B₂ := ⟨(), (), (⟨fun i => i.elim0, fun i => toE (f i.val, 0, 0)⟩, ())⟩
  (lendPart B₂ (B₂.rowsOf 2) (c.look 2) aS p).toOption.bind fun h =>
    (play (p.steps "sum" aS (decls k₂) none h) ds []
      ⟨⟨wit, front, 0⟩, front, [], none⟩).toOption.map
      fun y => roundsOf y.1

/-- `hear` at the point z, then `row` at the summand's true value at the challenge. `C`: the claimed
sum. -/
def left₂ (z C : E) (rs : List Fmt.RoundView) (r : E) (m : Nat → E) : Option E :=
  (hear (Aff.ofConst C) (k₂At z) (({} : Fork).slots 3) rs).bind fun y =>
    (row y.1 (atL g₂ r) {} y.2).map fun x => formAt x.2 m x.1

#guard runOf k₂ == 3 && ownRun k₂ == 3 && sumAt (e 6) == e 165
-- the three scalars, written (as at the first call), where 6 was drawn before the part
#guard firsts (played₂ [dE 9, dE 6] (fun i => 40 + i.toUInt64) [dE 11, dE 5]) ==
  some [[538], [228, 152]]
-- the verifier's definition at that point leaves 0
#guard (played₂ [dE 9, dE 6] (fun i => 40 + i.toUInt64) [dE 11, dE 5]).bind
  (left₂ (e 6) (sumAt (e 6)) · (e 5) (maskOf fun i => 40 + i.toUInt64)) == some zeroE
-- where 7 was drawn before: at the point 7: 0; at the point 6: not: the part follows the run
#guard (played₂ [dE 9, dE 7] (fun i => 40 + i.toUInt64) [dE 11, dE 5]).bind
  (left₂ (e 7) (sumAt (e 7)) · (e 5) (maskOf fun i => 40 + i.toUInt64)) == some zeroE
#guard ((played₂ [dE 9, dE 7] (fun i => 40 + i.toUInt64) [dE 11, dE 5]).bind
  (left₂ (e 6) (sumAt (e 6)) · (e 5) (maskOf fun i => 40 + i.toUInt64))).any (· != zeroE)
-- a false claimed sum: not 0
#guard ((played₂ [dE 9, dE 6] (fun i => 40 + i.toUInt64) [dE 11, dE 5]).bind
  (left₂ (e 6) (addE (sumAt (e 6)) oneE) · (e 5) (maskOf fun i => 40 + i.toUInt64))).any
    (· != zeroE)

/-! ### The summand too reads `Front`, at a later move -/

/-- The factor that the caller puts on its summand: the last challenge drawn before the part, plus
what was passed on. -/
def factorOf (fr : Front Nat) : E := addE ((drawnE fr.heard).getLastD zeroE) (e fr.own.toUInt64)

/-- As `job₂`, with the summand times that factor: `round`, which is asked at the part's second
move, reads `Front`: its challenges and what was passed on. -/
def job₄ : SumJob L Nat := { job₂ with round := fun _ fr _ => scaleL (factorOf fr) g₂ }

/-- `front`: as at `played₂`. `own`: what was passed on to the part. -/
def played₄ (front : List Fmt.Drawn) (own : Nat) (ds : List Fmt.Drawn) : Option (List Fmt.RoundView) :=
  let p : Part L L Nat := sumPart "mask to sum" "no ends" job₄
  let c : Coins B₂ := ⟨(), (), (⟨fun i => i.elim0, fun i => toE (40 + i.val.toUInt64, 0, 0)⟩, ())⟩
  (lendPart B₂ (B₂.rowsOf 2) (c.look 2) aS p).toOption.bind fun h =>
    (play (p.steps "sum" aS (decls k₂) none h) ds []
      ⟨⟨wit, front, own⟩, front, [], none⟩).toOption.map
      fun y => roundsOf y.1

/-- The verifier's definition at the point z, for the summand times f. -/
def left₄ (z f : E) (rs : List Fmt.RoundView) (r : E) : Option E :=
  (hear (Aff.ofConst (mulE f (sumAt z))) (k₂At z) (({} : Fork).slots 3) rs).bind fun y =>
    (row y.1 (mulE f (atL g₂ r)) {} y.2).map fun x =>
      formAt x.2 (maskOf fun i => 40 + i.toUInt64) x.1

-- 6 was drawn before and 3 was passed on: the factor is 9: the verifier's definition leaves 0. It
-- would not if the part's own first challenge, 11, were counted among those before: the factor 14
#guard (played₄ [dE 9, dE 6] 3 [dE 11, dE 5]).bind (left₄ (e 6) (e 9) · (e 5)) == some zeroE
#guard ((played₄ [dE 9, dE 6] 3 [dE 11, dE 5]).bind (left₄ (e 6) (e 14) · (e 5))).any (· != zeroE)
-- it follows what was passed on
#guard (played₄ [dE 9, dE 6] 4 [dE 11, dE 5]).bind (left₄ (e 6) (e 10) · (e 5)) == some zeroE
#guard ((played₄ [dE 9, dE 6] 4 [dE 11, dE 5]).bind (left₄ (e 6) (e 9) · (e 5))).any (· != zeroE)

/-! ## The third call: a variable at a point before Y; the end values' block is another owner's -/

def k₃ : Call := ⟨0, [.point zeroE 3], some ⟨2, 2⟩⟩
def k₃At (z : E) : Call := ⟨0, [.point z 3], some ⟨2, 2⟩⟩

/-- A table's first two entries, at r. -/
def at0 (t : Nat → E) (r : E) : E := addE (t 0) (mulE r (subE (t 1) (t 0)))

def job₃ : SumJob L Nat :=
  { shape := k₃, points := fun _ fr => [(drawnE fr.heard).getLastD zeroE], lead := fun _ _ => []
    round := fun _ _ _ => g₂
    inY := fun w _ rs m =>
      mulL [at0 w.w₀.a (rs.headD zeroE), m.getD 0 zeroE]
        [at0 w.w₀.b (rs.headD zeroE), m.getD 1 zeroE]
    ends := fun w _ rs => [at0 w.w₀.a (rs.headD zeroE), at0 w.w₀.b (rs.headD zeroE)] }

/-- A second owner, before the first: the place of `hear 1` in the description of
Johnson/Desc/BlockToy.lean. -/
def pN : Place := ⟨3, some 0, 1, .K4⟩
def aN : Addr := ⟨pN, 0⟩

/-- The first block is the mask row's; the end values' block is the second owner's. -/
abbrev B₃ : ProverCoinCounts :=
  { first := [], shared := [], second := [(aN, ⟨0, 2⟩), (aM, ⟨0, 13⟩)]
    ahead := [⟨"mask to sum", aM, ⟨0, 0⟩, ⟨0, 5⟩, aS, true⟩,
      ⟨"other to ends", aN, ⟨0, 0⟩, ⟨0, 2⟩, aS, true⟩]
    cuts := [] }

def played₃ (g f : Nat → UInt64) (ds : List Fmt.Drawn) : Option (List Fmt.RoundView) :=
  let p : Part L L Nat := sumPart "mask to sum" "other to ends" job₃
  let c : Coins B₃ := ⟨(), (), (⟨fun i => i.elim0, fun i => toE (g i.val, 0, 0)⟩,
    (⟨fun i => i.elim0, fun i => toE (f i.val, 0, 0)⟩, ()))⟩
  (lendPart B₃ (B₃.rowsOf 2) (c.look 2) aS p).toOption.bind fun h =>
    (play (p.steps "sum" aS (decls k₃) none h) ds []
      ⟨⟨wit, [dE 6], 0⟩, [dE 6], [], none⟩).toOption.map
      fun y => roundsOf y.1

/-- What the verifier's definition leaves at the point 6. -/
def whole₃ (rs : List Fmt.RoundView) :=
  whole (Aff.ofConst (sumAt (e 6))) (k₃At (e 6))
    (fun _ sh => mulE (sh.getD 0 zeroE) (sh.getD 1 zeroE)) (({} : Fork).slots 7) rs

/-- The mask entries by slot: five of the mask row, then the second owner's two. -/
def mask₃ (j : Nat) : E := if j < 5 then e (40 + j.toUInt64) else e (70 + (j.toUInt64 - 5))

#guard B₃.word VerifiableInference.Desc.BlockToy.F == none
#guard scalarsOf k₃ == [1, 2, 2, 2] && ownRun k₃ == 5
#guard ((played₃ (fun i => 70 + i.toUInt64) (fun i => 40 + i.toUInt64)
    [dE 11, dE 5, dE 9, d0]).bind whole₃).map (fun y => formAt y.2.2 mask₃ y.2.1) == some zeroE
-- the hidden values under the end values' slots are the tables' true values: so the second owner's
-- coins are what is put over them
#guard ((played₃ (fun i => 70 + i.toUInt64) (fun i => 40 + i.toUInt64)
    [dE 11, dE 5, dE 9, d0]).bind whole₃).map
      (fun y => (formAt y.2.2 mask₃ (Aff.slot 5), formAt y.2.2 mask₃ (Aff.slot 6))) ==
  some (at0 tabs.a (e 5), at0 tabs.b (e 5))
-- what is sent changes with the second owner's coin; not with the mask row's sixth
#guard sig (played₃ (fun i => 70 + i.toUInt64) (fun i => 40 + i.toUInt64) [dE 11, dE 5, dE 9, d0])
  != sig (played₃ (fun i => 71 + i.toUInt64) (fun i => 40 + i.toUInt64) [dE 11, dE 5, dE 9, d0])
#guard sig (played₃ (fun i => 70 + i.toUInt64) (fun i => 40 + i.toUInt64) [dE 11, dE 5, dE 9, d0])
  == sig (played₃ (fun i => 70 + i.toUInt64) (fun i => if i < 5 then 40 + i.toUInt64 else 0)
    [dE 11, dE 5, dE 9, d0])

/-! ## The side -/

/-- A sub-protocol with the call's own rounds, which decides nothing: only to give the side its
form. -/
def sumBlock : Block Unit Nat :=
  { name := "sum", place := pS, planOk := true, rounds := (decls k₁).map (·.1)
    oracles := (decls k₁).map (·.2), before := [], decide := fun s _ _ => .ok s, claims := []
    after := [] }

def sumSide : Side Unit Nat L L Nat Nat :=
  { block := sumBlock, row := [(sumP, sumSim aS k₁)] }
def sumU : Member L L Nat Nat := ⟨0, decls k₁, sumP, sumSim aS k₁⟩

#guard sumSide.fits
#guard !sumP.plain && sumP.takes == ⟨0, 0⟩ && (sumSim (Pb := Nat) aS k₁).takes == ⟨0, 10⟩

/-- Ten coins of the extension field, from words. -/
def ten (f : Nat → UInt64 × UInt64 × UInt64) : Cs ⟨0, runOf k₁⟩ :=
  ⟨fun i => i.elim0, fun i => toE (f i.val)⟩

/-- The state that is set beside `tells` at the empty `Before`: no round shown, and `some []` as its
columns opened: the premise of `Good.exact` (Honest/Side.lean) asks just that there, whatever rounds
are declared. -/
def mid₁ : Mid L Nat := ⟨⟨wit, [], 0⟩, [], [], some []⟩

-- its field is what the empty `Before` holds for the reads of declared rounds: at no round, and at
-- a round that opens a tree
#guard mid₁.opened == (⟨[], []⟩ : Before).opened (readsBefore [] ⟨[], []⟩)
#guard mid₁.opened ==
  (⟨[], []⟩ : Before).opened (readsBefore
    [(1, 0, [{ entry := VerifiableInference.Desc.BlockToy.openA,
               opens := [(VerifiableInference.Desc.BlockToy.tree, .own 0)] }])] ⟨[], []⟩)

/-- What the part shows, played alone, at the two blocks that it spends: f's first eight; the next
two; from `mid₁`. -/
def shown₁ (f : Nat → UInt64) : Option (List Shown) :=
  sumSide.shows .own sumU
    (Cs.empty, ((⟨fun i => i.elim0, fun i => toE (f i.val, 0, 0)⟩ : Cs ⟨0, ownRun k₁⟩),
      ((⟨fun i => i.elim0, fun i => toE (f (8 + i.val), 0, 0)⟩ : Cs ⟨0, 2⟩), ())), ())
    mid₁ ds₁ [[], [], [], [], []]

-- played alone by the side it shows what `played` has
#guard (shown₁ fun i => 100 + 7 * i.toUInt64).map (·.map (·.vals)) ==
  (played sumP k₁ c₁ ds₁).map (·.map (·.vals))
-- the simulator, at the ten scalars that the part shows as its coins, outputs the same; at other
-- coins something else
def scalarsShown (f : Nat → UInt64) : List (UInt64 × UInt64 × UInt64) :=
  ((shown₁ f).getD []).flatMap fun s => s.vals.filterMap fun g =>
    match g with
    | .e x => some x
    | _ => none
#guard sumU.tells .own (ten fun i => (scalarsShown fun i => 100 + 7 * i.toUInt64).getD i (0, 0, 0))
  wit ⟨[], []⟩ ds₁ [[], [], [], [], []] == shown₁ fun i => 100 + 7 * i.toUInt64
#guard sumU.tells .own (ten fun _ => (0, 0, 0)) wit ⟨[], []⟩ ds₁ [[], [], [], [], []] !=
  shown₁ fun i => 100 + 7 * i.toUInt64

/-! ## The owner, and a carrier after the spender -/

def maskP : Part L L Nat := maskPart mask

/-- The owner's two rounds. -/
def maskDecls : List (Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle) :=
  [({ entry := { name := "SEND seed", msg := 32, roots := 1, drawE := 1, drawNZ := 1 } },
      [⟨2, 3, []⟩]),
    ({ entry := { name := "SEND answer", msg := 24, answers := 1 } }, [])]

def playedM (c : Coins Bs) (ds : List Fmt.Drawn) : Option (List Played) :=
  (lendPart Bs (Bs.rowsOf 2) (c.look 2) aM maskP).toOption.bind fun h =>
    (play (maskP.steps "mask" aM maskDecls none h) ds []
      ⟨⟨wit, [], 0⟩, [], [], none⟩).toOption.map (·.1)

-- it takes the book's thirteen coins, sends one table and then one answer
#guard maskP.takes == ⟨0, 13⟩ && maskP.plain
#guard (playedM c₁ [dE 4, d0]).map (·.map fun p => (p.vals.length, p.tables.length)) ==
  some [(0, 1), (1, 0)]
-- a symbol changes with an entry that the sumcheck spends, and with the tail
#guard (playedM c₁ [dE 4, d0]).map (·.map fun p => p.tables.map fun t => t.map (·.col 1)) !=
  (playedM (coinsS fun i => 100 + 7 * i.toUInt64 + (if i == 3 then 1 else 0)) [dE 4, d0]).map
    (·.map fun p => p.tables.map fun t => t.map (·.col 1))
#guard (playedM c₁ [dE 4, d0]).map (·.map fun p => p.tables.map fun t => t.map (·.col 1)) !=
  (playedM (coinsS fun i => 100 + 7 * i.toUInt64 + (if i == 12 then 1 else 0)) [dE 4, d0]).map
    (·.map fun p => p.tables.map fun t => t.map (·.col 1))

/-- A sub-protocol with the owner's two rounds, which decides nothing: only to give the side its
form. -/
def maskBlock : Block Unit Nat :=
  { name := "mask", place := pM, planOk := true, rounds := maskDecls.map (·.1)
    oracles := maskDecls.map (·.2), before := [], decide := fun s _ _ => .ok s, claims := []
    after := [] }

def maskSide : Side Unit Nat L L Nat Nat :=
  { block := maskBlock, row := [(maskP, maskSim aM mask)] }
def maskU : Member L L Nat Nat := ⟨0, maskDecls, maskP, maskSim aM mask⟩

/-- Thirteen coins of the extension field, from words; three. -/
def thirteen (f : Nat → UInt64) : Cs ⟨0, mask.ell + mask.tail⟩ :=
  ⟨fun i => i.elim0, fun i => toE (f i.val, 0, 0)⟩
def three (f : Nat → UInt64 × UInt64 × UInt64) : Cs ⟨0, 1 + mask.tail⟩ :=
  ⟨fun i => i.elim0, fun i => toE (f i.val)⟩

/-- What the owner shows, played alone, where its table is read at these positions; from `mid₁`. -/
def shownM (ps : List Nat) : Option (List Shown) :=
  maskSide.shows .own maskU (thirteen fun i => 100 + 7 * i.toUInt64, (), ())
    mid₁ [dE 4, d0] [[ps], []]

#guard maskSide.fits && (maskSim (Pb := Nat) aM mask).takes == ⟨0, 3⟩
-- it shows two columns of three words, and one answer
#guard (shownM [1, 3]).map (·.map fun s => (s.vals.length, s.cols.map (·.map fun c => c.2.length)))
  == some [(0, [[3, 3]]), (1, [])]
/-- What it shows, as three elements: the answer, then the symbols. -/
def threeShown (ps : List Nat) : List (UInt64 × UInt64 × UInt64) :=
  let l := (shownM ps).getD []
  (l.flatMap fun s => s.vals.filterMap fun g =>
    match g with
    | .answer x => some x
    | _ => none) ++
  (l.flatMap fun s => s.cols.flatMap fun c => c.map fun x =>
    (x.2.getD 0 0, x.2.getD 1 0, x.2.getD 2 0))
-- the simulator, at what the owner shows as its coins, outputs the same; at other coins something
-- else
#guard maskU.tells .own (three fun i => (threeShown [1, 3]).getD i (0, 0, 0)) wit ⟨[], []⟩
  [dE 4, d0] [[[1, 3]], []] == shownM [1, 3]
#guard maskU.tells .own (three fun _ => (0, 0, 0)) wit ⟨[], []⟩ [dE 4, d0] [[[1, 3]], []] !=
  shownM [1, 3]
-- at more distinct positions than the tail has coins it outputs `none`; a position that is
-- listed twice counts once
#guard (maskU.tells .own (three fun _ => (0, 0, 0)) wit ⟨[], []⟩ [dE 4, d0]
  [[[0, 1, 3]], []]).isNone
#guard (maskU.tells .own (three fun _ => (0, 0, 0)) wit ⟨[], []⟩ [dE 4, d0]
  [[[1, 3, 1]], []]).isSome

/-- A carrier after the spender: it is given the row's eleven entries as a carried block, and says
their sum. -/
def closeP : Part L L Nat :=
  { takes := ⟨0, 0⟩, spends := [], carries := [("mask to close", ⟨0, 11⟩)]
    bad := fun _ _ => none, hid := fun _ _ _ => none
    badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves := [⟨fun c _ _ => .ok (sayE [(coinsE c.2.2.1).foldl addE zeroE]), fun t => t.own⟩] }

-- `carriedAt` gives it the very entries that the sumcheck has spent, and the
-- eleventh
#guard ((carriedAt Bs c₁ 2 aC closeP).toOption.map fun c => coinsE c.1) ==
  some ((List.range 11).map fun i => e (100 + 7 * i.toUInt64))

end ProofFile.Honest.SumToy

#print axioms ProofFile.Honest.SumToy.e
#print axioms ProofFile.Honest.SumToy.mulL
#print axioms ProofFile.Honest.SumToy.lin
#print axioms ProofFile.Honest.SumToy.Tabs
#print axioms ProofFile.Honest.SumToy.L
#print axioms ProofFile.Honest.SumToy.tabs
#print axioms ProofFile.Honest.SumToy.wit
#print axioms ProofFile.Honest.SumToy.at1
#print axioms ProofFile.Honest.SumToy.at2
#print axioms ProofFile.Honest.SumToy.dE
#print axioms ProofFile.Honest.SumToy.dE3
#print axioms ProofFile.Honest.SumToy.d0
#print axioms ProofFile.Honest.SumToy.k₁
#print axioms ProofFile.Honest.SumToy.trueSum
#print axioms ProofFile.Honest.SumToy.job₁
#print axioms ProofFile.Honest.SumToy.pM
#print axioms ProofFile.Honest.SumToy.pS
#print axioms ProofFile.Honest.SumToy.pC
#print axioms ProofFile.Honest.SumToy.aM
#print axioms ProofFile.Honest.SumToy.aS
#print axioms ProofFile.Honest.SumToy.aC
#print axioms ProofFile.Honest.SumToy.mask
#print axioms ProofFile.Honest.SumToy.Bs
#print axioms ProofFile.Honest.SumToy.coinsS3
#print axioms ProofFile.Honest.SumToy.coinsS
#print axioms ProofFile.Honest.SumToy.c₁
#print axioms ProofFile.Honest.SumToy.sumP
#print axioms ProofFile.Honest.SumToy.decls
#print axioms ProofFile.Honest.SumToy.played
#print axioms ProofFile.Honest.SumToy.sig
#print axioms ProofFile.Honest.SumToy.ds₁
#print axioms ProofFile.Honest.SumToy.maskOf
#print axioms ProofFile.Honest.SumToy.formAt
#print axioms ProofFile.Honest.SumToy.ledger
#print axioms ProofFile.Honest.SumToy.left
#print axioms ProofFile.Honest.SumToy.hiddenAt
#print axioms ProofFile.Honest.SumToy.firsts
#print axioms ProofFile.Honest.SumToy.turn
#print axioms ProofFile.Honest.SumToy.k₂
#print axioms ProofFile.Honest.SumToy.k₂At
#print axioms ProofFile.Honest.SumToy.atL
#print axioms ProofFile.Honest.SumToy.g₂
#print axioms ProofFile.Honest.SumToy.job₂
#print axioms ProofFile.Honest.SumToy.sumAt
#print axioms ProofFile.Honest.SumToy.B₂
#print axioms ProofFile.Honest.SumToy.played₂
#print axioms ProofFile.Honest.SumToy.left₂
#print axioms ProofFile.Honest.SumToy.factorOf
#print axioms ProofFile.Honest.SumToy.job₄
#print axioms ProofFile.Honest.SumToy.played₄
#print axioms ProofFile.Honest.SumToy.left₄
#print axioms ProofFile.Honest.SumToy.k₃
#print axioms ProofFile.Honest.SumToy.k₃At
#print axioms ProofFile.Honest.SumToy.at0
#print axioms ProofFile.Honest.SumToy.job₃
#print axioms ProofFile.Honest.SumToy.pN
#print axioms ProofFile.Honest.SumToy.aN
#print axioms ProofFile.Honest.SumToy.B₃
#print axioms ProofFile.Honest.SumToy.played₃
#print axioms ProofFile.Honest.SumToy.whole₃
#print axioms ProofFile.Honest.SumToy.mask₃
#print axioms ProofFile.Honest.SumToy.sumBlock
#print axioms ProofFile.Honest.SumToy.sumSide
#print axioms ProofFile.Honest.SumToy.sumU
#print axioms ProofFile.Honest.SumToy.ten
#print axioms ProofFile.Honest.SumToy.mid₁
#print axioms ProofFile.Honest.SumToy.shown₁
#print axioms ProofFile.Honest.SumToy.scalarsShown
#print axioms ProofFile.Honest.SumToy.maskP
#print axioms ProofFile.Honest.SumToy.maskDecls
#print axioms ProofFile.Honest.SumToy.playedM
#print axioms ProofFile.Honest.SumToy.maskBlock
#print axioms ProofFile.Honest.SumToy.maskSide
#print axioms ProofFile.Honest.SumToy.maskU
#print axioms ProofFile.Honest.SumToy.thirteen
#print axioms ProofFile.Honest.SumToy.three
#print axioms ProofFile.Honest.SumToy.shownM
#print axioms ProofFile.Honest.SumToy.threeShown
#print axioms ProofFile.Honest.SumToy.closeP
