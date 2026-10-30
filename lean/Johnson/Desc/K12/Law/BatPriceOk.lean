-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.SmallOk
/-
Johnson/Desc/K12/Law/BatPriceOk.lean: THE PRICE OF THE PROXIMITY TEST's ROUND "BAT" AS NUMBERS, AND ONE TEST WITH CODE ON THEM. DEFINITIONS WITH CODE ALONE; NO THEOREM; NO Mathlib BENEATH IT. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  geoB · w0B · wNB · wtB · wtAllB · wOfB   THE NUMBER w IN THE LAW OF THE FORMAT's SAMPLER («at most w hash-block strings go to one tuple of typed values»), typed again over plain numbers after the library's geo (Run/DrawCount.lean) · w0 | wN (Run/DrawCountNum.lean) · nGive | nFail | wt | wtAll | bsOf (Run/DrawPage.lean) · toBS (Run/DrawBS.lean), AT THE SECOND FIELD: these stand over Mathlib. that wOfB ds IS (bsOf .two ds).w is a lemma of Johnson/Desc/K12/Law/PayPub.lean (wOfB_eq): not here
  blocksOfB ds    the round's hash blocks: (mostAll ds + 3) / 4
  chalsB w        the number of the written round's verifier messages: (2 ^ 256) ^ blocks * 2 ^ work
  batV0 p r       v₀: the count in typed values: lstJB a (r a) * (entry.rows − 1): a: the plan's first stage in the library's form; entry: the plan's first written round's ("BAT"'s): THE PLAN's NUMBER OF ROWS
  batW p          w at "BAT"'s draws
  batE0 p r       e₀ := v₀ * w: the count in verifier messages that pass the round's work
  batPriceOk p r k   e₀ * 2 ^ k ≤ the number of "BAT"'s verifier messages: in the library's words RoundBelow v₀ ("BAT"'s round) (2 ^ −k) (OnBytes/Slice/ManyErr.lean:48: n * w ≤ εs * the number of challenge values), the comparison that smallOk's gate asks of the chain's rounds at k := 128; false where the plan has no stage or no written round
  batGate p r     the gate's OWN clause at that count: roundN w v₀ (Johnson/Desc/K12/Law/SmallOk.lean): it goes by the number of typed values and a bound on the sampler's bias, not by w
  batBits p r     the greatest k ≤ 512 with batPriceOk p r k
  payOn · batPayOk p r k   THE TEST THAT CAN FAIL EVERYWHERE: the first stage's nine clauses of johOk (stageJL: sizes in order · two coefficients a code · 0 < radius < distance · below the Johnson radius) AND batPriceOk's comparison: so where the list's bound has no meaning it says false, not «true for nothing» · batPayBits: its greatest k
  batPriceLines tag p r   one line with the five numbers and both verdicts, and two controls, each due false WHERE johOk SAYS YES: the rows * 2 ^ 70 · the radius at the distance; then batPayOk's line and three controls, EACH DUE false EVERYWHERE: the rows * 2 ^ 70 · the radius at the distance · the radius 0
WHAT FOR: the public half of what the payer of the batching's converse asks (lstJ (radius) * (rows − 1) ≤ v₀) AT v₀ := batV0, and whether e₀ := v₀ * w is small against the round's verifier messages. THE LAWS: Johnson/Desc/K12/Law/PayPub.lean (payPub_of_joh) · Johnson/Desc/K12/Law/BatPriceLaw.lean (batBelow_of_ok · batPay_gives): not here.
WHAT IT DOES NOT SAY: lstJB has a meaning only below the Johnson radius (johOk's clause joh.johnson): at or beyond it the division's denominator is cut off at 0 and Lean's division by 0 gives 0: SO batPriceOk ALONE SAYS true THERE: it is to be read beside johOk AT THE SAME RADIUS: the line prints both · nothing on the chain's other rounds · no level of security.
EVALUATED (a run's word; the prints are not in this library): batPriceOk, at another text than this file's, at the four proximity tests of both stored example proofs, at the least radii that the prices need and at the planner's own: true at 128 with johOk true beside it, both controls false; the greatest k 175 to 185. At the tiny proof johOk is false, the bound is 0, batPriceOk says true for nothing and its first control says true: NO TOOTH THERE: hence batPayOk: RoundsHoldPlaces.lean.
-/
set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params
open VerifiableInference.Desc.K12 (P12)

def geoB (F T : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => T ^ n + F * geoB F T n

def wxB (m f Q : Nat) : Nat := m * geoB f Q 6
def w0B (m f Q : Nat) : Nat := m * geoB f Q 6 + f ^ 6
def wNB (m f Q : Nat) : Nat :=
  wxB m f Q * w0B m f Q ^ 2 * Q ^ 18 + w0B m f Q ^ 3 * (wxB m f Q * w0B m f Q ^ 2) +
    (w0B m f Q ^ 3) ^ 2

/-- At the second field: one word gives a value; 2 ^ 32 − 1 words fail. -/
def wtB : Fmt.Draw → Nat
  | .elem => w0B 1 (2 ^ 32 - 1) (2 ^ 64) ^ 3
  | .elemNZ => wNB 1 (2 ^ 32 - 1) (2 ^ 64)
  | .pos k => 2 ^ (64 - k)
  | .trits n => 2 ^ (64 * ((n + 31) / 32) - 2 * n)
  | .sealed => 1

def wtAllB : List Fmt.Draw → Nat
  | [] => 1
  | d :: ds => wtB d * wtAllB ds

def blocksOfB (ds : List Fmt.Draw) : Nat := (Fmt.mostAll ds + 3) / 4

def wOfB (ds : List Fmt.Draw) : Nat :=
  wtAllB ds * (2 ^ 64) ^ (4 * blocksOfB ds - Fmt.mostAll ds)

def chalsB (w : WR) : Nat := (2 ^ 256) ^ blocksOfB (Fmt.dsOf w.entry w.kind) * 2 ^ w.entry.work

/-- The plan's first stage, in the library's form, and its first written round. -/
def batAtB (p : P12) : Option (Fmt.M1.Stage × WR) :=
  match p.nums.stages.head?, (writtenOf p.nums).bind (·.head?) with
  | some a, some w => some (stN a, w)
  | _, _ => none

def v0On (a : Fmt.M1.Stage) (e rows : Nat) : Nat := lstJB a e * (rows - 1)

def priceOn (a : Fmt.M1.Stage) (w : WR) (e rows k : Nat) : Bool :=
  decide (v0On a e rows * wOfB (Fmt.dsOf w.entry w.kind) * 2 ^ k ≤ chalsB w)

def batV0 (p : P12) (r : Fmt.M1.Stage → Nat) : Nat :=
  ((batAtB p).map fun x => v0On x.1 (r x.1) x.2.entry.rows).getD 0

def batW (p : P12) : Nat := ((batAtB p).map fun x => wOfB (Fmt.dsOf x.2.entry x.2.kind)).getD 0

def batE0 (p : P12) (r : Fmt.M1.Stage → Nat) : Nat := batV0 p r * batW p


def batPriceOk (p : P12) (r : Fmt.M1.Stage → Nat) (k : Nat) : Bool :=
  (batAtB p).any fun x => priceOn x.1 x.2 (r x.1) x.2.entry.rows k

def batGate (p : P12) (r : Fmt.M1.Stage → Nat) : Bool :=
  (batAtB p).any fun x => roundN x.2 (v0On x.1 (r x.1) x.2.entry.rows)

def batBits (p : P12) (r : Fmt.M1.Stage → Nat) : Nat := bitsOf (batPriceOk p r)

/-- The comparison, asked only where the list's bound has a meaning: the first stage's nine clauses
of johOk stand in front. -/
def payOn (a : Fmt.M1.Stage) (w : WR) (e rows k : Nat) : Bool :=
  ok (stageJL a e) && priceOn a w e rows k

/-- THE TEST THAT CAN FAIL EVERYWHERE. -/
def batPayOk (p : P12) (r : Fmt.M1.Stage → Nat) (k : Nat) : Bool :=
  (batAtB p).any fun x => payOn x.1 x.2 (r x.1) x.2.entry.rows k

def batPayBits (p : P12) (r : Fmt.M1.Stage → Nat) : Nat := bitsOf (batPayOk p r)

def batPriceLines (tagS : String) (p : P12) (r : Fmt.M1.Stage → Nat) : List String :=
  match batAtB p with
  | some (a, w) =>
    let e := r a
    [s!"{tagS}.BATPRICE\tbatPriceOk at 128 {batPriceOk p r 128} · the gate's own clause {batGate p r} · johOk at this radius {johOk p r}\tradius {e} · the Johnson bound on the list {lstJB a e} · rows {w.entry.rows} · v0 {batV0 p r} · w < 2^{(batW p).log2 + 1} · e0 < 2^{(batE0 p r).log2 + 1} · verifier messages 2^{(chalsB w).log2} · blocks {blocksOfB (Fmt.dsOf w.entry w.kind)} · work {w.entry.work}\tthe greatest k {batBits p r}",
     s!"{tagS}.BATPRICE.control.1\tthe rows * 2 ^ 70\t{priceOn a w e (w.entry.rows * 2 ^ 70) 128}",
     s!"{tagS}.BATPRICE.control.2\tthe radius at the distance: batPriceOk && johOk\t{batPriceOk p (fun x => dB x) 128 && johOk p fun x => dB x}",
     s!"{tagS}.BATPAY\tbatPayOk at 128 {batPayOk p r 128}\tthe first stage's clauses {ok (stageJL a e)}\tthe greatest k {batPayBits p r}",
     s!"{tagS}.BATPAY.control.1\tthe rows * 2 ^ 70\t{payOn a w e (w.entry.rows * 2 ^ 70) 128}",
     s!"{tagS}.BATPAY.control.2\tthe radius at the distance\t{batPayOk p (fun x => dB x) 128}",
     s!"{tagS}.BATPAY.control.3\tthe radius 0\t{batPayOk p (fun _ => 0) 128}"]
  | none => [s!"{tagS}.BATPRICE\tno stage, or no written round"]

end H2K.Pub
