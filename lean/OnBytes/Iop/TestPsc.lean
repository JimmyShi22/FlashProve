-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/TestPsc.lean: tests of OnBytes/Iop/Psc.lean. They run when this file compiles.

What is tested.
 1. Small values by hand: the coefficient that is not sent, for both kinds of weight, and the
    linear form of the hiding polynomial.
 2. Agreement with the product test of Fmt/M1Psc.lean. That file states the same sumcheck for one
    summand, a b - c, and has an honest prover. On that prover's messages both files give the same
    point, the same row and the same two claims.
 3. The dry run of Psc.verify goes through on the entries of Psc.roundsOf, with the same kinds and
    items.

No module of the program imports this file. It holds no theorem.
-/
import OnBytes.Iop.Psc
import Fmt.M1Psc

namespace OnBytes.TestPsc

/-- A small number as an element of the extension field. -/
def n (x : UInt64) : E := ofF x

-- a plain sum: 2 c0 + c1 + c2 = 100 with c0 = 5, c2 = 7
#guard (Psc.Weight.plain 3).complete [n 5, n 7] (n 100) == [n 5, n 83, n 7]
-- an equality weight at z = 3: c0 + 3 (c1 + c2) = 100 with c1 = 5, c2 = 7
#guard (Psc.Weight.equality (n 3) 3).complete [n 5, n 7] (n 100) == [n 64, n 5, n 7]
-- reading at 0: the constant is the claim
#guard (Psc.Weight.atZero 4).complete [n 5, n 7, n 9] (n 100) == [n 100, n 5, n 7, n 9]
#guard Psc.polyAt [n 1, n 2, n 3] (n 10) == n 321
-- two variables under plain sums, challenges 2 and 3: psi = X, so the first variable's
-- coefficients are multiplied by 3
#guard Psc.hidingForm [Psc.Weight.plain 3, Psc.Weight.plain 3] [n 2, n 3] ==
  [n 6, n 12, n 1, n 3, n 9]
-- under equality weights psi = 1
#guard Psc.hidingForm [Psc.Weight.equality (n 5) 3, Psc.Weight.atZero 3] [n 2, n 3] ==
  [n 2, n 4, n 1, n 3, n 9]
#guard Psc.hidingEntries [Psc.Weight.plain 3, Psc.Weight.plain 3] == 5

/-- The summand a b - c: a and b are shown, c is kept. -/
def product : Psc.Summand where
  shown := 2
  kept := 1
  degree := 2
  coeffs := fun _ y => [mulE (y.getD 0 zeroE) (y.getD 1 zeroE), negE oneE]

/-- The claim that the sum of eq(zeta, i) (a_i b_i - c_i) is 0. -/
def claim (zeta : List E) : Psc.Claim where
  vars := zeta.map fun z => Psc.Weight.equality z 3
  masks := []
  target := zeroE

/-- The first count mask entries of oracle message 0. -/
def slots (count : Nat) : List Slot := (List.range count).map fun i => ⟨0, i⟩

/-- The messages of the other text's prover in this text's form. -/
def heard (m : Fmt.M1.PscMsg) (d : Fmt.M1.PscDraw) : Psc.Heard where
  mu := E.ofTriple m.mu
  eps := E.ofTriple d.eps
  rounds := ((m.q.zip d.gamma).map fun p =>
      ([E.ofTriple p.1.1, E.ofTriple p.1.2], E.ofTriple p.2)) ++
    [([E.ofTriple m.p.1, E.ofTriple m.p.2], E.ofTriple d.beta)]
  values := [E.ofTriple m.v.1, E.ofTriple m.v.2]

/-- Both texts give the same on the honest prover's messages for 2^K places and seed s. -/
def agree (K s : Nat) : Bool :=
  let f := Fmt.Fld.two
  let zeta := Fmt.M1.PscHon.zetas f K s
  let d := Fmt.M1.PscHon.draws f K s
  let m := Fmt.M1.PscHon.msg f (Fmt.M1.PscHon.wit f K 16 s) K zeta d
  let o := Fmt.M1.pscStep f zeta m d
  let gamma := o.gamma.map E.ofTriple
  let beta := E.ofTriple o.beta
  match Psc.run (claim (zeta.map E.ofTriple)) product (slots (2 * K + 5)) (heard m d) with
  | none => false
  | some x =>
    x.point == gamma && x.rowMaps == [E.ofTriple (f.negE o.eps)] &&
    x.rowTarget == E.ofTriple (f.subE o.R (f.mulE o.eps (f.mulE o.v1 o.v2))) &&
    x.rowMasks ==
      (slots (2 * K + 3)).map (fun t => (t, E.ofTriple (Fmt.M1.maskU f K o t.index))) &&
    (x.ends.map fun e => (e.point, e.masks, e.value)) ==
      [(gamma, [((⟨0, 2 * K + 3⟩ : Slot), beta)], E.ofTriple o.v1),
       (gamma, [((⟨0, 2 * K + 4⟩ : Slot), beta)], E.ofTriple o.v2)]

#guard agree 2 1
#guard agree 3 7

/-- A round as data that can be compared. -/
def lineOf (r : Fmt.Round) : Fmt.Entry × Fmt.Kind × List Fmt.Item := (r.entry, r.kind, r.items)

/-- Under the entries of Psc.roundsOf the dry run of the block goes through, which shows that the
number of rounds, their names and their numbers of draws agree; its kinds and items are those of
Psc.roundsOf. The entries themselves come back as they were handed in. -/
def sameRounds (c : Psc.Claim) (S : Psc.Summand) : Bool :=
  let want := Psc.roundsOf 0 (Psc.sizeOf c S)
  match (Psc.verify c S (slots (Psc.masksOf c S))).rounds
      { entries := want.map (·.entry), st := {} } with
  | none => false
  | some got => got.map (fun r => lineOf r.1) == want.map lineOf

#guard sameRounds (claim [n 2, n 3, n 4]) product
#guard sameRounds { vars := [], masks := [], target := zeroE } product
#guard sameRounds
  { vars := [Psc.Weight.plain 3, Psc.Weight.plain 3], masks := [], target := n 1 }
  { shown := 0, kept := 1, degree := 0, coeffs := fun _ _ => [zeroE, oneE] }
-- this claim takes seven fresh mask entries; with six the block fails
#guard Psc.masksOf (claim [n 2]) product == 7
#guard ((Psc.verify (claim [n 2]) product (slots 7)).rounds
  { entries := (Psc.roundsOf 0 (Psc.sizeOf (claim [n 2]) product)).map (·.entry)
    st := {} }).isSome
#guard ((Psc.verify (claim [n 2]) product (slots 6)).rounds
  { entries := (Psc.roundsOf 0 (Psc.sizeOf (claim [n 2]) product)).map (·.entry)
    st := {} }).isNone

end OnBytes.TestPsc
