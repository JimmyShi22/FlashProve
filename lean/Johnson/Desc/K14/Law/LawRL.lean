-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LawRL.lean: the laws of the constraints (rec_gamma) and (loc_x) in the linear
claim's shared rounds, as statements: definitions of propositions alone.

  LaysRecW    where the place "(rec_gamma)" says yes: its three clauses held; G_u has just the
              constraints recGamma more, one a seed of the record, in the seeds' order; no other
              group's constraints and nothing of the small record turn.
  LaysLocW    where "LOC" says yes: G_u has just one constraint locX more for each location drawn,
              in the order of the draws, each off the column that is handed there.
  RecEq, RecMeansW   what (rec_gamma) says of words, as an equation in K: the folded row's own
              sample at the record's seed is the fold of the rows' answers.
  LocEq, LocMeansW   what (loc_x) says of words: the code word of (u, r_u) at x is the fold of the
              column at x. The generator's row is taken off the plain function generatorAt.
  PlacedU     what the two MEANS want of the statement at o_u.
  InRange     a premise by name: every drawn location is below 2 ^ logN. "LOC" takes a drawn
              location modulo 2 ^ logN; the test that it lies in its range is the format's.

What is not claimed. Nothing is proved in this file. That these two families pin u to the fold of
the index's rows at gamma is not stated here: it rests on the code's distance and on the key's law.

-/
import Johnson.Desc.K14.Law.Law

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Model (Reading)
open OnBytes.Means (Words)
open VerifiableInference.Desc.Ground (ok)

variable {K : Type} [Field K] (ρ : Reading K)

/-- The constraints (rec_gamma) at a state: one a seed of the record. -/
def recRows (p : Par) (l : Lin) : Option (List Row) :=
  l.key.seeds.zipIdx.mapM fun x =>
    recGamma p.S.fold.index x.1 x.2 (weights p.S l) l.key.record l.oU

/-- **LAYS**, for (rec_gamma). -/
def LaysRecW : Prop :=
  ∀ (p : Par) (d d' : St) (rs : List Fmt.RoundView), laysRec p d rs = some d' →
    ok (laysRecL p d.loc) = true ∧ d'.loc = d.loc ∧
    ∃ rows, recRows p d.loc = some rows ∧
      rowsOn d' d.loc.gU = rowsOn d d.loc.gU ++ rows ∧
      ∀ g, g ≠ d.loc.gU → rowsOn d' g = rowsOn d g

/-- The locations as "LOC" takes them. -/
def locations (p : Par) (r : Fmt.RoundView) : List Nat :=
  r.drawn.poss.map (· % 2 ^ p.S.fold.index.code.logN)

/-- Every drawn location lies in its range. -/
def InRange (p : Par) (r : Fmt.RoundView) : Prop := ∀ x ∈ r.drawn.poss, x < 2 ^ p.S.fold.index.code.logN

/-- The constraints (loc_x) at a state: one a location drawn. -/
def locRows (p : Par) (l : Lin) (r : Fmt.RoundView) (cols : List (Nat × List UInt64)) :
    Option (List Row) :=
  (locations p r).mapM fun x => do
    locX p.S.fold x (weights p.S l) ((← cols.lookup x).toArray) l.oU

/-- **LAYS**, for (loc_x). -/
def LaysLocW : Prop :=
  ∀ (p : Par) (d d' : St) (r : Fmt.RoundView) (cols : List (Nat × List UInt64)),
    loc p d [r] [cols] = some d' →
    d'.loc = d.loc ∧
    ∃ rows, locRows p d.loc r cols = some rows ∧ rows.length = r.drawn.poss.length ∧
      rowsOn d' d.loc.gU = rowsOn d d.loc.gU ++ rows ∧
      ∀ g, g ≠ d.loc.gU → rowsOn d' g = rowsOn d g

/-- What the two MEANS want of the statement at o_u: it has a main table of its layout's size, which
holds a row's message and its random tail. -/
structure PlacedU (T : Statement) (S : FoldeqShape) (u : FoldedRow) : Prop where
  has : T.has u.oracle .main = true
  bits : T.tableBits u.oracle .main = u.lay.bits
  room : S.index.code.logEll ≤ u.lay.bits
  roomTail : S.tailFirst + S.index.code.r ≤ 2 ^ u.lay.bits
  aligned : S.tailFirst % 2 ^ S.index.code.logR = 0

/-- (rec_gamma) for answer i, as an equation in K. z, beta: the seed; theta t: what X ^ t reads as;
w r: the weight of row r; y: the record; u: the folded row's message. In front of the pads eq(z, .);
on answer i's three pads beta (1, X, X ^ 2); on the other pads 0. -/
def RecEq (s : IndexShape) (z : List K) (beta : K) (theta : Nat → K) (i : Nat) (w y u : Nat → K) :
    Prop :=
  (∑ k ∈ Finset.range s.plain, eqK z k * u k) +
      ∑ t ∈ Finset.range 3, beta * theta t * u (s.padPlace i t) =
    ∑ r ∈ Finset.range s.rows, w r * y (r * s.answers + i)

/-- **MEANS**, for (rec_gamma). -/
def RecMeansW : Prop :=
  ∀ (T : Statement) (S : FoldeqShape) (seed : SampleSeed) (i : Nat) (w y : Array E)
    (u : FoldedRow) (row : Row), S.index.ok = true → i < S.index.answers →
    seed.z.length = S.index.cubeBits → recGamma S.index seed i w y u = some row →
    PlacedU T S u → ∀ m : Words K,
      (Means.Says ρ T row m ↔
        RecEq S.index (seed.z.map ρ.val) (ρ.val seed.beta) (fun t => ρ.val (thetaE t)) i
          (fun r => ρ.val (w.getD r zeroE)) (fun k => ρ.val (y.getD k zeroE))
          (fun k => m u.oracle .main (u.lay.index k)))

/-- The product of the factors at the bits that are set in j, the lowest bit first. -/
def bitsK : List K → Nat → K
  | [], _ => 1
  | x :: l, j => (if j % 2 = 1 then x else 1) * bitsK l (j / 2)

/-- (loc_x) as an equation in K: row x of the code's generator matrix, on the message and on the
random tail, gives the fold of the column. g: the code's generator row at x; col: the column. -/
def LocEq (S : FoldeqShape) (g : GeneratorRow) (w : Nat → K) (rows : Nat) (col u : Nat → K) :
    Prop :=
  let c := S.index.code
  let f := g.f.map fun a => ρ.val (ofF a)
  ρ.val (ofF g.messageScale) * (∑ j ∈ Finset.range c.ell, bitsK (f.take c.logEll) j * u j) +
      ρ.val (ofF g.tailScale) *
        (∑ j ∈ Finset.range c.r, bitsK (f.take c.logR) j * u (S.tailFirst + j)) =
    ∑ r ∈ Finset.range rows, w r * col r

/-- **MEANS**, for (loc_x). -/
def LocMeansW : Prop :=
  ∀ (T : Statement) (S : FoldeqShape) (x : Nat) (w : Array E) (column : Array F) (u : FoldedRow)
    (row : Row), S.index.ok = true → locX S x w column u = some row → PlacedU T S u →
    ∀ m : Words K,
      (Means.Says ρ T row m ↔
        LocEq ρ S (generatorAt S.index.code x) (fun r => ρ.val (w.getD r zeroE)) w.size
          (fun r => ρ.val (ofF (column.getD r 0))) (fun k => m u.oracle .main (u.lay.index k)))

end Desc.K14.Law
