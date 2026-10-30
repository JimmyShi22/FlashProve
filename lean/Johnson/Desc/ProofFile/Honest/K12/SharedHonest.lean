-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/SharedHonest.lean: honest values for the eight sub-protocols of
the small shared chain of SharedSmall.lean, with the committed table's rows as a parameter: the key,
the prover's tables, the answers, the scalar, the columns that the round "LOC" reads, and the
rounds. A test file: definitions and `#guard` lines; no theorem.

Why. Johnson/Desc/K14/Honest/Toy.lean has such values at one fixed table, whose rows hold numbers at
the four free places. `rowsOf` (Johnson/Desc/ProofFile/Honest/K14/Parts.lean), by which the honest
side's parts read the table, is 0 there. So no readers give that file's rows, and its key, answers
and columns do not fit a job that calls `rowsOf`.

  `symbolAt`, `keyAt`, `wordsAt`, `answerAt`, `muAt`, `roundsAt`   repeat `symbol`, `key`, `words`,
                 `answer`, `mu` and `roundsOf` of Toy.lean, without its changes for trials, with the
                 rows as the argument Rw
  `weights`, `rand`, `rows`   made-up readers, and `rowsOf` at them. up: added to one entry of the
                 matrix
  `runAt`        the eight `decide` functions in a row, at `P3`

What is checked. At Toy.lean's own rows the six definitions give Toy.lean's key, answers, scalar and
rounds. The rows at the made-up readers equal Toy.lean's rows but at the four free places, where
they are 0. At these rows the eight sub-protocols accept, and all ten constraints that they leave
(six on G_u, one on G_omega, three sample rows) hold of the prover's tables; with the key made of
another table two of them fail. The three sample rows hold by construction: the answers are computed
as their left sides.

Limits. As in Toy.lean: tiny sizes; the library's check on the key (`okKey`) is not asked; the first
fresh table's entries stand in no constraint of the eight; `decide` is called, not `Block.step`; a
row's symbol at a location is computed over `generatorAt`, and nothing compares it with a program
that encodes. `symbolAt` reads the first word of an entry alone, so it is meant for rows over the
base field. One list of challenges. That the eight sub-protocols accept is a test at one example.
Nothing on completeness, soundness or hiding.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.SharedSmall
import Johnson.Desc.ProofFile.Honest.K14.Parts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light.SharedHonest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Means (Words)
open Desc.K14 (St blocks first)
open Desc.K14.Honest (uAtE omegaAtE muAtE)
open Desc.K14.Law (sumE eqE valueE rowsOn)
open Desc.K14.Honest.Toy (shape seeds Chal chal draws kappa rnd layU allSent rowE)
open VerifiableInference.Desc (K1.sampleRow K1.Msg.of K1.cutSeeds)
open ProofFile.Honest.K12.Light.SharedSmall (codes2 shape3 P3)

/-- The committed table's rows before encoding: row, place. -/
abbrev Rows : Type := Nat → Nat → E

/-- The symbol of row r at the location x. -/
def symbolAt (Rw : Rows) (r x : Nat) : UInt64 :=
  let c := shape.fold.index.code
  let g := generatorAt c x
  let bit (n j : Nat) : UInt64 :=
    ((g.f.take n).zipIdx.foldl (fun a y => if (j / 2 ^ y.2) % 2 == 1 then mulF a y.1 else a) 1)
  addF (mulF g.messageScale ((List.range c.ell).foldl
      (fun s j => addF s (mulF (bit c.logEll j) (Rw r j).triple.1)) 0))
    (mulF g.tailScale ((List.range c.r).foldl
      (fun s j => addF s (mulF (bit c.logR j) (Rw r (shape.fold.tailFirst + j)).triple.1)) 0))

/-- The key: the seeds, and each row's own out-of-domain answers. -/
def keyAt (Rw : Rows) : TableKey :=
  let s := shape.fold.index
  { item := 0, seeds := seeds
    record := ((List.range 4).flatMap fun r => seeds.zipIdx.map fun x =>
      addE (sumE s.plain fun k => mulE (eqE x.1.z k) (Rw r k))
        (sumE 3 fun i => mulE (mulE x.1.beta (thetaE i)) (Rw r (s.padPlace x.2 i)))).toArray }

/-- The prover's tables: o_u is message 0, the first fresh table 1, o_omega 2, o_sp 3. -/
def wordsAt (Rw : Rows) (c : Chal) : Words E := fun o part i =>
  match o, part with
  | 0, .main => if i == 31 then rnd 50 else uAtE shape c.psi Rw (layU.entryAt i)
  | 1, .mask => rnd (60 + i)
  | 2, .main => if i == 3 then rnd 51 else omegaAtE shape c.psi Rw i
  | 3, .mask => if i == 3 then rnd 52 else if i == 0 then kappa else rnd (70 + i)
  | _, _ => zeroE

/-- An honest answer: the left side of the message's own sample row at the honest tables. -/
def answerAt (Rw : Rows) (c : Chal) (o : Nat) (s : OracleShape) (v : Nat) (l : List E) : E :=
  let sd := (K1.cutSeeds v 1 l).headD ([], zeroE)
  valueE allSent (K1.sampleRow (K1.Msg.of Desc.K14.Honest.Toy.codes s) o sd.1 sd.2 0 zeroE)
    (wordsAt Rw c)

/-- The honest scalar. -/
def muAt (Rw : Rows) (c : Chal) : E := muAtE shape c.psi c.zeta Rw kappa

/-- The rounds of the eight sub-protocols, and the columns that "LOC" is handed. -/
def roundsAt (Rw : Rows) (c : Chal) : List (List Fmt.RoundView × List (List (Nat × List UInt64))) :=
  let aU := answerAt Rw c 0 shape.fold.u 5 c.seedU
  let aO := answerAt Rw c 2 shape.omega 2 c.seedOmega
  let aS := answerAt Rw c 3 shape.sharedSplit 2 c.seedOmega
  [([⟨[], draws c.psi⟩], []),
   ([⟨[], draws c.seedU⟩, ⟨[.answer aU.triple], draws []⟩], []),
   ([], []),
   ([⟨[], draws [] c.locs⟩],
     [c.locs.map fun x => (x % 64, (List.range 4).map fun r => symbolAt Rw r (x % 64))]),
   ([⟨[], draws c.seedOmega⟩, ⟨[.answer aO.triple, .answer aS.triple], draws []⟩], []),
   ([], []),
   ([⟨[], draws c.zeta⟩], []),
   ([⟨[.e (muAt Rw c).triple], draws []⟩], [])]

/-- Made-up readers. Row r of the table then holds 100 r + k + 1 at the place k, as in Toy.lean,
but at the free places. up: added to row 1's place 2. -/
def weights (up : Nat) : ProofFile.Honest.Weights :=
  ⟨fun y x => OnBytes.Slice.toF (UInt64.ofNat
    (100 * (x / 2) + (x % 2 + 2 * y) + 1 + (if y == 1 && x == 2 then up else 0)))⟩
def rand : ProofFile.Honest.TableRand :=
  ⟨fun r i => OnBytes.Slice.toF (UInt64.ofNat (100 * r + (10 + i) + 1)),
    fun r i => OnBytes.Slice.toF (UInt64.ofNat (100 * r + (16 + i) + 1))⟩
def rows (up : Nat) : Rows := ProofFile.Honest.K14.rowsOf shape3 (weights up) rand

/-- The eight decisions in a row at `P3`, from the first state at a key. -/
def runAt (k : TableKey) (Rw : Rows) (c : Chal) : Except String St :=
  match blocks P3 with
  | none => .error "no blocks"
  | some bs =>
    (bs.zip (roundsAt Rw c)).foldl
      (fun d x => d.bind fun s => x.1.decide s x.2.1 x.2.2) (.ok (first codes2 k))

/-- Constraint by constraint: does it hold of the prover's tables? -/
def each (d : St) (l : List Row) (Rw : Rows) (c : Chal) : List Bool :=
  l.map fun r => decide (valueE d.st r (wordsAt Rw c) = r.target)

/-- For each open constraint on G_u, on G_omega, and each sample row: whether it holds. -/
def holds (k : TableKey) (Rw : Rows) (c : Chal) : Option (List Bool × List Bool × List Bool) :=
  (runAt k Rw c).toOption.map fun d =>
    (each d (rowsOn d d.loc.gU) Rw c, each d (rowsOn d d.loc.gOmega) Rw c,
      each d (d.st.oracles.toList.flatMap (·.sampleRows.toList)) Rw c)

def vals (l : List (List Fmt.RoundView × List (List (Nat × List UInt64)))) :=
  l.map fun x => (x.1.map (·.vals), x.1.map (·.drawn), x.2)

-- at Toy.lean's own rows: Toy.lean's key, scalar and rounds (the answers and the columns are in
-- the rounds)
#guard (keyAt (rowE {})).record.map (·.triple) ==
  (Desc.K14.Honest.Toy.key {}).record.map (·.triple)
#guard (muAt (rowE {}) (chal 0)).triple == (Desc.K14.Honest.Toy.mu (chal 0)).triple
#guard vals (roundsAt (rowE {}) (chal 0)) == vals (Desc.K14.Honest.Toy.roundsOf {} (chal 0))
-- the comparison can fail: at the made-up readers' rows the rounds are others
#guard vals (roundsAt (rows 0) (chal 0)) != vals (Desc.K14.Honest.Toy.roundsOf {} (chal 0))
-- the rows at the made-up readers: Toy.lean's but at the free places 6 to 9, where they are 0
#guard (List.range 4).all fun r => (List.range 20).all fun k =>
  (rows 0 r k).triple == (if 6 ≤ k && k < 10 then (0, 0, 0) else (rowE {} r k).triple)
-- at these rows the eight accept, and all ten constraints hold
#guard holds (keyAt (rows 0)) (rows 0) (chal 0) ==
  some ([true, true, true, true, true, true], [true], [true, true, true])
-- a key made of another table: the two constraints on the key's out-of-domain answers fail
#guard holds (keyAt (rows 1)) (rows 0) (chal 0) ==
  some ([false, false, true, true, true, true], [true], [true, true, true])

end ProofFile.Honest.K12.Light.SharedHonest

#print axioms ProofFile.Honest.K12.Light.SharedHonest.Rows
#print axioms ProofFile.Honest.K12.Light.SharedHonest.symbolAt
#print axioms ProofFile.Honest.K12.Light.SharedHonest.keyAt
#print axioms ProofFile.Honest.K12.Light.SharedHonest.wordsAt
#print axioms ProofFile.Honest.K12.Light.SharedHonest.answerAt
#print axioms ProofFile.Honest.K12.Light.SharedHonest.muAt
#print axioms ProofFile.Honest.K12.Light.SharedHonest.roundsAt
#print axioms ProofFile.Honest.K12.Light.SharedHonest.weights
#print axioms ProofFile.Honest.K12.Light.SharedHonest.rand
#print axioms ProofFile.Honest.K12.Light.SharedHonest.rows
#print axioms ProofFile.Honest.K12.Light.SharedHonest.runAt
#print axioms ProofFile.Honest.K12.Light.SharedHonest.each
#print axioms ProofFile.Honest.K12.Light.SharedHonest.holds
#print axioms ProofFile.Honest.K12.Light.SharedHonest.vals
