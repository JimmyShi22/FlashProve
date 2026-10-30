--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/Toy.lean: A TEST THAT CAN FAIL: the eight sub-protocols of the linear
claim's shared rounds, decided by their own text at a small shape, on what the coded honest values
of Johnson/Desc/K14/Honest/Coded.lean make. Definitions with code and #guard lines; no theorem.

The shared rounds test no equation: they lay constraints for two later proximity tests. So two
things are held. Each of the eight accepts. And every constraint that lies behind the last holds of
the prover's words, computed by valueE (Johnson/Desc/K14/Law/SaysTests.lean), EACH CONSTRAINT BY
ITSELF: on G_u two (rec_gamma), three (loc_x) and (fold_u); on G_omega (fold_omega); and three
sample rows. The three sample rows hold by construction: the answers here are computed as these
rows' own left sides. The seven others are the kind's own, and nothing here is computed from them.
Then one value at a time is changed by one, and the lines say WHICH constraints fail.

The shape. A committed table of four rows (v = 2) of sixteen places, with two out-of-domain answers
a row: six places hold the matrix, four are free, six are pads; a tail of two. A matrix of three
rows (kRow = 2, and three is no power of two) and eight columns (kLo = 1). o_u has two main rows, so
an entry's index in the table is not its number in the vector. Two codes, so the shape splits; the
first mask goes out with o_u. The table's entries are small numbers; all values are synthetic.

Some sent values as numbers. At challenges that are all 0 or all 1 the equality vectors pick one
entry, so by the formula mu = sum of eq(z_fd, j) Omega_j + kappa, Omega_j = sum of eq(psi_lo, t)
U(t + 2 j), U k = sum of eq(gamma, r) Rw r k, the scalar is one entry of the table plus kappa.

Limits. A small shape; three lists of challenges. Still idle at this shape: psi_lo has one
coordinate; o_omega has one main row; the committed table's code and o_u's own are one code; the
tail begins where the message ends, so there is no gap between them. The library's test on the
instance (okKey) is not asked of the key, nor the codes' own tests; the list beforePoint is a
placeholder. The sub-protocols' decide is called, not
Block.step: the form of rounds and columns is not held here. The stages of the two proximity tests
in the shape are placeholders. The symbol of a row at a location is computed here over generatorAt;
nothing holds it against a program that encodes. No tree, no column of a message that is sent, no
proximity test. The first mask's entries stand in no constraint of these rounds. Nothing on any
property.

-/
import Johnson.Desc.K14.Honest.Coded
import Johnson.Desc.K14.Blocks
import Johnson.Desc.K14.Law.SaysTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest.Toy
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Means (Words)
open Desc.K14.Law (sumE eqE valueE rowsOn)
open VerifiableInference.Desc (K1.sampleRow K1.Msg.of K1.cutSeeds)

/-! ## The shape -/

def codes : Codes := { base := #[⟨6, 16, 2⟩, ⟨5, 4, 2⟩], mask := #[⟨4, 4, 2⟩] }

def shape : LinShape :=
  { fold := { index := { code := ⟨6, 16, 2⟩, v := 2, answers := 2, saltBytes := 40 }
              u := { code := 0, mainRows := 2, mainDeg := 3, maskRows := 0, maskCode := noId,
                     answers := 1 }
              rowsHigh := true, leafClass := 0, columns := 3 }
    kLo := 1, matrixRows := 3
    omega := { code := 1, mainRows := 1, mainDeg := 3, maskRows := 0, maskCode := noId,
               answers := 1 }
    w := { code := 1, mainRows := 3, mainDeg := 3, maskRows := 0, maskCode := noId, answers := 1 }
    omegaRowsHigh := true, wRowsHigh := true
    sharedSplit := { code := noId, mainRows := 0, mainDeg := 3, maskRows := 1, maskCode := 0,
                     answers := 1 }
    ownSplit := { code := noId, mainRows := 0, mainDeg := 1, maskRows := 0, maskCode := noId,
                  answers := 0 }
    omegaLeafClass := 1, sharedSplitLeafClass := 2, wLeafClass := 0, ownSplitLeafClass := 3
    sharedMaskCode := 0, ownMaskCode := 0, masksAhead := true
    testU := [⟨0, 0, 1, 0⟩], testOmega := [⟨1, 0, 0, 0⟩], testOwn := [⟨1, 0, 2, 0⟩]
    testOwnOmega := [], choice := ⟨true⟩ }

def P : P14 :=
  { set := {}, scope := .shared, codes := codes, S := shape, item := 0, beforePoint := [(1, 0)] }

#guard linOk codes shape && shape.sharedSplitNeeded && codes.lengthsOk
#guard shape.kRow == 2 && shape.kCol == 3 && shape.fold.index.plain == 10 &&
  shape.fold.tailFirst == 16 && shape.fold.entries == 18

/-- How the folded row lies in o_u's main table. -/
def layU : VectorLay := vectorLay codes shape.fold.u true

-- an entry's index in the table is not its number in the vector
#guard layU.index 3 == 6 && layU.index 17 == 3 && layU.entryAt 6 == 3

/-! ## Synthetic values -/

/-- An element of the extension field for each number. -/
def rnd (n : Nat) : E :=
  E.mk3 (normF (UInt64.ofNat (n * 2654435761 + 12345))) (normF (UInt64.ofNat (n * n * 40503 + 7)))
    (normF (UInt64.ofNat (n * 97 + n * n * n)))

/-- What can be changed in a trial: a number is added to one value. -/
structure Turn where
  table : Nat := 0
  column : Nat := 0
  u : Nat := 0
  omega : Nat := 0
  kappa : Nat := 0
  padU : Nat := 0
  padOmega : Nat := 0
  padSp : Nat := 0
  answerU : Nat := 0
  answerOmega : Nat := 0
  answerSp : Nat := 0
  mu : Nat := 0

def bump (n : Nat) (x : E) : E := addE x (ofF (UInt64.ofNat n))

/-- The committed table's rows before encoding, as words of the base field, laid out as the folded
row is: sixteen places of the message, then the tail. Row r holds 100 r + k + 1 at the place k. -/
def rowF (t : Turn) (r k : Nat) : UInt64 :=
  if k < 18 then UInt64.ofNat (100 * r + k + 1 + (if r == 1 && k == 2 then t.table else 0)) else 0

def rowE (t : Turn) (r k : Nat) : E := ofF (rowF t r k)

/-- The symbol of row r at the location x. -/
def symbol (t : Turn) (r x : Nat) : UInt64 :=
  let c := shape.fold.index.code
  let g := generatorAt c x
  let bit (n j : Nat) : UInt64 :=
    ((g.f.take n).zipIdx.foldl (fun a y => if (j / 2 ^ y.2) % 2 == 1 then mulF a y.1 else a) 1)
  addF (mulF g.messageScale ((List.range c.ell).foldl
      (fun s j => addF s (mulF (bit c.logEll j) (rowF t r j))) 0))
    (mulF g.tailScale ((List.range c.r).foldl
      (fun s j => addF s (mulF (bit c.logR j) (rowF t r (shape.fold.tailFirst + j)))) 0))

/-- The key's two OOD seeds. -/
def seeds : List SampleSeed :=
  [⟨[rnd 1, rnd 2, rnd 3, rnd 4], rnd 5⟩, ⟨[rnd 6, rnd 7, rnd 8, rnd 9], rnd 10⟩]

/-- The key: the seeds, and each row's own OOD answers. -/
def key (t : Turn) : TableKey :=
  let s := shape.fold.index
  { item := 0, seeds := seeds
    record := ((List.range 4).flatMap fun r => seeds.zipIdx.map fun x =>
      addE (sumE s.plain fun k => mulE (eqE x.1.z k) (rowE t r k))
        (sumE 3 fun i => mulE (mulE x.1.beta (thetaE i)) (rowE t r (s.padPlace x.2 i)))).toArray }

/-! ## A run -/

/-- The challenges of a run: the shared point; the elements of the seed of each of the two sendings;
the locations; z_fd. -/
structure Chal where
  psi : List E
  seedU : List E
  locs : List Nat
  seedOmega : List E
  zeta : List E

def chal (n : Nat) : Chal :=
  { psi := (List.range 3).map fun i => rnd (n + 11 + i)
    seedU := (List.range 6).map fun i => rnd (n + 20 + i)
    locs := [3 + n, 17, 50], seedOmega := (List.range 3).map fun i => rnd (n + 30 + i)
    zeta := [rnd (n + 40), rnd (n + 41)] }

/-- A list at which the shared point and z_fd have the one value b in every coordinate. -/
def flat (b : E) : Chal := { chal 0 with psi := [b, b, b], zeta := [b, b] }

def draws (l : List E) (ps : List Nat := []) : Fmt.Drawn := ⟨l.map (·.triple), ps, [], none⟩

/-- The entry of the mask message that "SPLIT" takes. -/
def kappa : E := E.mk3 1000 2000 3000

/-- The prover's words: o_u is message 0, the first mask 1, o_omega 2, o_sp 3. The pads stand at the
last index of their tables. -/
def words (t : Turn) (c : Chal) : Words E := fun o part i =>
  match o, part with
  | 0, .main =>
    if i == 31 then bump t.padU (rnd 50)
    else bump (if i == 6 then t.u else 0) (uAtE shape c.psi (rowE {}) (layU.entryAt i))
  | 1, .mask => rnd (60 + i)
  | 2, .main =>
    if i == 3 then bump t.padOmega (rnd 51)
    else bump (if i == 1 then t.omega else 0) (omegaAtE shape c.psi (rowE {}) i)
  | 3, .mask =>
    if i == 3 then bump t.padSp (rnd 52) else if i == 0 then bump t.kappa kappa else rnd (70 + i)
  | _, _ => zeroE

/-- The statement that has all four messages: for the tables' sizes alone. -/
def allSent : Statement :=
  { codes := codes, groups := #[]
    oracles := #[{ shape := shape.fold.u },
      { shape := { maskRows := 1, maskCode := 0, answers := 0 } },
      { shape := shape.omega }, { shape := shape.sharedSplit }] }

/-- An honest answer: the left side of the message's own sample row at the honest words. v: the
coordinates of the sending's seed. -/
def answer (c : Chal) (o : Nat) (s : OracleShape) (v : Nat) (l : List E) : E :=
  let sd := (K1.cutSeeds v 1 l).headD ([], zeroE)
  valueE allSent (K1.sampleRow (K1.Msg.of codes s) o sd.1 sd.2 0 zeroE) (words {} c)

/-- The honest scalar. -/
def mu (c : Chal) : E := muAtE shape c.psi c.zeta (rowE {}) kappa

/-- The rounds of the eight sub-protocols, and the columns that "LOC" is handed. -/
def roundsOf (t : Turn) (c : Chal) : List (List Fmt.RoundView × List (List (Nat × List UInt64))) :=
  let aU := bump t.answerU (answer c 0 shape.fold.u 5 c.seedU)
  let aO := bump t.answerOmega (answer c 2 shape.omega 2 c.seedOmega)
  let aS := bump t.answerSp (answer c 3 shape.sharedSplit 2 c.seedOmega)
  [([⟨[], draws c.psi⟩], []),
   ([⟨[], draws c.seedU⟩, ⟨[.answer aU.triple], draws []⟩], []),
   ([], []),
   ([⟨[], draws [] c.locs⟩], [c.locs.map fun x => (x % 64, (List.range 4).map fun r =>
      addF (symbol {} r (x % 64)) (if r == 2 && x == 17 then UInt64.ofNat t.column else 0))]),
   ([⟨[], draws c.seedOmega⟩, ⟨[.answer aO.triple, .answer aS.triple], draws []⟩], []),
   ([], []),
   ([⟨[], draws c.zeta⟩], []),
   ([⟨[.e (bump t.mu (mu c)).triple], draws []⟩], [])]

/-- The eight decisions in a row, from the first state at a key. -/
def runAt (k : TableKey) (t : Turn) (c : Chal) : Except String St :=
  match blocks P with
  | none => .error "no blocks"
  | some bs =>
    (bs.zip (roundsOf t c)).foldl
      (fun d x => d.bind fun s => x.1.decide s x.2.1 x.2.2) (.ok (first codes k))

/-- At the key of the trial's committed table. -/
def run (t : Turn) (c : Chal) : Except String St := runAt (key t) t c

/-- Constraint by constraint: does it hold of the trial's words? -/
def each (d : St) (l : List Row) (t : Turn) (c : Chal) : List Bool :=
  l.map fun r => decide (valueE d.st r (words t c) = r.target)

/-- **Behind the run**: for each open constraint on G_u, for each on G_omega, and for each sample
row, in the messages' order: whether it holds of the trial's words. -/
def holds (t : Turn) (c : Chal) : Option (List Bool × List Bool × List Bool) :=
  (run t c).toOption.map fun d =>
    (each d (rowsOn d d.loc.gU) t c, each d (rowsOn d d.loc.gOmega) t c,
      each d (d.st.oracles.toList.flatMap (·.sampleRows.toList)) t c)

/-- Short names for the lists below. -/
abbrev yes : Bool := true
abbrev no : Bool := false

/-! ## The lines -/

-- the eight pass their own tests on the plan, and accept, at three lists of challenges
#guard (blocks P).map (·.all (·.planOk)) == some true
#guard (run {} (chal 0)).toOption.isSome && (run {} (chal 7)).toOption.isSome &&
  (run {} (flat oneE)).toOption.isSome
-- on G_u: (rec_gamma) twice, (loc_x) three times, (fold_u); on G_omega: (fold_omega); the sample
-- rows of o_u, o_omega, o_sp: ALL TEN HOLD of the honest words
#guard holds {} (chal 0) == some ([yes, yes, yes, yes, yes, yes], [yes], [yes, yes, yes])
#guard holds {} (chal 7) == some ([yes, yes, yes, yes, yes, yes], [yes], [yes, yes, yes])
#guard holds {} (flat oneE) == some ([yes, yes, yes, yes, yes, yes], [yes], [yes, yes, yes])
-- the decisions read none of the values below: they accept the changed ones too.
-- the scalar: both halves of (fold) fail, and nothing else
#guard holds { mu := 1 } (chal 0) == some ([yes, yes, yes, yes, yes, no], [no], [yes, yes, yes])
-- entry 3 of the folded row: every constraint on G_u reads it; so does o_u's sample row
#guard holds { u := 1 } (chal 0) == some ([no, no, no, no, no, no], [yes], [no, yes, yes])
-- entry 1 of omega_col: (fold_omega), and o_omega's sample row
#guard holds { omega := 1 } (chal 0) == some ([yes, yes, yes, yes, yes, yes], [no], [yes, no, yes])
-- the mask's entry: both halves of (fold), and o_sp's sample row
#guard holds { kappa := 1 } (chal 0) == some ([yes, yes, yes, yes, yes, no], [no], [yes, yes, no])
-- a key made of another committed table: (rec_gamma) at both seeds
#guard holds { table := 1 } (chal 0) == some ([no, no, yes, yes, yes, yes], [yes], [yes, yes, yes])
-- a column, at the second location, that is not the table's: that (loc_x)
#guard holds { column := 1 } (chal 0) ==
  some ([yes, yes, yes, no, yes, yes], [yes], [yes, yes, yes])
-- a pad or an answer: that message's sample row
#guard holds { padU := 1 } (chal 0) == some ([yes, yes, yes, yes, yes, yes], [yes], [no, yes, yes])
#guard holds { padOmega := 1 } (chal 0) ==
  some ([yes, yes, yes, yes, yes, yes], [yes], [yes, no, yes])
#guard holds { padSp := 1 } (chal 0) == some ([yes, yes, yes, yes, yes, yes], [yes], [yes, yes, no])
#guard holds { answerU := 1 } (chal 0) ==
  some ([yes, yes, yes, yes, yes, yes], [yes], [no, yes, yes])
#guard holds { answerOmega := 1 } (chal 0) ==
  some ([yes, yes, yes, yes, yes, yes], [yes], [yes, no, yes])
#guard holds { answerSp := 1 } (chal 0) ==
  some ([yes, yes, yes, yes, yes, yes], [yes], [yes, yes, no])
-- a key whose first OOD seed has the factor 0 is rejected under that clause's own name, at the
-- honest rounds
#guard (match runAt { key {} with seeds := [⟨(seeds.headD default).z, zeroE⟩] ++ seeds.drop 1 } {}
      (chal 0) with
    | .error e => e
    | .ok _ => "accepts") == "not met: no seed of the record has the factor 0"

/-! ## Sent values as numbers, by the formula in the head -/

-- all challenges 0: j = 0, t = 0, r = 0: the table's entry 1, plus kappa = (1000, 2000, 3000)
#guard (mu (flat zeroE)).triple == (1001, 2000, 3000)
-- all challenges 1: eq(z_fd, .) picks j = 3, and the matrix has three rows: nothing but kappa
#guard (mu (flat oneE)).triple == (1000, 2000, 3000)
-- (that line fails only if BOTH bounds on the matrix's rows are lost, omegaHonE's and muHonE's)
-- psi_sh all 1, z_fd = (0, 1): j = 2, t = 1, r = 3: row 3's place 5 holds 306
#guard (mu { flat oneE with zeta := [zeroE, oneE] }).triple == (1306, 2000, 3000)
-- psi_lo = 0, gamma = (1, 0), z_fd = (1, 0): j = 1, t = 0, r = 1: row 1's place 2 holds 103
#guard (mu { flat zeroE with psi := [zeroE, oneE, zeroE], zeta := [oneE, zeroE] }).triple ==
  (1103, 2000, 3000)

-- at the first and the second list, where products of elements outside the base field occur:
-- computed apart from this file, without running it, in whole numbers, two ways
#guard (mu (chal 0)).triple ==
  (6725129374282406393, 16068485999762459927, 7145759265900491532)
#guard (mu (chal 7)).triple ==
  (3558002817821568987, 10585351576885869426, 11533501416133547431)

/-! ## The print -/

/-- Lines for a print: a pure definition; nothing is run when this file is compiled. -/
def printLines : List String :=
  [s!"mu at the first list: {(mu (chal 0)).triple}",
   s!"the three answers: {(answer (chal 0) 0 shape.fold.u 5 (chal 0).seedU).triple} {
     (answer (chal 0) 2 shape.omega 2 (chal 0).seedOmega).triple} {
     (answer (chal 0) 3 shape.sharedSplit 2 (chal 0).seedOmega).triple}",
   s!"which constraints hold, honest: {holds {} (chal 0)}",
   s!"which constraints hold, mu + 1: {holds { mu := 1 } (chal 0)}"]

end Desc.K14.Honest.Toy
