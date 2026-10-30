-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Coins.lean: how many coins the prover's side of a proximity test
takes, in which order they come, and how `BCoins`, the random values that `bodyAll`
(Johnson/Prover/Link/BodyAll.lean) and `stagesAll` (Johnson/Desc/K12/Honest/Stages.lean) take as a
parameter, is read from them. For any list of stages. Definitions only, none marked `noncomputable`;
no theorem. It imports Mathlib.

The order. Whoever makes the book of coins (`ProverCoinCounts`, Johnson/Desc/ProofFile/Honest/Frame.lean) has to
keep it too. All coins here are elements of the extension field.
  A fold's fresh table (k rounds, 2^h rows): the hiding polynomial's 2k + 1 coefficients, variable
    by variable, within a variable by rising degree, degrees 1, 2 for every variable but the last
    and 0, 1, 2 for the last; then the rows' tails, row 0 first.
  A code switch into a stage (k', h'; main code (l, r); mask code (l', r')), out of a stage with
    mask code (l₀', r₀') and main tails of r₀ entries: the 2^k' main rows' tails, row 0 first; the
    free entries of the new mask table, that is, those that are not carried over from the old stage,
    in the order of the table's own index, the pad last: 2^h' l' - (2 l₀' + r₀ + 2 r₀') of them; the
    2^h' mask rows' tails; then what "rides" with the new stage's rows: the next fold's fresh table
    as above, or, into the last stage, the masking word: its main row's tail, its main row's
    message, its mask row's message, its mask row's tail.

  `Stretch`, `Stretch.zero`, `stretchOf`, `stretches`   a stretch is a run of coins, read by number;
                 the stretch without a coin; the coins of a `Cs` (Frame.lean), 0 beyond the count;
                 those of a list of named stretches, by the stretch's number
  `byName`, `hideAt`   a hiding polynomial's coefficients, indexed by the library's type `HIdx`
                 (Cb/Ld/LdHide.lean): from a function of (variable, degree) and the constant; from
                 coins in the order above
  `carriedIn`, `dueFresh`, `dueWord`, `freeRoom`, `dueSwitch`, `dueFrom`, `dueRest`   the counts
  `Marks`, `startAt`, `marksAt`   where, among the coins of all switches, the four stretches of
                 switch number j begin
  `coinsOf`      the `BCoins` read from the first fold's coefficients and the switches' coins

Limits.
- Beyond the count `stretchOf` gives 0, beyond the list `stretches` gives `Stretch.zero`, and a
  row's tail read beyond its length gives the next row's coins: nothing here shows that no
  definition reads there.
- The counts take k from the `Stage`; the library's index type takes h + (k - h): the two are equal
  where h ≤ k, which the block's test on the plan asks (`sizesOk`, Johnson/Desc/K12/Sizes.lean).
- Where the new mask table is too small for what is carried, the subtraction in `freeRoom` gives 0
  free entries.
- The field `new j` of `coinsOf` fills every field of the state (`PS`). After a switch that is not
  the last, its `sM` and `sT` (the masking word's main row and that row's tail) hold coins of the
  next fold's fresh table: these two fields are meant to be read at the last stage alone. Its `fM`
  is 0 there: the caller puts the packing in; `aNext` (Johnson/Desc/K12/Honest/Stages.lean) is such
  a caller.
- In `coinsOf`, outside the counts. (a) `fr j i` subtracts `carriedIn` from i, and the subtraction
  stops at 0: at every i up to `carriedIn` it gives the first free entry's coin. (b) Where i -
  `carriedIn` reaches the number of free entries, it gives the mask rows' tails' coins. (c) `W s j`
  reads 2 (s.h + s.g) + 1 coins at the caller's s, while the count has 2k + 1: where h > k the
  coefficients run on into the fresh table's tails. (d) `W s j` at the last stage's number reads the
  masking word's coins as coefficients. (e) Beyond the list of stages `getD` gives `default`, a
  stage of zeros; `tabM` and `tabZ` of `new j` are the constant 0. Nothing here shows that no
  definition reads at these places.
- No test here. The order is tested where a prover's rounds are compared with another program's
  (Toy.lean).
- Nothing on how a coin is sampled. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Prover.Link.BodyAll
import Johnson.Desc.ProofFile.Honest.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open Johnson.Prover.Link (PS BCoins)

/-! ## 1 Coins by number -/

/-- A run of coins, by number: `f` those of the base field, `e` those of the extension field. -/
structure Stretch where
  f : ℕ → GF
  e : ℕ → GE

/-- The stretch without a coin: 0 at every number. -/
def Stretch.zero : Stretch := ⟨fun _ => 0, fun _ => 0⟩

/-- The coins of a `Cs`, whose type states their count, by number; 0 beyond the count. -/
def stretchOf {d : Due} (c : Cs d) : Stretch :=
  ⟨fun i => if h : i < d.f then c.f ⟨i, h⟩ else 0, fun i => if h : i < d.e then c.e ⟨i, h⟩ else 0⟩

/-- The coins of a list of named stretches, by the stretch's number; beyond the list,
`Stretch.zero`. -/
def stretches : (l : List (String × Due)) → CsAll l → ℕ → Stretch
  | [], _, _ => Stretch.zero
  | d :: l, c, n =>
    let c' : Cs d.2 × CsAll l := c
    match n with
    | 0 => stretchOf c'.1
    | n + 1 => stretches l c'.2 n

/-! ## 2 The hiding polynomial's coefficients -/

/-- Coefficients indexed by the library's type `HIdx`. w l t: the coefficient of variable number l,
counted from 1, at degree t (1 or 2). w0: the constant. -/
def byName : (k : ℕ) → (ℕ → ℕ → GE) → GE → HIdx (sVars GE 2 k) → GE
  | 0, _, w0, _ => w0
  | _ + 1, w, _, .inl t => w 1 (t.val + 1)
  | k + 1, w, w0, .inr i => byName k (fun l t => w (l + 1) t) w0 i

/-- The same from 2k + 1 coins in the order that the file's head gives for a fresh table. -/
def hideAt (k : ℕ) (c : ℕ → GE) : HIdx (sVars GE 2 k) → GE :=
  byName k (fun l t => c (if l < k then 2 * (l - 1) + (t - 1) else 2 * (k - 1) + t))
    (c (2 * (k - 1)))

/-! ## 3 The counts -/

/-- How many entries a switch out of a stage carries into the new mask table: two mask rows'
messages, the main row's tail, two mask rows' tails. -/
def carriedIn (s : Fmt.M1.Stage) : ℕ := 2 * s.Z.l + s.C.r + 2 * s.Z.r

/-- The number of coins of the fresh table of a stage's fold. -/
def dueFresh (s : Fmt.M1.Stage) : ℕ := 2 * s.k + 1 + 2 ^ s.h * s.Z.r

/-- The number of coins of the masking word at the last stage. -/
def dueWord (s : Fmt.M1.Stage) : ℕ := s.C.r + s.C.l + s.Z.l + s.Z.r

/-- The number of free entries (those not carried) of the mask table that a switch makes. -/
def freeRoom (cur next : Fmt.M1.Stage) : ℕ := 2 ^ next.h * next.Z.l - carriedIn cur

/-- The number of coins of a switch. last: the next stage is the last. -/
def dueSwitch (cur next : Fmt.M1.Stage) (last : Bool) : ℕ :=
  2 ^ next.k * next.C.r + freeRoom cur next + 2 ^ next.h * next.Z.r +
    if last then dueWord next else dueFresh next

/-- The number of coins of the switches from a stage on. -/
def dueFrom : Fmt.M1.Stage → List Fmt.M1.Stage → ℕ
  | _, [] => 0
  | cur, next :: rest => dueSwitch cur next rest.isEmpty + dueFrom next rest

/-- **The number of coins of all switches of a test.** -/
def dueRest : List Fmt.M1.Stage → ℕ
  | [] => 0
  | s :: rest => dueFrom s rest

/-! ## 4 Where a switch's stretches begin -/

/-- The number of the first coin of: the main rows' tails, the free entries, the mask rows' tails,
what "rides". -/
structure Marks where
  main : ℕ
  free : ℕ
  mask : ℕ
  ride : ℕ

/-- The number of the first coin of switch number j; j counts from 0. -/
def startAt : Fmt.M1.Stage → List Fmt.M1.Stage → ℕ → ℕ
  | _, [], _ => 0
  | _, _ :: _, 0 => 0
  | cur, next :: rest, j + 1 => dueSwitch cur next rest.isEmpty + startAt next rest j

/-- The `Marks` of switch number j. -/
def marksAt (stages : List Fmt.M1.Stage) (j : ℕ) : Marks :=
  let cur := stages.getD j default
  let next := stages.getD (j + 1) default
  let a := match stages with
    | [] => 0
    | s :: rest => startAt s rest j
  { main := a, free := a + 2 ^ next.k * next.C.r
    mask := a + 2 ^ next.k * next.C.r + freeRoom cur next
    ride := a + 2 ^ next.k * next.C.r + freeRoom cur next + 2 ^ next.h * next.Z.r }

/-! ## 5 `BCoins` -/

/-- **`BCoins`, the random values that the definitions and theorems of Johnson/Prover/Link/ take as
a parameter, read from coins.** hide: the first fold's 2k + 1 coefficients. c: the switches' coins.
-/
def coinsOf (stages : List Fmt.M1.Stage) (hide c : ℕ → GE) : BCoins where
  W := fun s j =>
    hideAt (s.h + s.g) (if j = 0 then hide else fun i => c ((marksAt stages (j - 1)).ride + i))
  new := fun j =>
    let next := stages.getD (j + 1) default
    let m := marksAt stages j
    let last := j + 2 == stages.length
    { tabM := fun _ => 0, tabZ := fun _ => 0
      tM := fun b q => c (m.main + b * next.C.r + q)
      tZ := fun b q => c (m.mask + b * next.Z.r + q)
      fM := fun _ q => if last then c (m.ride + next.C.r + next.C.l + q) else 0
      fT := fun b q =>
        if last then c (m.ride + next.C.r + next.C.l + next.Z.l + q)
        else c (m.ride + (2 * next.k + 1) + b * next.Z.r + q)
      sM := fun q => c (m.ride + next.C.r + q)
      sT := fun q => c (m.ride + q) }
  fr := fun j i => c ((marksAt stages j).free + (i - carriedIn (stages.getD j default)))

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.Stretch
#print axioms ProofFile.Honest.K12.Stretch.zero
#print axioms ProofFile.Honest.K12.stretchOf
#print axioms ProofFile.Honest.K12.stretches
#print axioms ProofFile.Honest.K12.byName
#print axioms ProofFile.Honest.K12.hideAt
#print axioms ProofFile.Honest.K12.carriedIn
#print axioms ProofFile.Honest.K12.dueFresh
#print axioms ProofFile.Honest.K12.dueWord
#print axioms ProofFile.Honest.K12.freeRoom
#print axioms ProofFile.Honest.K12.dueSwitch
#print axioms ProofFile.Honest.K12.dueFrom
#print axioms ProofFile.Honest.K12.dueRest
#print axioms ProofFile.Honest.K12.Marks
#print axioms ProofFile.Honest.K12.startAt
#print axioms ProofFile.Honest.K12.marksAt
#print axioms ProofFile.Honest.K12.coinsOf
