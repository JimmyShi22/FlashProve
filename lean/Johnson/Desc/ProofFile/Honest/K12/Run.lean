-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Run.lean: the building blocks of `runBy` (RunBy.lean), which
computes a prover's side of a proximity test (`KindName.K12`) on field elements stored as triples of
64-bit words. Definitions only. It imports Fmt/M1Own.lean and Johnson/Desc/K12/JoinGuarded.lean; no
Mathlib.

  `Tree`         a tree's depth and column function; a field of `Seams` returns one
  `denseAt`      a claim's row of coefficients, expanded into two arrays of words
  `Seams`, `Seams.lib`   the five expensive functions of a run as fields of a structure, so that
                 faster versions can be passed in (Halve.lean, FastW.lean); the originals: four
                 from Fmt/ (`colOf` paired with the stage's depth), and `denseAt`
  `Sorted`, `Sorted.ofTags`   the prover's random values ("coins"), one function for each use; the
                 numbering of Fmt/M1Own.lean in that form
  `rideCoin`, `ridersBy`, `hideBy`   `riders` and `hideOf` of Fmt/M1Own.lean, reading a `Sorted`
  `nextBy`       from one stage's rows to the next stage's
  `groupOf`      a tree's columns at sampled positions
  `RunIn`        the input of `runBy`

Why `Sorted`. Fmt/M1Own.lean reads every coin as `coin tag n` with tag = 100 i + an offset. At a
stage made by a switch with more than 20 main rows or more than 10 mask rows two tags coincide, and
one coin would be used twice. Such stages occur: counting from 0, stage 1 of `piUFull` has 32 main
rows and stage 4 of `piLFull` has 16 mask rows (Johnson/Desc/K12/Law/PlacesFull.lean). `Sorted`
gives each use an address of its own. Stage j of the test, counted from 0, has its coins under i = j
+ 1.

Three definitions repeat others that cannot be used as they are. `nextBy` repeats `nextSt`
(Fmt/M1Own.lean), which calls `csOwnG` and builds the tags in its body, so neither can be passed in.
No theorem here relates the two. `groupOf` and `Tree` repeat `groupAt`
(Johnson/Prover/Link/BodyAll.lean) and `Tree` (Johnson/Desc/K12/Honest/Stages.lean), whose files
import Mathlib (`groupOf_eq`, RunBySpec.lean).

Limits.
- `Seams.lib` is slow; Halve.lean, Fast.lean, FastCol.lean, FldW.lean and FastDense.lean say why.
  Nothing is measured.
- Nothing checks the fields of `RunIn` against each other.
- Whether two addresses of a `Sorted` hold independent values is up to whoever builds it. That,
  where the stages pass `StagesOk`, the result of a run at `Seams.lib` does not depend on the values
  outside the addresses of `keptOf` is `Spec.kept_reads` (KeptSpec.lean): no statement of this
  library concludes it. That it depends on each of these is not proved.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Fmt.M1Own
import Johnson.Desc.K12.JoinGuarded

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Fmt (Fld)
open Fmt.M1 (E Stage GRow csOwnG)
open Fmt.M1.Own (PSt rowsOf tabOf colOf riders hideOf)
open VerifiableInference.Desc.K12 (P12 T12 dense)

/-! ## 1 The parameters, and the step from one stage to the next -/

/-- A tree: its depth, and its column at a position, as words. -/
abbrev Tree : Type := Nat × (Nat → List UInt64)

/-- **A claim's row of coefficients, expanded into two arrays of words.** For the main table: 2 ^ n
entries, n := k + the least number of bits for a row's message. For the mask table: 2 ^ h * Z.l
entries, cut or padded with 0. Slow (one pass over all tensors for each entry) where some tensor's
number of variables is not n. -/
def denseAt (row : OnBytes.GroupRow) (s : Stage) : GRow :=
  let n := s.k + OnBytes.ceilLog2 s.C.l
  ⟨if row.c.tensors.all (fun v => v.vars == n) then dense row.c n
    else Array.ofFn (n := 2 ^ n) fun i => (row.c.entry i.val).triple,
    Array.ofFn (n := 2 ^ s.h * s.Z.l) fun i => (row.d.getD i.val OnBytes.zeroE).triple,
    row.target.triple⟩

/-- **The five expensive functions of a run**, as fields, so that faster versions can be passed in
(`Seams.lib`; `Seams.halving`, Halve.lean; `Seams.fast`, FastW.lean). -/
structure Seams where
  /-- a fold's rounds: what is sent, and with it the linear coefficient. The `List E` argument: the
  elements sampled in the fold's rounds -/
  rounds : Fld → Fmt.M1.FoldOwn.Trial → List E → List ((E × E) × E)
  /-- the main table and the mask table of the oracle message that a code switch sends: the
  arguments of `csOwnG` -/
  folded : Fld → Stage → Stage → List E → List (List E) → List (List E) → List (List E) →
    List (List E) → List (List E) → List (List E) → List E → E → Array E × Array E
  /-- rows of n entries as one table: entry c of row b is at index b + (number of rows) * c. The
  arguments of `tabOf` -/
  tab : List (List E) → Nat → Array E
  /-- the tree that a code switch sends: the new stage, whether it is the last, its rows and tails.
  A pair, so that what the column function needs can be prepared once, when the pair is built -/
  tree : Stage → Bool → PSt → Tree
  /-- a claim's row of coefficients, expanded: the arguments of `denseAt` -/
  dense : OnBytes.GroupRow → Stage → GRow

/-- The originals. -/
def Seams.lib : Seams :=
  ⟨fun f T g => Fmt.M1.FoldOwn.honest f T [] g, csOwnG, tabOf,
    fun next last Q => (next.C.a, colOf next false last Q), denseAt⟩

/-- **The prover's random values ("coins"), one function for each use.** Arguments: the stage's
number i, the row (where the use has rows), the index in the list. Separate addresses do not make
the values independent: that is up to whoever builds the structure. -/
structure Sorted where
  /-- the tail of a main row -/
  main : Nat → Nat → Nat → E
  /-- the tail of a mask row -/
  mask : Nat → Nat → Nat → E
  /-- the hiding polynomial's coefficients, by the numbers of `hideOf` -/
  hide : Nat → Nat → E
  /-- the tail of a row of the fresh table -/
  fresh : Nat → Nat → Nat → E
  /-- the free entries of the oracle message that makes the stage -/
  free : Nat → Nat → E
  /-- that message's pad -/
  pad : Nat → E
  /-- the masking word's four lists: main row, mask row, and their tails -/
  word : Nat → Nat → Nat → E

/-- The numbering of Fmt/M1Own.lean. Main row 20 shares its tag with mask row 0, mask row 10 with
the hiding polynomial, fresh row 10 with the free entries. So at a stage with more than 20 main
rows, or more than 10 mask or fresh rows, two addresses hold one value, and no theorem on a random
value can be stated at this numbering. -/
def Sorted.ofTags (coin : Nat → Nat → E) : Sorted :=
  { main := fun i b => coin (100 * i + b), mask := fun i b => coin (100 * i + 20 + b)
    hide := fun i => coin (100 * i + 30), fresh := fun i b => coin (100 * i + 40 + b)
    free := fun i => coin (100 * i + 50), pad := fun i => coin (100 * i + 51) 0
    word := fun i j => coin (100 * i + 60 + j) }

/-- Translates the tags that `riders` asks for at stage i into addresses of K. If `last` is true
these are the masking word's four tags (100 i + 60 to + 63); otherwise 100 i + 30 (hiding
polynomial) and 100 i + 40 + b (fresh row b). A smaller tag would give another use's value where a
random value is due, because the subtraction truncates; `riders` asks for none (`nx_riders_last`,
`nx_riders_mid`, RunByNext.lean). -/
def rideCoin (K : Sorted) (i : Nat) : Bool → Nat → Nat → E
  | true, tag, n => K.word i (tag - (100 * i + 60)) n
  | false, tag, n =>
    if tag = 100 * i + 30 then K.hide i n else K.fresh i (tag - (100 * i + 40)) n

/-- `Fmt.M1.Own.riders`, reading a `Sorted`. -/
def ridersBy (f : Fld) (K : Sorted) (i : Nat) (s : Stage) (last : Bool) :
    List (List E) × List (List E) :=
  riders f (rideCoin K i last) i s last

/-- `Fmt.M1.Own.hideOf`, reading a `Sorted`. -/
def hideBy (K : Sorted) (i : Nat) : Fmt.M1.FoldOwn.Hide := hideOf (fun _ => K.hide i) i

/-- `Fmt.M1.Own.nextSt` with `csOwnG` and the random values as parameters. It lists 2 ^ h * Z.l
values of `K.free i`; `csOwnG` drops those beyond the mask table's free entries (see `CoinTie`,
RunBySpec.lean). -/
def nextBy (S : Seams) (f : Fld) (K : Sorted) (i : Nat) (old new : Stage) (last : Bool)
    (g : List E) (p : PSt) : PSt :=
  let gg := S.folded f old new g p.M p.Rh p.W p.Sg p.P p.Pi
    ((List.range (2 ^ new.h * new.Z.l)).map (K.free i)) (K.pad i)
  let rd := ridersBy f K i new last
  { M := rowsOf (2 ^ new.k) gg.1,
    Rh := (List.range (2 ^ new.k)).map fun b => (List.range new.C.r).map (K.main i b)
    W := rowsOf (2 ^ new.h) gg.2,
      Sg := (List.range (2 ^ new.h)).map fun b =>
          (List.range new.Z.r).map (K.mask i b), P := rd.1, Pi := rd.2 }

/-! ## 2 The input -/

/-- **The input of `runBy`.** -/
structure RunIn where
  /-- the test's parameters -/
  p : P12
  /-- the first fold sends its own fresh table -/
  own : Bool
  /-- the verifier's state on entry to the test -/
  door : T12
  /-- the first stage's main rows, all 2 ^ k of them, rows of zeros too; their tails; its mask rows;
  their tails. The two fields for the fresh table are not read -/
  first : PSt
  /-- the trees that the first round of positions opens, in the order of the declared openings, as a
  function of the first stage's state, fresh table included -/
  trees : PSt → List Tree
  /-- the random values. Under i = 1 only the hiding polynomial's and the fresh table's are read
  (with fewer than two stages: the masking word's): the first stage's tails are in `first` -/
  coin : Sorted

/-- A tree's columns at the sampled positions. The positions are reduced modulo the tree's length,
sorted, and listed once each (`Fmt.listOf`). Each column comes with its position. -/
def groupOf (x : Tree) (poss : List Nat) : List (Nat × List UInt64) :=
  (Fmt.listOf (poss.map (· % 2 ^ x.1))).map fun y => (y, x.2 y)

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.Tree
#print axioms ProofFile.Honest.K12.Light.denseAt
#print axioms ProofFile.Honest.K12.Light.Seams
#print axioms ProofFile.Honest.K12.Light.Seams.lib
#print axioms ProofFile.Honest.K12.Light.Sorted
#print axioms ProofFile.Honest.K12.Light.Sorted.ofTags
#print axioms ProofFile.Honest.K12.Light.rideCoin
#print axioms ProofFile.Honest.K12.Light.ridersBy
#print axioms ProofFile.Honest.K12.Light.hideBy
#print axioms ProofFile.Honest.K12.Light.nextBy
#print axioms ProofFile.Honest.K12.Light.RunIn
#print axioms ProofFile.Honest.K12.Light.groupOf
