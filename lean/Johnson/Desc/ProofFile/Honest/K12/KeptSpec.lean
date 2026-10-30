-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/KeptSpec.lean: four statements, L-1 to L-4, on which random values
`runBy` (RunBy.lean), `testAll` (Test.lean) and `memOfSending` (JobShared.lean) read, as ten named
`Prop`s, with the definitions that they need. No statement is proved here. Eight are proved:
`Spec.src_reads`, `Spec.kept_perm` and `Spec.src_nodup` (KeptLaw2.lean); `Spec.mem_reads`,
`Spec.spot_reads`, `Spec.spot_perm` and `Spec.spots_tab` (KeptLaw3.lean); `Spec.first_reads`
(KeptLaw4.lean). No statement of this library concludes `Spec.kept_reads` (L-1) or
`Spec.test_reads`. Near the second, in other letters: `stagesAll_same` (Sim/Reads.lean): the text of
the stages is the same at two values of `BCoins` and two states of the prover that agree inside the
stages' sizes; it names neither `testAll` nor `TestCoins`.

  `CoinAt`, `Sorted.read`, `Sorted.set`   an address of a `Sorted` (Run.lean); the value at it; a
                 `Sorted` with another value at one address
  `hideNums`, `grid`, `keptRide`, `keptSwitch`, `keptFrom`, `keptOf`   the kept addresses of a list
                 of stages: those whose values a run reads and does not drop
  `CoinSrc`, `TestCoins.read`, `srcOf`, `allSrc`   a number of a `TestCoins` outside the members'
                 values; the value at it; the number that `sortedOf` (RunOf.lean) reads for an
                 address; all numbers within the counts
  `Spot`, `Laid.read`, `spotsOf`, `coinOf`   a place in a message's four tables; the entry there;
                 the places that `rowsOfLaid` tabulates; the number of the random value that stands
                 at a place of a message that is no fresh table
  `Spec.kept_reads`   L-1. Where the stages pass `StagesOk`: two families of random values that
                 agree at the kept addresses give the same result of `runBy` at `Seams.lib`,
                 warnings included
  `Spec.src_reads`, `Spec.kept_perm`, `Spec.src_nodup`   L-2. `sortedOf` at an address is the value
                 at `srcOf`, encoded. Where the stages pass `StagesOk`, `srcOf` maps the list of
                 kept addresses onto a rearrangement of `allSrc`, which has no repeat: one to one,
                 within the counts, and onto
  `Spec.test_reads`   L-1 and L-2 on the side of `testAll`, at `R.toTest` for a job R on words
                 (RunJob.lean). At a general `TestJob` this form is false: `trees₀` is handed all
                 the fresh table's tails
  `Spec.mem_reads`, `Spec.spot_reads`, `Spec.spot_perm`, `Spec.spots_tab`   L-3. A member's rows
                 depend on its random values below `dueOf` alone. At a place with a number the entry
                 is the value of that number; at another place it does not depend on the values. The
                 places' numbers are a rearrangement of 0 to `dueOf` - 1: this one under
                 `msgShapeFits` (Johnson/Desc/ProofFile/Honest/K14/SendingsShapes.lean), a clause of
                 `sendingsFit`. `rowsOfLaid` tabulates the entries at the places of `spotsOf`. The
                 first three speak of a message that is no fresh table
  `Spec.first_reads`   L-4. Where the stages pass `StagesOk`: the messages of the first part's
                 rounds do not depend on the switches' random values, nor, where the fresh table was
                 sent before the test, on that table's tails

The kept addresses. Under i = 1: what rides with the first stage. At the switch from stage j to
stage j + 1, under i = j + 2: the new main rows' tails; the free entries n < `freeRoom` - 1; the
pad; the new mask rows' tails; what rides with the new stage. What rides with a stage that is not
the last: the 2 k + 1 coefficients of the hiding polynomial, under the numbers of `hideOf` (0, and 2
l + t for l from 1 to k and t = 1, 2), and the fresh table's rows' tails. With the last stage: the
masking word's four lists.

Limits. This file holds statements only. `keptOf` is written by hand beside the code. L-1 ties it to
`runBy` one way: the result does not depend on what is not kept. L-2 bounds it from the other side:
every number within the counts is the source of one kept address. L-1 changes the field `coin` of a
`RunIn` alone: at `RunIn.ofTest` (RunOf.lean) the fields `trees` and `first` are made of the same
`TestCoins`, so L-1 by itself does not compare two such inputs; `Spec.test_reads` does, at
`R.toTest`. That a run's result depends on every kept address is no statement here. `srcOf` repeats
the offsets of `sortedOf`, and `coinOf` those of `laid`
(Johnson/Desc/ProofFile/Honest/K14/Sendings.lean); `Spec.src_reads` and `Spec.spot_reads` are the
statements that they agree. L-1 is stated at `Seams.lib`: another `Seams` could read what `csOwnG`
drops. L-3 ends at a member's rows: no statement here carries them into the first stage's rows of a
run. The hypotheses of L-4 are equations of whole functions, which the `TestCoins` of the test's own
two parts do not satisfy: see `Spec.first_reads_in` and `Spec.first_meets` (LentSpec.lean). Not
stated here, L-5: the step from the random values that a part is lent to a `TestCoins`
(`firstPartBy`, `restPartBy`, PartsBy.lean): LentSpec.lean, of whose eleven statements one is proved
whole (`first_reads_in`, LentLaw3.lean). None of the statements says that values are distinct, or
how they are sampled. Nothing on completeness, soundness or hiding.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.RunOf
import Johnson.Desc.ProofFile.Honest.K12.RunBy
import Johnson.Desc.ProofFile.Honest.K12.Parts
import Johnson.Desc.ProofFile.Honest.K12.JobShared
import Johnson.Desc.ProofFile.Honest.K14.SendingsShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (Codes OracleShape)
open OnBytes.Slice (GE ofE)
open Fmt.M1 (E Stage)
open ProofFile.Honest.K14 (Laid laid dueOf MsgSort SendJob Ask)

/-! ## 1 The kept addresses -/

/-- An address of a `Sorted`. -/
inductive CoinAt where
  | main (i b n : ℕ)
  | mask (i b n : ℕ)
  | hide (i n : ℕ)
  | fresh (i b n : ℕ)
  | free (i n : ℕ)
  | pad (i : ℕ)
  | word (i j n : ℕ)
  deriving DecidableEq, Repr

/-- The value at an address. -/
def Sorted.read (K : Sorted) : CoinAt → E
  | .main i b n => K.main i b n
  | .mask i b n => K.mask i b n
  | .hide i n => K.hide i n
  | .fresh i b n => K.fresh i b n
  | .free i n => K.free i n
  | .pad i => K.pad i
  | .word i j n => K.word i j n

/-- K with the value v at the address a. -/
def Sorted.set (K : Sorted) (a : CoinAt) (v : E) : Sorted :=
  { main := fun i b n => if a = .main i b n then v else K.main i b n
    mask := fun i b n => if a = .mask i b n then v else K.mask i b n
    hide := fun i n => if a = .hide i n then v else K.hide i n
    fresh := fun i b n => if a = .fresh i b n then v else K.fresh i b n
    free := fun i n => if a = .free i n then v else K.free i n
    pad := fun i => if a = .pad i then v else K.pad i
    word := fun i j n => if a = .word i j n then v else K.word i j n }

/-- The numbers of `Fmt.M1.Own.hideOf` that a fold of k variables reads. -/
def hideNums (k : ℕ) : List ℕ :=
  0 :: (List.range k).flatMap fun l => [2 * (l + 1) + 1, 2 * (l + 1) + 2]

/-- f b n for b < r and n < m, row by row. -/
def grid {α : Type} (r m : ℕ) (f : ℕ → ℕ → α) : List α :=
  (List.range r).flatMap fun b => (List.range m).map (f b)

/-- What rides with stage s, under i. -/
def keptRide (i : ℕ) (s : Stage) (last : Bool) : List CoinAt :=
  if last then
    (List.range s.C.l).map (.word i 0) ++ (List.range s.Z.l).map (.word i 1) ++
      (List.range s.C.r).map (.word i 2) ++ (List.range s.Z.r).map (.word i 3)
  else (hideNums s.k).map (.hide i) ++ grid (2 ^ s.h) s.Z.r (.fresh i)

/-- The kept addresses of a switch, under i. -/
def keptSwitch (i : ℕ) (cur next : Stage) (last : Bool) : List CoinAt :=
  grid (2 ^ next.k) next.C.r (.main i) ++ (List.range (freeRoom cur next - 1)).map (.free i) ++
    [.pad i] ++ grid (2 ^ next.h) next.Z.r (.mask i) ++ keptRide i next last

/-- The kept addresses of the switches from stage j on. -/
def keptFrom : ℕ → Stage → List Stage → List CoinAt
  | _, _, [] => []
  | j, cur, next :: rest =>
    keptSwitch (j + 2) cur next rest.isEmpty ++ keptFrom (j + 1) next rest

/-- **The kept addresses of a list of stages.** -/
def keptOf : List Stage → List CoinAt
  | [] => []
  | s :: rest => keptRide 1 s rest.isEmpty ++ keptFrom 0 s rest

/-! ## 2 Where `sortedOf` takes an address's value from -/

/-- A number of a `TestCoins`, outside the members' values. -/
inductive CoinSrc where
  | hide (n : ℕ)
  | tails (b n : ℕ)
  | rest (n : ℕ)
  deriving DecidableEq, Repr

/-- The value at a number. Declared in the namespace of `TestCoins`, ProofFile.Honest.K12, so that
`C.read` can be written. -/
def _root_.ProofFile.Honest.K12.TestCoins.read (C : TestCoins) : CoinSrc → GE
  | .hide n => C.hide n
  | .tails b n => C.tails b n
  | .rest n => C.rest n

/-- The number that `sortedOf stages` reads for an address. -/
def srcOf (stages : List Stage) : CoinAt → CoinSrc :=
  let s (i : ℕ) : Stage := stages.getD (i - 1) default
  let m (i : ℕ) : Marks := marksAt stages (i - 2)
  let hide (i n : ℕ) : CoinSrc := if i = 1 then .hide n else .rest ((m i).ride + n)
  fun
  | .main i b n => .rest ((m i).main + b * (s i).C.r + n)
  | .mask i b n => .rest ((m i).mask + b * (s i).Z.r + n)
  | .hide i n =>
    if n = 0 then hide i (2 * ((s i).k - 1))
    else if (n - 1) / 2 < (s i).k then
      hide i (2 * ((n - 1) / 2 - 1) + (n - 2 * ((n - 1) / 2) - 1))
    else hide i (2 * ((s i).k - 1) + (n - 2 * ((n - 1) / 2)))
  | .fresh i b n =>
    if i = 1 then .tails b n else .rest ((m i).ride + (2 * (s i).k + 1) + b * (s i).Z.r + n)
  | .free i n => .rest ((m i).free + n)
  | .pad i => .rest ((m i).free + freeRoom (stages.getD (i - 2) default) (s i) - 1)
  | .word i j n =>
    match j with
    | 0 => .rest ((m i).ride + (s i).C.r + n)
    | 1 => .rest ((m i).ride + (s i).C.r + (s i).C.l + n)
    | 2 => .rest ((m i).ride + n)
    | _ => .rest ((m i).ride + (s i).C.r + (s i).C.l + (s i).Z.l + n)

/-- All numbers within the counts: the first fold's 2 k + 1 coefficients, its fresh table's rows'
tails, the switches' `dueRest` values. -/
def allSrc : List Stage → List CoinSrc
  | [] => []
  | s :: rest =>
    (List.range (2 * s.k + 1)).map .hide ++ grid (2 ^ s.h) s.Z.r .tails ++
      (List.range (dueRest (s :: rest))).map .rest

/-! ## 3 Where a random value stands in a member's rows -/

/-- A place in a message's four tables: row, then entry. -/
inductive Spot where
  | main (r j : ℕ)
  | mainTail (r t : ℕ)
  | mask (r j : ℕ)
  | maskTail (r t : ℕ)
  deriving DecidableEq, Repr

/-- The entry at a place. Declared in the namespace of `Laid`, ProofFile.Honest.K14, whose other names are
in Johnson/Desc/ProofFile/Honest/K14/, so that `L.read` can be written. -/
def _root_.ProofFile.Honest.K14.Laid.read (L : Laid) : Spot → OnBytes.E
  | .main r j => L.main r j
  | .mainTail r t => L.mainTail r t
  | .mask r j => L.mask r j
  | .maskTail r t => L.maskTail r t

/-- The places that `rowsOfLaid` tabulates. -/
def spotsOf (codes : Codes) (s : OracleShape) : List Spot :=
  let c := codes.base.getD s.code default
  let z := codes.mask.getD s.maskCode default
  grid s.mainRows c.ell .main ++ grid s.mainRows c.r .mainTail ++ grid s.maskRows z.ell .mask ++
    grid s.maskRows z.r .maskTail

/-- The number of the random value that stands at a place of a message that is no fresh table; none
where the vector's entry stands. -/
def coinOf (codes : Codes) (s : OracleShape) : Spot → Option ℕ :=
  let c := codes.base.getD s.code default
  let z := codes.mask.getD s.maskCode default
  let atPad := s.mainRows * c.r
  let atMask := atPad + (if s.maskRows == 0 then s.answers else 0)
  let atTail := atMask + s.maskRows * z.ell
  fun
  | .main r j =>
    if s.maskRows == 0 && r + 1 == s.mainRows && decide (c.ell - s.answers ≤ j) &&
        decide (j < c.ell) then some (atPad + (j - (c.ell - s.answers)))
    else none
  | .mainTail r t => some (r * c.r + t)
  | .mask r j => some (atMask + j * s.maskRows + r)
  | .maskTail r t => some (atTail + r * z.r + t)

/-! ## 4 The statements -/

/-- L-1. Where the stages pass `StagesOk`, two families of random values that agree at the kept
addresses give the same result of `runBy` at `Seams.lib`. -/
def Spec.kept_reads : Prop :=
  ∀ (I : RunIn) (K' : Sorted) (D : ℕ → Fmt.Drawn), StagesOk I.p.nums.stages = true →
    (∀ a ∈ keptOf I.p.nums.stages, I.coin.read a = K'.read a) →
    runBy Seams.lib I D = runBy Seams.lib { I with coin := K' } D

/-- L-2, first half. `sortedOf` at an address is the value at `srcOf`, encoded. The encoding is
`ofE`; `toE` reads the value back (`toE_ofE`, OnBytes/Slice/Field.lean). -/
def Spec.src_reads : Prop :=
  ∀ (stages : List Stage) (C : TestCoins) (a : CoinAt),
    (sortedOf stages C).read a = ofE (C.read (srcOf stages a))

/-- L-2, second half. Where the stages pass `StagesOk`: on the kept addresses `srcOf` is one to one,
within the counts, and onto. -/
def Spec.kept_perm : Prop :=
  ∀ (stages : List Stage), StagesOk stages = true →
    ((keptOf stages).map (srcOf stages)).Perm (allSrc stages)

/-- L-2, third part. `allSrc` has no repeat, so that `Spec.kept_perm` says "one to one". -/
def Spec.src_nodup : Prop := ∀ (stages : List Stage), (allSrc stages).Nodup

/-- L-1 and L-2 on the side of `testAll`, at a job on words whose stages pass `StagesOk`: two
families of random values with the same members' values that agree at all numbers within the counts
give the same result. -/
def Spec.test_reads : Prop :=
  ∀ (W X : Type) (R : RunJob W X) (w : W) (fr : Front X) (C C' : TestCoins) (D : ℕ → Fmt.Drawn),
    StagesOk R.p.nums.stages = true → C.mem = C'.mem →
    (∀ x ∈ allSrc R.p.nums.stages, C.read x = C'.read x) →
    testAll R.toTest w fr C D = testAll R.toTest w fr C' D

/-- L-3, first part. The rows of a member whose message is no fresh table depend on its random
values below `dueOf` alone. -/
def Spec.mem_reads : Prop :=
  ∀ (W X : Type) (J : SendJob) (at_ : Addr) (k : ℕ) (fs : Option ℕ × Option ℕ) (ask : W → Ask)
    (v? : Option (W → Front X → ℕ → OnBytes.E)) (w : W) (fr : Front X) (c c' : Stretch)
    (high : Bool), J.sort k = .plain high →
    (∀ i < dueOf J.Q.codes (J.Q.sent.getD k default).shape (J.sort k), c.e i = c'.e i) →
    (memOfSending J at_ k fs ask v?).rows w fr c = (memOfSending J at_ k fs ask v?).rows w fr c'

/-- L-3, second part. At a place with a number the entry is the value of that number; at another
place the entry does not depend on the values. -/
def Spec.spot_reads : Prop :=
  ∀ (codes : Codes) (s : OracleShape) (v cs : ℕ → OnBytes.E) (high : Bool) (x : Spot),
    (laid codes s v cs (.plain high)).read x =
      match coinOf codes s x with
      | some i => cs i
      | none => (laid codes s v (fun _ => OnBytes.zeroE) (.plain high)).read x

/-- L-3, third part. Where the shape passes `msgShapeFits`: the numbers at the tabulated places are
0 to `dueOf` - 1, each once. -/
def Spec.spot_perm : Prop :=
  ∀ (codes : Codes) (s : OracleShape) (high : Bool),
    ProofFile.Honest.K14.msgShapeFits codes s (.plain high) = true →
    ((spotsOf codes s).filterMap (coinOf codes s)).Perm
      (List.range (dueOf codes s (.plain high)))

/-- L-3, fourth part. `rowsOfLaid` tabulates the entries at the places of `spotsOf`, in their order,
each as its triple of words. `memOfSending` makes an entry of a member's encoded value by
`E.ofTriple`, and `triple` gives that triple back (`triple_ofTriple`, OnBytes/Base.lean); no
statement here joins the two. -/
def Spec.spots_tab : Prop :=
  ∀ (codes : Codes) (s : OracleShape) (L : Laid),
    (rowsOfLaid codes s L).M.flatten ++ (rowsOfLaid codes s L).Rh.flatten ++
        (rowsOfLaid codes s L).W.flatten ++ (rowsOfLaid codes s L).Sg.flatten =
      (spotsOf codes s).map fun x => (L.read x).triple

/-- L-4. Where the stages pass `StagesOk`: the messages of the first part's rounds do not depend on
the switches' random values, nor, where the fresh table was sent before the test, on that table's
tails. -/
def Spec.first_reads : Prop :=
  ∀ (W X : Type) (J : TestJob W X) (w : W) (fr : Front X) (C C' : TestCoins) (D : ℕ → Fmt.Drawn)
    (i : ℕ), StagesOk J.p.nums.stages = true → i < firstLen J.p.nums.stages →
    C.hide = C'.hide → C.mem = C'.mem → (J.fresh.isNone = true → C.tails = C'.tails) →
    msgAt J w fr C D i = msgAt J w fr C' D i

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.CoinAt
#print axioms ProofFile.Honest.K12.Light.Sorted.read
#print axioms ProofFile.Honest.K12.Light.Sorted.set
#print axioms ProofFile.Honest.K12.Light.hideNums
#print axioms ProofFile.Honest.K12.Light.grid
#print axioms ProofFile.Honest.K12.Light.keptRide
#print axioms ProofFile.Honest.K12.Light.keptSwitch
#print axioms ProofFile.Honest.K12.Light.keptFrom
#print axioms ProofFile.Honest.K12.Light.keptOf
#print axioms ProofFile.Honest.K12.Light.CoinSrc
#print axioms ProofFile.Honest.K12.TestCoins.read
#print axioms ProofFile.Honest.K12.Light.srcOf
#print axioms ProofFile.Honest.K12.Light.allSrc
#print axioms ProofFile.Honest.K12.Light.Spot
#print axioms ProofFile.Honest.K14.Laid.read
#print axioms ProofFile.Honest.K12.Light.spotsOf
#print axioms ProofFile.Honest.K12.Light.coinOf
#print axioms ProofFile.Honest.K12.Light.Spec.kept_reads
#print axioms ProofFile.Honest.K12.Light.Spec.src_reads
#print axioms ProofFile.Honest.K12.Light.Spec.kept_perm
#print axioms ProofFile.Honest.K12.Light.Spec.src_nodup
#print axioms ProofFile.Honest.K12.Light.Spec.test_reads
#print axioms ProofFile.Honest.K12.Light.Spec.mem_reads
#print axioms ProofFile.Honest.K12.Light.Spec.spot_reads
#print axioms ProofFile.Honest.K12.Light.Spec.spot_perm
#print axioms ProofFile.Honest.K12.Light.Spec.spots_tab
#print axioms ProofFile.Honest.K12.Light.Spec.first_reads
