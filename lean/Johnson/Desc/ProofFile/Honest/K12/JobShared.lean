-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/JobShared.lean: makers of the jobs, on words, of the shared
chain's two proximity tests: the one on the group G_u = {o_u, o_sp} and the one on G_omega =
{o_omega, o_sp} (Johnson/Desc/K14/Text.lean). Each member's rows before encoding are the sender's
own: `laid`, the function by which the honest side of the two sendings builds a message's rows
(Johnson/Desc/ProofFile/Honest/K14/Sendings.lean), is called with the member's own random values and
tabulated. The trees and their columns are defined a second time here: which message's rows lie in
which tree is written by hand, and the symbols are computed by `treeW` (ColW.lean, through
`RunIn.ofRun`, RunJob.lean; equal to `treeBy`, RunRows.lean, by `treeW_eq`), where the sendings have
`columnOf` over `treesMade`. No theorem relates the two; JobSharedToy.lean compares them at one
small example. Definitions only. It imports Mathlib.

  `tabE`, `rowsOfLaid`   a function of row and place, tabulated as lists of words; one message's
                 rows in full
  `firstsOf`     the first rows of the members' blocks, by `layBlocks` (OnBytes/Iop/Ground.lean)
  `memOfSending`   message number k of a sending, as a member of a group (`Mem`, RunMany.lean)
  `noState`, `doorOf`   a state on entry to a test: the chain's blocks before the test, folded
                 (`foldBlocks`, Johnson/Desc/Block.lean) over the rounds shown and a list of opened
                 columns, then the seat's `enter`; a state that the caller names where one fails
  `askOf`        the committed table's rows before encoding: `rowsOf` at the two readers
  `depthOf`, `jobAtU`, `jobAtOmega`   the two makers (`ManyJob`)

Random values. `memOfSending` gives `laid` the member's own random values, numbered from 0: the main
rows' tails, the pad of its out-of-domain sample where that lies in a main row, the mask rows'
entries, their tails. `SendJob.rows` gives `laid` the sending's values from the message's offset on.
That the two are the same values is up to whoever gives the test's parts their random values; it is
not checked here. The shapes at which `laid` lays what it is meant to lay are those that
`sendingsFit A.P` accepts (Johnson/Desc/ProofFile/Honest/K14/SendingsShapes.lean): every theorem on
a random value over these two jobs is to take it as a named public hypothesis. o_sp's values stand
in three places of the shared chain: they go into both jobs, and the round "SPLIT" spends entry 0 of
its mask row. So a theorem on either test cannot take them as unused elsewhere. The first fresh
table's values are handled by the test's parts: there the random values that a part is lent become a
`TestCoins` (`firstPartBy`, `restPartBy`, PartsBy.lean).

The vector that o_u or o_omega carries. A caller that already holds it passes it in (u?, omega?); it
is compared with nothing. With `none` the sender's `SendJob.data` computes it from `askOf`. With
`some v` the index committer's pads and tails inside the vector are the caller's: a v computed over
`entriesOf` (Johnson/Desc/ProofFile/Honest/K14/Parts.lean), which has the matrix's places alone, has
0 there, without a warning, and is another folded row than the one that was sent; `RunJob.rowsFit`
and `ManyJob.layFits` stay true. That is o_u's case. The vector of o_omega is computed from the
folded row's entries at the matrix's places alone (`omegaHonE`, Johnson/Desc/K14/Honest/Coded.lean),
where `rowsOf` is `entriesOf`: by reading, without a lemma, no pad or tail of the index committer
stands in it, and `rand` reaches no row of `jobAtOmega`.

The index committer's pads and tails. With `none` they come from the prover's input through the two
readers `weights` and `rand`, by `rowsOf` (Johnson/Desc/ProofFile/Honest/K14/Parts.lean), as in
`proverSidesOfSharedSendings`. By type the readers see the prover's input alone. That they are the readers of
`proverSidesOfSharedSendings` in the same prover's side is up to the caller: a `rand` of zeros gives `entriesOf`.
`memOfSending` takes any function of type W → `Ask`; the two makers fill it by `askOf` alone. u? and
omega? see no member's random values, but they do see what precedes the test, whose rounds are
functions of random values.
`rowsOf` gives the committed rows only where `LinShape.ok` (OnBytes/Iop/Lin.lean) accepts `A.P.S`:
at another shape the matrix's places run into the pads, and `rowsOf` lays an entry of the matrix
where a pad of the index committer is due (the limits of
Johnson/Desc/ProofFile/Honest/K14/Parts.lean). No check here or in FitShared.lean asks it, and
`sendingsFit` does not; SharedSmall.lean evaluates `linOk` at the small example. Under the library's
head `linOk` is a theorem at the shared chain's own parameters (`linOk_at_head`,
Johnson/Desc/ProofFile/Honest/K14/SendingsAtFilling.lean).

Limits.
- The sendings' public data A, the test's parameters p, the two readers and the state on entry are
  parameters. Nothing here takes them from a description, and `StagesOk` at p's stages is up to the
  caller. That A is the one of `proverSidesOfSharedSendings` in the same prover's side is up to the caller too: its
  field `atPoint`, the number of the round "LIN point", is compared with nothing.
- Written for a shape in which the first fresh table goes out with o_u and o_sp exists
  (`masksAhead`, `sharedSplitNeeded`). Otherwise message 1 of a sending does not exist, and the
  member has no rows, without a warning. The same holds where a shape names a code that the table of
  codes lacks. `sendingsFit` is false where o_sp has no row and where a code is lacking; it asks
  neither `masksAhead` nor `sharedSplitNeeded`, which are hypotheses of their own (tests:
  SharedSmall.lean).
- Compared by nothing here: the stages in the shape (`testU`, from which the sending takes the first
  fresh table's k and h) with those in p. Where they differ, the border between the table's
  coefficients and its tails moves, and one value serves as both; `ManyJob.layFits` and
  `RunJob.rowsFit` do not see it; nor is `TestJob.freshFits` (Test.lean) or p's field `ownMask`
  asked here (checks with theorems: FitShared.lean). Nor the pieces of the trees with `treesMade`.
- `ManyJob.layFits` compares the stage's two codes with those of the state's group, not with the
  codes from which `rowsOfLaid` takes its lengths; `RunJob.rowsFit` compares these lengths.
- `firstsOf` passes `layBlocks` the sizes that `Statement.layout` would for members that are not
  kept. Nothing proves that the two agree; `ManyJob.layFits` checks it at a state.
- `doorOf` returns its parameter `fall` where the fold or `enter` fails, without a warning of its
  own, and drops what is left over of rounds and columns. At a `fall` that holds the plan's public
  part alone, `runBy` then computes on an empty claim, with its warnings; nothing refuses. The
  halves ignore these warnings (PartsBy.lean): where a half is used, nothing tells a fold that
  failed from one that returned. `doorOf` reads the input twice: in the chain's first state and in
  `cols`.
- Which columns the blocks before the test have read is a parameter (`cols`). Before the test on
  G_omega these include columns that the test on G_u opened, which depend on that test's random
  values: `cols` cannot compute them. So at the test on G_omega `doorOf` returns `fall` at every
  honest run, as long as a part is handed no opened column.
- So the checks on the state on entry (`ManyJob.layFits`; `pubOf_doorOf`, FitSharedLaw.lean) are
  never to be read as "the state on entry is the verifier's". A statement on what a job sends whose
  `doorOf` falls back is a statement on this text, at a state on entry that is made of the plan's
  public part and is not shown to be the verifier's; it is none on the protocol's honest prover.
- Like the sendings, it supports main rows over the extension field only.
- `jobAtU` and `jobAtOmega` are evaluated at one small example (JobSharedToy.lean), and so is
  `doorOf` (PubAtSmallDoor.lean). Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K14.Sendings
import Johnson.Desc.ProofFile.Honest.K12.RunMany
import Johnson.Desc.K12.Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (Codes OracleShape ceilLog2 layBlocks)
open OnBytes.Slice (ofE)
open Fmt.M1.Own (PSt)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc.K12 (P12 T12)
open ProofFile.Honest.K14 (Laid laid dueOf SendJob SendPub jobU jobOmega sendPlace Ask rowsOf)

variable {W X S₀ : Type}

/-- r rows of n entries, as words. -/
def tabE (r n : ℕ) (f : ℕ → ℕ → OnBytes.E) : List (List Fmt.M1.E) :=
  (List.range r).map fun i => (List.range n).map fun j => (f i j).triple

/-- **One message's rows in full**, as lists of words. -/
def rowsOfLaid (codes : Codes) (s : OracleShape) (L : Laid) : PSt :=
  let c := codes.base.getD s.code default
  let z := codes.mask.getD s.maskCode default
  { M := tabE s.mainRows c.ell L.main, Rh := tabE s.mainRows c.r L.mainTail
    W := tabE s.maskRows z.ell L.mask, Sg := tabE s.maskRows z.r L.maskTail, P := [], Pi := [] }

/-- The first rows of the members' blocks: main, mask; none where a member has no such row. -/
def firstsOf (shapes : List OracleShape) : List (Option ℕ × Option ℕ) :=
  let main := (layBlocks (shapes.map fun s =>
    if s.mainRows == 0 then none else some (ceilLog2 s.mainRows)).toArray).1
  let mask := (layBlocks (shapes.map fun s =>
    if s.maskRows == 0 then none else some (ceilLog2 s.maskRows)).toArray).1
  (List.range shapes.length).map fun i => (main.getD i none, mask.getD i none)

/-- **Message number k of a sending, as a member.** at_: the address of the sending's part. fs: the
first rows of its blocks. ask: the sending's input, computed from the test's. v?: the vector that
its main table carries, where the caller holds it. -/
def memOfSending (J : SendJob) (at_ : Addr) (k : ℕ) (fs : Option ℕ × Option ℕ) (ask : W → Ask)
    (v? : Option (W → Front X → ℕ → OnBytes.E)) : Mem W X :=
  let s := (J.Q.sent.getD k default).shape
  { sent := (at_, k, ⟨0, dueOf J.Q.codes s (J.sort k)⟩)
    shape := ⟨fs.1.getD 0, s.mainRows, fs.2.getD 0, s.maskRows, s.mainDeg == 1⟩
    rows := fun w fr c =>
      rowsOfLaid J.Q.codes s
        (laid J.Q.codes s
          (match v? with
            | some v => v w fr
            | none => J.data ⟨ask w, fr.heard, ()⟩ k)
          (fun i => OnBytes.E.ofTriple (ofE (c.e i))) (J.sort k)) }

/-- A state that holds nothing. -/
def noState : T12 :=
  { st := default, book := default, roots := 0, g := 0, pass := .nothing, mask := none }

/-- **A state on entry to a test**: what the fold and `enter` return, or `fall` where one fails.
bs: the chain's blocks before the test. s₀: the chain's first state. enter: the seat's. cols: the
columns that these blocks have read, in order.
fall: the state that is returned where the fold or `enter` fails; it is meant to hold the plan's
public part and nothing else (`stateOfPub`, FitShared.lean). Where both return, the state is the one
that `enter` returns; that its public part is the plan's too is a hypothesis of `pubOf_doorOf`
(FitSharedLaw.lean). The fold is called with 0 as the number of the first tree, as
Johnson/Desc/Block.lean calls it for the first and the shared chain; for the second chain that file
passes a parameter. -/
def doorOf (bs : List (Block S₀ Unit)) (s₀ : W → S₀) (enter : S₀ → Except String T12)
    (cols : W → Front X → List OpenedColumn) (fall : T12) (w : W) (fr : Front X) : T12 :=
  match foldBlocks 0 bs (s₀ w) fr.seen.rounds (cols w fr) with
  | .ok x => (enter x.1).toOption.getD fall
  | .error _ => fall

/-- The depth of the tree number i of those that the first round of positions opens; 0, without a
warning, where `p.nums.first` has no entry i. -/
def depthOf (p : P12) (i : ℕ) : ℕ := ((p.nums.first[i]?).map (·.1.a)).getD 0

/-- The committed table's rows before encoding, as the sendings' halves read them: `rowsOf` at the
two readers. -/
def askOf (A : SendPub) (weights : W → Weights) (rand : W → TableRand) (w : W) : Ask :=
  ⟨rowsOf A.P.S (weights w) (rand w)⟩

/-- **The test on G_u.** The first fresh table went out with o_u. weights, rand: the two readers, as
in `proverSidesOfSharedSendings`. -/
def jobAtU (A : SendPub) (p : P12) (door : W → Front X → T12) (weights : W → Weights)
    (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E)) : ManyJob W X :=
  let ask := askOf A weights rand
  let fs := firstsOf [((jobU A).Q.sent.getD 0 default).shape,
    ((jobOmega A).Q.sent.getD 1 default).shape]
  { p := p
    mems := [memOfSending (jobU A) ⟨sendPlace 2, 0⟩ 0 (fs.getD 0 (none, none)) ask u?,
      memOfSending (jobOmega A) ⟨sendPlace 5, 0⟩ 1 (fs.getD 1 (none, none)) ask none]
    fresh := some (⟨sendPlace 2, 0⟩, 1), rec₀ := door
    trees := [(depthOf p 0, [.main 0, .fresh]), (depthOf p 1, [.mask 1])] }

/-- **The test on G_omega.** The first fold sends its own fresh table. weights, rand: the two
readers, as in `proverSidesOfSharedSendings`. -/
def jobAtOmega (A : SendPub) (p : P12) (door : W → Front X → T12) (weights : W → Weights)
    (rand : W → TableRand) (omega? : Option (W → Front X → ℕ → OnBytes.E)) : ManyJob W X :=
  let ask := askOf A weights rand
  let fs := firstsOf [((jobOmega A).Q.sent.getD 0 default).shape,
    ((jobOmega A).Q.sent.getD 1 default).shape]
  { p := p
    mems := [memOfSending (jobOmega A) ⟨sendPlace 5, 0⟩ 0 (fs.getD 0 (none, none)) ask omega?,
      memOfSending (jobOmega A) ⟨sendPlace 5, 0⟩ 1 (fs.getD 1 (none, none)) ask none]
    fresh := none, rec₀ := door
    trees := [(depthOf p 0, [.main 0]), (depthOf p 1, [.mask 1]),
      ((p.nums.stages.headD default).Z.a, [.fresh])] }

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.tabE
#print axioms ProofFile.Honest.K12.Light.rowsOfLaid
#print axioms ProofFile.Honest.K12.Light.firstsOf
#print axioms ProofFile.Honest.K12.Light.memOfSending
#print axioms ProofFile.Honest.K12.Light.noState
#print axioms ProofFile.Honest.K12.Light.doorOf
#print axioms ProofFile.Honest.K12.Light.depthOf
#print axioms ProofFile.Honest.K12.Light.askOf
#print axioms ProofFile.Honest.K12.Light.jobAtU
#print axioms ProofFile.Honest.K12.Light.jobAtOmega
