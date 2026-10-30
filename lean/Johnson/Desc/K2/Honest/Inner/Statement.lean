-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Inner/Statement.lean: WHAT IS OWED OF THE HONEST SIDE OF THE CODE SWITCH
BETWEEN TWO SEGMENTS (Johnson/Desc/K2/Honest/Carrying.lean) AGAINST THE ROWS THAT THE KIND's OWN
TEXT LAYS (`swRows`, Johnson/Desc/Own/SwitchRows.lean): STATEMENTS ALONE: three, each a definition
of a proposition. NOTHING IS PROVED IN THIS FILE, and none of the three is one of the library's
goals: they are lemmas' statements. No coin, no round, no frame and no decision stands in them.

  `RestIsParts`     the rest, as Carrying.lean's one list has it, has the length and the offsets of
                    the program's `switchParts`: part by part, entry by entry
  `NewPadsUnread`   at the places of the NEW pads (the carrying message's; each copy's) every row
                    that the switch lays has, read in the field, the coefficient 0
  `SwitchRowsHold`  if the claim in front is true of what the fold left, the kept
                    members' stored sample rows are true of them, and the symbols read are these
                    rows' code words' symbols, then EVERY ROW THAT THE SWITCH LAYS says true of the
                    honest new messages
(That the carrying message's laying is the inverse of the program's `cutIndex` and
`SwitchPlaces.get` is a theorem: Johnson/Desc/K2/Honest/Inner/LaidBackProof.lean.)

The terms in which they are stated:
  `sizesAt`         THE SWITCH's SIZES ARE MADE of the statement, the single rows and the target:
                    the kept members' shapes are read off the statement
  `OldFits`         what is public of the claim in front: its form on the main row has the main
                    code's variables; its two written vectors are no longer than a mask row's
                    message; it counts the kept members' rows; it reads kept members alone; and
                    of the kept members' stored sample rows: none has a stretch or a form (the
                    sending's maker lays tensors and single entries alone)
  `SeatedAt`        the statement holds the carrying message and the copies under their numbers, at
                    the target's shapes
  `Held.entryIn`    an entry of a kept member's table; 0 at a row beyond its real rows
  `ClaimTrue`       the claim on the single rows (`SingleRows`, OnBytes/Iop/Fold.lean), said of a
                    `Left`: its form on the folded main row, its forms on the kept members' tables,
                    its two written vectors on the mask rows, add up to its target
  `oldWords`        words in which the kept members' old messages stand under their old numbers
  `rowOfComplex`, `SymbolsAre`   the row number j of the complex (main; the kept rows by member and
                    row; the old mask row; the fresh one) as a message and a tail under its code;
                    "y holds, position by position and row by row, these rows' symbols"
  `newWords`        words in which the carrying message and the copies stand under their new numbers
  `HonestMain`      outside the pads the new messages' main rows are `mainRows` at what the fold
                    left

TEN OF THE FOURTEEN PREMISES ARE PUBLIC; the other four speak of values (`HonestMain`, `ClaimTrue`,
the stored sample rows' truth, `SymbolsAre`). Of the ten the kind itself asks: the program's test on
a target (`switchTargetCheck`, OnBytes/Iop/Cs.lean; the kind's `targetOk` is that test:
`targetOk_eq`, Johnson/Top/H0/Tw/K2/TargetAgree.lean; the kind asks it of the statement in front of
the sending); "the maker returns"; every position below the code's length; and, of its plan, a
length of at most 2 ^ 32 where the positions are drawn (`plan_32`,
Johnson/Top/H0/K2Hands/AtYes.lean). THAT A YES OF THE DECISION GIVES THE OTHERS IS NOT SHOWN HERE:
the rest lies in main rows; the mask code's length at most 2 ^ 32; each copy has a main row (the
library's `KeptPos`, the same file, written out); `OldFits`; `SeatedAt`; `lengthsOk`.
`OldFits` holds the public clauses of the library's `ClaimOK`
(Johnson/Top/H0/K2Hands/ClaimJoin.lean), two counts, and the premise under which a stored sample
row's form reads as the row's own coefficients (`formOn_reads`,
Johnson/Top/H0/K2Hands/FormOnReads.lean: with a stretch of step 0 the two part).

Where the words come from. `SwitchRowsHold` takes the new messages in full (V) as a letter and asks
of them what the honest prover's text gives (`HonestMain`). Of what stands at a pad, in a tail or in
a mask row `HonestMain` asks nothing. That no row of the switch has a coefficient at a new pad's
place is `NewPadsUnread`: stated here, not proved. `SwitchRowsHold` stands at EVERY V that meets
`HonestMain`: so, under its premises, what stands there does not turn whether a row says true.

Where the premises can be met. One set of values at which all premises of `SwitchRowsHold` hold
together is typed as a theorem: Inner/Member.lean [not in this library; so here read: not proved in
this library].

WHICH OF THE THREE ARE SHOWN, ELSEWHERE: `RestIsParts` (Inner/RestIsPartsProof.lean) and
`SwitchRowsHold` (Inner/Holds.lean). `NewPadsUnread`: not.

By which road. They stand at every statement, with no yes of a decision
and no place in them: so by the closed forms of the rows' coefficients
(OnBytes/Slice/BlkCsKept.lean, BlkCsStretch.lean, BlkCsRows.lean;
Johnson/Top/H0/H2K/GenRowsAt.lean), with `RestIsParts` and
LaidBackProof.lean's two theorems; not by the law at a yes (`text_of_after`,
Johnson/Top/H0/K2Hands/AfterText.lean), whose premises want a typed caller at a place.

Limits. `NewPadsUnread` IS NOT "THE ROWS ARE ADMITTED": the ground's test on a new row (`rowL`,
Johnson/Desc/First/Base/Ground.lean) asks that the coefficient's three WORDS are 0, at the pad that
the statement has STORED for each member, and seven things more; none of that is stated here.
`SwitchRowsHold` stands at targets whose rest lies in main rows: those between two segments.
Nothing on the new messages' sample rows: these are the sending's. Nothing on whether the kind's
decision returns. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Carrying
import Johnson.Desc.Own.SwitchRows
import Johnson.Desc.Means.Says
import OnBytes.Slice.BlkRead
import Johnson.Prover.Send.Core

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE readE formAt coefAt rdE codeOf)
open OnBytes.Means (Words Says)
open Johnson.Prover.Send (Rows)
open Johnson.Prover.Link (symG)

/-! ## 1 The terms -/

/-- **The switch's sizes**, made of the statement, the single rows and the target. -/
def sizesAt (S : Statement) (old : SingleRows) (T : SwitchTarget) : Sizes :=
  ⟨S.codes, old.code, old.maskCode,
    (switchKept old).toList.map fun o => (S.oracles.getD o default).shape, T⟩

/-- What is public of the claim in front. -/
structure OldFits (S : Statement) (old : SingleRows) : Prop where
  mainVars : ∀ v ∈ old.c.tensors, v.vars = (S.codes.base.getD old.code default).logEll
  d0 : (old.d.getD 0 #[]).size ≤ (S.codes.mask.getD old.maskCode default).ell
  d1 : (old.d.getD 1 #[]).size ≤ (S.codes.mask.getD old.maskCode default).ell
  rows : old.keptRows =
    ((switchKept old).toList.map fun o => (S.oracles.getD o default).shape.mainRows).sum
  named : ∀ f ∈ old.kept.toList, f.oracle ∈ (switchKept old).toList
  once : (switchKept old).toList.Nodup
  keptCode : ∀ o ∈ (switchKept old).toList, (S.oracles.getD o default).shape.code = old.code
  stored : ∀ o ∈ (switchKept old).toList, ∀ r ∈ (S.oracles.getD o default).sampleRows.toList,
    r.runs.size = 0 ∧ r.forms.size = 0

/-- The statement holds the carrying message and the copies under their numbers, at the target's
shapes; the numbers are apart from each other and from the kept members' old ones. -/
structure SeatedAt (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat)
    (anew : Array Nat) : Prop where
  carrying : (S.oracles[g]?).map (fun x : OnBytes.Oracle => x.shape) = some T.shape
  copies : ∀ (a : Nat) (k : KeptTarget), T.kept[a]? = some k →
    ((anew[a]?).bind fun o => (S.oracles[o]?).map fun x : OnBytes.Oracle => x.shape) = some k.shape
  olds : ∀ o ∈ (switchKept old).toList, o < S.oracles.size
  apart : (g :: anew.toList ++ (switchKept old).toList).Nodup

/-- An entry of a kept member's table; 0 at a row beyond its real rows. -/
def Held.entryIn (H : Held) (s : OracleShape) (index : Nat) : GE :=
  if index % 2 ^ ceilLog2 s.mainRows < s.mainRows then H.entry s index else 0

/-- The claim on the single rows, said of what a fold left: each of its forms on a kept member is
read on that member's table. A claim with a form on a message that is no kept member is not true. -/
def ClaimTrue (Z : Sizes) (old : SingleRows) (W : Left) : Prop :=
  (∀ f ∈ old.kept.toList, f.oracle ∈ (switchKept old).toList) ∧
  (∑ j ∈ Finset.range (Z.codes.base.getD Z.code default).ell, formAt old.c j * W.main j) +
    (old.kept.toList.map fun f =>
      match (switchKept old).toList.idxOf? f.oracle with
      | some a =>
        ∑ i ∈ Finset.range
            (2 ^ (ceilLog2 (Z.kept.getD a {}).mainRows +
              (Z.codes.base.getD Z.code default).logEll)),
          formAt f.c i * (W.kept a).entryIn (Z.kept.getD a {}) i
      | none => 0).sum +
    (∑ r ∈ Finset.range 2, ∑ i ∈ Finset.range (Z.codes.mask.getD Z.maskCode default).ell,
      readE ((old.d.getD r #[]).getD i zeroE) * W.mask r i) =
  readE old.target

/-- Words in which the kept members' old messages stand under their old numbers; 0 elsewhere. -/
def oldWords (Z : Sizes) (old : SingleRows) (W : Left) : Words GE := fun o part i =>
  match part, (switchKept old).toList.idxOf? o with
  | .main, some a => (W.kept a).entryIn (Z.kept.getD a {}) i
  | _, _ => 0

/-- The row number j of the complex of single rows, as a code, a message and a tail: 0 the folded
main row; then the kept rows, by member and row; then the old mask row and the fresh one. Beyond
these: whatever `Left.mask` yields at a number from 2 on: not meant to be read. -/
def rowOfComplex (Z : Sizes) (W : Left) (j : Nat) : Fmt.M1.Code × (Nat → GE) × (Nat → GE) :=
  let C := codeOf (Z.codes.base.getD Z.code default)
  let Zc := codeOf (Z.codes.mask.getD Z.maskCode default)
  let keptRows := Z.kept.zipIdx.flatMap fun s => (List.range s.1.mainRows).map fun b => (s.2, b)
  if j == 0 then (C, W.main, W.mainTail)
  else match keptRows[j - 1]? with
    | some x => (C, (W.kept x.1).main x.2, (W.kept x.1).tail x.2)
    | none => (Zc, W.mask (j - 1 - keptRows.length), W.maskTail (j - 1 - keptRows.length))

/-- y holds, position by position (each listed position once) and row by row, the symbols of the
complex's rows; a mask row's at the position modulo its code's length. -/
def SymbolsAre (Z : Sizes) (old : SingleRows) (W : Left) (pos : Positions) (y : Array E) : Prop :=
  ∀ i j, i < pos.all.size → j < old.rows →
    readE (y.getD (i * old.rows + j) zeroE) =
      symG (rowOfComplex Z W j).1
        (if j < old.rows - old.masks then pos.all.getD i 0
          else pos.all.getD i 0 % 2 ^ (rowOfComplex Z W j).1.a)
        (rowOfComplex Z W j).2.1 (rowOfComplex Z W j).2.2

/-- Words in which the carrying message stands under the number g and the copy of the kept member
number a under anew[a]; 0 elsewhere. V: the new messages in full, in the order of sending. -/
def newWords (Z : Sizes) (g : Nat) (anew : Array Nat) (V : Nat → Rows) : Words GE := fun o part i =>
  if o = g then (V 0).word Z.target.shape part i
  else match anew.toList.idxOf? o with
    | some a => (V (1 + a)).word (Z.kept.getD a {}) part i
    | none => 0

/-- Outside the pads the main rows of the carrying message and the copies are `mainRows` at W. (Of
`mainRows`' letter for the own messages nothing is read at these numbers.) -/
def HonestMain (Z : Sizes) (W : Left) (V : Nat → Rows) : Prop :=
  ∀ k, k ≤ Z.kept.length →
    let s := if k = 0 then Z.target.shape else Z.kept.getD (k - 1) {}
    ∀ b j, b < s.mainRows → j < (Z.codes.base.getD s.code default).ell →
      (b + j * 2 ^ ceilLog2 s.mainRows) ∉
        ((padPlaces Z.codes s).filter fun p => p.part == .main).map (·.index) →
      (V k).main (s.mainDeg == 3) b j = mainRows Z W (fun _ _ _ => zeroG) k b j

/-! ## 2 The three statements -/

/-- The statement that the rest has the length and the offsets of the program's `switchParts`. Not
proved here; a lemma's statement, none of the library's goals. -/
def RestIsParts : Prop :=
  ∀ (S : Statement) (old : SingleRows) (T : SwitchTarget) (W : Left),
    old.masks = 2 → OldFits S old →
    let Z := sizesAt S old T
    let P := switchParts S old
    let c := S.codes.base.getD old.code default
    let zk := S.codes.mask.getD old.maskCode default
    let v (i : Nat) : GE := (rest Z W).getD i zeroG
    let keptRows := Z.kept.zipIdx.flatMap fun s => (List.range s.1.mainRows).map fun b => (s.2, b)
    (rest Z W).length = P.length ∧
    (∀ r i, r < 2 → i < zk.ell → v (P.maskAt.getD r 0 + i) = W.mask r i) ∧
    (∀ q, q < c.r → v (P.mainTailAt + q) = W.mainTail q) ∧
    (∀ n x q, keptRows[n]? = some x → q < c.r →
      v (P.keptTailAt.getD n 0 + q) = (W.kept x.1).tail x.2 q) ∧
    (∀ r q, r < 2 → q < zk.r → v (P.maskTailAt.getD r 0 + q) = W.maskTail r q) ∧
    ∀ a s t p, Z.kept[a]? = some s → (padPlaces S.codes s)[t]? = some p →
      v (P.oldPadAt.getD a 0 + t) = (W.kept a).entry s p.index

/-- The statement that no row that the switch lays has, read in the field, a coefficient at a new
pad's place. Not proved here; a lemma's statement, none of the library's goals. -/
def NewPadsUnread : Prop :=
  ∀ (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat) (anew : Array Nat)
    (pos : Positions) (y : Array E) (rows : List OnBytes.Row),
    switchTargetCheck S old T = true → OldFits S old → SeatedAt S old T g anew →
    Own.swRows S old T g anew pos y = some rows →
    ∀ r ∈ rows,
      (∀ p ∈ padPlaces S.codes T.shape, coefAt r g p.part p.index = 0) ∧
      ∀ (a : Nat) (k : KeptTarget), T.kept[a]? = some k →
        ∀ p ∈ padPlaces S.codes k.shape, coefAt r (anew.getD a noId) p.part p.index = 0

/-- The statement that every row that the switch lays says true of the honest new messages. S: the
statement behind the sending and the joins. W: what the fold left. V: the new messages in full. Not
proved here; a lemma's statement, none of the library's goals. -/
def SwitchRowsHold : Prop :=
  ∀ (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat) (anew : Array Nat)
    (pos : Positions) (y : Array E) (rows : List OnBytes.Row) (W : Left) (V : Nat → Rows),
    switchTargetCheck S old T = true → T.rest.part = .main → OldFits S old →
    (∀ k ∈ T.kept.toList, 0 < k.shape.mainRows) →
    SeatedAt S old T g anew → S.codes.lengthsOk = true →
    (S.codes.base.getD old.code default).logN ≤ 32 →
    (S.codes.mask.getD old.maskCode default).logN ≤ 32 →
    (∀ x ∈ pos.all.toList, x < 2 ^ (S.codes.base.getD old.code default).logN) →
    Own.swRows S old T g anew pos y = some rows →
    HonestMain (sizesAt S old T) W V →
    ClaimTrue (sizesAt S old T) old W →
    (∀ o ∈ (switchKept old).toList, ∀ r ∈ (S.oracles.getD o default).sampleRows.toList,
      Says rdE S r (oldWords (sizesAt S old T) old W)) →
    SymbolsAre (sizesAt S old T) old W pos y →
    ∀ r ∈ rows, Says rdE S r (newWords (sizesAt S old T) g anew V)

end VerifiableInference.Desc.K2.Honest
