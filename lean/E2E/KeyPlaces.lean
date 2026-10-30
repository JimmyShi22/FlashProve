-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyPlaces.lean: names for the places of the sub-protocols of the key file's description; each
sub-protocol's place and number of rounds at the full size, written out as three lists of literals
(below: the written lists); and the round of its chain at which each begins. The theorems show that
the written lists are the description's own at all public files in scope, wherever the description
can be made and passes two of its tests. The description (`Key.descriptionFromSource`, Johnson/Desc/Key/Desc.lean;
its type is `FileDescription`, Johnson/Desc/Block.lean) is the key file's IOP as written in Lean. It has
three chains: the first, the shared and the last (the fields `first`, `shared`, `second`). Each
chain gives a list of sub-protocols (`Block`; the list is `Chain.blocksInOrder`). A place (`Place`; all three
in the same file) is a sub-protocol's label: chain, link, piece and kind. A row is a place with a
number of rounds; `rowsOf` (Johnson/RunOne/Sound/KeyListsAtFK.lean) gives the rows of a list of
sub-protocols. The full size is that of the sizes `keyFull`
(Johnson/Goal/PlanValues/KeySizedReturns.lean). Public files are in scope where `VerifierAndGoals.InScope`
(Ladder.lean) accepts them.

The file is for whoever writes a prover's part for a sub-protocol of the key file. Such a file has
to say at which place the part is and which challenge, by number, it reads. With this file a place
is called by name and a number is computed from the description's own lists (`startIn`), so that
neither is written as a number where it is used. Everything here is public data. Definitions,
theorems and tests. The lines that begin with `#guard` are the tests: Lean's evaluator runs them
when the file is compiled, and the kernel does not check them.

  `places_of_made`: at public files in scope: every description F that the library's maker returns
    at what its reading routine returns, and whose tests `planOk` and `wantedOk` pass, has the rows
    `fullFirst`, `fullShared` and `fullSecond`: the places and numbers of rounds of its three lists,
    in order. No parameter of the description is left free. `places_named` (E2E/KeyPlacesNamed.lean)
    applies it to `keyFileDescription X N P` under `KeyNamed Z X N P` (E2E/KeyProtocolOverDescription.lean): the description
    whose pull-back along `keyInstanceOfOutOfDomainSample` has the key file's decision at Z as its `run`
  `places_in_scope`: the same for `Key.descriptionFromSource X N P`, at every N and P, where X is what `Key.sourceOf`
    returns at what the maker's first step returns
  `first_written`, `shared_written`, `second_written`: the library's own tables of places and
    numbers of rounds (`Key.wantedFirst`, Johnson/Desc/Key/WantedFirst.lean; `Key.wantedShared`,
    `Key.wantedSecond`, Johnson/Desc/Key/WantedLater.lean) at the sizes of `keyFull` are the three
    written lists, places and numbers: the first table at every argument whose fields `ranges` and
    `lin` are `keyFull.ranges.x` and `keyFull.once.shape`, the two others at `keyFull.once.shape`
  `first_written_no`: a negative test: with the kind in the first label changed from K1 to K2 the
    first of these equations is false
  `roundsInFront_rows`: for every list of sub-protocols and every place: `roundsInFront`
    (Johnson/Desc/ProofFile/Honest/ForKinds.lean), the number of a chain's rounds before a place, is
    `startIn` of the list's rows
  `order_rows`: for every description: the order of places `orderOf` of the frame
    (Johnson/Desc/ProofFile/Honest/Frame.lean: the types in which an honest prover is written for a
    description) is the places of the three lists' rows, chain after chain
  `starts_first`, `starts_shared`, `starts_second`: `startIn` at the three written lists, as numbers
    from 0, at every place whose row has a round
  `fullFirst`, `fullShared`, `fullSecond`: definitions: the written lists: for each sub-protocol of
    the three chains, in order, its row at the full size: 19, 12 and 4 rows
  `linkRows i n`: a definition: the six rows of the link of lookup i. Only the third, at
    `lookPlace i`, has rounds: n. The five other places have no name
  `startIn rows p`: a definition: the number of rounds of the rows before the first row at the place
    p; `none` if no row is at p
  `idxPlace`, `msgPlace`, `lookPlace i`, `rowsPlace`, `rngPlace`, `battPlace`, `wPlace`,
    `sealPlace`: definitions: the named places of the first chain
  `frontPlace`, `pointPlace`, `foldedPlace`, `gammaPlace`, `locPlace`, `omegaPlace`, `joinsPlace`,
    `zetaPlace`, `splitPlace`, `foldedTestPlace`, `omegaTestPlace`, `sharedSealPlace`: definitions:
    the places of the shared chain
  `tableSecondPlace`, `sourcesPlace`, `ownTestPlace`, `endPlace`: definitions: the places of the
    last chain

By what. The three equations on the tables and `first_written_no` are proved by evaluation in Lean's
kernel (`decide +kernel`); `first_written` and `first_written_no` first unfold the table and rewrite
by their two hypotheses. `places_in_scope` joins the three with `desc_lists`
(Johnson/RunOne/Sound/KeyListsAtFK.lean: under `planOk` and `wantedOk` each chain's rows are its
table) and with `five_in_scope` and `shared_lin_in_scope` (Johnson/RunOne/Law/KeyInScope.lean: in
scope the sizes that the tables read are those of `keyFull`). `places_of_made` unfolds
`Key.descriptionFromPlan` (Johnson/Desc/Key/Desc.lean) and calls `places_in_scope` with `readOf_publicOfO`
(Johnson/RunOne/Law/KeyInScope.lean). `roundsInFront_rows` is by induction on the list, `order_rows`
by `simp` after unfolding, the three theorems on the starts by `decide`.

Hypotheses of `places_of_made`. hZ: the three public files Zp are in scope. h0: the reading routine,
`publicOfO` (Johnson/Desc/Ok/PlanWritten/PublicAt.lean) at the hash function `OnBytes.secondHashFunction`,
returns X₀ at Zp. hm: the maker's first step, `Key.madeAt` (Johnson/Desc/Key/Road.lean), returns m
at X₀, the layout file and cfg; cfg is in the place of the public files' digest and is arbitrary.
hF: its second step, `Key.descriptionFromPlan`, returns F at m. hp, hw: F passes `planOk` and `wantedOk`
(Johnson/Desc/Block.lean). `places_in_scope` has hP, `ReadOf Zp.pol X₀`
(Johnson/RunOne/Law/KeyInScope.lean), in place of h0, and hX, that `Key.sourceOf` returns X at m, in
place of hF.

Limits.
- A place is a label that the maker of a sub-protocol stamps on it. No table says which sub-protocol
  has a label (the library's own limit: Johnson/Desc/Block.lean, at `wantedOk`). So the theorems
  state labels and numbers of rounds, in order; what is done at a place they do not state. What the
  places' docstrings say of it is read off the files that define the chains
  (Johnson/Desc/Key/Chain1.lean, Chains23.lean and what they call).
- The numbers of rounds at the full size, as lists of numbers without the labels, are in the library
  twice: `L₁`, `L₂`, `L₃` (Johnson/RunOne/Sound/KeyListsInScope.lean) and `roundsW₁`, `roundsW₂`,
  `roundsW₃` (Johnson/Top/Fire/Code/KeyRoundsAtSeat.lean). This file adds the labels with them, and
  the starts.
- `fullFirst` has the first chain's sealing round among its 18,851 rounds. The rounds' data that
  `FileDescription.data` (Johnson/Desc/BlockSlot.lean) makes of a description have that chain without its
  last round (`WholeD.of`, OnBytes/Maker/WholeOf.lean).
- That the reading routine and the maker return and that `planOk` and `wantedOk` pass is proved of
  no files here. `kseat_name` (Johnson/Goal/Description/KeySeat.lean) gives all four, at the
  constant `Key.fixedDigest` for cfg, where the IOP's own test on the public files accepts
  (`protocolDataWellFormed`, Johnson/Goal/Description/Live.lean). That it accepts is a theorem of the side library
  at the written files `storedPublicFiles` and `zGap` (`AtFullSide.Top.theLive_zFull`, `theLive_zGap`), which
  this file does not call. `protocolDataWellFormed` is no hypothesis here.
- The full size only. No prover is defined.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import Johnson.RunOne.Sound.KeyListsAtFK
import Johnson.RunOne.Law.KeyInScope
import Johnson.Desc.ProofFile.Honest.ForKinds

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyBook
open VerifiableInference.Desc (Place Block FileDescription)
open VerifiableInference.Desc.Key
open Johnson.RunOne.Sound (rowsOf desc_lists)
open Johnson.RunOne.Law.KeyInScope (five_in_scope shared_lin_in_scope)
open Lk6.AtPlan (keyFull)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest (roundsInFront)

/-! ## 1 The places

Each docstring names the sub-protocol that the library's files put at the label; no theorem states
it (see the Limits). A sending is a sub-protocol of the kind K1: oracle messages are sent and
sampled, in two rounds. -/

/-- The sending of the index-mask message. -/
def idxPlace : Place := ⟨1, none, 1, .K1⟩
/-- The sending of the message with the multiplicities. -/
def msgPlace : Place := ⟨1, none, 2, .K1⟩
/-- The argument of lookup number i, from 0. -/
def lookPlace (i : Nat) : Place := ⟨1, some i, 2, .K3⟩
/-- All lookups' rows are put onto the ranges' group; no round. -/
def rowsPlace : Place := ⟨1, none, 4, .frame⟩
/-- The proximity test on the ranges' group. -/
def rngPlace : Place := ⟨1, none, 5, .K12⟩
/-- The batching of the rows on the table. -/
def battPlace : Place := ⟨1, none, 13, .K13⟩
/-- The sending of W. -/
def wPlace : Place := ⟨1, none, 14, .K1⟩
/-- The first chain's end: the sealing round. -/
def sealPlace : Place := ⟨1, none, 15, .frame⟩
/-- The shared chain's front; no round. -/
def frontPlace : Place := ⟨2, none, 0, .frame⟩
/-- The shared point is drawn ("LIN point"). -/
def pointPlace : Place := ⟨2, none, 1, .K14⟩
/-- The sending of the folded row. -/
def foldedPlace : Place := ⟨2, none, 2, .K1⟩
/-- The sub-protocol named "(rec_gamma)" (Johnson/Desc/K14/Blocks.lean); no round. -/
def gammaPlace : Place := ⟨2, none, 3, .K14⟩
/-- The stored table is read at drawn positions ("LOC"). -/
def locPlace : Place := ⟨2, none, 4, .K14⟩
/-- The sending of Omega and of the split's mask message. -/
def omegaPlace : Place := ⟨2, none, 5, .K1⟩
/-- The sub-protocol named "joins": the messages join their groups; no round. -/
def joinsPlace : Place := ⟨2, none, 6, .K14⟩
/-- The second point is drawn ("LIN zeta"). -/
def zetaPlace : Place := ⟨2, none, 7, .K14⟩
/-- The split ("SPLIT"). -/
def splitPlace : Place := ⟨2, none, 8, .K14⟩
/-- The proximity test on the folded row's group. -/
def foldedTestPlace : Place := ⟨2, none, 9, .K12⟩
/-- The proximity test on Omega's group. -/
def omegaTestPlace : Place := ⟨2, none, 10, .K12⟩
/-- The shared chain's end: its sealing round. -/
def sharedSealPlace : Place := ⟨2, none, 11, .frame⟩
/-- The second part of the test on the table; no round. -/
def tableSecondPlace : Place := ⟨3, none, 0, .K14⟩
/-- The sources of the trees that are taken over from the earlier chains; no round. -/
def sourcesPlace : Place := ⟨3, none, 1, .frame⟩
/-- The proximity test on the own group. -/
def ownTestPlace : Place := ⟨3, none, 2, .K12⟩
/-- The last chain's end; no round. -/
def endPlace : Place := ⟨3, none, 3, .frame⟩

/-- The six rows of the link of lookup i: only the third, at `lookPlace i`, has rounds: n. -/
def linkRows (i n : Nat) : List (Place × Nat) :=
  [(⟨1, some i, 0, .frame⟩, 0), (⟨1, some i, 1, .frame⟩, 0), (lookPlace i, n),
    (⟨1, some i, 3, .frame⟩, 0), (⟨1, some i, 4, .frame⟩, 0), (⟨1, some i, 5, .frame⟩, 0)]

/-- The rows of the first chain's 19 sub-protocols, at the full size. -/
def fullFirst : List (Place × Nat) :=
  [(idxPlace, 2), (msgPlace, 2)] ++ linkRows 0 9581 ++ linkRows 1 9220 ++
    [(rowsPlace, 0), (rngPlace, 23), (battPlace, 20), (wPlace, 2), (sealPlace, 1)]

/-- The rows of the shared chain's 12. -/
def fullShared : List (Place × Nat) :=
  [(frontPlace, 0), (pointPlace, 1), (foldedPlace, 2), (gammaPlace, 0), (locPlace, 1),
    (omegaPlace, 2), (joinsPlace, 0), (zetaPlace, 1), (splitPlace, 1), (foldedTestPlace, 35),
    (omegaTestPlace, 24), (sharedSealPlace, 1)]

/-- The rows of the last chain's 4. -/
def fullSecond : List (Place × Nat) :=
  [(tableSecondPlace, 0), (sourcesPlace, 0), (ownTestPlace, 30), (endPlace, 0)]

/-- The number of rounds of the rows before the first row at a place; `none` if no row is at it. -/
def startIn : List (Place × Nat) → Place → Option Nat
  | [], _ => none
  | r :: l, a => if r.1 == a then some 0 else (startIn l a).map (· + r.2)

/-! ## 2 The library's tables at the sizes of `keyFull` -/

theorem first_written (one : OnBytes.Params.OneTime) (hr : one.ranges = keyFull.ranges.x)
    (hl : one.lin = keyFull.once.shape) : wantedFirst one = fullFirst := by
  unfold wantedFirst
  rw [hr, hl]
  decide +kernel

theorem shared_written : wantedShared keyFull.once.shape = fullShared := by decide +kernel

theorem second_written : wantedSecond keyFull.once.shape = fullSecond := by decide +kernel

/-- A negative test: with the kind in the first label changed from K1 to K2 the equation of
`first_written` is false. -/
theorem first_written_no (one : OnBytes.Params.OneTime) (hr : one.ranges = keyFull.ranges.x)
    (hl : one.lin = keyFull.once.shape) :
    wantedFirst one ≠ (⟨1, none, 1, .K2⟩, 2) :: fullFirst.tail := by
  unfold wantedFirst
  rw [hr, hl]
  decide +kernel

/-! ## 3 The description's own lists -/

/-- **In scope the three lists of `Key.descriptionFromSource X N P` have the written places and numbers of rounds**,
where X₀ meets `ReadOf`, the maker's first step and `Key.sourceOf` return, and `planOk` and
`wantedOk` pass. N, P and cfg are arbitrary. -/
theorem places_in_scope {Zp : PublicFiles} (hZ : InScope Zp = true) {X₀ : OnBytes.Model.Verify.Public}
    (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol X₀) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
    (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (hp : (descriptionFromSource X N P).planOk = true) (hw : (descriptionFromSource X N P).wantedOk = true) :
    rowsOf (descriptionFromSource X N P).first.blocksInOrder = fullFirst ∧ rowsOf (descriptionFromSource X N P).shared.blocksInOrder = fullShared ∧
      rowsOf (descriptionFromSource X N P).second.blocksInOrder = fullSecond := by
  obtain ⟨h₁, h₂, h₃⟩ := desc_lists X N P hp hw
  obtain ⟨-, hr, hl, -, -⟩ := five_in_scope hZ hP hm hX hp
  have hs := shared_lin_in_scope hZ hP hm hX hp
  refine ⟨h₁.trans (first_written _ hr hl), ?_, ?_⟩
  · rw [h₂, hs]
    exact shared_written
  · rw [h₃, hs]
    exact second_written

/-- **In scope every description that the maker returns at what the reading routine returns has the
written places and numbers of rounds**, if its tests `planOk` and `wantedOk` pass. -/
theorem places_of_made {Zp : PublicFiles} (hZ : InScope Zp = true) {X₀ : OnBytes.Model.Verify.Public}
    (h0 : VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction Zp.pol Zp.KL (some Zp.lay) =
      .ok X₀) {cfg : ByteArray} {m : Johnson.G.OfPlan.Made} (hm : madeAt X₀ Zp.lay cfg = .ok m)
    {F : FileDescription Xi} (hF : descriptionFromPlan m = .ok F) (hp : F.planOk = true)
    (hw : F.wantedOk = true) :
    rowsOf F.first.blocksInOrder = fullFirst ∧ rowsOf F.shared.blocksInOrder = fullShared ∧
      rowsOf F.second.blocksInOrder = fullSecond := by
  unfold descriptionFromPlan at hF
  split at hF
  · rename_i X N P hX _ _
    obtain rfl := Except.ok.inj hF
    exact places_in_scope hZ (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO h0) hm hX hp hw
  all_goals cases hF

/-! ## 4 The starts -/

/-- `roundsInFront` of a list of sub-protocols, at a place, is `startIn` of the list's rows. -/
theorem roundsInFront_rows {S Cl : Type} (bs : List (Block S Cl)) (a : Place) :
    roundsInFront bs a = startIn (rowsOf bs) a := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    show (if b.place == a then some 0 else (roundsInFront bs a).map (· + b.rounds.length)) =
      (if b.place == a then some 0 else (startIn (rowsOf bs) a).map (· + b.rounds.length))
    rw [ih]

/-- The frame's order of places, `orderOf`, is the places of the rows, chain after chain. -/
theorem order_rows {Xi : Type} (F : FileDescription Xi) :
    ProofFile.Honest.orderOf F =
      (rowsOf F.first.blocksInOrder ++ rowsOf F.shared.blocksInOrder ++ rowsOf F.second.blocksInOrder).map (·.1) := by
  simp [ProofFile.Honest.orderOf, rowsOf, List.map_map, Function.comp_def]

/-- The round of the first chain, from 0, at which each of its sub-protocols with a round begins. -/
theorem starts_first :
    [idxPlace, msgPlace, lookPlace 0, lookPlace 1, rngPlace, battPlace, wPlace, sealPlace].map
      (startIn fullFirst) =
    [some 0, some 2, some 4, some 9585, some 18805, some 18828, some 18848, some 18850] := by
  decide

/-- The same for the shared chain. -/
theorem starts_shared :
    [pointPlace, foldedPlace, locPlace, omegaPlace, zetaPlace, splitPlace, foldedTestPlace,
      omegaTestPlace, sharedSealPlace].map (startIn fullShared) =
    [some 0, some 1, some 3, some 4, some 6, some 7, some 8, some 43, some 67] := by
  decide

/-- The same for the last chain. -/
theorem starts_second : startIn fullSecond ownTestPlace = some 0 := by decide

-- 35 rows; 18,851 + 68 + 30 rounds; no label occurs twice; a place that is in no row has no start
#guard fullFirst.length == 19 && fullShared.length == 12 && fullSecond.length == 4
#guard (fullFirst.map (·.2)).sum == 18851 && (fullShared.map (·.2)).sum == 68 &&
  (fullSecond.map (·.2)).sum == 30
#guard ((fullFirst ++ fullShared ++ fullSecond).map (·.1)).eraseDups.length == 35
#guard startIn fullFirst ownTestPlace == none

end AtPublicFiles.KeyBook

#print axioms AtPublicFiles.KeyBook.first_written
#print axioms AtPublicFiles.KeyBook.shared_written
#print axioms AtPublicFiles.KeyBook.second_written
#print axioms AtPublicFiles.KeyBook.first_written_no
#print axioms AtPublicFiles.KeyBook.places_in_scope
#print axioms AtPublicFiles.KeyBook.places_of_made
#print axioms AtPublicFiles.KeyBook.roundsInFront_rows
#print axioms AtPublicFiles.KeyBook.order_rows
#print axioms AtPublicFiles.KeyBook.starts_first
#print axioms AtPublicFiles.KeyBook.starts_shared
#print axioms AtPublicFiles.KeyBook.starts_second
#print axioms AtPublicFiles.KeyBook.idxPlace
#print axioms AtPublicFiles.KeyBook.msgPlace
#print axioms AtPublicFiles.KeyBook.lookPlace
#print axioms AtPublicFiles.KeyBook.rowsPlace
#print axioms AtPublicFiles.KeyBook.rngPlace
#print axioms AtPublicFiles.KeyBook.battPlace
#print axioms AtPublicFiles.KeyBook.wPlace
#print axioms AtPublicFiles.KeyBook.sealPlace
#print axioms AtPublicFiles.KeyBook.frontPlace
#print axioms AtPublicFiles.KeyBook.pointPlace
#print axioms AtPublicFiles.KeyBook.foldedPlace
#print axioms AtPublicFiles.KeyBook.gammaPlace
#print axioms AtPublicFiles.KeyBook.locPlace
#print axioms AtPublicFiles.KeyBook.omegaPlace
#print axioms AtPublicFiles.KeyBook.joinsPlace
#print axioms AtPublicFiles.KeyBook.zetaPlace
#print axioms AtPublicFiles.KeyBook.splitPlace
#print axioms AtPublicFiles.KeyBook.foldedTestPlace
#print axioms AtPublicFiles.KeyBook.omegaTestPlace
#print axioms AtPublicFiles.KeyBook.sharedSealPlace
#print axioms AtPublicFiles.KeyBook.tableSecondPlace
#print axioms AtPublicFiles.KeyBook.sourcesPlace
#print axioms AtPublicFiles.KeyBook.ownTestPlace
#print axioms AtPublicFiles.KeyBook.endPlace
#print axioms AtPublicFiles.KeyBook.linkRows
#print axioms AtPublicFiles.KeyBook.fullFirst
#print axioms AtPublicFiles.KeyBook.fullShared
#print axioms AtPublicFiles.KeyBook.fullSecond
#print axioms AtPublicFiles.KeyBook.startIn
