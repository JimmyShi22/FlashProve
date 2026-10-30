-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyBookThirdNamed.lean: the third of the eleven tests that the frame
(Johnson/Desc/ProofFile/Honest/Frame.lean) has on a book of coins passes at the key file's book
(`keyBook K`, E2E/KeyBook.lean) and the key file's description at the public files: `third_named`.
E2E/KeyBookPassesNamed.lean shows that no test fails there if the third passes (`book_named`). So
all eleven pass: `book_passes`. Both theorems are at the full size only; they are general in the
public files Z in scope and in the X, N, P with `KeyNamed Z X N P`. The third test is derived by the
theorems of E2E/KeyBookThird.lean from a test on numbers, which is evaluated here in Lean's kernel
(`decide +kernel`). Definitions, theorems and two negative tests.

Terms. A description (`FileDescription`, Johnson/Desc/Block.lean) is the IOP of a file as written in Lean.
It has three chains, the first, the shared and the second, each a list of sub-protocols (`Block`),
each at a place (`Place`: a label of chain, link, piece and kind). `keyFileDescription X N P`
(E2E/KeyProtocolOverDescription.lean) is a key file's description. A chain's rows (`rowsOf`,
Johnson/RunOne/Sound/KeyListsAtFK.lean) are, for each sub-protocol, its place and its number of
rounds. A sub-protocol declares its rounds and the oracle messages that they send (`Oracle`,
Johnson/Desc/Oracle.lean). A symbol of an oracle message has so many words (`words`), some of them
mask words (`SymbolComponent.mask`). A book (`ProverCoinCounts`, the frame) is public data that goes with a description.
It has a table for each chain, entries and cuts. A row of a table is the address of a part of the
prover (`Addr`: a place, and the part's number there) with that part's count of coins (`Due`: f of
the base field, e of the extension field). The third test has the name "a place states more mask
words than its parts have coins" and is `masksOk` (the frame) at each of the three chains;
`thirdAt F B` (E2E/KeyBookPassesNamed.lean) is that conjunction. It says of every sub-protocol: the
mask words of its oracle messages, added up, are at most f + 3 e of the table's rows at its place,
added up. The rounds' data (`WholeD`, OnBytes/Maker/Whole.lean) are what `F.data file` returns: for
each chain a list of rounds (`ds₁`, `ds₂`, `ds₃`), each with the number of roots that it sends
(`entry.roots`) and the shapes of the trees whose roots it sends (`trees`). A tree's width is the
field `W` of its shape. The head of E2E/KeyBookThird.lean has these terms at more length.

  `book_passes`: under the three hypotheses below: `(keyBook K).word (keyFileDescription X N P) = none`.
    `ProverCoinCounts.word` (the frame) is the name of the first of the eleven tests that fails; `none`: every
    test passes
  `third_named`: under the same hypotheses: `thirdAt (keyFileDescription X N P) (keyBook K) = true`
  `data_named`: under scope and h: `(keyFileDescription X N P).data "key file"` returns `dKeyFull`
    (Johnson/Flat/Dec/FitAtWritten.lean): the rounds' data built from the library's literal lists of
    the key file's rounds at the full size (`dryKeyFull`, Johnson/G/DryKeyLit.lean), in a form that
    Lean's kernel can evaluate
  `senders₁`, `senders₂`, `senders₃`: definitions: a literal list for each chain; an element is the
    number of a round, from 0, and the widths of that round's trees
  `walk₁`, `walk₂`, `walk₃`: `sendersAre` (E2E/KeyBookThird.lean) passes at each chain's rounds in
    `dKeyFull`, numbered from 0, and the chain's list: the rounds whose `entry.roots` is not 0 or
    which have a tree are, in order, those of the list, with these widths. By evaluation in Lean's
    kernel
  `walk_no`: a negative test: with 13 in place of 12 as the width of the last tree of `senders₃`,
    `sendersAre` fails
  `full_third`: `thirdFull (keyBook K)` passes at the K that `fullPub` returns. By evaluation in
    Lean's kernel. It is stated by `atFull` (E2E/KeyBookAtWritten.lean): `atFull f` is f at that K,
    and false if `fullPub` is `none`
  `full_third_no`: a negative test: `thirdFull` fails at the book without the first row of its first
    table, the row of the part that sends the index-mask message (`⟨idxPlace, 0⟩`)
  `thirdFull B`: a definition: `thirdThin` (E2E/KeyBookThird.lean: the test on numbers, on a short
    list) at each of the three chains: at the numbers of rounds in the chain's list, at `widthOf` of
    that list, at the table of B for the chain, and at the chain's rows at the full size as literal
    lists (`fullFirst`, `fullShared`, `fullSecond`, E2E/KeyPlaces.lean). At every row it says: no
    round of the row is in the list, or `widthOf` of the list is at most f + 3 e at the row's place
  `widthOf T`: a definition: all widths in the list T, added up
  `plan_blocks`: at every description F: if `F.planOk` passes, `blocksOk` (Johnson/Desc/Block.lean)
    passes at each of the three chains. By unfolding

By what. Theorems that are cited without a file are of E2E/KeyBookThird.lean or of this file.
`data_named`: the fields of `KeyNamed` give the hypotheses of `laidFixed_of`
(Johnson/Desc/Key/SlotIs.lean), by which the library's `Key.keyDataAndDecisionAtFixedDigest` (Johnson/Desc/Key/Slot.lean)
returns the key file's rounds' data at Z. By `laid_data_written`
(Johnson/Goal/Numbers/KeySeatLaidAt.lean), in scope these are `writtenKFull`, and by
`writtenKFull_eq` (Johnson/Flat/Dec/FitAtWritten.lean) that is `dKeyFull`. `third_named` calls
`masksOk_of` at each chain, with W := `widthOf` of the chain's list. Its hypothesis hb comes from
`plan_blocks` at the field `plan` of `KeyNamed`. For hW, the words of all oracle messages of the
chain add up to `widthOf` of the chain's list: by `told_sum`, `sent_length`, `widths_chains`,
`senders_spec` at `walk₁`, `walk₂` or `walk₃`, and `counts_of_data`
(Johnson/Desc/Sound/TakenBelowOfData.lean) or, at the second chain, `roundsOfData`
(Johnson/Desc/Sound/DataRounds.lean) with `entries_of`. For hc, `places_named`
(E2E/KeyPlacesNamed.lean) rewrites the chain's rows to the literal list, and `roots_first` and
`roots_later` rewrite the declared numbers of roots to those in `dKeyFull`; then `check_of_thin` at
`full_third` (through `of_atFull`, E2E/KeyBookPassesNamed.lean) and at `senders_spec`, at the first
chain with `with_zero`. `roots_first` needs that the first chain declares a round: the numbers of
rounds in `fullFirst` do not add up to 0 (`decide`). `book_passes` is `book_named`
(E2E/KeyBookPassesNamed.lean) at `third_named`.

Hypotheses of `third_named` and `book_passes`. scope: `InScope Z = true` (Ladder.lean): the three
public files Z are in the scope of the library's goals; among other things the layout file is that
of the stored full-size example. h: `KeyNamed Z X N P` (E2E/KeyProtocolOverDescription.lean): X, N, P are what
the key file's description at Z is made of: the library's `Key.descAt` (Johnson/Desc/Key/Road.lean)
returns `keyFileDescription X N P` at the files of Z, the description's own three tests accept, and its rounds'
data are the key file's at Z. hK: `fullPub = some K` (E2E/KeyBookAtWritten.lean): K (`KeyPub`: the
public data from which the book is computed) is the one at the library's sizes of the full size;
`full_made` (E2E/KeyBookPassesNamed.lean) shows that there is such a K.

Limits.
- The bound is crude: every place that sends a root is compared with the widths of all trees of its
  chain together, and not with its own mask words. Nothing is shown on how many mask words a place
  declares.
- The book is `keyBook K` with its carried entries (`KeyPub.carried`). An entry (`Ahead`, the frame)
  is a named block of the coins of one part, the owner, that one part, the spender, is given; it is
  spent or carried. The carried entries are a proposal: see the head of E2E/KeyBook.lean, whose
  limits on them and on the book's counts apply. `thirdAt` reads the three tables only;
  `book_passes` is of the book with these entries.
- That the tests pass says that the book is consistent with itself and with the description. It does
  not say that any part of a prover fits the book.
- The full size only: `dKeyFull`, `senders₁`, `senders₂`, `senders₃`, `fullFirst`, `fullShared`,
  `fullSecond` and `fullPub` are values at the full size, and `InScope` fixes the layout file.
  Nothing is shown at another size.
- K is computed from the library's value `keyFull` (hK). That `KeyPub.of` returns the same K at the
  sizes from which the description at Z is made is not stated here. `pub_of_made`
  (E2E/KeyBookSourced.lean) states it, under hypotheses of its own.
- `KeyNamed` is a hypothesis: no X, N, P that meet it are shown here. `key_named`
  (E2E/KeyProtocolOverDescription.lean) shows some where the IOP's own test on the public files accepts.
- Each negative test is one example. `full_third_no` is stated by `atFull`, which is false also
  where `fullPub` is `none`; `full_third` and `full_made` show that it is not `none`.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.KeyBookThird
import E2E.KeyBookPassesNamed
import Johnson.Goal.Numbers.KeySeatLaidAt
import Johnson.Desc.Key.SlotIs
import Johnson.Flat.Dec.FitAtWritten

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyBook
open VerifiableInference.Desc
open VerifiableInference.Desc.Key (Source LaterPlaces descAt descriptionFromPlan laidFixed_of)
open VerifiableInference.Desc.Sound (baseOf)
open Johnson.RunOne.Sound (rowsOf)
open Johnson.G (writtenKFull dKeyFull writtenKFull_eq)
open VerifierAndGoals (PublicFiles InScope)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData)
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription)
open ProofFile.Honest (ProverCoinCounts masksOk)

variable {Z : PublicFiles} {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

/-! ## 1 The rounds' data -/

/-- In scope the rounds' data of the key file's description are `dKeyFull`: the data built from the
library's literal lists of the key file's rounds at the full size. -/
theorem data_named (scope : InScope Z = true) (h : KeyNamed Z X N P) :
    (keyFileDescription X N P).data "key file" = .ok dKeyFull := by
  obtain ⟨X₀, m, h0, hm, hd, ha⟩ := h.named
  have hF : descriptionFromPlan m = .ok (keyFileDescription X N P) := by
    unfold descAt at hd
    rw [hm] at hd
    exact hd
  have hl := laidFixed_of X₀ Z.lay m (keyFileDescription X N P) (dataAtFiles flashProveData Z).DK hm hF h.plan h.wanted
    h.owed h.data ha
  have hb : ((VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL
      (some Z.lay)).bind fun Y => VerifiableInference.Desc.Key.keyDataAndDecisionAtFixedDigest Y Z.lay) =
      .ok ((dataAtFiles flashProveData Z).DK,
        ((keyFileDescription X N P).pull VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample).run) := by
    rw [h0]
    exact hl
  rw [← writtenKFull_eq, ← VerifiableInference.PlanWritten.laid_data_written scope hb]
  exact h.data

/-! ## 2 The rounds that send a root, as literal lists -/

/-- The first chain's list: a round's number, from 0, and the widths of its trees (`walk₁`). -/
def senders₁ : List (Nat × List Nat) :=
  [(0, [3]), (2, [77]), (18811, [96]), (18818, [72]), (18824, [12]), (18848, [12])]

/-- The shared chain's list (`walk₂`). -/
def senders₂ : List (Nat × List Nat) :=
  [(1, [324]), (4, [36, 3]), (17, [120]), (25, [72]), (32, [72]), (39, [12]), (44, [3]), (49, [96]),
    (56, [96]), (63, [12])]

/-- The second chain's list (`walk₃`). -/
def senders₃ : List (Nat × List Nat) := [(7, [96]), (14, [72]), (20, [72]), (26, [12])]

set_option maxRecDepth 1000000 in
theorem walk₁ : sendersAre 0 dKeyFull.ds₁ senders₁ = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem walk₂ : sendersAre 0 dKeyFull.ds₂ senders₂ = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem walk₃ : sendersAre 0 dKeyFull.ds₃ senders₃ = true := by decide +kernel

/-- A negative test: with 13 in place of 12 as the width of the last tree, `sendersAre` fails. -/
theorem walk_no : sendersAre 0 dKeyFull.ds₃ [(7, [96]), (14, [72]), (20, [72]), (26, [13])] =
    false := by decide +kernel

/-- All widths in the list T, added up. -/
def widthOf (T : List (Nat × List Nat)) : Nat := (T.flatMap (·.2)).sum

/-- The test on numbers `thirdThin` at the three chains: at each chain's list above, the table of B
for the chain and the chain's rows at the full size. -/
def thirdFull (B : ProverCoinCounts) : Bool :=
  thirdThin (senders₁.map (·.1)) (widthOf senders₁) B.first 0 fullFirst &&
    thirdThin (senders₂.map (·.1)) (widthOf senders₂) B.shared 0 fullShared &&
    thirdThin (senders₃.map (·.1)) (widthOf senders₃) B.second 0 fullSecond

theorem full_third : atFull (fun K => thirdFull (keyBook K)) = true := by decide +kernel

/-- A negative test: `thirdFull` fails at the book without the first row of its first table, the row
of the part that sends the index-mask message. -/
theorem full_third_no : atFull (fun K =>
    thirdFull { keyBook K with first := (keyBook K).first.drop 1 }) = false := by decide +kernel

/-! ## 3 At the key file's description -/

theorem plan_blocks {Xi : Type} {F : FileDescription Xi} (h : F.planOk = true) :
    blocksOk F.first.blocksInOrder = true ∧ blocksOk F.shared.blocksInOrder = true ∧
      blocksOk F.second.blocksInOrder = true := by
  unfold FileDescription.planOk FileDescription.planOkCore at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, b1⟩, b2⟩, b3⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact ⟨b1, b2, b3⟩

/-- **The frame's third test passes at the key file's description and the book `keyBook K`.** In
scope, at every X, N, P with `KeyNamed Z X N P`, where K is what `fullPub` returns. -/
theorem third_named (scope : InScope Z = true) (h : KeyNamed Z X N P) (K : KeyPub)
    (hK : fullPub = some K) : thirdAt (keyFileDescription X N P) (keyBook K) = true := by
  have hD := data_named scope h
  obtain ⟨b1, b2, b3⟩ := plan_blocks h.plan
  obtain ⟨r1, r2, r3⟩ := places_named scope h
  obtain ⟨s1, v1⟩ := senders_spec 0 _ _ walk₁
  obtain ⟨s2, v2⟩ := senders_spec 0 _ _ walk₂
  obtain ⟨s3, v3⟩ := senders_spec 0 _ _ walk₃
  obtain ⟨c1, c2, c3⟩ := widths_chains dKeyFull
  obtain ⟨a₁, a₂, a₃⟩ := roundsOfData (keyFileDescription X N P) "key file" dKeyFull hD
  have hne : (keyFileDescription X N P).roundsDeclaredByBlocks.1 ≠ [] := by
    intro e
    have hl : ((rowsOf (keyFileDescription X N P).first.blocksInOrder).map (·.2)).sum = 0 := by
      have : ((keyFileDescription X N P).first.blocksInOrder.flatMap (·.rounds)).length = 0 := by
        show (keyFileDescription X N P).roundsDeclaredByBlocks.1.length = 0
        rw [e]
        rfl
      rw [List.length_flatMap] at this
      unfold rowsOf
      rw [List.map_map]
      exact this
    rw [r1] at hl
    exact absurd hl (by decide)
  have e1 : ((keyFileDescription X N P).first.blocksInOrder.flatMap (·.rounds)).map (·.entry.roots) =
      dKeyFull.ds₁.map (·.entry.roots) ++ [0] := roots_first hD hne
  have e2 : ((keyFileDescription X N P).shared.blocksInOrder.flatMap (·.rounds)).map (·.entry.roots) =
      dKeyFull.ds₂.map (·.entry.roots) := (roots_later hD).1
  have e3 : ((keyFileDescription X N P).second.blocksInOrder.flatMap (·.rounds)).map (·.entry.roots) =
      dKeyFull.ds₃.map (·.entry.roots) := (roots_later hD).2
  have hc := of_atFull full_third hK
  unfold thirdFull at hc
  simp only [Bool.and_eq_true] at hc
  have w1 : ((sentOf (keyFileDescription X N P).first.blocksInOrder).map (·.2)).sum ≤ widthOf senders₁ := by
    have := told_sum hD h.plan 0
    have hl : (Sound.sentAt (keyFileDescription X N P) 0).length = dKeyFull.t₁ := by
      show (sentOf (keyFileDescription X N P).first.blocksInOrder).length = _
      rw [sent_length b1]
      exact (counts_of_data hD).1.symm
    rw [hl, c1, v1] at this
    exact Nat.le_of_eq this
  have w2 : ((sentOf (keyFileDescription X N P).shared.blocksInOrder).map (·.2)).sum ≤ widthOf senders₂ := by
    have := told_sum hD h.plan 1
    have hl : (Sound.sentAt (keyFileDescription X N P) 1).length = dKeyFull.t₂ := by
      show (sentOf (keyFileDescription X N P).shared.blocksInOrder).length = _
      rw [sent_length b2]
      exact (counts_of_data hD).2.symm
    rw [hl, c2, v2] at this
    exact Nat.le_of_eq this
  have w3 : ((sentOf (keyFileDescription X N P).second.blocksInOrder).map (·.2)).sum ≤ widthOf senders₃ := by
    have := told_sum hD h.plan 2
    have hl : (Sound.sentAt (keyFileDescription X N P) 2).length =
        (dKeyFull.ds₃.map (·.trees.length)).sum := by
      show (sentOf (keyFileDescription X N P).second.blocksInOrder).length = _
      rw [sent_length b3]
      exact congrArg List.sum (entries_of a₃).2
    rw [hl, c3, v3] at this
    exact Nat.le_of_eq this
  unfold thirdAt
  rw [masksOk_of b1 _ _ w1 (by
      rw [r1, e1]
      exact check_of_thin _ _ _ _ 0 _ hc.1.1 (with_zero s1)),
    masksOk_of b2 _ _ w2 (by
      rw [r2, e2]
      exact check_of_thin _ _ _ _ 0 _ hc.1.2 s2),
    masksOk_of b3 _ _ w3 (by
      rw [r3, e3]
      exact check_of_thin _ _ _ _ 0 _ hc.2 s3)]
  rfl

/-- **The book `keyBook K` passes all eleven of the frame's tests at the key file's description.**
Under the hypotheses of `third_named`. `none`: no test fails. -/
theorem book_passes (scope : InScope Z = true) (h : KeyNamed Z X N P) (K : KeyPub)
    (hK : fullPub = some K) : (keyBook K).word (keyFileDescription X N P) = none :=
  book_named scope h K hK (third_named scope h K hK)

end AtPublicFiles.KeyBook

#print axioms AtPublicFiles.KeyBook.data_named
#print axioms AtPublicFiles.KeyBook.walk₁
#print axioms AtPublicFiles.KeyBook.walk₂
#print axioms AtPublicFiles.KeyBook.walk₃
#print axioms AtPublicFiles.KeyBook.walk_no
#print axioms AtPublicFiles.KeyBook.full_third
#print axioms AtPublicFiles.KeyBook.full_third_no
#print axioms AtPublicFiles.KeyBook.third_named
#print axioms AtPublicFiles.KeyBook.book_passes
#print axioms AtPublicFiles.KeyBook.senders₁
#print axioms AtPublicFiles.KeyBook.senders₂
#print axioms AtPublicFiles.KeyBook.senders₃
#print axioms AtPublicFiles.KeyBook.widthOf
#print axioms AtPublicFiles.KeyBook.thirdFull
#print axioms AtPublicFiles.KeyBook.plan_blocks
