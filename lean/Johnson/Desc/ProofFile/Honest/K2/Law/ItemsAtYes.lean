-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ItemsAtYes.lean: the kind "the code switch" (K2): AT A YES OF
THE KIND's OWN DECISION (`AtYes`, Johnson/Top/H0/K2Hears/Whole.lean) THE TABLE OF JOINTS' TWO ITEMS
"row m carried" AND "row m position" HOLD OF GIVEN WORDS, WHERE THE ROWS THAT THE SWITCH MADE SAY
TRUE OF WORDS THAT ARE ONE WITH THE GIVEN ONES AT THE CARRYING MESSAGE AND THE COPIES, OFF THE NEW
PADS' PLACES. Three statements with their proofs: calls; no definition. No prover, no coin, no
thread.

  `keptPos_list` `KeptPos` (Johnson/Top/H0/K2Hands/AtYes.lean), which runs over the numbers below
                    the size, in the form over the list's members in which `SwitchRowsHold` asks it
  `items_at_yes` nw: any words. The made rows say true of nw at S3, the statement behind the joins ·
                    each made row has no coefficient off g and the copies (`OnNew`), nor at a new
                    pad's place (`Spares`) · nw and the given words are one at g and at each copy,
                    AT EVERY PART AND INDEX THAT IS NO PLACE OF THAT MESSAGE's PAD ⊢ the two items
                    at the state behind
  `items_at_yes_of_values` the same at nw := `newWords`
                    (Johnson/Desc/K2/Honest/Inner/Statement.lean), the first three premises paid:
                    UNDER EIGHT PUBLIC PREMISES OF `SwitchRowsHold` AT S3, AND ITS FOUR ON VALUES
                    (`HonestMain` · `ClaimTrue` · the kept members' stored sample rows say true of
                    `oldWords` · `SymbolsAre`)

How. `yes_items_of_rows` (Honest/K2/Law/ItemsOfRows.lean) wants each made row to say its claim of
the given words at the state behind. What a row says reads of a statement the codes and the
messages' shapes alone (the library's `says_of_shapes`, Johnson/Desc/Means/Forth/AllMet.lean), and
`AtYes.tables` has these the same at S3 and behind; `says_offPads`
(Johnson/Desc/K2/Honest/Inner/SaysOffPads.lean) passes from nw to the given words. In the third:
`switchRowsHold` (Inner/Holds.lean), `rowsOnNew` (Inner/RowsOnNew.lean) and `padsUnread`
(Inner/PadsProof.lean), each at `AtYes.made`.

OF `SwitchRowsHold`'s TEN PUBLIC PREMISES: the tenth (the rows are made) is `AtYes.made`; the one on
the kept targets' main rows comes from hk by `keptPos_list`; EIGHT ARE ASKED AT S3: check · restMain
· fits · seated · lengths · hlogC · hlogZ · hx. THE FIRST OF THE EIGHT IS NOT FAR TO SEEK:
`AtYes.check` is the very test, with the front's x.st where S3 stands here, and `AtYes.sent`,
`AtYes.same` relate x.st to S3; no law that carries the test across is called in this file.

Limits. ALL ON VALUES IS PREMISES: Wl (what the fold left) and V (the new messages in full) are
letters; shown of no run. The eight public premises at S3, KeptPos, that the group had no open row
in front, and the three equations on the table's numbers are premises. "A pad's place": as
`padPlaces` (OnBytes/Iop/Cs.lean) lists it. hA SPEAKS AT `getD a noId` OF THE COPIES' NUMBERS, the
form in which `Spares` speaks: were there fewer numbers than entries of x.T.kept, that would be the
message `noId`; that there are enough lies in `AtYes.sent`: not drawn out here. At the state behind
the kind's OWN decision: the library's `AtYes.behind` (Johnson/Top/H0/Tw/K2C/TieThreeRows.lean)
carries `AtYes` across a step that keeps the tables and the group's rows. Targets whose rest lies in
main rows. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ItemsOfRows
import Johnson.Desc.K2.Honest.Inner.SaysOffPads
import Johnson.Desc.Means.Forth.AllMet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes OnBytes.Means
open OnBytes.Slice (GE rdE coefAt)
open Johnson.Prover.Send (Rows)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (S Numbers rowSays)
open VerifiableInference.Desc.First.K2 (P2 AtYes KeptPos frameAt keptSamples targetRows)
open VerifiableInference.Desc.K2.Honest (OnNew Spares says_offPads copies_covered rowsOnNew
  padsUnread switchRowsHold Left OldFits SeatedAt sizesAt HonestMain ClaimTrue oldWords SymbolsAre
  newWords)

/-- `KeptPos`, over the list's members. -/
theorem keptPos_list {T : SwitchTarget} (hk : KeptPos T) :
    ∀ k ∈ T.kept.toList, 0 < k.shape.mainRows := by
  intro k hm
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
  have hi' : i < T.kept.size := by simpa using hi
  simpa using hk i hi'

variable {P W : Type}

/-- **At any words of which the made rows say true.** -/
theorem items_at_yes (N : Numbers) (words : P × S → Strs → W → Words GE) (m : Nat) (z : P)
    (yy : Strs) (w : W) {p : P2} {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {c : Code}
    (A : AtYes p s s' r₁ r₂ gs x y S3 Y rows G c) (hk : KeptPos x.T) (hf : G.rows = #[])
    (hg : N.groupAt m = x.f.group)
    (hc : ∀ W₀, frameAt x = some W₀ → N.rowsAt m .carried = (0, 1 + keptSamples x W₀))
    (hp : ∀ W₀, frameAt x = some W₀ → N.rowsAt m .position =
      (1 + keptSamples x W₀, r₂.drawn.poss.length * (1 + targetRows x.T + 2)))
    (nw : Words GE)
    (hOn : ∀ r ∈ rows, OnNew (y.ids.getD 0 noId) (y.ids.extract 1 (1 + x.T.kept.size)) (coefAt r))
    (hSp : ∀ r ∈ rows,
      Spares S3 x.T (y.ids.getD 0 noId) (y.ids.extract 1 (1 + x.T.kept.size)) (coefAt r))
    (hSay : ∀ r ∈ rows, Says rdE S3 r nw)
    (hG : ∀ part i, (∀ q ∈ padPlaces S3.codes x.T.shape, q.part = part → q.index ≠ i) →
      nw (y.ids.getD 0 noId) part i = words (z, s') yy w (y.ids.getD 0 noId) part i)
    (hA : ∀ (a : Nat) (k : KeptTarget), x.T.kept[a]? = some k → ∀ part i,
      (∀ q ∈ padPlaces S3.codes k.shape, q.part = part → q.index ≠ i) →
      nw ((y.ids.extract 1 (1 + x.T.kept.size)).getD a noId) part i =
        words (z, s') yy w ((y.ids.extract 1 (1 + x.T.kept.size)).getD a noId) part i) :
    rowSays N words m .carried (z, s') yy w ∧ rowSays N words m .position (z, s') yy w :=
  yes_items_of_rows N words m z yy w A hk hf hg hc hp fun r hr =>
    (says_offPads s'.st S3 x.T r _ _ nw _ (hOn r hr) (hSp r hr)
      (copies_covered x.T _ (by simp only [Array.size_extract]; omega)) hG hA).1
      ((says_of_shapes rdE A.tables.codes A.tables.shape r nw).2 (hSay r hr))

/-- **At the honest new messages**: Wl: what the fold left. V: the new messages in full, in the
order of sending. Wl, V, the given words and w are free letters, tied to no run, coin or input. The
four premises on values are shown at no letters. -/
theorem items_at_yes_of_values (N : Numbers) (words : P × S → Strs → W → Words GE) (m : Nat)
    (z : P) (yy : Strs) (w : W) {p : P2} {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {c : Code}
    (A : AtYes p s s' r₁ r₂ gs x y S3 Y rows G c) (hk : KeptPos x.T) (hf : G.rows = #[])
    (hg : N.groupAt m = x.f.group)
    (hc : ∀ W₀, frameAt x = some W₀ → N.rowsAt m .carried = (0, 1 + keptSamples x W₀))
    (hp : ∀ W₀, frameAt x = some W₀ → N.rowsAt m .position =
      (1 + keptSamples x W₀, r₂.drawn.poss.length * (1 + targetRows x.T + 2)))
    (check : switchTargetCheck S3 x.f.rows x.T = true) (restMain : x.T.rest.part = .main)
    (fits : OldFits S3 x.f.rows)
    (seated : SeatedAt S3 x.f.rows x.T (y.ids.getD 0 noId)
      (y.ids.extract 1 (1 + x.T.kept.size)))
    (lengths : S3.codes.lengthsOk = true)
    (hlogC : (S3.codes.base.getD x.f.rows.code default).logN ≤ 32)
    (hlogZ : (S3.codes.mask.getD x.f.rows.maskCode default).logN ≤ 32)
    (hx : ∀ v ∈ (Positions.ofDraws p.logN r₂.drawn.poss).all.toList,
      v < 2 ^ (S3.codes.base.getD x.f.rows.code default).logN)
    (Wl : Left) (V : Nat → Rows)
    (hM : HonestMain (sizesAt S3 x.f.rows x.T) Wl V)
    (hC : ClaimTrue (sizesAt S3 x.f.rows x.T) x.f.rows Wl)
    (hS : ∀ o ∈ (switchKept x.f.rows).toList, ∀ r ∈ (S3.oracles.getD o default).sampleRows.toList,
      Says rdE S3 r (oldWords (sizesAt S3 x.f.rows x.T) x.f.rows Wl))
    (hY : SymbolsAre (sizesAt S3 x.f.rows x.T) x.f.rows Wl
      (Positions.ofDraws p.logN r₂.drawn.poss) Y)
    (hG : ∀ part i, (∀ q ∈ padPlaces S3.codes x.T.shape, q.part = part → q.index ≠ i) →
      newWords (sizesAt S3 x.f.rows x.T) (y.ids.getD 0 noId)
        (y.ids.extract 1 (1 + x.T.kept.size)) V (y.ids.getD 0 noId) part i =
      words (z, s') yy w (y.ids.getD 0 noId) part i)
    (hA : ∀ (a : Nat) (k : KeptTarget), x.T.kept[a]? = some k → ∀ part i,
      (∀ q ∈ padPlaces S3.codes k.shape, q.part = part → q.index ≠ i) →
      newWords (sizesAt S3 x.f.rows x.T) (y.ids.getD 0 noId)
        (y.ids.extract 1 (1 + x.T.kept.size)) V
        ((y.ids.extract 1 (1 + x.T.kept.size)).getD a noId) part i =
      words (z, s') yy w ((y.ids.extract 1 (1 + x.T.kept.size)).getD a noId) part i) :
    rowSays N words m .carried (z, s') yy w ∧ rowSays N words m .position (z, s') yy w :=
  items_at_yes N words m z yy w A hk hf hg hc hp _
    (rowsOnNew S3 x.f.rows x.T _ _ _ Y rows check restMain fits (keptPos_list hk) seated lengths
      hlogC hlogZ hx A.made)
    (padsUnread S3 x.f.rows x.T _ _ _ Y rows check restMain fits (keptPos_list hk) seated lengths
      hlogC hlogZ hx A.made)
    (switchRowsHold S3 x.f.rows x.T _ _ _ Y rows Wl V check restMain fits (keptPos_list hk) seated
      lengths hlogC hlogZ hx A.made hM hC hS hY)
    hG hA

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.keptPos_list
#print axioms ProofFile.Honest.K2.Law.items_at_yes
#print axioms ProofFile.Honest.K2.Law.items_at_yes_of_values
