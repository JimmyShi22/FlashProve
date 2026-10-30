-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ItemsInTables.lean: the kind "the code switch" (K2): THE TWO
LAWS OF Honest/K2/Law/ItemsAtYes.lean WITH LESS ASKED: the given words need be one with the others
at the carrying message and the copies only INSIDE THESE MESSAGES' TABLES at the state behind, off
the new pads' places. Two statements with their proofs: calls; no definition. No prover, no coin, no
thread.

  `items_in_tables` `items_at_yes`, hG and hA asked at an index below `tableSize s'.st` of the
                    message and part alone
  `items_in_tables_of_values` `items_at_yes_of_values`, likewise

WHY, AND HOW: Johnson/Desc/K2/Honest/Inner/SaysInTables.lean: `says_inTables` stands where
`says_offPads` stood; all else is ItemsAtYes.lean's text. The two elder laws follow from these; they
have been handed in and stay as they are.

Limits. Those of ItemsAtYes.lean, all. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ItemsAtYes
import Johnson.Desc.K2.Honest.Inner.SaysInTables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes OnBytes.Means
open OnBytes.Slice (GE rdE coefAt)
open Johnson.Prover.Send (Rows)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (S Numbers rowSays)
open VerifiableInference.Desc.First.K2 (P2 AtYes KeptPos frameAt keptSamples targetRows)
open VerifiableInference.Desc.K2.Honest (OnNew Spares says_inTables copies_covered rowsOnNew
  padsUnread switchRowsHold Left OldFits SeatedAt sizesAt HonestMain ClaimTrue oldWords SymbolsAre
  newWords)

variable {P W : Type}

/-- **At any words of which the made rows say true.** -/
theorem items_in_tables (N : Numbers) (words : P × S → Strs → W → Words GE) (m : Nat) (z : P)
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
    (hG : ∀ part i, i < tableSize s'.st (y.ids.getD 0 noId) part →
      (∀ q ∈ padPlaces S3.codes x.T.shape, q.part = part → q.index ≠ i) →
      nw (y.ids.getD 0 noId) part i = words (z, s') yy w (y.ids.getD 0 noId) part i)
    (hA : ∀ (a : Nat) (k : KeptTarget), x.T.kept[a]? = some k → ∀ part i,
      i < tableSize s'.st ((y.ids.extract 1 (1 + x.T.kept.size)).getD a noId) part →
      (∀ q ∈ padPlaces S3.codes k.shape, q.part = part → q.index ≠ i) →
      nw ((y.ids.extract 1 (1 + x.T.kept.size)).getD a noId) part i =
        words (z, s') yy w ((y.ids.extract 1 (1 + x.T.kept.size)).getD a noId) part i) :
    rowSays N words m .carried (z, s') yy w ∧ rowSays N words m .position (z, s') yy w :=
  yes_items_of_rows N words m z yy w A hk hf hg hc hp fun r hr =>
    (says_inTables s'.st S3 x.T r _ _ nw _ (hOn r hr) (hSp r hr)
      (copies_covered x.T _ (by simp only [Array.size_extract]; omega)) hG hA).1
      ((says_of_shapes rdE A.tables.codes A.tables.shape r nw).2 (hSay r hr))

/-- **At the honest new messages**: Wl: what the fold left. V: the new messages in full, in the
order of sending. Wl, V, the given words and w are free letters, tied to no run, coin or input. The
four premises on values are shown at no letters. -/
theorem items_in_tables_of_values (N : Numbers) (words : P × S → Strs → W → Words GE) (m : Nat)
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
    (hG : ∀ part i, i < tableSize s'.st (y.ids.getD 0 noId) part →
      (∀ q ∈ padPlaces S3.codes x.T.shape, q.part = part → q.index ≠ i) →
      newWords (sizesAt S3 x.f.rows x.T) (y.ids.getD 0 noId)
        (y.ids.extract 1 (1 + x.T.kept.size)) V (y.ids.getD 0 noId) part i =
      words (z, s') yy w (y.ids.getD 0 noId) part i)
    (hA : ∀ (a : Nat) (k : KeptTarget), x.T.kept[a]? = some k → ∀ part i,
      i < tableSize s'.st ((y.ids.extract 1 (1 + x.T.kept.size)).getD a noId) part →
      (∀ q ∈ padPlaces S3.codes k.shape, q.part = part → q.index ≠ i) →
      newWords (sizesAt S3 x.f.rows x.T) (y.ids.getD 0 noId)
        (y.ids.extract 1 (1 + x.T.kept.size)) V
        ((y.ids.extract 1 (1 + x.T.kept.size)).getD a noId) part i =
      words (z, s') yy w ((y.ids.extract 1 (1 + x.T.kept.size)).getD a noId) part i) :
    rowSays N words m .carried (z, s') yy w ∧ rowSays N words m .position (z, s') yy w :=
  items_in_tables N words m z yy w A hk hf hg hc hp _
    (rowsOnNew S3 x.f.rows x.T _ _ _ Y rows check restMain fits (keptPos_list hk) seated lengths
      hlogC hlogZ hx A.made)
    (padsUnread S3 x.f.rows x.T _ _ _ Y rows check restMain fits (keptPos_list hk) seated lengths
      hlogC hlogZ hx A.made)
    (switchRowsHold S3 x.f.rows x.T _ _ _ Y rows Wl V check restMain fits (keptPos_list hk) seated
      lengths hlogC hlogZ hx A.made hM hC hS hY)
    hG hA

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.items_in_tables
#print axioms ProofFile.Honest.K2.Law.items_in_tables_of_values
