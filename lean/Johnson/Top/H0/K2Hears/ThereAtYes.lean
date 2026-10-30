-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/ThereAtYes.lean: the code switch: AT A YES OF THE KIND's DECISION THE
FRONT READS SOMETHING OFF THE ORACLES AT EVERY POSITION, WHATEVER THE ORACLES: the premise h0 of
SlotIs.lean's slot_is and of all that stands on it.
  symbolsAt_sz   what Johnson/Desc/Own/Symbols.lean's symbolsAt holds at a listed position has the
                 sizes of LongCols.lean's colOne, at any reading of the oracles and any position;
                 and colOne is there
  there_of_atYes  THE STATEMENT: at AtYes with at least one listed position: (longFront p s x orc
                 q).isSome = true AT EVERY orc AND EVERY q
WHY NO PREMISE ON THE COLUMNS. LongOne.lean's heard_is_front says WHAT is read and so asks that the
opened columns are the oracles' (ColsOf). Being there hangs on look-ups and sizes alone
(LongThere.lean's rowsAt_there): a yes has laid the opened columns at position number 0, and these
have the shapes' sizes.
LIMITS. Nothing on what is read. From a seated sub-protocol's acceptance to AtYes, and that the
kind's test gives a listed position, is not here. No soundness is claimed.
-/
import Johnson.Top.H0.K2Hears.LongThere

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model Desc.Plain
open VerifiableInference.Desc.Own (rowsAt symbols_at symbolsAt Opened OR SzC rowsAt_there)
open _root_.Tw.K2 (switchNotices)

theorem symbolsAt_sz {S : Statement} {B : TreeBook} {pos : Positions} {cols : List Opened}
    {o : Nat} {p : Nat × Nat} {out : Array Column} (h : symbolsAt S B pos cols o p = some out)
    (i : Nat) (hi : i < pos.all.size) (ft logN : Nat) (orc : Nat → Nat → List UInt64) (q : Nat) :
    OR SzC (colOne S B ft logN orc o p q) out[i]? := by
  unfold symbolsAt at h
  split at h
  · rename_i tree x mine h1 h2 h3
    dsimp only at h
    obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨k1, k2⟩ := OnBytes.Slice.list_mapM_inv _ _ _ hl
    have hil : i < l.length := by
      rw [k1]
      simpa using hi
    have k3 := k2 i (by simpa using hi)
    rw [List.getElem_range, List.getElem?_eq_getElem hil] at k3
    obtain ⟨here, -, k4⟩ := Option.bind_eq_some_iff.1 k3
    obtain ⟨c, -, k5⟩ := Option.map_eq_some_iff.1 k4
    rw [List.getElem?_toArray, List.getElem?_eq_getElem hil, ← k5]
    unfold colOne
    rw [h1, h2]
    exact ⟨by simp [Blk.columnOf], by simp [Blk.columnOf]⟩
  · cases h

/-- **At a yes the front reads something at every position, whatever the oracles.** -/
theorem there_of_atYes {p : P2} {s s' : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {S3 : Statement} {Y : Array E}
    {rows : List OnBytes.Row} {G : Group} {c : Code}
    (A : AtYes p s s' r₁ r₂ gs x y S3 Y rows G c)
    (hpos : 0 < (Positions.ofDraws p.logN r₂.drawn.poss).all.size)
    (orc : Nat → Nat → List UInt64) (q : Nat) : (longFront p s x orc q).isSome = true := by
  obtain ⟨B, left, hr⟩ := A.read
  obtain ⟨places, cols, opened, R⟩ := readOld_inv hr
  have hm : x.f.rows.masks = 2 := (Johnson.Top.H.check_facts A.check).1
  obtain ⟨seg, hseg, -⟩ := symbols_at x.f.rows hm opened _ Y R.hLayout 0 hpos
  unfold longFront
  rw [sent_book A.sentBy]
  have hp : (singleRowsOracles x.f.rows).mapM (fun o => y.book.place[o]?) = some places := R.hPlaces
  simp only [Option.bind_some, hp]
  rw [rowsAt_there x.f.rows _ opened 0 0 fun w => ?_, hseg]
  · rfl
  obtain ⟨z1, z2⟩ := OnBytes.Slice.array_mapM_inv _ _ _ R.hSymbols
  unfold openedOne
  by_cases hw : w < ((singleRowsOracles x.f.rows).zip places).size
  · have h1 := z2 w hw
    have hw' : w < opened.size := by rw [z1]; exact hw
    rw [Array.getElem?_eq_getElem hw'] at h1
    have h2 : OR SzC (colOne y.st y.book (par9 p).firstTree p.logN orc
        ((singleRowsOracles x.f.rows).zip places)[w].1
        ((singleRowsOracles x.f.rows).zip places)[w].2 q) opened[w][0]? :=
      symbolsAt_sz h1 0 hpos (par9 p).firstTree p.logN orc q
    rw [colOne_congr (sent_shapes A.sent)] at h2
    rw [Array.getElem?_eq_getElem hw', Array.getElem?_map, Array.getElem?_eq_getElem hw]
    simp only [Option.map_some, Option.bind_some]
    cases hc : colOne (skelOf x) y.book (par9 p).firstTree p.logN orc
      ((singleRowsOracles x.f.rows).zip places)[w].1 ((singleRowsOracles x.f.rows).zip places)[w].2
      q with
    | none =>
      rw [hc] at h2
      exact h2
    | some c0 =>
      rw [hc] at h2
      exact h2
  · have ha : opened[w]? = none :=
      Array.getElem?_eq_none (by rw [z1]; exact Nat.le_of_not_lt hw)
    rw [ha, Array.getElem?_eq_none (by rw [Array.size_map]; exact Nat.le_of_not_lt hw)]
    trivial

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.there_of_atYes
