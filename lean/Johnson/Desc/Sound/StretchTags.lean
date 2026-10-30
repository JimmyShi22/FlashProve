-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/StretchTags.lean: the stretch of a file's data at a block bears the entries that
the block declares. Statements with their proofs; no kind is named.

Letters: those of FitsOfOk (Johnson/Desc/Sound/Tiles.lean): the data dataOf a R₁ R₂ R₃ of three
lists of written rounds; WrittenAs e (bs.flatMap (·.rounds)) R₁: the blocks' declared rounds in a
row are written as R₁.
  rounds_at      the declared rounds in a row, cut at block k by the blocks' own counts, are block
                 k's declared rounds.
  room_of_later  where a later block declares a round, block k's rounds end before the row's end.
  written_tags   round by round the written round has the declared round's entry, and its kind is
                 kindOf of the entry's name.
  data_tags      the first chain's data have the written rounds' entries and kinds, but for the
                 last round (the seal).
  stretch_tags   so the stretch at block k has block k's declared entries and their names' kinds,
                 where a round is declared behind it.
What is not claimed. Anything on the second or the third chain's data. That any rounds are written
so. Nothing on soundness.

-/
import Johnson.Desc.Sound.Tiles
import Johnson.Desc.K14.Law.CutAt
import Johnson.Desc.K13.Law.Tries
import OnBytes.Maker.ReadData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law

open OnBytes OnBytes.Maker OnBytes.Flat
open OnBytes.Params (Rounds)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound
open _root_.Desc.K14.Law (roundsIn)

variable {T Cl : Type}

/-- A round's entry, and its kind. -/
abbrev Tag : Type := Fmt.Entry × Option Fmt.Kind

def tagD (r : Fmt.DeclaredRound) : Tag := (r.entry, Fmt.kindOf r.entry.name)
def tagW (x : Fmt.Round × List Fmt.Stored) : Tag := (x.1.entry, some x.1.kind)
def tagR (d : RDT) : Tag := (d.entry, some d.kind)

theorem roundsIn_cons (b : Block T Cl) (l : List (Block T Cl)) :
    roundsIn (b :: l) = b.rounds.length + roundsIn l := by
  simp [roundsIn]

theorem length_flat (bs : List (Block T Cl)) : (bs.flatMap (·.rounds)).length = roundsIn bs := by
  induction bs with
  | nil => rfl
  | cons b l ih => rw [List.flatMap_cons, List.length_append, ih, roundsIn_cons]

/-- **The declared rounds at block k.** -/
theorem rounds_at : ∀ (bs : List (Block T Cl)) (k : ℕ) (x : Block T Cl), bs[k]? = some x →
    ((bs.flatMap (·.rounds)).drop (roundsIn (bs.take k))).take x.rounds.length = x.rounds
  | [], _, _, h => by simp at h
  | b :: l, 0, x, h => by
    obtain rfl : b = x := by simpa using h
    have h0 : roundsIn ((b :: l).take 0) = 0 := rfl
    rw [h0, List.drop_zero, List.flatMap_cons, List.take_left]
  | b :: l, k + 1, x, h => by
    have h' : l[k]? = some x := by simpa using h
    rw [List.take_succ_cons, roundsIn_cons, List.flatMap_cons, ← List.drop_drop,
      List.drop_left]
    exact rounds_at l k x h'

theorem le_roundsIn (l : List (Block T Cl)) (y : Block T Cl) (h : y ∈ l) :
    y.rounds.length ≤ roundsIn l :=
  List.le_sum_of_mem (List.mem_map.2 ⟨y, h, rfl⟩)

/-- What stands behind block k. -/
theorem room_of_later (bs : List (Block T Cl)) : ∀ (k j : ℕ) (x y : Block T Cl), bs[k]? = some x →
    bs[j]? = some y → k < j → 0 < y.rounds.length →
    roundsIn (bs.take k) + x.rounds.length < roundsIn bs := by
  induction bs with
  | nil => intro k j x y h; simp at h
  | cons b l ih =>
    intro k j x y h hj hkj hy
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hj' : l[j]? = some y := by simpa using hj
    cases k with
    | zero =>
      obtain rfl : b = x := by simpa using h
      have hm := le_roundsIn l y (List.mem_of_getElem? hj')
      have h0 : roundsIn ((b :: l).take 0) = 0 := rfl
      rw [roundsIn_cons, h0]
      omega
    | succ k =>
      have := ih k j x y (by simpa using h) hj' (by omega) hy
      rw [List.take_succ_cons, roundsIn_cons, roundsIn_cons]
      omega

/-- **Declared rounds as written rounds: the tags.** -/
theorem written_tags {e : List (List ByteArray × ByteArray)} {l : List Fmt.DeclaredRound} {R : Rounds}
    (h : WrittenAs e l R) : R.map tagW = l.map tagD := by
  induction h with
  | nil => rfl
  | @cons r x l R h1 _ ih =>
    rw [List.map_cons, List.map_cons, ih]
    congr 1
    obtain ⟨hr, _⟩ := h1
    unfold Fmt.DeclaredRound.round at hr
    obtain ⟨k, hk, h2⟩ := Option.bind_eq_some_iff.1 hr
    obtain ⟨os, _, h3⟩ := Option.map_eq_some_iff.1 h2
    unfold tagW tagD
    rw [← h3, hk]

/-- **The first chain's data: the tags.** -/
theorem data_tags (a : ℕ) (R₁ R₂ R₃ : Rounds) :
    (dataOf a R₁ R₂ R₃).ds₁.map tagR = (R₁.map tagW).dropLast := by
  show (((Three.Whole.of R₁ R₂ R₃).ds₁.dropLast).map rdtOf).map tagR = _
  rw [List.map_map, List.map_dropLast]
  exact congrArg List.dropLast (rdsFromL_map _ _ _ _ _ _ (tagR ∘ rdtOf) tagW (fun _ _ => rfl) R₁)

/-- **The stretch at block k.** -/
theorem stretch_tags (a : ℕ) (R₁ R₂ R₃ : Rounds) {e : List (List ByteArray × ByteArray)}
    (bs : List (Block T Cl)) (hW : WrittenAs e (bs.flatMap (·.rounds)) R₁) (k : ℕ)
    (x : Block T Cl) (hx : bs[k]? = some x)
    (hroom : roundsIn (bs.take k) + x.rounds.length < roundsIn bs) :
    (((dataOf a R₁ R₂ R₃).ds₁.drop (roundsIn (bs.take k))).take x.rounds.length).map tagR =
      x.rounds.map tagD := by
  rw [List.map_take, List.map_drop, data_tags, written_tags hW, List.dropLast_eq_take,
    List.drop_take, List.take_take, List.length_map, length_flat,
    Nat.min_eq_left (by omega), ← List.map_drop, ← List.map_take, rounds_at bs k x hx]

end VerifiableInference.Desc.K13.Law
