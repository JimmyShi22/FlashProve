-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerTies.lean: THEOREMS: THE THREE STATEMENTS OF LedgerTiesOwed.lean: the
pieces' rounds bear the written rounds' entries and kinds.
  zipWith_map_fst  a list zipped with a list of its own length, where what is read of the result
                   hangs on the first member alone.
  data2_written    the second chain's data, read as (entry, kind), ARE the written list read so: as
                   lists: no index is left out: sentBefore R is as long as R (the lemma
                   sentBefore_length, OnBytes/Maker/ReadSpecs.lean), so the zip cuts nothing.
  dataOfWritten    the first statement: index by index.
  takeOfRow        the second: the first seven rounds of a row's data.
  tiesAtScope      the third: in scope, where the value is laid (laidPOf_written,
                   Johnson/Desc/Laid/ProofFullScope.lean).
NOTHING HERE EVALUATES A WRITTEN LIST.
What is not claimed. THAT THE FIRST SEVEN ROUNDS OF THE LAID DATA ARE THE SEVEN ROUNDS OF A ROW's
PIECES: tiesAtScope takes "D.ds₂.take 7 = [...]" as a premise, and takeOfRow takes the eight pieces'
data's forms (f.ds = [], x3.ds = [], x6.ds = [] among them): who joins the two owes that the row's
data are the laid data. Nothing of the first or the third chain's data (the first chain's leave out
its last round). Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerTiesOwed
import OnBytes.Maker.ReadSpecs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Maker
open OnBytes.Params (Rounds)
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)

theorem zipWith_map_fst {α β γ δ : Type} {f : α → β → γ} {g : γ → δ} {h : α → δ}
    (hg : ∀ a b, g (f a b) = h a) :
    ∀ (l : List α) (l' : List β), l'.length = l.length → (List.zipWith f l l').map g = l.map h
  | [], [], _ => rfl
  | a :: l, b :: l', e => by
    have e' : l'.length = l.length := by simpa using e
    simp only [List.zipWith_cons_cons, List.map_cons, hg, zipWith_map_fst hg l l' e']
  | [], _ :: _, e => by simp at e
  | _ :: _, [], e => by simp at e

/-- **The second chain's data, read as (entry, kind), are the written list read so.** -/
theorem data2_written (a : ℕ) (R : Rounds × Rounds × Rounds) :
    (WholeD.of a (wholeAt (some R))).ds₂.map (fun d : RDT => (d.entry, d.kind)) =
      R.2.1.map fun r => (r.1.entry, r.1.kind) := by
  show (List.map rdtOf (List.zipWith (Three.rdOf _ _ _ 1 _ 0) R.2.1
    (Three.sentBefore R.2.1))).map (fun d : RDT => (d.entry, d.kind)) = _
  rw [List.map_map]
  refine zipWith_map_fst ?_ _ _ (sentBefore_length _)
  intro _ _
  rfl

theorem dataOfWritten : DataOfWrittenOwed := by
  intro a R i
  unfold writtenAt
  rw [← List.getElem?_map, data2_written, List.getElem?_map]

theorem takeOfRow : TakeOfRowOwed := by
  intro C Fr S Cl W f pt x2 x3 x4 x5 x6 x7 rest d d21 d22 d4 d51 d52 d7 hf hpt h2 h3 h4 h5 h6 h7
  simp [rowData, List.flatMap_cons, hf, hpt, h2, h3, h4, h5, h6, h7]

/-- Below 7 a list and its first seven members say the same. -/
theorem at_take {α : Type} {l L : List α} (h : l.take 7 = L) (i : ℕ) (hi : i < 7) :
    l[i]? = L[i]? := by
  rw [← h, List.getElem?_take_of_lt hi]

theorem tiesAtScope : TiesAtScopeOwed := by
  intro o Z D r hZ h d d21 d22 d4 d51 d52 d7 ht
  obtain rfl : D = Johnson.G.writtenPFull := LPFD.Full.laidPOf_written hZ h
  have key : ∀ (i : ℕ) (x : RDT), i < 7 → [d, d21, d22, d4, d51, d52, d7][i]? = some x →
      writtenAt Johnson.G.dryProofFull.2.1 i = some (x.entry, x.kind) := by
    intro i x hi hx
    rw [← dataOfWritten 32 Johnson.G.dryProofFull i, at_take ht i hi, hx]
    rfl
  exact ⟨key 0 d (by decide) rfl, key 1 d21 (by decide) rfl, key 3 d4 (by decide) rfl,
    key 4 d51 (by decide) rfl, key 6 d7 (by decide) rfl⟩

end Desc.K14.Law
