-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/MaskEntry.lean: THE PROOF OF THE STATEMENT OF
Johnson/Road/K4/Rec/MaskEntryStatement.lean (`MaskEntryIs`), AS IT IS TYPED THERE: at an unmarked
statement inside the promise of the table of joints at a border, the mask entry that the reader of
the rows on the committed table of weights reads through the verifier's state, at the index masks'
message and the entry that its ledger hands out next, is one entry of the witness's own table, at a
seat, a row and a place of the public parameters. Statements with their proofs.
Main names:
  `taken_row_place`: the k-th number that a ledger of m mask rows hands out has the low bits k % m
    and the high bits k / m (`takenNo_eq`, OnBytes/Iop/LedgerPlaces.lean; `entryAt_entryNo`,
    Fmt/PlacesLaws.lean).
  `mask_entry_at`: **the core, free of any table of joints**: at a verifier's state that passes the
    proximity test's three public tests, whose book has a place for every message and names trees
    that are there: at a message number o with the shape sh and the seat q of the public
    parameters, and k below the shape's count of free entries:
    `(rwBook arr mat (z, s) w).mask ⟨o, takenNo sh.maskRows k⟩ =
      w.tab s.st.codes sh (arr q.1 q.2) q.1 q.2 true (k % sh.maskRows) (k / sh.maskRows)`.
    The cut of the reader to the table's size does not bite: the number lies within the mask table
    (`takenNo_lt`, `tableSize_mask`: Johnson/Desc/K13/Law/LedgerWithin.lean).
  `maskEntryIs`: the statement: the core's premises out of the promise (`three_at`,
    Johnson/Road/K4/Rec/NextEntry.lean) and the two tests.
What is not claimed. What the statement's file says is not claimed. K04_law, the law of K4's
sub-protocol itself, IS NOT PROVED BY THIS. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Road.K4.Rec.MaskEntryStatement
import Johnson.Road.K4.Rec.NextEntry
import Johnson.Desc.K13.Law.LedgerWithin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Rec
open OnBytes OnBytes.Model OnBytes.Slice
open Fmt.Places (logUp entryNo entryAt freeAt entryAt_entryNo)
open OnBytes.Means (tableSize realRows wordsOn)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S ModelPart Pub More Meaning Numbers pubSets)
open VerifiableInference.Desc.K12.Door (Laid msgShapesB bookInOrderB seatsCarriedB placesBelowB
  msgShape_at place_of_seats)
open VerifiableInference.Desc.K13.Law (rwBook maskCut takenNo_lt tableSize_mask free_is)
open VerifiableInference.Desc.Sound (Frame MsgT onQ wordsFirst wordsFirst_is tabFirst_at_door)
open Johnson.Desc.First.Walk.Tied (rowsBefore)

/-- The k-th number handed out: its low bits are the row k % m, its high bits the place k / m. -/
theorem taken_row_place {m : ℕ} (hm : 0 < m) (k : ℕ) :
    takenNo m k % 2 ^ logUp m = k % m ∧ takenNo m k / 2 ^ logUp m = k / m := by
  have hE := entryAt_entryNo (m := m) (r := k % m) (c := k / m) (Nat.mod_lt _ hm)
  have hT : takenNo m k = entryNo m (k % m) (k / m) := takenNo_eq hm k
  rw [← hT] at hE
  unfold entryAt at hE
  split at hE
  · have e := Option.some.inj hE
    exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
  · cases hE

/-- **The core.** -/
theorem mask_entry_at {Pp Cells Tok : Type} {nR kC : ℕ} (arr : ℕ → ℕ → ℕ)
    (mat : Cells → Fin nR → (Fin kC → Bool) → GE) (M : List OracleShape) (L : Laid) (z : Pp)
    (s : S) (w : VerifiableInference.Desc.Wit Cells Tok MsgT) (o k : ℕ) (sh : OracleShape)
    (q : ℕ × ℕ) (h₁ : msgShapesB M s.st = true) (h₂ : bookInOrderB 0 s.book s.roots = true)
    (h₃ : seatsCarriedB L s.book = true) (hs : s.book.place.size = s.st.oracles.size)
    (hb : placesBelowB L s.book.place.size s.book.trees.size = true)
    (ho : o < s.st.oracles.size) (hsh : M[o]? = some sh) (hq : L.places[o]? = some q)
    (hm : 0 < sh.maskRows) (h1 : 1 ≤ sh.answers)
    (hk : k < Send.freeMaskEntries sh.maskRows (s.st.codes.mask.getD sh.maskCode default).ell
      sh.answers) :
    (rwBook arr mat (z, s) w).mask ⟨o, takenNo sh.maskRows k⟩ =
      w.tab s.st.codes sh (arr q.1 q.2) q.1 q.2 true (k % sh.maskRows) (k / sh.maskRows) := by
  obtain ⟨sh', q', a1, a2, a3⟩ :=
    tabFirst_at_door arr M L s.st s.book s.roots h₁ h₂ h₃ hs hb w o ho
  obtain rfl : sh' = sh := Option.some.inj (a1.symm.trans hsh)
  obtain rfl : q' = q :=
    Option.some.inj (a2.symm.trans ((place_of_seats h₃ o (by rw [hs]; exact ho)).trans hq))
  obtain ⟨x, hx, hxs⟩ : ∃ x, s.st.oracles[o]? = some x ∧ x.shape = sh' := by
    have e := msgShape_at h₁ o ho
    rw [a1] at e
    exact Option.map_eq_some_iff.1 e
  have hv : takenNo sh'.maskRows k < tableSize s.st o .mask := by
    rw [tableSize_mask hx (by rw [hxs]; exact hm), hxs]
    exact takenNo_lt hm h1 (by rw [← free_is]; exact hk)
  have hrb : s.st.rowBits o .mask = logUp sh'.maskRows := by
    unfold Statement.rowBits
    rw [hx]
    show ceilLog2 (x.shape.rows .mask) = _
    rw [hxs]
    rfl
  have hrr : realRows s.st o .mask = sh'.maskRows := by
    unfold realRows
    rw [hx]
    show x.shape.rows .mask = _
    rw [hxs]
    rfl
  obtain ⟨e1, e2⟩ := taken_row_place hm k
  show maskCut s.st (wordsFirst arr s.st s.book w) ⟨o, takenNo sh'.maskRows k⟩ = _
  unfold maskCut
  dsimp only
  rw [if_pos hv, wordsFirst_is]
  unfold wordsOn
  rw [hrb, hrr, e1, e2, if_pos (Nat.mod_lt _ hm), a3]
  rfl

/-- **The statement.** -/
theorem maskEntryIs : MaskEntryIs := by
  intro P Cells Tok Fr N Mg Z links ps j m M L cs fvs sh q eS eB eSe eC hO hF hsh hq b hb hu nR kC
    arr mat w
  obtain ⟨hin, hpub, hbk⟩ := three_at hb hu
  have op : ∀ i ∈ maskItems, Mg.pub i (Z, b.1) = true := fun i hi =>
    List.all_eq_true.mp hpub i (List.mem_append_left _ (by
      simpa using List.all_eq_true.mp hO i hi))
  have h₁ : msgShapesB M b.1.st = true :=
    (eS (Z, b.1)).symm.trans (op _ (by simp [maskItems]))
  have h₂ : bookInOrderB 0 b.1.book b.1.roots = true :=
    (eB (Z, b.1)).symm.trans (op _ (by simp [maskItems]))
  have h₃ : seatsCarriedB L b.1.book = true :=
    (eSe (Z, b.1)).symm.trans (op _ (by simp [maskItems]))
  have hcs : b.1.st.codes = cs := eC (Z, b.1) hin
  unfold VerifiableInference.Desc.First.bookAt at hbk
  simp only [Bool.and_eq_true, beq_iff_eq] at hbk
  unfold maskFitsB at hF
  rw [hsh] at hF
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hF
  obtain ⟨⟨hlt, hbel⟩, ⟨hm0, h1⟩, hk⟩ := hF
  have hno : nextNoP M (N.msgsAt ps[j]?) N.indexNo fvs m =
      takenNo sh.maskRows (rowsBefore fvs m) := by
    unfold nextNoP
    rw [List.getElem?_take_of_lt hlt, hsh]
    rfl
  rw [hno, ← hcs]
  exact mask_entry_at arr mat M L Z b.1 w N.indexNo (rowsBefore fvs m) sh q h₁ h₂ h₃ hbk.1.2
    (by rw [hbk.1.2, hbk.2, hbk.1.1]; exact hbel) (by rw [hbk.2]; exact hlt) hsh hq hm0 h1
    (by rw [hcs]; exact hk)

end OnBytes.Road.K4.Rec

#print axioms OnBytes.Road.K4.Rec.taken_row_place
#print axioms OnBytes.Road.K4.Rec.mask_entry_at
#print axioms OnBytes.Road.K4.Rec.maskEntryIs
