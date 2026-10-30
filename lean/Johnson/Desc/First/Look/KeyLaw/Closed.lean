-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/KeyLaw/Closed.lean: THE TYPED LOOKUP OF A KEY FILE'S LOOKUP WITH NO LETTER
LEFT: made of the plan's lookup, the matrix's size and the table of homes alone. Its entries are
read off words and off a matrix, and the conditions that a link's law puts on a typed lookup hold at
it for ALL words and ALL matrices.

The typed lookup datK has the public record pubOf (Wf.lookupOf id m l) by construction. Its entries:
a place for each member of the table of homes (and one to spare); a cell for each row of the table
and each real plane (and one plane to spare); a cell for each entry of the matrix. Its table is the
range table. Its keys are the keys that the matrix's cells hold (Leaves.key), part by part. Its
states are of any type T: nothing of it reads them, and the typed verifier hands them on.

Main names:
  JK, datK, slK, msgK: the entries; the typed lookup; where a mask entry stands; the reading.
  matOf: the matrix that entries hold. matOf_msgK: read off a matrix it is that matrix, inside.
  tiedK, faceIsK, keysAreK: Tied, FaceIs and KeysAre hold at it, for all words and matrices.
  KeysIn, in_iff, in_iff_at: the typed in-relation: every key that the matrix holds is the number of
    a row of the range table.
  holds_cut: a row on the matrix reads the matrix inside its size alone.

Limits. KeysIn speaks of the matrix cut at its size: that no run reads outside it is the test
fitsMatrix's, which in_iff does not spend. The table of homes hs is an argument. That this typed
lookup is the one at which a typed list of the whole file stands, and that the words and the matrix
are what a file's oracle messages hold, is not shown here.

-/
import Johnson.Desc.First.Look.KeyLaw.KeyClaim
import Johnson.Desc.First.Look.KeyLaw.FaceAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Slice OnBytes.K.Kc
open OnBytes.Model (Reading)
open OnBytes.Params (Setting WfLookup WfPart WfPublic)
open Lk6 (Dat Pub pubOf)

variable (T : Type) (id : ℕ) (m : Wf.Matrix) (l : WfLookup) (hs : List Slot)

/-- The entries. -/
abbrev JK : Type :=
  Fin (hs.length + 1) ⊕ (Fin (2 ^ l.d) × Fin (Wf.planesOf l + 1)) ⊕ (Fin m.rows × Fin (2 ^ m.kCol))

/-- The matrix that entries hold; 0 outside its size. -/
def matOf (μ : JK m l hs → GE) (r c : ℕ) : GE :=
  if h : r < m.rows ∧ c < 2 ^ m.kCol then μ (.inr (.inr (⟨r, h.1⟩, ⟨c, h.2⟩))) else 0

/-- **The typed lookup of a key file's lookup.** -/
noncomputable def datK : Dat GE :=
  { pubOf (Wf.lookupOf id m l) with
    St := T
    J := JK m l hs
    key := fun _ μ j =>
      match l.parts[j]? with
      | some p => Leaves.key (Leaves.lkOf l (Leaves.padOf id m l zeroE)) (matOf m l hs μ) m.kCol
          p.runs
      | none => fun _ => 0
    tab := fun _ u => (u : GE)
    bAt := fun u p => .inr (.inl (⟨u % 2 ^ l.d, Nat.mod_lt _ (Nat.two_pow_pos _)⟩,
      ⟨p % (Wf.planesOf l + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩)) }

/-- Where a mask entry stands: at its first place in the table of homes. -/
def slK : Slot → (datK T id m l hs).J :=
  fun s => .inl ⟨hs.idxOf s % (hs.length + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

/-- The entries, read off words and a matrix. -/
def msgK (x : WfPublic) (codes : Codes) (i : ℕ) (w : Means.Words GE) (M : ℕ → ℕ → GE) :
    (datK T id m l hs).J → GE
  | .inl a => w (hs.getD a.val default).oracle .mask (hs.getD a.val default).index
  | .inr (.inl c) => Planes.bitsOf x codes i (w x.messageId .main) c.1.val c.2.val
  | .inr (.inr c) => M c.1.val c.2.val

/-- Read off a matrix, the entries hold that matrix, inside its size. -/
theorem matOf_msgK (x : WfPublic) (codes : Codes) (i : ℕ) (w : Means.Words GE) (M : ℕ → ℕ → GE)
    (r c : ℕ) (hr : r < m.rows) (hc : c < 2 ^ m.kCol) :
    matOf m l hs (msgK T id m l hs x codes i w M) r c = M r c := by
  unfold matOf
  rw [dif_pos ⟨hr, hc⟩]
  rfl

/-- **For all words and matrices the entries read off them are tied to the words.** -/
theorem tiedK (x : WfPublic) (codes : Codes) (i : ℕ) (w : Means.Words GE) (M : ℕ → ℕ → GE) :
    Tied (datK T id m l hs) (slK T id m l hs) (msgK T id m l hs x codes i w M) w x codes i hs where
  mask := fun s h => by
    have h1 : hs.idxOf s < hs.length := List.idxOf_lt_length_iff.2 h
    have h2 : hs.idxOf s % (hs.length + 1) = hs.idxOf s := Nat.mod_eq_of_lt (by omega)
    have h3 : hs.getD (hs.idxOf s) default = s := by
      rw [List.getD_eq_getElem _ _ h1, List.getElem_idxOf]
    show w (hs.getD (hs.idxOf s % (hs.length + 1)) default).oracle .mask
      (hs.getD (hs.idxOf s % (hs.length + 1)) default).index = _
    rw [h2, h3]
  bit := fun t ht j hj => by
    have ht' : t < 2 ^ l.d := ht
    have hj' : j < Wf.planesOf l := hj
    show Planes.bitsOf x codes i (w x.messageId .main) (t % 2 ^ l.d) (j % (Wf.planesOf l + 1)) = _
    rw [Nat.mod_eq_of_lt ht', Nat.mod_eq_of_lt (by omega)]

/-- **The face of the lookup is this typed lookup's.** -/
theorem faceIsK {p : ℕ} (st : T) (hadm : (pubOf (Wf.lookupOf id m l)).Adm p) (hd : l.d ≤ 64) :
    FaceIs (datK T id m l hs) st (faceOfLkp (Wf.lookupOf id m l)) :=
  faceIs_lookupOf id m l (datK T id m l hs) st rfl hadm (fun _ _ => rfl) hd

/-- **Its keys are the keys that the matrix in its entries holds.** -/
theorem keysAreK (st : T) (μ : (datK T id m l hs).J → GE) :
    KeysAre (datK T id m l hs) st μ id m l (matOf m l hs μ) := by
  intro j p hp
  show (match l.parts[j]? with
    | some p => Leaves.key (Leaves.lkOf l (Leaves.padOf id m l zeroE)) (matOf m l hs μ) m.kCol
        p.runs
    | none => fun _ => 0) = _
  rw [hp]

/-- A matrix cut at its size: 0 outside. -/
def cutM (M : ℕ → ℕ → GE) (r c : ℕ) : GE := if r < m.rows ∧ c < 2 ^ m.kCol then M r c else 0

/-- Read off a matrix, the entries hold that matrix, cut at its size. -/
theorem matOf_cut (x : WfPublic) (codes : Codes) (i : ℕ) (w : Means.Words GE) (M : ℕ → ℕ → GE) :
    matOf m l hs (msgK T id m l hs x codes i w M) = cutM m M := by
  funext r c
  unfold matOf cutM
  by_cases h : r < m.rows ∧ c < 2 ^ m.kCol
  · rw [dif_pos h, if_pos h]
    rfl
  · rw [dif_neg h, if_neg h]

/-- Every key of every part that the matrix holds is the number of a row of the range table. -/
def KeysIn (M : ℕ → ℕ → GE) : Prop :=
  ∀ (j : ℕ) (p : WfPart), l.parts[j]? = some p → ∀ b < 2 ^ (m.kCol + p.logPlaces),
    ∃ u : ℕ, u < 2 ^ l.d ∧
      Leaves.key (Leaves.lkOf l (Leaves.padOf id m l zeroE)) M m.kCol p.runs b = (u : GE)

/-- **The typed lookup's in-relation**, of the entries: every key that the matrix in the entries
holds is the number of a row of the range table. -/
theorem in_iff (st : T) (μ : (datK T id m l hs).J → GE) :
    (datK T id m l hs).In st μ ↔ KeysIn id m l (matOf m l hs μ) := by
  have hm : (datK T id m l hs).m = l.parts.length := List.length_map _
  have hv : ∀ (j : ℕ) (p : WfPart), l.parts[j]? = some p →
      (datK T id m l hs).v j = m.kCol + p.logPlaces := by
    intro j p hp
    show (l.parts.map fun p => p.logPlaces + m.kCol).getD j 0 = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hp]
    exact Nat.add_comm _ _
  constructor
  · intro h j p hp b hb
    have hj : j < (datK T id m l hs).m := by
      rw [hm]
      exact (List.getElem?_eq_some_iff.1 hp).1
    obtain ⟨u, hu, e⟩ := h j hj b (by rw [hv j p hp]; exact hb)
    exact ⟨u, hu, by rw [← keysAreK T id m l hs st μ j p hp]; exact e⟩
  · intro h j hj b hb
    have hj' : j < l.parts.length := by
      rw [← hm]
      exact hj
    have hp := List.getElem?_eq_getElem hj'
    obtain ⟨u, hu, e⟩ := h j _ hp b (by rw [← hv j _ hp]; exact hb)
    exact ⟨u, hu, by rw [keysAreK T id m l hs st μ j _ hp]; exact e⟩

/-- The same, of the entries read off words and a matrix. -/
theorem in_iff_at (st : T) (x : WfPublic) (codes : Codes) (i : ℕ) (w : Means.Words GE)
    (M : ℕ → ℕ → GE) :
    (datK T id m l hs).In st (msgK T id m l hs x codes i w M) ↔ KeysIn id m l (cutM m M) := by
  rw [in_iff, matOf_cut]

/-- A row on the matrix reads the matrix inside its size alone. -/
theorem holds_cut (W : PscF.World) (M M' : ℕ → ℕ → GE) (R k : ℕ) (t : Leaves.TRowF)
    (h : ∀ r < R, ∀ c < 2 ^ k, M r c = M' r c) : t.Holds W M R k ↔ t.Holds W M' R k := by
  unfold Leaves.TRowF.Holds
  have e : (∑ r ∈ Finset.range R, ∑ c ∈ Finset.range (2 ^ k), t.g r * Leaves.eqW t.psi c * M r c) =
      ∑ r ∈ Finset.range R, ∑ c ∈ Finset.range (2 ^ k), t.g r * Leaves.eqW t.psi c * M' r c :=
    Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun c hc => by
      rw [h r (Finset.mem_range.1 hr) c (Finset.mem_range.1 hc)]
  rw [e]

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.tiedK
#print axioms VerifiableInference.Desc.K3.KeyLaw.faceIsK
#print axioms VerifiableInference.Desc.K3.KeyLaw.keysAreK
#print axioms VerifiableInference.Desc.K3.KeyLaw.in_iff_at
