-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/DigitsAtTrace.lean

The smallness test's prover side at a trace T: that the cells are small if T's entries are; which
matrices a sub-proof's list names; the two arrays ZZ and BZ; and the lookup on the digits at them,
with no premise on the digits.

It joins three texts. Johnson/Desc/K8/Honest/Window.lean has the test cellsSmall on cells, and the
digits digitAt as a function of cells and of the drawn matrix;
Johnson/Desc/ProofFile/Honest/K8/Digits.lean has the array ZZ (zzOf) and the structure Digits of the
two arrays; Johnson/HonestTrace/CountsDigits.lean has BZ as a function of ZZ (bzOf) and the relation
of the lookup on the digits.

Main definitions: "cellsC X T" (the trace as a reader of cells by segment, label, row and column:
cellOf X T, Johnson/HonestTrace/Full.lean) · "matsOf X k" (for each matrix of the list of sub-proof
k: its owner's segment number, its label there, and the first column 0) · "zzE", "bzE" (the two
arrays in the extension field) · "digitsOf" (the structure Digits: ZZ is zzOf, BZ is bzOf of it) ·
"nuZ" (the reading of the places Fo.Pl: the planes' cells from BZ by virtZ, the mask entries from an
argument) · "MzFits tl" (tl.mz is the number of all rows of cells of tl's matrices).

Main theorems:
* "cellsSmall_cellOf", "cellsSmall_meetsAll": if every entry of T is below 129 in absolute value
  (MeetsAll.small), cellsSmall p (cellsAtOf (cellsC X T) mats) = true, at all numbers p and every
  list mats.
* "cellsAtOf_matsOf": under NamesFit and MeetsAll, for k < 25: read through matsOf X k, the reader
  gives T k mu r c at every number, row and column; the borrowed matrices too ("owner_entries").
  "matsOf_length": under PartsFit the list has 9, 5 or 8 members.
* "laidBZ_digitsOf": LaidBZ holds of zzE and bzE, with no premise. "digitsIn_zzOf": under
  FromPieces tl and MzFits tl, DigitsIn holds of zzE, at every list, reader of cells and drawn
  matrix (from digitAt_lt, Johnson/Desc/K8/Honest/DigitsLaw.lean).
* "claimsZero_digits_zzOf": under FromPieces tl, MzFits tl and Ch.Fits: ClaimsZero
  (Johnson/HonestTrace/LookAtClaims.lean) at tl.f9, lm = 5, the key vectors kvZ of zzE and ν := nuZ
  of bzE, for all mask entries, jLK, θ and al.

Limits. Beside this folder's own files this file imports Johnson/Desc/K8/Honest/DigitsLaw.lean and
Johnson/Desc/ProofFile/Honest/K8/Digits.lean. FromPieces, MzFits, PartsFit, NamesFit, MeetsAll and
Ch.Fits are assumed. The owners are Sz.ref.owner's (Johnson/HonestTrace/Places.lean), at 12 groups.
On sizes. THE FULL SIZE ALONE. cellsC and matsOf number the segments as a proof with 12 groups of
layers does (Seg.ofNo 12: group g is 2 g, its attention 2 g + 1, the head 24), whatever X's own
number of groups is. From k = 25 on cellsC X T answers 0 and matsOf X k is empty. At public files
with fewer groups both go wrong without a word: at the small example (2 groups: its head is
sub-proof 4) they take number 4 for a group of layers: cellsC answers 0 at every label of the head,
and matsOf X 4 is a group's list. cellsAtOf_matsOf and matsOf_length ask the parts 3, 1, 1, 4.
On labels. A part of af, ad, as or hf is a label of its own here ("af0", "af1"), with columns from
0: so every first column is 0. cellsC X T answers 0 at every string that is no label of the segment,
"af", "ad", "as" and "hf" among them. At a list with such strings cellsSmall says true of zeros: the
law speaks of T's entries only through a list that names them, as matsOf X k does
(cellsAtOf_matsOf).
On the window. digitsIn_zzOf and claimsZero_digits_zzOf hold at every list, reader and drawn matrix
because the entries of zzOf are remainders, in range at every integer. Nothing here says that a
combination lies in its window, so nothing on whether ZZ's digits give the combinations back
(digitAt_back, Johnson/Desc/K8/Honest/DigitsLaw.lean, asks leaves = none).
On the list. ClaimsZero is on the library's list Fo.claimsOf at lm = 5, at rsF, a term of this
library that no statement compares with a prover's program. Of that list and the smallness test's
own routines the library says this (Fo.tail_look_dig, OnBytes/Tie/Pv/Lookup/Ends/FoTailLook.lean,
with Fo.claimsZ_perm): where Forest.objects, HTailF2.linJoin9 and HTailF2.linBits9 return in turn,
what the test has heard holds the end values of the rounds (Fo.HeardIs), the world's virtual rows on
BZ and ZZ are as its premises say, and its premises on public numbers and the state's sizes hold,
the total of the sub-proof's one equation grows by Fo.powSum of a permutation of that list, at the
digits' own letters. None of these premises is shown here at rsF.
What a prover's side still owes behind this file: that no combination leaves its window, with the
share of drawn matrices at which one does; the test's claims that tie ZZ to the cells; the premises
just named; that the matrix which member mu of matsOf X k names has the rows and columns of member
mu of tl.mats (shown here: the length of matsOf X k alone, under PartsFit; that tl.mats has as many
members is not shown in this file); the mask entries; that the arrays are sent and committed.

Not claimed: that a prover commits to these arrays; that a verifier accepts; anything on what the
arrays show of the cells.
-/
import Johnson.HonestTrace.CellOfAt
import Johnson.HonestTrace.LookAtDigitsClaims
import Johnson.HonestTrace.Places
import Johnson.Desc.ProofFile.Honest.K8.Digits
import Johnson.Desc.K8.Honest.DigitsLaw

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model
open OnBytes.Road
open OnBytes.Model (HTailF2)
open Fo.ZPlan (FromPieces)
open ProofFile.Honest (Cells)
open ProofFile.Honest.K8 (Digits zzOf parOfTail cellsAtOf signedOf)
open VerifiableInference.Desc.First.K8 (Par)
open VerifiableInference.Desc.First.K8.Honest (cellsSmall digitAt allRows)

/-! ## (a) The cells are small -/

/-- A trace as the reader of cells by segment, label, row and column. At a string that is no label
of the segment it yields 0; as at zzOf (Johnson/Desc/ProofFile/Honest/K8/Digits.lean): "At a name in
mats that is no label the cells are what the reader yields there." Read through a list mats
(cellsAtOf), "the entries are the trace's only at mats := matsOf X k (cellsAtOf_matsOf)". -/
def cellsC (X : Model.Verify.Public) (T : Tr) : Cells := ⟨cellOf X T⟩

variable {X : Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-- An integer below 129 in absolute value, carried into the base field, is read back by
signedOf. -/
theorem signedOf_cast (z : ℤ) (h : |z| < 129) : signedOf ((z : ℤ) : Cb.Gl.F) = z := by
  have hp : (Code.pGold : ℤ) = 18446744069414584321 := by rw [Code.pGold_eq]; rfl
  have hv : ((((z : ℤ) : Cb.Gl.F)).val : ℤ) = z % (Code.pGold : ℤ) := ZMod.val_intCast z
  obtain ⟨h1, h2⟩ := abs_lt.1 h
  unfold signedOf
  by_cases hz : 0 ≤ z
  · have e : z % (Code.pGold : ℤ) = z := Int.emod_eq_of_lt hz (by rw [hp]; omega)
    rw [e] at hv
    have hc : 2 * (((z : ℤ) : Cb.Gl.F)).val < Code.pGold := by
      have : (2 * (((z : ℤ) : Cb.Gl.F)).val : ℤ) < (Code.pGold : ℤ) := by rw [hv, hp]; omega
      exact_mod_cast this
    rw [if_pos hc, hv]
  · have e : z % (Code.pGold : ℤ) = z + (Code.pGold : ℤ) := by
      rw [← Int.add_emod_right]
      exact Int.emod_eq_of_lt (by rw [hp]; omega) (by omega)
    rw [e] at hv
    have hc : ¬ 2 * (((z : ℤ) : Cb.Gl.F)).val < Code.pGold := by
      intro hlt
      have : (2 * (((z : ℤ) : Cb.Gl.F)).val : ℤ) < (Code.pGold : ℤ) := by exact_mod_cast hlt
      rw [hv, hp] at this
      omega
    rw [if_neg hc, hv]
    ring

/-- If every entry of T is below 129 in absolute value: at every number, string, row and column,
cellOf X T is the image of an integer below 129 in absolute value. -/
theorem cellOf_int (X : Model.Verify.Public) (T : Tr) (hs : ∀ k a r c, |T k a r c| < 129)
    (k : ℕ) (s : String) (r c : ℕ) :
    ∃ z : ℤ, |z| < 129 ∧ cellOf X T k s r c = ((z : ℤ) : Cb.Gl.F) := by
  have h0 : ∃ z : ℤ, |z| < 129 ∧ (0 : Cb.Gl.F) = ((z : ℤ) : Cb.Gl.F) := ⟨0, by norm_num, by simp⟩
  have hb : ∀ σ μ, |byName X T σ μ r c| < 129 := by
    intro σ μ
    unfold byName
    split
    · split
      · exact hs _ _ _ _
      · norm_num
    · norm_num
  unfold cellOf
  split
  · split
    · exact ⟨_, hb _ _, rfl⟩
    · exact h0
  · exact h0

/-- If every entry of T is below 129 in absolute value, the test cellsSmall says true of the cells
that cellsAtOf reads off cellOf X T: at all numbers p and every list mats. At a member of mats whose
string is no label of its segment these cells are 0, not entries of T. -/
theorem cellsSmall_cellOf (hs : ∀ k a r c, |T k a r c| < 129) (p : Par)
    (mats : List (ℕ × String × ℕ)) : cellsSmall p (cellsAtOf (cellsC X T) mats) = true := by
  unfold cellsSmall
  refine List.all_eq_true.2 fun mu _ => List.all_eq_true.2 fun r _ => List.all_eq_true.2
    fun c _ => decide_eq_true ?_
  unfold cellsAtOf
  cases mats[mu]? with
  | none => simp
  | some m =>
    obtain ⟨z, hz, e⟩ := cellOf_int X T hs m.1 m.2.1 r (m.2.2 + c)
    show (signedOf (cellOf X T m.1 m.2.1 r (m.2.2 + c))).natAbs ≤ 128
    rw [e, signedOf_cast z hz]
    rw [Int.abs_eq_natAbs] at hz
    omega

/-- Under MeetsAll the same. -/
theorem cellsSmall_meetsAll (M : MeetsAll X i x T) (p : Par) (mats : List (ℕ × String × ℕ)) :
    cellsSmall p (cellsAtOf (cellsC X T) mats) = true :=
  cellsSmall_cellOf M.small p mats

/-! ## (b) The list of matrices of a segment: owner's segment, label there, first column -/

/-- For each matrix of the list of sub-proof k at X's numbers of parts, in the list's order: the
number of the segment that owns it, its label there, and 0, its first column under that label. The
empty list from k = 25 on. -/
def matsOf (X : Model.Verify.Public) (k : ℕ) : List (ℕ × String × ℕ) :=
  match Seg.ofNo 12 k with
  | some σ =>
    (MatName.all (X.y.parts.getD 0 0) (X.y.parts.getD 1 0) (Hd.shapeA X (k / 2)).cf.NAs X.hS.NHf
      σ).map fun μ => ((Sz.ref.owner σ μ).1.no 12, (Sz.ref.owner σ μ).2.label, 0)
  | none => []

/-- For k < 25 there is a segment with the number k. -/
theorem seg_of_lt {k : ℕ} (hk : k < 25) : ∃ σ, Seg.ofNo 12 k = some σ := by
  by_cases h24 : k = 24
  · exact ⟨.head, by rw [h24]; rfl⟩
  · by_cases he : k % 2 = 0
    · obtain ⟨g, rfl⟩ : ∃ g, k = 2 * g := ⟨k / 2, by omega⟩
      exact ⟨.ff g, Seg.ofNo_no (σ := .ff g) (show g < 12 by omega)⟩
    · obtain ⟨g, rfl⟩ : ∃ g, k = 2 * g + 1 := ⟨k / 2, by omega⟩
      exact ⟨.att g, Seg.ofNo_no (σ := .att g) (show g < 12 by omega)⟩

/-- Under NamesFit and MeetsAll, for a segment σ of the proof: the owner of member number mu of σ's
list is a segment of the proof, has a number for the matrix, and T holds there the entries of
matrix number mu of σ's list. -/
theorem owner_entries (N : NamesFit X T) (M : MeetsAll X i x T) {σ : Seg} (hσ : σ.Below 12)
    {mu : ℕ} {μ : MatName} (hμ : (MatName.all 3 1 1 4 σ)[mu]? = some μ) (r c : ℕ) :
    ∃ a, (Sz.ref.owner σ μ).1.Below 12 ∧
      MatName.no? 3 1 1 4 (Sz.ref.owner σ μ).1 (Sz.ref.owner σ μ).2 = some a ∧
      T ((Sz.ref.owner σ μ).1.no 12) a r c = T (σ.no 12) mu r c := by
  have hn := all_no_ref σ hμ
  have own : Sz.ref.owner σ μ = (σ, μ) → ∃ a, (Sz.ref.owner σ μ).1.Below 12 ∧
      MatName.no? 3 1 1 4 (Sz.ref.owner σ μ).1 (Sz.ref.owner σ μ).2 = some a ∧
      T ((Sz.ref.owner σ μ).1.no 12) a r c = T (σ.no 12) mu r c := fun e => by
    rw [e]
    exact ⟨mu, hσ, hn, rfl⟩
  have iQA : (Model.Layer.matIx X.y).iQA = 6 := by
    show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 2 = 6
    rw [N.parts.af, N.parts.ad]
  have iXO : (Model.Layer.matIx X.y).iXO = 7 := by
    show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 3 = 7
    rw [N.parts.af, N.parts.ad]
  have iXI : (Model.Layer.matIx X.y).iXI = 8 := by
    show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 4 = 8
    rw [N.parts.af, N.parts.ad]
  cases σ with
  | ff g =>
    have hg : g < 12 := hσ
    cases μ <;> try exact own rfl
    · -- xbI
      obtain rfl : mu = 8 := (Option.some.inj (show some (3 + 1 + 4) = some mu from hn)).symm
      by_cases h0 : g = 0
      · exact own (if_pos h0)
      · have e : Sz.ref.owner (.ff g) .xbI = (.ff (g - 1), .xbO) := if_neg h0
        rw [e]
        refine ⟨7, show g - 1 < 12 by omega, rfl, ?_⟩
        have s := M.ords.seamFF g (by omega) hg r c
        rw [iXI, iXO] at s
        exact s.symm
  | att g =>
    have hg : g < 12 := hσ
    cases μ <;> try exact own rfl
    · -- qa
      obtain rfl : mu = 4 := (Option.some.inj (show some (1 + 3) = some mu from hn)).symm
      refine ⟨6, hg, rfl, ?_⟩
      have s := M.ords.seamA g hg r c
      rw [iQA, N.parts.as g hg] at s
      exact s.symm
  | head =>
    cases μ <;> try exact own rfl
    · -- xbL
      obtain rfl : mu = 7 := (Option.some.inj (show some (4 + 3) = some mu from hn)).symm
      refine ⟨7, show 11 < 12 by norm_num, rfl, ?_⟩
      have s := M.ords.seamH r c
      rw [iXO, N.parts.hf] at s
      exact s.symm

/-- Under NamesFit and MeetsAll, for k < 25: read through matsOf X k, the reader of cells cellOf X T
gives the list of sub-proof k in T, at every number, row and column; borrowed matrices too. -/
theorem cellsAtOf_matsOf (N : NamesFit X T) (M : MeetsAll X i x T) {k : ℕ} (hk : k < 25)
    (mu r c : ℕ) : cellsAtOf (cellsC X T) (matsOf X k) mu r c = T k mu r c := by
  obtain ⟨σ, hσ⟩ := seg_of_lt hk
  obtain ⟨hb, hno⟩ := Seg.of_ofNo hσ
  have p1 := (parts_at N.parts hσ).1
  unfold cellsAtOf matsOf
  rw [hσ]
  simp only [p1, List.getElem?_map]
  cases hμ : (MatName.all 3 1 1 4 σ)[mu]? with
  | none =>
    have hl : labelAt X k mu = none := by
      unfold labelAt
      rw [hσ]
      simp only [Option.bind_some, p1, hμ, Option.map_none]
    rw [N.beyond k hk mu r c hl]
    rfl
  | some μ =>
    obtain ⟨a, ob, on, oe⟩ := owner_entries N M hb hμ r c
    show signedOf (cellOf X T ((Sz.ref.owner σ μ).1.no 12) (Sz.ref.owner σ μ).2.label r (0 + c)) =
      _
    rw [Nat.zero_add, cellOf_label N.parts T ob on, signedOf_cast _ (M.small _ _ _ _), oe, hno]

/-- Under PartsFit, for k < 25: matsOf X k has 8 members at the head, 9 at a group of layers, 5 at
an attention sub-proof. -/
theorem matsOf_length (P : PartsFit X) {k : ℕ} (hk : k < 25) :
    (matsOf X k).length = if k = 24 then 8 else if k % 2 = 0 then 9 else 5 := by
  obtain ⟨σ, hσ⟩ := seg_of_lt hk
  obtain ⟨hb, hno⟩ := Seg.of_ofNo hσ
  have p1 := (parts_at P hσ).1
  unfold matsOf
  rw [hσ]
  simp only [p1, List.length_map]
  cases σ with
  | ff g =>
    have e : 2 * g = k := hno
    have hg : g < 12 := hb
    rw [if_neg (by omega), if_pos (by omega)]
    rfl
  | att g =>
    have e : 2 * g + 1 = k := hno
    rw [if_neg (by omega), if_neg (by omega)]
    rfl
  | head =>
    have e : 24 = k := hno
    rw [if_pos e.symm]
    rfl

/-! ## (c) The two arrays, and the lookup on the digits at them -/

/-- ZZ in the extension field. As at zzOf (Johnson/Desc/ProofFile/Honest/K8/Digits.lean): "This is
the array before encoding: which part sends it, with which coins, is not said here. At a name in
mats that is no label the cells are what the reader yields there." -/
def zzE (tl : HTailF2) (mats : List (ℕ × String × ℕ)) (C : Cells) (trits : List ℤ) :
    ℕ → ℕ → Cb.Gl.E := fun u col => algebraMap Cb.Gl.F Cb.Gl.E (zzOf tl mats C trits u col)

/-- **The two arrays**: ZZ is zzOf; BZ is bzOf (Johnson/HonestTrace/CountsDigits.lean) of it. Beyond
its 32 rows and bzColumns columns bz is whatever bzOf yields. Of each of the two, as at zzOf
(Johnson/Desc/ProofFile/Honest/K8/Digits.lean): "This is the array before encoding: which part sends
it, with which coins, is not said here. At a name in mats that is no label the cells are what the
reader yields there." -/
def digitsOf (tl : HTailF2) (mats : List (ℕ × String × ℕ)) (C : Cells) (trits : List ℤ) :
    Digits where
  zz := zzOf tl mats C trits
  bz := fun row col => ((bzOf tl (zzE tl mats C trits) row col : ℕ) : Cb.Gl.F)

/-- BZ in the extension field. As at zzOf (Johnson/Desc/ProofFile/Honest/K8/Digits.lean): "This is
the array before encoding: which part sends it, with which coins, is not said here. At a name in
mats that is no label the cells are what the reader yields there." -/
def bzE (tl : HTailF2) (mats : List (ℕ × String × ℕ)) (C : Cells) (trits : List ℤ) :
    ℕ → ℕ → Cb.Gl.E := fun row col =>
  algebraMap Cb.Gl.F Cb.Gl.E ((digitsOf tl mats C trits).bz row col)

/-- The reading of the places Fo.Pl of the lookup on the digits: the cells of the matrix with one
row a plane from BZ (virtZ); the mask entries from an argument; 0 elsewhere. The mask is a letter,
never a default: "whoever calls it at a run lays the mask row's entries there by a named cut: never
0". At a key's place and at .zero it reads 0. That no claim of this lookup reads it at a key's place
is not shown in this file: none of its theorems names a key's place; claimsZero_digits
(Johnson/HonestTrace/LookAtDigitsClaims.lean) asks of a reading its values at the planes' cells and
at .zero alone. -/
def nuZ (tl : HTailF2) (bz : ℕ → ℕ → Cb.Gl.E) (mask : ℕ → Cb.Gl.E) : _root_.Fo.Pl → Cb.Gl.E
  | .mask j => mask j
  | .cell r c => virtZ tl bz r c
  | .key _ _ => 0
  | .zero => 0

/-- The digits' width in the plan's state is the number of all rows of cells of its matrices. -/
def MzFits (tl : HTailF2) : Prop := tl.mz = allRows (parOfTail tl)

variable (tl : HTailF2) (mats : List (ℕ × String × ℕ)) (C : Cells) (trits : List ℤ)

/-- bzE holds bzOf of zzE: LaidBZ, at every tl, list, reader of cells and drawn matrix. -/
theorem laidBZ_digitsOf : LaidBZ tl (zzE tl mats C trits) (bzE tl mats C trits) :=
  fun _ _ _ _ => map_natCast _ _

variable {tl}

/-- Under FromPieces tl and MzFits tl: every digit of zzE is in its range (DigitsIn), at every list,
reader of cells and drawn matrix. -/
theorem digitsIn_zzOf (hF : FromPieces tl) (hm : MzFits tl) :
    DigitsIn tl (zzE tl mats C trits) := by
  obtain ⟨-, -, k0, k1, -, -⟩ := nums_Z hF
  intro q hq u _ c hc
  refine ⟨digitAt (parOfTail tl) (cellsAtOf C mats) trits.toArray u (q * tl.mz + c), ?_,
    map_natCast _ _⟩
  have hlt := VerifiableInference.Desc.First.K8.Honest.digitAt_lt (parOfTail tl)
    (cellsAtOf C mats) trits.toArray u (q * tl.mz + c)
  have hq' : q = 0 ∨ q = 1 := by omega
  rcases hq' with rfl | rfl
  · rw [k0]
    rw [if_pos (by rw [← hm]; omega)] at hlt
    exact hlt
  · rw [k1]
    rw [if_neg (by rw [← hm]; omega), OnBytes.Model.t2D1_eq] at hlt
    exact hlt

open Look in
/-- Under FromPieces tl, MzFits tl and Ch.Fits: ClaimsZero at the lookup on the digits, with the key
vectors kvZ of zzE and ν := nuZ of bzE: at every list, reader of cells and drawn matrix, for all
mask entries, jLK, θ and al. -/
theorem claimsZero_digits_zzOf (hF : FromPieces tl) (hm : MzFits tl) (jLK : ℕ)
    (mask : ℕ → Cb.Gl.E) (θ al : Cb.Gl.E) (Ch : Chal Cb.Gl.E) (hC : Ch.Fits tl.f9.v tl.f9.d 5) :
    ClaimsZero tl.f9 5 jLK (kvZ tl (zzE tl mats C trits)) θ al
      (nuZ tl (bzE tl mats C trits) mask) Ch :=
  claimsZero_digits hF (digitsIn_zzOf mats C trits hF hm) (laidBZ_digitsOf tl mats C trits) jLK _
    (fun _ _ _ _ => rfl) rfl θ al Ch hC

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.signedOf_cast
#print axioms OnBytes.HonestTrace.cellOf_int
#print axioms OnBytes.HonestTrace.cellsSmall_cellOf
#print axioms OnBytes.HonestTrace.cellsSmall_meetsAll
#print axioms OnBytes.HonestTrace.seg_of_lt
#print axioms OnBytes.HonestTrace.owner_entries
#print axioms OnBytes.HonestTrace.cellsAtOf_matsOf
#print axioms OnBytes.HonestTrace.matsOf_length
#print axioms OnBytes.HonestTrace.laidBZ_digitsOf
#print axioms OnBytes.HonestTrace.digitsIn_zzOf
#print axioms OnBytes.HonestTrace.claimsZero_digits_zzOf
