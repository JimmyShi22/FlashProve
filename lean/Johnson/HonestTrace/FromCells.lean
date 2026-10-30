-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/FromCells.lean

The keys and the planes' bits of the 25 lookups of the calls as functions of two readers, besides
what is public: a reader of cells by the sub-proof's number, the matrix's label, row and column, and
a reader of the committed matrix of weights by row and column.

The library's key vectors and bits (G.kvG, A.kvA, H.kvH, G.bitsG, A.bitsA, H.bitsH,
OnBytes/Tie/Pv/Lookup/Ends/) read names: a matrix's NUMBER in the sub-proof's list, row and column,
or a cell of the weights. This file makes readings of these names from cell : ℕ → String → ℕ → ℕ →
Cb.Gl.F and entry : ℕ → ℕ → Cb.Gl.F, and shows that at the readers cellOf X T
(Johnson/HonestTrace/Full.lean) and entryOf i (Johnson/HonestTrace/IndexReaders.lean) they are the
library's own readings of the lists T and the index i.

Main definitions: "labelAt X k a" (the label of matrix number a of sub-proof k: member a of
MatName.all, spelt by MatName.label, Johnson/HonestTrace/Names.lean; a part's label bears its number
also where the matrix lies in one part ("ad0", "as0"), and at "af", "ad", "as", "hf" cellOf X T is
0) · "atNo" (a cell by the matrix's number, carried into the extension field by algebraMap; 0 where
the number has no label) · "fromG", "fromA", "fromH" (the readings of the three kinds of names) ·
"nuFrom" (the reading of the places Fo.Pl of a lookup: the planes' cells by the label of matrix
number bNo X k, the mask entries from an argument, 0 elsewhere) · "PartsFit", "NamesFit" (the law's
premises).

Main theorems, under NamesFit X T:
* "atNo_cellOf": for k < 25, atNo at cellOf X T is T's entry, carried into the extension field.
* "fromG_cellOf", "fromA_cellOf", "fromH_cellOf": for g < 12, fromG at cellOf X T and entryOf i is
  cellMW (T (2 g)) i.mat; fromA at cellOf X T is cellZ (T (2 g + 1)); fromH is readH (T 24) i.mat:
  equations of functions, at every name.
* "midP_layers_cells", "midP_att_cells", "midP_head_cells": under LookPub, MeetsAll and PlanesLaid
  besides, Cb.Lkp.MidP holds with keys and bits read at fromG, fromA, fromH.
* "claimsZero_layers_cells", "claimsZero_att_cells", "claimsZero_head_cells": under the same,
  ClaimsZero (Johnson/HonestTrace/LookAtClaims.lean) holds with the key vectors read at fromG,
  fromA, fromH and ν := nuFrom, for all mask entries.

Limits. NamesFit, LookPub, MeetsAll and PlanesLaid are assumed, not proved, in this file (proved for
public files in the goals' scope, where they are read and publicOf returns:
Johnson/Goal/HonestTrace/FromCellsInScope.lean and FullPlanesInScope.lean; NamesFit at every T that
is 0 outside the plans' shapes, MeetsAll at the served trace theTrace). All is at 12
groups (25 sub-proofs) and the numbers of parts 3, 1, 1, 4, which are the full-size example's: there
no two names of one list have one label. At the small example's numbers (2 groups, hf in 1 part)
PartsFit fails. The types of the two readers are typed here; no file of another library is imported.
The lookups of the smallness tests' digits are not covered.

Not claimed: that a prover holds such readers; anything on a verifier.

-/
import Johnson.HonestTrace.IndexReaders
import Johnson.HonestTrace.LookAtClaims

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model
open OnBytes.Road
open OnBytes.Road.L5 (cellZ)
open OnBytes.Road.Alg (cellMW)
open OnBytes.Road.Hd (readH)
open OnBytes.Ends (NameA)

/-! ## Readers of the library's names from a reader by labels and a reader of the weights -/

/-- The label of matrix number a in the list of sub-proof k (2 g: group g; 2 g + 1: its attention
sub-proof; 24: the head), at X's numbers of parts; none from the list's length on and from k = 25
on. -/
def labelAt (X : Model.Verify.Public) (k a : ℕ) : Option String :=
  (Seg.ofNo 12 k).bind fun σ =>
    ((MatName.all (X.y.parts.getD 0 0) (X.y.parts.getD 1 0) (Hd.shapeA X (k / 2)).cf.NAs
      X.hS.NHf σ)[a]?).map MatName.label

/-- The cell (r, c) of matrix number a of sub-proof k, read by the matrix's label and carried into
the extension field; 0 where the number has no label. -/
def atNo (X : Model.Verify.Public) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F) (k a r c : ℕ) :
    Cb.Gl.E :=
  match labelAt X k a with
  | some s => algebraMap Cb.Gl.F Cb.Gl.E (cell k s r c)
  | none => 0

/-- The reading of a group's names (OnBytes/Tie/Pv/Lookup/Ends/G.lean) from the two readers. -/
def fromG (X : Model.Verify.Public) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F)
    (entry : ℕ → ℕ → Cb.Gl.F) (g : ℕ) : Ends.G.NameG → Cb.Gl.E
  | .cell a r c => atNo X cell (2 * g) a r c
  | .w r c => algebraMap Cb.Gl.F Cb.Gl.E (entry r c)

/-- The reading of an attention sub-proof's names (OnBytes/Tie/Pv/Lookup/Ends/A.lean). -/
def fromA (X : Model.Verify.Public) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F) (g : ℕ) :
    NameA → Cb.Gl.E := fun n => atNo X cell (2 * g + 1) n.M n.r n.c

/-- The reading of the head's names (OnBytes/Tie/Pv/Lookup/Ends/H.lean) from the two readers. -/
def fromH (X : Model.Verify.Public) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F)
    (entry : ℕ → ℕ → Cb.Gl.F) : Ends.H.NameH → Cb.Gl.E
  | .cell a r c => atNo X cell 24 a r c
  | .w r c => algebraMap Cb.Gl.F Cb.Gl.E (entry r c)

/-- The reading of the places Fo.Pl of the lookup of sub-proof k: the planes' cells by the label of
matrix number bNo X k; the mask entries from an argument; 0 at the other places. -/
def nuFrom (X : Model.Verify.Public) (cell : ℕ → String → ℕ → ℕ → Cb.Gl.F) (k : ℕ)
    (mask : ℕ → Cb.Gl.E) : _root_.Fo.Pl → Cb.Gl.E
  | .mask j => mask j
  | .cell r c => atNo X cell k (bNo X k) r c
  | .key _ _ => 0
  | .zero => 0

/-! ## The law: at cellOf X T and entryOf i these are the library's readers of T -/

/-- X's numbers of parts are 3 (af), 1 (ad), 1 (as, in every group below 12) and 4 (hf). -/
structure PartsFit (X : Model.Verify.Public) : Prop where
  af : X.y.parts.getD 0 0 = 3
  ad : X.y.parts.getD 1 0 = 1
  as : ∀ g < 12, (Hd.shapeA X g).cf.NAs = 1
  hf : X.hS.NHf = 4

/-- What the law asks of X and T: PartsFit X, and T is 0 at every number that has no label. -/
structure NamesFit (X : Model.Verify.Public) (T : Tr) : Prop where
  parts : PartsFit X
  beyond : ∀ k < 25, ∀ a r c, labelAt X k a = none → T k a r c = 0

variable {X : Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-- At the numbers of parts 3, 1, 1, 4: member number a of a segment's list of names has the number
a. -/
theorem all_no_ref (σ : Seg) {a : ℕ} {μ : MatName} (h : (MatName.all 3 1 1 4 σ)[a]? = some μ) :
    MatName.no? 3 1 1 4 σ μ = some a := by
  cases σ with
  | ff g =>
    have e : MatName.all 3 1 1 4 (.ff g) =
        [.af 0, .af 1, .af 2, .ad 0, .ar, .b, .qa, .xbO, .xbI] := rfl
    rw [e] at h
    have ha : a < 9 := by
      by_contra hn
      rw [List.getElem?_eq_none (by simpa using hn)] at h
      exact absurd h (by simp)
    interval_cases a <;> simp at h <;> subst h <;> rfl
  | att g =>
    have e : MatName.all 3 1 1 4 (.att g) = [.as 0, .ah, .ao, .bA, .qa] := rfl
    rw [e] at h
    have ha : a < 5 := by
      by_contra hn
      rw [List.getElem?_eq_none (by simpa using hn)] at h
      exact absurd h (by simp)
    interval_cases a <;> simp at h <;> subst h <;> rfl
  | head =>
    have e : MatName.all 3 1 1 4 .head = [.hf 0, .hf 1, .hf 2, .hf 3, .hd, .hr, .bH, .xbL] := rfl
    rw [e] at h
    have ha : a < 8 := by
      by_contra hn
      rw [List.getElem?_eq_none (by simpa using hn)] at h
      exact absurd h (by simp)
    interval_cases a <;> simp at h <;> subst h <;> rfl

/-- Under PartsFit, at a segment with the number k: the list of names, the numbers and the search by
a label at X's numbers of parts are those at 3, 1, 1, 4. -/
theorem parts_at (N : PartsFit X) {k : ℕ} {σ : Seg} (hσ : Seg.ofNo 12 k = some σ) :
    MatName.all (X.y.parts.getD 0 0) (X.y.parts.getD 1 0) (Hd.shapeA X (k / 2)).cf.NAs X.hS.NHf σ =
        MatName.all 3 1 1 4 σ ∧
      (∀ μ, MatName.no? (X.y.parts.getD 0 0) (X.y.parts.getD 1 0) (Hd.shapeA X (k / 2)).cf.NAs
        X.hS.NHf σ μ = MatName.no? 3 1 1 4 σ μ) ∧
      ∀ s, MatName.ofLabel? (X.y.parts.getD 0 0) (X.y.parts.getD 1 0)
        (Hd.shapeA X (k / 2)).cf.NAs X.hS.NHf σ s = MatName.ofLabel? 3 1 1 4 σ s := by
  obtain ⟨hb, hk⟩ := Seg.of_ofNo hσ
  rw [N.af, N.ad, N.hf]
  cases σ with
  | ff g => exact ⟨rfl, fun μ => by cases μ <;> rfl, fun _ => rfl⟩
  | att g =>
    have hg : g < 12 := hb
    have e : k / 2 = g := by
      have : 2 * g + 1 = k := hk
      omega
    rw [e, N.as g hg]
    exact ⟨rfl, fun _ => rfl, fun _ => rfl⟩
  | head => exact ⟨rfl, fun μ => by cases μ <;> rfl, fun _ => rfl⟩

/-- Under NamesFit, for k < 25: atNo at the reader cellOf X T is the entry of T at sub-proof k,
matrix number a, row r and column c, carried into the extension field. -/
theorem atNo_cellOf (N : NamesFit X T) {k : ℕ} (hk : k < 25) (a r c : ℕ) :
    atNo X (cellOf X T) k a r c = ((T k a r c : ℤ) : Cb.Gl.E) := by
  unfold atNo
  cases hl : labelAt X k a with
  | none =>
    rw [N.beyond k hk a r c hl]
    simp
  | some s =>
    unfold labelAt at hl
    cases hσ : Seg.ofNo 12 k with
    | none =>
      rw [hσ] at hl
      exact absurd hl (by simp)
    | some σ =>
      obtain ⟨p1, p2, p3⟩ := parts_at N.parts hσ
      obtain ⟨-, hno⟩ := Seg.of_ofNo hσ
      rw [hσ] at hl
      simp only [Option.bind_some, p1] at hl
      cases hμ : (MatName.all 3 1 1 4 σ)[a]? with
      | none =>
        rw [hμ] at hl
        exact absurd hl (by simp)
      | some μ =>
        rw [hμ] at hl
        obtain rfl : μ.label = s := by simpa using hl
        have hn := all_no_ref σ hμ
        have hf := MatName.ofLabel?_label_ref σ μ (List.mem_of_getElem? hμ)
        have hby : byName X T σ μ r c = T k a r c := by
          unfold byName noAt
          rw [hno, if_pos hσ, p2 μ, hn]
        show algebraMap Cb.Gl.F Cb.Gl.E (cellOf X T k μ.label r c) = _
        unfold cellOf
        rw [hσ]
        simp only [p3, hf, hby]
        exact map_intCast _ _

/-- Under NamesFit, for g < 12: fromG at the readers cellOf X T and entryOf i is the library's
reading cellMW of the list T (2 g) and the index's matrix, at every name. -/
theorem fromG_cellOf (N : NamesFit X T) (i : Cm.Idx) {g : ℕ} (hg : g < 12) :
    fromG X (cellOf X T) (entryOf i) g = cellMW (T (2 * g)) i.mat := by
  funext n
  cases n with
  | cell a r c => exact atNo_cellOf N (by omega) a r c
  | w r c => exact map_intCast _ _

/-- Under NamesFit, for g < 12: fromA at the reader cellOf X T is the library's reading cellZ of the
list T (2 g + 1), at every name. -/
theorem fromA_cellOf (N : NamesFit X T) {g : ℕ} (hg : g < 12) :
    fromA X (cellOf X T) g = (cellZ (T (2 * g + 1)) : NameA → Cb.Gl.E) := by
  funext n
  exact atNo_cellOf N (by omega) n.M n.r n.c

/-- Under NamesFit: fromH at the readers cellOf X T and entryOf i is the library's reading readH of
the list T 24 and the index's matrix, at every name. -/
theorem fromH_cellOf (N : NamesFit X T) (i : Cm.Idx) :
    fromH X (cellOf X T) (entryOf i) = readH (T 24) i.mat := by
  funext n
  cases n with
  | cell a r c => exact atNo_cellOf N (by omega) a r c
  | w r c => exact map_intCast _ _

/-! ## The relation after the challenge, and the lookup's claims, at these terms -/

/-- Under NamesFit, LookPub, MeetsAll and PlanesLaid, for g < 12 and all θ and al: Cb.Lkp.MidP holds
of the joint key vector, the joint table, the public padding and the planes' bits of group g, keys
and bits read at fromG X (cellOf X T) (entryOf i) g. -/
theorem midP_layers_cells (N : NamesFit X T) (Q : LookPub X) (M : MeetsAll X i x T)
    (L : PlanesLaid X i x T) {g : ℕ} (hg : g < 12) (θ al : Cb.Gl.E) :
    Cb.Lkp.MidP X.y.fo.v X.y.fo.d 5 32
      (Ends.G.keyG X.layers g (fromG X (cellOf X T) (entryOf i) g) θ) (Ends.G.tabG X.layers θ)
      (FoNums.pads X.y.fo)
      (fun u j => Ends.G.bitsG X.y (fromG X (cellOf X T) (entryOf i) g) (u * 32 + j)) al := by
  rw [fromG_cellOf N i hg]
  exact midP_layers Q M L hg θ al

/-- The same at the attention sub-proof of group g, keys and bits read at fromA X (cellOf X T) g. -/
theorem midP_att_cells (N : NamesFit X T) (Q : LookPub X) (M : MeetsAll X i x T)
    (L : PlanesLaid X i x T) {g : ℕ} (hg : g < 12) (θ al : Cb.Gl.E) :
    Cb.Lkp.MidP (fsAt X g).v (fsAt X g).d 5 32
      (Ends.A.keyA (Hd.shapeA X g) (fsAt X g) (fromA X (cellOf X T) g) θ)
      (Ends.A.tabA (fsAt X g) θ) (FoNums.pads (fsAt X g))
      (fun u j => Ends.A.bitsA (Hd.shapeA X g) (fsAt X g) (fromA X (cellOf X T) g) (u * 32 + j))
      al := by
  rw [fromA_cellOf N hg]
  exact midP_att Q M L hg θ al

/-- The same at the head, keys and bits read at fromH X (cellOf X T) (entryOf i). -/
theorem midP_head_cells (N : NamesFit X T) (Q : LookPub X) (M : MeetsAll X i x T)
    (L : PlanesLaid X i x T) (θ al : Cb.Gl.E) :
    Cb.Lkp.MidP X.HLy.fs.v X.HLy.fs.d 5 32
      (Ends.H.keyH (pubHAt X x) (fromH X (cellOf X T) (entryOf i)) θ)
      (Ends.H.tabH (pubHAt X x) θ) (FoNums.pads X.HLy.fs)
      (fun u j => Ends.H.bitsH X.hS X.HLy.fs (fromH X (cellOf X T) (entryOf i)) (u * 32 + j))
      al := by
  rw [fromH_cellOf N i]
  exact midP_head Q M L θ al

open Look in
/-- Under NamesFit, LookPub, MeetsAll and PlanesLaid, for g < 12: for all mask entries, all jLK and
al, every θ that is 0 where the shape has one call, and all challenges C with C.Fits: ClaimsZero
holds at the lookup of the calls of group g, with the key vectors read at
fromG X (cellOf X T) (entryOf i) g and ν := nuFrom X (cellOf X T) (2 g) mask. -/
theorem claimsZero_layers_cells (N : NamesFit X T) (Q : LookPub X) (M : MeetsAll X i x T)
    (L : PlanesLaid X i x T) {g : ℕ} (hg : g < 12) (jLK : ℕ) (mask : ℕ → Cb.Gl.E)
    (θ al : Cb.Gl.E) (h1 : FoNums.several X.y.fo = false → θ = 0) (C : Chal Cb.Gl.E)
    (hC : C.Fits X.y.fo.v X.y.fo.d 5) :
    ClaimsZero X.y.fo X.y.h.lmb jLK
      (Ends.G.kvG X.layers g (fromG X (cellOf X T) (entryOf i) g)) θ al
      (nuFrom X (cellOf X T) (2 * g) mask) C := by
  rw [fromG_cellOf N i hg]
  refine claimsZero_layers Q M L hg jLK _ (fun r _ c _ => ?_) rfl θ al h1 C hC
  show atNo X (cellOf X T) (2 * g) (bNo X (2 * g)) r c = _
  rw [atNo_cellOf N (by omega), bNoL X hg]
  rfl

open Look in
/-- The same at the attention sub-proof of group g, with the key vectors read at
fromA X (cellOf X T) g and ν := nuFrom X (cellOf X T) (2 g + 1) mask. -/
theorem claimsZero_att_cells (N : NamesFit X T) (Q : LookPub X) (M : MeetsAll X i x T)
    (L : PlanesLaid X i x T) {g : ℕ} (hg : g < 12) (jLK : ℕ) (mask : ℕ → Cb.Gl.E)
    (θ al : Cb.Gl.E) (h1 : FoNums.several (fsAt X g) = false → θ = 0) (C : Chal Cb.Gl.E)
    (hC : C.Fits (fsAt X g).v (fsAt X g).d 5) :
    ClaimsZero (fsAt X g) (Hd.shapeA X g).cf.lmb jLK
      (Ends.A.kvA (Hd.shapeA X g) (fsAt X g) (fromA X (cellOf X T) g)) θ al
      (nuFrom X (cellOf X T) (2 * g + 1) mask) C := by
  rw [fromA_cellOf N hg]
  refine claimsZero_att Q M L hg jLK _ (fun r _ c _ => ?_) rfl θ al h1 C hC
  show atNo X (cellOf X T) (2 * g + 1) (bNo X (2 * g + 1)) r c = _
  rw [atNo_cellOf N (by omega), bNo_odd]
  rfl

open Look in
/-- The same at the head, with the key vectors read at fromH X (cellOf X T) (entryOf i) and
ν := nuFrom X (cellOf X T) 24 mask. -/
theorem claimsZero_head_cells (N : NamesFit X T) (Q : LookPub X) (M : MeetsAll X i x T)
    (L : PlanesLaid X i x T) (jLK : ℕ) (mask : ℕ → Cb.Gl.E) (θ al : Cb.Gl.E)
    (h1 : FoNums.several X.HLy.fs = false → θ = 0) (C : Chal Cb.Gl.E)
    (hC : C.Fits X.HLy.fs.v X.HLy.fs.d 5) :
    ClaimsZero X.HLy.fs X.hS.lmbH jLK
      (Ends.H.kvH (pubHAt X x) (fromH X (cellOf X T) (entryOf i))) θ al
      (nuFrom X (cellOf X T) 24 mask) C := by
  rw [fromH_cellOf N i]
  refine claimsZero_head Q M L jLK _ (fun r _ c _ => ?_) rfl θ al h1 C hC
  show atNo X (cellOf X T) 24 (bNo X 24) r c = _
  rw [atNo_cellOf N (by omega), bNo_head]
  rfl

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.all_no_ref
#print axioms OnBytes.HonestTrace.parts_at
#print axioms OnBytes.HonestTrace.atNo_cellOf
#print axioms OnBytes.HonestTrace.fromG_cellOf
#print axioms OnBytes.HonestTrace.fromA_cellOf
#print axioms OnBytes.HonestTrace.fromH_cellOf
#print axioms OnBytes.HonestTrace.midP_layers_cells
#print axioms OnBytes.HonestTrace.midP_att_cells
#print axioms OnBytes.HonestTrace.midP_head_cells
#print axioms OnBytes.HonestTrace.claimsZero_layers_cells
#print axioms OnBytes.HonestTrace.claimsZero_att_cells
#print axioms OnBytes.HonestTrace.claimsZero_head_cells
