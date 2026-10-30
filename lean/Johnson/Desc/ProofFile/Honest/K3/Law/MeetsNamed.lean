-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/MeetsNamed.lean: the honest side of the kind "lookup" (K3): the
two witnesses of "keys and bits are honest", by name. Theorems, and one definition (`nuZm`).

Terms. Honest/K3/GLOSSARY.md: see there owner and borrowed matrix, seated filling, sources, keys and
bits are honest, trace's bundles, cells and full size. In this file: `LookIn.Meets h lm`
(Honest/K3/WitLaw.lean) says that there are key vectors kv and a reading nu of the verifier's places
with which a structure's keys are the joint vector and its bits are what nu reads at the bits'
places. Whoever needs the two themselves finds them here, at the keys and bits of the four sorts of
lookup (Honest/K3/WitFill.lean), and at the filling that reads a borrowed matrix under its owner's
segment and name (Honest/K3/WitOwner.lean).

What is shown.
  `lookG_key`, `lookA_key`, `lookH_key`, `lookZ_key`: the keys are the joint vector of the named key
    vectors: by the structures' own text.
  `lookG_bit`, `lookA_bit`, `lookH_bit`: at every reader of cells, all mask entries, u < 2 ^ d and j
    < 32: the bit is what `nuFrom` (Johnson/HonestTrace/FromCells.lean) reads at the bit's place.
  `nuZm`, `lookZ_bit`: the like on the digits; conditional on `Fo.ZPlan.FromPieces tl`.
    `nuZm tl zz mask` writes out, arm for arm, `OnBytes.HonestTrace.nuZ tl (bzIn tl zz) mask`
    (Johnson/HonestTrace/DigitsAtTrace.lean); the tie: `nuZm_eq`
    (Honest/K3/Law/TiesTrace.lean [not in this library]). `nuZ` of Honest/K3/WitFill.lean is a third
    reading of that sort, with 0 at the mask entries.
  `ownLayers_eq`, `ownAttention_eq`, `ownHead_eq`, `ownDigits_eq`: at the trace's own readers the
    filling's four fields are these structures; the first three conditionally.
  `ownG_key`, `ownG_bit`, `ownA_key`, `ownA_bit`, `ownH_key`, `ownH_bit`: so the same at the
    filling's own terms.
The reading is general in the mask row: a bit's place is never a mask entry's place, so the equation
on the bits holds with every function in the mask entries' stead.

Hypotheses that remain.
  `hg`: g < 12 (in `lookG_bit` and at the filling's own terms; `lookA_bit` asks nothing of g).
  `hu`, `hj`: the row is below 2 ^ d; the plane is below 32.
  `hh`, `hL`: (at the head) the shape and the layout of the public data are the public part's.
  `hF`: (in `lookZ_bit`) `Fo.ZPlan.FromPieces tl`: public.
  `B`, `O`, `N`, `M`: (at the filling's own terms) the hypotheses of the equations of
    Honest/K3/Law/WitOwnerFull.lean: `PlanLabels X`, `PlanOwners X`, `NamesFit X T`,
    `MeetsAll X i x T`.

Imported. Honest/K3/WitDigits.lean, which lies beneath this file, imports
Johnson/HonestTrace/DigitsAtTrace.lean.

Users. Honest/K3/Law/Thread/ExchangeFillAt.lean
calls `ownLayers_eq`, `ownAttention_eq`, `ownHead_eq`, the four theorems on keys (`lookG_key`,
`lookA_key`, `lookH_key`, `lookZ_key`) and the four on bits (`lookG_bit`, `lookA_bit`, `lookH_bit`,
`lookZ_bit`).

Limits. `lookG_bit` asks g < 12; it and `lookA_bit` go by the written numbers of FromCells.lean: the
full size alone. `lookH_bit` and `ownH_bit` go by a written number too: link 24, the head's at the
full size. Written besides: 32 planes throughout; 5 for lm in `lookZ_bit`. No instance of these
hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.WitOwnerFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3
open OnBytes.HonestTrace (fromG fromA fromH nuFrom fsAt pubHAt cellOf entryOf atNo kvZ virtZ
  NamesFit
  MeetsAll Tr)
open OnBytes.Road (Hd.shapeA)
open Inst.Model (Instance ppref)

/-! ## 1 The keys -/

theorem lookG_key (X : OnBytes.Model.Verify.Public) (g : ℕ) (C : Cells) (W : Weights)
    (theta : Cb.Gl.E) (n : ℕ) :
    (lookG X g C W).key theta n =
      OnBytes.Ends.jointKey X.y.fo (OnBytes.Ends.G.kvG X.layers g (fromG X C.cell W.entry g)) theta
        n :=
  rfl

theorem lookA_key (X : OnBytes.Model.Verify.Public) (g : ℕ) (C : Cells) (theta : Cb.Gl.E) (n : ℕ) :
    (lookA X g C).key theta n =
      OnBytes.Ends.jointKey (fsAt X g)
        (OnBytes.Ends.A.kvA (Hd.shapeA X g) (fsAt X g) (fromA X C.cell g)) theta n := rfl

theorem lookH_key (X : OnBytes.Model.Verify.Public) (P : OnBytes.Ends.H.PubH) (C : Cells)
    (W : Weights)
    (theta : Cb.Gl.E) (n : ℕ) :
    (lookH X P C W).key theta n =
      OnBytes.Ends.jointKey P.L.fs (OnBytes.Ends.H.kvH P (fromH X C.cell W.entry)) theta n := rfl

theorem lookZ_key (tl : OnBytes.Model.HTailF2) (zz : ℕ → ℕ → Cb.Gl.F) (theta : Cb.Gl.E) (n : ℕ) :
    (lookZ tl zz).key theta n = OnBytes.Ends.jointKey tl.f9 (kvZ tl (inExt zz)) theta n := rfl

/-! ## 2 The bits, general in the mask row -/

/-- A group's layers: at every reader of cells and of weights and all mask entries; g < 12. -/
theorem lookG_bit (X : OnBytes.Model.Verify.Public) {g : ℕ} (hg : g < 12) (C : Cells) (W : Weights)
    (mask : ℕ → Cb.Gl.E) (theta : Cb.Gl.E) (jLK : ℕ) {u j : ℕ} (hu : u < 2 ^ X.y.fo.d)
    (hj : j < 32) :
    (lookG X g C W).bit u j =
      nuFrom X C.cell (2 * g) mask ((_root_.Fo.numsF X.y.fo X.y.h.lmb jLK theta).bAt u j) := by
  obtain ⟨e1, e2⟩ := split32 u hj
  show (match OnBytes.Ends.G.placeG X.y ((u * 32 + j) / 32) ((u * 32 + j) % 32) with
    | some n => fromG X C.cell W.entry g n
    | none => 0) = nuFrom X C.cell (2 * g) mask
      (match FoNums.cellOf X.y.fo u j with
        | some y => .cell (FoNums.cellRC X.y.fo X.y.h.lmb y).1 (FoNums.cellRC X.y.fo X.y.h.lmb y).2
        | none => .zero)
  rw [e1, e2]
  unfold OnBytes.Ends.G.placeG FoNums.cellOf
  by_cases hc : u % 2 ^ X.y.fo.cK < X.y.fo.NC
  · rw [if_pos ⟨hc, hj, hu⟩, if_pos hc]
    show atNo X C.cell (2 * g) (OnBytes.Ends.G.iB X.y) _ _ =
      atNo X C.cell (2 * g) (OnBytes.HonestTrace.bNo X (2 * g)) _ _
    rw [OnBytes.HonestTrace.bNoL X hg]
    rfl
  · rw [if_neg (fun h => hc h.1), if_neg hc]
    rfl

/-- A group's attention: at every reader of cells and all mask entries. -/
theorem lookA_bit (X : OnBytes.Model.Verify.Public) (g : ℕ) (C : Cells) (mask : ℕ → Cb.Gl.E)
    (theta : Cb.Gl.E) (jLK : ℕ) {u j : ℕ} (hu : u < 2 ^ (fsAt X g).d) (hj : j < 32) :
    (lookA X g C).bit u j =
      nuFrom X C.cell (2 * g + 1) mask
        ((_root_.Fo.numsF (fsAt X g) (Hd.shapeA X g).cf.lmb jLK theta).bAt u j) := by
  obtain ⟨e1, e2⟩ := split32 u hj
  show (match OnBytes.Ends.A.placeBA (Hd.shapeA X g) (fsAt X g) ((u * 32 + j) / 32)
      ((u * 32 + j) % 32) with
    | some n => fromA X C.cell g n
    | none => 0) = nuFrom X C.cell (2 * g + 1) mask
      (match FoNums.cellOf (fsAt X g) u j with
        | some y => .cell (FoNums.cellRC (fsAt X g) (Hd.shapeA X g).cf.lmb y).1
            (FoNums.cellRC (fsAt X g) (Hd.shapeA X g).cf.lmb y).2
        | none => .zero)
  rw [e1, e2]
  unfold OnBytes.Ends.A.placeBA FoNums.cellOf
  by_cases hc : u % 2 ^ (fsAt X g).cK < (fsAt X g).NC
  · rw [if_pos ⟨hc, hj, hu⟩, if_pos hc]
    show atNo X C.cell (2 * g + 1) ((Hd.shapeA X g).cf.NAs + 2) _ _ =
      atNo X C.cell (2 * g + 1) (OnBytes.HonestTrace.bNo X (2 * g + 1)) _ _
    rw [OnBytes.HonestTrace.bNo_odd]
    rfl
  · rw [if_neg (fun h => hc h.1), if_neg hc]
    rfl

/-- The head, at public data whose shape and layout are the public part's: at every reader and all
mask entries. -/
theorem lookH_bit (X : OnBytes.Model.Verify.Public) (P : OnBytes.Ends.H.PubH) (hh : P.h = X.hS)
    (hL : P.L = X.HLy) (C : Cells) (W : Weights) (mask : ℕ → Cb.Gl.E) (theta : Cb.Gl.E) (jLK : ℕ)
    {u j : ℕ} (hu : u < 2 ^ X.HLy.fs.d) (hj : j < 32) :
    (lookH X P C W).bit u j =
      nuFrom X C.cell 24 mask ((_root_.Fo.numsF X.HLy.fs X.hS.lmbH jLK theta).bAt u j) := by
  obtain ⟨e1, e2⟩ := split32 u hj
  show (match OnBytes.Ends.H.placeH P.h P.L.fs ((u * 32 + j) / 32) ((u * 32 + j) % 32) with
    | some n => fromH X C.cell W.entry n
    | none => 0) = nuFrom X C.cell 24 mask
      (match FoNums.cellOf X.HLy.fs u j with
        | some y => .cell (FoNums.cellRC X.HLy.fs X.hS.lmbH y).1
            (FoNums.cellRC X.HLy.fs X.hS.lmbH y).2
        | none => .zero)
  rw [e1, e2, hh, hL]
  unfold OnBytes.Ends.H.placeH FoNums.cellOf
  by_cases hc : u % 2 ^ X.HLy.fs.cK < X.HLy.fs.NC
  · rw [if_pos ⟨hc, hj, hu⟩, if_pos hc]
    show atNo X C.cell 24 (X.hS.NHf + 2) _ _ =
      atNo X C.cell 24 (OnBytes.HonestTrace.bNo X 24) _ _
    rw [OnBytes.HonestTrace.bNo_head]
    rfl
  · rw [if_neg (fun h => hc h.1), if_neg hc]
    rfl

/-- The reading of the verifier's places at the digits, with a mask row: the planes' cells out of
BZ, read as the matrix with one row a plane; the mask entries from the argument; 0 elsewhere. It is
`OnBytes.HonestTrace.nuZ` at `bzIn tl zz` (`nuZm_eq`, Honest/K3/Law/TiesTrace.lean
[not in this library]). -/
def nuZm (tl : OnBytes.Model.HTailF2) (zz : ℕ → ℕ → Cb.Gl.F) (mask : ℕ → Cb.Gl.E) :
    _root_.Fo.Pl → Cb.Gl.E
  | .mask j => mask j
  | .cell r c => virtZ tl (bzIn tl zz) r c
  | .key _ _ => 0
  | .zero => 0

/-- The digits: at every array ZZ and all mask entries. Conditional on `Fo.ZPlan.FromPieces tl`
(public). No instance of these hypotheses is exhibited in this file. -/
theorem lookZ_bit {tl : OnBytes.Model.HTailF2} (hF : Fo.ZPlan.FromPieces tl) (zz : ℕ → ℕ → Cb.Gl.F)
    (mask : ℕ → Cb.Gl.E) (theta : Cb.Gl.E) (jLK : ℕ) {u j : ℕ} (hu : u < 2 ^ tl.f9.d)
    (hj : j < 32) :
    (lookZ tl zz).bit u j = nuZm tl zz mask ((_root_.Fo.numsF tl.f9 5 jLK theta).bAt u j) := by
  have hb : OnBytes.HonestTrace.LaidBZ tl (inExt zz) (bzIn tl zz) := fun _ _ _ _ => rfl
  exact (OnBytes.HonestTrace.bz_plane hb hu hj).trans
    (OnBytes.HonestTrace.Look.bAt_plane tl.f9 5 jLK theta
      (OnBytes.HonestTrace.hitsZ tl (inExt zz)) (le_refl 5) (Nat.le_add_left 5 _) (nuZm tl zz mask)
      (fun r hr c hc => OnBytes.HonestTrace.virtZ_plane hF hb r hr c hc) rfl hu hj).symm

/-! ## 3 At the filling's own terms -/

section
variable {X : OnBytes.Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {T : Tr}
variable {W₀ Xi Tr' : Type}

/-- Conditional on `PlanLabels X`, `PlanOwners X`, `NamesFit X T`, `MeetsAll X i x T`, g < 12.
No instance of these hypotheses is exhibited in this file. -/
theorem ownLayers_eq (B : PlanLabels X) (O : PlanOwners X) (N : NamesFit X T) (M : MeetsAll X i x T)
    {g : ℕ} (hg : g < 12) (cells : Tr' → Cells) (weights : W₀ → Weights)
    (pubH : Xi → OnBytes.Ends.H.PubH) :
    (ownSources X cells weights pubH).layers g ⟨cellOf X T⟩ ⟨entryOf i⟩ =
      lookG X g ⟨cellOf X T⟩ ⟨entryOf i⟩ := by
  show (⟨fun theta n => OnBytes.Ends.G.keyG X.layers g
      (ownG X (cellOf X T) (entryOf i) (linkG X g)) theta n,
    fun u j => OnBytes.Ends.G.bitsG X.y (ownG X (cellOf X T) (entryOf i) (linkG X g))
      (u * 32 + j)⟩ : LookIn) = _
  rw [ownG_eq B O N M hg]
  rfl

/-- Conditional on the same. No instance of these hypotheses is exhibited in this file. -/
theorem ownAttention_eq (B : PlanLabels X) (O : PlanOwners X) (N : NamesFit X T)
    (M : MeetsAll X i x T) {g : ℕ} (hg : g < 12) (cells : Tr' → Cells) (weights : W₀ → Weights)
    (pubH : Xi → OnBytes.Ends.H.PubH) :
    (ownSources X cells weights pubH).attention g ⟨cellOf X T⟩ = lookA X g ⟨cellOf X T⟩ := by
  show (⟨fun theta n => OnBytes.Ends.A.keyA (Hd.shapeA X g) (fsAt X g)
      (ownA X (cellOf X T) (linkA X g)) theta n,
    fun u j => OnBytes.Ends.A.bitsA (Hd.shapeA X g) (fsAt X g) (ownA X (cellOf X T) (linkA X g))
      (u * 32 + j)⟩ : LookIn) = _
  rw [ownA_eq B O N M hg]
  rfl

/-- Conditional on the same. No instance of these hypotheses is exhibited in this file. -/
theorem ownHead_eq (B : PlanLabels X) (O : PlanOwners X) (N : NamesFit X T) (M : MeetsAll X i x T)
    (cells : Tr' → Cells) (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH) (y : Xi) :
    (ownSources X cells weights pubH).head y ⟨cellOf X T⟩ ⟨entryOf i⟩ =
      lookH X (pubH y) ⟨cellOf X T⟩ ⟨entryOf i⟩ := by
  show (⟨fun theta n => OnBytes.Ends.H.keyH (pubH y)
      (ownH X (cellOf X T) (entryOf i) (linkH X)) theta n,
    fun u j => OnBytes.Ends.H.bitsH (pubH y).h (pubH y).L.fs
      (ownH X (cellOf X T) (entryOf i) (linkH X)) (u * 32 + j)⟩ : LookIn) = _
  rw [ownH_eq B O N M]
  rfl

/-- The digits' field is lookZ at the link's structure and zzOwn: by the filling's own text, at
every public part, reader and sampled matrix. -/
theorem ownDigits_eq (X : OnBytes.Model.Verify.Public) (cells : Tr' → Cells)
    (weights : W₀ → Weights)
    (pubH : Xi → OnBytes.Ends.H.PubH) (link : ℕ) (C : Cells) (ts : List Int) :
    (ownSources X cells weights pubH).digits link C ts = lookZ (tlOf X link) (zzOwn X link C ts) :=
      rfl

/-- Conditional on `PlanLabels X`, `PlanOwners X`, `NamesFit X T`, `MeetsAll X i x T`, g < 12.
No instance of these hypotheses is exhibited in this file. -/
theorem ownG_key (B : PlanLabels X) (O : PlanOwners X) (N : NamesFit X T) (M : MeetsAll X i x T)
    {g : ℕ} (hg : g < 12) (cells : Tr' → Cells) (weights : W₀ → Weights)
    (pubH : Xi → OnBytes.Ends.H.PubH) (theta : Cb.Gl.E) (n : ℕ) :
    ((ownSources X cells weights pubH).layers g ⟨cellOf X T⟩ ⟨entryOf i⟩).key theta n =
      OnBytes.Ends.jointKey X.y.fo
        (OnBytes.Ends.G.kvG X.layers g (fromG X (cellOf X T) (entryOf i) g)) theta n := by
  rw [ownLayers_eq B O N M hg]
  rfl

/-- Conditional on the same; all mask entries. No instance of these hypotheses is exhibited in this
file. -/
theorem ownG_bit (B : PlanLabels X) (O : PlanOwners X) (N : NamesFit X T) (M : MeetsAll X i x T)
    {g : ℕ} (hg : g < 12) (cells : Tr' → Cells) (weights : W₀ → Weights)
    (pubH : Xi → OnBytes.Ends.H.PubH) (mask : ℕ → Cb.Gl.E) (theta : Cb.Gl.E) (jLK : ℕ) {u j : ℕ}
    (hu : u < 2 ^ X.y.fo.d) (hj : j < 32) :
    ((ownSources X cells weights pubH).layers g ⟨cellOf X T⟩ ⟨entryOf i⟩).bit u j =
      nuFrom X (cellOf X T) (2 * g) mask
        ((_root_.Fo.numsF X.y.fo X.y.h.lmb jLK theta).bAt u j) := by
  rw [ownLayers_eq B O N M hg]
  exact lookG_bit X hg ⟨cellOf X T⟩ ⟨entryOf i⟩ mask theta jLK hu hj

/-- Conditional on the same. No instance of these hypotheses is exhibited in this file. -/
theorem ownA_key (B : PlanLabels X) (O : PlanOwners X) (N : NamesFit X T) (M : MeetsAll X i x T)
    {g : ℕ} (hg : g < 12) (cells : Tr' → Cells) (weights : W₀ → Weights)
    (pubH : Xi → OnBytes.Ends.H.PubH) (theta : Cb.Gl.E) (n : ℕ) :
    ((ownSources X cells weights pubH).attention g ⟨cellOf X T⟩).key theta n =
      OnBytes.Ends.jointKey (fsAt X g)
        (OnBytes.Ends.A.kvA (Hd.shapeA X g) (fsAt X g) (fromA X (cellOf X T) g)) theta n := by
  rw [ownAttention_eq B O N M hg]
  rfl

/-- Conditional on the same; all mask entries. No instance of these hypotheses is exhibited in this
file. -/
theorem ownA_bit (B : PlanLabels X) (O : PlanOwners X) (N : NamesFit X T) (M : MeetsAll X i x T)
    {g : ℕ} (hg : g < 12) (cells : Tr' → Cells) (weights : W₀ → Weights)
    (pubH : Xi → OnBytes.Ends.H.PubH) (mask : ℕ → Cb.Gl.E) (theta : Cb.Gl.E) (jLK : ℕ) {u j : ℕ}
    (hu : u < 2 ^ (fsAt X g).d) (hj : j < 32) :
    ((ownSources X cells weights pubH).attention g ⟨cellOf X T⟩).bit u j =
      nuFrom X (cellOf X T) (2 * g + 1) mask
        ((_root_.Fo.numsF (fsAt X g) (Hd.shapeA X g).cf.lmb jLK theta).bAt u j) := by
  rw [ownAttention_eq B O N M hg]
  exact lookA_bit X g ⟨cellOf X T⟩ mask theta jLK hu hj

/-- Conditional on the same. No instance of these hypotheses is exhibited in this file. -/
theorem ownH_key (B : PlanLabels X) (O : PlanOwners X) (N : NamesFit X T) (M : MeetsAll X i x T)
    (cells : Tr' → Cells) (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH) (y : Xi)
    (theta : Cb.Gl.E) (n : ℕ) :
    ((ownSources X cells weights pubH).head y ⟨cellOf X T⟩ ⟨entryOf i⟩).key theta n =
      OnBytes.Ends.jointKey (pubH y).L.fs
        (OnBytes.Ends.H.kvH (pubH y) (fromH X (cellOf X T) (entryOf i))) theta n := by
  rw [ownHead_eq B O N M]
  rfl

/-- Conditional on the same, and on the letter's shape and layout being the public part's (those of
`headPub` are, by `rfl`); all mask entries. No instance of these hypotheses is exhibited in this
file. -/
theorem ownH_bit (B : PlanLabels X) (O : PlanOwners X) (N : NamesFit X T) (M : MeetsAll X i x T)
    (cells : Tr' → Cells) (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH) (y : Xi)
    (hh : (pubH y).h = X.hS) (hL : (pubH y).L = X.HLy) (mask : ℕ → Cb.Gl.E) (theta : Cb.Gl.E)
    (jLK : ℕ) {u j : ℕ} (hu : u < 2 ^ X.HLy.fs.d) (hj : j < 32) :
    ((ownSources X cells weights pubH).head y ⟨cellOf X T⟩ ⟨entryOf i⟩).bit u j =
      nuFrom X (cellOf X T) 24 mask ((_root_.Fo.numsF X.HLy.fs X.hS.lmbH jLK theta).bAt u j) := by
  rw [ownHead_eq B O N M]
  exact lookH_bit X (pubH y) hh hL ⟨cellOf X T⟩ ⟨entryOf i⟩ mask theta jLK hu hj

end

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.lookG_key
#print axioms ProofFile.Honest.K3.lookA_key
#print axioms ProofFile.Honest.K3.lookH_key
#print axioms ProofFile.Honest.K3.lookZ_key
#print axioms ProofFile.Honest.K3.lookG_bit
#print axioms ProofFile.Honest.K3.lookA_bit
#print axioms ProofFile.Honest.K3.lookH_bit
#print axioms ProofFile.Honest.K3.lookZ_bit
#print axioms ProofFile.Honest.K3.ownLayers_eq
#print axioms ProofFile.Honest.K3.ownAttention_eq
#print axioms ProofFile.Honest.K3.ownHead_eq
#print axioms ProofFile.Honest.K3.ownDigits_eq
#print axioms ProofFile.Honest.K3.ownG_key
#print axioms ProofFile.Honest.K3.ownG_bit
#print axioms ProofFile.Honest.K3.ownA_key
#print axioms ProofFile.Honest.K3.ownA_bit
#print axioms ProofFile.Honest.K3.ownH_key
#print axioms ProofFile.Honest.K3.ownH_bit
