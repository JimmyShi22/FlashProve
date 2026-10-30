-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/WitFill.lean: the honest side of the kind "lookup" (K3): the
filling of the letters `Sources` (Honest/K3/Wit.lean), at the full size alone: the keys and bits of
a proof file's lookups as functions of `Cells.cell` and `Weights.entry` (Honest/ForKinds.lean); and
that they are honest (`LookIn.Meets`, Honest/K3/WitLaw.lean), conditional on the trace's bundles of
hypotheses. Definitions with code and seven theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: ZZ and BZ are the smallness test's two arrays of digits
and of their counts' bits.

What is defined and shown. The keys and bits are not written in this file. They are the library's
terms (`OnBytes.Ends.G.keyG`, `bitsG`; `A.keyA`, `bitsA`; `H.keyH`, `bitsH`; the files under
OnBytes/Tie/Pv/Lookup/Ends/) at the readings that Johnson/HonestTrace/FromCells.lean makes of the
two readers (`fromG`, `fromA`, `fromH`); on the digits the key vectors `kvZ` and the array `bzOf` of
Johnson/HonestTrace/CountsDigits.lean, at an array ZZ that is a letter here.
  1 `midP_congr`, `meets_of`: from the library's relation at a structure's own keys and bits to
    `LookIn.Meets`. `split32`: a small fact on numbers.
  2 `lookG`, `lookA`, `lookH`, `lookZ`: the four sorts' keys and bits. `inExt`, `bzIn`: an array
    over the base field, and the array BZ of an array ZZ, in the extension field.
  3 `tlAt`, `fullSources`: the smallness test's structure at a link; the filling. This `tlAt` bears
    the short name of the library's `First.Look.tlAt` (Johnson/Desc/First/Look/Laid.lean), which
    returns an option; no equation between the two is stated in this file.
  4 `lookG_meets`, `lookA_meets`, `lookH_meets`, `lookZ_meets`: conditional: they are honest. `nuZ`:
    the reading of the verifier's places at the digits.

Hypotheses that remain, in the theorems of section 4. `N`: `NamesFit X T`
(Johnson/HonestTrace/FromCells.lean); `Q`, `L`: `LookPub X` and `PlanesLaid X i x T`
(Johnson/HonestTrace/FullPlanes.lean); `M`: `MeetsAll X i x T` (Johnson/HonestTrace/Full.lean):
bundles of statements on a trace T; they are proved of the honest trace, in the goals' scope, in
files that this one does not import. `hg`: (at the layers and at attention) g < 12. On the digits:
`hF`: `Fo.ZPlan.FromPieces tl` (OnBytes/Tie/Pv/Lookup/Ends/FoZPlaced1.lean; on public data), and
`hd`: `DigitsIn tl (inExt zz)`: every digit is in its range. Of the smallness test's own array
`zzOf` that holds at every sampled matrix (`digitsIn_zzOf`, Johnson/HonestTrace/DigitsAtTrace.lean,
under `FromPieces` and `MzFits`; `digits_meets`, Honest/K3/WitDigits.lean, calls it): outside its
window a combination's digits are in range and do not give it back.
In section 1. `hM`, `h`: (in `midP_congr`) the two arrays of bits agree at the table's rows and the
32 planes; the library's relation holds of the first. `h0`, `hk`, `hb`, `hm`: (in `meets_of`) the
reading is 0 at the place zero; the keys are the joint key vector's; the bits are the reading at the
verifier's places; the library's relation holds. `hj`: (in `split32`) j < 32.

Imported, through Honest/K3/WitLaw.lean. Files directly under Honest/.

Users. Honest/K3/WitDigits.lean calls `fullSources` and `lookZ_meets`; Honest/K3/WitPlan.lean states
equations between this filling and its own.

Limits. At the full size alone: `fromG`, `fromA` and `fromH` find a matrix's label by written
numbers: twelve groups; the head is segment 24. The numbers of parts of af, ad, as, hf they take off
the public part (`labelAt`, Johnson/HonestTrace/FromCells.lean); that these are 3, 1, 1, 4 is what
`PartsFit`, a field of `NamesFit`, asks. At another
number of groups the head's keys are read in a segment that is not the head's.
Honest/K3/WitPlan.lean has a reading that goes by the public part's own numbers.
There is no theorem at a size that can be run: the three theorems on the calls depend on `NamesFit`,
which fails at the numbers of the small example.
The shape: the theorems are stated at the shapes X.y.fo, fsAt X g, X.HLy.fs and tl.f9, which are the
field fs of the verifier's own place of a lookup (`First.Look.lookAt`,
Johnson/Desc/First/Look/LookAt.lean); a row stands at the face of the shape that the kind's own
parameters make (P.shape): that the two are one shape is a public fact, is a hypothesis in the
library's theorems on the lookup too, and is not stated in this file. Shown in part: `ShapeIsFs`
(Honest/K3/LotPublic.lean) names it as a hypothesis, and by `shapeIsFs_holds` (there) an acceptance
of the test `shapeIsFs` gives it; that the test accepts is not shown in that file.
`lookH_meets` is at P := pubHAt X x; the head of `fullSources` is at the letter pubH: that pubH x is
pubHAt X x is for whoever seats the filling to show. Shown in part: `pubHAt_eq`
(Honest/K3/WitHead.lean) shows that pubHAt X x is `headPub` at the request's covered positions and
tokens; that a seated filling's letter is that one is not shown in that file. ZZ is a letter (zzOf).
The head's public data depend on the instance through a letter (pubH). The terms are a
specification's: each key is summed anew at every reading, and a count of the digits goes through
all keys at every bit. Nothing in this file says that a verifier's sub-protocol accepts. Evaluated
in part: Honest/K3/SeatFitsPlayed.lean [not in this library], at a synthetic public part and at
another filling (`tiedOwnSources`, Honest/K3/WitOwner.lean), not at this file's.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.WitLaw
import Johnson.HonestTrace.FromCells
import Johnson.HonestTrace.LookAtDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3
open OnBytes.HonestTrace (fromG fromA fromH nuFrom fsAt pubHAt cellOf entryOf NamesFit LookPub
  MeetsAll PlanesLaid kvZ bzOf virtZ DigitsIn LaidBZ Tr)
open OnBytes.Road (Hd.shapeA)
open Inst.Model (Instance ppref)

/-! ## 1 From the relation to the hypothesis -/

/-- The library's relation reads the bits at the table's rows and the 32 planes alone. -/
theorem midP_congr {n T : ℕ} {key t : ℕ → Cb.Gl.E} {pads : List (ℕ × ℕ)}
    {M M' : ℕ → ℕ → Cb.Gl.E} {al : Cb.Gl.E} (hM : ∀ u < 2 ^ T, ∀ j < 32, M u j = M' u j)
    (h : Cb.Lkp.MidP n T 5 32 key t pads M al) : Cb.Lkp.MidP n T 5 32 key t pads M' al := by
  obtain ⟨b, c, q⟩ := h
  refine ⟨fun u hu j hj => ?_, ?_, ?_⟩
  · have hj' : j < 32 := by
      norm_num at hj
      exact hj
    rw [← hM u hu j hj']
    exact b u hu j hj
  · unfold Cb.Lkp.NumKeysP at c ⊢
    rw [← c]
    exact Finset.sum_congr rfl fun u hu => Finset.sum_congr rfl fun j hj => by
      rw [hM u (Finset.mem_range.1 hu) j (Finset.mem_range.1 hj)]
  · have e : (∏ j ∈ Finset.range 32, Cb.Lkp.tabProd T t M al j ^ 2 ^ j) =
        ∏ j ∈ Finset.range 32, Cb.Lkp.tabProd T t M' al j ^ 2 ^ j :=
      Finset.prod_congr rfl fun j hj => by
        have e2 : Cb.Lkp.tabProd T t M al j = Cb.Lkp.tabProd T t M' al j := by
          unfold Cb.Lkp.tabProd
          exact Finset.prod_congr rfl fun u hu => by
            rw [hM u (Finset.mem_range.1 hu) j (Finset.mem_range.1 hj)]
        rw [e2]
    rw [q, e]

/-- From the relation at a structure's own keys and bits, and the two ties, to the hypothesis
`LookIn.Meets`. -/
theorem meets_of (L : LookIn) (h : OnBytes.Model.Forest.Shape) (lm : ℕ) (kv : ℕ → ℕ → Cb.Gl.E)
    (nu : _root_.Fo.Pl → Cb.Gl.E) (h0 : nu .zero = 0)
    (hk : ∀ theta n, L.key theta n = OnBytes.Ends.jointKey h kv theta n)
    (hb : ∀ (theta : Cb.Gl.E) (jLK u j : ℕ), u < 2 ^ h.d → j < 32 →
      L.bit u j = nu ((_root_.Fo.numsF h lm jLK theta).bAt u j))
    (hm : ∀ theta al : Cb.Gl.E, Cb.Lkp.MidP h.v h.d 5 32 (L.key theta)
      (OnBytes.Ends.jointTab h theta) (FoNums.pads h) L.bit al) : L.Meets h lm := by
  refine ⟨kv, nu, h0, hk, hb, fun theta al jLK => ?_⟩
  have e : L.key theta = OnBytes.Ends.jointKey h kv theta := funext (hk theta)
  rw [← e]
  exact midP_congr (fun u hu j hj => hb theta jLK u j hu hj) (hm theta al)

/-- Entry 32 u + j of the planes' vector is (row u, plane j). -/
theorem split32 (u : ℕ) {j : ℕ} (hj : j < 32) : (u * 32 + j) / 32 = u ∧ (u * 32 + j) % 32 = j := by
  constructor <;> omega

/-! ## 2 The four sorts' keys and bits -/

/-- The calls of group g's layers. -/
def lookG (X : OnBytes.Model.Verify.Public) (g : ℕ) (C : Cells) (W : Weights) : LookIn :=
  ⟨fun theta n => OnBytes.Ends.G.keyG X.layers g (fromG X C.cell W.entry g) theta n,
   fun u j => OnBytes.Ends.G.bitsG X.y (fromG X C.cell W.entry g) (u * 32 + j)⟩

/-- The calls of group g's attention. -/
def lookA (X : OnBytes.Model.Verify.Public) (g : ℕ) (C : Cells) : LookIn :=
  ⟨fun theta n => OnBytes.Ends.A.keyA (Hd.shapeA X g) (fsAt X g) (fromA X C.cell g) theta n,
   fun u j => OnBytes.Ends.A.bitsA (Hd.shapeA X g) (fsAt X g) (fromA X C.cell g) (u * 32 + j)⟩

/-- The head's calls. Here P is what is public at the head, the request's covered positions and
checked tokens among it. -/
def lookH (X : OnBytes.Model.Verify.Public) (P : OnBytes.Ends.H.PubH) (C : Cells) (W : Weights) :
    LookIn :=
  ⟨fun theta n => OnBytes.Ends.H.keyH P (fromH X C.cell W.entry) theta n,
   fun u j => OnBytes.Ends.H.bitsH P.h P.L.fs (fromH X C.cell W.entry) (u * 32 + j)⟩

/-- An array over the base field, in the extension field. -/
def inExt (a : ℕ → ℕ → Cb.Gl.F) (r c : ℕ) : Cb.Gl.E := algebraMap Cb.Gl.F Cb.Gl.E (a r c)

/-- The array BZ of an array ZZ, in the extension field. -/
def bzIn (tl : OnBytes.Model.HTailF2) (zz : ℕ → ℕ → Cb.Gl.F) (r c : ℕ) : Cb.Gl.E :=
  ((bzOf tl (inExt zz) r c : ℕ) : Cb.Gl.E)

/-- The digits of a smallness test with the structure tl, of the array ZZ. -/
def lookZ (tl : OnBytes.Model.HTailF2) (zz : ℕ → ℕ → Cb.Gl.F) : LookIn :=
  ⟨fun theta n => OnBytes.Ends.jointKey tl.f9 (kvZ tl (inExt zz)) theta n,
   fun u j => bzIn tl zz ((OnBytes.DgP.portQ tl).bAt u j).2.1 ((OnBytes.DgP.portQ tl).bAt u j).2.2⟩

/-! ## 3 The filling -/

/-- The structure of the smallness test of the link with the given number: an even link below 24 is
a group's layers, an odd one its attention, 24 the head; the empty structure where the public part
has no such plan. -/
def tlAt (X : OnBytes.Model.Verify.Public) (link : ℕ) : OnBytes.Model.HTailF2 :=
  if link = 24 then X.H.tl
  else if link % 2 = 0 then ((X.G[link / 2]?).map (·.tl)).getD {}
  else ((X.A[link / 2]?).map (·.seam.tl)).getD {}

/-- **The filling, at the full size.** Here cells and weights are the two readers; pubH is what is
public at the head, as a function of the instance; zzOf is the array ZZ of a link's smallness test,
as a function of the cells and the sampled matrix. -/
def fullSources {W₀ Xi Tr' : Type} (X : OnBytes.Model.Verify.Public) (cells : Tr' → Cells)
    (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH)
    (zzOf : ℕ → Cells → List Int → ℕ → ℕ → Cb.Gl.F) : Sources W₀ Xi Tr' :=
  { cells := cells
    weights := weights
    layers := lookG X
    attention := lookA X
    head := fun x => lookH X (pubH x)
    digits := fun link C ts => lookZ (tlAt X link) (zzOf link C ts) }

/-! ## 4 They are honest -/

section
variable {X : OnBytes.Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-- **The keys and bits of a group's layers are honest.** Conditional on `NamesFit X T`,
`LookPub X`, `MeetsAll X i x T`, `PlanesLaid X i x T` and g < 12: so at the full size alone.
No instance of these hypotheses is exhibited in this file: the trace's files prove the four of the
honest trace, in the goals' scope, in files that this one does not import. -/
theorem lookG_meets (N : NamesFit X T) (Q : LookPub X) (M : MeetsAll X i x T)
    (L : PlanesLaid X i x T) {g : ℕ} (hg : g < 12) :
    (lookG X g ⟨cellOf X T⟩ ⟨entryOf i⟩).Meets X.y.fo X.y.h.lmb := by
  refine meets_of _ _ _ (OnBytes.Ends.G.kvG X.layers g (fromG X (cellOf X T) (entryOf i) g))
    (nuFrom X (cellOf X T) (2 * g) fun _ => 0) rfl (fun _ _ => rfl)
    (fun theta jLK u j hu hj => ?_)
    (fun theta al => OnBytes.HonestTrace.midP_layers_cells N Q M L hg theta al)
  obtain ⟨e1, e2⟩ := split32 u hj
  show (match OnBytes.Ends.G.placeG X.y ((u * 32 + j) / 32) ((u * 32 + j) % 32) with
    | some n => fromG X (cellOf X T) (entryOf i) g n
    | none => 0) = nuFrom X (cellOf X T) (2 * g) (fun _ => 0)
      (match FoNums.cellOf X.y.fo u j with
        | some y => .cell (FoNums.cellRC X.y.fo X.y.h.lmb y).1 (FoNums.cellRC X.y.fo X.y.h.lmb y).2
        | none => .zero)
  rw [e1, e2]
  unfold OnBytes.Ends.G.placeG FoNums.cellOf
  by_cases hc : u % 2 ^ X.y.fo.cK < X.y.fo.NC
  · rw [if_pos ⟨hc, hj, hu⟩, if_pos hc]
    show OnBytes.HonestTrace.atNo X (cellOf X T) (2 * g) (OnBytes.Ends.G.iB X.y) _ _ =
      OnBytes.HonestTrace.atNo X (cellOf X T) (2 * g) (OnBytes.HonestTrace.bNo X (2 * g)) _ _
    rw [OnBytes.HonestTrace.bNoL X hg]
    rfl
  · rw [if_neg (fun h => hc h.1), if_neg hc]
    rfl

/-- **The keys and bits of a group's attention are honest.** Conditional on `NamesFit X T`,
`LookPub X`, `MeetsAll X i x T`, `PlanesLaid X i x T` and g < 12: so at the full size alone.
No instance of these hypotheses is exhibited in this file, as at `lookG_meets`. -/
theorem lookA_meets (N : NamesFit X T) (Q : LookPub X) (M : MeetsAll X i x T)
    (L : PlanesLaid X i x T) {g : ℕ} (hg : g < 12) :
    (lookA X g ⟨cellOf X T⟩).Meets (fsAt X g) (Hd.shapeA X g).cf.lmb := by
  refine meets_of _ _ _
    (OnBytes.Ends.A.kvA (Hd.shapeA X g) (fsAt X g) (fromA X (cellOf X T) g))
    (nuFrom X (cellOf X T) (2 * g + 1) fun _ => 0) rfl (fun _ _ => rfl)
    (fun theta jLK u j hu hj => ?_)
    (fun theta al => OnBytes.HonestTrace.midP_att_cells N Q M L hg theta al)
  obtain ⟨e1, e2⟩ := split32 u hj
  show (match OnBytes.Ends.A.placeBA (Hd.shapeA X g) (fsAt X g) ((u * 32 + j) / 32)
      ((u * 32 + j) % 32) with
    | some n => fromA X (cellOf X T) g n
    | none => 0) = nuFrom X (cellOf X T) (2 * g + 1) (fun _ => 0)
      (match FoNums.cellOf (fsAt X g) u j with
        | some y => .cell (FoNums.cellRC (fsAt X g) (Hd.shapeA X g).cf.lmb y).1
            (FoNums.cellRC (fsAt X g) (Hd.shapeA X g).cf.lmb y).2
        | none => .zero)
  rw [e1, e2]
  unfold OnBytes.Ends.A.placeBA FoNums.cellOf
  by_cases hc : u % 2 ^ (fsAt X g).cK < (fsAt X g).NC
  · rw [if_pos ⟨hc, hj, hu⟩, if_pos hc]
    show OnBytes.HonestTrace.atNo X (cellOf X T) (2 * g + 1) ((Hd.shapeA X g).cf.NAs + 2) _ _ =
      OnBytes.HonestTrace.atNo X (cellOf X T) (2 * g + 1)
        (OnBytes.HonestTrace.bNo X (2 * g + 1)) _ _
    rw [OnBytes.HonestTrace.bNo_odd]
    rfl
  · rw [if_neg (fun h => hc h.1), if_neg hc]
    rfl

/-- **The keys and bits of the head are honest**, at the head's public data of the request x.
Conditional on `NamesFit X T`, `LookPub X`, `MeetsAll X i x T`, `PlanesLaid X i x T`: so at the full
size alone. No instance of these hypotheses is exhibited in this file, as at `lookG_meets`. -/
theorem lookH_meets (N : NamesFit X T) (Q : LookPub X) (M : MeetsAll X i x T)
    (L : PlanesLaid X i x T) :
    (lookH X (pubHAt X x) ⟨cellOf X T⟩ ⟨entryOf i⟩).Meets X.HLy.fs X.hS.lmbH := by
  refine meets_of _ _ _
    (OnBytes.Ends.H.kvH (pubHAt X x) (fromH X (cellOf X T) (entryOf i)))
    (nuFrom X (cellOf X T) 24 fun _ => 0) rfl (fun _ _ => rfl)
    (fun theta jLK u j hu hj => ?_)
    (fun theta al => OnBytes.HonestTrace.midP_head_cells N Q M L theta al)
  obtain ⟨e1, e2⟩ := split32 u hj
  show (match OnBytes.Ends.H.placeH X.hS X.HLy.fs ((u * 32 + j) / 32) ((u * 32 + j) % 32) with
    | some n => fromH X (cellOf X T) (entryOf i) n
    | none => 0) = nuFrom X (cellOf X T) 24 (fun _ => 0)
      (match FoNums.cellOf X.HLy.fs u j with
        | some y => .cell (FoNums.cellRC X.HLy.fs X.hS.lmbH y).1
            (FoNums.cellRC X.HLy.fs X.hS.lmbH y).2
        | none => .zero)
  rw [e1, e2]
  unfold OnBytes.Ends.H.placeH FoNums.cellOf
  by_cases hc : u % 2 ^ X.HLy.fs.cK < X.HLy.fs.NC
  · rw [if_pos ⟨hc, hj, hu⟩, if_pos hc]
    show OnBytes.HonestTrace.atNo X (cellOf X T) 24 (X.hS.NHf + 2) _ _ =
      OnBytes.HonestTrace.atNo X (cellOf X T) 24 (OnBytes.HonestTrace.bNo X 24) _ _
    rw [OnBytes.HonestTrace.bNo_head]
    rfl
  · rw [if_neg (fun h => hc h.1), if_neg hc]
    rfl

end

/-- The reading of the verifier's places at the digits: the planes' cells out of BZ, read as the
matrix with one row for each plane. At every place that is no cell it is 0. -/
def nuZ (tl : OnBytes.Model.HTailF2) (zz : ℕ → ℕ → Cb.Gl.F) : _root_.Fo.Pl → Cb.Gl.E
  | .cell r c => virtZ tl (bzIn tl zz) r c
  | _ => 0

/-- **The keys and bits of the digits are honest.** Conditional on `Fo.ZPlan.FromPieces tl` (on
public data) and `DigitsIn tl zz`: every digit is in its range. At any size. No instance of these
hypotheses is exhibited in this file: the library shows `FromPieces` at every smallness
test's structure of what `Verify.publicOf` (OnBytes/Model/VerifyPublic.lean) returns
(`public_G_from`, `public_A_from`, `public_H_from`, OnBytes/Tie/Pv/Lookup/Ends/FoZPlaced1.lean). -/
theorem lookZ_meets {tl : OnBytes.Model.HTailF2} (hF : Fo.ZPlan.FromPieces tl)
    {zz : ℕ → ℕ → Cb.Gl.F} (hd : DigitsIn tl (inExt zz)) : (lookZ tl zz).Meets tl.f9 5 := by
  have hb : LaidBZ tl (inExt zz) (bzIn tl zz) := fun _ _ _ _ => rfl
  refine meets_of _ _ _ (kvZ tl (inExt zz)) (nuZ tl zz) rfl (fun _ _ => rfl)
    (fun theta jLK u j hu hj => ?_)
    (fun theta al => OnBytes.HonestTrace.lawZ hF hd hb theta al)
  exact (OnBytes.HonestTrace.bz_plane hb hu hj).trans
    (OnBytes.HonestTrace.Look.bAt_plane tl.f9 5 jLK theta
      (OnBytes.HonestTrace.hitsZ tl (inExt zz)) (le_refl 5) (Nat.le_add_left 5 _) (nuZ tl zz)
      (fun r hr c hc => OnBytes.HonestTrace.virtZ_plane hF hb r hr c hc) rfl hu hj).symm

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.midP_congr
#print axioms ProofFile.Honest.K3.meets_of
#print axioms ProofFile.Honest.K3.split32
#print axioms ProofFile.Honest.K3.lookG_meets
#print axioms ProofFile.Honest.K3.lookA_meets
#print axioms ProofFile.Honest.K3.lookH_meets
#print axioms ProofFile.Honest.K3.lookZ_meets
