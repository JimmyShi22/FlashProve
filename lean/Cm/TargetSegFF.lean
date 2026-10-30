-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegFF.lean: the feed-forward segment of group g (all of the group's four layers but
attention itself, from queries, keys and values to its output o (Cm/TargetSegAtt.lean); 34 families
of keys, among them the seven that hold a matrix product with weights: queries and keys with the
rotation, values, output projection, gate, up and down projections with the routed experts, router;
see the head of Cm/TargetSegModel.lean), assembled as a segment (`SegSpec`) of Cb/Req/ReqSpec.lean
over p = 2^64 - 2^32 + 1, and its conditions compared with those of Cm/TargetPRel.lean (`TP.CondL`
at `Cb.Gl.p`: `ffKey`, `ffIdn`).

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`). A segment has the shape of its matrix of cells, its families of identities and
its families of keys with their tables. Keys (`FFSeg.key`), identities (`FFSeg.idnVal`) and the
relation's part `FFSeg.trace` are those of Inst/Model/FF/Trace.lean. Group g is four consecutive
layers of the model; its feed-forward segment is segment 2 g of Cm/SegLayout.lean.

Main names:
  `KeyOK Φ g tb s f`: what the theorems on `ffSpec` require of the family f that renders the keys
    of s: (iff) for every set S that holds the padding value of the table: all values of f on its
    cube are in S if and only if all keys of s (those of Inst/Model/FF/Trace.lean, over E, at the
    trace `tA g A` and the weights `wOf g W`) are; (wf); (places) it reads only places of valid
    cells that the segment reads, own or borrowed (`IsFF`).
  `IdnOK Φ g first tok fs`: what they require of the list fs of families that render the identities
    (J1) to (J10), and (J11) if first = true: (iff) all values of these families on their cubes are
    0 if and only if all valid identities (`FFSeg.idnVal`, over E, at the trace `tA g A`, `embOf W`
    and `tok x₀`) are 0; (wf), (places): as in `KeyOK`, of every family of fs.
  `affKey_ok`: the 22 affine families of Cm/SegPilotAff.lean have `KeyOK`.
  `ffSpec tb kf idf`: the segment: 2^19 rows, 5,990 columns; keys: the 34 families with their
    tables; identities: idf.
  `ffSpec_holds_iff`: under `KeyOK` of all kf s and `IdnOK` of idf, its conditions hold at integer
    matrices M and an integer index matrix if and only if the keys of Inst/Model/FF/Trace.lean are
    entries of their tables and that file's identities are 0, over the prime field `Cb.Gl.F`, for
    every integer trace on the valid names that agrees with M at the owners' places (`ownFF`,
    Cm/SegLayout.lean).
  `ffSpec_iff_toMat`, `ffSpec_iff_ofMat`: the same for g < `nGr`, at the table of scales
    `SFK κ nf g`, at `tbRef` and first = `decide (g = 0)`: at the matrices of a trace
    (completeness; under `hh : h.OK`, with `Hd.OK` of Cm/SegLayout.lean) and at the trace of
    matrices (knowledge soundness), in the words of `TP.CondL`'s clauses `ffKey`, `ffIdn` at g.
  `ffSpec_wf`, `ffSpec_places`: under the same two hypotheses the segment is well formed
    (`SegSpec.WF`) and reads only places with `IsFF g` (told at `KeyOK`). `ffSpec_reads`: see its
    docstring.

The field is `Cb.Gl.F` (Cb/Gl/GlField.lean), the integers modulo p. `castW` is
`Cm.TP.castW Cb.Gl.p` (an integer index matrix, read modulo p) and `segFF κ nf g` is
`Cm.TP.segFF Cb.Gl.p κ nf g`: the model's conditions are `Cm.TP.CondL` at `Cb.Gl.p`
(Cm/TargetPRel.lean: clauses `ffKey`, `ffIdn`).

Limits: the families that are not affine (matrix products with weights; products of cells) and the
identities are parameters here, with `KeyOK` / `IdnOK` as hypotheses.
Terms: lean/GLOSSARY.md.
-/
import Cm.SegFF
import Cm.TargetSegAll
import Cm.TargetSegFFAffPass


set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS
open Cb Inst.Model Inst.Model.All Finset
open Inst.Model.Layout (kRef)

variable [scl : Scl] {X E : Type} [Field E] [Algebra Cb.Gl.F E]

/-- What the theorems on `ffSpec` require of a family of keys. -/
structure KeyOK (Φ : IdxFmt Cb.Gl.F) (g : ℕ) (tb : Tables) (s : FFSeg.Fam) (f : Cb.Fam X E) :
    Prop where
  iff : ∀ (x₀ : X) (W : ℕ → ℕ → Cb.Gl.F) (A : ℕ → ℕ → ℕ → E) (S : Set E), ((padOf tb s : ℤ) : E) ∈
      S →
    ((∀ b < 2 ^ f.v, f.val Φ x₀ W A b ∈ S) ↔
      ∀ l < DF.nl, FFSeg.present s l = true →
        ∀ x < FFSeg.len DF s, ∀ i < DF.T, FFSeg.key DF (tA g A) tb (4 * g) (wOf g W) s l x i ∈ S)
  wf : f.WF Φ
  places : ∀ p ∈ f.places, IsFF g p

/-- What they require of the families of identities. -/
structure IdnOK (Φ : IdxFmt Cb.Gl.F) (g : ℕ) (first : Bool)
    (tok : X → ℕ → ℕ) (fs : List (Cb.Fam X E)) : Prop where
  iff : ∀ (x₀ : X) (W : ℕ → ℕ → Cb.Gl.F) (A : ℕ → ℕ → ℕ → E),
    (∀ f ∈ fs, ∀ b < 2 ^ f.v, f.val Φ x₀ W A b = 0) ↔
    ∀ j : FFSeg.Idn, j.Valid DF first → FFSeg.idnVal DF (tA g A) (embOf W) (tok x₀) j = 0
  wf : ∀ f ∈ fs, f.WF Φ
  places : ∀ f ∈ fs, ∀ p ∈ f.places, IsFF g p

theorem affKey_ok (Φ : IdxFmt Cb.Gl.F) (g : ℕ) (tb : Tables) {s : FFSeg.Fam} (hs : isAff s = true) :
    KeyOK Φ g tb s (affKeyFam (X := X) (E := E) g tb s) where
  iff := fun x₀ W A S hS => affKey_iff g tb Φ x₀ W A (4 * g) (wOf g W) hs S hS
  wf := affKey_wf g tb Φ s
  places := affKey_places g tb s

/-! ## Tables -/

/-- all families -/
def allFams : List FFSeg.Fam :=
  [.G, .U, .UT, .QK, .N1, .N2, .O, .D, .V, .LR, .XR, .LT, .DD, .GH, .UH, .OH, .DH, .VH, .LH, .QKH,
    .N1H, .N2H, .ROW, .SEL, .L3, .G0, .CN1, .CN2, .CQK, .CV, .CLR, .F, .MR, .CG]

theorem mem_allFams (s : FFSeg.Fam) : s ∈ allFams := by cases s <;> decide

/-- log2 of the number of rows of the table of a family -/
def tOf (s : FFSeg.Fam) : ℕ := if FFSeg.call s = 3 then 8 else 16

theorem rows_eq (tb : Tables) (s : FFSeg.Fam) : (FFSeg.lut tb (FFSeg.call s)).rows = 2 ^ tOf s := by
  cases s <;> rfl

/-- the padding value is an entry of the table -/
theorem pad_mem (tb : Tables) (s : FFSeg.Fam) :
    ((padOf tb s : ℤ) : Cb.Gl.F) ∈ (FFSeg.lutSet (FFSeg.lut tb (FFSeg.call s)) : Set Cb.Gl.F) := by
  have h0 : ∀ L : Lut,
      0 < L.rows → L.row 0 = L.pad → ((L.pad : ℤ) : Cb.Gl.F) ∈ (FFSeg.lutSet L : Set Cb.Gl.F) :=
    fun L h1 h2 => ⟨0, h1, by rw [h2]⟩
  have h15 : ∀ L : Lut, 2 ^ 15 < L.rows → L.row (2 ^ 15) = L.pad →
      ((L.pad : ℤ) : Cb.Gl.F) ∈ (FFSeg.lutSet L : Set Cb.Gl.F) :=
    fun L h1 h2 => ⟨2 ^ 15, h1, by rw [h2]⟩
  cases s <;> first
    | exact h0 R16 (by norm_num [R16]) (by simp [R16])
    | exact h0 R8 (by norm_num [R8]) (by simp [R8])
    | exact h15 FC (by norm_num [FC]) TablesSanity.fc_pad
    | exact h15 (FS tb) (by norm_num [FS]) (TablesSanity.fs_pad tb)
    | exact h15 (FL tb) (by norm_num [FL]) (TablesSanity.fl_pad tb)

/-! ## The segment -/

variable (g : ℕ) (tb : Tables) (kf : FFSeg.Fam → Cb.Fam X E) (idf : List (Cb.Fam X E))

/-- The feed-forward segment of group g (what the name covers: this file's head). -/
def ffSpec : SegSpec X Cb.Gl.F E :=
  ⟨19, colsFF, idf, allFams.map fun s => (kf s, tabOf (FFSeg.lut tb (FFSeg.call s)) (tOf s))⟩

variable {g tb kf idf} {Φ : IdxFmt Cb.Gl.F} {first : Bool} {tok : X → ℕ → ℕ}

theorem ffSpec_wf (hk : ∀ s, KeyOK Φ g tb s (kf s)) (hi : IdnOK Φ g first tok idf) :
    (ffSpec tb kf idf).WF Φ := by
  refine ⟨hi.wf, fun k hkm => ?_⟩
  obtain ⟨s, -, rfl⟩ := List.mem_map.1 hkm
  exact (hk s).wf

theorem ffSpec_places (hk : ∀ s, KeyOK Φ g tb s (kf s)) (hi : IdnOK Φ g first tok idf) :
    ∀ p ∈ (ffSpec tb kf idf).places, IsFF g p := by
  rintro p (⟨f, hf, hp⟩ | ⟨k, hkm, hp⟩)
  · exact hi.places f hf p hp
  · obtain ⟨s, -, rfl⟩ := List.mem_map.1 hkm
    exact (hk s).places p hp

/-- Under `hk`, `hi` and `ht`, at integer matrices M and an integer index matrix the conditions of
the segment hold if and only if those of Inst/Model/FF/Trace.lean on keys and identities hold at
t'. -/
theorem ffSpec_holds_iff (hk : ∀ s, KeyOK Φ g tb s (kf s))
    (hi : IdnOK Φ g first tok idf) (x₀ : X) (M : ℕ → ℕ → ℕ → ℤ) (Wi : Mat)
    (t' : {c : FFSeg.Cell // c.Valid DF} → ℤ) (ht : ∀ c, t' c = tM g M c.val) :
    (ffSpec tb kf idf).Holds Φ x₀ (TP.castW Cb.Gl.p Wi) (Partition.castM (E := E) M) ↔
    (∀ k, (FFSeg.trace DF tb kRef (4 * g) first Cb.Gl.F).key (tok x₀) (TP.castW Cb.Gl.p Wi) t' k ∈
      (FFSeg.trace DF tb kRef (4 * g) first Cb.Gl.F).table k) ∧
    ∀ j, (FFSeg.trace DF tb kRef (4 * g) first Cb.Gl.F).idn (tok x₀) (TP.castW Cb.Gl.p Wi) t' j =
      0 := by
  have hS : ∀ s, ((padOf tb s : ℤ) : E) ∈
      {e : E | ∃ u ∈ (tabOf (FFSeg.lut tb (FFSeg.call s)) (tOf s) : Tab Cb.Gl.F).set,
        e = algebraMap Cb.Gl.F E u} := fun s =>
    ⟨((padOf tb s : ℤ) : Cb.Gl.F),
      (mem_tabOf (rows_eq tb s) _).2 (pad_mem tb s),
      (map_intCast _ _).symm⟩
  unfold SegSpec.Holds
  rw [and_comm]
  refine and_congr ?_ ?_
  · constructor
    · rintro h ⟨⟨s, l, x, i⟩, hl, hp, hx, hii⟩
      have h1 := ((hk s).iff x₀ (TP.castW Cb.Gl.p Wi) (Partition.castM (E := E) M) _ (hS s)).1
        (h (kf s, _) (List.mem_map_of_mem (mem_allFams s))) l hl hp x hx i hii
      exact (key_mem_iff g M Wi t' ht tb (rows_eq tb s) hl hp hx hii).1 h1
    · intro h k hkm
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 hkm
      refine ((hk s).iff x₀ (TP.castW Cb.Gl.p Wi) (Partition.castM (E := E) M) _ (hS s)).2
        fun l hl hp x hx i hii => ?_
      exact (key_mem_iff g M Wi t' ht tb (rows_eq tb s) hl hp hx hii).2
        (h ⟨(s, l, x, i), hl, hp, hx, hii⟩)
  · refine (hi.iff x₀ (TP.castW Cb.Gl.p Wi) (Partition.castM (E := E) M)).trans ?_
    constructor
    · rintro h ⟨j, hj⟩
      exact (idn_zero_iff g M Wi t' ht first (tok x₀) hj).1 (h j hj)
    · intro h j hj
      exact (idn_zero_iff g M Wi t' ht first (tok x₀) hj).2 (h ⟨j, hj⟩)

/-! ## At the conditions of Cm/TargetPRel.lean (`Cm.TP.CondL` at `Cb.Gl.p`) -/

omit scl in
/-- For the matrices of a trace (completeness): under the hypotheses below, the segment's
conditions hold at `toMat h T` if and only if the clauses `ffKey`, `ffIdn` of `Cm.TP.CondL Cb.Gl.p`
hold at g. -/
theorem ffSpec_iff_toMat (κ : ℕ → LayerScale) (nf : NormPar) (h : Hd) (hh : h.OK) (hg : g < nGr)
    (hk : ∀ s, KeyOK (scl := SFK κ nf g) Φ g tbRef s (kf s))
    (hi : IdnOK (scl := SFK κ nf g) Φ g (decide (g = 0)) tok idf) (x₀ : X) (T : Trace) (Wi : Mat) :
    (ffSpec tbRef kf idf).Holds Φ x₀ (TP.castW Cb.Gl.p Wi) (Partition.castM (E := E) (toMat h T)) ↔
    (∀ k, (TP.segFF Cb.Gl.p κ nf g).key (tok x₀) (TP.castW Cb.Gl.p Wi) (fun c => T.vFF g c.val) k ∈
      (TP.segFF Cb.Gl.p κ nf g).table k) ∧
    ∀ j,
      (TP.segFF Cb.Gl.p κ nf g).idn (tok x₀) (TP.castW Cb.Gl.p Wi) (fun c => T.vFF g c.val) j = 0 :=
  ffSpec_holds_iff (scl := SFK κ nf g) hk hi x₀ (toMat h T) Wi (fun c => T.vFF g c.val)
    fun c => (lay_read_toMat h hh T).1 g hg c.val c.property

omit scl in
/-- For the trace of matrices (knowledge soundness): under the hypotheses below, the segment's
conditions hold at M if and only if the clauses `ffKey`, `ffIdn` of `Cm.TP.CondL Cb.Gl.p` hold at g
for `ofMat h M`. -/
theorem ffSpec_iff_ofMat (κ : ℕ → LayerScale) (nf : NormPar) (h : Hd) (hg : g < nGr)
    (hk : ∀ s, KeyOK (scl := SFK κ nf g) Φ g tbRef s (kf s))
    (hi : IdnOK (scl := SFK κ nf g) Φ g (decide (g = 0)) tok idf) (x₀ : X)
    (M : ℕ → ℕ → ℕ → ℤ) (Wi : Mat) :
    (ffSpec tbRef kf idf).Holds Φ x₀ (TP.castW Cb.Gl.p Wi) (Partition.castM (E := E) M) ↔
    (∀ k, (TP.segFF Cb.Gl.p κ nf g).key
        (tok x₀) (TP.castW Cb.Gl.p Wi) (fun c => (ofMat h M).vFF g c.val) k ∈
      (TP.segFF Cb.Gl.p κ nf g).table k) ∧
    ∀ j, (TP.segFF Cb.Gl.p κ nf g).idn
        (tok x₀) (TP.castW Cb.Gl.p Wi) (fun c => (ofMat h M).vFF g c.val) j = 0 :=
  ffSpec_holds_iff (scl := SFK κ nf g) hk hi x₀ M Wi (fun c => (ofMat h M).vFF g c.val)
    fun c => (lay_read_ofMat h M).1 g hg c.val c.property

omit scl in
/-- under the hypotheses below, the places that the segment reads are among those of the layout
(`reads`) -/
theorem ffSpec_reads (κ : ℕ → LayerScale) (nf : NormPar) (h : Hd) (hg : g < nGr)
    (hk : ∀ s, KeyOK (scl := SFK κ nf g) Φ g tbRef s (kf s))
    (hi : IdnOK (scl := SFK κ nf g) Φ g (decide (g = 0)) tok idf) :
    ∀ p ∈ (ffSpec tbRef kf idf).places, p ∈ reads h (2 * g) :=
  fun p hp => isFF_reads g h hg (ffSpec_places (scl := SFK κ nf g) hk hi p hp)

end Cm.Seg.TS
