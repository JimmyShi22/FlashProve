-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegFFAffPass.lean: from the (V) statements of the feed-forward segment's families to the
conditions of Cm/TargetPRel.lean (`TP.CondL` at `Cb.Gl.p`: `ffKey`, `ffIdn`), over
p = 2^64 - 2^32 + 1. One lemma for all keys, one for all identities; no family is named.

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean). Used in the theorems on `ffSpec` (Cm/TargetSegFF.lean:
`ffSpec_holds_iff`).

A (V) statement says: at the vertex of an index, the value of a family is the key (identity) of
Inst/Model/FF/Trace.lean over E, at the trace `tA g A` (the matrices A over E, read at the owners'
places) and the weights `wOf g W` (read from the index matrix over the prime field, carried into
E).
The conditions of Cm/TargetPRel.lean are formed over the prime field `Cb.Gl.F`, at a trace of
integers defined on valid names. Here: if A is a family M of integer matrices read in E, W an
integer matrix read in `Cb.Gl.F`, and the integer trace t' agrees with M at the owners' places,
then
  `key_pass`: at an index of its family, the key over E is the image of the key over `Cb.Gl.F`;
    `idn_pass`: the same for the identities with valid names;
  `key_mem_iff`, `idn_zero_iff`: so "the key over E is the image of an element of the table" says
    "the key over `Cb.Gl.F` is an entry of the table" (for a table of 2^T rows), and "the identity
    over E is 0" says "the identity over `Cb.Gl.F` is 0".
Why: both sides are casts of one integer (`FFSeg.key_cast`, `FFSeg.idn_cast`), and a key at an
index of its family reads valid names only (`FFSeg.key_congr`, `FFSeg.idn_congr`).

`castW` is `Cm.TP.castW Cb.Gl.p` (an integer index matrix, read modulo p: Cm/TargetPRel.lean).

Limits: what is not said of the segment's families: Cm/TargetSegFFAll.lean, the head, Limits.
Terms: lean/GLOSSARY.md.
-/
import Cm.SegFFAffPass
import Cm.TargetSegAll


set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS
open Cb Inst.Model Inst.Model.All Finset
open Inst.Model.Layout (kRef)

variable [scl : Scl] {E : Type} [Field E] [Algebra Cb.Gl.F E] (g : ℕ)

/-- integer matrices, read as an integer trace of the feed-forward segment of group g -/
def tM (M : ℕ → ℕ → ℕ → ℤ) : FFSeg.Cell → ℤ := fun c => at' M (ownFF g c).place

theorem tA_castM (M : ℕ → ℕ → ℕ → ℤ) : tA g (Partition.castM (E := E) M) = FFSeg.castT (tM g M) :=
  rfl

theorem wOf_cast (Wi : Mat) :
    wOf (F := Cb.Gl.F) (E := E) g (TP.castW Cb.Gl.p Wi) =
      fun l => FFSeg.LW.ofInt E (Layout.layerOf ppref kRef Wi (4 * g + l)) := funext fun l => by
  unfold wOf
  rw [FFSeg.Cast.layerCast', mapLW_ofInt]

/-- the embedding that (J11) reads: from the index matrix over the prime field, carried into E -/
def embOf (W : ℕ → ℕ → Cb.Gl.F) : ℕ → ℕ → E := fun a b =>
  algebraMap Cb.Gl.F E (FFSeg.embR ppref kRef W a b)

theorem embOf_cast (Wi : Mat) :
    embOf (E := E) (TP.castW Cb.Gl.p Wi) =
      fun a b => (((Layout.weightsOf ppref kRef Wi).Emb a b : ℤ) : E) := by
  funext a b
  unfold embOf
  rw [FFSeg.embCast]
  exact map_intCast _ _

variable (M : ℕ → ℕ → ℕ → ℤ)
  (Wi : Mat) (t' : {c : FFSeg.Cell // c.Valid DF} → ℤ) (ht : ∀ c, t' c = tM g M c.val) (tb : Tables)
include ht

theorem rd_agrees :
    ∀ c : FFSeg.Cell, c.Valid DF → tM g M c = (FFSeg.rd DF t' : FFSeg.Cell → ℤ) c := fun c hc => by
  unfold FFSeg.rd
  rw [dif_pos hc, ht ⟨c, hc⟩]
  exact (Int.cast_id).symm

/-- The keys. -/
theorem key_pass {s : FFSeg.Fam} {l x i : ℕ} (hl : l < DF.nl) (hs : FFSeg.present s l = true)
    (hx : x < FFSeg.len DF s) (hi : i < DF.T) :
    FFSeg.key DF (tA g (Partition.castM (E := E) M)) tb (4 * g)
        (wOf g (TP.castW Cb.Gl.p Wi)) s l x i =
      algebraMap Cb.Gl.F E
        (FFSeg.key DF (FFSeg.rd DF t') tb (4 * g)
          (fun l => FFSeg.layerR ppref kRef (TP.castW Cb.Gl.p Wi) (4 * g + l)) s l x i) := by
  rw [tA_castM, wOf_cast, FFSeg.key_cast, FFSeg.rd_cast]
  simp only [FFSeg.Cast.layerCast']
  rw [FFSeg.key_cast, map_intCast,
    FFSeg.key_congr (rd_agrees g M t' ht) rfl tb (4 * g) _ hl hs hx hi]

/-- The identities. -/
theorem idn_pass (first : Bool) (tok : ℕ → ℕ) {j : FFSeg.Idn} (hj : j.Valid DF first) :
    FFSeg.idnVal DF (tA g (Partition.castM (E := E) M)) (embOf (TP.castW Cb.Gl.p Wi)) tok j =
      algebraMap Cb.Gl.F E
        (FFSeg.idnVal DF (FFSeg.rd DF t') (FFSeg.embR ppref kRef (TP.castW Cb.Gl.p Wi)) tok j) := by
  rw [tA_castM, embOf_cast, FFSeg.idn_cast, FFSeg.rd_cast, FFSeg.embCast, FFSeg.idn_cast,
    map_intCast, FFSeg.idn_congr (rd_agrees g M t' ht) first _ tok hj]

omit ht in
/-- Under `hL`, the image of k is the image of an element of the table if and only if k is an entry
of the table -/
theorem mem_image_iff {L : Lut} {T : ℕ} (hL : L.rows = 2 ^ T) (k : Cb.Gl.F) :
    (∃ u ∈ (tabOf L T : Tab Cb.Gl.F).set, algebraMap Cb.Gl.F E k = algebraMap Cb.Gl.F E u) ↔
    k ∈ (FFSeg.lutSet L : Set Cb.Gl.F) := by
  constructor
  · rintro ⟨u, hu, h⟩
    rw [(algebraMap Cb.Gl.F E).injective h]
    exact (mem_tabOf hL u).1 hu
  · exact fun h => ⟨k, (mem_tabOf hL k).2 h, rfl⟩

theorem key_mem_iff {L : Lut} {T : ℕ} (hL : L.rows = 2 ^ T) {s : FFSeg.Fam} {l x i : ℕ}
    (hl : l < DF.nl) (hs : FFSeg.present s l = true) (hx : x < FFSeg.len DF s) (hi : i < DF.T) :
    (∃ u ∈ (tabOf L T : Tab Cb.Gl.F).set,
      FFSeg.key DF (tA g (Partition.castM (E := E) M)) tb (4 * g)
          (wOf g (TP.castW Cb.Gl.p Wi)) s l x i =
        algebraMap Cb.Gl.F E u) ↔
    FFSeg.key DF (FFSeg.rd DF t') tb (4 * g)
        (fun l => FFSeg.layerR ppref kRef (TP.castW Cb.Gl.p Wi) (4 * g + l)) s l x i ∈
      (FFSeg.lutSet L : Set Cb.Gl.F) := by
  rw [key_pass g M Wi t' ht tb hl hs hx hi]
  exact mem_image_iff hL _

theorem idn_zero_iff (first : Bool) (tok : ℕ → ℕ) {j : FFSeg.Idn} (hj : j.Valid DF first) :
    FFSeg.idnVal DF (tA g (Partition.castM (E := E) M)) (embOf (TP.castW Cb.Gl.p Wi)) tok j = 0 ↔
    FFSeg.idnVal DF (FFSeg.rd DF t') (FFSeg.embR ppref kRef (TP.castW Cb.Gl.p Wi)) tok j = 0 := by
  rw [idn_pass g M Wi t' ht first tok hj]
  exact map_eq_zero_iff _ (algebraMap Cb.Gl.F E).injective

end Cm.Seg.TS
