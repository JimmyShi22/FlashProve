-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysIdn.lean: the identities' half of the conditions of a feed-forward segment,
on cells in the numbering of the verifier's lists.

The conditions of a segment of the library's partition have two halves (SegSpec.Holds in
Cb/Req/ReqSpec.lean): every identity is 0 at every vertex, and every key lies in its table.
Johnson/Road/FormsKeysTie.lean and the files behind it say the keys' half of a group's feed-forward
segment on the cells of integer matrices Mz that are numbered as the verifier's list for a group
numbers its matrices: the cells named by the library's numbers of features, at the part, row and
column that the verifier's rule gives a feature. This file does the same for the identities' half,
and joins the two.

The identities (Idn, idnVal in Inst/Model/FF/Trace.lean): for each of the 8 norm instances of a
group and each position the 17 identities of the ledger of a normalisation
(Inst/Model/Common/Ledger.lean); for each of the 2 layers with experts and each position, that the
selector's entries sum to 1; in the first group, for each feature and position, that the stream
that comes in is the embedding of the prompt's token.

What is compared with what. The sections up to idn_scl: the library with itself. From idn_dict on:
on one side the library's idnVal and keyVec on cells named by these files' dictionary (cellsOf,
cellsAt) in integer matrices Mz, at an embedding and weights read by the library's layout in an
integer index matrix Wi, all carried into the field, under the table of scales sclOf; on the other
side the conditions of segment 2 g of the library's model at Wi modulo the prime and at integer
matrices of the library's. No function of the verifier's sub-proof stands in a statement: of the
verifier there is the layout's numbers (through cellsAt) and the scale file (through wordsAt).

Main definitions: IdnHold (the first clause of SegSpec.Holds). Main theorems.
 - holds_halves, idn_glued_any: the two halves; gluing keeps the identities' half.
 - idn_seg, idn_glued, keys_seg: the halves of segment 2 g of the model, before gluing and glued,
   in identities by name and in the eight key vectors; for all index matrices and all matrices of
   cells.
 - idn_scl, idn_dict: two tables of scales with the same words; the two dictionaries.
 - idn_end, keys_end, holds_end: on the cells of Mz, before gluing, for any integer matrices that
   hold them at the library's places.
 - idn_port_file, holds_port_file, holds_lab_file: at the matrices of
   Johnson/Road/FormsKeysDict.lean and Johnson/Road/FormsKeysDictA.lean, glued.

Who reads the targets. Holds of (Cm.Seg.TS.segM s k).glued is what the Cond of the library's
partition asks of segment k, at the partition's own format (the library crosses: SegSpec.holds_same
in Cb/Part/LdPartIdxFmt.lean); the laws admit and force read Cond whole: all 25 segments, and a
bound on the cells. Holds of segM s k before gluing, for all k below 25, is read by the library's
model_force and model_equiv (Cm/TargetSegModel.lean). Twelve of the 25 segments are said here; so
nothing here reaches the relation.


At which sizes. idn_glued_any: every segment. idn_scl: all sizes, every ring. All else: DF, the
library's Dim.ref; the format fmtRef; the reference tables; groups of four layers, the first layer
4 g; the fields Cb.Gl.F and Cb.Gl.E (idn_dict: every field over Cb.Gl.F). From idn_dict on: at
casts of integers alone.

The hypotheses, and that they can be met. g < nGr = 12. hD: met by dict_valid and dict_lab, as in
the last section. hw: met by scalesOf (words_file). hy, S, Z, Z2, hp4: see
Johnson/Road/FormsKeysTieP.lean. That the segment is well formed and that its families have the
library's IdnOK are theorems of the library (ffSeg_wf, idn_ok).

What is not claimed. That the identities vanish or that the entries lie in the tables. That the
verifier's claims say so: by a reading of its text it claims each line of a ledger once for each
norm, at a token point, where the library asks each identity at every position; what lies between
is not touched here. That a run's matrices are casts of integers, or small. That Wi is a matrix to
which anybody has committed, or that the verifier reads its weights and its embedding by the
library's layout; that its tables are the library's reference tables; which array and tensor stands
where is the library's (that the verifier's tensors lie where cellsOf reads is tied_cellsOf in
Johnson/Road/FormsKeysFits.lean, which no term joins with this file); that the prompt of x is the
request's. That scalesOf h sc nf is lawful. The program does not import this file.
-/
import Johnson.Road.FormsKeysTieP

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model.Layer (Lay Shape Scales layout)
open Inst.Model (Scl Tables Mat ppref)
open Inst.Model.All (DF SFK nGr)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Dim Cell Idn idnVal embR keyVec layerR lut aC)

/-! ## The identities' half of a segment's conditions -/

section Half

variable {X F E : Type} [Field F] [Field E] [Algebra F E]

/-- The identities' half of the conditions of a segment: every family of identities is 0 at every
vertex of its cube. It is the first of the two clauses of the library's SegSpec.Holds
(Cb/Req/ReqSpec.lean). -/
def IdnHold (S : Cb.SegSpec X F E) (Φ : Cb.IdxFmt F) (x : X) (W : ℕ → ℕ → F)
    (A : ℕ → ℕ → ℕ → E) : Prop :=
  ∀ f ∈ S.idn, ∀ b < 2 ^ f.v, f.val Φ x W A b = 0

/-- The conditions of a segment are its two halves. -/
theorem holds_halves (S : Cb.SegSpec X F E) (Φ : Cb.IdxFmt F) (x : X) (W : ℕ → ℕ → F)
    (A : ℕ → ℕ → ℕ → E) : S.Holds Φ x W A ↔ IdnHold S Φ x W A ∧ KeysHold S Φ x W A :=
  Iff.rfl

/-- Gluing keeps the identities' half. The library has this for the two halves together
(glued_holds_iff in Cb/Req/ReqGlueProofsSeg.lean); the proof is the first half of that one. -/
theorem idn_glued_any {S : Cb.SegSpec X F E} {Φ : Cb.IdxFmt F} (h : S.WF Φ) (x : X)
    (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E) :
    IdnHold S.glued Φ x W A ↔ IdnHold S Φ x W A := by
  show (∀ f ∈ [Cb.Fam.glue (0 : E) S.idn], ∀ b < 2 ^ f.v, f.val Φ x W A b = 0) ↔ _
  rw [List.forall_mem_singleton]
  exact Cb.glue_zero_iff X F E S.idn Φ x W A h.1

end Half

/-! ## The library's segment -/

/-- The identities' half of the library's feed-forward segment of group g, before gluing, says that
all identities of the library's relation, by their names, vanish at the matrices read as a trace and
the embedding read in the index matrix. It is the field iff of the library's IdnOK
(Cm/TargetSegFF.lean). For all index matrices over the prime field and all matrices of cells. -/
theorem idn_ffSpec [scl : Scl] {X E : Type} [Field E] [Algebra Cb.Gl.F E]
    {Φ : Cb.IdxFmt Cb.Gl.F} {g : ℕ} {first : Bool} {tok : X → ℕ → ℕ} {idf : List (Cb.Fam X E)}
    (tb : Tables) (kf : Inst.Model.FFSeg.Fam → Cb.Fam X E)
    (hi : Cm.Seg.TS.IdnOK Φ g first tok idf) (x₀ : X) (W : ℕ → ℕ → Cb.Gl.F)
    (A : ℕ → ℕ → ℕ → E) :
    IdnHold (Cm.Seg.TS.ffSpec tb kf idf) Φ x₀ W A ↔
      ∀ j : Idn, j.Valid DF first →
        idnVal DF (Cm.Seg.tA g A) (Cm.Seg.TS.embOf W) (tok x₀) j = 0 :=
  hi.iff x₀ W A

/-- Segment 2 g of the library's model is well formed. -/
theorem wf_even (s : Cm.Scales) {g : ℕ} (hg : g < nGr) :
    (Cm.Seg.TS.segM s (2 * g)).WF Cm.Seg.TS.fmtRef := by
  rw [segM_even s hg]
  exact Cm.Seg.TS.ffSeg_wf _ s.kap s.nf g Cm.Seg.tokX hg

/-- The identities' half of segment 2 g of the library's model, before gluing. -/
theorem idn_seg (s : Cm.Scales) {g : ℕ} (hg : g < nGr) (x : Cm.Seg.XI) (W : ℕ → ℕ → Cb.Gl.F)
    (A : ℕ → ℕ → ℕ → Cb.Gl.E) :
    IdnHold (Cm.Seg.TS.segM s (2 * g)) Cm.Seg.TS.fmtRef x W A ↔
      ∀ j : Idn, j.Valid DF (decide (g = 0)) →
        idnVal (scl := SFK s.kap s.nf g) DF (Cm.Seg.tA g A) (Cm.Seg.TS.embOf W) (Cm.Seg.tokX x)
          j = 0 := by
  rw [segM_even s hg]
  unfold Cm.Seg.TS.ffSeg
  exact idn_ffSpec (scl := SFK s.kap s.nf g) _ _
    (Cm.Seg.TS.idn_ok (scl := SFK s.kap s.nf g) g Cm.Seg.tokX) x W A

/-- The same in glued form, which is the segment of the library's partition. -/
theorem idn_glued (s : Cm.Scales) {g : ℕ} (hg : g < nGr) (x : Cm.Seg.XI) (W : ℕ → ℕ → Cb.Gl.F)
    (A : ℕ → ℕ → ℕ → Cb.Gl.E) :
    IdnHold (Cm.Seg.TS.segM s (2 * g)).glued Cm.Seg.TS.fmtRef x W A ↔
      ∀ j : Idn, j.Valid DF (decide (g = 0)) →
        idnVal (scl := SFK s.kap s.nf g) DF (Cm.Seg.tA g A) (Cm.Seg.TS.embOf W) (Cm.Seg.tokX x)
          j = 0 :=
  (idn_glued_any (wf_even s hg) x W A).trans (idn_seg s hg x W A)

/-- The keys' half of segment 2 g of the library's model, before gluing: vecs_glued
(Johnson/Road/FormsKeysTie.lean) without the gluing. -/
theorem keys_seg (s : Cm.Scales) {g : ℕ} (hg : g < nGr) (x : Cm.Seg.XI) (W : ℕ → ℕ → Cb.Gl.F)
    (A : ℕ → ℕ → ℕ → Cb.Gl.E) :
    KeysHold (Cm.Seg.TS.segM s (2 * g)) Cm.Seg.TS.fmtRef x W A ↔
      ∀ c : Fin 8, ∀ X, X < 2 ^ aC DF c →
        keyVec (scl := SFK s.kap s.nf g) DF (Cm.Seg.tA g A) Inst.Model.tbRef (4 * g)
          (Cm.Seg.wOf g W) c X ∈ InT (E := Cb.Gl.E) Inst.Model.tbRef c :=
  (keys_glued (wf_even s hg) x W A).symm.trans (vecs_glued s hg x W A)

/-! ## Two tables of scales; two dictionaries -/

/-- Two tables of scales with the same words give the same identities. -/
theorem idn_scl {R : Type} [CommRing R] (s s' : Scl) (h : ∀ l, s.κ l = s'.κ l) (D : Dim)
    (t : Cell → R) (emb : ℕ → ℕ → R) (tok : ℕ → ℕ) (j : Idn) :
    idnVal (scl := s) D t emb tok j = idnVal (scl := s') D t emb tok j := by
  obtain ⟨κ, nf⟩ := s
  obtain ⟨κ', nf'⟩ := s'
  obtain rfl : κ = κ' := funext h
  cases j <;> rfl

/-- The identities in the two dictionaries, at casts of integers. If integer matrices M of the
library's hold, at the library's places of the valid names of cells of group g, the cells of the
integer matrices Mz, then an identity of the relation has one value on the cells of Mz and on the
library's reading of M; the embedding on both sides is read in one integer index matrix. By the
library's idn_congr over the integers. -/
theorem idn_dict [scl : Scl] {E : Type} [Field E] [Algebra Cb.Gl.F E] (y : Lay) (Mz : Mats ℤ)
    (Wi : Mat) (g : ℕ) (M : ℕ → ℕ → ℕ → ℤ)
    (hD : ∀ c : Cell, c.Valid DF → Cm.Seg.TS.tM g M c = cellsOf DF (cellsAt y Mz) c)
    (first : Bool) (tok : ℕ → ℕ) {j : Idn} (hj : j.Valid DF first) :
    idnVal DF (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : E))))
        (embR ppref kRef fun a b => ((Wi a b : ℤ) : E)) tok j =
      idnVal DF (Cm.Seg.tA g (Cb.Partition.castM (E := E) M))
        (Cm.Seg.TS.embOf (Cm.TP.castW Cb.Gl.p Wi)) tok j := by
  rw [Cm.Seg.TS.tA_castM, Cm.Seg.TS.embOf_cast, cells_cast, Inst.Model.FFSeg.embCast,
    Inst.Model.FFSeg.idn_cast, Inst.Model.FFSeg.idn_cast,
    Inst.Model.FFSeg.idn_congr (fun c hc => (hD c hc).symm) first _ tok hj]

/-! ## On the cells of matrices in the numbering of the verifier's list -/

/-- All identities of group g vanish on the cells of Mz, under the table of scales of these files,
exactly if the identities' half of segment 2 g of the library's model, before gluing, holds at the
integer index matrix and at integer matrices M that hold the cells of Mz at the library's places.
Asked besides: the words of the group's four layers are those of the library's table s. -/
theorem idn_end (y : Lay) (Mz : Mats ℤ) (Wi : Mat) {g : ℕ} (hg : g < nGr) (M : ℕ → ℕ → ℕ → ℤ)
    (hD : ∀ c : Cell, c.Valid DF → Cm.Seg.TS.tM g M c = cellsOf DF (cellsAt y Mz) c) (h : Shape)
    (sc : Scales) (s : Cm.Scales)
    (hw : ∀ l, l < 4 → wordsAt h sc (g * 4 + l) = s.kap (4 * g + l)) (x : Cm.Seg.XI) :
    (∀ j : Idn, j.Valid DF (decide (g = 0)) →
      idnVal (scl := sclOf h sc g 4) DF
          (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))))
          (embR ppref kRef fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (Cm.Seg.tokX x) j = 0) ↔
    IdnHold (Cm.Seg.TS.segM s (2 * g)) Cm.Seg.TS.fmtRef x (Cm.TP.castW Cb.Gl.p Wi)
      (Cb.Partition.castM (E := Cb.Gl.E) M) := by
  rw [idn_seg s hg]
  refine forall_congr' fun j => imp_congr_right fun hj => ?_
  rw [idn_scl (sclOf h sc g 4) (SFK s.kap s.nf g) (kap_sclOf h sc g s.kap hw s.nf),
    idn_dict (scl := SFK s.kap s.nf g) y Mz Wi g M hD _ _ hj]

/-- The keys' half likewise, before gluing: tie_end (Johnson/Road/FormsKeysTieE.lean) without the
gluing. -/
theorem keys_end (y : Lay) (Mz : Mats ℤ) (Wi : Mat) {g : ℕ} (hg : g < nGr) (M : ℕ → ℕ → ℕ → ℤ)
    (hD : ∀ c : Cell, c.Valid DF → Cm.Seg.TS.tM g M c = cellsOf DF (cellsAt y Mz) c) (h : Shape)
    (sc : Scales) (s : Cm.Scales)
    (hw : ∀ l, l < 4 → wordsAt h sc (g * 4 + l) = s.kap (4 * g + l)) (x : Cm.Seg.XI) :
    (∀ c : Fin 8, ∀ X, X < 2 ^ aC DF c →
      ∃ u ∈ (Cm.Seg.tabOf (lut Inst.Model.tbRef c) (if c = 3 then 8 else 16) :
          Cb.Tab Cb.Gl.F).set,
        keyVec (scl := sclOf h sc g 4) DF
            (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))))
            Inst.Model.tbRef (4 * g)
            (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * g + l)) c X =
          algebraMap Cb.Gl.F Cb.Gl.E u) ↔
    KeysHold (Cm.Seg.TS.segM s (2 * g)) Cm.Seg.TS.fmtRef x (Cm.TP.castW Cb.Gl.p Wi)
      (Cb.Partition.castM (E := Cb.Gl.E) M) :=
  (tie_end y Mz Wi hg M hD h sc s hw x).trans (keys_glued (wf_even s hg) x _ _)

/-- The whole conditions of segment 2 g of the library's model, before gluing, at integer matrices
M that hold the cells of Mz: all identities vanish on the cells of Mz, and all entries of the eight
key vectors on them are images of entries of the library's reference tables. -/
theorem holds_end (y : Lay) (Mz : Mats ℤ) (Wi : Mat) {g : ℕ} (hg : g < nGr) (M : ℕ → ℕ → ℕ → ℤ)
    (hD : ∀ c : Cell, c.Valid DF → Cm.Seg.TS.tM g M c = cellsOf DF (cellsAt y Mz) c) (h : Shape)
    (sc : Scales) (s : Cm.Scales)
    (hw : ∀ l, l < 4 → wordsAt h sc (g * 4 + l) = s.kap (4 * g + l)) (x : Cm.Seg.XI) :
    (Cm.Seg.TS.segM s (2 * g)).Holds Cm.Seg.TS.fmtRef x (Cm.TP.castW Cb.Gl.p Wi)
        (Cb.Partition.castM (E := Cb.Gl.E) M) ↔
    (∀ j : Idn, j.Valid DF (decide (g = 0)) →
      idnVal (scl := sclOf h sc g 4) DF
          (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))))
          (embR ppref kRef fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (Cm.Seg.tokX x) j = 0) ∧
    (∀ c : Fin 8, ∀ X, X < 2 ^ aC DF c →
      ∃ u ∈ (Cm.Seg.tabOf (lut Inst.Model.tbRef c) (if c = 3 then 8 else 16) :
          Cb.Tab Cb.Gl.F).set,
        keyVec (scl := sclOf h sc g 4) DF
            (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))))
            Inst.Model.tbRef (4 * g)
            (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * g + l)) c X =
          algebraMap Cb.Gl.F Cb.Gl.E u) :=
  (holds_halves _ _ _ _ _).trans
    (and_congr (idn_end y Mz Wi hg M hD h sc s hw x).symm
      (keys_end y Mz Wi hg M hD h sc s hw x).symm)

/-- The words of the table made from the verifier's scale file, for a group. -/
theorem words_file (h : Shape) (sc : Scales) (nf : Inst.Model.NormPar) {g : ℕ} (hg : g < nGr) :
    ∀ l, l < 4 → wordsAt h sc (g * 4 + l) = (scalesOf h sc nf).kap (4 * g + l) := fun l hl => by
  have hg' : g < 12 := hg
  rw [Nat.mul_comm g 4]
  exact kap_scalesOf h sc nf (by omega)

section Port

variable {h : Shape} {pc : List (List String)} {y : Lay} (hy : layout h pc = .ok y)
  (S : Switches h) (Z : Sized h DF) (Z2 : Sized2 h DF) (hp4 : h.p4 = true)

include hy S Z Z2 hp4

/-- One group, the identities' half in glued form, at the library's matrices libM y g Mz made from
Mz and the library's table of scales made from the verifier's scale file. -/
theorem idn_port_file (Mz : Mats ℤ) (Wi : Mat) {g : ℕ} (hg : g < nGr) (sc : Scales)
    (nf : Inst.Model.NormPar) (x : Cm.Seg.XI) :
    IdnHold (Cm.Seg.TS.segM (scalesOf h sc nf) (2 * g)).glued Cm.Seg.TS.fmtRef x
        (Cm.TP.castW Cb.Gl.p Wi) (Cb.Partition.castM (E := Cb.Gl.E) (libM y g Mz)) ↔
    (∀ j : Idn, j.Valid DF (decide (g = 0)) →
      idnVal (scl := sclOf h sc g 4) DF
          (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))))
          (embR ppref kRef fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (Cm.Seg.tokX x) j = 0) :=
  (idn_glued_any (wf_even _ hg) x _ _).trans
    (idn_end y Mz Wi hg (libM y g Mz) (fun c hc => dict_valid hy S Z Z2 hp4 g Mz c hc) h sc _
      (words_file h sc nf hg) x).symm

/-- One group, the whole conditions of the segment of the library's partition. -/
theorem holds_port_file (Mz : Mats ℤ) (Wi : Mat) {g : ℕ} (hg : g < nGr) (sc : Scales)
    (nf : Inst.Model.NormPar) (x : Cm.Seg.XI) :
    (Cm.Seg.TS.segM (scalesOf h sc nf) (2 * g)).glued.Holds Cm.Seg.TS.fmtRef x
        (Cm.TP.castW Cb.Gl.p Wi) (Cb.Partition.castM (E := Cb.Gl.E) (libM y g Mz)) ↔
    (∀ j : Idn, j.Valid DF (decide (g = 0)) →
      idnVal (scl := sclOf h sc g 4) DF
          (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))))
          (embR ppref kRef fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (Cm.Seg.tokX x) j = 0) ∧
    (∀ c : Fin 8, ∀ X, X < 2 ^ aC DF c →
      ∃ u ∈ (Cm.Seg.tabOf (lut Inst.Model.tbRef c) (if c = 3 then 8 else 16) :
          Cb.Tab Cb.Gl.F).set,
        keyVec (scl := sclOf h sc g 4) DF
            (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))))
            Inst.Model.tbRef (4 * g)
            (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * g + l)) c X =
          algebraMap Cb.Gl.F Cb.Gl.E u) :=
  (holds_halves _ _ _ _ _).trans
    (and_congr (idn_port_file hy S Z Z2 hp4 Mz Wi hg sc nf x)
      (tie_port_file hy S Z Z2 hp4 Mz Wi hg sc nf x).symm)

/-- All twelve groups at one list of the library's matrices, libOfA y Ma, made from integer
matrices Ma that are named by the labels of the verifier's plan: the whole conditions of the twelve
even segments of the library's partition. -/
theorem holds_lab_file (Ma : ℕ → ℕ → ℕ → ℤ) (Wi : Mat) (sc : Scales) (nf : Inst.Model.NormPar)
    (x : Cm.Seg.XI) :
    (∀ g, g < nGr →
      (Cm.Seg.TS.segM (scalesOf h sc nf) (2 * g)).glued.Holds Cm.Seg.TS.fmtRef x
        (Cm.TP.castW Cb.Gl.p Wi) (Cb.Partition.castM (E := Cb.Gl.E) (libOfA y Ma))) ↔
    ∀ g, g < nGr →
      (∀ j : Idn, j.Valid DF (decide (g = 0)) →
        idnVal (scl := sclOf h sc g 4) DF
            (cellsOf DF (cellsAt y (fun a r c => ((mzA y Ma g a r c : ℤ) : Cb.Gl.E))))
            (embR ppref kRef fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (Cm.Seg.tokX x) j = 0) ∧
      (∀ c : Fin 8, ∀ X, X < 2 ^ aC DF c →
        ∃ u ∈ (Cm.Seg.tabOf (lut Inst.Model.tbRef c) (if c = 3 then 8 else 16) :
            Cb.Tab Cb.Gl.F).set,
          keyVec (scl := sclOf h sc g 4) DF
              (cellsOf DF (cellsAt y (fun a r c => ((mzA y Ma g a r c : ℤ) : Cb.Gl.E))))
              Inst.Model.tbRef (4 * g)
              (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * g + l)) c X =
            algebraMap Cb.Gl.F Cb.Gl.E u) :=
  forall_congr' fun g => imp_congr_right fun hg =>
    (Cb.glued_holds_iff _ _ _ _ _ _ _ _ (wf_even _ hg)).trans
      (holds_end y (mzA y Ma g) Wi hg (libOfA y Ma)
        (fun c hc => dict_lab hy S Z Z2 hp4 Ma hg c hc) h sc _ (words_file h sc nf hg) x)

end Port

#print axioms holds_halves
#print axioms idn_glued_any
#print axioms idn_ffSpec
#print axioms wf_even
#print axioms idn_seg
#print axioms idn_glued
#print axioms keys_seg
#print axioms idn_scl
#print axioms idn_dict
#print axioms idn_end
#print axioms keys_end
#print axioms holds_end
#print axioms words_file
#print axioms idn_port_file
#print axioms holds_port_file
#print axioms holds_lab_file

end OnBytes.Road
