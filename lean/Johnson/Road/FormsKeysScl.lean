-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysScl.lean: the keys of a feed-forward segment read the layers' words of a
table of scales alone.

The library passes the table of quantization scales along as an instance (Scl in
Inst/Model/Scl.lean): κ l, the words of layer l of a segment, and nf, the constants of the final
normalisation. The theorems of these files stand under the table sclOf
(Johnson/Road/FormsKeysFits.lean), made from the verifier's scale file, whose nf is ⟨0, 0, 0⟩. The
library's condition on a group's keys (Cm.TP.CondL.ffKey in Cm/TargetPRel.lean) stands under SFK κ
nf g (Inst/Model/All/TraceK.lean), and the library's theorems on it ask a lawful table, whose nf
has eps at least 1. So for no lawful table are the two equal as records (they are equal at nf = ⟨0,
0, 0⟩, if the words agree). This file shows that this does not matter for the keys: they read κ
alone; and that the two κ agree as soon as the words of the group's four layers do.

What is compared with what. The first two sections: the library with itself, at two tables.
kap_sclOf, kap_scalesOf: the words that these files read in the verifier's scale file (wordsAt)
against the library's words. The last section: the library's key vectors on the verifier's cells
under sclOf, against the library's relation under SFK.

Main definitions: scalesOf (the library's KLFile.words on the records that fileOf of
Johnson/Road/FormsKeysWords.lean cuts out of the verifier's file by the verifier's own kl and klM;
the library reads no flat file; nf is free). Main theorems.
 - key_scl, lin_scl, term_scl, mat_scl, keyVec_scl, trace_key_scl, trace_table_scl: two tables with
   the same words give the same keys, parts of keys, key vectors, and keys and tables of the
   relation.
 - kap_sclOf: (sclOf h sc g 4).κ is (SFK κ nf g).κ, if wordsAt h sc (g 4 + l) = κ (4 g + l) for l <
   4.
 - kap_scalesOf: the table scalesOf has the words of wordsAt.
 - keyVecs_mem_iff_SFK; keyVecs_ffKey (the right side in the letters of Cm.TP.CondL.ffKey at g);
   keyVecs_ffKey_file.

Who reads the target. Cm.TP.CondL.ffKey is read by the library's theorems on the relation modulo p
(Cm/TargetPRel.lean) and, through ffSpec_holds_iff (Cm/TargetSegFF.lean), by its partition.

At which sizes. The first two sections: every Dim; every commutative ring for key, keyVec and the
relation's keys; every field for lin, term and mat, which the library defines over a field. The
last: DF, the library's Dim.ref, alone, and groups of four layers.

The hypotheses, and that they can be met.
 - the two tables have the same words: met by sclOf and SFK under hw (kap_sclOf).
 - hw: the words of the group's four layers, as wordsAt reads them, are κ's. Met for g < 12, with
   no further hypothesis, by κ := (scalesOf h sc nf).kap (kap_scalesOf, from wordsAt_eq of
   Johnson/Road/FormsKeysWords.lean): keyVecs_ffKey_file.
 - ht: the trace holds the integer cells: met by taking that for the trace.

What is not claimed. That scalesOf h sc nf is lawful is not shown: it depends on the file and on
nf. That the first layer g Lam of a group of the verifier is 4 g, that its tables are the reference
tables and its sizes the reference sizes is not shown here. That the two tables are equal as
records is not needed, and holds for no lawful table. The program does not import this file.
-/
import Johnson.Road.FormsKeysPass
import Johnson.Road.FormsKeysWords
import Inst.Model.FF.Objects

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model.Layer (Lay Shape Scales)
open Inst.Model (Scl Tables Lut Mat ppref LayerScale NormPar)
open Inst.Model.All (DF SFK kapG)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Dim Cell Fam LW key lin term mat keyVec layerR lut aC KeyName trace)

/-! ## Two tables with the same words -/

section Same

variable {R : Type} [CommRing R] (s s' : Scl) (h : ∀ l, s.κ l = s'.κ l) (D : Dim) (t : Cell → R)
  (tb : Tables) (L0 : ℕ) (w : ℕ → LW R)

include h

/-- A key. -/
theorem key_scl (f : Fam) (l x i : ℕ) :
    key (scl := s) D t tb L0 w f l x i = key (scl := s') D t tb L0 w f l x i := by
  obtain ⟨κ, nf⟩ := s
  obtain ⟨κ', nf'⟩ := s'
  obtain rfl : κ = κ' := funext h
  cases f <;> rfl

/-- The key vector of a call, at every index. -/
theorem keyVec_scl (c : Fin 8) (X : ℕ) :
    keyVec (scl := s) D t tb L0 w c X = keyVec (scl := s') D t tb L0 w c X := by
  unfold keyVec
  simp only [key_scl s s' h]

end Same

section Parts

variable {K : Type} [Field K] (s s' : Scl) (h : ∀ l, s.κ l = s'.κ l) (D : Dim) (t : Cell → K)
  (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)

include h

/-- The affine part of a key. -/
theorem lin_scl (f : Fam) (l x i : ℕ) :
    lin (scl := s) D t tb L0 w f l x i = lin (scl := s') D t tb L0 w f l x i := by
  obtain ⟨κ, nf⟩ := s
  obtain ⟨κ', nf'⟩ := s'
  obtain rfl : κ = κ' := funext h
  cases f <;> rfl

/-- The part of a key that is a sum of products of two values at the position. -/
theorem term_scl (f : Fam) (l x i : ℕ) :
    term (scl := s) D t tb L0 w f l x i = term (scl := s') D t tb L0 w f l x i := by
  obtain ⟨κ, nf⟩ := s
  obtain ⟨κ', nf'⟩ := s'
  obtain rfl : κ = κ' := funext h
  cases f <;> rfl

/-- The part of a key that is a matrix product. -/
theorem mat_scl (f : Fam) (l x i : ℕ) :
    mat (scl := s) D t w f l x i = mat (scl := s') D t w f l x i := by
  obtain ⟨κ, nf⟩ := s
  obtain ⟨κ', nf'⟩ := s'
  obtain rfl : κ = κ' := funext h
  cases f <;> rfl

end Parts

/-- The keys of the part of the field relation that belongs to the segment. -/
theorem trace_key_scl (s s' : Scl) (h : ∀ l, s.κ l = s'.κ l) (D : Dim) (tb : Tables) (kW L0 : ℕ)
    (first : Bool) (F : Type) [CommRing F] (tok : ℕ → ℕ) (W : ℕ → ℕ → F)
    (t' : {c : Cell // c.Valid D} → ℤ) (q : KeyName D) :
    (trace (scl := s) D tb kW L0 first F).key tok W t' q =
      (trace (scl := s') D tb kW L0 first F).key tok W t' q :=
  key_scl s s' h D _ tb L0 _ _ _ _ _

/-- Their tables read no scale. -/
theorem trace_table_scl (s s' : Scl) (D : Dim) (tb : Tables) (kW L0 : ℕ) (first : Bool)
    (F : Type) [CommRing F] (q : KeyName D) :
    (trace (scl := s) D tb kW L0 first F).table q =
      (trace (scl := s') D tb kW L0 first F).table q :=
  rfl

/-! ## The table of these files against the library's table of a group -/

/-- The words of the table sclOf for group g of four layers are those of the library's table of the
group, if the words of the group's four layers are. κ: the words of all layers of the model. -/
theorem kap_sclOf (h : Shape) (sc : Scales) (g : ℕ) (κ : ℕ → LayerScale)
    (hw : ∀ l, l < 4 → wordsAt h sc (g * 4 + l) = κ (4 * g + l)) (nf : NormPar) (l : ℕ) :
    (sclOf h sc g 4).κ l = (SFK κ nf g).κ l :=
  hw (l % 4) (Nat.mod_lt _ (by norm_num))

/-- A table of scales of the library: the library's KLFile.words on the records that fileOf
(Johnson/Road/FormsKeysWords.lean), a definition of these files, cuts out of the verifier's scale
file by the verifier's own kl and klM. The library reads no flat file. The final normalisation nf
is free: it is not taken from the file. -/
def scalesOf (h : Shape) (sc : Scales) (nf : NormPar) : Cm.Scales := ⟨(fileOf h sc).words, nf⟩

/-- Its words are those that wordsAt reads, in the 48 layers. -/
theorem kap_scalesOf (h : Shape) (sc : Scales) (nf : NormPar) {L : ℕ} (hL : L < 48) :
    wordsAt h sc L = (scalesOf h sc nf).kap L := by
  unfold Cm.Scales.kap
  rw [dif_pos hL]
  exact wordsAt_eq h sc ⟨L, hL⟩

/-! ## The key vectors under the table of these files, the relation under the library's -/

section Pass

variable {EE : Type} [Field EE] [Algebra Cb.Gl.F EE] (y : Lay) (Mz : Mats ℤ) (Wi : Mat)
  (t' : {c : Cell // c.Valid DF} → ℤ) (ht : ∀ c, t' c = cellsOf DF (cellsAt y Mz) c.val)

include ht

/-- keyVecs_mem_iff (Johnson/Road/FormsKeysPass.lean) with the key vectors under the table sclOf of
these files and the relation's clause under the library's table SFK κ nf g, for every final
normalisation nf. Asked: the words of the group's four layers are κ's. -/
theorem keyVecs_mem_iff_SFK (h : Shape) (sc : Scales) (g : ℕ) (κ : ℕ → LayerScale)
    (hw : ∀ l, l < 4 → wordsAt h sc (g * 4 + l) = κ (4 * g + l)) (nf : NormPar) (tb : Tables)
    (L0 : ℕ) (first : Bool) (tok : ℕ → ℕ) :
    (∀ c : Fin 8, ∀ X, X < 2 ^ aC DF c →
      ∃ u ∈ (Cm.Seg.tabOf (lut tb c) (if c = 3 then 8 else 16) : Cb.Tab Cb.Gl.F).set,
        keyVec (scl := sclOf h sc g 4) DF
            (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : EE)))) tb L0
            (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : EE)) (L0 + l)) c X =
          algebraMap Cb.Gl.F EE u) ↔
    ∀ q, (trace (scl := SFK κ nf g) DF tb kRef L0 first Cb.Gl.F).key tok
        (Cm.TP.castW Cb.Gl.p Wi) t' q ∈
      (trace (scl := SFK κ nf g) DF tb kRef L0 first Cb.Gl.F).table q := by
  rw [keyVecs_mem_iff (scl := sclOf h sc g 4) y Mz Wi t' ht tb L0 first tok]
  refine forall_congr' fun q => ?_
  rw [trace_key_scl (sclOf h sc g 4) (SFK κ nf g) (kap_sclOf h sc g κ hw nf)]
  rfl

/-- The same in the letters of the library's condition Cm.TP.CondL.ffKey at group g
(Cm/TargetPRel.lean): the reference tables, the first layer 4 g. -/
theorem keyVecs_ffKey (h : Shape) (sc : Scales) (g : ℕ) (κ : ℕ → LayerScale)
    (hw : ∀ l, l < 4 → wordsAt h sc (g * 4 + l) = κ (4 * g + l)) (nf : NormPar) (tok : ℕ → ℕ) :
    (∀ c : Fin 8, ∀ X, X < 2 ^ aC DF c →
      ∃ u ∈ (Cm.Seg.tabOf (lut Inst.Model.tbRef c) (if c = 3 then 8 else 16) :
          Cb.Tab Cb.Gl.F).set,
        keyVec (scl := sclOf h sc g 4) DF
            (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : EE)))) Inst.Model.tbRef (4 * g)
            (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : EE)) (4 * g + l)) c X =
          algebraMap Cb.Gl.F EE u) ↔
    ∀ k, (Cm.TP.segFF Cb.Gl.p κ nf g).key tok (Cm.TP.castW Cb.Gl.p Wi) t' k ∈
      (Cm.TP.segFF Cb.Gl.p κ nf g).table k :=
  keyVecs_mem_iff_SFK y Mz Wi t' ht h sc g κ hw nf Inst.Model.tbRef (4 * g) (decide (g = 0)) tok

/-- At the library's table made from the verifier's own scale file nothing is asked of the words,
for the twelve groups. -/
theorem keyVecs_ffKey_file (h : Shape) (sc : Scales) {g : ℕ} (hg : g < 12) (nf : NormPar)
    (tok : ℕ → ℕ) :
    (∀ c : Fin 8, ∀ X, X < 2 ^ aC DF c →
      ∃ u ∈ (Cm.Seg.tabOf (lut Inst.Model.tbRef c) (if c = 3 then 8 else 16) :
          Cb.Tab Cb.Gl.F).set,
        keyVec (scl := sclOf h sc g 4) DF
            (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : EE)))) Inst.Model.tbRef (4 * g)
            (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : EE)) (4 * g + l)) c X =
          algebraMap Cb.Gl.F EE u) ↔
    ∀ k, (Cm.TP.segFF Cb.Gl.p (scalesOf h sc nf).kap (scalesOf h sc nf).nf g).key tok
        (Cm.TP.castW Cb.Gl.p Wi) t' k ∈
      (Cm.TP.segFF Cb.Gl.p (scalesOf h sc nf).kap (scalesOf h sc nf).nf g).table k :=
  keyVecs_ffKey y Mz Wi t' ht h sc g _
    (fun l hl => by
      rw [Nat.mul_comm g 4]
      exact kap_scalesOf h sc nf (by omega)) _ tok

end Pass

#print axioms key_scl
#print axioms lin_scl
#print axioms term_scl
#print axioms mat_scl
#print axioms keyVec_scl
#print axioms trace_key_scl
#print axioms trace_table_scl
#print axioms kap_sclOf
#print axioms kap_scalesOf
#print axioms keyVecs_mem_iff_SFK
#print axioms keyVecs_ffKey
#print axioms keyVecs_ffKey_file

end OnBytes.Road
