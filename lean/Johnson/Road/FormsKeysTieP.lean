-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysTieP.lean: the key vectors on the verifier's cells against the keys' half of
the library's glued segment, at the library's matrices made from the verifier's.

Johnson/Road/FormsKeysTieE.lean carries the tie between the library's key vectors and its glued
families of keys to the key vectors on the verifier's cells, for any integer matrices of the
library's that hold those cells at the library's places. Johnson/Road/FormsKeysDict.lean makes such
matrices from the verifier's own list of matrices (libM for one group, libOf for all twelve) and
shows that they hold the cells (dict_valid, dict_all); Johnson/Road/FormsKeysDictA.lean does the
same for matrices named by the labels of the verifier's plan (libOfA, dict_lab). This file joins
the two.

What is compared with what. As in Johnson/Road/FormsKeysTieE.lean; the matrices on the right are
now definitions of these files, made from the matrices on the left.

Main theorems: tie_port (one group; the words of the scales asked); tie_port_file (one group, at
the library's table made from the verifier's scale file); tie_all_file (all twelve groups in one
list of matrices, given the seams); tie_lab_file (the same with the verifier's matrices named by
its plan's labels: nothing is asked at the seams).

Who reads the target. As in Johnson/Road/FormsKeysTie.lean. The laws admit and force read Cond
whole: all 25 segments, the identities' half too, and a bound on the cells: so nothing here reaches
the relation. The keys' half alone is read by the library's theorem on the lookup's claim before the
shift (ldPartKeys_holds in Cb/Part/LdPartLkpFam.lean), which the front of a segment and the law on
the multiplicities' bits use; no file of this library joins it with vecs_glued.

At which sizes. DF, the library's Dim.ref, alone; groups of four layers; the first layer 4 g; the
reference tables; the fields Cb.Gl.F and Cb.Gl.E.

The hypotheses, and that they can be met.
 - hy, S, Z, Z2, hp4: the verifier's layout returns y for the shape h; the eleven switches; the
   shape's sizes are the reference sizes; profile 4. Met together at the full public example:
   switchesK, sizedKF (theorems in Johnson/Road/FormsKeysRunK.lean), profile 4 by its definition;
   that the layout returns there is a run in that file.
 - g < nGr = 12.
 - hw in tie_port: met by s := scalesOf h sc nf: tie_port_file.
 - hseam in tie_all_file, for 0 < g < 12. No witness is given but matrices that are all 0. The
   verifier's list for a group has a number for the stream that comes in; from the second group on
   its plan marks that entry as the matrix to which the group before committed as its stream that
   goes out (tailsOf in OnBytes/Model/LayerPlan.lean; by reading, no theorem). These files give
   each group matrices of its own, so the two are two letters, and hseam says that they are one.
   tie_lab_file names the matrices by the plan's labels and needs no such hypothesis; that the
   labels are the plan's is labA_tails in Johnson/Road/FormsKeysDictA.lean; that the matrix with an
   earlier group's label is the one to which that group committed is not claimed.

What is not claimed. That the entries lie in the tables. That the entries of a run's matrices are
casts of integers, or that the seams hold in a run. That the verifier's first layer g Lam is 4 g,
its tables the reference tables, its field Cb.Gl.E. That Wi is a matrix to which anybody has
committed, or that the verifier reads its weights by the library's layerR. Anything on the
identities' halves, on the odd segments and the head, on the cells' size; libM is 0 at all segments
but two, and both libM and libOf read the verifier's matrices also at places where no cell stands.
The program does not import this file.
-/
import Johnson.Road.FormsKeysTieE
import Johnson.Road.FormsKeysDict
import Johnson.Road.FormsKeysDictA

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model.Layer (Lay Shape Scales layout)
open Inst.Model (Scl Tables Mat ppref)
open Inst.Model.All (DF nGr)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Cell keyVec layerR lut aC)

variable {h : Shape} {pc : List (List String)} {y : Lay} (hy : layout h pc = .ok y)
  (S : Switches h) (Z : Sized h DF) (Z2 : Sized2 h DF) (hp4 : h.p4 = true)

include hy S Z Z2 hp4

/-- One group. tie_end (Johnson/Road/FormsKeysTieE.lean) at the library's matrices libM y g Mz, made
from the verifier's integer matrices Mz (Johnson/Road/FormsKeysDict.lean): the hypothesis on the
matrices is dict_valid. -/
theorem tie_port (Mz : Mats ℤ) (Wi : Mat) {g : ℕ} (hg : g < nGr) (sc : Scales) (s : Cm.Scales)
    (hw : ∀ l, l < 4 → wordsAt h sc (g * 4 + l) = s.kap (4 * g + l)) (x : Cm.Seg.XI) :
    (∀ c : Fin 8, ∀ X, X < 2 ^ aC DF c →
      ∃ u ∈ (Cm.Seg.tabOf (lut Inst.Model.tbRef c) (if c = 3 then 8 else 16) :
          Cb.Tab Cb.Gl.F).set,
        keyVec (scl := sclOf h sc g 4) DF
            (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)))) Inst.Model.tbRef
            (4 * g) (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * g + l))
            c X =
          algebraMap Cb.Gl.F Cb.Gl.E u) ↔
    KeysHold (Cm.Seg.TS.segM s (2 * g)).glued Cm.Seg.TS.fmtRef x (Cm.TP.castW Cb.Gl.p Wi)
      (Cb.Partition.castM (E := Cb.Gl.E) (libM y g Mz)) :=
  tie_end y Mz Wi hg (libM y g Mz) (fun c hc => dict_valid hy S Z Z2 hp4 g Mz c hc) h sc s hw x

/-- One group, at the library's table of scales made from the verifier's own scale file: nothing is
asked of the words. -/
theorem tie_port_file (Mz : Mats ℤ) (Wi : Mat) {g : ℕ} (hg : g < nGr) (sc : Scales)
    (nf : Inst.Model.NormPar) (x : Cm.Seg.XI) :
    (∀ c : Fin 8, ∀ X, X < 2 ^ aC DF c →
      ∃ u ∈ (Cm.Seg.tabOf (lut Inst.Model.tbRef c) (if c = 3 then 8 else 16) :
          Cb.Tab Cb.Gl.F).set,
        keyVec (scl := sclOf h sc g 4) DF
            (cellsOf DF (cellsAt y (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)))) Inst.Model.tbRef
            (4 * g) (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * g + l))
            c X =
          algebraMap Cb.Gl.F Cb.Gl.E u) ↔
    KeysHold (Cm.Seg.TS.segM (scalesOf h sc nf) (2 * g)).glued Cm.Seg.TS.fmtRef x
      (Cm.TP.castW Cb.Gl.p Wi) (Cb.Partition.castM (E := Cb.Gl.E) (libM y g Mz)) :=
  tie_end_file y Mz Wi hg (libM y g Mz) (fun c hc => dict_valid hy S Z Z2 hp4 g Mz c hc) h sc nf x

/-- All twelve groups in one list of the library's matrices, libOf y Mz, made from the integer
matrices Mz g of the twelve layer sub-proofs. Asked: at each seam, the matrix of the stream that
comes into group g holds what the matrix of the stream that goes out of group g - 1 holds. -/
theorem tie_all_file (Mz : ℕ → Mats ℤ) (Wi : Mat)
    (hseam : ∀ g, g < nGr → 0 < g → Seam y Mz g) (sc : Scales) (nf : Inst.Model.NormPar)
    (x : Cm.Seg.XI) :
    (∀ g, g < nGr → (∀ c : Fin 8, ∀ X, X < 2 ^ aC DF c →
        ∃ u ∈ (Cm.Seg.tabOf (lut Inst.Model.tbRef c) (if c = 3 then 8 else 16) :
            Cb.Tab Cb.Gl.F).set,
          keyVec (scl := sclOf h sc g 4) DF
              (cellsOf DF (cellsAt y (fun a r c => ((Mz g a r c : ℤ) : Cb.Gl.E)))) Inst.Model.tbRef
              (4 * g) (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * g + l))
              c X =
            algebraMap Cb.Gl.F Cb.Gl.E u)) ↔
    ∀ g, g < nGr →
      KeysHold (Cm.Seg.TS.segM (scalesOf h sc nf) (2 * g)).glued Cm.Seg.TS.fmtRef x
        (Cm.TP.castW Cb.Gl.p Wi) (Cb.Partition.castM (E := Cb.Gl.E) (libOf y Mz)) :=
  forall_congr' fun g => imp_congr_right fun hg =>
    tie_end_file y (Mz g) Wi hg (libOf y Mz)
      (fun c hc => dict_all hy S Z Z2 hp4 Mz g (hseam g hg) c hc) h sc nf x

/-- All twelve groups in one list of the library's matrices, without a hypothesis on the seams. The
verifier's matrices are named by the labels of its plan (labA, mzA, libOfA in
Johnson/Road/FormsKeysDictA.lean): the stream that comes into a later group has the label of the
stream that goes out of the group before, so the two are one matrix of Ma by definition. -/
theorem tie_lab_file (Ma : ℕ → ℕ → ℕ → ℤ) (Wi : Mat) (sc : Scales) (nf : Inst.Model.NormPar)
    (x : Cm.Seg.XI) :
    (∀ g, g < nGr → (∀ c : Fin 8, ∀ X, X < 2 ^ aC DF c →
        ∃ u ∈ (Cm.Seg.tabOf (lut Inst.Model.tbRef c) (if c = 3 then 8 else 16) :
            Cb.Tab Cb.Gl.F).set,
          keyVec (scl := sclOf h sc g 4) DF
              (cellsOf DF (cellsAt y (fun a r c => ((mzA y Ma g a r c : ℤ) : Cb.Gl.E))))
              Inst.Model.tbRef (4 * g)
              (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * g + l))
              c X =
            algebraMap Cb.Gl.F Cb.Gl.E u)) ↔
    ∀ g, g < nGr →
      KeysHold (Cm.Seg.TS.segM (scalesOf h sc nf) (2 * g)).glued Cm.Seg.TS.fmtRef x
        (Cm.TP.castW Cb.Gl.p Wi) (Cb.Partition.castM (E := Cb.Gl.E) (libOfA y Ma)) :=
  forall_congr' fun g => imp_congr_right fun hg =>
    tie_end_file y (mzA y Ma g) Wi hg (libOfA y Ma)
      (fun c hc => dict_lab hy S Z Z2 hp4 Ma hg c hc) h sc nf x

#print axioms tie_port
#print axioms tie_port_file
#print axioms tie_all_file
#print axioms tie_lab_file

end OnBytes.Road
