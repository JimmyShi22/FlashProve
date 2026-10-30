-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysLinkW.lean: the order of a group of layers is not empty.

Johnson/Road/FormsKeysLinkL.lean names three statements on the integer matrices behind the
sub-proof of a group of layers, numbered as the verifier's list numbers them (LayerOrd: they are
small; all identities vanish on their cells; all entries of the eight key vectors lie in the
library's reference tables) and shows that they put the group's link in order. No theorem concludes
the three from a proof file. This file shows that they can hold together: it goes backwards, from
the matrices of the library's honest trace to a list in the verifier's numbering.

What is compared with what. As in Johnson/Road/FormsKeysIdn.lean. The list is read out of the
library's matrices by a definition of these files (backM in Johnson/Road/FormsKeysDictB.lean). No
run of the verifier or of a prover stands behind it.

Main theorems: layerOrd_of_holds; layerOrd_true; layerOrd_met; layerOrd_met_kit.

Who reads the target. LayerOrd is the hypothesis of linkOK_layer
(Johnson/Road/FormsKeysLinkL.lean). The theorems here are witnesses: nobody needs to read them.

At which sizes. DF, the library's Dim.ref, alone; all else as in Johnson/Road/FormsKeysLinkE.lean.
layerOrd_met_kit: the shape, the scale words and the final norm of the full public example.

The hypotheses, and that they can be met. hy, S, Z, Z2, hp4: see Johnson/Road/FormsKeysTieP.lean.
hs, the table made from the scale file is lawful: a theorem at the full public example
(lawful_words in Johnson/Road/FormsKeysLaw.lean). ht, the request is true: next_true_exists
(Johnson/Road/HeadTop.lean). In layerOrd_met_kit hy alone is left: that the layout returns at that
shape is a run (Johnson/Road/FormsKeysRunK.lean).

What is not claimed. The witness has all weights 0 and all tokens 0: it shows that the three
statements are not contradictory, and no more. That the list read out of the honest trace is what
an honest prover commits to. Anything on a proof file. The program does not import this file.
-/
import Johnson.Road.FormsKeysLinkL
import Johnson.Road.FormsKeysDictB
import Johnson.Road.FormsKeysLaw
import Johnson.Road.HeadTop
import Cm.TargetSegModelProofs

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model.Layer (Lay Shape Scales layout)
open Inst.Model (Mat ppref Instance)
open Inst.Model.All (DF nGr)
open Inst.Model.FFSeg (Cell)

/-- From the library's numbering to that of the verifier's list. If the conditions of segment 2 g
of the library's model hold at integer matrices A, and integer matrices Mz that are small inside
the shapes of the list hold at their cells what A holds at the library's places, then the group is
in order at Mz. Asked besides: the words of the group's four layers are those of the library's
table s. -/
theorem layerOrd_of_holds (y : Lay) (Mz : Mats ℤ) (Wi : Mat) {g : ℕ} (hg : g < nGr)
    (A : ℕ → ℕ → ℕ → ℤ)
    (hD : ∀ c : Cell, c.Valid DF → Cm.Seg.TS.tM g A c = cellsOf DF (cellsAt y Mz) c) (h : Shape)
    (sc : Scales) (s : Cm.Scales)
    (hw : ∀ l, l < 4 → wordsAt h sc (g * 4 + l) = s.kap (4 * g + l)) (x : Cm.Seg.XI)
    (hS : SmallM y Mz)
    (H : (Cm.Seg.TS.segM s (2 * g)).Holds Cm.Seg.TS.fmtRef x (Cm.TP.castW Cb.Gl.p Wi)
      (Cm.Seg.TS.cM A)) :
    LayerOrd h sc y g Mz Wi x :=
  ⟨hS, ((holds_cM y Mz Wi hg A hD h sc s hw x).mp H).1,
    ((holds_cM y Mz Wi hg A hD h sc s hw x).mp H).2⟩

section Port

variable {h : Shape} {pc : List (List String)} {y : Lay} (hy : layout h pc = .ok y)
  (S : Switches h) (Z : Sized h DF) (Z2 : Sized2 h DF) (hp4 : h.p4 = true)

include hy S Z Z2 hp4

/-- At a lawful table made from the scale file, and a true request: every group is in order at the
list of matrices, in the verifier's numbering, read out of the matrices of the library's honest
trace (backM in Johnson/Road/FormsKeysDictB.lean). -/
theorem layerOrd_true (sc : Scales) (nf : Inst.Model.NormPar) (hs : (scalesOf h sc nf).Lawful)
    (i : Cm.Idx) (x : Instance ppref)
    (ht : Cm.TrueAt (scalesOf h sc nf).kap (scalesOf h sc nf).nf i x) {g : ℕ} (hg : g < nGr) :
    LayerOrd h sc y g
      (backM y g (Cm.Seg.toMat Cm.Seg.Hd.plain (Cm.trace2 (scalesOf h sc nf) i x))) i.mat x := by
  have H := (Cm.Seg.TS.model_true (scalesOf h sc nf) hs i x).2 ht
  have hg' : g < 12 := hg
  refine layerOrd_of_holds y _ i.mat hg _ (fun c hc => dict_back hy S Z Z2 hp4 g _ c hc) h sc _
    (words_file h sc nf hg) x
    (small_back hy S Z2 hg' fun q hq => lt_trans (H.1 q hq) (by norm_num)) (H.2 (2 * g) ?_)
  show 2 * g < 25
  omega

/-- The order is not empty: at a lawful table made from the scale file there are an index, a request
for the next token and lists of matrices at which all twelve groups are in order. -/
theorem layerOrd_met (sc : Scales) (nf : Inst.Model.NormPar)
    (hs : (scalesOf h sc nf).Lawful) :
    ∃ (i : Cm.Idx) (x : Instance ppref) (Mz : ℕ → Mats ℤ), x.r = 1023 ∧ x.e = 1024 ∧
      ∀ g, g < nGr → LayerOrd h sc y g (Mz g) i.mat x := by
  obtain ⟨i, x, hr, he, ht⟩ := Hd.Top.next_true_exists hs
  exact ⟨i, x, _, hr, he, fun g hg => layerOrd_true hy S Z Z2 hp4 sc nf hs i x ht hg⟩

end Port

/-- At the full public example, its scale words and its final norm: the only hypothesis left is that
the verifier's layout returns. -/
theorem layerOrd_met_kit {pc : List (List String)} {y : Lay} (hy : layout hKF pc = .ok y) :
    ∃ (i : Cm.Idx) (x : Instance ppref) (Mz : ℕ → Mats ℤ), x.r = 1023 ∧ x.e = 1024 ∧
      ∀ g, g < nGr → LayerOrd hKF scKF y g (Mz g) i.mat x :=
  layerOrd_met hy switchesK.2 sizedKF.1 sizedKF.2 rfl scKF nfKF lawful_words

#print axioms layerOrd_of_holds
#print axioms layerOrd_true
#print axioms layerOrd_met
#print axioms layerOrd_met_kit

end OnBytes.Road
