-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadSeam24.lean: at every place that segment 24 of the library's model may read, the
family of matrices that is filled from the output head's list alone is the dictionary D5.

Johnson/Road/HeadL5.lean fills the library's family of matrices from the list of the head's
sub-proof alone (headMx). Johnson/Road/HeadDict.lean fills it from matrices that are named by the
labels of the verifier's plans (D5). The two differ: in a feed-forward segment headMx has the head's
copy of the stream in every slot. This file shows that they agree wherever the conditions of segment
24 may read (Cm.Seg.reads in Cm/SegLayout.lean): at the places of the head's own cells, and at the
places in slot 7 of segment 22 under which the head reads the stream.

What is compared with what: two definitions of these files, at the places that the library names.

Main theorems: headMx_D5.

The hypotheses: twelve groups of layers. The library's shape hd of the head is any.

What is not claimed. Nothing on what the matrices hold. The program does not import this file.
-/
import Johnson.Road.HeadDict
import Cm.SegLayoutProofs

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open OnBytes.Model.Layer (Lay)
open Cm.Seg (at' reads)

/-- **Where segment 24 may read, headMx at the head's list read by labels is D5.** At: any
letter. -/
theorem headMx_D5 (hd : Cm.Seg.Hd) (h : Model.Head.Shape) {y : Lay} (h12 : y.NGr = 12)
    (At Z : ℕ → ℕ → ℕ → ℤ) :
    ∀ q ∈ reads hd 24, at' (headMx h y (mzH h y Z)) q = at' (D5 h y At Z) q := by
  intro q hq
  rcases hq with ⟨g, c, e, hg, hc, rfl⟩ | ⟨g, c, e, hg, hc, rfl⟩ | ⟨-,
    ⟨n, hn, hn24, rfl⟩ | ⟨φ, i, hφ, hi, rfl⟩⟩
  · rw [Cm.Seg.nGr_eq] at hg
    omega
  · omega
  · unfold Cm.Seg.at'
    rw [hn24]
    exact (D5_headMx_24 h y At Z _ _).symm
  · rw [place_x]
    rw [Cm.Seg.nFeat_x] at hφ
    rw [Cm.Seg.nT_eq] at hi
    have hrow : ((7 + φ / 64 / 5990) * 65536 + (φ % 64 * 2 ^ 10 + i)) / 65536 = 7 := by
      have e10 : (2 : ℕ) ^ 10 = 1024 := by norm_num
      rw [e10]
      omega
    have key := D5_headMx_22 h h12 At Z hrow (φ / 64 % 5990)
    unfold Cm.Seg.at'
    dsimp only
    exact key.symm

#print axioms headMx_D5

end OnBytes.Road.Hd
