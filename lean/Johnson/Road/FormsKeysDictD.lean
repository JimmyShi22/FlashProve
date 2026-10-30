-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysDictD.lean: at every place that a feed-forward segment may read, the layers'
own dictionary for one group is the one dictionary by labels.

The links of the three kinds are shown in order at dictionaries of their own. For the feed-forward
segment of group g that is libMZ y g (mzA y Z g) (Johnson/Road/FormsKeysDictZ.lean,
Johnson/Road/FormsKeysDictA.lean): the matrices with the labels of group g, cut to their shapes, and
the stream that comes in laid where the library reads it. The seam between the links is shown at one
dictionary for all segments, D5 (Johnson/Road/HeadDict.lean). The two differ where no cell stands.
Johnson/Road/Lane5Congr.lean shows that a link in order at one family of matrices is in order at
every family that agrees with it at the places which the segment may read. This file shows that
agreement.

What is compared with what: definitions of these files with each other, at the places of the
library's own set reads (Cm/SegLayout.lean).

Main theorem: dict_D5.

The hypotheses: those of dict_valid (Johnson/Road/FormsKeysDict.lean, whose head says where they are
met: at the full-size example alone), and g < 12. The head's shape, the library's letter for the
kind of head, the matrices of attention and the matrices Z are free letters.

What is not claimed. Nothing at places that the segment may not read. What the heads of the files
named above do not claim is not claimed here. The program does not import this file.
-/
import Johnson.Road.FormsKeysDictZ
import Johnson.Road.HeadDict

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model.Layer (Lay layout)
open Inst.Model.All (DF)
open Cm.Seg (at' ownFF)

/-- At every place that the feed-forward segment of group g may read, the layers' dictionary for the
group, at the matrices with the group's labels, holds what the one dictionary by labels holds. -/
theorem dict_D5 {h : Model.Layer.Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) (S : Switches h) (Z : Sized h DF) (Z2 : Sized2 h DF)
    (hp4 : h.p4 = true) (hH : Model.Head.Shape) (hd : Cm.Seg.Hd) (At Zm : ℕ → ℕ → ℕ → ℤ) {g : ℕ}
    (hg : g < 12) :
    ∀ q ∈ Cm.Seg.reads hd (2 * g),
      at' (libMZ y g (mzA y Zm g)) q = at' (Hd.D5 hH y At Zm) q := by
  intro q hq
  have p19 : (2 : ℕ) ^ 19 = 524288 := by norm_num
  rcases hq with ⟨g', c, e, -, hc, rfl⟩ | ⟨g', c, e, -⟩ | ⟨e, -⟩
  · obtain rfl : g' = g := by omega
    have C := cut_at hy S Z Z2 hp4 g' c hc
    have e1 : at' (libMZ y g' (mzA y Zm g')) (ownFF g' c).place =
        at' (libOfA y Zm) (ownFF g' c).place :=
      (dict_mz hy S Z Z2 hp4 g' (mzA y Zm g') c hc).trans (dict_lab hy S Z Z2 hp4 Zm hg c hc).symm
    rw [e1]
    generalize (ownFF g' c).place = p at C ⊢
    show libOfA y Zm p.1 p.2.1 p.2.2 = Hd.D5 hH y At Zm p.1 p.2.1 p.2.2
    rcases C with ⟨a, ⟨b, -, -⟩, -⟩ | ⟨a, b, -⟩
    · exact (Hd.D5_libOfA hH y At Zm (by omega) (by omega) (by omega) _).symm
    · exact (Hd.D5_libOfA hH y At Zm (by omega) (by omega) (by omega) _).symm
  · omega
  · omega

#print axioms dict_D5

end OnBytes.Road
