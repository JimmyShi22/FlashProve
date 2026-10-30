-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5Congr.lean

"A link is in order" depends on the matrices only at the places that its segment may read; and how
links that are shown in order at dictionaries of their own are put together.

Why. The three kinds of link are shown in order at three dictionaries, each from the arrays of a
link's own sub-proof to the library's places ("libMZ", "attMx", "Hd.headMx"); the seam is shown at a
fourth, by labels ("Hd.D5"). They differ where no cell stands. This file makes that harmless, once
for all kinds.

Main theorems:
* "own_reads": the place of a cell lies among the places that its own segment may read.
* "linkOK_congr": if two families of matrices agree at every place that segment k may read, a link
  that is in order at the one is in order at the other ("Cb.Req.holds_congr").
* "premise_of_links": if every link k is in order at matrices "B k" of its own, and "B k" agrees
  with "A k" at every place that segment k may read, and the seam holds of A, then the premise holds
  of A. (Lane5Top.lean uses "linkOK_congr" directly.)

Not claimed: all that Lane5.lean does not claim. It imports Lane5.lean alone.
-/
import Johnson.Road.Lane5

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

variable {h : Cm.Seg.Hd} {seg : Segs} {Wz : Mat} {x : Instance ppref}

/-- **The place of a cell lies among the places that its own segment may read.** -/
theorem own_reads {n : Cm.Seg.Name} (hn : n.Valid h) : n.place ∈ Cm.Seg.reads h n.place.1 := by
  cases n with
  | ff g c => exact Or.inl ⟨g, c, rfl, hn.1, hn.2.1, by rw [Cm.Seg.ownFF_own hn.2.2]⟩
  | att g c => exact Or.inr (Or.inl ⟨g, c, rfl, hn.1, hn.2.1, by rw [Cm.Seg.ownAtt_own hn.2.2]⟩)
  | hf φ i => exact Or.inr (Or.inr ⟨rfl, Or.inl ⟨_, hn, rfl, rfl⟩⟩)
  | hd φ i => exact Or.inr (Or.inr ⟨rfl, Or.inl ⟨_, hn, rfl, rfl⟩⟩)
  | hr φ i => exact Or.inr (Or.inr ⟨rfl, Or.inl ⟨_, hn, rfl, rfl⟩⟩)

/-- **"In order" reads the matrices at the places that the segment may read, and nowhere else.** -/
theorem linkOK_congr (L : SegLaws h seg) {k : ℕ} (hk : k < Cm.Seg.nSeg) {A A' : Mx}
    (hA : ∀ q ∈ Cm.Seg.reads h k, Cm.Seg.at' A q = Cm.Seg.at' A' q)
    (H : LinkOK h seg Wz x k A) : LinkOK h seg Wz x k A' :=
  linkOK_of_holds
    (fun n hn e => by
      have hq : n.place ∈ Cm.Seg.reads h k := e ▸ own_reads hn
      rw [← hA n.place hq]
      exact H.small n hn e)
    (Cb.Req.holds_congr (L.wf k hk)
      (fun q hq => congrArg (fun z : ℤ => (z : Cb.Gl.E)) (hA q (L.places k hk q hq))) H.holds)

/-- **Links that are in order at dictionaries of their own, put together.** -/
theorem premise_of_links (L : SegLaws h seg) {A B : ℕ → Mx}
    (hB : ∀ k < Cm.Seg.nSeg, LinkOK h seg Wz x k (B k))
    (hAB : ∀ k < Cm.Seg.nSeg, ∀ q ∈ Cm.Seg.reads h k, Cm.Seg.at' (B k) q = Cm.Seg.at' (A k) q)
    (hS : ∀ k < Cm.Seg.nSeg, ∀ q ∈ Cm.Seg.reads h k,
      Cm.Seg.at' (A k) q = Cm.Seg.at' (A q.1) q) : Premise h seg Wz x A :=
  ⟨fun k hk => linkOK_congr L hk (hAB k hk) (hB k hk), hS⟩

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.own_reads
#print axioms OnBytes.Road.L5.linkOK_congr
#print axioms OnBytes.Road.L5.premise_of_links
