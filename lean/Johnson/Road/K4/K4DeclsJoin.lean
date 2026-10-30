-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4DeclsJoin.lean: from the equation of Johnson/Road/K4/K4Decls.lean to THE JOIN
(Joined, Johnson/Desc/Reads/DeclRow.lean) of each read that the layers' own rounds declare: at every
entry of a declared read the smallness test's table has the make's cells and the declared weights.

  `hsz_of_lens`: the test on lengths (lensB) says of a list that lies in the third vector that every
    array of weights is as long as its run.
  `asks_kinds`: a family of tableAsks has one part, or it is af's or ad's with that matrix's parts.
  `asks_fit`: so, at the list of matrices that tailsOf makes, each part of a family has the rows
    and columns of its first part.
  `k4_joined`: the join of each declaration d of the list, from the equation, under PartsFit and
    Whole of d.
  `k4_joined_hear`: at a hearing, at the sizes and weights of the row (sizeU3, phiU3).
No new argument: tables_of_funs and joined_of_tables (Johnson/Desc/Reads/: DeclRow.lean, Join.lean).
Limits. PREMISES THAT STAY in k4_joined_hear: the test on lengths says yes of o.funs (lensB: a
premise; who pays it is not said here); the plan's list of matrices is
what tailsOf makes, and g is a group of the layout; the record tl of the smallness test has that
list's rows and columns; for each declaration: PartsFit's first half (its parts lie in the record)
and Whole (the run is not empty; the make fits: for a long family two equations on L, T and the
rows; for the planes' three: the run is the column). NOT HERE: the address of a use. Met through
Lean at no member. Nothing on soundness.


-/
import Johnson.Road.K4.K4Decls
import Johnson.Desc.Reads.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Lay Reads TableAsk TableAt layParts layTables tableAsks phiOf funsOf Pub
  Own HPlan2 pointsOf tailsOf matIx)
open OnBytes.Desc.First.K4 (engFl hear)
open VerifiableInference.Reads
open Cb.Pv.Tail (TSize)

/-- The test on lengths, of a list that lies in the third vector. -/
theorem hsz_of_lens {funs : Array HFun} (ht : ∀ Fn ∈ funs.toList, Fn.tree = 2)
    (hB : lensB funs = true) : ∀ Fn ∈ funs.toList, Fn.phi.size = Fn.len := by
  intro Fn hF
  have h1 : Fn ∈ u3Tabs funs := List.mem_filter.mpr ⟨hF, by rw [ht Fn hF]; rfl⟩
  exact beq_iff_eq.mp (List.all_eq_true.mp hB Fn h1)

/-- A family has one part, or it is af's or ad's. -/
theorem asks_kinds (y : Lay) (rd : Reads) (g : ℕ) : ∀ a ∈ tableAsks y rd g,
    a.parts = 1 ∨ (a.M0 = firstM y 0 ∧ a.parts = partsM y 0) ∨
      (a.M0 = firstM y 1 ∧ a.parts = partsM y 1) := by
  intro a ha
  unfold tableAsks at ha
  simp only [List.mem_append] at ha
  rcases ha with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h)
  · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h
    exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h
    exact Or.inl rfl
  · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h
    exact Or.inl rfl
  · split at h
    · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h
      exact Or.inl rfl
    · exact absurd h List.not_mem_nil
  · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h
    exact Or.inl rfl
  · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h
    exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h
    exact Or.inl rfl
  · split at h
    · obtain ⟨n, _, rfl⟩ := List.mem_map.mp h
      exact Or.inl rfl
    · exact absurd h List.not_mem_nil
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> exact Or.inl rfl

/-- At tailsOf's list each part of a family has the rows and columns of the first. -/
theorem asks_fit (y : Lay) (rd : Reads) {g : ℕ} (hg : g < y.NGr) : ∀ a ∈ tableAsks y rd g,
    ∀ q, q < a.parts → (matsR y g).getD (a.M0 + q) (0, 0) = (matsR y g).getD a.M0 (0, 0) := by
  intro a ha q hq
  rcases asks_kinds y rd g a ha with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain rfl : q = 0 := by omega
    rfl
  · rw [h1]
    rw [h2] at hq
    rw [tails_pair y hg (by omega) hq]
    exact (tails_pair y hg (mat := 0) (p := 0) (by omega) (by omega)).symm
  · rw [h1]
    rw [h2] at hq
    rw [tails_pair y hg (by omega) hq]
    exact (tails_pair y hg (mat := 1) (p := 0) (by omega) (by omega)).symm

/-- **The join of a declared read**, from the equation. -/
theorem k4_joined {K : Type} {tl : HTailF2} {funs : Array HFun} {ds : List (ReadDecl E)}
    (val : E → K) (h : FunsAre (sizeU3 tl funs) funs ds) {d : ReadDecl E} (hd : d ∈ ds)
    (hF : PartsFit (sizeU3 tl funs) d)
    (hW : d.Whole ((sizeU3 tl funs).m d.mat) ((sizeU3 tl funs).k d.mat)) :
    Joined (sizeU3 tl funs) (phiU3 val funs) val d :=
  joined_of_tables (tables_of_funs val h).1 hd hF hW

/-- **The equation and the join at a hearing**, at the row's sizes and weights. -/
theorem k4_joined_hear {K : Type} {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard}
    {F G : Fork} {t u : Tape} {o : Own} (h : hear engFl P hp g fo F t = some (o, G, u))
    (val : E → K) (tl : HTailF2) (hT : P.tails = tailsOf P.y) (hg : g < P.y.NGr)
    (htl : ∀ i, (matsR P.y g).getD i (0, 0) = ((tl.mats.getD i {}).m, (tl.mats.getD i {}).k))
    (hB : lensB o.funs = true) :
    ∃ pts ds, pointsOf P.y o.H o.hd o.hd2 = some pts ∧
      k4Decls P.y fo pts (matsR P.y g) (tableAsks P.y P.rd g) 0 = some ds ∧
      FunsAre (sizeU3 tl o.funs) o.funs ds ∧
      ∀ d ∈ ds, PartsFit (sizeU3 tl o.funs) d →
        d.Whole ((sizeU3 tl o.funs).m d.mat) ((sizeU3 tl o.funs).k d.mat) →
        Joined (sizeU3 tl o.funs) (phiU3 val o.funs) val d := by
  have e10 := (Desc.First.K4.hear_public h).2.2
  obtain ⟨iU3, tab, laid, nU3, TS, claimsP, pts0, hd2, _, _, _, _, _, _, _, _, _, e10⟩ := e10
  have htree := (OnBytes.Tie.Pv.Tail.Closed.funs_shapes e10).2
  have hm : ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) = matsR P.y g := by
    rw [hT]
    rfl
  obtain ⟨pts, ds, h1, h2, h3⟩ := k4_funsAre_hear h (sizeU3 tl o.funs)
    (by rw [hm]; exact htl) (by rw [hm]; exact asks_fit P.y P.rd hg) (hsz_of_lens htree hB)
  rw [hm] at h2
  exact ⟨pts, ds, h1, h2, h3, fun d hd hF hW => k4_joined val h3 hd hF hW⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.hsz_of_lens
#print axioms OnBytes.Road.K4.asks_kinds
#print axioms OnBytes.Road.K4.asks_fit
#print axioms OnBytes.Road.K4.k4_joined
#print axioms OnBytes.Road.K4.k4_joined_hear
