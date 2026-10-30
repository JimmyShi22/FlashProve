-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/ReadsLaw.lean: the law of the reads, from the relation that stands in front of the
draw of the smallness test's matrix.

Many statements on a sub-proof's claims take the law of the reads as a hypothesis on a world
(Fo.ReadsAll, OnBytes/Tie/Pv/Lookup/Ends/FoKeys.lean): each entry of a table in the vector of reads
is the combination of its matrix's cells under the table's weights. The proved block of the
smallness test has that content in its first joint (relIn, Cb/Pv/Tail/Block.lean); the library says
it table by table at the verifier's own record (reads_at, OnBytes/Tie/Pv/Tail/LettersAt.lean) and in
the world of the committed entries (holds_at, OnBytes/Tie/Pv/Tail/HoldsAt.lean). This file spells
these two as Fo.ReadsAll.

Main theorems (namespace `Meaning.Reads`).
  `readsAll_of_tabs`: if at every place that the record's `tabAt` names the entry of the vector of
      reads is the sum of the table's block of cells under the table's weights, then Fo.ReadsAll
      holds at the record's matrices and tables. Premise: each table's matrix is one of the
      record's.
  `readsAll_of_relIn`: **from the relation in front of the draw, at any letters over the record's
      sizes** (TLetters, Cb/Pv/Tail/Tables.lean): there is one integer matrix for each committed
      matrix, small, whose packing is the letters' symbols, and Fo.ReadsAll holds at these integers'
      images. The tables with their weights (funs) are a letter apart from the record, of which they
      have the shapes alone. Two premises on the letters: their weights are these tables'; their
      committed reads are the world's entries.
  `readsAll_of_atA`: the same where the letters are read off the arrays' entries A (the library's
      AtA, OnBytes/Tie/Pv/Tail/EndsAt.lean): Fo.ReadsAll holds of A itself.
  `readsAll_at`: the same at the letters `thetaAt` and the early
      part of the committed entries m: there is one integer matrix for each committed matrix, small,
      whose packing is the committed symbols, and Fo.ReadsAll holds of the entries of the world
      `portWorld ρ Y F m` at these integers' images in the field.
  `readsAll_sizes`: Fo.ReadsAll reads a list of matrices through the numbers of rows and of columns
      alone.

Limits. `readsAll_at` has holds_at's five premises, which are shown nowhere here: the cells of the
array iU3 and of the symbol arrays are early; iU3 has one row with the weight 1 (RowsBelow,
UnitRow); every place that a table names lies below K3. THE RELATION IN FRONT OF THE DRAW IS A
PREMISE: that it holds of what a prover has committed to, but for an error, is the smallness test's
own law. The integers stand under "there are"; small integers with the committed packing are unique
under Size.Uniq (Cb/Pv/Tail/Unique.lean), which is not used here. Which record is meant: one in
which the tables are laid (tl.funs); in a plan's own record the list is empty and all this says
nothing. Nothing on soundness.
-/
import OnBytes.Tie.Pv.Tail.HoldsAt
import OnBytes.Tie.Pv.Tail.EndsAt
import OnBytes.Tie.Pv.Tail.EndLoopsB
import OnBytes.Tie.Pv.Lookup.Ends.FoReadsIn
import Johnson.Road.FormsKeysTab

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Reads
open Finset
open OnBytes OnBytes.Model Fo
open OnBytes.Tie.Pv.Tail OnBytes.Road.Rows Cb.Pv.Tail Iop

/-- **The tables' clause, spelled as the law of the reads.** a μ r c: cell (row r, column c) of
matrix μ, in the field. -/
theorem readsAll_of_tabs {K : Type} [CommRing K] (ρ : Reading K) (tl : HTailF2)
    (entry : ℕ → ℕ → ℕ → K) (iU3 K3 : ℕ) (a : ℕ → ℕ → ℕ → K)
    (hNM : ∀ f ∈ tl.funs.toList, f.tree = 2 → f.mat < tl.NM)
    (h : ∀ (n : ℕ) (Fn : HFun), tl.funs[n]? = some Fn → ∀ c sg pos,
      tl.tabAt Fn c sg = some pos →
        entry iU3 (pos / K3) (pos % K3) =
          ∑ j ∈ range Fn.len, ρ.val (Fn.phi.getD j zeroE) * a Fn.mat (sg * Fn.len + j) c) :
    ReadsAll ρ tl.mats tl.funs entry iU3 K3 a := by
  intro f hf ht col hcol
  have hq : 0 < (tl.mats.getD f.mat {}).m / f.len := by
    rcases Nat.eq_zero_or_pos ((tl.mats.getD f.mat {}).m / f.len) with h0 | h0
    · rw [h0, Nat.mul_zero] at hcol
      exact absurd hcol (Nat.not_lt_zero _)
    · exact h0
  have hl : f.len ≠ 0 := by
    intro h0
    rw [h0, Nat.div_zero] at hq
    exact absurd hq (Nat.lt_irrefl _)
  have hc : col / ((tl.mats.getD f.mat {}).m / f.len) < (tl.mats.getD f.mat {}).k :=
    Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hcol)
  have hs := Nat.mod_lt col hq
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp hf
  have hn' : tl.funs[n]? = some f := by rw [← Array.getElem?_toList]; exact hn
  have e := h n f hn' _ _ _ (Road.tailAt_some tl f (hNM f hf ht) hl hc hs)
  rw [Nat.add_assoc, Nat.div_add_mod'] at e
  exact e

/-- **The law of the reads, from the relation in front of the draw, at any letters over the record's
sizes.** The record tl gives the sizes alone. funs: the tables with their weights, which may hang on
what was drawn in a run; hsh: they have the matrices, lengths and first entries of the record's
tables. hphi: the letters' weights are these tables' (at funs := tl.funs: the field phi of the
library's AtA). hu: the entries of the world's virtual rows, read as the claims read the vector of
reads, are the letters' committed reads. -/
theorem readsAll_of_relIn {K : Type} [CommRing K] (ρ : Reading K) (tl : HTailF2)
    (Θ : TLetters K (Tie.Pv.Tail.sizeOf tl)) {x : Θ.X} {msg : Θ.M}
    (h : relIn Θ.letters x msg) (funs : Array HFun)
    (hsh : (Tie.Pv.Tail.sizeOf tl).tabs =
      funs.toList.map fun Fn => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab))
    (entry : ℕ → ℕ → ℕ → K) (iU3 K3 : ℕ)
    (hphi : ∀ n Fn, funs.toList[n]? = some Fn → ∀ j, j < Fn.len →
      Θ.phi x n j = ρ.val (Fn.phi.getD j zeroE))
    (hu : ∀ f ∈ funs.toList, f.tree = 2 → ∀ c < (tl.mats.getD f.mat {}).k,
      ∀ sg < (tl.mats.getD f.mat {}).m / f.len,
        Θ.u3 msg (f.start + c * ((tl.mats.getD f.mat {}).m / f.len) + sg) =
          u3Val entry iU3 K3 (f.start + c * ((tl.mats.getD f.mat {}).m / f.len) + sg))
    (hNM : ∀ f ∈ funs.toList, f.tree = 2 → f.mat < tl.NM) :
    ∃ a : ℕ → ℕ → ℕ → ℤ,
      (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k → ∀ i, i < (tl.mats.getD μ {}).m →
        |a μ c i| < 2 * ((2 ^ lbz : ℕ) : ℤ)) ∧
      (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k →
        ∀ i', i' < Alg.symRows (tl.mats.getD μ {}).m →
          Θ.sym msg μ i' c =
            ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl.mats.getD μ {}).m => a μ c i) i' : ℤ) :
              K)) ∧
      ReadsAll ρ tl.mats funs entry iU3 K3 (fun μ r c => ((a μ c r : ℤ) : K)) := by
  obtain ⟨a, h1, h2, h3⟩ := reads_of_relIn Θ h
  refine ⟨a, h1, h2, ?_⟩
  refine readsAll_of_reads ρ tl.mats funs entry iU3 K3 (Θ.u3 msg) (Θ.phi x)
    (fun μ c i => ((a μ c i : ℤ) : K)) hu hphi fun n f hn ht c hc sg hsg => ?_
  have hT : (Tie.Pv.Tail.sizeOf tl).tabs[n]? = some ⟨f.mat, f.len, f.start⟩ := by
    rw [hsh, List.getElem?_map, hn]
    rfl
  exact h3 n ⟨f.mat, f.len, f.start⟩ hT (hNM f (List.mem_of_getElem? hn) ht) c hc sg hsg

/-- Where the letters are read off the arrays' entries A (the library's AtA), the letters' committed
reads are A's entries at the array u3Of tl, read as the claims read the vector of reads. hpos: every
place that a table names lies below K3. -/
theorem atA_reads {K : Type} [CommRing K] {ρ : Reading K} {tl : HTailF2}
    {Θ : TLetters K (Tie.Pv.Tail.sizeOf tl)} {x : Θ.X} {msg : Θ.M}
    {Z : Cb.Pv.Tail.Dig K (Tie.Pv.Tail.sizeOf tl).size} {β : Dr (Tie.Pv.Tail.sizeOf tl).size}
    {A : ℕ → ℕ → ℕ → K} (at' : Port.AtA ρ tl Θ x msg Z β A) (K3 : ℕ)
    (hpos : ∀ f ∈ tl.funs.toList, f.tree = 2 → ∀ c < (tl.mats.getD f.mat {}).k,
      ∀ sg < (tl.mats.getD f.mat {}).m / f.len,
        f.start + c * ((tl.mats.getD f.mat {}).m / f.len) + sg < K3)
    (hNM : ∀ f ∈ tl.funs.toList, f.tree = 2 → f.mat < tl.NM) :
    ∀ f ∈ tl.funs.toList, f.tree = 2 → ∀ c < (tl.mats.getD f.mat {}).k,
      ∀ sg < (tl.mats.getD f.mat {}).m / f.len,
        Θ.u3 msg (f.start + c * ((tl.mats.getD f.mat {}).m / f.len) + sg) =
          u3Val A (Port.u3Of tl) K3 (f.start + c * ((tl.mats.getD f.mat {}).m / f.len) + sg) := by
  intro f hf ht c hc sg hsg
  have hl : f.len ≠ 0 := by
    intro h0
    rw [h0, Nat.div_zero] at hsg
    exact absurd hsg (Nat.not_lt_zero _)
  have hp : Port.posOf tl f sg c =
      f.start + c * ((tl.mats.getD f.mat {}).m / f.len) + sg := by
    unfold Port.posOf
    rw [Road.tailAt_some tl f (hNM f hf ht) hl hc hsg]
    rfl
  have e := at'.u3 (f, sg)
    ((Port.mem_readsList tl tl.funs f sg).2 ⟨hf, hNM f hf ht, Or.inr ht, hsg⟩) c hc
  rw [hp] at e
  rw [e]
  unfold u3Val
  rw [Nat.div_eq_of_lt (hpos f hf ht c hc sg hsg), Nat.mod_eq_of_lt (hpos f hf ht c hc sg hsg)]

/-- **The law of the reads where the letters are read off the arrays' entries A** (the library's
AtA, OnBytes/Tie/Pv/Tail/EndsAt.lean): it holds of A itself, at the array u3Of tl. -/
theorem readsAll_of_atA {K : Type} [CommRing K] (ρ : Reading K) (tl : HTailF2)
    (Θ : TLetters K (Tie.Pv.Tail.sizeOf tl)) {x : Θ.X} {msg : Θ.M}
    {Z : Cb.Pv.Tail.Dig K (Tie.Pv.Tail.sizeOf tl).size} {β : Dr (Tie.Pv.Tail.sizeOf tl).size}
    {A : ℕ → ℕ → ℕ → K} (at' : Port.AtA ρ tl Θ x msg Z β A) (h : relIn Θ.letters x msg) (K3 : ℕ)
    (hpos : ∀ f ∈ tl.funs.toList, f.tree = 2 → ∀ c < (tl.mats.getD f.mat {}).k,
      ∀ sg < (tl.mats.getD f.mat {}).m / f.len,
        f.start + c * ((tl.mats.getD f.mat {}).m / f.len) + sg < K3)
    (hNM : ∀ f ∈ tl.funs.toList, f.tree = 2 → f.mat < tl.NM) :
    ∃ a : ℕ → ℕ → ℕ → ℤ,
      (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k → ∀ i, i < (tl.mats.getD μ {}).m →
        |a μ c i| < 2 * ((2 ^ lbz : ℕ) : ℤ)) ∧
      (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k →
        ∀ i', i' < Alg.symRows (tl.mats.getD μ {}).m →
          A (tl.gtTree.getD μ 0) i' c =
            ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl.mats.getD μ {}).m => a μ c i) i' : ℤ) :
              K)) ∧
      ReadsAll ρ tl.mats tl.funs A (Port.u3Of tl) K3 (fun μ r c => ((a μ c r : ℤ) : K)) := by
  obtain ⟨a, h1, h2, h3⟩ := readsAll_of_relIn ρ tl Θ h tl.funs rfl A (Port.u3Of tl) K3 at'.phi
    (atA_reads at' K3 hpos hNM) hNM
  refine ⟨a, h1, fun μ hμ c hc i' hi' => ?_, h3⟩
  rw [← at'.sym μ i' c hμ hi' hc]
  exact h2 μ hμ c hc i' hi'

/-- **The law of the reads, from the relation in front of the draw**, at the letters thetaAt and in
the world of the committed entries. -/
theorem readsAll_at {K J : Type} [Field K] [Fintype J] (ρ : Reading K) (Y : Lay J) (tl : HTailF2)
    (F : Fork) (iU3 K3 : ℕ) (X : Type) (Ex : ExtSpec) (W₀ : Type)
    (ride : X × Ex.Str → (JE Y tl → K) → Cb.Pv.Tail.Dig K (Tie.Pv.Tail.sizeOf tl).size × W₀ → Prop)
    {x : X} (m : J → K)
    (heU : ∀ r c, early tl (.cell iU3 r c) = true)
    (heS : ∀ μ i' c, μ < tl.NM → early tl (.cell (tl.gtTree.getD μ 0) i' c) = true)
    (hR : RowsBelow Y F iU3) (hU : UnitRow F iU3)
    (hpos : ∀ (n : ℕ) (Fn : HFun), tl.funs[n]? = some Fn → ∀ c sg pos,
      tl.tabAt Fn c sg = some pos → pos < K3)
    (hNM : ∀ f ∈ tl.funs.toList, f.tree = 2 → f.mat < tl.NM)
    (h : relIn (thetaAt ρ Y tl iU3 K3 X Ex W₀ ride).letters x (earlyOf Y tl m)) :
    ∃ a : ℕ → ℕ → ℕ → ℤ,
      (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k → ∀ i, i < (tl.mats.getD μ {}).m →
        |a μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ)) ∧
      (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k →
        ∀ i', i' < Alg.symRows (tl.mats.getD μ {}).m →
          Y.cellAt m (tl.gtTree.getD μ 0) i' c =
            ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl.mats.getD μ {}).m => a μ i c) i' : ℤ) :
              K)) ∧
      ReadsAll ρ tl.mats tl.funs (portWorld ρ Y F m).entry iU3 K3
        (fun μ r c => ((a μ r c : ℤ) : K)) := by
  obtain ⟨a, h1, h2, h3⟩ := holds_at ρ Y tl F iU3 K3 X Ex W₀ ride m heU heS hR hU hpos h
  exact ⟨a, h1, h2, readsAll_of_tabs ρ tl _ iU3 K3 (fun μ r c => ((a μ r c : ℤ) : K)) hNM h3⟩

/-- The law of the reads reads a list of matrices through the numbers of rows and columns alone. -/
theorem readsAll_sizes {K : Type} [CommRing K] (ρ : Reading K) {mats mats' : Array TMat}
    (hm : ∀ μ, (mats.getD μ {}).m = (mats'.getD μ {}).m ∧ (mats.getD μ {}).k = (mats'.getD μ {}).k)
    {funs : Array HFun} {entry : ℕ → ℕ → ℕ → K} {iU3 K3 : ℕ} {cellM : ℕ → ℕ → ℕ → K}
    (h : ReadsAll ρ mats funs entry iU3 K3 cellM) : ReadsAll ρ mats' funs entry iU3 K3 cellM := by
  intro f hf ht
  have e := h f hf ht
  unfold FunRead at e ⊢
  rw [(hm f.mat).1, (hm f.mat).2] at e
  exact e

#print axioms readsAll_of_tabs
#print axioms readsAll_of_relIn
#print axioms atA_reads
#print axioms readsAll_of_atA
#print axioms readsAll_at
#print axioms readsAll_sizes

end Meaning.Reads
