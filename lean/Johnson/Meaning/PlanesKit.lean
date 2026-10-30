-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/PlanesKit.lean: the law of Johnson/Meaning/PlanesLaw.lean in the letters in which a
sub-proof's own text gives its tables: a kit for the instances.

`host_planes` asks for three tables as the library's Fo.PlaneTab. A sub-proof's text gives a table
as a member of its list with a first entry, a matrix, a length and an array of weights (so the
library's TabAt.laid, Johnson/Road/Rows/AttRead.lean, for attention), and the weights as what the
lookup hands in: Forest.phiB at the two points, Forest.phiP. Here the law is stated on that.

Main names (namespace `Meaning.Planes`).
  `LaidAt funs t mat len phi`: a table of the list funs, in the vector of reads, begins at entry t,
      on blocks of len rows of matrix mat, under the weights phi.
  `planeTab_of_laid`: such a table as a Fo.PlaneTab.
  `host_planes_of_laid`: **the three clauses**, from: the three tables LaidAt on one matrix iB,
      under the lookup's own weights; the matrix has its rows in one block of 2^lm and at least the
      planes' columns; its cells are the lookup's; the caller's readers are entries of the vector of
      reads (`ReadersAre`); the law of the reads.

What an instance brings: its list of tables and list of matrices; the record g that its lookup has
heard; the three first entries; iB; iU3 and K3; ReadersAre; and that the three tables lie in the
vector of reads (tree = 2), which TabAt.laid does not say: the verifier's three routines that lay
tables write that number (OnBytes/Model/Layer.lean, AttentionTables.lean, HeadTables.lean), by
reading.
Limits. As Johnson/Meaning/PlanesLaw.lean's: THE LAW OF THE READS IS A PREMISE. It names no text: an
instance does.
-/
import Johnson.Meaning.PlanesLaw
import OnBytes.Tie.Pv.Lookup.Forest.FoPhi
import OnBytes.Tie.Pv.Lookup.Port.FoTwins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Planes
open Cb Cb.Fo Cb.Fo.NumsEq TwV
open OnBytes OnBytes.Model Fo

/-- A table of the list, in the vector of reads: its first entry, matrix, length and weights. -/
def LaidAt (funs : Array HFun) (t mat len : ℕ) (phi : Array E) : Prop :=
  ∃ Fn ∈ funs.toList, Fn.tree = 2 ∧ Fn.start = t ∧ Fn.mat = mat ∧ Fn.len = len ∧ Fn.phi = phi

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- Such a table as a table of a lookup's planes. -/
theorem planeTab_of_laid {mats : Array TMat} {funs : Array HFun} {cellM : ℕ → ℕ → ℕ → K}
    {t iB lm : ℕ} {phi : Array E} (T : LaidAt funs t iB (2 ^ lm) phi) (w : ℕ → K) (h : FoNums.Sh)
    (ν : _root_.Fo.Pl → K) (h1 : (mats.getD iB {}).m / 2 ^ lm = 1)
    (h2 : planeCols h lm ≤ (mats.getD iB {}).k)
    (hw : ∀ j < 2 ^ lm, ρ.val (phi.getD j zeroE) = w j)
    (h4 : ∀ r < 2 ^ lm, ∀ c < planeCols h lm, cellM iB r c = ν (.cell r c)) :
    ∃ f, PlaneTab ρ mats funs cellM f t w h lm ν := by
  obtain ⟨f, hf, e0, e1, e2, e3, e4⟩ := T
  refine ⟨f, hf, e0, e1, e3, ?_, ?_, ?_, ?_⟩
  · rw [e2, e3]
    exact h1
  · rw [e2]
    exact h2
  · rw [e4]
    exact hw
  · rw [e2]
    exact h4

/-- **The three clauses, in the letters of a sub-proof's own tables.** g: what the caller's lookup
has heard. b0, b1: the weights that it hands in at its two points. -/
theorem host_planes_of_laid {mats : Array TMat} {funs : Array HFun} {cellM : ℕ → ℕ → ℕ → K}
    (g : Forest.Heard) {lm iB iU3 K3 tB0 tB1 tP : ℕ} {b0 b1 : Array E}
    (y0 : Forest.phiB g lm 0 = some b0) (y1 : Forest.phiB g lm 1 = some b1)
    (T0 : LaidAt funs tB0 iB (2 ^ lm) b0) (T1 : LaidAt funs tB1 iB (2 ^ lm) b1)
    (TP : LaidAt funs tP iB (2 ^ lm) (Forest.phiP lm))
    (h1 : (mats.getD iB {}).m / 2 ^ lm = 1) (h2 : planeCols g.shape lm ≤ (mats.getD iB {}).k)
    (ν : _root_.Fo.Pl → K)
    (h4 : ∀ r < 2 ^ lm, ∀ c < planeCols g.shape lm, cellM iB r c = ν (.cell r c))
    {bit : ℕ → ℕ → Aff} {pin : ℕ → Aff} (R : ReadersAre g.shape lm iU3 K3 tB0 tB1 tP bit pin)
    (W : World K) (hA : ReadsAll ρ mats funs W.entry iU3 K3 cellM) :
    K3HostPlanes g.shape lm (rdL ρ g.zb0) (rdL ρ g.zb1) ν (fun f => f.value ρ W) bit pin := by
  obtain ⟨f0, t0⟩ := planeTab_of_laid ρ T0 (fun r => (phiBK g.shape lm (rdL ρ g.zb0)).getD r 0)
    g.shape ν h1 h2 (fun j _ => by
      rw [rdL_getD, phiB_val ρ g lm 0 b0 y0]
      rfl) h4
  obtain ⟨f1, t1⟩ := planeTab_of_laid ρ T1 (fun r => (phiBK g.shape lm (rdL ρ g.zb1)).getD r 0)
    g.shape ν h1 h2 (fun j _ => by
      rw [rdL_getD, phiB_val ρ g lm 1 b1 y1]
      rfl) h4
  obtain ⟨fP, tp⟩ := planeTab_of_laid ρ TP (fun r => (2 : K) ^ (r % 32)) g.shape ν h1 h2
    (fun j hj => phiP_val ρ lm j hj) h4
  exact host_planes ρ t0 t1 tp R W hA

end

#print axioms planeTab_of_laid
#print axioms host_planes_of_laid

end Meaning.Planes
