-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/G6/Rider/Model/OneHot.lean: identity j10 of a feed-forward segment ("the selector's entries sum
to 1 at every position of every layer with experts") as a family of arrays on cubes.

Definitions, statements and proofs. No protocol occurs here. The rule for a second zero test on a
block's challenges (Cb/G6/Rider/Carrier.lean) has a source `OnCubes` and a target `AtCoords`, both
over free arrays. This file fills the arrays with the defects of j10, in the names of
Inst/Model/FF/Trace.lean, and restates source and target in those names.
Main names:
  `hotAt D t l i`: the defect of j10 at layer l and position i: `idnVal` at `Idn.j10 l i`, with the
    embedding and the prompt filled by zeros; j10 reads neither (`hotAt_idn`). `hotAt_sum`: it is
    the sum of the selector's entries minus 1. `hotAt_d10`: it is `d10`
    (Inst/Model/FF/Objects.lean).
  `hotFam D cells`: the family, one member for each l < D.ne, each on the cube of D.lT variables.
    `cells` is a free letter: how the cells are read off a state and a tuple of messages.
  `hot_source`: `OnCubes` of the family says that `idnVal` is 0 at every valid `Idn.j10 l i`, for
    every embedding, prompt and flag.
  `hot_target`: `AtCoords` of the family, all members at one choice sel of coordinates, says that
    for every l < D.ne the multilinear extension of i ↦ `idnVal` .. (.j10 l i) is 0 at the point t ↦
    pt (sel t). Coordinate 0 belongs to the top bit of i, as in `Blocks.ext`.
  `hot_not_back`: the target does not give the source. If D.lT, D.ne and D.nx are at least 1 there
    are cells and a point at which the target holds and the source fails.
Limits: nothing on which block draws the point, on its counts, or on who tests the target.
`hot_not_back` gives one point for one choice of cells; it counts nothing.
-/
import Inst.Model.FF.Objects
import Blocks.LookupRel
import Cb.G6.Rider.Carrier

set_option autoImplicit false

namespace Cb.Rider
open Blocks Finset Inst.Model Inst.Model.FFSeg

section OneHot
variable {K : Type} [Field K] [scl : Scl] (D : Dim)

/-- The defect of j10 at layer l and position i. -/
def hotAt (t : Cell → K) (l i : ℕ) : K := idnVal D t (fun _ _ => 0) (fun _ => 0) (.j10 l i)

/-- The identity j10 reads neither the embedding nor the prompt. -/
theorem hotAt_idn (t : Cell → K) (emb : ℕ → ℕ → K) (tok : ℕ → ℕ) (l i : ℕ) :
    idnVal D t emb tok (.j10 l i) = hotAt D t l i := rfl

theorem hotAt_sum (t : Cell → K) (l i : ℕ) :
    hotAt D t l i = ∑ e ∈ range D.nx, val t .sel l e i - 1 := rfl

theorem hotAt_d10 (t : Cell → K) (l i : ℕ) : hotAt D t l i = d10 D t l i := rfl

variable {St M : Type} (cells : St → M → Cell → K)

/-- The family: one member for each layer with experts; the cells are read off the state and the
tuple of messages by `cells`. -/
def hotFam : Fin D.ne → St → M → ℕ → K := fun l st m i => hotAt D (cells st m) l i

/-- The source, in the names of the field relation. -/
theorem hot_source (st : St) (m : M) :
    OnCubes (fun _ : Fin D.ne => D.lT) (hotFam D cells) st m ↔
      ∀ (emb : ℕ → ℕ → K) (tok : ℕ → ℕ) (first : Bool) (l i : ℕ), (Idn.j10 l i).Valid D first →
        idnVal D (cells st m) emb tok (.j10 l i) = 0 :=
  ⟨fun h _ _ _ l i hv => h ⟨l, hv.1⟩ i hv.2,
    fun h l i hi => h (fun _ _ => 0) (fun _ => 0) false l i ⟨l.2, hi⟩⟩

/-- The target, in the names of the field relation. -/
theorem hot_target (sel : ℕ → ℕ) (st : St) (pt : ℕ → K) (m : M) :
    AtCoords (fun _ : Fin D.ne => D.lT) (fun _ => sel) (hotFam D cells) st pt m ↔
      ∀ l, l < D.ne →
        ext D.lT (fun i => idnVal D (cells st m) (fun _ _ => 0) (fun _ => 0) (.j10 l i))
          (fun t => pt (sel t)) = 0 :=
  ⟨fun h l hl => h ⟨l, hl⟩, fun h l => h l l.2⟩

/-- The target does not give the source: cells whose defect is -1 at position 0 and 0 elsewhere, and
the vertex 1 as the point. -/
theorem hot_not_back (hT : 1 ≤ D.lT) (he : 1 ≤ D.ne) (hx : 1 ≤ D.nx) :
    ∃ (t : Cell → K) (u : ℕ → K),
      (∀ l, l < D.ne →
        ext D.lT (fun i => idnVal D t (fun _ _ => 0) (fun _ => 0) (.j10 l i)) u = 0) ∧
      ¬ ∀ (emb : ℕ → ℕ → K) (tok : ℕ → ℕ) (first : Bool) (l i : ℕ), (Idn.j10 l i).Valid D first →
        idnVal D t emb tok (.j10 l i) = 0 := by
  have h1 : 1 < 2 ^ D.lT := Nat.one_lt_two_pow (by omega)
  let t : Cell → K := fun c => if c.j = 0 ∧ c.i ≠ 0 then 1 else 0
  have hv : ∀ l i, hotAt D t l i = if i = 0 then -1 else 0 := by
    intro l i
    rw [hotAt_sum]
    have e : ∀ e ∈ range D.nx, val t .sel l e i = if e = 0 ∧ i ≠ 0 then 1 else 0 := by
      intro e _
      simp [FFSeg.val, t, Arr.nCell, Arr.off]
    rw [sum_congr rfl e]
    by_cases hi : i = 0
    · simp [hi]
    · have : ∑ e ∈ range D.nx, (if e = 0 ∧ i ≠ 0 then (1 : K) else 0) = 1 := by
        rw [sum_eq_single_of_mem 0 (mem_range.2 (by omega)) (fun b _ hb => by simp [hb])]
        simp [hi]
      rw [this, if_neg hi, sub_self]
  refine ⟨t, cubePt D.lT 1, fun l _ => ?_, fun h => ?_⟩
  · show ext D.lT (fun i => hotAt D t l i) (cubePt D.lT 1) = 0
    rw [ext_cubePt D.lT _ h1, hv, if_neg one_ne_zero]
  · have h0 := h (fun _ _ => 0) (fun _ => 0) false 0 0 ⟨by omega, Nat.two_pow_pos _⟩
    rw [hotAt_idn, hv, if_pos rfl] at h0
    exact one_ne_zero (neg_eq_zero.1 h0)

end OneHot

end Cb.Rider

#print axioms Cb.Rider.hot_source
#print axioms Cb.Rider.hot_target
#print axioms Cb.Rider.hot_not_back
