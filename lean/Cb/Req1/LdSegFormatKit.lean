-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegFormatKit.lean: rules for "the reduction leaves that oracle alone" (`IOR.IdxLink`,
Cb/Req1/LdReqFormat.lean).

Definitions, lemmas with proofs. No protocol, no code occurs here.
Lemmas for the book-keeping of Cb/Req1/LdReqFormat.lean, which follows one input oracle through a
composition of interactive oracle reductions: how steps that only regroup, copy or pass on oracles
act on it.
An oracle of the kind E0 (the encoded index) is somewhere among the oracles of a joint (`IxAt`). A
chain passes joints at which it is at other places; the steps between are re-bracketings.
A map of oracles (`ExtMap`, Ior/Frame.lean) is a function on strings with, for each new position,
a declared set `src` of old positions, from which its symbol is meant to be computed
(`ExtMap.IsLocal` says that it is; not asked here).

Main names:
  `g.Moves i₁ i₂`: the map g of oracles takes the oracle at the place i₁ (`IxAt`) to the place i₂:
    its string is kept; a symbol at the new place comes from that symbol alone; no other new symbol
    comes from it.
  `g.Avoids i`: no symbol of g's image comes from the oracle at i.
  Rules for these two: identity; composition; the two projections; a pair (one component moves the
    oracle, the other avoids); what avoids.
  `IdxLink.pure`, `IdxLink.post`, `IdxLink.pre`: a step without rounds; a reduction, then a step; a
    step, then a reduction: `IdxLink` of each, if the step's map `Moves` the oracle and the
    reduction has `IdxLink`, the middle place shared.
  `IdxLink.of_step`: a reduction that leaves all of the left part alone (`IdxStep`,
    Cb/Ld/LdWfPre.lean) leaves alone whatever is in the left part, at every place.
  `IdxLink.of_copies`: a block that only copies its oracles (`OnlyCopies`: a drawing, a saying)
    leaves every oracle alone. `OnlyCopies.bears`: see its docstring.
  `IdxLink.keepE_right`, `IdxLink.keepE_left`: further oracles handed on unchanged (`R.keepE F`):
    what is among them; what is in R's own oracles, if R leaves it alone.

Limits: this file says nothing on relations, nothing on any protocol.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqFormat
import Blocks.ClosingBlock
import Blocks.Stage
import Cb.Gen.Code
import Hiop.ChainList
import Blocks.Level2Def
import Blocks.PfrHVZK_rs
import Iop.Deco
import Mathlib.Data.FinEnum

set_option autoImplicit false

namespace Iop
open Prob IOR

namespace ExtMap
variable {E0 E₁ E₂ E₃ F : ExtSpec}

/-- The map takes the oracle at i₁ to i₂. -/
structure Moves (g : ExtMap E₁ E₂) (i₁ : IxAt E0 E₁) (i₂ : IxAt E0 E₂) : Prop where
  str : ∀ y, i₂.str (g.map y) = i₁.str y
  src : ∀ p, g.src (i₂.pos p) = {i₁.pos p}
  aux : ∀ q, (∀ p, q ≠ i₂.pos p) → ∀ p, i₁.pos p ∉ g.src q

/-- No symbol of the image comes from the oracle at i. -/
def Avoids (g : ExtMap E₁ E₂) (i : IxAt E0 E₁) : Prop := ∀ q p, i.pos p ∉ g.src q

theorem Moves.id (i : IxAt E0 E₁) : (ExtMap.id E₁).Moves i i :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ hq p hp => hq p (Finset.mem_singleton.1 hp).symm⟩

theorem Moves.comp {g' : ExtMap E₂ E₃} {g : ExtMap E₁ E₂} {i₁ : IxAt E0 E₁} {i₂ : IxAt E0 E₂}
    {i₃ : IxAt E0 E₃} (h' : g'.Moves i₂ i₃) (h : g.Moves i₁ i₂) : (g'.comp g).Moves i₁ i₃ := by
  classical
  refine ⟨fun y => (h'.str _).trans (h.str y), fun p => ?_, fun q hq p hp => ?_⟩
  · show (g'.src (i₃.pos p)).biUnion g.src = _
    rw [h'.src, Finset.singleton_biUnion, h.src]
  · obtain ⟨q', hq', hp'⟩ := Finset.mem_biUnion.1 hp
    by_cases hx : ∃ p', q' = i₂.pos p'
    · obtain ⟨p', rfl⟩ := hx
      exact h'.aux q hq p' hq'
    · exact h.aux q' (fun p' hp'' => hx ⟨p', hp''⟩) p hp'

theorem Moves.fst (i : IxAt E0 E₁) (F : ExtSpec) : (ExtMap.fst E₁ F).Moves (i.inl F) i :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ hq p hp => hq p (Sum.inl.inj (Finset.mem_singleton.1 hp)).symm⟩

theorem Moves.snd (i : IxAt E0 E₁) (F : ExtSpec) : (ExtMap.snd F E₁).Moves (i.inr F) i :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ hq p hp => hq p (Sum.inr.inj (Finset.mem_singleton.1 hp)).symm⟩

theorem Avoids.fst (i : IxAt E0 F) (E₁ : ExtSpec) : (ExtMap.fst E₁ F).Avoids (i.inr E₁) :=
  fun _ _ hp => by cases Finset.mem_singleton.1 hp
theorem Avoids.snd (i : IxAt E0 E₁) (F : ExtSpec) : (ExtMap.snd E₁ F).Avoids (i.inl F) :=
  fun _ _ hp => by cases Finset.mem_singleton.1 hp

/-- first g, which avoids -/
theorem Avoids.comp {g : ExtMap E₁ E₂} {i : IxAt E0 E₁} (h : g.Avoids i) (g' : ExtMap E₂ E₃) :
    (g'.comp g).Avoids i := by
  classical
  intro q p hp
  obtain ⟨q', _, hp'⟩ := Finset.mem_biUnion.1 hp
  exact h q' p hp'

/-- first g, which moves the oracle; then g', which avoids -/
theorem Avoids.comp_moves {g' : ExtMap E₂ E₃} {g : ExtMap E₁ E₂} {i₁ : IxAt E0 E₁} {i₂ : IxAt E0 E₂}
    (h' : g'.Avoids i₂) (h : g.Moves i₁ i₂) : (g'.comp g).Avoids i₁ := by
  classical
  intro q p hp
  obtain ⟨q', hq', hp'⟩ := Finset.mem_biUnion.1 hp
  by_cases hx : ∃ p', q' = i₂.pos p'
  · obtain ⟨p', rfl⟩ := hx
    exact h' q p' hq'
  · exact h.aux q' (fun p' hp'' => hx ⟨p', hp''⟩) p hp'

theorem Avoids.pair {g₁ : ExtMap E₁ E₂} {g₂ : ExtMap E₁ E₃} {i : IxAt E0 E₁}
    (h₁ : g₁.Avoids i) (h₂ : g₂.Avoids i) :
    (g₁.pair g₂).Avoids i := fun q p hp => by
  cases q with
  | inl q => exact h₁ q p hp
  | inr q => exact h₂ q p hp

theorem Moves.pair_left {g₁ : ExtMap E₁ E₂} {g₂ : ExtMap E₁ E₃} {i₁ : IxAt E0 E₁} {i₂ : IxAt E0 E₂}
    (h₁ : g₁.Moves i₁ i₂) (h₂ : g₂.Avoids i₁) :
    (g₁.pair g₂).Moves i₁ (i₂.inl E₃) :=
  ⟨fun y => h₁.str y, fun p => h₁.src p, fun q hq p hp => by
    cases q with
    | inl q => exact h₁.aux q (fun p' hp' => hq p' (congrArg Sum.inl hp')) p hp
    | inr q => exact h₂ q p hp⟩

theorem Moves.pair_right {g₁ : ExtMap E₁ E₂} {g₂ : ExtMap E₁ E₃} {i₁ : IxAt E0 E₁} {i₃ : IxAt E0 E₃}
    (h₁ : g₁.Avoids i₁) (h₂ : g₂.Moves i₁ i₃) :
    (g₁.pair g₂).Moves i₁ (i₃.inr E₂) :=
  ⟨fun y => h₂.str y, fun p => h₂.src p, fun q hq p hp => by
    cases q with
    | inl q => exact h₁ q p hp
    | inr q => exact h₂.aux q (fun p' hp' => hq p' (congrArg Sum.inr hp')) p hp⟩

end ExtMap

namespace IOR
variable {X₁ X₂ X₃ X X' : Type} {E0 E₁ E₂ E₃ Ea Eb Ex F : ExtSpec}

/-- A step without rounds. -/
theorem IdxLink.pure {g : ExtMap E₁ E₂} {i₁ : IxAt E0 E₁} {i₂ : IxAt E0 E₂}
    (h : g.Moves i₁ i₂) (f : X₁ → Option X₂) : (IOR.pure f g).IdxLink i₁ i₂ :=
  ⟨fun _ _ hp => absurd hp (Finset.notMem_empty _),
    fun _ p => p.elim, fun y _ => h.str y,
    fun _ p => ⟨h.src p, rfl⟩,
    fun _ q hq p hp => h.aux q hq p hp⟩

/-- A reduction, then a step without rounds. -/
theorem IdxLink.post {R : IOR X₁ E₁ X₂ E₂} {g : ExtMap E₂ E₃} {i₁ : IxAt E0 E₁} {i₂ : IxAt E0 E₂}
    {i₃ : IxAt E0 E₃} (h : R.IdxLink i₁ i₂) (hg : g.Moves i₂ i₃) (f : X₂ → Option X₃) :
    (R.post f g).IdxLink i₁ i₃ := by
  classical
  refine ⟨h.noIdx, h.noTie, fun y τ => (hg.str _).trans (h.copy y τ),
    fun ρ p => ⟨?_, ?_⟩, fun ρ q hq p hp => ?_⟩
  · show (g.src (i₃.pos p)).biUnion (R.srcE ρ) = _
    rw [hg.src, Finset.singleton_biUnion, (h.srcIdx ρ p).1]
  · show (g.src (i₃.pos p)).biUnion (R.srcO ρ) = _
    rw [hg.src, Finset.singleton_biUnion]
    exact (h.srcIdx ρ p).2
  · obtain ⟨q', hq', hp'⟩ :=
      Finset.mem_biUnion.1 (show i₁.pos p ∈ (g.src q).biUnion (R.srcE ρ) from hp)
    by_cases hx : ∃ p', q' = i₂.pos p'
    · obtain ⟨p', rfl⟩ := hx
      exact hg.aux q hq p' hq'
    · exact h.srcAux ρ q' (fun p' hp'' => hx ⟨p', hp''⟩) p hp'

/-- A step without rounds, then a reduction. -/
theorem IdxLink.pre {R : IOR X₂ E₂ X₃ E₃} {g : ExtMap E₁ E₂} {i₁ : IxAt E0 E₁} {i₂ : IxAt E0 E₂}
    {i₃ : IxAt E0 E₃} (hg : g.Moves i₁ i₂) (h : R.IdxLink i₂ i₃) (f : X₁ → Option X₂) :
    (R.pre f g).IdxLink i₁ i₃ := by
  classical
  have key : ∀ (U : Finset E₂.Pos), (∀ p', i₂.pos p' ∉ U) → ∀ p, i₁.pos p ∉ U.biUnion g.src := by
    intro U hU p hp
    obtain ⟨q', hq', hp'⟩ := Finset.mem_biUnion.1 hp
    exact hg.aux q' (fun p' hp'' => hU p' (hp'' ▸ hq')) p hp'
  refine ⟨fun ρ p => key _ (fun p' => h.noIdx ρ p') p,
    fun ρ p q => key _ (fun p' => h.noTie ρ p p') q,
    fun y τ => (h.copy _ τ).trans (hg.str y),
    fun ρ p => ⟨?_, (h.srcIdx ρ p).2⟩,
    fun ρ q hq p => key _ (fun p' => h.srcAux ρ q hq p') p⟩
  show (R.srcE ρ (i₃.pos p)).biUnion g.src = _
  rw [(h.srcIdx ρ p).1, Finset.singleton_biUnion, hg.src]

/-- A reduction that leaves all of the left part alone leaves alone whatever is there. -/
theorem IdxLink.of_step {R : IOR X₁ (Ex.prod Ea) X₂ (Ex.prod Eb)} (h : R.IdxStep) (i : IxAt E0 Ex) :
    R.IdxLink (i.inl Ea) (i.inl Eb) :=
  ⟨fun ρ p => h.noIdx ρ _, fun ρ p q => h.noTie ρ p _, fun y τ => congrArg i.str (h.copy y τ), fun ρ p => h.srcIdx ρ _, fun ρ q hq p hp => by
    cases q with
    | inl q =>
        rw [(h.srcIdx ρ q).1] at hp
        exact hq p (congrArg Sum.inl (Sum.inl.inj (Finset.mem_singleton.1 hp)).symm)
    | inr q => exact h.srcAux ρ q _ hp⟩

/-- A block that only copies its oracles leaves every oracle alone. -/
theorem IdxLink.of_copies {R : IOR X Ex X' Ex} (h : R.OnlyCopies) (i : IxAt E0 Ex) :
    R.IdxLink i i :=
  ⟨fun ρ p hp => by rw [h.noReads] at hp; exact Finset.notMem_empty _ hp,
    fun ρ p q hq => by rw [h.noTie] at hq; exact Finset.notMem_empty _ hq,
    fun y τ => congrArg i.str (h.copy y τ),
    fun ρ p => h.src ρ _, fun ρ q hq p hp => by
      rw [(h.src ρ q).1] at hp
      exact hq p (Finset.mem_singleton.1 hp).symm⟩

open Classical in
/-- what such a block needs is what follows needs -/
theorem OnlyCopies.need {R : IOR X Ex X' Ex} (h : R.OnlyCopies)
    (ρ : Rho R.shape) (U : Finset Ex.Pos) : R.need ρ U = U := by
  ext q
  rw [mem_need, IOR.mem_given]
  constructor
  · rintro ((hq | ⟨p, _, hq⟩) | ⟨u, hu, hq⟩)
    · rw [h.noReads] at hq
      exact absurd hq (Finset.notMem_empty _)
    · rw [h.noTie] at hq
      exact absurd hq (Finset.notMem_empty _)
    · rw [(h.src ρ u).1] at hq
      exact (Finset.mem_singleton.1 hq) ▸ hu
  · exact fun hq => Or.inr ⟨q, hq, by rw [(h.src ρ q).1]; exact Finset.mem_singleton_self q⟩

open Classical in
/-- A block that only copies its oracles bears what follows, with the same demand on both sides, if
its budget holds of the empty set. -/
theorem OnlyCopies.bears {R : IOR X Ex X' Ex} (h : R.OnlyCopies)
    (bud : Rho R.shape → Finset (OPos R.shape) → Prop)
    (hb : ∀ ρ, bud ρ ∅) (q : Finset Ex.Pos → Prop) : R.Bears bud q q := by
  intro ρ U hU
  have e : U.biUnion (R.srcO ρ) = ∅ := Finset.eq_empty_of_forall_notMem fun p hp => by
    obtain ⟨u, _, hp⟩ := Finset.mem_biUnion.1 hp
    rw [(h.src ρ u).2] at hp
    exact Finset.notMem_empty _ hp
  rw [e, h.need]
  exact ⟨hb ρ, hU⟩

/-- Further oracles handed on unchanged: what is among them. -/
theorem IdxLink.keepE_right (R : IOR X₁ E₁ X₂ E₂) (i : IxAt E0 F) :
    (R.keepE F).IdxLink (i.inr E₁) (i.inr E₂) := by
  refine ⟨fun ρ p hp => ?_, fun ρ p q hq => ?_, fun _ _ => rfl,
    fun _ _ => ⟨rfl, rfl⟩, fun ρ q hq p hp => ?_⟩
  · obtain ⟨_, _, h⟩ := Finset.mem_map.1 hp
    cases h
  · obtain ⟨_, _, h⟩ := Finset.mem_map.1 hq
    cases h
  · cases q with
    | inl q =>
        obtain ⟨_, _, h⟩ := Finset.mem_map.1 hp
        cases h
    | inr q => exact hq p (congrArg Sum.inr (Sum.inr.inj (Finset.mem_singleton.1 hp)).symm)

/-- .. and what is in R's own oracles, if R leaves it alone. -/
theorem IdxLink.keepE_left {R : IOR X₁ E₁ X₂ E₂} {i₁ : IxAt E0 E₁} {i₂ : IxAt E0 E₂}
    (h : R.IdxLink i₁ i₂) (F : ExtSpec) :
    (R.keepE F).IdxLink (i₁.inl F) (i₂.inl F) := by
  refine ⟨fun ρ p hp => ?_, fun ρ p q hq => ?_, fun y τ => h.copy y.1 τ,
    fun ρ p => ⟨?_, (h.srcIdx ρ p).2⟩, fun ρ q hq p hp => ?_⟩
  · obtain ⟨a, ha, e⟩ := Finset.mem_map.1 hp
    exact h.noIdx ρ p (Sum.inl.inj e ▸ ha)
  · obtain ⟨a, ha, e⟩ := Finset.mem_map.1 hq
    exact h.noTie ρ p q (Sum.inl.inj e ▸ ha)
  · show (R.srcE ρ (i₂.pos p)).map Function.Embedding.inl = _
    rw [(h.srcIdx ρ p).1, Finset.map_singleton]
    rfl
  · cases q with
    | inl q =>
        obtain ⟨a, ha, e⟩ := Finset.mem_map.1 hp
        exact h.srcAux ρ q (fun p' hp' => hq p' (congrArg Sum.inl hp')) p (Sum.inl.inj e ▸ ha)
    | inr q => cases Finset.mem_singleton.1 hp

theorem IdxLink.keepX {R : IOR X₁ E₁ X₂ E₂} {i₁ : IxAt E0 E₁} {i₂ : IxAt E0 E₂}
    (h : R.IdxLink i₁ i₂) (Z : Type) : (R.keepX Z).IdxLink i₁ i₂ :=
  ⟨h.noIdx, h.noTie, h.copy, h.srcIdx, h.srcAux⟩

end IOR
end Iop
