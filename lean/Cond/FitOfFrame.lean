-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cond/FitOfFrame.lean: the compiler's data and side conditions of one sub-protocol, through the steps
without rounds.

Definitions, statements and proofs. Generic: no protocol occurs.
This is book-keeping for the compiler: beside security properties it needs data on a protocol's
format and side conditions on these data, and both must pass through every way of building a
protocol from parts.
Cond/FitOfSub.lean has the bundle of data (`IOR.SubData`) and of conditions (`IOR.SubFit`) of an
IOR, and the rule for "R₁; then R₂". The blocks of the protocols under Cb/
are joined not only by composition but also by the constructions of Ior/Frame.lean
and Ior/FrameOn.lean, which add no
round: a further explicit part or further oracles are handed on (keepX, keepE), the witness has a
further part (carry), a step without rounds stands before or behind (pre, post), a block works on a
part of a larger statement (on). Here the bundles go through all of them.

Main names:
  `ExtMap.Thin g`: every symbol of the image is computed from at most one position of the argument.
    So are the identity, the projections, pairs and compositions of such maps: all re-bracketings.
  `OpenB.keep`: the numbers of openings (`OpenB`, Cond/FitOfOpens.lean) when further oracles are
    handed on: a later query costs at least one position in the bound (it may go to the oracles
    handed on).
  `opensLe_keepX`, `opensLe_keepE`, `opensLe_pre`, `opensLe_post`, `opensLe_on`: the rules on
    numbers of openings: `keepX` keeps o, and so do `pre` and `post` at a thin map; `keepE` takes o
    to `o.keep`, and so does `on` at thin maps gi, go.
  `opensLe_pure`, `SubData.pure`, `subFit_pure`: a step without rounds, alone, along a thin map: no
    round, no coin, nothing opened; a later query costs at most one position.
  `SubData.keepX`, `keepE`, `carry`, `pre`, `post`, `on`: the data: shape, numberings, samplers,
    coins and decision procedures are those of the block.
  `subFit_keepX` to `subFit_on`: the conditions; for `pre`, `post`, `on` the maps are thin.

Every field of the bundles `IOR.SubData.pre`, `post`, `on`, `pure`, `dropZ` is a field of the
block's bundle, `decHid` at mapped arguments; but `keepE`, and so `on`, have `D.ob.keep`, and the
fields of `pure` are constants. (Three of the definitions are marked noncomputable all the same:
their TYPES name IOR.pre and IOR.post, which form unions of finite sets with classical equality
tests.)

Notation: `OpenB` (Cond/FitOfOpens.lean) has four numbers: `n`: own positions, in the prover's
oracles and the implicit instance together; `nE`: own positions in the implicit instance; `bl`:
positions for one query to the new implicit instance; `bE`: of these, in the implicit instance.

Limits: this file says nothing on security. For a map that is not thin (a symbol computed from
several positions) there is no rule here.

Terms: lean/GLOSSARY.md.

-/
import Cond.FitOfSub
import Ior.FrameOn
import Ior.ChainZ
import Mathlib.Data.Finset.Sum
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-- A union of sets with at most one element each. -/
theorem card_biUnion_thin {α β : Type} [DecidableEq β] (s : Finset α)
    (f : α → Finset β) (h : ∀ a, (f a).card ≤ 1) : (s.biUnion f).card ≤ s.card :=
  Finset.card_biUnion_le.trans ((Finset.sum_le_card_nsmul s _ 1 fun a _ => h a).trans (by simp))

namespace ExtMap
variable {E E' E'' E₁ E₂ : ExtSpec}

/-- Every symbol of the image is computed from at most one position. -/
def Thin (g : ExtMap E E') : Prop := ∀ q, (g.src q).card ≤ 1

theorem thin_id (E : ExtSpec) : (ExtMap.id E).Thin := fun _ => le_of_eq (Finset.card_singleton _)
theorem thin_fst (E₁ E₂ : ExtSpec) : (ExtMap.fst E₁ E₂).Thin := fun _ =>
  le_of_eq (Finset.card_singleton _)
theorem thin_snd (E₁ E₂ : ExtSpec) : (ExtMap.snd E₁ E₂).Thin := fun _ =>
  le_of_eq (Finset.card_singleton _)
theorem thin_toNone (E : ExtSpec) : (ExtMap.toNone E).Thin := fun _ => Nat.zero_le _
theorem Thin.pair {g₁ : ExtMap E E₁} {g₂ : ExtMap E E₂} (h₁ : g₁.Thin) (h₂ : g₂.Thin) :
    (ExtMap.pair g₁ g₂).Thin := fun q => match q with
  | .inl q => h₁ q
  | .inr q => h₂ q
open Classical in
theorem Thin.comp {g' : ExtMap E' E''} {g : ExtMap E E'} (h' : g'.Thin) (h : g.Thin) :
    (g'.comp g).Thin :=
  fun q => (card_biUnion_thin _ _ h).trans (h' q)

end ExtMap

/-- The numbers of openings when further oracles are handed on. -/
def OpenB.keep (o : OpenB) : OpenB := ⟨o.n, o.nE, max o.bl 1, max o.bE 1⟩

namespace IOR
variable {X X' Xi Xi' Xo Xo' Z : Type}
  {E E' Ei Ei' Eo Eo' F : ExtSpec} {W W' Wi Wi' Wo Wo' Wz : Type} {lam : ℕ}

/-! ## 1. Numbers of openings -/

theorem opensLe_keepX {R : IOR Xi Ei Xo Eo} {o : OpenB} (h : R.OpensLe o) (Z : Type) :
    (R.keepX Z).OpensLe o := ⟨h.tot, h.ext⟩

open Classical in
/-- What `R.pre f g` opens in its implicit instance, at a thin g, the sources of later queries
counted: no more positions than R opens in its own. -/
theorem card_ext_pre (R : IOR Xi Ei Xo Eo) (f : Xi' → Option Xi) {g : ExtMap Ei' Ei} (hg : g.Thin)
    (ρ : Rho R.shape) (U : Finset Eo.Pos) :
    ((R.pre f g).extReads ρ ∪ U.biUnion ((R.pre f g).srcE ρ)).card ≤
      (R.extReads ρ ∪ U.biUnion (R.srcE ρ)).card := by
  refine le_trans (Finset.card_le_card ?_) (card_biUnion_thin _ g.src hg)
  intro p hp
  rcases Finset.mem_union.1 hp with h | h
  · have h' : p ∈ (R.extReads ρ).biUnion g.src := h
    obtain ⟨q, hq, hpq⟩ := Finset.mem_biUnion.1 h'
    exact Finset.mem_biUnion.2 ⟨q, Finset.mem_union_left _ hq, hpq⟩
  · obtain ⟨u, hu, h⟩ := Finset.mem_biUnion.1 h
    have h' : p ∈ (R.srcE ρ u).biUnion g.src := h
    obtain ⟨q, hq, hpq⟩ := Finset.mem_biUnion.1 h'
    exact Finset.mem_biUnion.2 ⟨q, Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨u, hu, hq⟩), hpq⟩

theorem opensLe_pre {R : IOR Xi Ei Xo Eo} {o : OpenB} (h : R.OpensLe o) (f : Xi' → Option Xi)
    {g : ExtMap Ei' Ei} (hg : g.Thin) : (R.pre f g).OpensLe o :=
  ⟨fun ρ U => le_trans (Nat.add_le_add_left (card_ext_pre R f hg ρ U) _) (h.tot ρ U),
    fun ρ U => le_trans (card_ext_pre R f hg ρ U) (h.ext ρ U)⟩

open Classical in
theorem sub_srcO_post (R : IOR Xi Ei Xo Eo) (f : Xo → Option Xo') (g : ExtMap Eo Eo')
    (ρ : Rho R.shape) (U : Finset Eo'.Pos) :
    (R.post f g).reads ρ ∪ U.biUnion ((R.post f g).srcO ρ) ⊆
      R.reads ρ ∪ (U.biUnion g.src).biUnion (R.srcO ρ) := by
  intro p hp
  rcases Finset.mem_union.1 hp with h | h
  · exact Finset.mem_union_left _ h
  · obtain ⟨u, hu, h⟩ := Finset.mem_biUnion.1 h
    have h' : p ∈ (g.src u).biUnion (R.srcO ρ) := h
    obtain ⟨q, hq, hpq⟩ := Finset.mem_biUnion.1 h'
    exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨q, Finset.mem_biUnion.2 ⟨u, hu, hq⟩, hpq⟩)

open Classical in
theorem sub_srcE_post (R : IOR Xi Ei Xo Eo) (f : Xo → Option Xo') (g : ExtMap Eo Eo')
    (ρ : Rho R.shape) (U : Finset Eo'.Pos) :
    (R.post f g).extReads ρ ∪ U.biUnion ((R.post f g).srcE ρ) ⊆
      R.extReads ρ ∪ (U.biUnion g.src).biUnion (R.srcE ρ) := by
  intro p hp
  rcases Finset.mem_union.1 hp with h | h
  · exact Finset.mem_union_left _ h
  · obtain ⟨u, hu, h⟩ := Finset.mem_biUnion.1 h
    have h' : p ∈ (g.src u).biUnion (R.srcE ρ) := h
    obtain ⟨q, hq, hpq⟩ := Finset.mem_biUnion.1 h'
    exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨q, Finset.mem_biUnion.2 ⟨u, hu, hq⟩, hpq⟩)

open Classical in
theorem opensLe_post {R : IOR Xi Ei Xo Eo} {o : OpenB} (h : R.OpensLe o) (f : Xo → Option Xo')
    {g : ExtMap Eo Eo'} (hg : g.Thin) : (R.post f g).OpensLe o :=
  ⟨fun ρ U =>
      le_trans (Nat.add_le_add (Finset.card_le_card (sub_srcO_post R f g ρ U))
          (Finset.card_le_card (sub_srcE_post R f g ρ U)))
        (le_trans (h.tot ρ (U.biUnion g.src))
          (Nat.add_le_add_left (Nat.mul_le_mul_left _ (card_biUnion_thin U g.src hg)) _)),
    fun ρ U =>
      le_trans (Finset.card_le_card (sub_srcE_post R f g ρ U))
        (le_trans (h.ext ρ (U.biUnion g.src))
          (Nat.add_le_add_left (Nat.mul_le_mul_left _ (card_biUnion_thin U g.src hg)) _))⟩

/-- The queries to the block's own new oracles, and to the oracles handed on. -/
def toL {Eo F : ExtSpec} (U : Finset (Eo.prod F).Pos) : Finset Eo.Pos :=
  Finset.toLeft (α := Eo.Pos) (β := F.Pos) U
def toR {Eo F : ExtSpec} (U : Finset (Eo.prod F).Pos) : Finset F.Pos :=
  Finset.toRight (α := Eo.Pos) (β := F.Pos) U
theorem card_toL_add_toR {Eo F : ExtSpec} (U : Finset (Eo.prod F).Pos) :
    (toL U).card + (toR U).card = U.card :=
  Finset.card_toLeft_add_card_toRight (α := Eo.Pos) (β := F.Pos)

open Classical in
theorem sub_srcO_keepE (R : IOR Xi Ei Xo Eo) (F : ExtSpec)
    (ρ : Rho R.shape) (U : Finset (Eo.prod F).Pos) :
    (R.keepE F).reads ρ ∪ U.biUnion ((R.keepE F).srcO ρ) ⊆
      R.reads ρ ∪ (toL U).biUnion (R.srcO ρ) := by
  intro p hp
  rcases Finset.mem_union.1 hp with h | h
  · exact Finset.mem_union_left _ h
  · obtain ⟨u, hu, h⟩ := Finset.mem_biUnion.1 h
    rcases u with u | u
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨u, Finset.mem_toLeft.2 hu, h⟩)
    · exact absurd h (Finset.notMem_empty p)

open Classical in
theorem sub_srcE_keepE (R : IOR Xi Ei Xo Eo) (F : ExtSpec) [dE : DecidableEq (Ei.prod F).Pos]
    (ρ : Rho R.shape) (U : Finset (Eo.prod F).Pos) :
    (R.keepE F).extReads ρ ∪ U.biUnion ((R.keepE F).srcE ρ) ⊆
      ((R.extReads ρ ∪ (toL U).biUnion (R.srcE ρ)).disjSum (toR U) : Finset (Ei.Pos ⊕ F.Pos)) := by
  intro p hp
  rcases Finset.mem_union.1 hp with h | h
  · have h' : p ∈ (R.extReads ρ).map Function.Embedding.inl := h
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.1 h'
    exact Finset.inl_mem_disjSum.2 (Finset.mem_union_left _ hq)
  · obtain ⟨u, hu, h⟩ := Finset.mem_biUnion.1 h
    rcases u with u | u
    · have h' : p ∈ (R.srcE ρ u).map Function.Embedding.inl := h
      obtain ⟨q, hq, rfl⟩ := Finset.mem_map.1 h'
      exact Finset.inl_mem_disjSum.2
        (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨u, Finset.mem_toLeft.2 hu, hq⟩))
    · have h' : p ∈ ({Sum.inr u} : Finset (Ei.Pos ⊕ F.Pos)) := h
      rw [Finset.mem_singleton.1 h']
      exact Finset.inr_mem_disjSum.2 (Finset.mem_toRight.2 hu)

/-- a·x + y ≤ max a 1 · (x + y) -/
theorem mul_add_le_max (a x y : ℕ) : a * x + y ≤ max a 1 * (x + y) := by
  rw [Nat.mul_add]
  exact Nat.add_le_add (Nat.mul_le_mul_right _ (le_max_left _ _))
    (le_trans (le_of_eq (Nat.one_mul y).symm) (Nat.mul_le_mul_right _ (le_max_right _ _)))

open Classical in
theorem opensLe_keepE {R : IOR Xi Ei Xo Eo} {o : OpenB} (h : R.OpensLe o) (F : ExtSpec) :
    (R.keepE F).OpensLe o.keep := by
  refine ⟨fun ρ U => ?_, fun ρ U => ?_⟩
  · have h1 := Finset.card_le_card (sub_srcO_keepE R F ρ U)
    have h2 := Finset.card_le_card
      (sub_srcE_keepE (dE := fun a b => Classical.propDecidable (a = b)) R F ρ U)
    rw [Finset.card_disjSum] at h2
    have h3 := h.tot ρ (toL U)
    have h4 := mul_add_le_max o.bl (toL U).card (toR U).card
    rw [card_toL_add_toR] at h4
    show _ ≤ o.n + max o.bl 1 * U.card
    refine le_trans (Nat.add_le_add h1 h2) ?_
    refine le_trans (le_of_eq (Nat.add_assoc _ _ _).symm) ?_
    refine le_trans (Nat.add_le_add_right h3 _) ?_
    omega
  · have h2 := Finset.card_le_card
      (sub_srcE_keepE (dE := fun a b => Classical.propDecidable (a = b)) R F ρ U)
    rw [Finset.card_disjSum] at h2
    have h3 := h.ext ρ (toL U)
    have h4 := mul_add_le_max o.bE (toL U).card (toR U).card
    rw [card_toL_add_toR] at h4
    show _ ≤ o.nE + max o.bE 1 * U.card
    refine le_trans h2 ?_
    omega

theorem opensLe_on {R : IOR Xi Ei Xo Eo} {o : OpenB} (h : R.OpensLe o) (Z : Type) (F : ExtSpec)
    (fi : X → Option (Xi × Z)) {gi : ExtMap E (Ei.prod F)} (fo : Xo × Z → Option X')
    {go : ExtMap (Eo.prod F) E'} (hi : gi.Thin) (ho : go.Thin) :
    (R.on Z F fi gi fo go).OpensLe o.keep :=
  opensLe_post (opensLe_pre (opensLe_keepE (opensLe_keepX h Z) F) fi hi) fo ho

open Classical in
theorem opensLe_pure (f : Xi → Option Xo) {g : ExtMap Ei Eo} (hg : g.Thin) :
    (IOR.pure f g).OpensLe ⟨0, 0, 1, 1⟩ := by
  have key : ∀ U : Finset Eo.Pos,
      ((∅ : Finset Ei.Pos) ∪ U.biUnion g.src).card ≤ U.card := fun U => by
    rw [Finset.empty_union]
    exact card_biUnion_thin U g.src hg
  have key0 : ∀ U : Finset Eo.Pos,
      ((∅ : Finset (OPos (IOR.pure f g).shape)) ∪ U.biUnion fun _ => ∅).card = 0 := fun U => by
    rw [Finset.empty_union, Finset.card_eq_zero]
    exact Finset.eq_empty_of_forall_notMem fun p hp => by
      obtain ⟨_, _, h⟩ := Finset.mem_biUnion.1 hp
      exact absurd h (Finset.notMem_empty p)
  refine ⟨fun ρ U => ?_, fun ρ U => ?_⟩
  · show ((∅ : Finset (OPos (IOR.pure f g).shape)) ∪ U.biUnion fun _ => ∅).card +
        ((∅ : Finset Ei.Pos) ∪ U.biUnion g.src).card ≤ 0 + 1 * U.card
    rw [key0, Nat.zero_add, Nat.zero_add, Nat.one_mul]
    exact key U
  · show ((∅ : Finset Ei.Pos) ∪ U.biUnion g.src).card ≤ 0 + 1 * U.card
    rw [Nat.zero_add, Nat.one_mul]
    exact key U

/-! ## 2. The data -/

/-- The data of a step without rounds. -/
def SubData.pure (lam : ℕ) (f : Xi → Option Xo) (g : ExtMap Ei Eo) (m : Xi × Wi → Xo × Wo) :
    (IOR.pure f g).SubData (Honest.pure f g m) lam where
  pt := ()
  pos := ()
  dr := ()
  coin := Num.ofFinEnum Unit
  decBad := fun _ => isFalse fun h => h
  decHid := fun _ _ _ => isFalse fun h => h
  ob := ⟨0, 0, 1, 1⟩

theorem subFit_pure (lam : ℕ) (f : Xi → Option Xo) {g : ExtMap Ei Eo} (hg : g.Thin)
    (m : Xi × Wi → Xo × Wo) (κ₀ : ℝ≥0∞) :
    SubFit (SubData.pure lam f g m) κ₀ :=
  ⟨trivial, opensLe_pure f hg⟩

/-- The data for the honest side whose last witness forgets a further part (`Honest.dropZ`,
Ior/ChainZ.lean). -/
def SubData.dropZ {R : IOR Xi Ei Xo Eo} {H : R.Honest Wi (Wo × Wz)} (D : R.SubData H lam) :
    R.SubData H.dropZ lam :=
  ⟨D.pt, D.pos, D.dr, D.coin, D.decBad, D.decHid, D.ob⟩

theorem subFit_dropZ {R : IOR Xi Ei Xo Eo} {H : R.Honest Wi (Wo × Wz)} {D : R.SubData H lam}
    {κ₀ : ℝ≥0∞} (h : SubFit D κ₀) : SubFit D.dropZ κ₀ :=
  ⟨h.good, h.opens⟩

namespace SubData
variable {R : IOR Xi Ei Xo Eo} {H : R.Honest Wi Wo} (D : R.SubData H lam)

def keepX (Z : Type) : (R.keepX Z).SubData (H.keepX Z) lam :=
  ⟨D.pt, D.pos, D.dr, D.coin, D.decBad, fun w a ρ => D.decHid w a.1 ρ, D.ob⟩
def keepE (F : ExtSpec) : (R.keepE F).SubData (H.keepE F) lam :=
  ⟨D.pt, D.pos, D.dr, D.coin, D.decBad, D.decHid, D.ob.keep⟩
def carry (Wz : Type) : R.SubData (H.carry Wz) lam :=
  ⟨D.pt, D.pos, D.dr, D.coin, D.decBad, fun w x ρ => D.decHid w.1 x ρ, D.ob⟩
def pre (f : Xi' → Option Xi) (g : ExtMap Ei' Ei) (m : Xi' × Wi' → Xi × Wi) :
    (R.pre f g).SubData (H.pre f g m) lam :=
  ⟨D.pt, D.pos, D.dr, D.coin, D.decBad, fun w x ρ => D.decHid (m (x, w)).2 (m (x, w)).1 ρ, D.ob⟩
def post (f : Xo → Option Xo') (g : ExtMap Eo Eo') (m : Xo × Wo → Xo' × Wo') :
    (R.post f g).SubData (H.post f g m) lam :=
  ⟨D.pt, D.pos, D.dr, D.coin, D.decBad, D.decHid, D.ob⟩

/-- The data of a block on a part of a larger statement. -/
def on (Z : Type) (F : ExtSpec) (Wz : Type) (fi : X → Option (Xi × Z))
    (gi : ExtMap E (Ei.prod F)) (fo : Xo × Z → Option X') (go : ExtMap (Eo.prod F) E')
    (mi : X × W → (Xi × Z) × (Wi × Wz)) (mo : (Xo × Z) × (Wo × Wz) → X' × W') :
    (R.on Z F fi gi fo go).SubData (H.on Z F Wz fi gi fo go mi mo) lam :=
  ((((D.keepX Z).keepE F).carry Wz).pre fi gi mi).post fo go mo

end SubData

/-! ## 3. The conditions -/

section Fit
variable {R : IOR Xi Ei Xo Eo} {H : R.Honest Wi Wo} {D : R.SubData H lam} {κ₀ : ℝ≥0∞}

theorem subFit_keepX (h : SubFit D κ₀) (Z : Type) : SubFit (D.keepX Z) κ₀ :=
  ⟨h.good, opensLe_keepX h.opens Z⟩
theorem subFit_keepE (h : SubFit D κ₀) (F : ExtSpec) : SubFit (D.keepE F) κ₀ :=
  ⟨h.good, opensLe_keepE h.opens F⟩
theorem subFit_carry (h : SubFit D κ₀) (Wz : Type) : SubFit (D.carry Wz) κ₀ := ⟨h.good, h.opens⟩
theorem subFit_pre (h : SubFit D κ₀) (f : Xi' → Option Xi) {g : ExtMap Ei' Ei}
    (hg : g.Thin) (m : Xi' × Wi' → Xi × Wi) : SubFit (D.pre f g m) κ₀ :=
  ⟨h.good, opensLe_pre h.opens f hg⟩
theorem subFit_post (h : SubFit D κ₀) (f : Xo → Option Xo') {g : ExtMap Eo Eo'}
    (hg : g.Thin) (m : Xo × Wo → Xo' × Wo') : SubFit (D.post f g m) κ₀ :=
  ⟨h.good, opensLe_post h.opens f hg⟩
theorem subFit_on (h : SubFit D κ₀) (Z : Type) (F : ExtSpec) (Wz : Type)
    (fi : X → Option (Xi × Z)) {gi : ExtMap E (Ei.prod F)} (fo : Xo × Z → Option X')
    {go : ExtMap (Eo.prod F) E'} (hi : gi.Thin) (ho : go.Thin)
    (mi : X × W → (Xi × Z) × (Wi × Wz)) (mo : (Xo × Z) × (Wo × Wz) → X' × W') :
    SubFit (D.on Z F Wz fi gi fo go mi mo) κ₀ :=
  subFit_post (subFit_pre (subFit_carry (subFit_keepE (subFit_keepX h Z) F) Wz) fi hi mi) fo ho mo

/-- The numbers of the samplers' blocks do not change (by definition). -/
theorem tot_on (Z : Type) (F : ExtSpec) (Wz : Type) (fi : X → Option (Xi × Z))
    (gi : ExtMap E (Ei.prod F)) (fo : Xo × Z → Option X') (go : ExtMap (Eo.prod F) E')
    (mi : X × W → (Xi × Z) × (Wi × Wz)) (mo : (Xo × Z) × (Wo × Wz) → X' × W') :
    (D.on Z F Wz fi gi fo go mi mo).tot = D.tot ∧ (D.on Z F Wz fi gi fo go mi mo).maxB = D.maxB :=
  ⟨rfl, rfl⟩
theorem tot_pre (f : Xi' → Option Xi) (g : ExtMap Ei' Ei) (m : Xi' × Wi' → Xi × Wi) :
    (D.pre f g m).tot = D.tot ∧ (D.pre f g m).maxB = D.maxB := ⟨rfl, rfl⟩
theorem tot_post (f : Xo → Option Xo') (g : ExtMap Eo Eo') (m : Xo × Wo → Xo' × Wo') :
    (D.post f g m).tot = D.tot ∧ (D.post f g m).maxB = D.maxB := ⟨rfl, rfl⟩

end Fit

end IOR
end Iop
