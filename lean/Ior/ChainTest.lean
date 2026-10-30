-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/ChainTest.lean: a test of the bundle (`Good`) of Ior/Chain.lean: what `Good` cannot say of an
interactive oracle reduction (IOR) whose last witness forgets what its hidden event reads, and how a
carried part of the witness cures it.

All statements are proved here.

The block: one round; the prover sends nothing; the verifier sends one bit. The witness is a bit.
The run is withheld, hidden, where the verifier's bit equals the witness: an event of probability
1/2 for every witness (`pr_ev`: at most 1/2), with no coin in play.

Main names:
  `H`: the honest side that ends with the trivial witness: the bit is forgotten.
  `Hz`: the honest side that ends with (trivial witness, the bit): the bit rides along.
  `good_shares_cover`: in general, under `g : Good R H A B ext P`: two input witnesses whose honest
    runs end in the same output witness have the same core (`keeps`), hence one cover: pHid pays for
    the union of their hidden sets.
  `never_good`: `H` is `Good` for no joints, cores, extractor and numbers with pHid < 1, though each
    single witness withholds one value of two. So the bundle is too strong a demand on an IOR that
    forgets what its event reads.
  `good_z`: `Hz` is `Good` (between the joints `A`, `B`: no condition), with pHid = 1/2: the core is
    the bit.
  `dropZ_eq`, `cured`: `H` is `Hz` with the further part dropped at the end, and by the closing rule
    of Ior/ChainZ.lean it has these properties that a parameter list asks for: the five clauses of
    `cured` (at the joint `A`: no condition), with the true number 1/2.

The lesson for a chain: whatever a later hidden event reads rides along as a further part of the
witness up to the last joint (`Honest.carry`, `Spec.good_frame`, Ior/Frame.lean), and is dropped
there (`Honest.dropZ`, `Spec.end_of_good`, Ior/ChainZ.lean).
Terms: lean/GLOSSARY.md.
-/
import Ior.ChainZ
import Blocks.Basic
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
namespace ChainTest
open Prob IOR Blocks
open scoped ENNReal

/-- Under `g`: two witnesses whose honest runs end in the same output witness have the same core,
hence one cover: the bound pHid pays for the union of their hidden sets. -/
theorem good_shares_cover {K Xi Xo Wi Wo : Type} {Ei Eo : ExtSpec} {R : IOR Xi Ei Xo Eo}
    {H : R.Honest Wi Wo} {A : Rels K Xi Ei Wi} {B : Rels K Xo Eo Wo}
    {ext : Ei.Str → Orcs R.shape → Wo → Wi} {P : Nums K R} (g : Good R H A B ext P) (w w' : Wi)
    (x x' : Xi) (c c' : H.Coin) (ρ ρ' : Rho R.shape)
    (h : ((H.strat w x c).run ρ).2.2 = ((H.strat w' x' c').run ρ').2.2) :
    prRho (H.Hid w x ∪ H.Hid w' x') ≤ P.pHid := by
  have hk : A.core w = A.core w' := by rw [← g.keeps w x c ρ, ← g.keeps w' x' c' ρ', h]
  refine le_trans (pr_mono _ ?_) (g.prCov (A.core w))
  intro σ hσ
  cases hσ with
  | inl h1 => exact g.cover w x h1
  | inr h2 => rw [hk]; exact g.cover w' x' h2

/-- Nothing from the prover, one bit from the verifier. -/
abbrev rd : Round := plainRound Unit Bool ()

/-- One round, one verifier bit; the verifier accepts. -/
def R : IOR Unit extNone Unit extNone where
  shape := [rd]
  blinded := fun _ => true
  extReads := fun _ => ∅
  reads := fun _ => ∅
  out := fun _ _ _ => some ()
  imp := fun _ _ => ()
  srcE := fun _ _ => ∅
  srcO := fun _ _ => ∅
  tie := fun _ _ => ∅

/-- The event: the verifier's bit equals k. -/
def ev (k : Bool) : Set (Rho R.shape) := {ρ | (show Bool × Unit from ρ).1 = k}

/-- The last witness forgets the bit. -/
def H : R.Honest Bool Unit where
  Coin := Unit
  strat := fun _ _ _ => ((((), ()), fun _ => ((), ())) : Strat [rd] (Unit × Unit))
  Bad := ∅
  Hid := fun w _ => ev w

/-- The bit rides along. -/
def Hz : R.Honest Bool (Unit × Bool) where
  Coin := Unit
  strat := fun w _ _ => ((((), ()), fun _ => ((), ((), w))) : Strat [rd] (Unit × (Unit × Bool)))
  Bad := ∅
  Hid := fun w _ => ev w

theorem pr_ev (k : Bool) : prRho (ev k) ≤ 1 / 2 := by
  have h := prRho_head_le rd [] (fun c => c = k) 1 (le_of_eq (cnt_eq_const k))
  have e : ((1 : ℕ) : ℝ≥0∞) / (Fintype.card rd.Chal : ℝ≥0∞) = 1 / 2 := by
    show ((1 : ℕ) : ℝ≥0∞) / (Fintype.card Bool : ℝ≥0∞) = 1 / 2
    rw [Fintype.card_bool]
    norm_num
  rw [e] at h
  exact h

/-- Whatever the joints, the kind of cores, the cover and the extractor: `H` is `Good` only with
pHid ≥ 1. -/
theorem never_good {K : Type} {A : Rels K Unit extNone Bool} {B : Rels K Unit extNone Unit}
    {ext : extNone.Str → Orcs R.shape → Unit → Bool} {P : Nums K R} (g : Good R H A B ext P) :
    1 ≤ P.pHid := by
  have h := good_shares_cover
    g true false () () () () ((true, ()) : Bool × Unit) ((true, ()) : Bool × Unit) rfl
  have hu : H.Hid true () ∪ H.Hid false () = Set.univ := by
    refine Set.eq_univ_of_forall fun σ => ?_
    cases hσ : (show Bool × Unit from σ).1 with
    | true => exact Or.inl hσ
    | false => exact Or.inr hσ
  rw [hu] at h
  refine le_trans (le_of_eq ?_) h
  exact (pr_eq_one_of_support_subset _ (Set.subset_univ _)).symm

/-- The joints: no condition; the core is the bit. -/
def A : Rels Bool Unit extNone Bool := ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, id⟩
def B : Rels Bool Unit extNone (Unit × Bool) :=
  ⟨fun _ _ _ => True, fun _ _ => True, fun _ => True, Prod.snd⟩
def P : Nums Bool R := ⟨((0, ()) : ℕ × Unit), 0, 1 / 2, fun _ _ => True, ev⟩

/-- With the bit carried along the block is `Good`, with the true number 1/2 (`pr_ev`: at most
1/2). -/
theorem good_z : Good R Hz A B (fun _ _ w => w.2) P where
  point := ⟨((plainPoint Unit Bool (), ()) : rd.IsPoint × Unit)⟩
  isLocal := ⟨fun _ _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  acc := fun _ _ _ _ _ _ _ => ⟨rfl, trivial⟩
  onOut := fun _ _ _ _ _ => trivial
  keeps := fun _ _ _ _ => rfl
  prBad := prRho_empty _ fun _ h => h
  cover := fun _ _ => le_refl _
  prCov := pr_ev
  know := fun _ _ => Doomed.of_forall _ _ fun _ _ _ _ _ => trivial
  exact := ⟨fun _ ρ T _ => PMF.pure (some (R.view T ((Hz.strat true () ()).run ρ).1)), fun x y w _ ρ hρ T _ => by
    rw [Hz.output_of_not_mem T (fun h => h.elim id hρ)]
    exact PMF.map_const (unif Unit) (some (R.view T ((Hz.strat true () ()).run ρ).1))⟩

/-- `H` is `Hz` with the further part dropped at the end. -/
theorem dropZ_eq : Hz.dropZ = H := rfl

/-- The cure: `H` has these properties that a parameter list asks for: the five clauses below (at
the joint `A`: no condition), with the true number 1/2 (`pr_ev`: at most 1/2). -/
theorem cured :
    H.Acc A.rel (fun _ _ _ => True) ∧
    prRho H.Bad ≤ 0 ∧
    (∀ w x, prRho (H.Hid w x) ≤ 1 / 2) ∧
    R.red.Know A.on A.relR (fun _ (_ : Unit) => True) (fun _ _ _ => false) P.err ∧
    H.Exact A.rel P.bud := by
  have h := end_of_good Bool Unit Unit extNone extNone R Bool Unit Bool Hz A B
    (fun _ _ w => w.2) P (fun _ _ _ => True) (fun _ _ => True) false good_z
    (fun _ _ _ _ => trivial) (fun _ _ _ => trivial)
  rw [dropZ_eq] at h
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

end ChainTest
end Iop
