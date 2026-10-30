-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowCollRulesMaskTest.lean: a small case for "masks sent in advance": the rule is not empty,
and its conditions bite (of its conditions `Fresh` is shown to fail, at one reading:
`not_fresh_pad`).

A guard against vacuous notions (Ior/KnowCollRulesMask.lean: `Fresh`, `exact_seq_masked`;
Ior/Masked.lean: `MM`). Definitions, and theorems with their proofs.

The case: all values are bits. The witness is a secret bit s.
  The prefix (`H₁`): one round: the honest prover draws a mask M and a pad η, and sends y = M + η
    in the clear (think: the answer to a sample of an oracle that holds M and η). It hands on
    (s, M, η).
  The block (`H₂`): one round: the prover, without coins, sends s + M in the clear. Its own mask is
    M; what it reads of the witness is (s, M): not the pad.

Main names (what is shown):
  `mm`: the block has the item "masked messages": over a uniform M its message is a uniform bit.
  `block_not_exact`: the block alone is not zero knowledge in the exact form, in this sense:
    `¬ H₂.Exact all₂ anyT`: for a fixed witness its message tells s + M, and the simulator is given
    nothing.
  `shows_mask`: what the prefix shows depends on the mask, coin by coin: with the same pad, another
    mask gives another y. So the mask is no fresh coin of the block, and the rule for chains of
    Ior/ExactSeq.lean does not apply (`block_not_exact`).
  `fresh`: yet the prefix is Fresh for the block's reading: given y, the mask is uniform and
    independent of s, in this sense: `H₁.Fresh all anyT D.kc D.Mk D.put`.
  `not_fresh_pad`: with the pad in view it is not: for the reading (s, M, η), Fresh fails.
    (y, η tell M.)
  `prefix_exact`, `whole_exact`: the prefix is honest-verifier zero knowledge; so, by the rule, is
    the whole, in this sense: `H₁.ExactWith all anyT S₁`;
    `(H₁.seq H₂).ExactWith all (budSeq R R anyT fun _ _ => True) (simSeq S₁ (D.simOwn mm.noOrc))`.

Limits: this file says nothing beyond this case: no oracle, no further position, no verifier
message occurs in it.
Terms: lean/GLOSSARY.md.
-/
import Ior.KnowCollRulesMaskProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop.MaskTest
open Prob IOR

/-- a round: one bit in the clear, no oracle, an empty verifier message -/
def rB : Round where
  Orc := Unit
  Pos := Empty
  Sym := fun _ => Unit
  rd := fun _ p => p.elim
  Plain := Bool
  Chal := Unit
  dOrc := ()
  dPlain := false

/-- one such round between trivial statements; the verifier reads nothing and accepts -/
def R : IOR Unit extNone Unit extNone where
  shape := [rB]
  blinded := fun _ => true
  extReads := fun _ => ∅
  reads := fun _ => ∅
  out := fun _ _ _ => some ()
  imp := fun _ _ => ()
  srcE := fun _ _ => ∅
  srcO := fun _ _ => ∅
  tie := fun _ _ => ∅

/-- the transcript in which the prover says b -/
def say (b : Bool) : Tr R.shape := (((), b), (), ())

/-- The prefix: coins (M, η); it says M + η and hands on (s, M, η). -/
def H₁ : R.Honest Bool (Bool × Bool × Bool) where
  Coin := Bool × Bool
  strat := fun s _ c => (((), xor c.1 c.2), fun _ => ((), (s, c.1, c.2)))
  Bad := ∅
  Hid := fun _ _ => ∅

/-- The block: no coins; it says s + M. -/
def H₂ : R.Honest (Bool × Bool × Bool) Unit where
  Coin := Unit
  strat := fun w _ _ => (((), xor w.1 w.2.1), fun _ => ((), ()))
  Bad := ∅
  Hid := fun _ _ => ∅

/-- The parameters of the block's item: it reads (s, M); its own mask is M. -/
def D : MaskData R (Bool × Bool × Bool) where
  Kc := Bool × Bool
  kc := fun w => (w.1, w.2.1)
  Xp := Unit
  pub := fun _ => ()
  Mk := Bool
  put := fun M k => (k.1, M)
  Cl := fun _ _ => True
  msg := fun k _ _ => (xor k.1 k.2, ())
  sim := fun _ _ => (unif Bool).map fun b => (b, ())

def all : Unit → Unit → Bool → Prop := fun _ _ _ => True
def all₂ : Unit → Unit → Bool × Bool × Bool → Prop := fun _ _ _ => True
def anyT : Rho R.shape → Finset (OPos R.shape) → Prop := fun _ _ => True

theorem noOrc : IsEmpty (OPos R.shape) := ⟨fun p => Sum.elim Empty.elim Empty.elim p⟩

def xorE (a : Bool) : Bool ≃ Bool :=
  ⟨xor a, xor a, fun b => by cases a <;> cases b <;> rfl, fun b => by cases a <;> cases b <;> rfl⟩

/-- (M, η) ↦ (M + η, M) -/
def e₁ : Bool × Bool ≃ Bool × Bool :=
  ⟨fun c => (xor c.1 c.2, c.1),
    fun z => (z.2, xor z.1 z.2),
    fun c => by obtain ⟨a, b⟩ := c; cases a <;> cases b <;> rfl,
    fun c => by obtain ⟨a, b⟩ := c; cases a <;> cases b <;> rfl⟩

/-- ((M, η), M') ↦ ((M + η, M'), M) -/
def e₂ : (Bool × Bool) × Bool ≃ (Bool × Bool) × Bool :=
  ⟨fun a => ((xor a.1.1 a.1.2, a.2), a.1.1),
    fun b => ((b.2, xor b.1.1 b.2), b.1.2),
    fun c => by obtain ⟨⟨a, b⟩, d⟩ := c; cases a <;> cases b <;> cases d <;> rfl,
    fun c => by obtain ⟨⟨a, b⟩, d⟩ := c; cases a <;> cases b <;> cases d <;> rfl⟩

theorem free₁ (w : Bool) (x : Unit) : H₁.withheld w x = ∅ := Set.union_empty _
theorem free₂ (w : Bool × Bool × Bool) (x : Unit) : H₂.withheld w x = ∅ := Set.union_empty _

/-- The block has the item "masked messages". -/
theorem mm : H₂.MM D :=
  ⟨noOrc, free₂, fun _ _ _ _ => rfl, fun _ _ _ h => h,
    fun k _ _ _ =>
      map_unif_reindex (xorE k.1) (fun M => (xor k.1 M, ())) (fun b => (b, ())) fun _ => rfl⟩

/-- The block alone is not zero knowledge, in this sense: `¬ H₂.Exact all₂ anyT`. -/
theorem block_not_exact : ¬ H₂.Exact all₂ anyT :=
  masked_not_exact Unit Unit extNone extNone R (Bool × Bool × Bool) Unit H₂ D all₂ anyT mm
    (fun _ => rfl) () () () (false, false, false) (true, false, false) ((), ()) trivial trivial
    trivial (fun h => Bool.noConfusion (congrArg Prod.fst h))

/-- What the prefix shows depends on the mask. -/
theorem shows_mask (s η : Bool) (T : Finset (OPos R.shape)) :
    R.view T ((H₁.strat s () (false, η)).run ((), ())).1 ≠
      R.view T ((H₁.strat s () (true, η)).run ((), ())).1 := fun h => by
  have h1 : xor false η = xor true η := congrArg (fun V : View R => V.plains.1) h
  cases η <;> cases h1

/-- what is seen, as a function of (the bit said, the mask) -/
def φ (s : Bool) (T : Finset (OPos R.shape)) (z : Bool × Bool) :
    View R × Unit × (Bool × Bool) :=
  (R.view T (say z.1), (), (s, z.2))

/-- The prefix is Fresh for the block's reading. -/
theorem fresh : H₁.Fresh all anyT D.kc D.Mk D.put := by
  intro x y s _ ρ _ T _
  have r : (unif (Bool × Bool)).map (H₁.seen D.kc s x ρ T) = (unif (Bool × Bool)).map (φ s T) :=
    MaskKit.map_unif_of_equiv e₁ (φ s T)
  have l : (unif ((Bool × Bool) × Bool)).map (fun a =>
        ((H₁.seen D.kc s x ρ T a.1).1,
          (H₁.seen D.kc s x ρ T a.1).2.1,
          D.put a.2 (H₁.seen D.kc s x ρ T a.1).2.2)) =
      (unif (Bool × Bool)).map (φ s T) := by
    refine (MaskKit.map_unif_of_equiv e₂ (fun b => φ s T b.1)).trans ?_
    have c : (fun b : (Bool × Bool) × Bool => φ s T b.1) = φ s T ∘ Prod.fst := rfl
    rw [c, ← PMF.map_comp, map_fst_unif]
  exact l.trans r.symm

/-- With the pad in view the prefix is not Fresh. -/
theorem not_fresh_pad :
    ¬ H₁.Fresh all anyT (fun w : Bool × Bool × Bool => w) Bool
      (fun M k => (k.1, M, k.2.2)) := fun h => by
  have e := h () () false trivial ((), ()) (by rw [free₁]; exact fun h => h) ∅ trivial
  have hm : (R.view ∅ (say false), (), ((false, true, false) : Bool × Bool × Bool)) ∈
      ((unif H₁.Coin).map
        (H₁.seen (fun w : Bool × Bool × Bool => w) false () ((), ()) ∅)).support := by
    rw [← e]
    exact (PMF.mem_support_map_iff _ _ _).2
      ⟨(((false, false), true) : H₁.Coin × Bool), PMF.mem_support_uniformOfFintype _, rfl⟩
  obtain ⟨c, -, hc⟩ := (PMF.mem_support_map_iff _ _ _).1 hm
  have h1 : xor c.1 c.2 = false :=
    congrArg (fun z : View R × Unit × (Bool × Bool × Bool) => z.1.plains.1) hc
  have h2 : c.1 = true := congrArg (fun z : View R × Unit × (Bool × Bool × Bool) => z.2.2.2.1) hc
  have h3 : c.2 = false := congrArg (fun z : View R × Unit × (Bool × Bool × Bool) => z.2.2.2.2) hc
  rw [h2, h3] at h1
  cases h1

/-- the prefix's simulator: a uniform bit -/
def S₁ : Honest.Sim R := fun _ _ T _ =>
  (unif Bool).map fun b => some (R.view T (say b))

theorem prefix_exact : H₁.ExactWith all anyT S₁ := by
  intro x y s _ ρ _ T _
  rw [H₁.output_of_not_mem T (by rw [free₁]; exact fun h => h)]
  refine (MaskKit.map_unif_of_equiv e₁ (fun z : Bool × Bool => some (R.view T (say z.1)))).trans ?_
  have c : (fun z : Bool × Bool => some (R.view T (say z.1))) =
      (fun b => some (R.view T (say b))) ∘ Prod.fst := rfl
  rw [c, ← PMF.map_comp, map_fst_unif]
  rfl

theorem isLocal : R.IsLocal := ⟨fun _ _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => rfl⟩

theorem acc : H₁.Acc all all₂ := fun _ _ _ _ _ _ _ => ⟨rfl, trivial⟩

/-- By the rule, the whole is honest-verifier zero knowledge, in this sense:
`(H₁.seq H₂).ExactWith all (budSeq R R anyT fun _ _ => True) (simSeq S₁ (D.simOwn mm.noOrc))`. -/
theorem whole_exact :
    (H₁.seq H₂).ExactWith all (budSeq R R anyT fun _ _ => True) (simSeq S₁ (D.simOwn mm.noOrc)) :=
  exact_seq_masked Unit Unit Unit extNone extNone extNone R R Bool (Bool × Bool × Bool)
    Unit H₁ H₂ all all₂ anyT S₁ D mm isLocal acc prefix_exact fresh fun _ _ _ _ => trivial

end Iop.MaskTest
