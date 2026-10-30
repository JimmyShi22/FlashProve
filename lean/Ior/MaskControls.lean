-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/MaskControls.lean: controls for `Fresh` and `Blind` (masks sent in advance): what the two
properties refuse, and where `Fresh` alone says nothing.

Small honest sides and theorems on them, with their proofs, on the test bed of
Ior/KnowCollRulesMaskTest.lean (its IOR `R`, prefix `H₁`, parameters `D`). `Fresh`, `Blind`:
`Honest.Fresh`, `Honest.Blind`, Ior/KnowCollRulesMask.lean (reading: the argument `kc` of `Fresh`,
`kci`, `kco` of `Blind`; overwriting: `put`, and `puti`, `puto`).

Main names:
  `Hc`: one coin laid at two places.
  `fresh1`, `fresh2`: each place is Fresh at the reading that forgets the other.
  `pair_not_fresh`: the pair is not Fresh.
  `one_not_fresh_whole`: neither place is Fresh at the one reading that sees both (stated for the
    first place: the overwriting `fun M k => (k.1, M, k.2.2)`).
  `fresh_idle`: Fresh at an overwriting that does nothing holds of every honest side (stated for
    the honest sides of `R`, with `Bool` for `Mk`, at the budget `anyT`): alone it has no content;
    its content comes from the masked block's law at the same overwriting.
  `Hb`: the block that says s + M and hands the witness on.
  `used_not_blind`: that block is not Blind for the mask.
  `used_not_fresh`: after the block has used it, the mask is not fresh any more, in this sense:
    `¬ (H₁.seq Hb).Fresh all (budSeq R R anyT anyT) D.kc D.Mk D.put`: the property itself, not the
    calculus.

Limits (what they are worth): negative controls: the properties are not true of everything. So that
two pending blocks may name one entry (Cb/Ld/LdMia.lean, (6)) is harmless: the first use breaks
"hands on" for the other. (shown here of the one block `Hb`: `used_not_blind`, `used_not_fresh`; no
theorem here names `LdMv.Hands`) At the toy reference requests themselves there is no negative
control (of `Fresh`, `Blind`, `LdMv.Hands`: by reading).
Terms: lean/GLOSSARY.md.
-/
import Ior.KnowCollRulesMaskTest
import Ior.FreshJoinProofs

set_option autoImplicit false

namespace Iop.MaskCtl
open Prob IOR MaskTest

/-! (1) One coin laid at two places: each place is Fresh at the reading that forgets the other; the
pair is not Fresh; neither place is Fresh at the one reading that sees both (stated for the first
place: `one_not_fresh_whole`). -/
def Hc : R.Honest Bool (Bool × Bool × Bool) where
  Coin := Bool
  strat := fun s _ c => (((), false), fun _ => ((), (s, c, c)))
  Bad := ∅
  Hid := fun _ _ => ∅

theorem freec (w : Bool) (x : Unit) : Hc.withheld w x = ∅ := Set.union_empty _

def k1 : Bool × Bool × Bool → Bool × Bool := fun w => (w.1, w.2.1)
def k2 : Bool × Bool × Bool → Bool × Bool := fun w => (w.1, w.2.2)
def p1 : Bool → Bool × Bool → Bool × Bool := fun M k => (k.1, M)

theorem fresh1 : Hc.Fresh all anyT k1 Bool p1 := by
  intro x y s _ ρ _ T _
  have l : (unif (Bool × Bool)).map (fun a =>
        ((Hc.seen k1 s x ρ T a.1).1,
          (Hc.seen k1 s x ρ T a.1).2.1,
          p1 a.2 (Hc.seen k1 s x ρ T a.1).2.2)) =
      (unif Bool).map (Hc.seen k1 s x ρ T) := by
    have c : (fun a : Bool × Bool =>
          ((Hc.seen k1 s x ρ T a.1).1,
            (Hc.seen k1 s x ρ T a.1).2.1,
            p1 a.2 (Hc.seen k1 s x ρ T a.1).2.2)) =
        (Hc.seen k1 s x ρ T) ∘ Prod.snd := rfl
    rw [c]
    exact ((PMF.map_comp (Prod.snd : Bool × Bool → Bool) (unif (Bool × Bool))
        (fun c : Bool => Hc.seen k1 s x ρ T c)).symm).trans
      (by rw [map_snd_unif]; rfl)
  exact l

theorem fresh2 : Hc.Fresh all anyT k2 Bool p1 := by
  intro x y s _ ρ _ T _
  have l : (unif (Bool × Bool)).map (fun a =>
        ((Hc.seen k2 s x ρ T a.1).1,
          (Hc.seen k2 s x ρ T a.1).2.1,
          p1 a.2 (Hc.seen k2 s x ρ T a.1).2.2)) =
      (unif Bool).map (Hc.seen k2 s x ρ T) := by
    have c : (fun a : Bool × Bool =>
          ((Hc.seen k2 s x ρ T a.1).1,
            (Hc.seen k2 s x ρ T a.1).2.1,
            p1 a.2 (Hc.seen k2 s x ρ T a.1).2.2)) =
        (Hc.seen k2 s x ρ T) ∘ Prod.snd := rfl
    rw [c]
    exact ((PMF.map_comp (Prod.snd : Bool × Bool → Bool) (unif (Bool × Bool))
        (fun c : Bool => Hc.seen k2 s x ρ T c)).symm).trans
      (by rw [map_snd_unif]; rfl)
  exact l

theorem pair_not_fresh :
    ¬ Hc.Fresh all anyT (fun w : Bool × Bool × Bool => w) (Bool × Bool)
      (fun M k => (k.1, M.1, M.2)) := fun h => by
  have e := h () () false trivial ((), ()) (by rw [freec]; exact fun h => h) ∅ trivial
  have hm : (R.view ∅ (say false), (), ((false, true, false) : Bool × Bool × Bool)) ∈
      ((unif Hc.Coin).map
        (Hc.seen (fun w : Bool × Bool × Bool => w) false () ((), ()) ∅)).support := by
    rw [← e]
    exact (PMF.mem_support_map_iff _ _ _).2
      ⟨((false, (true, false)) : Hc.Coin × (Bool × Bool)), PMF.mem_support_uniformOfFintype _, rfl⟩
  obtain ⟨c, -, hc⟩ := (PMF.mem_support_map_iff _ _ _).1 hm
  have h2 : c = true := congrArg (fun z : View R × Unit × (Bool × Bool × Bool) => z.2.2.2.1) hc
  have h3 : c = false := congrArg (fun z : View R × Unit × (Bool × Bool × Bool) => z.2.2.2.2) hc
  rw [h2] at h3
  cases h3

theorem one_not_fresh_whole :
    ¬ Hc.Fresh all anyT (fun w : Bool × Bool × Bool => w) Bool
      (fun M k => (k.1, M, k.2.2)) := fun h => by
  have e := h () () false trivial ((), ()) (by rw [freec]; exact fun h => h) ∅ trivial
  have hm : (R.view ∅ (say false), (), ((false, true, false) : Bool × Bool × Bool)) ∈
      ((unif Hc.Coin).map
        (Hc.seen (fun w : Bool × Bool × Bool => w) false () ((), ()) ∅)).support := by
    rw [← e]
    exact (PMF.mem_support_map_iff _ _ _).2
      ⟨((false, true) : Hc.Coin × Bool), PMF.mem_support_uniformOfFintype _, rfl⟩
  obtain ⟨c, -, hc⟩ := (PMF.mem_support_map_iff _ _ _).1 hm
  have h2 : c = true := congrArg (fun z : View R × Unit × (Bool × Bool × Bool) => z.2.2.2.1) hc
  have h3 : c = false := congrArg (fun z : View R × Unit × (Bool × Bool × Bool) => z.2.2.2.2) hc
  rw [h2] at h3
  cases h3

/-! (1b) `Fresh` alone has no content at an overwriting that does nothing: every honest side is
Fresh for it (stated for the honest sides of `R`, with `Bool` for `Mk`, at the budget `anyT`:
`fresh_idle`). -/
theorem fresh_idle {Wi Wo Kc : Type} (H : R.Honest Wi Wo)
    (Ri : Unit → Unit → Wi → Prop) (kc : Wo → Kc) :
    H.Fresh Ri anyT kc Bool (fun _ k => k) := by
  intro x y w _ ρ _ T _
  have c : (fun a : H.Coin × Bool =>
        ((H.seen kc w x ρ T a.1).1, (H.seen kc w x ρ T a.1).2.1, (H.seen kc w x ρ T a.1).2.2)) =
      (H.seen kc w x ρ T) ∘ Prod.fst := rfl
  show (unif (H.Coin × Bool)).map (fun a : H.Coin × Bool =>
      ((H.seen kc w x ρ T a.1).1, (H.seen kc w x ρ T a.1).2.1, (H.seen kc w x ρ T a.1).2.2)) = _
  rw [c, ← PMF.map_comp, map_fst_unif]

/-! (2) Reuse: the block that says s + M and hands the witness on. -/
def Hb : R.Honest (Bool × Bool × Bool) (Bool × Bool × Bool) where
  Coin := Unit
  strat := fun w _ _ => (((), xor w.1 w.2.1), fun _ => ((), w))
  Bad := ∅
  Hid := fun _ _ => ∅

theorem used_not_blind : ¬ Hb.Blind D.kc D.kc D.Mk D.put D.put := fun h => by
  have := (h (false, false, false) (false, true, false) true () () ((), ()) rfl).1
  have h1 : true = false := congrArg (fun τ : Tr R.shape => τ.1.2) this
  cases h1

/-- After the block has used it, the mask is not fresh any more (the property itself, not the
calculus), in this sense: `¬ (H₁.seq Hb).Fresh all (budSeq R R anyT anyT) D.kc D.Mk D.put`. -/
theorem used_not_fresh :
    ¬ (H₁.seq Hb).Fresh all (budSeq R R anyT anyT) D.kc D.Mk D.put := fun h => by
  have e := h () () false trivial ((), (), ()) (by
    rintro ((h | h) | (h | ⟨_, _, h⟩)) <;> exact (h : False)) ∅ (fun _ _ _ _ => ⟨trivial, trivial⟩)
  let f : View (R.seq R) × Unit × (Bool × Bool) → Bool × (Bool × Bool) := fun z =>
    ((z.1.plains : Bool × Bool × Unit).2.1, z.2.2)
  have e' := congrArg (PMF.map f) e
  have hs := congrArg PMF.support e'
  have hm := (Set.ext_iff.1 hs (false, (false, true))).1
    ((PMF.mem_support_map_iff _ _ _).2
      ⟨_, (PMF.mem_support_map_iff _ _ _).2
          ⟨((((false, false), ()), true) : (H₁.seq Hb).Coin × Bool),
            PMF.mem_support_uniformOfFintype _,
            rfl⟩,
        rfl⟩)
  obtain ⟨z, hz, hf⟩ := (PMF.mem_support_map_iff _ _ _).1 hm
  obtain ⟨c, -, hc⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
  subst hc
  have h1 : xor false c.1.1 = false := congrArg Prod.fst hf
  have h2 : c.1.1 = true := congrArg (fun z : Bool × (Bool × Bool) => z.2.2) hf
  rw [h2] at h1
  cases h1

end Iop.MaskCtl
