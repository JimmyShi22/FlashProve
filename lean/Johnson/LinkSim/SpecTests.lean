-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/SpecTests.lean: ExactOff (Johnson/LinkSim/Spec.lean) can fail and can hold. Three
tests on a one-round protocol in which the prover sends one bit.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has. Three honest provers for the protocol qBit, and for each whether some simulator
satisfies ExactOff with U empty and every private input valid. The private input is a bit w. There
is no input oracle and no oracle message, and the verifier sends no challenge.
  sideLeak     sends w.                                No simulator is exact for it (leak_fails).
  sideStruck   samples a coin and still sends w.       No simulator is exact for it
                                                       (struck_fails).
  sideMask     samples a coin c and sends w xor c.     The simulator that sends a uniform bit
                                                       (simBit) is exact for it (mask_exact).
So the property separates a masked message from a bare one, and a coin that is sampled and not used
does not help. Both failures rest on bare_fails (this file's; SpecFormTests.lean has another of that
name, in namespace Toy2): no prover of this protocol with empty abort sets that sends w whatever its
coin has an exact simulator. Johnson/LinkSim/SpecFormTests.lean uses sideLeak.

Limits. The protocol is a small example and no part of any scheme: one bit, one round.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.Spec
import Prob.Linear

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.Toy
open Prob
open _root_.Compile.Lifetime (SimOf)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- One round: no oracle message, one bit in the clear, no challenge. -/
def rBit : Round where
  Orc := Unit
  Pos := Empty
  Sym := fun _ => Unit
  rd := fun _ _ => ()
  Plain := Bool
  Chal := Unit
  dOrc := ()
  dPlain := false

/-- No input oracle (no external strings). -/
def noExt : ExtSpec := ⟨Unit, Empty, Unit, fun _ _ => ()⟩

/-- The protocol of that one round. -/
def qBit : InteractiveOracleProof Unit noExt where
  shape := [rBit]
  blinded := fun _ => true
  extReads := fun _ _ => ∅
  reads := fun _ _ _ => ∅
  accept := fun _ _ _ => true

/-- The strategy that sends the bit b. -/
def say (b : Bool) : Strat qBit.shape Unit := (((), b), fun _ => ())

/-- It sends its private input. -/
def sideLeak : Honest qBit Bool where
  Coin := Unit
  ext := fun _ => ()
  strat := fun w _ _ => say w
  Bad := ∅
  Hid := fun _ _ => ∅

/-- It samples a coin and still sends its private input. -/
def sideStruck : Honest qBit Bool where
  Coin := Bool
  ext := fun _ => ()
  strat := fun w _ _ => say w
  Bad := ∅
  Hid := fun _ _ => ∅

/-- It samples a coin c and sends its private input xor c. -/
def sideMask : Honest qBit Bool where
  Coin := Bool
  ext := fun _ => ()
  strat := fun w _ c => say (xor w c)
  Bad := ∅
  Hid := fun _ _ => ∅

/-- The disclosed view of the run in which b is sent. -/
def viewOfBit (ρ : Rho qBit.shape) (b : Bool) : DView qBit := qBit.dview () () ((say b).run ρ).1

theorem viewOfBit_inj (ρ : Rho qBit.shape) {b b' : Bool} (h : viewOfBit ρ b = viewOfBit ρ b') :
    b = b' :=
  congrArg (fun v : DView qBit => (show Bool × Unit from v.plains).1) h

/-- The simulator that sends a uniform bit. -/
def simBit : SimOf qBit := fun _ ρ _ => (unif Bool).map fun b => some (viewOfBit ρ b)

/-- For an honest prover with empty abort sets, the output is the distribution, over a uniform coin,
of the disclosed view of its run. -/
theorem output_eq (H : Honest qBit Bool) (hB : H.Bad = ∅) (hH : H.Hid = fun _ _ => ∅) (w : Bool)
    (ρ : Rho qBit.shape) :
    H.output w () ρ =
      (unif H.Coin).map fun c => some (qBit.dview () (H.ext w) ((H.strat w () c).run ρ).1) := by
  unfold Honest.output
  rw [if_neg]
  unfold Honest.withheld
  rw [hB, hH]
  simp

/-- An honest prover with empty abort sets that sends w whatever its coin has no simulator that
satisfies ExactOff with U empty: its output is a point mass that differs between w = true and w =
false. -/
theorem bare_fails (H : Honest qBit Bool) (hB : H.Bad = ∅) (hH : H.Hid = fun _ _ => ∅)
    (he : ∀ w, H.ext w = ()) (hs : ∀ w c, H.strat w () c = say w) :
    ¬ ∃ S : SimOf qBit, ExactOff H (fun _ _ => True) S ∅ := by
  rintro ⟨S, hS⟩
  have ρ : Rho qBit.shape := Classical.arbitrary _
  have hno : ∀ w, ρ ∉ H.Hid w () := fun w => by
    rw [hH]
    exact Set.notMem_empty ρ
  have h1 := hS true () trivial ρ (Set.notMem_empty ρ) (hno true)
  have h0 := hS false () trivial ρ (Set.notMem_empty ρ) (hno false)
  rw [he] at h1 h0
  have e := h1.trans h0.symm
  rw [output_eq H hB hH, output_eq H hB hH] at e
  simp only [hs, he] at e
  have hm : some (viewOfBit ρ true) ∈
      ((unif H.Coin).map fun _ => some (viewOfBit ρ true)).support :=
    (PMF.mem_support_map_iff _ _ _).2
      ⟨Classical.arbitrary _, PMF.mem_support_uniformOfFintype _, rfl⟩
  have hm' : some (viewOfBit ρ true) ∈
      ((unif H.Coin).map fun _ => some (viewOfBit ρ false)).support := e ▸ hm
  obtain ⟨_, -, h⟩ := (PMF.mem_support_map_iff _ _ _).1 hm'
  exact Bool.false_ne_true (viewOfBit_inj ρ (Option.some.inj h))

/-- No simulator is exact for the prover that sends its private input. -/
theorem leak_fails : ¬ ∃ S : SimOf qBit, ExactOff sideLeak (fun _ _ => True) S ∅ :=
  bare_fails sideLeak rfl rfl (fun _ => rfl) fun _ _ => rfl

/-- Nor for the prover that samples a coin and does not use it. -/
theorem struck_fails : ¬ ∃ S : SimOf qBit, ExactOff sideStruck (fun _ _ => True) S ∅ :=
  bare_fails sideStruck rfl rfl (fun _ => rfl) fun _ _ => rfl

/-- The uniform bit is exact for the prover that sends its private input xor a coin. -/
theorem mask_exact : ExactOff sideMask (fun _ _ => True) simBit ∅ := by
  intro w x _ ρ _ _
  rw [output_eq sideMask rfl rfl]
  have hb : Function.Bijective (xor w) :=
    Function.Involutive.bijective fun c => by cases w <;> cases c <;> rfl
  show (unif Bool).map (fun c => some (viewOfBit ρ (xor w c))) =
    (unif Bool).map fun b => some (viewOfBit ρ b)
  exact ((congrArg (PMF.map fun b => some (viewOfBit ρ b))
    (map_unif_of_bijective hb)).symm.trans (PMF.map_comp _ _ _)).symm

end OnBytes.LinkSim.Toy

#print axioms OnBytes.LinkSim.Toy.leak_fails
#print axioms OnBytes.LinkSim.Toy.struck_fails
#print axioms OnBytes.LinkSim.Toy.mask_exact
