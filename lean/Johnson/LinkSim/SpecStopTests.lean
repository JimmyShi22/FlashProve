-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/SpecStopTests.lean: small examples of an abort that depends on a private bit, and
of an oracle message read at one position of two. Tests of ExactOff (Johnson/LinkSim/Spec.lean),
of ShiftTo and of Shows (Johnson/LinkSim/SpecForm.lean).
Terms of this folder: Johnson/LinkSim/Spec.lean.

An abort on a private bit. ExactOff asks nothing at the verifier messages in Hid, the part of the
honest prover's abort set that may depend on the private input. So ExactOff at the empty U, by
itself, admits a prover that aborts depending on a private bit. On the way to the error terms 0 and
0, the only premise that excludes it is the second premise of Spec.fieldsZero: Hid is empty. The
protocol is askDrawn (Johnson/LinkSim/SpecFormTests.lean): the input oracle is two bits (y0, y1),
the private input, and the verifier reads the position that it samples. The prover sends y0 xor
coin, and aborts when the sampled bit equals y1.
  stop_passes      with Hid the set of verifier messages whose sampled bit equals y1, this prover
                   satisfies ExactOff at the empty U, against the simulator that sends its coin.
                   The abort tells y1, and the property does not see it.
  stop_not_empty   that prover does not satisfy "Hid is empty".
  stop_sent_fails  a prover that never aborts, but whose message depends on y1: y0 xor coin if y1
                   is 1, and a fixed bit if y1 is 0. No family of strategies satisfies ShiftTo at
                   all inputs and messages. At the sampled bit 0 the verifier reads y0 alone, and
                   two inputs with the same y0 and different y1 give a uniform bit against a fixed
                   one.

An oracle message read at one position. No other small example has an oracle. The second clause of
Shows (the oracles' symbols at the positions read) is tested here alone. In askOrc the private
input is a bit w, the prover sends an oracle message of two bits, and the verifier reads it at the
position that it samples.
  orc_bare_fails   the oracle message (w, w): no family.
  orc_split_holds  the oracle message (coin, coin xor w): a family, the one that sends (k, k) for
                   its coin k. Each position by itself is a uniform bit, and only one is read.

Limits. The protocols here are small examples and no part of any scheme.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.SpecFormTests
import Johnson.LinkSim.SameView
import Johnson.LinkSim.Shift

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.Toy3
open Prob
open _root_.Compile.Lifetime (SimOf)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.LinkSim.Toy2

/-! ## An abort on a private bit -/

/-- The bit that the verifier samples in the one round. -/
def drawn (ρ : Rho askDrawn.shape) : Bool := (show Bool × Unit from ρ).1

/-- The prover sends y0 xor coin. Its abort set Hid is the set of verifier messages whose sampled
bit equals y1. -/
def sideStop : Honest askDrawn (Bool × Bool) where
  Coin := Bool
  ext := fun w => w
  strat := fun w _ c => say id (xor w.1 c)
  Bad := ∅
  Hid := fun w _ => {ρ | drawn ρ = w.2}

/-- The simulator that sends its coin. -/
def simCoin : SimOf askDrawn :=
  simOfStrat askDrawn Bool (fun f => ((f false).getD false, (f true).getD false)) ∅
    fun _ _ _ k => say id k

/-- The prover that aborts depending on y1 satisfies ExactOff at the empty U. -/
theorem stop_passes : ExactOff sideStop (fun _ _ => True) simCoin ∅ := by
  intro w x _ ρ _ hH
  have hw : ρ ∉ sideStop.withheld w x := fun h => Or.elim h (fun h => h) hH
  have e1 : sideStop.output w x ρ = (unif Bool).map fun c =>
      some (askDrawn.dview x w ((say id (xor w.1 c)).run ρ).1) := if_neg hw
  have e2 : simCoin x ρ (askDrawn.extAns x ρ (sideStop.ext w)) = (unif Bool).map fun k =>
      some (askDrawn.dview x
        (((askDrawn.extAns x ρ w false).getD false, (askDrawn.extAns x ρ w true).getD false) :
          Bool × Bool) ((say id k).run ρ).1) := if_neg (Set.notMem_empty ρ)
  rw [e1, e2]
  refine map_eq_of_bij (xor w.1)
    (Function.Involutive.bijective fun c => by cases w.1 <;> cases c <;> rfl) _ _ fun c => ?_
  refine congrArg some (dview_run_eq askDrawn x _ _ _ _ ρ ⟨rfl, no_orc id _ _⟩ fun p hp => ?_)
  have hp' : askDrawn.extAns x ρ w p = some (twoBits.rd w p) := if_pos hp
  cases p with
  | false =>
    show w.1 = (askDrawn.extAns x ρ w false).getD false
    rw [hp']
    rfl
  | true =>
    show w.2 = (askDrawn.extAns x ρ w true).getD false
    rw [hp']
    rfl

/-- That prover's Hid is not empty. -/
theorem stop_not_empty : ¬ ∀ w x, sideStop.Hid w x = ∅ := by
  intro h
  have hm : ((true, ()) : Bool × Unit) ∈ sideStop.Hid (false, true) () := rfl
  rw [h] at hm
  exact hm

/-- A prover that never aborts and sends a fixed bit where y1 is 0: no family satisfies ShiftTo. -/
theorem stop_sent_fails : ¬ ∃ σ : Fam id Bool, ∀ w ρ,
    ShiftTo (sideOf id Bool fun w c => xor w.1 c && w.2) Bool σ w () ρ := by
  rintro ⟨σ, h⟩
  obtain ⟨c', e⟩ := sent_of_shift id (fun w (c : Bool) => xor w.1 c && w.2) σ (false, true)
    (false, false) (false, ()) (extAns_same id _ _ _ rfl) (h _ _) (h _ _) true
  cases c' <;> exact Bool.noConfusion e

/-! ## An oracle read at one position of two -/

/-- One round: an oracle message of two bits, nothing in the clear, one bit sampled by the
verifier. -/
@[reducible] def rOrc : Round where
  Orc := Bool × Bool
  Pos := Bool
  Sym := fun _ => Bool
  rd := fun o p => if p then o.2 else o.1
  Plain := Unit
  Chal := Bool
  dOrc := (false, false)
  dPlain := ()

/-- The verifier reads the oracle message at the position that it sampled. -/
@[reducible] def askOrc : InteractiveOracleProof Unit OnBytes.LinkSim.Toy.noExt where
  shape := [rOrc]
  blinded := fun _ => true
  extReads := fun _ _ => ∅
  reads := fun _ ρ _ => ({Sum.inl (show Bool × Unit from ρ).1} : Finset (Bool ⊕ Empty))
  accept := fun _ _ _ => true

/-- The strategy that sends the oracle message o. -/
def lay (o : Bool × Bool) : Strat askOrc.shape Unit := ((o, ()), fun _ => ())

/-- The honest prover that sends the oracle message f w c, for its private input w and its coin c.
Its abort set is empty. -/
def sideOrc (Coin : Type) [Fintype Coin] [Nonempty Coin] (f : Bool → Coin → Bool × Bool) :
    Honest askOrc Bool where
  Coin := Coin
  ext := fun _ => ()
  strat := fun w _ c => lay (f w c)
  Bad := ∅
  Hid := fun _ _ => ∅

/-- The families of strategies of a simulator with the coin type Ks. -/
abbrev FamO (Ks : Type) : Type :=
  Unit → Rho askOrc.shape → (Empty → Option Unit) → Ks → Strat askOrc.shape Unit

/-- The oracle message (w, w): no family. -/
theorem orc_bare_fails : ¬ ∃ σ : FamO Unit,
    ∀ w ρ, ShiftTo (sideOrc Unit fun w _ => (w, w)) Unit σ w () ρ := by
  rintro ⟨σ, h⟩
  obtain ⟨φ, -, hs⟩ := h true (false, ())
  obtain ⟨φ', -, hs'⟩ := h false (false, ())
  have hr : (Sum.inl false : Bool ⊕ Empty) ∈ ({Sum.inl false} : Finset (Bool ⊕ Empty)) :=
    Finset.mem_singleton.2 rfl
  have e1 := (hs ()).2 (Sum.inl false) (Or.inl hr)
  have e2 := (hs' ()).2 (Sum.inl false) (Or.inl hr)
  have e3 : (true : Bool) = false := e1.trans e2.symm
  exact Bool.noConfusion e3

/-- The oracle message (coin, coin xor w): the family that sends its coin at both positions. -/
theorem orc_split_holds : ∃ σ : FamO Bool,
    ∀ w ρ, ShiftTo (sideOrc Bool fun w c => (c, xor c w)) Bool σ w () ρ := by
  refine ⟨fun _ _ _ k => lay (k, k), fun w ρ => ?_⟩
  obtain ⟨d, u⟩ : Bool × Unit := ρ
  cases d with
  | false =>
    refine ⟨id, Function.bijective_id, fun c => ⟨rfl, fun p hp => ?_⟩⟩
    rcases hp with hp | hp
    · have e : p = Sum.inl false := Finset.mem_singleton.1 hp
      subst e
      rfl
    · exact Bool.noConfusion hp
  | true =>
    refine ⟨fun c => xor c w,
      Function.Involutive.bijective fun c => by cases w <;> cases c <;> rfl,
      fun c => ⟨rfl, fun p hp => ?_⟩⟩
    rcases hp with hp | hp
    · have e : p = Sum.inl true := Finset.mem_singleton.1 hp
      subst e
      rfl
    · exact Bool.noConfusion hp

end OnBytes.LinkSim.Toy3

#print axioms OnBytes.LinkSim.Toy3.stop_passes
#print axioms OnBytes.LinkSim.Toy3.stop_not_empty
#print axioms OnBytes.LinkSim.Toy3.stop_sent_fails
#print axioms OnBytes.LinkSim.Toy3.orc_bare_fails
#print axioms OnBytes.LinkSim.Toy3.orc_split_holds
