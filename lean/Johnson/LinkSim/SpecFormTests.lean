-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/SpecFormTests.lean: small examples in which ShiftTo fails or holds, and four
vacuous instances of ExactOff.
Terms of this folder: Johnson/LinkSim/Spec.lean.

The small example. The input oracle is two bits (y0, y1), and it is the private input. There is one
round: the prover sends one bit in the clear, and the verifier samples one bit. The verifier reads
one position of the input oracle, pos applied to the bit it sampled. In askDrawn it reads the
position that it sampled; in askFirst it always reads position 0, that is y0.

What this file has. Six tests of ShiftTo (Johnson/LinkSim/SpecForm.lean). In each, the simulator's
coins have the honest prover's own coin type. "No family" means that no family of strategies σ,
whatever its definition, makes ShiftTo hold at all private inputs and all verifier messages.
  the honest prover sends                 protocol    verdict
  y0                                      askDrawn    no family        (bare_fails)
  y0, after sampling a coin it ignores    askDrawn    no family        (unused_fails)
  y0 xor y1                               askDrawn    no family        (both_fails)
  y0 and coin (half a mask)               askDrawn    no family        (half_fails)
  y0 xor coin                             askDrawn    a family         (masked_holds)
  y0                                      askFirst    a family         (read_holds): what is sent is
                                                      the symbol that the simulator is given
The four failures rest on sent_of_shift: if ShiftTo holds at two private inputs at which the
verifier reads the same, every bit that the prover can send at the first it can also send at the
second.
Four vacuous instances of ExactOff (Johnson/LinkSim/Spec.lean), for the honest prover that sends its
private input (sideLeak, Johnson/LinkSim/SpecTests.lean). Each holds and says nothing; the first
three hold for every simulator. Each is either accounted for in an error term elsewhere or is a
failure of completeness.
  idle_U       U is all verifier messages. (Accounted for: the measure of U enters the error term
               zL of the clause on the simulator.)
  idle_valid   no private input is valid.
  idle_Hid     the private part of the abort set (Hid) is all verifier messages. (Accounted for:
               its measure is the other error term, hL.)
  idle_Bad     the public part of the abort set (Bad) is all verifier messages, so both sides
               output none. (This enters no error term: what fails is completeness of the same
               honest prover.)

Limits. The protocols here are small examples and no part of any scheme.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.SpecForm
import Johnson.LinkSim.SpecTests

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.Toy2
open Prob
open _root_.Compile.Lifetime (SimOf)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- The input oracle: two bits; position false reads y0, position true reads y1. -/
@[reducible] def twoBits : ExtSpec := ⟨Bool × Bool, Bool, Bool, fun y p => if p then y.2 else y.1⟩

/-- One round: no oracle message, one bit sent in the clear, one bit sampled by the verifier. -/
@[reducible] def rAsk : Round where
  Orc := Unit
  Pos := Empty
  Sym := fun _ => Unit
  rd := fun _ _ => ()
  Plain := Bool
  Chal := Bool
  dOrc := ()
  dPlain := false

/-- The protocol: the verifier reads the input-oracle position pos b, where b is the bit it
sampled. -/
@[reducible] def ask (pos : Bool → Bool) : InteractiveOracleProof Unit twoBits where
  shape := [rAsk]
  blinded := fun _ => true
  extReads := fun _ ρ => ({pos (show Bool × Unit from ρ).1} : Finset Bool)
  reads := fun _ _ _ => ∅
  accept := fun _ _ _ => true

/-- It reads the position that it sampled. -/
abbrev askDrawn : InteractiveOracleProof Unit twoBits := ask id
/-- It always reads the position 0. -/
abbrev askFirst : InteractiveOracleProof Unit twoBits := ask fun _ => false

variable (pos : Bool → Bool)

/-- The strategy that sends the bit b. -/
def say (b : Bool) : Strat (ask pos).shape Unit := (((), b), fun _ => ())

/-- The bit that a transcript's plain part holds. -/
def bitOf (τ : Tr (ask pos).shape) : Bool := (show Bool × Unit from τ.plains).1

theorem bitOf_say (b : Bool) (ρ : Rho (ask pos).shape) : bitOf pos ((say pos b).run ρ).1 = b := rfl

/-- The honest prover that sends f w c, for its private input w and its coin c. Its abort set is
empty. -/
def sideOf (Coin : Type) [Fintype Coin] [Nonempty Coin] (f : Bool × Bool → Coin → Bool) :
    Honest (ask pos) (Bool × Bool) where
  Coin := Coin
  ext := fun w => w
  strat := fun w _ c => say pos (f w c)
  Bad := ∅
  Hid := fun _ _ => ∅

/-- The families of strategies of a simulator with the coin type Ks. -/
abbrev Fam (Ks : Type) : Type :=
  Unit → Rho (ask pos).shape → (Bool → Option Bool) → Ks → Strat (ask pos).shape Unit

/-- The lemma behind the four failures. Let ShiftTo hold at two private inputs w and w' at which the
verifier reads the same. Then for every coin c there is a coin c' such that the bit sent at w with c
is the bit sent at w' with c'. -/
theorem sent_of_shift {Coin Ks : Type} [Fintype Coin] [Nonempty Coin]
    (f : Bool × Bool → Coin → Bool) (σ : Fam pos Ks) (w w' : Bool × Bool)
    (ρ : Rho (ask pos).shape) (ha : (ask pos).extAns () ρ w = (ask pos).extAns () ρ w')
    (h : ShiftTo (sideOf pos Coin f) Ks σ w () ρ) (h' : ShiftTo (sideOf pos Coin f) Ks σ w' () ρ)
    (c : Coin) : ∃ c', f w c = f w' c' := by
  obtain ⟨φ, -, hs⟩ := h
  obtain ⟨φ', hφ', hs'⟩ := h'
  obtain ⟨c', hc'⟩ := hφ'.2 (φ c)
  refine ⟨c', ?_⟩
  have e1 := congrArg (fun π : Plains (ask pos).shape => (show Bool × Unit from π).1) (hs c).1
  have e2 := congrArg (fun π : Plains (ask pos).shape => (show Bool × Unit from π).1) (hs' c').1
  have ha' : (ask pos).extAns () ρ ((sideOf pos Coin f).ext w) =
      (ask pos).extAns () ρ ((sideOf pos Coin f).ext w') := ha
  rw [hc', ← ha'] at e2
  exact e1.trans e2.symm

/-- What the verifier reads of two private inputs that agree at the position read. -/
theorem extAns_same (w w' : Bool × Bool) (ρ : Rho (ask pos).shape)
    (h : twoBits.rd w (pos (show Bool × Unit from ρ).1) =
      twoBits.rd w' (pos (show Bool × Unit from ρ).1)) :
    (ask pos).extAns () ρ w = (ask pos).extAns () ρ w' := by
  funext p
  unfold InteractiveOracleProof.extAns
  by_cases hp : p ∈ (ask pos).extReads () ρ
  · rw [if_pos hp, if_pos hp]
    have e : p = pos (show Bool × Unit from ρ).1 := Finset.mem_singleton.1 hp
    rw [e, h]
  · rw [if_neg hp, if_neg hp]

/-- In this protocol the verifier reads no position of an oracle message, and every position is
blinded. -/
theorem no_orc (τ τ' : Tr (ask pos).shape) (p : OPos (ask pos).shape)
    (hp : p ∈ (ask pos).reads () τ.rho τ.plains ∨ (ask pos).blinded p = false) :
    τ.read p = τ'.read p := by
  rcases hp with h | h
  · exact absurd h (Finset.notMem_empty p)
  · exact Bool.noConfusion h

/-! ## Four failures -/

/-- The prover sends y0: no family. -/
theorem bare_fails : ¬ ∃ σ : Fam id Unit,
    ∀ w ρ, ShiftTo (sideOf id Unit fun w _ => w.1) Unit σ w () ρ := by
  rintro ⟨σ, h⟩
  obtain ⟨_, e⟩ := sent_of_shift id (fun w (_ : Unit) => w.1) σ (false, false) (true, false)
    (true, ()) (extAns_same id _ _ _ rfl) (h _ _) (h _ _) ()
  exact Bool.noConfusion e

/-- The prover samples a coin and sends y0 all the same: no family. -/
theorem unused_fails : ¬ ∃ σ : Fam id Bool,
    ∀ w ρ, ShiftTo (sideOf id Bool fun w _ => w.1) Bool σ w () ρ := by
  rintro ⟨σ, h⟩
  obtain ⟨_, e⟩ := sent_of_shift id (fun w (_ : Bool) => w.1) σ (false, false) (true, false)
    (true, ()) (extAns_same id _ _ _ rfl) (h _ _) (h _ _) false
  exact Bool.noConfusion e

/-- The prover sends y0 xor y1: no family. -/
theorem both_fails : ¬ ∃ σ : Fam id Unit,
    ∀ w ρ, ShiftTo (sideOf id Unit fun w _ => xor w.1 w.2) Unit σ w () ρ := by
  rintro ⟨σ, h⟩
  obtain ⟨_, e⟩ := sent_of_shift id (fun w (_ : Unit) => xor w.1 w.2) σ (false, false)
    (false, true) (false, ()) (extAns_same id _ _ _ rfl) (h _ _) (h _ _) ()
  exact Bool.noConfusion e

/-- The prover sends y0 and coin, half a mask: no family. -/
theorem half_fails : ¬ ∃ σ : Fam id Bool,
    ∀ w ρ, ShiftTo (sideOf id Bool fun w c => w.1 && c) Bool σ w () ρ := by
  rintro ⟨σ, h⟩
  obtain ⟨c', e⟩ := sent_of_shift id (fun w (c : Bool) => w.1 && c) σ (true, false) (false, false)
    (true, ()) (extAns_same id _ _ _ rfl) (h _ _) (h _ _) true
  exact Bool.noConfusion e

/-! ## Two that hold -/

/-- The prover sends y0 xor coin: the family that sends its coin. -/
theorem masked_holds : ∃ σ : Fam id Bool,
    ∀ w ρ, ShiftTo (sideOf id Bool fun w c => xor w.1 c) Bool σ w () ρ :=
  ⟨fun _ _ _ k => say id k, fun w ρ =>
    ⟨xor w.1, Function.Involutive.bijective fun c => by cases w.1 <;> cases c <;> rfl,
      fun _ => ⟨rfl, no_orc id _ _⟩⟩⟩

/-- The prover sends y0 and the verifier always reads position 0: the family that sends the symbol
it is given. -/
theorem read_holds : ∃ σ : Fam (fun _ => false) Unit,
    ∀ w ρ, ShiftTo (sideOf (fun _ => false) Unit fun w _ => w.1) Unit σ w () ρ :=
  ⟨fun _ _ ans _ => say _ ((ans false).getD false), fun w ρ =>
    ⟨id, Function.bijective_id, fun _ => ⟨by
      have e : (askFirst.extAns () ρ w false).getD false = w.1 := by
        unfold InteractiveOracleProof.extAns
        rw [if_pos (Finset.mem_singleton.2 rfl)]
        rfl
      show ((say _ w.1).run ρ).1.plains = ((say _ ((askFirst.extAns () ρ w false).getD false)).run
        ρ).1.plains
      rw [e], no_orc _ _ _⟩⟩⟩

/-! ## Four vacuous instances of ExactOff -/

open OnBytes.LinkSim.Toy (qBit sideLeak)

/-- Vacuous: U is all verifier messages. -/
theorem idle_U (S : SimOf qBit) : ExactOff sideLeak (fun _ _ => True) S Set.univ :=
  fun _ _ _ ρ hU _ => absurd (Set.mem_univ ρ) hU

/-- Vacuous: no private input is valid. -/
theorem idle_valid (S : SimOf qBit) : ExactOff sideLeak (fun _ _ => False) S ∅ :=
  fun _ _ hv => hv.elim

/-- Vacuous: the private part of the abort set is all verifier messages. -/
theorem idle_Hid (S : SimOf qBit) :
    ExactOff { sideLeak with Hid := fun _ _ => Set.univ } (fun _ _ => True) S ∅ :=
  fun _ _ _ ρ _ hH => absurd (Set.mem_univ ρ) hH

/-- Vacuous: the public part of the abort set is all verifier messages; both sides output none. -/
theorem idle_Bad :
    ExactOff { sideLeak with Bad := Set.univ } (fun _ _ => True) (fun _ _ _ => PMF.pure none)
      ∅ := by
  intro w x _ ρ _ _
  exact if_pos (Or.inl (Set.mem_univ ρ))

end OnBytes.LinkSim.Toy2

#print axioms OnBytes.LinkSim.Toy2.bare_fails
#print axioms OnBytes.LinkSim.Toy2.unused_fails
#print axioms OnBytes.LinkSim.Toy2.both_fails
#print axioms OnBytes.LinkSim.Toy2.half_fails
#print axioms OnBytes.LinkSim.Toy2.masked_holds
#print axioms OnBytes.LinkSim.Toy2.read_holds
#print axioms OnBytes.LinkSim.Toy2.idle_U
#print axioms OnBytes.LinkSim.Toy2.idle_valid
#print axioms OnBytes.LinkSim.Toy2.idle_Hid
#print axioms OnBytes.LinkSim.Toy2.idle_Bad
