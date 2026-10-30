-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/Seeded/Members.lean: members and non-members of the premises and of the property of
Hiop/Seeded/Whole.lean.

Definitions, statements and proofs. Nothing here is about the protocol of the release.
  Part 1, at ANY object: provers that withhold everything (`ProversS.silent`) meet every premise on
    provers, with the simulators that show nothing and with error 0 (`silent_ext`, `silent_good`).
    So no clause on provers is unmeetable; and so the property `HidesWhole` says little of provers
    unless completeness of the same provers stands beside it.
  Part 2, a toy object (`toy`): no rounds, words of length 0, two seeds; its answer at a seed is a
    given function of the index. If that function is constant, all premises hold together and the
    theorem applies (`toy_reads`, `toy_member`).
  Part 3, the negative test, at ANY object: if at some seed of Gs the honest answer tells the index
    (a map takes it back to the index) and there are two indices, then the premise on hiding fails
    (`not_reads_of_leak`), and the property fails for EVERY simulator and every z below 1/2
    (`one_le_of_leak`). At the toy object whose answer is the index: `leak_not_reads`,
    `leak_not_hides`.
The toy member is wholly idle: it guards against premises that contradict one another, and no more.
A member whose answer hangs on index, randomness and seed and whose prover shows something, and
negative tests on runs, are in Hiop/Seeded/Pad.lean.

Terms: lean/GLOSSARY.md.

-/
import Hiop.Seeded.WholeProof

set_option autoImplicit false

noncomputable section

namespace Hiop.Seeded
open Prob Iop Compile.Lifetime Compile.BatchLife
open scoped ENNReal

variable {I X : Type} {L : HolographicProtocol I X}

/-! ## Part 1. Provers that withhold everything -/

/-- The object's own honest sides, with the encodings as external strings and with every value of
the verifier's randomness in the public part of the abort set: nothing is ever shown. -/
def ProversS.silent (L : HolographicProtocol I X) : ProversS L where
  T := fun _ => { L.honestOfflineProver with ext := fun w => L.encodeIndex w.1 w.2.1, Bad := Set.univ }
  Lk := fun _ =>
    { L.honestLinkProver with ext := fun w => (L.encodeIndex w.1 w.2.1.1, L.encodeIndex w.1 w.2.2.1), Bad := Set.univ }
  B := fun _ => { L.honestOnlineBatchProver with ext := fun w => L.encodeIndex w.1 w.2.1, Bad := Set.univ }

/-- Simulators of runs that show nothing. -/
def simsNone (L : HolographicProtocol I X) : SimsS L where
  T := fun _ _ _ _ => PMF.pure none
  Lk := fun _ _ _ _ => PMF.pure none
  B := fun _ _ _ _ _ => PMF.pure fun _ => none

theorem silent_ext : (ProversS.silent L).Ext :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- Two maps that agree everywhere differ on a set of probability 0. -/
theorem pr_ne_le {γ δ : Type} (p : PMF γ) (f g : γ → δ) (h : ∀ a, f a = g a) (z : ℝ≥0∞) :
    pr p {a | f a ≠ g a} ≤ z :=
  (le_of_eq (pr_eq_zero_of_forall_not_mem p fun a _ (ha : f a ≠ g a) => ha (h a))).trans (zero_le z)

theorem silent_good (Gs : L.OutOfDomainSeed → Prop) (Ryes : I → X → Prop) (zT zL zO : ℝ≥0∞) :
    (simsNone L).Good (ProversS.silent L) Gs Ryes zT zL zO where
  goodT := fun e w x _ _ => by
    have h : ∀ ρ, ((ProversS.silent L).T e).output w x ρ = PMF.pure none := fun ρ => by
      unfold Honest.output
      exact if_pos (Or.inl (Set.mem_univ ρ))
    exact pr_ne_le _ _ _ h _
  goodL := fun e w x _ _ _ => by
    have h : ∀ ρ, ((ProversS.silent L).Lk e).output w x ρ = PMF.pure none := fun ρ => by
      unfold Honest.output
      exact if_pos (Or.inl (Set.mem_univ ρ))
    exact pr_ne_le _ _ _ h _
  goodB := fun e w x _ _ J xs _ => by
    have h : ∀ ρ, ((ProversS.silent L).B e).output w x ρ J = PMF.pure fun _ => none := fun ρ => by
      unfold BatchHonestProver.output
      refine Eq.trans (congrArg (fun F => PMF.map F _) (funext fun c => funext fun j => ?_))
        (PMF.map_const _ (fun _ => none))
      show _ = none
      split
      · rfl
      · exact if_pos (Or.inl (Or.inl (Set.mem_univ _)))
    exact pr_ne_le _ _ _ h _

/-! ## Part 2. A toy object -/

/-- The protocol without rounds, which reads nothing and accepts. -/
def nilProto (Y : Type) (E : ExtSpec) : InteractiveOracleProof Y E where
  shape := []
  blinded := fun _ => false
  extReads := fun _ _ => ∅
  reads := fun _ _ _ => ∅
  accept := fun _ _ _ => true

/-- A toy object: words of length 0, no committer's randomness, two seeds, three protocols without
rounds. The honest answer, at both seeds, is ans i. -/
def toy (I A : Type) (ans : I → A) : HolographicProtocol I Unit where
  wordLength := 0
  Symbol := Unit
  EncodingRandomness := Unit
  encodeIndex := fun _ _ _ => ()
  OutOfDomainSeed := Bool
  OutOfDomainAnswer := A
  honestOutOfDomainAnswer := fun i _ _ => ans i
  hasCollisionAt := fun _ _ => False
  decodeIndex := fun _ _ => none
  offline := nilProto _ _
  link := nilProto _ _
  maxBatchSize := 1
  onlineBatch := ⟨nilProto _ _, PUnit.unit⟩
  honestOfflineProver := { Coin := Unit, ext := fun _ _ => (), strat := fun _ _ _ => (), Bad := ∅,
                           Hid := fun _ _ => ∅ }
  honestLinkProver := { Coin := Unit, ext := fun _ => (fun _ => (), fun _ => ()), strat := fun _ _ _ => (),
                        Bad := ∅, Hid := fun _ _ => ∅ }
  honestOnlineBatchProver := { Coin0 := Unit, Coin := Unit, ext := fun _ _ => (), strat0 := fun _ _ => (),
                               strat := fun _ _ _ _ => (), Bad := ∅, Hid := fun _ _ => ∅, stop0 := fun _ => false }
  early := id
  late := none

theorem card_le_of_isEmpty {γ : Type} [IsEmpty γ] (T : Finset γ) (q : ℕ) : T.card ≤ q := by
  rw [Finset.eq_empty_of_isEmpty T, Finset.card_empty]
  exact Nat.zero_le q

/-- If the answer does not hang on the index, the toy object meets the premise on reads and hiding,
at all numbers. -/
theorem toy_reads {I A : Type} {ans : I → A} (h : ∀ i i', ans i = ans i')
    (Gs : (toy I A ans).OutOfDomainSeed → Prop) (b qT qpar qch qon : ℕ) :
    ReadsS (toy I A ans) Gs b qT qpar qch qon where
  cntT := fun _ _ => card_le_of_isEmpty (γ := Fin 0) _ _
  cntLp := fun _ _ => card_le_of_isEmpty (γ := Fin 0 ⊕ Fin 0) _ _
  cntLc := fun _ _ => card_le_of_isEmpty (γ := Fin 0 ⊕ Fin 0) _ _
  cntB := fun _ _ => card_le_of_isEmpty (γ := Fin 0) _ _
  hidE := fun S _ _ _ i i' => by
    show (unif Unit).map (fun _ => (ans i, fun _ : S => ())) =
      (unif Unit).map (fun _ => (ans i', fun _ : S => ()))
    rw [h i i']

/-- All premises of `Spec.whole_provers` hold together at the toy object with a constant answer and
silent provers; its conclusion there. -/
theorem toy_member (I A : Type) (a : A) (Gs : (toy I A fun _ => a).OutOfDomainSeed → Prop)
    (Ryes : I → Unit → Prop) (B : BoundsR) (b : ℕ) (hB : ∀ e, e ≤ B.nenc → B.reads e ≤ b) (i₀ : I) :
    HidesWhole (toy I A fun _ => a) (ProversS.silent _) Gs Ryes B
      (simWholeS _ (simsNone _) i₀) (B.err 0 0 0) :=
  whole_provers I Unit (toy I A fun _ => a) Gs Ryes b 0 0 0 0 0 0 0
    (toy_reads (fun _ _ => rfl) Gs b 0 0 0 0) (ProversS.silent _) silent_ext (simsNone _)
    (silent_good Gs Ryes 0 0 0) B (fun e he => by simpa using hB e he) i₀

/-! ## Part 3. An answer that tells the index -/

theorem tv_pure_ne {γ : Type} {a b : γ} (h : a ≠ b) : tv (PMF.pure a) (PMF.pure b) = 1 := by
  rw [tv_pure_pure, if_neg h]

/-- If at a seed of Gs the honest answer tells the index, the premise on hiding fails. -/
theorem not_reads_of_leak {Gs : L.OutOfDomainSeed → Prop} {b qT qpar qch qon : ℕ} (dcd : L.OutOfDomainAnswer → I)
    (s : L.OutOfDomainSeed) (hs : Gs s) (hd : ∀ i r, dcd (L.honestOutOfDomainAnswer i r s) = i) {i i' : I} (hne : i ≠ i') :
    ¬ ReadsS L Gs b qT qpar qch qon := by
  intro hR
  have h := congrArg (PMF.map (dcd ∘ Prod.fst)) (hR.hidE ∅ (Nat.zero_le b) s hs i i')
  rw [PMF.map_comp, PMF.map_comp] at h
  have e1 : ∀ j : I,
      ((dcd ∘ Prod.fst) ∘ fun r => (L.honestOutOfDomainAnswer j r s, fun p : (∅ : Finset (Fin L.wordLength)) => L.encodeIndex j r p)) =
        Function.const _ j := fun j => funext fun r => hd j r
  rw [e1, e1, PMF.map_const, PMF.map_const] at h
  have h1 := tv_pure_ne hne
  rw [h, tv_self] at h1
  exact zero_ne_one h1

/-- If at a seed of Gs the honest answer tells the index, the property fails for every simulator,
whatever the provers and the bounds are: its error is at least 1/2. -/
theorem one_le_of_leak {P : ProversS L} {Gs : L.OutOfDomainSeed → Prop} {Ryes : I → X → Prop} {B : BoundsR}
    {S : SimulatorS L} {z : ℝ≥0∞} (dcd : L.OutOfDomainAnswer → I) (s : L.OutOfDomainSeed) (hs : Gs s)
    (hd : ∀ i r, dcd (L.honestOutOfDomainAnswer i r s) = i) {i i' : I} (hne : i ≠ i')
    (h : HidesWhole L P Gs Ryes B S z) : 1 ≤ z + z := by
  have hv : ∀ j, (realHostS L P j).view s (fun a => (EnvS.stop (dcd a.2) : EnvS L I)) =
      PMF.pure j := fun j => by
    show (realLawsS L P j).host.view s _ = _
    rw [viewS_host]
    have h0 : ∀ r, (EnvS.stop (dcd ((realLawsS L P j).rc (r, s)).2) : EnvS L I).run
        (realLawsS L P j).host (0, fun _ => (r, s)) = PMF.pure j := fun r => by
      show PMF.pure (dcd (L.honestOutOfDomainAnswer j r s)) = _
      rw [hd]
    simp only [h0, PMF.bind_const]
  have h1 := h i I s (fun a => .stop (dcd a.2)) hs fun _ => trivial
  have h2 := h i' I s (fun a => .stop (dcd a.2)) hs fun _ => trivial
  rw [hv] at h1 h2
  rw [tv_comm] at h2
  calc (1 : ℝ≥0∞) = tv (PMF.pure i) (PMF.pure i') := (tv_pure_ne hne).symm
    _ ≤ _ := tv_triangle _ _ _
    _ ≤ z + z := add_le_add h1 h2

/-- The toy object whose answer is the index does not meet the premise on hiding. -/
theorem leak_not_reads (b qT qpar qch qon : ℕ) :
    ¬ ReadsS (toy Bool Bool id) (fun _ => True) b qT qpar qch qon :=
  not_reads_of_leak (L := toy Bool Bool id) id true trivial (fun _ _ => rfl)
    (i := true) (i' := false) (by decide)

/-- Nor does it have the property, for any provers, bounds and simulator, below 1/2. -/
theorem leak_not_hides (P : ProversS (toy Bool Bool id)) (Ryes : Bool → Unit → Prop) (B : BoundsR)
    (S : SimulatorS (toy Bool Bool id)) (z : ℝ≥0∞)
    (h : HidesWhole (toy Bool Bool id) P (fun _ => True) Ryes B S z) : 1 ≤ z + z :=
  one_le_of_leak (L := toy Bool Bool id) id true trivial (fun _ _ => rfl)
    (i := true) (i' := false) (by decide) h

end Hiop.Seeded

#print axioms Hiop.Seeded.silent_ext
#print axioms Hiop.Seeded.silent_good
#print axioms Hiop.Seeded.toy_reads
#print axioms Hiop.Seeded.toy_member
#print axioms Hiop.Seeded.not_reads_of_leak
#print axioms Hiop.Seeded.one_le_of_leak
#print axioms Hiop.Seeded.leak_not_reads
#print axioms Hiop.Seeded.leak_not_hides
