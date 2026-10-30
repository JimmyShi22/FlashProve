-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/Seeded/Pad.lean: a small member of the premises of Hiop/Seeded/Whole.lean that is not idle, and
two provers on the same object that are no members.

Definitions, statements and proofs. Nothing here is about the protocol of the release.
The object `pad`: the index is a bit i; the committer's randomness is two bits (r₁, r₂); the encoded
index is the one symbol i + r₁; there are two seeds; the honest answer at the seed s is i · s + r₂.
So the answer hangs on index, randomness and seed, and (answer, symbol) is uniform for each index:
the two pads pay for it. The offline protocol has one round: the prover sends a bit in the clear,
the verifier reads the symbol and accepts if the two are equal.
  Part 1: the object; it hides one position beside the answer, at both seeds (`pad_reads`).
  Part 2: the honest prover sends the symbol. It shows something at every verifier's randomness
    (`pad_shows`), the verifier accepts it (`pad_accepts`), and a simulator that repeats the symbol
    read is exact (`pad_good`). All premises of `Spec.whole_all_seeds` hold together, at bounds that
    allow a further encoded index, a test and a link on each (`pad_member`).
  Part 3, negative tests on RUNS. A prover that sends the index in the clear (`tellProvers`), and a
    prover that sends the symbol but withholds its message just when the index is 1
    (`stopProvers`): with either, the property fails for EVERY simulator and every z below 1/2, as
    soon as one test is allowed (`tell_not_hides`, `stop_not_hides`). The general lemma:
    `one_le_of_views`.

Terms: lean/GLOSSARY.md.

-/
import Hiop.Seeded.Members

set_option autoImplicit false

noncomputable section

namespace Hiop.Seeded
open Prob Iop Compile.Lifetime Compile.BatchLife
open scoped ENNReal

/-! ## Part 1. The object -/

/-- One round: the prover sends one bit in the clear; no oracle, no challenge. -/
def bitRound : Round where
  Orc := Unit
  Pos := Empty
  Sym := fun _ => Unit
  rd := fun _ _ => ()
  Plain := Bool
  Chal := Unit
  dOrc := ()
  dPlain := false

/-- the bit that was sent -/
def bitOfTr (τ : Tr [bitRound]) : Bool := τ.1.2

/-- The prover sends a bit; the verifier reads the one symbol of the word and accepts if the two are
equal. -/
def bitProto (Y : Type) : InteractiveOracleProof Y (oneExternalString 1 Bool) where
  shape := [bitRound]
  blinded := fun _ => false
  extReads := fun _ _ => ({0} : Finset (Fin 1))
  reads := fun _ _ _ => ∅
  accept := fun _ y τ => bitOfTr τ == y 0

/-- The honest side of `bitProto` that sends the bit `say w` and withholds it where `stop w`. -/
def bitSide {Y Wt : Type} (word say stop : Wt → Bool) : Honest (bitProto Y) Wt where
  Coin := Unit
  ext := fun w _ => word w
  strat := fun w _ _ => (((), say w), fun _ => ())
  Bad := ∅
  Hid := fun w _ => {_ρ | stop w = true}

/-- The object. -/
def pad : HolographicProtocol Bool Unit where
  wordLength := 1
  Symbol := Bool
  EncodingRandomness := Bool × Bool
  encodeIndex := fun i r _ => xor i r.1
  OutOfDomainSeed := Bool
  OutOfDomainAnswer := Bool
  honestOutOfDomainAnswer := fun i r s => xor (i && s) r.2
  hasCollisionAt := fun _ _ => False
  decodeIndex := fun _ _ => none
  offline := bitProto _
  link := nilProto _ _
  maxBatchSize := 1
  onlineBatch := ⟨nilProto _ _, PUnit.unit⟩
  honestOfflineProver := bitSide (fun w => xor w.1 w.2.1.1) (fun w => xor w.1 w.2.1.1) fun _ => false
  honestLinkProver := { Coin := Unit, ext := fun w => (fun _ => xor w.1 w.2.1.1.1, fun _ => xor w.1 w.2.2.1.1),
                        strat := fun _ _ _ => (), Bad := ∅, Hid := fun _ _ => ∅ }
  honestOnlineBatchProver := { Coin0 := Unit, Coin := Unit, ext := fun w _ => xor w.1 w.2.1.1, strat0 := fun _ _ => (),
                               strat := fun _ _ _ _ => (), Bad := ∅, Hid := fun _ _ => ∅, stop0 := fun _ => false }
  early := id
  late := none

/-- The answer hangs on the index, on the randomness and on the seed. -/
theorem pad_ans_hangs :
    pad.honestOutOfDomainAnswer true (false, false) true ≠ pad.honestOutOfDomainAnswer false (false, false) true ∧
    pad.honestOutOfDomainAnswer true (false, false) true ≠ pad.honestOutOfDomainAnswer true (false, true) true ∧
    pad.honestOutOfDomainAnswer true (false, false) true ≠ pad.honestOutOfDomainAnswer true (false, false) false :=
  ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩

/-- Add a to the first pad and c to the second. -/
def shift (a c : Bool) : Bool × Bool ≃ Bool × Bool where
  toFun := fun r => (xor r.1 a, xor r.2 c)
  invFun := fun r => (xor r.1 a, xor r.2 c)
  left_inv := by
    rintro ⟨x, y⟩
    cases a <;> cases c <;> cases x <;> cases y <;> rfl
  right_inv := by
    rintro ⟨x, y⟩
    cases a <;> cases c <;> cases x <;> cases y <;> rfl

theorem card_le_one_fin (T : Finset (Fin 1)) : T.card ≤ 1 :=
  (Finset.card_le_univ T).trans (le_of_eq (Fintype.card_fin 1))

/-- The object hides one position beside the answer, at both seeds; the offline verifier reads one
position, a link none, a session at most one. -/
theorem pad_reads : pad.ReadsR 1 1 0 0 1 where
  cntT := fun _ _ => card_le_one_fin _
  cntLp := fun _ _ => by
    show ((∅ : Finset (Fin 1 ⊕ Fin 1)).filter _).card ≤ 0
    rw [Finset.filter_empty, Finset.card_empty]
  cntLc := fun _ _ => by
    show ((∅ : Finset (Fin 1 ⊕ Fin 1)).filter _).card ≤ 0
    rw [Finset.filter_empty, Finset.card_empty]
  cntB := fun _ _ => card_le_one_fin _
  hidE := fun S _ s i i' => by
    show (unif (Bool × Bool)).map (fun r => (xor (i && s) r.2, fun _ : S => xor i r.1)) =
      (unif (Bool × Bool)).map (fun r => (xor (i' && s) r.2, fun _ : S => xor i' r.1))
    have h : (fun r : Bool × Bool => (xor (i && s) r.2, fun _ : S => xor i r.1)) =
        (fun r : Bool × Bool => (xor (i' && s) r.2, fun _ : S => xor i' r.1)) ∘
          shift (xor i i') (xor (i && s) (i' && s)) := by
      funext r
      obtain ⟨x, y⟩ := r
      cases i <;> cases i' <;> cases s <;> cases x <;> cases y <;> rfl
    rw [h, ← PMF.map_comp, map_unif_equiv]

/-! ## Part 2. A prover that shows something -/

/-- There is no position of a prover's oracle. -/
theorem no_opos (p : OPos [bitRound]) : False :=
  match (p : Empty ⊕ Empty) with
  | .inl e => e.elim
  | .inr e => e.elim

/-- What `bitSide` shows where it does not withhold: the bit, and the symbol that the verifier
reads. -/
def bitView {Y : Type} (bit : Bool) (ans : Fin 1 → Option Bool) : DView (bitProto Y) :=
  ⟨((bit, ()) : Bool × Unit), ans, fun _ => none⟩

theorem output_bitSide {Y Wt : Type} (word say stop : Wt → Bool) (w : Wt) (y : Y)
    (ρ : Rho (bitProto Y).shape) :
    (bitSide (Y := Y) word say stop).output w y ρ =
      if stop w = true then PMF.pure none
      else PMF.pure (some (bitView (say w) ((bitProto Y).extAns y ρ fun _ => word w))) := by
  unfold Honest.output
  by_cases h : stop w = true
  · have hm : ρ ∈ (bitSide (Y := Y) word say stop).withheld w y := Or.inr h
    rw [if_pos hm, if_pos h]
  · have hm : ρ ∉ (bitSide (Y := Y) word say stop).withheld w y := fun hh =>
      ((Set.mem_union ρ _ _).1 hh).elim (fun h0 => h0) h
    have hc : (fun c : (bitSide (Y := Y) word say stop).Coin =>
        some ((bitProto Y).dview y ((bitSide (Y := Y) word say stop).ext w)
          (((bitSide (Y := Y) word say stop).strat w y c).run ρ).1)) =
        Function.const _ (some (bitView (say w) ((bitProto Y).extAns y ρ fun _ => word w))) := by
      funext c
      refine congrArg some ?_
      obtain ⟨c', ρ'⟩ := (ρ : Unit × Unit)
      show (⟨_, _, _⟩ : DView (bitProto Y)) = ⟨_, _, _⟩
      congr 1
      funext p
      exact (no_opos p).elim
    rw [if_neg hm, if_neg h, hc, PMF.map_const]

/-- The simulator that repeats the symbol that it is handed. -/
def bitSim {Y : Type} : SimOf (bitProto Y) :=
  fun _ _ ans => PMF.pure (some (bitView ((ans (0 : Fin 1)).getD false) ans))

/-- The provers: the offline one sends the symbol; links and sessions are silent. -/
def padProvers : ProversS pad :=
  ⟨fun _ => pad.honestOfflineProver, (ProversS.silent pad).Lk, (ProversS.silent pad).B⟩

/-- The simulators: the offline one repeats the symbol that it is handed. -/
def padSims : SimsS pad :=
  ⟨fun _ => bitSim, (simsNone pad).Lk, (simsNone pad).B⟩

theorem pad_ext : padProvers.Ext :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- the symbol that the offline verifier is handed -/
theorem extAns_zero {Y : Type} (y : Y) (ρ : Rho (bitProto Y).shape) (b : Bool) :
    ((bitProto Y).extAns y ρ fun _ => b) 0 = some b := by
  unfold InteractiveOracleProof.extAns
  exact if_pos (Finset.mem_singleton_self 0)

/-- It shows something, at every verifier's randomness. -/
theorem pad_shows (w : Bool × (Bool × Bool) × Bool) (x : pad.Rec) (ρ : Rho pad.offline.shape) :
    pad.honestOfflineProver.output w x ρ ≠ PMF.pure none := by
  intro h
  have h0 := output_bitSide (Y := pad.Rec) (fun w : Bool × (Bool × Bool) × Bool => xor w.1 w.2.1.1)
    (fun w => xor w.1 w.2.1.1) (fun _ => false) w x ρ
  rw [if_neg (by simp)] at h0
  have h1 := tv_pure_ne (Option.some_ne_none
    (bitView (Y := pad.Rec) (xor w.1 w.2.1.1)
      ((bitProto pad.Rec).extAns x ρ fun _ => xor w.1 w.2.1.1)))
  rw [← h0] at h1
  rw [show (bitSide (Y := pad.Rec) (fun w : Bool × (Bool × Bool) × Bool => xor w.1 w.2.1.1)
    (fun w => xor w.1 w.2.1.1) fun _ => false).output w x ρ = PMF.pure none from h, tv_self] at h1
  exact zero_ne_one h1

/-- The verifier accepts it. -/
theorem pad_accepts (w : Bool × (Bool × Bool) × Bool) (x : pad.Rec) (c : Unit)
    (ρ : Rho pad.offline.shape) :
    pad.offline.accept x (pad.honestOfflineProver.ext w) ((pad.honestOfflineProver.strat w x c).run ρ).1 = true := by
  obtain ⟨c', ρ'⟩ := (ρ : Unit × Unit)
  show (xor w.1 w.2.1.1 == xor w.1 w.2.1.1) = true
  exact beq_self_eq_true _

/-- The simulators are exact. -/
theorem pad_good (Gs : pad.OutOfDomainSeed → Prop) (Ryes : Bool → Unit → Prop) (zT zL zO : ℝ≥0∞) :
    padSims.Good padProvers Gs Ryes zT zL zO where
  goodT := fun e w x _ _ => by
    refine pr_ne_le _ _ _ (fun ρ => ?_) _
    have h0 := output_bitSide (Y := pad.Rec)
      (fun w : Bool × (Bool × Bool) × Bool => xor w.1 w.2.1.1)
      (fun w => xor w.1 w.2.1.1) (fun _ => false) w x ρ
    rw [if_neg (by simp)] at h0
    refine h0.trans ?_
    show _ = PMF.pure (some (bitView
      ((((bitProto pad.Rec).extAns x ρ fun _ => xor w.1 w.2.1.1) 0).getD false) _))
    rw [extAns_zero]
    rfl
  goodL := (silent_good Gs Ryes zT zL zO).goodL
  goodB := (silent_good Gs Ryes zT zL zO).goodB

/-- Bounds: one further encoded index; on each encoded index one test and one link. -/
def padBounds : BoundsR := ⟨1, fun _ => 1, fun _ => 1, fun _ => 0, fun _ => 0, 1⟩

theorem padBounds_fits : padBounds.Fits 1 1 0 0 1 := by
  intro e _
  show 1 * 1 + (if e = 0 then padBounds.sum padBounds.links * 0 else 0) + 1 * 0 + 0 * 1 + 0 ≤ 1
  split_ifs <;> simp

/-- All premises of `Spec.whole_all_seeds` hold together at this object and these provers; its
conclusion there, with error 0. -/
theorem pad_member (Ryes : Bool → Unit → Prop) (i₀ : Bool) :
    HidesWhole pad padProvers (fun _ => True) Ryes padBounds (simWholeS pad padSims i₀)
      (padBounds.err 0 0 0) :=
  whole_all_seeds Bool Unit pad Ryes 1 1 0 0 1 0 0 0 pad_reads padProvers pad_ext padSims
    (pad_good _ Ryes 0 0 0) padBounds padBounds_fits i₀

/-! ## Part 3. Provers that tell the index -/

variable {I X : Type} {L : HolographicProtocol I X}

/-- If some admissible environment outputs a on the index i and a' ≠ a on the index i', always, then
the property fails for every simulator below 1/2. -/
theorem one_le_of_views {P : ProversS L} {Gs : L.OutOfDomainSeed → Prop} {Ryes : I → X → Prop} {B : BoundsR}
    {S : SimulatorS L} {z : ℝ≥0∞} {α : Type} (s : L.OutOfDomainSeed) (hs : Gs s) (E : L.Rec → EnvS L α)
    {i i' : I} (hE : ∀ a, (E a).Adm B Gs (Ryes i) 0 UsedR.zero)
    (hE' : ∀ a, (E a).Adm B Gs (Ryes i') 0 UsedR.zero) {a a' : α} (hne : a ≠ a')
    (hv : (realHostS L P i).view s E = PMF.pure a)
    (hv' : (realHostS L P i').view s E = PMF.pure a')
    (h : HidesWhole L P Gs Ryes B S z) : 1 ≤ z + z := by
  have h1 := h i α s E hs hE
  have h2 := h i' α s E hs hE'
  rw [hv] at h1
  rw [hv', tv_comm] at h2
  calc (1 : ℝ≥0∞) = tv (PMF.pure a) (PMF.pure a') := (tv_pure_ne hne).symm
    _ ≤ _ := tv_triangle _ _ _
    _ ≤ z + z := add_le_add h1 h2

/-- Provers on `pad` whose offline side sends `say w` and withholds where `stop w`. -/
def bitProvers (say stop : Bool × (Bool × Bool) × Bool → Bool) : ProversS pad :=
  ⟨fun _ => bitSide (fun w => xor w.1 w.2.1.1) say stop, (ProversS.silent pad).Lk,
    (ProversS.silent pad).B⟩

/-- The environment that asks for one test on the first encoded index and outputs f of what was
shown. -/
def oneTest {α : Type} (f : Option (DView pad.offline) → α) : pad.Rec → EnvS pad α :=
  fun _ => .test 0 fun a => .stop (f a.2)

theorem adm_oneTest {α : Type} (f : Option (DView pad.offline) → α) (Gs : pad.OutOfDomainSeed → Prop)
    (ok : Unit → Prop) (B : BoundsR) (hB : 0 < B.tests 0) (a : pad.Rec) :
    (oneTest f a).Adm B Gs ok 0 UsedR.zero :=
  ⟨le_rfl, hB, fun _ => trivial⟩

/-- What that environment outputs, if the offline side's output at the index i is always o. -/
theorem view_oneTest {α : Type} (f : Option (DView pad.offline) → α)
    (say stop : Bool × (Bool × Bool) × Bool → Bool) (i s : Bool) (v : α)
    (h : ∀ (r : Bool × Bool) (ρ : Rho pad.offline.shape),
      ((bitSide (Y := pad.Rec) (fun w : Bool × (Bool × Bool) × Bool => xor w.1 w.2.1.1) say
        stop).output (i, r, s) (pad.recOf i r s) ρ).map f = PMF.pure v) :
    (realHostS pad (bitProvers say stop) i).view s (oneTest f) = PMF.pure v := by
  show (realLawsS pad (bitProvers say stop) i).host.view s _ = _
  rw [viewS_host]
  have h0 : ∀ r : Bool × Bool,
      (oneTest f ((realLawsS pad (bitProvers say stop) i).rc (r, s))).run
        (realLawsS pad (bitProvers say stop) i).host (0, fun _ => (r, s)) = PMF.pure v := by
    intro r
    show (EnvS.test 0 fun a => .stop (f a.2)).run _ _ = _
    rw [runS_test]
    show ((unif (Rho pad.offline.shape)).bind fun ρ =>
      ((bitSide (Y := pad.Rec) (fun w : Bool × (Bool × Bool) × Bool => xor w.1 w.2.1.1) say
        stop).output (i, r, s) (pad.recOf i r s) ρ).map fun o => (ρ, o)).bind
          (fun a => PMF.pure (f a.2)) = _
    rw [PMF.bind_bind]
    have h1 : ∀ ρ : Rho pad.offline.shape,
        (((bitSide (Y := pad.Rec) (fun w : Bool × (Bool × Bool) × Bool => xor w.1 w.2.1.1) say
          stop).output (i, r, s) (pad.recOf i r s) ρ).map fun o => (ρ, o)).bind
            (fun a => PMF.pure (f a.2)) = PMF.pure v := by
      intro ρ
      rw [PMF.bind_map]
      exact h r ρ
    simp only [h1, PMF.bind_const]
  simp only [h0, PMF.bind_const]

/-- The offline side sends the index in the clear. -/
def tellProvers : ProversS pad := bitProvers (fun w => w.1) fun _ => false

/-- The offline side sends the symbol, and withholds it just when the index is 1. -/
def stopProvers : ProversS pad := bitProvers (fun w => xor w.1 w.2.1.1) fun w => w.1

/-- the bit that was shown, if any -/
def bitOf : Option (DView pad.offline) → Option Bool
  | none => none
  | some v => some ((v.plains : Bool × Unit).1 : Bool)

theorem tell_not_hides (Gs : pad.OutOfDomainSeed → Prop) (s : Bool) (hs : Gs s) (Ryes : Bool → Unit → Prop)
    (B : BoundsR) (hB : 0 < B.tests 0) (S : SimulatorS pad) (z : ℝ≥0∞)
    (h : HidesWhole pad tellProvers Gs Ryes B S z) : 1 ≤ z + z := by
  have hv : ∀ i : Bool, (realHostS pad tellProvers i).view s (oneTest bitOf) =
      PMF.pure (some i) := fun i =>
    view_oneTest bitOf _ _ i s (some i) fun r ρ => by
      rw [output_bitSide, if_neg (by simp)]
      exact PMF.pure_map _ _
  exact one_le_of_views s hs (oneTest bitOf) (i := true) (i' := false)
    (adm_oneTest _ _ _ _ hB) (adm_oneTest _ _ _ _ hB) (a := some true) (a' := some false)
    (by simp) (hv true) (hv false) h

theorem stop_not_hides (Gs : pad.OutOfDomainSeed → Prop) (s : Bool) (hs : Gs s) (Ryes : Bool → Unit → Prop)
    (B : BoundsR) (hB : 0 < B.tests 0) (S : SimulatorS pad) (z : ℝ≥0∞)
    (h : HidesWhole pad stopProvers Gs Ryes B S z) : 1 ≤ z + z := by
  have hv : ∀ i : Bool, (realHostS pad stopProvers i).view s (oneTest Option.isNone) =
      PMF.pure i := fun i =>
    view_oneTest Option.isNone _ _ i s i fun r ρ => by
      rw [output_bitSide]
      cases i
      · rw [if_neg (by simp)]
        exact PMF.pure_map _ _
      · rw [if_pos rfl]
        exact PMF.pure_map _ _
  exact one_le_of_views s hs (oneTest Option.isNone) (i := true) (i' := false)
    (adm_oneTest _ _ _ _ hB) (adm_oneTest _ _ _ _ hB) (a := true) (a' := false)
    (by simp) (hv true) (hv false) h

end Hiop.Seeded

#print axioms Hiop.Seeded.pad_ans_hangs
#print axioms Hiop.Seeded.pad_reads
#print axioms Hiop.Seeded.pad_shows
#print axioms Hiop.Seeded.pad_accepts
#print axioms Hiop.Seeded.pad_good
#print axioms Hiop.Seeded.pad_member
#print axioms Hiop.Seeded.one_le_of_views
#print axioms Hiop.Seeded.tell_not_hides
#print axioms Hiop.Seeded.stop_not_hides
