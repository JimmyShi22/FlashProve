-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/Seeded/Foes.lean: two tests that can fail, for the property of Hiop/Seeded/Whole.lean: the set
of seeds and the budget of reads are letters that bite.

Definitions, statements and proofs. Toys: nothing here is about the protocol of the release. This
file states no goal of the release.

Part 1. AIM. The object `aim`: the index is a bit i, the committer's randomness two bits (r₁, r₂),
the encoded index the one symbol i + r₁; two seeds. The honest answer is r₂ at the seed 0 and THE
INDEX at the seed 1. In the experiment the environment NAMES the seed.
  `aim_reads`, `aim_member`: at Gs := {the seed 0} the premise on hiding holds and the property
    holds with error 0, for provers that show nothing.
  `aim_not_reads`, `aim_not_hides`: at any Gs that holds the seed 1 the premise fails, and the
    property fails for every simulator, all provers and all bounds: 1 ≤ z + z.
  So a seed that leaks cannot be paid by its share among all seeds (here 1/2): an environment aims
  at it. It must lie outside Gs, and whoever compiles pays for the chance that a seed falls outside
  Gs.
Part 2. A READ BEYOND THE BUDGET. The object `two`: the encoded index is the word (i + r₁, r₁).
  `two_reads`, `two_member`: one position hides (b = 1), and at bounds that allow one single read
    the property holds with error 0.
  `two_not_hides`: at bounds that allow TWO single reads of the first encoded index the property
    fails for every simulator and all provers: 1 ≤ z + z. The environment reads both positions and
    adds.
  `two_not_fits`: such bounds do not fit the budget 1.
  So `BoundsR.Fits` is a premise that bites.
Limits. Both are tests of `HidesWhole` (Hiop/Seeded/Whole.lean), the experiment with batches and
uniform verifier's randomness. The theorem on the scheme with the whole key published goes by
another instance of the same form, the game of Hiop/Seeded/Game.lean: these tests are of its cousin,
not of a step on its road.
Terms: lean/GLOSSARY.md.

-/
import Hiop.Seeded.Pad

set_option autoImplicit false

noncomputable section

namespace Hiop.Seeded
open Prob Iop Compile.Lifetime
open scoped ENNReal

/-! ## Part 1. Aim -/

def aim : HolographicProtocol Bool Unit where
  wordLength := 1
  Symbol := Bool
  EncodingRandomness := Bool × Bool
  encodeIndex := fun i r _ => xor i r.1
  OutOfDomainSeed := Bool
  OutOfDomainAnswer := Bool
  honestOutOfDomainAnswer := fun i r s => bif s then i else r.2
  hasCollisionAt := fun _ _ => False
  decodeIndex := fun _ _ => none
  offline := nilProto _ _
  link := nilProto _ _
  maxBatchSize := 1
  onlineBatch := ⟨nilProto _ _, PUnit.unit⟩
  honestOfflineProver := { Coin := Unit, ext := fun w _ => xor w.1 w.2.1.1, strat := fun _ _ _ => (), Bad := ∅,
                           Hid := fun _ _ => ∅ }
  honestLinkProver := { Coin := Unit, ext := fun w => (fun _ => xor w.1 w.2.1.1.1, fun _ => xor w.1 w.2.2.1.1),
                        strat := fun _ _ _ => (), Bad := ∅, Hid := fun _ _ => ∅ }
  honestOnlineBatchProver := { Coin0 := Unit, Coin := Unit, ext := fun w _ => xor w.1 w.2.1.1, strat0 := fun _ _ => (),
                               strat := fun _ _ _ _ => (), Bad := ∅, Hid := fun _ _ => ∅, stop0 := fun _ => false }
  early := id
  late := none

/-- At the seed 0 the object hides one position beside the answer; no verifier reads. -/
theorem aim_reads : ReadsS aim (fun s => s = false) 1 1 0 0 1 where
  cntT := fun _ _ => card_le_one_fin _
  cntLp := fun _ _ => by
    show ((∅ : Finset (Fin 1 ⊕ Fin 1)).filter _).card ≤ 0
    rw [Finset.filter_empty, Finset.card_empty]
  cntLc := fun _ _ => by
    show ((∅ : Finset (Fin 1 ⊕ Fin 1)).filter _).card ≤ 0
    rw [Finset.filter_empty, Finset.card_empty]
  cntB := fun _ _ => card_le_one_fin _
  hidE := fun S _ s hs i i' => by
    have hs' : s = false := hs
    subst hs'
    show (unif (Bool × Bool)).map (fun r => (r.2, fun _ : S => xor i r.1)) =
      (unif (Bool × Bool)).map (fun r => (r.2, fun _ : S => xor i' r.1))
    have h : (fun r : Bool × Bool => (r.2, fun _ : S => xor i r.1)) =
        (fun r : Bool × Bool => (r.2, fun _ : S => xor i' r.1)) ∘ shift (xor i i') false := by
      funext r
      obtain ⟨x, y⟩ := r
      cases i <;> cases i' <;> cases x <;> cases y <;> rfl
    rw [h, ← PMF.map_comp, map_unif_equiv]

/-- At Gs := {the seed 0}: the property, with error 0, for provers that show nothing. -/
theorem aim_member (Ryes : Bool → Unit → Prop) (i₀ : Bool) :
    HidesWhole aim (ProversS.silent aim) (fun s => s = false) Ryes padBounds
      (simWholeS aim (simsNone aim) i₀) (padBounds.err 0 0 0) :=
  whole_provers Bool Unit aim (fun s => s = false) Ryes 1 1 0 0 1 0 0 0 aim_reads
    (ProversS.silent aim) silent_ext (simsNone aim) (silent_good _ Ryes 0 0 0) padBounds
    padBounds_fits i₀

/-- At any set of seeds that holds the seed 1 the premise on hiding fails. -/
theorem aim_not_reads (Gs : Bool → Prop) (h1 : Gs true) (b qT qpar qch qon : ℕ) :
    ¬ ReadsS aim Gs b qT qpar qch qon :=
  not_reads_of_leak (L := aim) id true h1 (fun _ _ => rfl) (i := true) (i' := false) (by decide)

/-- And the property fails, for all provers, bounds and simulators, below 1/2. -/
theorem aim_not_hides (Gs : Bool → Prop) (h1 : Gs true) (P : ProversS aim)
    (Ryes : Bool → Unit → Prop) (B : BoundsR) (S : SimulatorS aim) (z : ℝ≥0∞)
    (h : HidesWhole aim P Gs Ryes B S z) : 1 ≤ z + z :=
  one_le_of_leak (L := aim) id true h1 (fun _ _ => rfl) (i := true) (i' := false) (by decide) h

/-! ## Part 2. A read beyond the budget -/

def two : HolographicProtocol Bool Unit where
  wordLength := 2
  Symbol := Bool
  EncodingRandomness := Bool × Bool
  encodeIndex := fun i r p => if p = 0 then xor i r.1 else r.1
  OutOfDomainSeed := Bool
  OutOfDomainAnswer := Bool
  honestOutOfDomainAnswer := fun _ r _ => r.2
  hasCollisionAt := fun _ _ => False
  decodeIndex := fun _ _ => none
  offline := nilProto _ _
  link := nilProto _ _
  maxBatchSize := 1
  onlineBatch := ⟨nilProto _ _, PUnit.unit⟩
  honestOfflineProver := { Coin := Unit, ext := fun w p => if p = 0 then xor w.1 w.2.1.1 else w.2.1.1,
                           strat := fun _ _ _ => (), Bad := ∅, Hid := fun _ _ => ∅ }
  honestLinkProver := { Coin := Unit,
                        ext := fun w => (fun p => if p = 0 then xor w.1 w.2.1.1.1 else w.2.1.1.1,
                          fun p => if p = 0 then xor w.1 w.2.2.1.1 else w.2.2.1.1),
                        strat := fun _ _ _ => (), Bad := ∅, Hid := fun _ _ => ∅ }
  honestOnlineBatchProver := { Coin0 := Unit, Coin := Unit, ext := fun w p => if p = 0 then xor w.1 w.2.1.1 else w.2.1.1,
                               strat0 := fun _ _ => (), strat := fun _ _ _ _ => (), Bad := ∅, Hid := fun _ _ => ∅,
                               stop0 := fun _ => false }
  early := id
  late := none

theorem card_empty_le {γ : Type} (q : ℕ) : (∅ : Finset γ).card ≤ q := by
  rw [Finset.card_empty]
  exact Nat.zero_le q

/-- A set of at most one of two positions misses one of them. -/
theorem misses_one (S : Finset (Fin 2)) (hS : S.card ≤ 1) : (0 : Fin 2) ∉ S ∨ (1 : Fin 2) ∉ S := by
  by_contra hc
  rw [not_or, not_not, not_not] at hc
  have h2 : ({0, 1} : Finset (Fin 2)) ⊆ S := by
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact hc.1
    · rw [Finset.mem_singleton.1 hp]
      exact hc.2
  have h3 := Finset.card_le_card h2
  have h4 : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
  omega

/-- One position of the word hides, beside the answer, at both seeds; no verifier reads. -/
theorem two_reads : ReadsS two (fun _ => True) 1 0 0 0 2 where
  cntT := fun _ _ => card_empty_le 0
  cntLp := fun _ _ => by
    show ((∅ : Finset (Fin 2 ⊕ Fin 2)).filter _).card ≤ 0
    rw [Finset.filter_empty, Finset.card_empty]
  cntLc := fun _ _ => by
    show ((∅ : Finset (Fin 2 ⊕ Fin 2)).filter _).card ≤ 0
    rw [Finset.filter_empty, Finset.card_empty]
  cntB := fun _ _ => (Finset.card_le_univ _).trans (le_of_eq (Fintype.card_fin 2))
  hidE := fun (S : Finset (Fin 2)) hS s _ i i' => by
    show (unif (Bool × Bool)).map
        (fun r => (r.2, fun p : S => if p.1 = 0 then xor i r.1 else r.1)) =
      (unif (Bool × Bool)).map (fun r => (r.2, fun p : S => if p.1 = 0 then xor i' r.1 else r.1))
    rcases misses_one S hS with h0 | h1
    · refine congrArg (fun f => PMF.map f (unif (Bool × Bool))) (funext fun r => ?_)
      refine Prod.ext rfl (funext fun p => ?_)
      have hp : p.1 ≠ 0 := fun e => h0 (e ▸ p.2)
      show (if p.1 = 0 then xor i r.1 else r.1) = if p.1 = 0 then xor i' r.1 else r.1
      rw [if_neg hp, if_neg hp]
    · have h : (fun r : Bool × Bool => (r.2, fun p : S => if p.1 = 0 then xor i r.1 else r.1)) =
          (fun r : Bool × Bool => (r.2, fun p : S => if p.1 = 0 then xor i' r.1 else r.1)) ∘
            shift (xor i i') false := by
        funext r
        obtain ⟨x, y⟩ := r
        refine Prod.ext ?_ (funext fun p => ?_)
        · show y = xor y false
          cases y <;> rfl
        · have hp : p.1 = 0 := by
            have h2 : p.1 ≠ 1 := fun e => h1 (e ▸ p.2)
            have h3 := p.1.isLt
            have h4 : p.1.val ≠ 1 := fun e => h2 (Fin.ext (by rw [Fin.val_one]; exact e))
            exact Fin.ext (by rw [Fin.val_zero]; omega)
          show (if p.1 = 0 then xor i x else x) = if p.1 = 0 then xor i' (xor x (xor i i')) else _
          rw [if_pos hp, if_pos hp]
          cases i <;> cases i' <;> cases x <;> rfl
      rw [h, ← PMF.map_comp, map_unif_equiv]

/-- Bounds that allow k single reads of the first encoded index, and nothing else. -/
def readBounds (k : ℕ) : BoundsR := ⟨0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => k, 0⟩

theorem readBounds_fits (k b : ℕ) (h : k ≤ b) : (readBounds k).Fits b 0 0 0 2 := by
  intro e _
  show 0 * 0 + (if e = 0 then (readBounds k).sum (readBounds k).links * 0 else 0) + 0 * 0 + 0 * 2 +
    k ≤ b
  split_ifs <;> omega

/-- Two single reads do not fit the budget 1. -/
theorem two_not_fits : ¬ (readBounds 2).Fits 1 0 0 0 2 := by
  intro h
  have h0 := h 0 (Nat.zero_le _)
  have h1 : 0 * 0 + (if (0 : ℕ) = 0 then (readBounds 2).sum (readBounds 2).links * 0 else 0) +
    0 * 0 + 0 * 2 + 2 ≤ 1 := h0
  omega

/-- At bounds that allow one single read: the property, with error 0. -/
theorem two_member (Ryes : Bool → Unit → Prop) (i₀ : Bool) :
    HidesWhole two (ProversS.silent two) (fun _ => True) Ryes (readBounds 1)
      (simWholeS two (simsNone two) i₀) ((readBounds 1).err 0 0 0) :=
  whole_provers Bool Unit two (fun _ => True) Ryes 1 0 0 0 2 0 0 0 two_reads
    (ProversS.silent two) silent_ext (simsNone two) (silent_good _ Ryes 0 0 0) (readBounds 1)
    (readBounds_fits 1 1 le_rfl) i₀

/-- The environment that reads both positions of the first encoded index and adds them. -/
def readBoth : two.Rec → EnvS two Bool :=
  fun _ => .read 0 (0 : Fin 2) fun y₀ => .read 0 (1 : Fin 2) fun y₁ =>
    .stop (xor (show Bool from y₀) (show Bool from y₁))

theorem adm_readBoth (Gs : Bool → Prop) (ok : Unit → Prop) (B : BoundsR) (hB : 2 ≤ B.reads 0)
    (a : two.Rec) : (readBoth a).Adm B Gs ok 0 UsedR.zero := by
  refine ⟨le_rfl, (by show 0 < B.reads 0; omega), fun _ => ⟨le_rfl, ?_, fun _ => trivial⟩⟩
  show bump (fun _ => 0) 0 0 < B.reads 0
  have h1 : bump (fun _ => 0) 0 0 = 1 := by simp [bump]
  omega

theorem view_readBoth (P : ProversS two) (i s : Bool) :
    (realHostS two P i).view s readBoth = PMF.pure i := by
  show (realLawsS two P i).host.view s _ = _
  rw [viewS_host]
  have h0 : ∀ r : Bool × Bool, (readBoth ((realLawsS two P i).rc (r, s))).run
      (realLawsS two P i).host (0, fun _ => (r, s)) = PMF.pure i := fun r => by
    unfold readBoth
    rw [runS_read, runS_read, runS_stop]
    show PMF.pure (xor (xor i r.1) r.1) = _
    cases i <;> cases r.1 <;> rfl
  simp only [h0, PMF.bind_const]

/-- At bounds that allow two single reads of the first encoded index the property fails, for all
provers and simulators, below 1/2. -/
theorem two_not_hides (P : ProversS two) (Gs : Bool → Prop) (s : Bool) (hs : Gs s)
    (Ryes : Bool → Unit → Prop) (B : BoundsR) (hB : 2 ≤ B.reads 0) (S : SimulatorS two) (z : ℝ≥0∞)
    (h : HidesWhole two P Gs Ryes B S z) : 1 ≤ z + z :=
  one_le_of_views s hs readBoth (i := true) (i' := false) (adm_readBoth Gs _ B hB)
    (adm_readBoth Gs _ B hB) (a := true) (a' := false) (by decide) (view_readBoth P true s)
    (view_readBoth P false s) h

end Hiop.Seeded

#print axioms Hiop.Seeded.aim_member
#print axioms Hiop.Seeded.aim_not_reads
#print axioms Hiop.Seeded.aim_not_hides
#print axioms Hiop.Seeded.two_member
#print axioms Hiop.Seeded.two_not_fits
#print axioms Hiop.Seeded.two_not_hides
