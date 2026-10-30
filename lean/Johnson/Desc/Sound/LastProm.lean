-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/LastProm.lean: WHAT THE FILES OF A KIND OF THE LAST CHAIN OWE FOR THE PROMISE BEHIND ITS BLOCK COMES DOWN TO THE BOOK-KEEPING, A TEST WITH CODE. One small lemma on the table, one statement written as
def … : Prop, and its proof.

The last chain's promise at a border (onQ₃, Johnson/Desc/Sound/BordersLastQ.lean; onL, Johnson/Desc/Last/BordersLast.lean) has five clauses. THREE ONLY RIDE: the slot's own condition Oc · "no mark" of the first chain · while
Omega's pin is open: the shared chain's promise on Omega. LastPromOf: past a piece that leaves what was handed to the chain as it is, whose stretch begins behind the trees that these three read, THEY ARE PAID
BY MAKE (cellStays, colStays, out_behind: CALLED): so the promise behind the block follows from the promise in front, the book-keeping behind it (shape (k + 1): a Bool) and, behind the last block, "nothing is
left" (a Bool).
  pinO_open_mono: on the table: where Omega's pin is open behind a block it was open in front.

Limits. OcReadsBelow lo Oc and ReadsTree Mg Pm are conditions on letters (Johnson/Desc/Sound/OcRides.lean, OmegaCrosses.lean say who pays them). "It leaves what was handed": the seat's make.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.OcRides
import Johnson.Desc.Sound.OmegaCrosses

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.Last

/-- Where Omega's pin is open behind a block it was open in front of it. -/
theorem pinO_open_mono : ∀ k : ℕ,
    ((openSetsL lastPlaces startLast)[k + 1]?.getD []).contains ItemL.pinO = true →
    ((openSetsL lastPlaces startLast)[k]?.getD []).contains ItemL.pinO = true
  | 0, _ => by decide
  | 1, _ => by decide
  | 2, h => absurd h (by decide)
  | 3, h => absurd h (by decide)
  | k + 4, h => by
    have hl : (openSetsL lastPlaces startLast).length = 5 := by decide
    have hn : (openSetsL lastPlaces startLast)[k + 4 + 1]? = none :=
      List.getElem?_eq_none (by rw [hl]; omega)
    rw [hn] at h
    exact absurd h (by decide)

/-- **The promise behind a block of the last chain, from the promise in front and two tests with code.** -/
def LastPromOf : Prop :=
  ∀ (P S₁ S₂ S₃ Cl Wt : Type) (C : CK) (Fr : Frame) (N : NumbersS) (Mg : MeaningS S₂ (P × S₁) Wt)
    (Pm : PromMeaning S₂) (PL : PromMeaningL S₂ S₃ (P × S₁)) (Oc : P × S₁ → Strs → Prop) (lo : ℕ)
    (x : Piece C Fr ((P × S₁ × S₂) × S₃) Cl Wt),
    OcReadsBelow lo Oc → lo ≤ x.base → ReadsTree Mg Pm → (N.tenant .oOmega).1 < x.base →
    (∀ a τ b, x.ior.red.out a τ = some b → b.1.1 = a.1.1) →
    ∀ (k : ℕ) a τ b, onQ₃ N Mg Pm PL Oc k a → x.ior.red.out a τ = some b →
      PL.shape (k + 1) (b.1.1.1, b.1.1.2.1) b.1.1.2.2 b.1.2 = true →
      (lastPlaces.length ≤ k + 1 → PL.nothingLeft b.1.2 = true) →
      onQ₃ N Mg Pm PL Oc (k + 1) b

theorem lastPromOf : LastPromOf := by
  intro P S₁ S₂ S₃ Cl Wt C Fr N Mg Pm PL Oc lo x hOc hlo hR hO hK k a τ b ha hb hs hn
  have e := hK a τ b hb
  have e2 := out_behind x a b τ hb
  obtain ⟨h1, h2, h3, -, -⟩ := ha
  refine ⟨?_, ?_, fun hc => ?_, hs, hn⟩
  · show Oc (b.1.1.1, b.1.1.2.1) (strsOf Fr b.2)
    rw [e, e2]
    exact hOc (a.1.1.1, a.1.1.2.1) (strsOf Fr a.2) (strsOf Fr (behind C Fr x.base x.ds a.2 τ))
      (fun z => cellStays C Fr x.base x.ds a.2 τ z)
      (fun j z hj => colStays C Fr x.base x.ds a.2 τ j z (Nat.lt_of_lt_of_le hj hlo)) h1
  · show Mg.unmarked1 (b.1.1.1, b.1.1.2.1)
    rw [e]
    exact h2
  · have h3' := h3 (pinO_open_mono k hc)
    show (PromS.noColl .oOmega).holds N Pm b.1.1.2.2 (strsOf Fr b.2)
    rw [e, e2]
    have hcol : ∀ z, (strsOf Fr (behind C Fr x.base x.ds a.2 τ)).col (N.tenant .oOmega).1 z =
        (strsOf Fr a.2).col (N.tenant .oOmega).1 z := fun z =>
      colStays C Fr x.base x.ds a.2 τ _ z hO
    exact ⟨hR.1 _ _ _ _ hcol h3'.1, hR.2.1 _ _ _ _ _ hcol h3'.2⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.pinO_open_mono
#print axioms VerifiableInference.Desc.Sound.lastPromOf
