-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyOn2Step.lean: THE
PREMISE L1hi OF on₂_of_tests (Johnson/RunOne/KeyOn2Tests.lean), TO THE LETTER, AT THE TWO BORDERS
BEHIND THE SHARED CHAIN's OWN SENDINGS, k = 3 | 6, PAID «BY A TERM»: OUT OF THE PIECE's OWN YES
(pc.ior.red.out x τ = some x' at pc.b = held b, b the description's second | fifth block of K14):
by seedIs_send2_at | seedIs_send5_at (KeySeedIs2Piece.lean) and four public ties (the place's codes
are csKey; its sampled messages' shapes are the six's shU | shO | shSp). After on₁'_of_step.
AN IMPLICATION: NO MEMBER IS SHOWN. y' IS BUILT, NO RUN's OWN.
OBJECT: on₂_of_tests' L1hi at k = 3 | 6 and z := x'.1 · USER: the member's column of rows 2.3 | 2.4
| 2.5 (through the forward halves from border 3) and 2.6 | 2.7 | 2.8 (from border 6) · LETTERS:
X N P D; decT recOf tab coll enc rad off₂; Q b1 … b8 b pc x τ x'.
  l1hi_at3   at border 3 the one own pin (3 ↦ message 0: o_u) bears the sending kind's row
  l1hi_at6   at border 6: pins 4 | 5 (↦ messages 2 | 3: o_omega | o_sp) out of the fifth block's
    yes; PIN 3's ROW IS A PREMISE THERE (h3: it was earned at border 3 and must have stayed:
    SeedIs.stays | old: not called here)
Nothing on soundness.
-/
import Johnson.RunOne.KeyOn2Tests
import Johnson.RunOne.KeySeedIs2Piece

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.KeyRows23
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.Key (Xi FirstState)
open VerifiableInference.Desc.K1 (SeedIs condPort shapesOf sampledAt)
open VerifiableInference.Desc.Plain
open Johnson.RunOne.KeyRows1 (plan₁)
open _root_.Run.PQ (CK)
open _root_.Desc.K14 (P14 blocks parK1 withU withOmega)
open Cb Johnson.Pack OnBytes.Maker OnBytes.Slice
open OnBytes.Params VerifiableInference.Desc.Sound

theorem pins₂_at3 : pinned (open₂ 3) = [0, 2, 3] := by decide
theorem pins₂_at6 : pinned (open₂ 6) = [0, 2, 3, 4, 5] := by decide

section
variable (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St₂ Unit) (hbl : blocks Q = some [b1, b2, b3,
    b4, b5, b6, b7, b8])
  {Cl W : Type} {C : CK} {Fr : Frame} (b : Block St₂ Cl)
include hbl

/-- **L1hi at border 3, out of the piece's yes.** -/
theorem l1hi_at3 (hd2 : b.decide = b2.decide) (hr2 : b.rounds = b2.rounds) (sentU : Array
    OnBytes.OracleNotice)
    (hU : withU Q.S = some sentU) (radP : ℕ → ℕ) (hC : condPort (parK1 Q 2 "o_u and the first mask"
        sentU) radP = true)
    (pc : Piece C Fr (P₂ × St₂) Cl W) (hpb : pc.b = held b) (x : (P₂ × St₂) × Fr.E.Str) (τ : Iop.Tr
        (uLT C pc.ds))
    (x' : (P₂ × St₂) × Fr.E.Str) (h : pc.ior.red.out x τ = some x')
    (S : LinShape) (a : ℕ) (hsh : LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 3 x'.1.2) = true)
    (hlen : (shapesOf (parK1 Q 2 "o_u and the first mask" sentU)).length = 2)
    (hk : sampledAt (parK1 Q 2 "o_u and the first mask" sentU) ⟨0, by rw [hlen]; decide⟩)
    (tieC : (parK1 Q 2 "o_u and the first mask" sentU).codes = Johnson.Top.H.csKey)
    (tieS : VerifiableInference.Desc.K1.shapeAt (parK1 Q 2 "o_u and the first mask" sentU) ⟨0,
        by rw [hlen]; decide⟩ = Johnson.Top.H.shU) :
    ∀ i : Fin six.length, numSix i ∈ pinned (open₂ 3) → ¬ numSix i < 3 →
      ∃ o ρ y, orc₂ (numSix i) = some o ∧ SeedIs Johnson.Top.H.csKey (six.get i).1 x'.1.2.st o ρ y
          := by
  intro i hi hn
  have H := seedIs_send2_at Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b hd2 hr2 sentU hU radP hC pc hpb x τ x' h
      S a hsh hlen ⟨0, by rw [hlen]; decide⟩ hk
  rw [tieC, tieS] at H
  obtain ⟨ρ, y, H⟩ := H
  rw [pins₂_at3] at hi
  obtain ⟨q, hq⟩ := i
  have h6 : q < 6 := hq
  interval_cases q
  · exact absurd (show (0 : ℕ) < 3 by decide) hn
  · exact absurd (show (1 : ℕ) < 3 by decide) hn
  · exact absurd (show (2 : ℕ) < 3 by decide) hn
  · exact ⟨0, ρ, y, rfl, H⟩
  · exact absurd (show (4 : ℕ) ∈ [0, 2, 3] from hi) (by decide)
  · exact absurd (show (5 : ℕ) ∈ [0, 2, 3] from hi) (by decide)

/-- **L1hi at border 6**: pins 4 | 5 out of the piece's yes; pin 3's row a premise. -/
theorem l1hi_at6 (hd5 : b.decide = b5.decide) (hr5 : b.rounds = b5.rounds) (sentU : Array
    OnBytes.OracleNotice)
    (hU : withU Q.S = some sentU) (radP : ℕ → ℕ) (hC : condPort (parK1 Q 5 "o_omega and o_sp"
        (withOmega Q.S)) radP = true)
    (pc : Piece C Fr (P₂ × St₂) Cl W) (hpb : pc.b = held b) (x : (P₂ × St₂) × Fr.E.Str) (τ : Iop.Tr
        (uLT C pc.ds))
    (x' : (P₂ × St₂) × Fr.E.Str) (h : pc.ior.red.out x τ = some x')
    (S : LinShape) (a : ℕ) (hsh : LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 6 x'.1.2) = true)
    (hlen : (shapesOf (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S))).length = 2)
    (hk0 : sampledAt (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)) ⟨0, by rw [hlen]; decide⟩)
    (hk1 : sampledAt (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)) ⟨1, by rw [hlen]; decide⟩)
    (tieC : (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)).codes = Johnson.Top.H.csKey)
    (tieS0 : VerifiableInference.Desc.K1.shapeAt (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)) ⟨0,
        by rw [hlen]; decide⟩ = Johnson.Top.H.shO)
    (tieS1 : VerifiableInference.Desc.K1.shapeAt (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)) ⟨1,
        by rw [hlen]; decide⟩ = Johnson.Top.H.shSp)
    (h3 : ∃ ρ y, SeedIs Johnson.Top.H.csKey Johnson.Top.H.shU x'.1.2.st 0 ρ y) :
    ∀ i : Fin six.length, numSix i ∈ pinned (open₂ 6) → ¬ numSix i < 3 →
      ∃ o ρ y, orc₂ (numSix i) = some o ∧ SeedIs Johnson.Top.H.csKey (six.get i).1 x'.1.2.st o ρ y
          := by
  intro i _ hn
  have H0 := seedIs_send5_at Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b hd5 hr5 sentU hU radP hC pc hpb x τ x'
      h S a hsh hlen ⟨0, by rw [hlen]; decide⟩ hk0
  have H1 := seedIs_send5_at Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b hd5 hr5 sentU hU radP hC pc hpb x τ x'
      h S a hsh hlen ⟨1, by rw [hlen]; decide⟩ hk1
  rw [tieC, tieS0] at H0
  rw [tieC, tieS1] at H1
  obtain ⟨ρ0, y0, H0⟩ := H0
  obtain ⟨ρ1, y1, H1⟩ := H1
  obtain ⟨ρ3, y3, H3⟩ := h3
  obtain ⟨q, hq⟩ := i
  have h6 : q < 6 := hq
  interval_cases q
  · exact absurd (show (0 : ℕ) < 3 by decide) hn
  · exact absurd (show (1 : ℕ) < 3 by decide) hn
  · exact absurd (show (2 : ℕ) < 3 by decide) hn
  · exact ⟨0, ρ3, y3, rfl, H3⟩
  · exact ⟨2, ρ0, y0, rfl, H0⟩
  · exact ⟨3, ρ1, y1, rfl, H1⟩

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.l1hi_at3
#print axioms Johnson.RunOne.KeyRows23.l1hi_at6
