-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyOn2Scope.lean: THE KEY FILE, THE ROAD TO A MEMBER OF on₂ k: "L1 at the shared
chain's own pins" (l1hi_at3 | l1hi_at6, Johnson/RunOne/KeyOn2Step.lean) WITH ITS PUBLIC TIES PAID IN
SCOPE, AND ITS PREMISE h3 PAID AT PIECES.
  seedIs_rides_piece   a sample row that stands in front of a piece that holds held of one of the
                       kind's eight seated blocks stands behind its yes (seedIs_rides through
                       piece_decides_at)
  h3_of_pieces         so pin 3's row rides from border 3 to border 6, past three pieces
  sentUKey · withU_key what goes out with o_u at the typed key can be said
  len2 · smp2 · tieS2 · len5 · smp50 · smp51 · tieS50 · tieS51
                       CLOSED FACTS, by evaluation in Lean's kernel, at the kind's parameters at the
                       typed key (p14Key, Johnson/RunOne/KeyRowsInScope.lean): either sending has
                       two messages; the pinned ones are sampled; their shapes are the written
                       shU | shO | shSp; the codes are csKey by rfl
  l1hi_at3_scope | l1hi_at6_scope
                       l1hi_at3 | l1hi_at6 at Q := p14At X P where the planner's sized key is
                       keyFull (key_of_scope): hU · hlen · hk · tieC · tieS are no premises any more
OBJECT   the pieces that hold held of (Key.descriptionFromSource X N P).shared.blocksInOrder[2 … 5]
USER     on₂_of_tests | on₂_of_step: not called here
What is not claimed. condPort at the two places (hC). IT FIXES THE RELEASE's ONE CONFIGURATION.
No member is shown. Nothing on soundness.

-/
import Johnson.RunOne.KeyOn2Step
import Johnson.RunOne.KeySmpStay2
import Johnson.RunOne.KeyRowsInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.K1 (SeedIs condPort shapesOf sampledAt)
open VerifiableInference.Desc.Plain
open _root_.Run.PQ (CK)
open _root_.Desc.K14 (P14 blocks parK1 withU withOmega)
open Cb Johnson.Pack OnBytes.Maker OnBytes.Slice
open OnBytes.Params VerifiableInference.Desc.Sound
open Lk6.AtPlan (keyFull)

/-! ## 1 A sample row rides past a piece -/

section
variable {Pr Cl W : Type} {C : CK} {Fr : Frame} (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St₂ Unit)
  (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
include hbl

theorem seedIs_rides_piece (b₀ : Block St₂ Unit) (hmem : b₀ ∈ [b1, b2, b3, b4, b5, b6, b7, b8])
    (b : Block St₂ Cl) (hd : b.decide = b₀.decide) (pc : Piece C Fr (Pr × St₂) Cl W)
    (hpb : pc.b = held b) (x : (Pr × St₂) × Fr.E.Str) (τ : Iop.Tr (uLT C pc.ds))
    (x' : (Pr × St₂) × Fr.E.Str) (h : pc.ior.red.out x τ = some x') (cs : OnBytes.Codes)
    (s : OnBytes.OracleShape) (o : Nat)
    (H : ∃ ρ y, SeedIs cs s x.1.2.st o ρ y) : ∃ ρ y, SeedIs cs s x'.1.2.st o ρ y := by
  obtain ⟨ρ, y, H⟩ := H
  have hdd := piece_decides_at pc x τ x' h
  rw [hpb] at hdd
  exact ⟨ρ, y, seedIs_rides Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b₀ hmem b hd x.1 x'.1 _ _ hdd cs s o ρ y
      H⟩

/-- **h3: from border 3 to border 6**: past "(rec_gamma)", "LOC" and "send o_omega". -/
theorem h3_of_pieces (c3 c4 c5 : Block St₂ Cl) (hd3 : c3.decide = b3.decide)
    (hd4 : c4.decide = b4.decide) (hd5 : c5.decide = b5.decide)
    (p3 p4 p5 : Piece C Fr (Pr × St₂) Cl W) (e3 : p3.b = held c3) (e4 : p4.b = held c4)
    (e5 : p5.b = held c5) (x3 x4 x5 x6 : (Pr × St₂) × Fr.E.Str) (τ3 : Iop.Tr (uLT C p3.ds))
    (τ4 : Iop.Tr (uLT C p4.ds)) (τ5 : Iop.Tr (uLT C p5.ds)) (o3 : p3.ior.red.out x3 τ3 = some x4)
    (o4 : p4.ior.red.out x4 τ4 = some x5) (o5 : p5.ior.red.out x5 τ5 = some x6)
    (cs : OnBytes.Codes) (s : OnBytes.OracleShape) (o : Nat)
    (H : ∃ ρ y, SeedIs cs s x3.1.2.st o ρ y) : ∃ ρ y, SeedIs cs s x6.1.2.st o ρ y :=
  seedIs_rides_piece Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b5 (by simp) c5 hd5 p5 e5 x5 τ5 x6 o5 cs s o
    (seedIs_rides_piece Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b4 (by simp) c4 hd4 p4 e4 x4 τ4 x5 o4 cs s o
      (seedIs_rides_piece Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b3 (by simp) c3 hd3 p3 e3 x3 τ3 x4 o3 cs s o
        H))

end

/-! ## 2 The closed facts at the typed key -/

/-- What goes out with o_u at the typed key. -/
def sentUKey : Array OnBytes.OracleNotice := (withU keyFull.once.shape).getD #[]

theorem withU_key : withU keyFull.once.shape = some sentUKey := by
  have h : (withU keyFull.once.shape).isSome = true := by decide +kernel
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 h
  unfold sentUKey
  rw [hs]
  rfl

abbrev P2K : VerifiableInference.Desc.K1.Par := parK1 (p14Key []) 2 "o_u and the first mask"
    sentUKey
abbrev P5K : VerifiableInference.Desc.K1.Par :=
  parK1 (p14Key []) 5 "o_omega and o_sp" (withOmega keyFull.once.shape)

theorem len2 : (shapesOf P2K).length = 2 := by decide +kernel
theorem len5 : (shapesOf P5K).length = 2 := by decide +kernel
theorem smp2 : sampledAt P2K ⟨0, by rw [len2]; decide⟩ := by decide +kernel
theorem smp50 : sampledAt P5K ⟨0, by rw [len5]; decide⟩ := by decide +kernel
theorem smp51 : sampledAt P5K ⟨1, by rw [len5]; decide⟩ := by decide +kernel
theorem tieS2 : VerifiableInference.Desc.K1.shapeAt P2K ⟨0, by rw [len2]; decide⟩ =
    Johnson.Top.H.shU := by decide +kernel
theorem tieS50 : VerifiableInference.Desc.K1.shapeAt P5K ⟨0, by rw [len5]; decide⟩ =
    Johnson.Top.H.shO := by decide +kernel
theorem tieS51 : VerifiableInference.Desc.K1.shapeAt P5K ⟨1, by rw [len5]; decide⟩ =
    Johnson.Top.H.shSp := by decide +kernel

/-! ## 3 L1 at the chain's own pins, in scope -/

section
variable {Cl W : Type} {C : CK} {Fr : Frame} (X : Source) (P : LaterPlaces)
  (hkey : X.chains.made.sized.key = keyFull) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St₂ Unit)
  (hbl : blocks (p14At X P) = some [b1, b2, b3, b4, b5, b6, b7, b8]) (b : Block St₂ Cl)
include hkey hbl

theorem l1hi_at3_scope (hd2 : b.decide = b2.decide) (hr2 : b.rounds = b2.rounds) (radP : ℕ → ℕ)
    (hC : condPort (parK1 (p14At X P) 2 "o_u and the first mask" sentUKey) radP = true)
    (pc : Piece C Fr (P₂ × St₂) Cl W) (hpb : pc.b = held b) (x : (P₂ × St₂) × Fr.E.Str)
    (τ : Iop.Tr (uLT C pc.ds)) (x' : (P₂ × St₂) × Fr.E.Str) (h : pc.ior.red.out x τ = some x')
    (S : LinShape) (a : ℕ) (hsh : LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 3 x'.1.2) = true) :
    ∀ i : Fin six.length, numSix i ∈ pinned (open₂ 3) → ¬ numSix i < 3 →
      ∃ o ρ y, orc₂ (numSix i) = some o ∧ SeedIs Johnson.Top.H.csKey (six.get i).1 x'.1.2.st o ρ y
          := by
  rw [p14At_key hkey P] at hbl hC
  exact l1hi_at3 (p14Key (beforeSharedPoint P)) b1 b2 b3 b4 b5 b6 b7 b8 hbl b hd2 hr2 sentUKey
    withU_key radP hC pc hpb x τ x' h S a hsh len2 smp2 rfl tieS2

theorem l1hi_at6_scope (hd5 : b.decide = b5.decide) (hr5 : b.rounds = b5.rounds) (radP : ℕ → ℕ)
    (hC : condPort (parK1 (p14At X P) 5 "o_omega and o_sp" (withOmega (p14At X P).S)) radP = true)
    (pc : Piece C Fr (P₂ × St₂) Cl W) (hpb : pc.b = held b) (x : (P₂ × St₂) × Fr.E.Str)
    (τ : Iop.Tr (uLT C pc.ds)) (x' : (P₂ × St₂) × Fr.E.Str) (h : pc.ior.red.out x τ = some x')
    (S : LinShape) (a : ℕ) (hsh : LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 6 x'.1.2) = true)
    (h3 : ∃ ρ y, SeedIs Johnson.Top.H.csKey Johnson.Top.H.shU x'.1.2.st 0 ρ y) :
    ∀ i : Fin six.length, numSix i ∈ pinned (open₂ 6) → ¬ numSix i < 3 →
      ∃ o ρ y, orc₂ (numSix i) = some o ∧ SeedIs Johnson.Top.H.csKey (six.get i).1 x'.1.2.st o ρ y
          := by
  rw [p14At_key hkey P] at hbl hC
  exact l1hi_at6 (p14Key (beforeSharedPoint P)) b1 b2 b3 b4 b5 b6 b7 b8 hbl b hd5 hr5 sentUKey
    withU_key radP hC pc hpb x τ x' h S a hsh len5 smp50 smp51 rfl tieS50 tieS51 h3

end

end Johnson.RunOne.KeyRows23
