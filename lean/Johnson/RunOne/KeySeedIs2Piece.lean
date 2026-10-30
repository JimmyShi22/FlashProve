-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeySeedIs2Piece.lean: THE KEY FILE, THE SHARED CHAIN's OWN PINS 3 | 4 | 5: "L1 BY A
TERM" FROM A PIECE's YES: behind a yes of the
piece that holds held of the seated "send o_u" | "send o_omega", each sampled message of the sending
bears the sending kind's own sample row
(SeedIs), AT ITS NUMBER IN THE STATEMENT. Johnson/RunOne/KeySeedIs2.lean has it from the block's
decision at two rounds that fit (hd, hfit);
here both come out of "out x τ = some x'".

  send_rounds          the kind's second and fifth blocks declare the sending kind's own two rounds
  (off sendAt's text)
  two_of_fit           rounds that fit two declared rounds are two
  seedIs_send2_piece | seedIs_send5_piece       from the piece's yes (piece_decides_at ·
  piece_fits_at · roundsFit_noDigest')
  seedIs_send2_at | seedIs_send5_at             THE INDEX: with the border's shape behind (shape₂ at
  3 | 6: two | four messages stand) and two
                       messages in the sending: the number is k | 2 + k

OBJECT   pc with pc.b = held b, b.decide = b₂ | b₅'s, b.rounds = b₂ | b₅'s (so at seat b₂ | seat b₅:
both by rfl)
USER     on₂_of_tests' premise (L1) at the open pins 3 | 4 | 5 (KeyOn2Tests.lean): not
called here
What is not claimed. condPort at the place (hC) · that the sending has two messages (hlen) · a
member. Nothing on soundness.

-/
import Johnson.RunOne.KeySeedIs2
import Johnson.RunOne.KeyRows2225At
import Johnson.RunOne.KeySendYes
import Johnson.Desc.Plain.PieceFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open VerifiableInference.Desc VerifiableInference.Desc.Plain VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K1 (Par condPort SeedIs shapeAt shapesOf sampledAt)
open _root_.Desc.K14 (P14 blocks parK1 withU withOmega)
open Johnson.RunOne.KeyRows1 (roundsFit_noDigest')

/-- Rounds that fit two declared rounds are two. -/
theorem two_of_fit (d₁ d₂ : Fmt.DeclaredRound) (rs : List Fmt.RoundView) (h : roundsFit [d₁, d₂] rs = true) : ∃
    r₁ r₂, rs = [r₁, r₂] := by
  have hl := roundsFit_length _ _ h
  match rs, hl with
  | [r₁, r₂], _ => exact ⟨r₁, r₂, rfl⟩

section
variable (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St₂ Unit) (hbl : blocks Q = some [b1, b2, b3,
    b4, b5, b6, b7, b8])
include hbl

/-- **The two sendings declare the sending kind's own rounds.** -/
theorem send_rounds (sentU : Array OracleNotice) (hU : withU Q.S = some sentU) :
    b2.rounds = VerifiableInference.Desc.K1.rounds (parK1 Q 2 "o_u and the first mask" sentU) ∧
        b5.rounds = VerifiableInference.Desc.K1.rounds (parK1 Q 5 "o_omega and o_sp" (withOmega
        Q.S)) := by
  unfold blocks at hbl
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
      List.cons.injEq, and_true] at hbl
  obtain ⟨s, hs, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hbl
  obtain rfl : s = sentU := Option.some.inj (hs.symm.trans hU)
  exact ⟨rfl, rfl⟩

variable {Pr Cl W : Type} {C : CK} {Fr : Frame} (b : Block St₂ Cl)

/-- **"send o_u": L1 from the piece's yes.** -/
theorem seedIs_send2_piece (hd2 : b.decide = b2.decide) (hr2 : b.rounds = b2.rounds) (sentU : Array
    OracleNotice)
    (hU : withU Q.S = some sentU) (rad : Nat → Nat) (hC : condPort (parK1 Q 2
        "o_u and the first mask" sentU) rad = true)
    (pc : Piece C Fr (Pr × St₂) Cl W) (hpb : pc.b = held b) (x : (Pr × St₂) × Fr.E.Str) (τ : Iop.Tr
        (uLT C pc.ds))
    (x' : (Pr × St₂) × Fr.E.Str) (h : pc.ior.red.out x τ = some x')
    (k : Fin (shapesOf (parK1 Q 2 "o_u and the first mask" sentU)).length) (hk : sampledAt (parK1 Q
        2 "o_u and the first mask" sentU) k) :
    ∃ ρ y, SeedIs (parK1 Q 2 "o_u and the first mask" sentU).codes (shapeAt (parK1 Q 2
        "o_u and the first mask" sentU) k) x'.1.2.st
      (x'.1.2.st.oracles.size - (shapesOf (parK1 Q 2 "o_u and the first mask" sentU)).length +
          k.val) ρ y := by
  have hf := (piece_fits_at pc x τ x' h).1
  have hdd := piece_decides_at pc x τ x' h
  rw [hpb] at hf hdd
  have hf' : roundsFit (VerifiableInference.Desc.K1.rounds (parK1 Q 2 "o_u and the first mask"
      sentU)) (rvT C pc.ds τ ++ pc.back) = true := by
    rw [← (send_rounds Q b1 b2 b3 b4 b5 b6 b7 b8 hbl sentU hU).1, ← hr2]
    exact hf
  obtain ⟨r₁, r₂, hrs⟩ := two_of_fit _ _ _ hf'
  rw [hrs] at hf' hdd
  exact seedIs_send2 Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b hd2 sentU hU rad hC x.1 x'.1 (noDigest r₁)
      (noDigest r₂) _ hdd
    ((roundsFit_noDigest' _ [r₁, r₂]).trans hf') k hk

/-- **"send o_omega": L1 from the piece's yes.** -/
theorem seedIs_send5_piece (hd5 : b.decide = b5.decide) (hr5 : b.rounds = b5.rounds) (sentU : Array
    OracleNotice)
    (hU : withU Q.S = some sentU) (rad : Nat → Nat) (hC : condPort (parK1 Q 5 "o_omega and o_sp"
        (withOmega Q.S)) rad = true)
    (pc : Piece C Fr (Pr × St₂) Cl W) (hpb : pc.b = held b) (x : (Pr × St₂) × Fr.E.Str) (τ : Iop.Tr
        (uLT C pc.ds))
    (x' : (Pr × St₂) × Fr.E.Str) (h : pc.ior.red.out x τ = some x')
    (k : Fin (shapesOf (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S))).length) (hk : sampledAt
        (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)) k) :
    ∃ ρ y, SeedIs (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)).codes (shapeAt (parK1 Q 5
        "o_omega and o_sp" (withOmega Q.S)) k) x'.1.2.st
      (x'.1.2.st.oracles.size - (shapesOf (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S))).length +
          k.val) ρ y := by
  have hf := (piece_fits_at pc x τ x' h).1
  have hdd := piece_decides_at pc x τ x' h
  rw [hpb] at hf hdd
  have hf' : roundsFit (VerifiableInference.Desc.K1.rounds (parK1 Q 5 "o_omega and o_sp" (withOmega
      Q.S))) (rvT C pc.ds τ ++ pc.back) = true := by
    rw [← (send_rounds Q b1 b2 b3 b4 b5 b6 b7 b8 hbl sentU hU).2, ← hr5]
    exact hf
  obtain ⟨r₁, r₂, hrs⟩ := two_of_fit _ _ _ hf'
  rw [hrs] at hf' hdd
  exact seedIs_send5 Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b hd5 rad hC x.1 x'.1 (noDigest r₁) (noDigest r₂)
      _ hdd
    ((roundsFit_noDigest' _ [r₁, r₂]).trans hf') k hk

/-- **THE INDEX behind "send o_u"**: the message number k. -/
theorem seedIs_send2_at (hd2 : b.decide = b2.decide) (hr2 : b.rounds = b2.rounds) (sentU : Array
    OracleNotice)
    (hU : withU Q.S = some sentU) (rad : Nat → Nat) (hC : condPort (parK1 Q 2
        "o_u and the first mask" sentU) rad = true)
    (pc : Piece C Fr (Pr × St₂) Cl W) (hpb : pc.b = held b) (x : (Pr × St₂) × Fr.E.Str) (τ : Iop.Tr
        (uLT C pc.ds))
    (x' : (Pr × St₂) × Fr.E.Str) (h : pc.ior.red.out x τ = some x')
    (S : LinShape) (a : Nat) (hsh : LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 3 x'.1.2) = true)
    (hlen : (shapesOf (parK1 Q 2 "o_u and the first mask" sentU)).length = 2)
    (k : Fin (shapesOf (parK1 Q 2 "o_u and the first mask" sentU)).length) (hk : sampledAt (parK1 Q
        2 "o_u and the first mask" sentU) k) :
    ∃ ρ y, SeedIs (parK1 Q 2 "o_u and the first mask" sentU).codes (shapeAt (parK1 Q 2
        "o_u and the first mask" sentU) k) x'.1.2.st k.val ρ y := by
  obtain ⟨ρ, y, H⟩ := seedIs_send2_piece Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b hd2 hr2 sentU hU rad hC pc
      hpb x τ x' h k hk
  have e : x'.1.2.st.oracles.size - (shapesOf (parK1 Q 2 "o_u and the first mask" sentU)).length +
      k.val = k.val := by
    have h1 := shape₂_at3 S a _ hsh
    omega
  rw [e] at H
  exact ⟨ρ, y, H⟩

/-- **THE INDEX behind "send o_omega"**: the message number 2 + k. -/
theorem seedIs_send5_at (hd5 : b.decide = b5.decide) (hr5 : b.rounds = b5.rounds) (sentU : Array
    OracleNotice)
    (hU : withU Q.S = some sentU) (rad : Nat → Nat) (hC : condPort (parK1 Q 5 "o_omega and o_sp"
        (withOmega Q.S)) rad = true)
    (pc : Piece C Fr (Pr × St₂) Cl W) (hpb : pc.b = held b) (x : (Pr × St₂) × Fr.E.Str) (τ : Iop.Tr
        (uLT C pc.ds))
    (x' : (Pr × St₂) × Fr.E.Str) (h : pc.ior.red.out x τ = some x')
    (S : LinShape) (a : Nat) (hsh : LKFU.Shape23.ok (LKFU.Shape23.shape₂ S a 6 x'.1.2) = true)
    (hlen : (shapesOf (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S))).length = 2)
    (k : Fin (shapesOf (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S))).length) (hk : sampledAt
        (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)) k) :
    ∃ ρ y, SeedIs (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)).codes (shapeAt (parK1 Q 5
        "o_omega and o_sp" (withOmega Q.S)) k) x'.1.2.st (2 + k.val) ρ y := by
  obtain ⟨ρ, y, H⟩ := seedIs_send5_piece Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b hd5 hr5 sentU hU rad hC pc
      hpb x τ x' h k hk
  have e : x'.1.2.st.oracles.size - (shapesOf (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S))).length
      + k.val = 2 + k.val := by
    have h1 := shape₂_at6 S a _ hsh
    omega
  rw [e] at H
  exact ⟨ρ, y, H⟩

end

end Johnson.RunOne.KeyRows23
