-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeySeedIs2.lean: «L1 BY A TERM» AT THE KEY FILE's SHARED
CHAIN's OWN PINS 3 | 4 | 5: BEHIND A YES OF A SENDING's BLOCK AS THE MAKER HOLDS IT (held b), THE
RECORD HOLDS THE SENDING KIND's OWN SAMPLE ROW AT EVERY SAMPLED MESSAGE (SeedIs:
Johnson/Desc/K1/Law/SeedIs.lean): general in the block; then at K14's second and fifth blocks («send
o_u» | «send o_omega»). After seedIs_of_step (Johnson/Top/Fire/Code/KeyFillStep.lean: the first chain's first block).
BY CALLS: seedIs_behind | SeedIs.travels | size_behind | reads_exists
(Johnson/Desc/K1/Law/) · held_okView | drawn_ok | factor_ok
(Johnson/Top/Fire/Code/KeyFillFactor.lean: the held block's yes holds the words'
test: general in the block) · hS_sends | hS_send5 (Johnson/RunOne/KeyRowsSeat.lean).
OBJECT: held b · USER: a member of on₂ … 3 | 6 (hasSmp ∧ NoColl at the new pins, through
sealed_gives | member_of_record): the strings' side's first half · LETTERS: P rad stOf b; Q.
  [seedIs_of_held: in a file of its own, Johnson/RunOne/KeySeedIsHeld.lean]
    general: IsSend P stOf' (held b) · condPort · the rounds fit · the block's yes ⟹
    ∃ ρ y, SeedIs … (stOf z'.2) (size − the place's messages + k) ρ y
  seedIs_send2 | seedIs_send5   at K14's own blocks
What is not claimed. NO MEMBER OF ANY PROMISE IS SHOWN HERE: an implication from a yes. That no
collision lies at that seed. Nothing on soundness.

-/
import Johnson.RunOne.KeyRowsSeat
import Johnson.RunOne.KeySeedIsHeld

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Plain VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K1 (Par condPort IsSend SeedIs shapeAt shapesOf sampledAt
    seedIs_behind size_behind reads_exists decideSend_iff)
open _root_.Desc.K14 (P14 blocks parK1 withU withOmega)

section
variable {Pr Cl : Type} (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St₂ Unit) (hbl : blocks Q = some
    [b1, b2, b3, b4, b5, b6, b7, b8]) (b : Block St₂ Cl)
include hbl

/-- **Behind «send o_u».** -/
theorem seedIs_send2 (hd2 : b.decide = b2.decide) (sentU : Array OracleNotice) (hU : withU Q.S =
    some sentU) (rad : Nat → Nat)
    (hC : condPort (parK1 Q 2 "o_u and the first mask" sentU) rad = true) (z z' : Pr × St₂) (r₁ r₂ :
        Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hd : (held b : Block (Pr × St₂) Cl).decide z [r₁, r₂] gs
        = .ok z')
    (hfit : roundsFit (VerifiableInference.Desc.K1.rounds (parK1 Q 2 "o_u and the first mask"
        sentU)) [r₁, r₂] = true)
    (k : Fin (shapesOf (parK1 Q 2 "o_u and the first mask" sentU)).length) (hk : sampledAt (parK1 Q
        2 "o_u and the first mask" sentU) k) :
    ∃ ρ y, SeedIs (parK1 Q 2 "o_u and the first mask" sentU).codes (shapeAt (parK1 Q 2
        "o_u and the first mask" sentU) k) z'.2.st
      (z'.2.st.oracles.size - (shapesOf (parK1 Q 2 "o_u and the first mask" sentU)).length + k.val)
          ρ y := by
  obtain ⟨sentU', hU', h⟩ := hS_sends (P := Pr) Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b hd2
  obtain rfl : sentU' = sentU := Option.some.inj (hU'.symm.trans hU)
  exact seedIs_of_held _ rad hC (fun s : St₂ => s.st) b h z z' r₁ r₂ gs hd hfit k hk

/-- **Behind «send o_omega».** -/
theorem seedIs_send5 (hd5 : b.decide = b5.decide) (rad : Nat → Nat)
    (hC : condPort (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)) rad = true) (z z' : Pr × St₂) (r₁
        r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hd : (held b : Block (Pr × St₂) Cl).decide z [r₁, r₂] gs
        = .ok z')
    (hfit : roundsFit (VerifiableInference.Desc.K1.rounds (parK1 Q 5 "o_omega and o_sp" (withOmega
        Q.S))) [r₁, r₂] = true)
    (k : Fin (shapesOf (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S))).length) (hk : sampledAt
        (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)) k) :
    ∃ ρ y, SeedIs (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)).codes (shapeAt (parK1 Q 5
        "o_omega and o_sp" (withOmega Q.S)) k) z'.2.st
      (z'.2.st.oracles.size - (shapesOf (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S))).length +
          k.val) ρ y :=
  seedIs_of_held _ rad hC (fun s : St₂ => s.st) b (hS_send5 (P := Pr) Q b1 b2 b3 b4 b5 b6 b7 b8 hbl
      b hd5) z z' r₁ r₂ gs hd hfit k hk

end

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.seedIs_send2
#print axioms Johnson.RunOne.KeyRows23.seedIs_send5
