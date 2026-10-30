-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeySeedIsHeld.lean: BEHIND A YES OF A SENDING's BLOCK AS THE
MAKER HOLDS IT (held b), THE RECORD HOLDS THE SENDING KIND's OWN SAMPLE ROW AT EVERY SAMPLED MESSAGE
(SeedIs: Johnson/Desc/K1/Law/SeedIs.lean): GENERAL IN THE BLOCK. A FILE OF ITS OWN, WITH LIGHT
IMPORTS, WANTED FOR the key file's first chain's later sendings: cut out of
Johnson/RunOne/KeySeedIs2.lean, not a token of the theorem turned.
BY CALLS: seedIs_behind | SeedIs.travels | size_behind | reads_exists | decideSend_iff
(Johnson/Desc/K1/Law/) · held_okView | drawn_ok | factor_ok
(Johnson/Top/Fire/Code/KeyFillFactor.lean).
OBJECT: held b · USER: seedIs_send2 | seedIs_send5 (KeySeedIs2.lean); a walk
at the first chain · LETTERS: P rad stOf b.
  seedIs_of_held   IsSend P stOf' (held b) · condPort · the rounds fit · the block's yes ⟹ ∃ ρ y,
    SeedIs … (stOf z'.2) (size − the place's messages + k) ρ y
What is not claimed. NO MEMBER OF ANY PROMISE: an implication from a yes. That no collision lies at
that seed. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.KeyFillFactor
import Johnson.Desc.K1.Law.Sound
import Johnson.Desc.K1.Law.SeedIs
import Johnson.Desc.K1.Law.GoodSend3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Plain VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K1 (Par condPort IsSend SeedIs shapeAt shapesOf sampledAt
    seedIs_behind size_behind reads_exists decideSend_iff)

/-- **Behind a held sending's yes the record holds the kind's own sample row.** -/
theorem seedIs_of_held {Pr S Cl : Type} (P : Par) (rad : Nat → Nat) (hC : condPort P rad = true)
    (stOf : S → Statement) (b : Block S Cl)
    (hS : IsSend P (fun z : Pr × S => stOf z.2) (held b : Block (Pr × S) Cl)) (z z' : Pr × S) (r₁ r₂
        : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hd : (held b : Block (Pr × S) Cl).decide z [r₁, r₂] gs =
        .ok z')
    (hfit : roundsFit (VerifiableInference.Desc.K1.rounds P) [r₁, r₂] = true)
    (k : Fin (shapesOf P).length) (hk : sampledAt P k) :
    ∃ ρ y, SeedIs P.codes (shapeAt P k) (stOf z'.2) ((stOf z'.2).oracles.size - (shapesOf P).length
        + k.val) ρ y := by
  obtain ⟨L, d, d', owed, ids, hyes, hsame, hsz⟩ := hS _ _ _ _ _ hd
  have hok := LPFD.drawn_ok _ (LPFD.held_okView b _ _ _ _ hd) r₁ List.mem_cons_self
  obtain ⟨ρ, hρ⟩ := reads_exists P r₁ (LPFD.factor_ok P _ hok) ((decideSend_iff P owed d d' _ _
      ids).1 hyes).1.2.2.1
  obtain ⟨y, hy⟩ := seedIs_behind P rad owed d d' _ _ ids hC hfit hyes ρ hρ k hk
  have hsize := size_behind P owed d d' _ _ ids hyes
  have e2 : (stOf z'.2).oracles.size - (shapesOf P).length + k.val = d.st.oracles.size + k.val := by
    have h1 : (stOf z'.2).oracles.size = d'.st.oracles.size := hsz
    rw [h1, hsize]
    omega
  rw [e2]
  exact ⟨_, y, hy.travels hsame⟩

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.seedIs_of_held
