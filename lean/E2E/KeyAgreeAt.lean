-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyAgreeAt.lean: K12/AgreeAtKey.lean's two laws TAKEN at the
thread's own jobs, at ⟨QK, 0⟩ (mems_U, mems_O of KeyDepthsClosed.lean), so that the premises' forms are
seen to fit the binders: at the book's own rows and look, at every k.

  agree_key_U, agree_key_O   Agree at jobKU's and jobKO's J

Limits. As K12/AgreeAtKey.lean's head. At O, plain coins. Nothing on completeness, soundness or hiding.
-/
import E2E.KeyDepthsClosed
import Johnson.Desc.ProofFile.Honest.K12.AgreeAtKey

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

namespace AtPublicFiles.KeyAgreeAt
open ProofFile.Honest
open OnBytes (TableKey)
open VerifiableInference.Desc (Block)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyLay (JKU JKO jobKU jobKO)
open AtPublicFiles.KeyDepthsClosed (AQ members_U fresh_U members_O fresh_O)
open H2K.Member (piKUFull piKOFull)
open ProofFile.Honest.K12 (Agree firstPart restPart firstRd restCoins agree_at_U agree_at_O)

variable {V W₀ Rc X₀ : Type} (K₀ : KeyPub) (hK₀ : fullPub = some K₀)
  (bs : List (Block St Unit)) (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64))
  (wts : Common W₀ Rc TableKey → Weights) (rnd : Common W₀ Rc TableKey → TableRand)

include hK₀ in
/-- **Agree at jobKU's J at a coin that the book lends.** -/
theorem agree_key_U (k : Coins (keyBook K₀))
    (c : RowCoins [(firstPart (JKU (X := X₀) AQ bs st wts rnd) : Part V _ _),
      restPart (JKU (X := X₀) AQ bs st wts rnd)])
    (hc : lendRow (keyBook K₀) ((keyBook K₀).rowsOf 1) (k.look 1) piKUFull.place
      [(firstPart (JKU (X := X₀) AQ bs st wts rnd) : Part V _ _),
        restPart (JKU (X := X₀) AQ bs st wts rnd)] 0 = .ok c)
    (w : Common W₀ Rc TableKey) (fr : Front X₀) :
    Agree (JKU (X := X₀) AQ bs st wts rnd) w fr (JKU (X := X₀) AQ bs st wts rnd).s₀
      (firstRd (JKU (X := X₀) AQ bs st wts rnd) c.1)
      (restCoins (JKU (X := X₀) AQ bs st wts rnd) c.2.1) :=
  agree_at_U K₀ hK₀ (jobKU (X := X₀) AQ piKUFull bs st wts rnd) rfl members_U fresh_U _ _ c hc w fr

include hK₀ in
/-- **Agree at jobKO's J at a coin that the book lends**, at plain coins. -/
theorem agree_key_O (k : Coins (keyBook K₀))
    (c : RowCoins [(firstPart (JKO (X := X₀) AQ bs wts rnd) : Part V _ _),
      restPart (JKO (X := X₀) AQ bs wts rnd)])
    (hc : lendRow (keyBook K₀) ((keyBook K₀).rowsOf 1) (k.look 1) piKOFull.place
      [(firstPart (JKO (X := X₀) AQ bs wts rnd) : Part V _ _),
        restPart (JKO (X := X₀) AQ bs wts rnd)] 0 = .ok c)
    (w : Common W₀ Rc TableKey) (fr : Front X₀) :
    Agree (JKO (X := X₀) AQ bs wts rnd) w fr (JKO (X := X₀) AQ bs wts rnd).s₀
      (firstRd (JKO (X := X₀) AQ bs wts rnd) c.1)
      (restCoins (JKO (X := X₀) AQ bs wts rnd) c.2.1) :=
  agree_at_O K₀ hK₀ (jobKO (X := X₀) AQ piKUFull piKOFull bs wts rnd) rfl members_O fresh_O _ _ c hc w fr

end AtPublicFiles.KeyAgreeAt

#print axioms AtPublicFiles.KeyAgreeAt.agree_key_U
#print axioms AtPublicFiles.KeyAgreeAt.agree_key_O
