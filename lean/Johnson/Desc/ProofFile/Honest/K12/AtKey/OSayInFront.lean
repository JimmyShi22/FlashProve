-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OSayInFront.lean: the rows that the test on G_omega takes in hold, in front of the
test, at every stand at 10 of the filled key thread and every coin lent: `says_at_ten_key` in the form `SaysInFront`
(E2E/OfflineSayAtRun.lean).

  `says_in_front_at_ten`   the statement, at any letter whose stands hold the field

Limits.
- NOT IN FRONT OF A LAW OVER COINS: `says_in_front_at_ten` bears this label; the rule is at its home, the head of
  Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: the letters w, k, m, E stand under the premise u (`ThrS`), of the
  first kind, and the sentence reads the input and the coins. None: the bar is flat.
- `SaysInFront` asks of the group under test alone: one is there at this state: `group_under_test` at the door's shape.
- hfield is a premise. That a stand at 10 is reached is not said.
- Nothing on completeness of the whole chain, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OSays
import E2E.OfflineSayAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open OnBytes (TableKey)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source)
open Desc.K14 (St)
open Desc.K14.Honest (Eight)
open ProofFile.Honest
open ProofFile.Honest.K14
open ProofFile.Honest.K12
open AtPublicFiles.KeySharedThread (parKey sentKey)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.AtFiles.Full (QK PF)
open AtPublicFiles.HalvesAreJobs (JO)
open AtPublicFiles.TableFilled (TR)
open AtPublicFiles.OfflineRows (SaysInFront)

section
variable (K₀ : KeyPub) (hK₀ : fullPub = some K₀) {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (K₁ : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)
  (B : Eight (parKey Xs PF)) (own₀ : X₀)

include hK₀ in
/-- **The rows that the test on G_omega takes in hold, in front of it, at every stand at 10 and every coin lent.** -/
theorem says_in_front_at_ten (e : parKey Xs PF = QK) {layO : OnBytes.TreeLay}
    (hQ : Plan2 (parKey Xs PF) (sentKey Xs PF) layO)
    (Said : ℕ → Coins (keyBook K₀) → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (hfield : ∀ k s m E, ThrS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 10 k s m E →
      ∀ cols, (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀).colsTo 10 m E = .ok cols →
      m.opened = some cols)
    (k : Coins (keyBook K₀)) (s : St) (m : Mid (Common W₀ Rc TableKey) X₀) (E : Env)
    (c : RowCoins [(firstPart (JO Xs K₁ B) : Part Empty _ _), restPart (JO Xs K₁ B)])
    (u : ThrS (TR K₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀) Said 10 k s m E)
    (hc : lendRow (keyBook K₀) ((keyBook K₀).rowsOf 1) (k.look 1) (JO Xs K₁ B).p.place
      [(firstPart (JO Xs K₁ B) : Part Empty _ _), restPart (JO Xs K₁ B)] 0 = .ok c) :
    SaysInFront (JO Xs K₁ B) m.st.input (frontOf m)
      (ProofFile.Honest.K12.Light.plainMany (manyAtTen Xs K₁ B (X₀ := X₀)) m.st.input (frontOf m)
        (restCoins (JO Xs K₁ B) c.2.1)) :=
  says_at_ten_key K₀ hK₀ Xs Nr K₁ ℓ Nm Mg₀ tk rest Kp Vd w B own₀ e hQ u.1 (hfield k s m E u) c hc

end

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.says_in_front_at_ten
