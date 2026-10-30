-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/PlaysAtBase.lean: "it plays" (PlaysS) at each of K1's 52 members of the first chain,
at lettersHead with the first chain's Script firstScriptAt, at the prover that the maker returns at
the base filling, at every Said.

  playsS_k1_base   number 2, each K1.noL l d, number 356

By what. playsS_k1_own (AtFullSide/K1/PlaysOwn.lean). Its premises on the member: k1Seated_first,
fields member, shape, half, fits, heardOnly. Its premise on the Script: ownTrees_first.

Limits.
- The head and the maker's return are hypotheses. The ten other letters of lettersHead and Said are
  bound by "for all": nothing here reads them.
- PlaysS asks under the pair ThrS: nothing here says that the pair holds of any stand.
- "It plays" is the frame's name for a premise's form. It is no completeness.
- Nothing on soundness, completeness or hiding.
-/
import AtFullSide.K1.PlaysOwn
import AtFullSide.K1.FirstScript

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest.FirstThread

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {W₀ : Type}
  {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **IT PLAYS AT EACH OF K1's 52 MEMBERS.** Under the head and the maker's return alone. -/
theorem playsS_k1_base (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : LocB W₀ → Prop) (Rd : Nat → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀)
    (Said : Nat → Coins A.B → Mid (LocB W₀) Unit → Prop) :
    PlaysS (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w).thread Said 2 ∧
      (∀ l, l < 25 → ∀ d : Bool,
        PlaysS (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
          w).thread Said (K1.noL l d)) ∧
      PlaysS (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w).thread Said 356 := by
  obtain ⟨⟨b₂, R₂⟩, hl, ⟨bw, Rw⟩⟩ :=
    k1Seated_first (I := I) (S := S) (Op := Op) h hA test carryX item n₁ n₂ b₀ Vd Rd Kp w
  refine ⟨?_, fun l hlt d => ?_, ?_⟩
  · exact playsS_k1_own _ Said 2 b₂ (witB I A.Z) _ () R₂.member R₂.shape R₂.half R₂.fits
      R₂.heardOnly (ownTrees_first_two h hA test carryX item n₁ n₂ b₀ Vd Rd Kp w)
  · obtain ⟨bl, Rl⟩ := hl l hlt d
    exact playsS_k1_own _ Said (K1.noL l d) bl (witB I A.Z) _ () Rl.member Rl.shape Rl.half Rl.fits
      Rl.heardOnly (ownTrees_first_later h hA test carryX item n₁ n₂ b₀ Vd Rd Kp w hlt d)
  · exact playsS_k1_own _ Said 356 bw (witB I A.Z) _ () Rw.member Rw.shape Rw.half Rw.fits
      Rw.heardOnly (ownTrees_first_w h hA test carryX item n₁ n₂ b₀ Vd Rd Kp w)

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.playsS_k1_base
