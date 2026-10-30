-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/WordsTiedJobW.lean: WordsTied at the last chain's test, at
the job jobW, at a group of the three members: the clause tied of the test's acceptance at
the named files.

  find_three     a layout of the three members finds each at its place
  tied_at_jobW   WordsTied at jobW's rows, at a group of the three members, from the equation
                 WordsAreSent

By what. words_tied_three (WordsTiedW.lean).

Limits.
- hm: members_of_narrow (WSeatsNarrow.lean) has it at a record that agrees with the closed shape, which
  sameCore_at_seat gives at every stand.
- E: sent_at_W pays it at wordsAtW. hn₀ lets the first member stand at another job that makes the same
  member: first_member_is_own (LettersFirst.lean) has that at K1's lot's placeJob: rowsLaid_is_member
  then serves it too.
- hv, same, hs₀ to hs₂, hc₀ to hc₂, the codes' lengths: public or of the sending: premises.
- NOT IN FRONT OF A LAW OVER COINS. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.WordsTiedW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open OnBytes (Statement Group GroupLayout)
open OnBytes.Slice (GE)
open OnBytes.Means (Words layoutOf)
open ProofFile.Honest (Front State)
open ProofFile.Honest.K12 (TestCoins)
open ProofFile.Honest.K14 (Ask sendingsFit)
open ProofFile.Honest.K12.Light (plainMany WordsTied SameCut vecAt)
open Johnson.Prover.Send (shapeAt)
open VerifiableInference.Desc.K12 (P12 T12)

/-- A layout of the three members finds each at its place. -/
theorem find_three (L : GroupLayout) (hm : L.members = #[4, 197, 199]) :
    L.find 4 = some 0 ∧ L.find 197 = some 1 ∧ L.find 199 = some 2 := by
  unfold GroupLayout.find
  rw [hm]
  refine ⟨?_, ?_, ?_⟩ <;> simp [List.idxOf?, List.findIdx?_cons]

variable {W X Xi : Type}

/-- **WordsTied at jobW's rows, at a group of the three members.** -/
theorem tied_at_jobW {Wd₀ : Type} (q : P12) (door : W → Front X → T12) (JF : K1.SendJob Readers X)
    (JW : K1.SendJob (K1.PlaceIn Xi) X)
    (Ap : ProofFile.Honest.K14.SendPub) (rd : W → Readers) (wit : W → K1.PlaceIn Xi) (ask : W → Ask)
    (n₁ : Nat) (JI : K1.SendJob Wd₀ X) (readers : W → Wd₀) (k₀ : Nat) (f₀ : Option Nat × Option Nat)
    (hn₀ : (jobW q door JF JW Ap rd wit ask n₁).mems[0]? = some (memK1 JI readers senderI k₀ f₀))
    (w : W) (fr : Front X) (C : TestCoins) (hQ : sendingsFit Ap.P = true)
    (hk : 0 < (ProofFile.Honest.K14.jobOmega ⟨Ap.P, n₁ + Ap.atPoint⟩).Q.sent.size)
    (t : State Ask Unit) (cs : Array OnBytes.E)
    (hv : vecAt (ProofFile.Honest.K14.jobOmega ⟨Ap.P, n₁ + Ap.atPoint⟩) 0 ask none w fr =
      (ProofFile.Honest.K14.jobOmega ⟨Ap.P, n₁ + Ap.atPoint⟩).data t 0)
    (same : SameCut (ProofFile.Honest.K14.jobOmega ⟨Ap.P, n₁ + Ap.atPoint⟩) 0 cs (C.mem 2))
    (s : T12) (g : Nat) (G : Group)
    (hm : G.members = #[4, 197, 199])
    (hs₀ : (s.st.oracles[4]?).map (·.shape) = some (shapeAt JI.P k₀))
    (hs₁ : (s.st.oracles[197]?).map (·.shape) = some (shapeAt JW.P 0))
    (hs₂ : (s.st.oracles[199]?).map (·.shape) = some (ProofFile.Honest.K12.Light.shapeAt
      (ProofFile.Honest.K14.jobOmega ⟨Ap.P, n₁ + Ap.atPoint⟩) 0))
    (hc₀ : s.st.codes = JI.P.codes) (hc₁ : s.st.codes = JW.P.codes)
    (hc₂ : s.st.codes = (ProofFile.Honest.K14.jobOmega ⟨Ap.P, n₁ + Ap.atPoint⟩).Q.codes)
    (hl₀ : 0 < (shapeAt JI.P k₀).mainRows →
      (JI.P.codes.base.getD (shapeAt JI.P k₀).code default).ell =
        2 ^ (JI.P.codes.base.getD (shapeAt JI.P k₀).code default).logEll)
    (hz₀ : 0 < (shapeAt JI.P k₀).maskRows →
      (JI.P.codes.mask.getD (shapeAt JI.P k₀).maskCode default).ell =
        2 ^ (JI.P.codes.mask.getD (shapeAt JI.P k₀).maskCode default).logEll)
    (hl₁ : 0 < (shapeAt JW.P 0).mainRows →
      (JW.P.codes.base.getD (shapeAt JW.P 0).code default).ell =
        2 ^ (JW.P.codes.base.getD (shapeAt JW.P 0).code default).logEll)
    (hz₁ : 0 < (shapeAt JW.P 0).maskRows →
      (JW.P.codes.mask.getD (shapeAt JW.P 0).maskCode default).ell =
        2 ^ (JW.P.codes.mask.getD (shapeAt JW.P 0).maskCode default).logEll)
    (hl₂ : 0 < (ProofFile.Honest.K12.Light.shapeAt
        (ProofFile.Honest.K14.jobOmega ⟨Ap.P, n₁ + Ap.atPoint⟩) 0).mainRows →
      ((ProofFile.Honest.K14.jobOmega ⟨Ap.P, n₁ + Ap.atPoint⟩).Q.codes.base.getD
        (ProofFile.Honest.K12.Light.shapeAt (ProofFile.Honest.K14.jobOmega ⟨Ap.P, n₁ + Ap.atPoint⟩) 0).code
        default).ell =
        2 ^ ((ProofFile.Honest.K14.jobOmega ⟨Ap.P, n₁ + Ap.atPoint⟩).Q.codes.base.getD
          (ProofFile.Honest.K12.Light.shapeAt (ProofFile.Honest.K14.jobOmega ⟨Ap.P, n₁ + Ap.atPoint⟩) 0).code
          default).logEll)
    (hz₂ : 0 < (ProofFile.Honest.K12.Light.shapeAt
        (ProofFile.Honest.K14.jobOmega ⟨Ap.P, n₁ + Ap.atPoint⟩) 0).maskRows →
      ((ProofFile.Honest.K14.jobOmega ⟨Ap.P, n₁ + Ap.atPoint⟩).Q.codes.mask.getD
        (ProofFile.Honest.K12.Light.shapeAt (ProofFile.Honest.K14.jobOmega ⟨Ap.P, n₁ + Ap.atPoint⟩) 0).maskCode
        default).ell =
        2 ^ ((ProofFile.Honest.K14.jobOmega ⟨Ap.P, n₁ + Ap.atPoint⟩).Q.codes.mask.getD
          (ProofFile.Honest.K12.Light.shapeAt (ProofFile.Honest.K14.jobOmega ⟨Ap.P, n₁ + Ap.atPoint⟩) 0).maskCode
          default).logEll)
    (m : Words GE)
    (E : WordsAreSent s.st m 4 197 199
      (K1.rowsR JI.P JI.ride (JI.data (readers w) fr)
        (csAt _ (K1.startR JI.P JI.ride k₀) (C.mem 0)) k₀)
      (K1.rowsR JW.P JW.ride (JW.data (wit w) fr) (csAt _ (K1.startR JW.P JW.ride 0) (C.mem 1)) 0)
      (shapeAt JI.P k₀) (shapeAt JW.P 0)
      (ProofFile.Honest.K14.jobOmega ⟨Ap.P, n₁ + Ap.atPoint⟩) t cs 0) :
    WordsTied s.st g G m (layoutOf s.st G)
      (plainMany (jobW q door JF JW Ap rd wit ask n₁) w fr C) := by
  obtain ⟨e₀, e₁, e₂⟩ := find_three (layoutOf s.st G) hm
  exact words_tied_three (jobW q door JF JW Ap rd wit ask n₁) w fr C JI JW readers wit
    senderI senderW senderO k₀ 0 f₀ _ _ hn₀ rfl Ap.P hQ
    (ProofFile.Honest.K14.jobOmega ⟨Ap.P, n₁ + Ap.atPoint⟩) (Or.inr ⟨rfl, rfl⟩) 0 hk _ rfl ask t hv cs
    rfl same s.st g G (layoutOf s.st G) 4 197 199 hm e₀ e₁ e₂ hs₀ hs₁ hs₂ hc₀ hc₁ hc₂ hl₀ hz₀ hl₁
    hz₁ hl₂ hz₂ m E

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.find_three
#print axioms ProofFile.Honest.K12.AtProof.tied_at_jobW
