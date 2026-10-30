-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/SendWFrame.lean: MEMBER 356 OF THE PROOF FILE's OWN FIRST CHAIN (W's sending at
the place M:4 and the rows behind it) IN THE FORM THAT THE THREAD's FRAME ASKS (ProofFile.Honest.Carries |
Returns at firstZA g vals, Johnson/AtFull/Shape/FrameForm.lean). Under the head P5J.AtMgA; a joining
of laws; nothing is evaluated.
  `sendW_rounds_at`: the member's declared rounds are K1's at W's parameters (K1.rounds (wPar Zp
    msg)).
  `sendWA P W`: the step on the whole: sendWGS P W on the chain's shape (SendWStepAtHead.lean); the
    makes of W's rows (sendForms P) and of the rows behind them (rowsForms W m), read at the shape m
    that W's sending's own step wG returns.
  **`sendW_frame`**: with msg what linMessageW reads off the first chain's parameters: for every g
    with g 356 = sendWA (wPar Zp msg) (K13.whereOf Zp) and every vals with vals 356 s rs gs = seedsV
    (wPar Zp msg) rs: Carries and Returns at 356.
By sendW_step_at (SendWStepAtHead.lean), sendW_forms_at (SendWFormsAtHead.lean), IM.back_of |
back_numbers | alone_rounds (Johnson/IMR/), carries_of_seat | returns_of_seat | seedsV
(FrameForm.lean), k1_fit (FormsAtHead.lean).
Limits. The step g and the test vals are letters with an equation at one number: no table of all 358
is built here. "Carries" is under the step's own return; two of sendWGS's tests are enough, not
shown to be needed: the step may refuse where the member says yes. seedsV IS A TEST ON VALUES IN A
ROUND (no seed's factor is 0). UNDER THE HEAD: that it has a member is shown in scope, where the
reader returns and `protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three
hold together, at two named sets of public files (`VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap`), in a side
library (AtFullSide/Top/HeadMemberAtFull.lean, HeadMemberAtGap.lean). No state is shown by a theorem
at which the step returns. At the earlier hash OnBytes.secondHashFunction. Nothing on soundness, completeness or
hiding.
Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.Shape.FrameOpt
import Johnson.AtFull.Shape.SendWFormsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link KindName roundsFit noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)
open ProofFile.Honest (Shape Carries Returns carries_seat returns_seat)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The declared rounds of member 356 are K1's at W's parameters. -/
theorem sendW_rounds_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ (b : Block S ProofFile.Cl) (msg : Array OracleNotice),
      linMessageW Zp.first.lin = some msg ∧ cF.blocksInOrder[356]? = some b ∧
      b.rounds = VerifiableInference.Desc.K1.rounds (wPar Zp msg) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, -, -, b, b', w, eb, -, hw, rfl, la⟩ := IM.back_of O
  have q := (IM.back_numbers h.scope h.reads O).1 3 b eb
  unfold VerifiableInference.Desc.K13.wBlock VerifiableInference.Desc.K1.wAt at hw
  obtain ⟨msg, hm, rfl⟩ := Option.map_eq_some_iff.1 hw
  refine ⟨_, msg, hm, q, ?_⟩
  rw [IM.alone_rounds la]
  exact List.append_nil _

/-- The step of member 356 on the whole: sendWGS on the chain's shape; the makes of W's rows and of
the rows behind them, read at the shape m behind W's sending. wG P x.1 stands twice in this text:
bare, and inside sendWGS. -/
def sendWA (P : VerifiableInference.Desc.K1.Par) (W : VerifiableInference.Desc.K13.Where)
    (x : ShA) : Except String ShA :=
  match wG P x.1, sendWGS P W x.1 with
  | some m, some u => .ok (u, rowsForms W m (sendForms P x.1.core.st.oracles.length x.2))
  | _, _ => .error "the member at M:4 refuses on shapes"

/-- **The frame's two premises at member 356** (W's sending and the rows behind it). -/
theorem sendW_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ msg : Array OracleNotice,
      (cF.blocksInOrder[356]?).isSome = true ∧ linMessageW Zp.first.lin = some msg ∧
      ∀ (ft : Nat) g vals,
        g 356 = sendWA (wPar Zp msg) (VerifiableInference.Desc.K13.whereOf Zp) →
        (∀ s rs gs, vals 356 s rs gs = seedsV (wPar Zp msg) rs) →
        Carries cF.blocksInOrder ft (firstZA g vals) 356 ∧ Returns cF.blocksInOrder ft (firstZA g vals) 356 := by
  obtain ⟨b, msg, hm, q, hc, hr⟩ := sendW_step_at h
  obtain ⟨b₁, msg₁, hm₁, q₁, hrd⟩ := sendW_rounds_at h
  obtain ⟨b₂, msg₂, hm₂, q₂, hf⟩ := sendW_forms_at h
  obtain rfl : msg = msg₁ := Option.some.inj (hm.symm.trans hm₁)
  obtain rfl : msg = msg₂ := Option.some.inj (hm.symm.trans hm₂)
  obtain rfl : b = b₁ := Option.some.inj (q.symm.trans q₁)
  obtain rfl : b = b₂ := Option.some.inj (q.symm.trans q₂)
  refine ⟨msg, by rw [q]; rfl, hm, fun ft g vals hg hv => ⟨?_, ?_⟩⟩
  · refine carries_of_seat q fun s rs gs t u hfit hd hu => ?_
    rw [hg] at hu
    rw [hrd] at hfit
    obtain ⟨r₁, r₂, rfl, -, -⟩ := k1_fit hfit
    unfold sendWA at hu
    split at hu
    · rename_i m w hm' hw
      cases hu
      have := hc s _ gs t w hd hw
      subst this
      show (chainSh t, _) = (chainSh t, formsOf t.st)
      rw [hf s (noDigest r₁) (noDigest r₂) gs t m hd hm']
      rfl
    · cases hu
  · refine returns_of_seat q fun s rs gs u hfit hu hvv => ?_
    rw [hg] at hu
    rw [hv] at hvv
    rw [hrd] at hfit
    obtain ⟨r₁, r₂, rfl, -, han⟩ := k1_fit hfit
    unfold sendWA at hu
    split at hu
    · rename_i m w hm' hw
      refine hr s (noDigest r₁) (noDigest r₂) gs w hw ?_ han
      intro y hy
      have := List.all_eq_true.1 hvv y hy
      simpa using this
    · cases hu

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.sendW_rounds_at
#print axioms Johnson.AtFull.Shape.sendW_frame
#print axioms Johnson.AtFull.Shape.sendWA
