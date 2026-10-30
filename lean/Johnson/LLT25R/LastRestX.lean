-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastRestX.lean (treeO is no field of
`FoldRest₃`): THE ONE FACT OF `FoldRest₃` (LastOwedCore.lean), seedO,
ON THE SHARED CHAIN's END, IS A THEOREM FROM WHAT THE LAYER X SAYS. One theorem.
  `FoldRest₃.ofX`: `FoldRest₃` from `PlanOk₃` and `XSamples cs S X` (LastSeedO.lean: wherever
    X says yes, Omega's message is there, has the plan's shape and passes `sampleL`). General in Oc
    and Rch: seedO spends neither "reached" nor Oc: what it spends of the promise is the
    book-keeping's yes and "ended … = some e", which holds X's yes.
Limits. `XSamples` is a premise. NO MEMBER. Nothing on soundness.
-/
import Johnson.LLT25R.LastOwedCore
import Johnson.LLT25R.LastSeedO

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace LLT25
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker Fo.Peel Cb
    Johnson.Pack
open Iop Prob _root_.Run
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn onOwn)
open VerifiableInference.Desc.Third (SharedOut firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers openSets sampledIn start)
open VerifiableInference.Desc.K13 (Where)
open _root_.Desc.K14 (St)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)
open ToldDesc (p14At)
open _root_.Desc.K14.Law.Fence (CoreFacts MemberFacts)
open H2K.Pin (NTuple)

variable (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (N : H2U.Places4) (c : Chain S Cl) {Cells Tok
          P₀ : Type} (D : WholeD) {Xi' : Type} (G : FileDescription Xi') (arr : ℕ → ℕ → ℕ) (dB : RDT) (dt : List
                 RDT) (get : (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ → P₀ × First.S)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf (p14At Z).codes
    s.l).om i).Smp) (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf (p14At
    Z).codes s.l).om i).Smp) (ms₁ ms₂ : List Mem) (decT₁ : (ℕ → Option (ℕ × List UInt64)) → P₀ ×
    First.S → Option Cells) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (M₁ :
    Meaning P₀ (Wit Cells Tok MsgT)) (MS : MeaningS St ((FL o mk Z (seatK Z N) N c).XiPub × (FL o mk
    Z (seatK Z N) N c).S₁) (Wit Cells Tok MsgT)) (stOf : St → OnBytes.Statement) (bookOf : St →
    OnBytes.TreeBook) (Pm₀ : PromMeaning St) (N₁ : Numbers) (Ns : NumbersS) (links : List ModelPart) (ps :
          List VerifiableInference.Desc.Place) (X : St → Bool) (Oc : (FL o mk Z (seatK Z N) N c).XiPub ×
          (FL o mk Z (seatK Z N) N c).S₁ → Strs → Prop) (rd : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (n₁ ft nΩ : ℕ)
        (V : VerifiableInference.Desc.Last.OwnSeats) (Ld :
    VerifiableInference.Desc.K12.Door.Laid) (Rch : (((FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z
    (seatK Z N) N c).S₁ × (FL o mk Z (seatK Z N) N c).S₂) × (FL o mk Z (seatK Z N) N c).S₃) ×
    (frameAt D (allOf D) D.key₃ (FL o mk Z (seatK Z N) N c).lastChainFirstTreeNumber).E.Str → Prop)

variable {o mk Z N c D G arr dB dt get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns
    links ps X Oc rd r n₁ ft nΩ V Ld Rch}

/-- **`FoldRest₃` from the tests on the plan and what the layer says of Omega's message.** -/
theorem FoldRest₃.ofX (hP : PlanOk₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links ps r n₁ ft nΩ V Ld)
    (hX : XSamples (p14At Z).codes (p14At Z).S X) :
    FoldRest₃ o mk Z N c D G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns X Oc
        nΩ Rch where
  seedO := fun a e hon _ he x hx hw => by
    obtain ⟨f₀, e₀, -, he₀, hk⟩ := shapeAt_of_onL _ _ _ _ _ _ _ _ hon
    obtain rfl : e₀ = e := Option.some.inj (he₀.symm.trans he)
    obtain ⟨xO, hxO, sxO, shO⟩ := hP.omegaSeat
    obtain rfl := hP.oneSeat x hx xO hxO (hw.trans sxO.symm)
    obtain ⟨st, rest, hst⟩ : ∃ st rest, (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.stages = st :: rest
        := by
      cases h : (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.stages with
      | nil =>
        have h2 := hP.twoStages
        rw [h] at h2
        simp at h2
      | cons st rest => exact ⟨st, rest, rfl⟩
    have hT := (hP.planAt x hx st rest hst).1
    rw [← shO] at hT ⊢
    exact seed_at_end (p14At Z) _ f₀ e₀ a.1.2 hk X a.1.1.2.2 hX he hT

end LLT25

#print axioms LLT25.FoldRest₃.ofX
