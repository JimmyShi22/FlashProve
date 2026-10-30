-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastRcCore.lean: ONE THEOREM, CUT OUT OF LastAtRc.lean,
UNTURNED [by program]: `FoldFirst₃.ofRc`: the four facts on what the first chain hands on, at Oc :=
`ocEnd … ∧ Rc`, Rch := Rc of what is handed, FROM hRc : ∀ q y, `ocEnd … q y` → Rc q → (get
q).2.failed = none → `rcLastB 0 (vAt Z N₁) Ld cs (get q).2 = true`, and `PlanOk₃`. Limits: hRc is a
premise. Nothing on soundness.
-/
import Johnson.LLT25R.LastV
import Johnson.LLT25R.LastRestX

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
    OnBytes.TreeBook) (Pm₀ : PromMeaning St) (N₁ : Numbers) (Ns : NumbersS) (links : List ModelPart) (X :
          St → Bool) (r : Fmt.M1.Stage → ℕ) (Ld :
          VerifiableInference.Desc.K12.Door.Laid)

variable (decT : (ℕ → Option (ℕ × List UInt64)) → (((FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z
    (seatK Z N) N c).S₁ × St) × (FL o mk Z (seatK Z N) N c).S₃) → Option Cells) (c₀' : Cells) (a₁ :
    Block (FL o mk Z (seatK Z N) N c).S₁ (FL o mk Z (seatK Z N) N c).Cl) (k₁ : List (Block (FL o mk
    Z (seatK Z N) N c).S₁ (FL o mk Z (seatK Z N) N c).Cl)) (a₂ : Block St (FL o mk Z (seatK Z N) N
    c).Cl) (k₂ : List (Block St (FL o mk Z (seatK Z N) N c).Cl)) (rest₁ : (i : ℕ) → (ds : List RDT)
    → Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) ((FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z
    (seatK Z N) N c).S₁) (Wit Cells Tok MsgT) ds) (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP
    .two) (frameAt D (allOf D) D.key₂ 0) (((FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z
    N) N c).S₁) × St) (Wit Cells Tok MsgT) ds) (d wEnd : Wit Cells Tok MsgT)

variable (Rc : (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ → Prop)

/-- **The four facts on what the first chain hands on, at any Rc that gives the five tests.** -/
theorem FoldFirst₃.ofRc (hRc : ∀ q y, ocEnd get N₁ (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁
    M₁) links (First.flatPlaces true links true) q y → Rc q → (get q).2.failed = none →
    ToldDesc.rcLastB 0 (vAt Z N₁) Ld (p14At Z).codes (get q).2 = true)
    (hP : PlanOk₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links (First.flatPlaces true links true) r
        (N₁.treesAt none) 0 1 (vAt Z N₁) Ld) :
    FoldFirst₃ o mk Z N c D G arr get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns X
        (fun q y => ocEnd get N₁ (meaningSig (p14At Z).codes G arr smp₁ ms₁ decT₁ M₁) links
        (First.flatPlaces true links true) q y ∧ Rc q) (N₁.treesAt none) 0 1 (vAt Z N₁) Ld (fun a =>
        Rc (a.1.1.1, a.1.1.2.1)) where
  two := fun _ _ hon hR hf => ToldDesc.rcLast_two (hRc _ _ hon.1.1 hR hon.2.1) hf
  roots := fun a f e hon hR hf he => by
    obtain ⟨k1, k2⟩ := ToldDesc.rcLast_roots (hRc _ _ hon.1.1 hR hon.2.1) hf
    obtain ⟨f₀, e₀, -, he₀, hk⟩ := shapeAt_of_onL _ _ _ _ _ _ _ _ hon
    obtain rfl : e₀ = e := Option.some.inj (he₀.symm.trans he)
    refine ⟨k1.trans ?_, k2, ToldDesc.omega_clause (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) hk
        hP.oneOmega⟩
    have hb := ToldDesc.bookAt_of_ocEnd get N₁ _ links _ _ _ hon.1.1 hon.2.1
    have hf' := hf
    unfold firstOfS at hf'
    obtain ⟨e', -, rfl⟩ := Option.map_eq_some_iff.1 hf'
    exact hb
  carried := fun _ _ hon hR hf => ToldDesc.rcLast_seats (hRc _ _ hon.1.1 hR hon.2.1) hf
  sampleE := fun _ f hon hR hf i x hx hi hw => by
    obtain ⟨xI, hxI, sxI, shI⟩ := hP.mineI
    obtain ⟨xW, hxW, sxW, shW⟩ := hP.mineW
    refine ToldDesc.rcLast_sample (hRc _ _ hon.1.1 hR hon.2.1) hf hi ?_
    rcases hw with hw | hw
    · obtain rfl := hP.oneSeat x hx xI hxI (hw.trans sxI.symm)
      exact .inl ⟨hw, shI⟩
    · obtain rfl := hP.oneSeat x hx xW hxW (hw.trans sxW.symm)
      exact .inr ⟨hw, shW⟩

end LLT25

#print axioms LLT25.FoldFirst₃.ofRc
