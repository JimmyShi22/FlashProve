-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/LaidMw1.lean: K01_law: LaidK1 («what the composed meaning's constant gives»: Johnson/Desc/K1/Law/CallsG.lean) HAS A MEMBER AT THE WIDER MEANING mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀), GENERAL IN Dm · dk · Mg₀, UNDER TWO PREMISES: hsmp (the reader of OOD samples is the named one, smpNamed (Johnson/Desc/Sound/SmpNamed.lean), at a
list of seats) · hfB (the test on the book says BookFits: bookFitsB_iff). The other eight fields: FillsK1's nine (fillsK1_mw1) and equations that hold by the composed meaning's own make.
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.MemberMw1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Maker Cb Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll d13 smpNamed)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.K13.Law (plus13)
open VerifiableInference.Desc.K12.Door (K12Data)

variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

/-- **LaidK1 at mw1.** -/
theorem laidK1_mw1 (seats : List (ℕ × ℕ)) (hsmp : Dm.smp = smpNamed Dm.cs seats)
    (hfB : ∀ B, Sound.bookFitsB B = true ↔ Book.BookFits B) (xb : S → Bool := fun _ => true) :
    LaidK1 Dm.N Dm.pubD Dm.G Dm.arr Dm.smp Dm.ms Dm.decT Dm.shape Dm.layout
      (fun a => (mgAll Dm Mg₀).inOrder a && liveX Dm.N Dm.shape xb a.2)
      (plus13 (d13 Dm) dk Mg₀).pub XV Dm.sent
      (First.FillP1.fillP1 Dm.d1 Dm.rw13 Dm.A1 Dm.cr1 Mg₀) seats Dm.St Dm.after Dm.wt Dm.rw
      (headLink XV) Dm.put Dm.H Dm.headPart Dm.digitsPart (.more none "K12.bookFits")
      Sound.bookFitsB Mg₀ (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀) xb) :=
  { fills := fillsK1_mw1 Dm dk Mg₀ xb
    num := rfl
    smp := hsmp
    row := rfl
    forms := rfl
    constr := rfl
    ioLive := fun _ h => by
      have h2 := (Bool.and_eq_true _ _ ▸ h).2
      unfold liveX at h2
      exact (Bool.and_eq_true _ _ ▸ h2).1
    fits := fun _ => rfl
    fitsSays := hfB }

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.laidK1_mw1
