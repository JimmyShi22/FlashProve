-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5RestIdn.lean: kind K5: THE FIELD bodyIdn OF K5Rest (K5AtMgPaid.lean), AS A THEOREM AT THE COMPOSED MEANING, AT THE PICK Zof := fun w => (𝔇.H.hid w).MA g (the model's integers of the group's attention sub-proof, as the witness is read).

Why. The field says: the two families of identities at the model's integers give the body of the constraint "idn" at the segment. At an odd number that is not the output head's that body is partA (shapeA X g) ((H.hid w).MA g) .idn :=
AttOwn1 ∧ AttOwn2 (Johnson/P5J/MeansQ.lean), and these two (Johnson/Goal/Meaning/Row.lean) are the two families, sign for sign: so the field holds by unfolding.

Main names: `zofAny`, `zofAll`: the pick. `shapeA_at`: the shape of the group's plan. `bodyIdn_any`: general in 𝔇. `bodyIdn_all`: at the closed constant. `rest_idn`: THE CHECK.
Is it empty here? An implication over witnesses whose antecedent is its conclusion's own text. IT FIXES THE LETTER Zof: K5Rest's field cells is owed at this Zof.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5RestOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.OnPublicFiles (headLink)
open OnBytes.Road.L5 (dimOf Zs cellsA)
open P5J (AtMgA mgAtAll TS)

/-- The shape of the group's plan. -/
theorem shapeA_at {X : Verify.Public} {g : ℕ} {a : Attention.Plan} (ha : X.A[g]? = some a) : OnBytes.Road.Hd.shapeA X g = a.S := by
  unfold OnBytes.Road.Hd.shapeA
  rw [ha]
  rfl

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public} (𝔇 : MgData Xi P Tok rows cols nR X)

/-- **The pick of Zof**: the model's integers of group g's attention sub-proof, as the witness is read. -/
def zofAny (g : ℕ) (w : Wit (CellsQ rows cols) Tok MsgT) : Zs := (𝔇.H.hid w).MA g

/-- **The field bodyIdn.** -/
theorem bodyIdn_any {g : ℕ} {a : Attention.Plan} (hH : 2 * g + 1 ≠ headLink X) (ha : X.A[g]? = some a) : ∀ i a₁ y w,
    ((∀ k b g' n, (Inst.Model.AttSeg.Idn.at1 k b g' n).Valid (dimOf a.S) →
        Inst.Model.AttSeg.idnVal (dimOf a.S) (Inst.Model.AttSeg.castT (cellsA a.S (zofAny 𝔇 g w)) : Inst.Model.AttSeg.Raw → Cb.Gl.F) (.at1 k b g' n) = 0) ∧
      ∀ b g' n, (Inst.Model.AttSeg.Idn.at2 b g' n).Valid (dimOf a.S) →
        Inst.Model.AttSeg.idnVal (dimOf a.S) (Inst.Model.AttSeg.castT (cellsA a.S (zofAny 𝔇 g w)) : Inst.Model.AttSeg.Raw → Cb.Gl.F) (.at2 b g' n) = 0) →
    bodyAll 𝔇 (2 * g + 1) .idn i a₁ y w := by
  intro i a₁ y w hf
  unfold bodyAll
  rw [if_neg hH, if_neg (by omega), show (2 * g + 1) / 2 = g by omega, shapeA_at ha]
  exact hf

end

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA o Z D r Zp Np cF x)

/-- The pick at the closed constant. -/
noncomputable def zofAll (g : ℕ) : Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT → Zs := zofAny h.𝔇 g

theorem bodyIdn_all {g : ℕ} {a : Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a) : ∀ i a₁ y w,
    ((∀ k b g' n, (Inst.Model.AttSeg.Idn.at1 k b g' n).Valid (dimOf a.S) →
        Inst.Model.AttSeg.idnVal (dimOf a.S) (Inst.Model.AttSeg.castT (cellsA a.S (zofAll h g w)) : Inst.Model.AttSeg.Raw → Cb.Gl.F) (.at1 k b g' n) = 0) ∧
      ∀ b g' n, (Inst.Model.AttSeg.Idn.at2 b g' n).Valid (dimOf a.S) →
        Inst.Model.AttSeg.idnVal (dimOf a.S) (Inst.Model.AttSeg.castT (cellsA a.S (zofAll h g w)) : Inst.Model.AttSeg.Raw → Cb.Gl.F) (.at2 b g' n) = 0) →
    bodyAll h.𝔇 (2 * g + 1) .idn i a₁ y w :=
  bodyIdn_any h.𝔇 (notHead_any (scope_all h).1 g) ha

/-- **THE CHECK.** -/
theorem rest_idn {Fr : Frame} {Ld : Laid} {Ms : List OracleShape} {bs g : ℕ} {before : List (ℕ × ℕ)} {a : Attention.Plan} {x₁ : Look.Place}
    {pl : VerifiableInference.Desc.Place} {O : List Item} {Q : List Pub} {Lk : Link S Claim} {same : S → S → Bool} {blk : Block S Claim}
    {nm : String} (ha : (P5J.At.X Zp).A[g]? = some a)
    (R : K5RestAll (Fr := Fr) h Ld Ms bs g before a x₁ pl O Q Lk same blk nm (zofAll h g)) :
    K5RestAll (Fr := Fr) h Ld Ms bs g before a x₁ pl O Q Lk same blk nm (zofAll h g) :=
  { R with bodyIdn := bodyIdn_all h ha }

end

end H2K5.Door

#print axioms H2K5.Door.shapeA_at
#print axioms H2K5.Door.bodyIdn_any
#print axioms H2K5.Door.bodyIdn_all
#print axioms H2K5.Door.rest_idn
