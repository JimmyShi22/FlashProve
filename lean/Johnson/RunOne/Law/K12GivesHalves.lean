-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12GivesHalves.lean: THE FIELD «gives» OF Left15 (Johnson/RunOne/Law/K12Left15.lean) FROM TWO HALVES AT THE BLOCK's OWN decide: the form in which the tables' files themselves pay a row (keeps_of_halves, Johnson/Desc/Key/KeyKeeps.lean), with two things added: the kind's law's conclusion as a premise of the backward half, and a NAMED map on witnesses in its conclusion. One statement; its proof is five lines. IT MOVES THE WEIGHT; IT PAYS NONE.
OBJECT. `Left15.gives`' type. USER. Whoever fills Left15.
LETTERS. The35.lean's; dB dt nl rad rd: Left15's. tbl: THE ONE TABLE THAT IS LAID AS MESSAGE 1 (and as the pad at its seat): it may read the statement in front and the witness behind: so a payer who takes it by choice off the kind's tuple has the witness's own message 1 to fall back on where there is no tuple (M is a bare letter: no member of it is at hand otherwise).
Premises: hbase: the trees of the messages whose pins are open in front lie below the maker's base (a payer: basesOk, Johnson/Top/Fire/Code/BasesOk.lean: a test that reads the letter at_) · fwd: the promise in front, decide's yes and the strings' staying give the promise behind · back: these, THE PROMISE BEHIND, the seat's two doors, "what was handed rides", and "one tuple for all rows" at the strings in front: every item open behind at w gives every item open in front at w with message 1 laid.

  gives_of_halves: the statement.
Limits. fwd and back hold all the weight: neither is shown. back asks more than «gives» (the witness in front is named): the price of the form that lets the riding items ride. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12Left15
import Johnson.Desc.Key.KeyLay
import Johnson.Desc.Key.KeyKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace Johnson.RunOne.Law.K12AtThe21
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.KeyRows23 (BaseSt AtFk Fk fr₁ fr₂ fr₃ On₁ Cl₁ On₂ Cl₂ On₃ Cl₃ oneAt St₂ St₃ seam₁_at_fk seam₂_at_fk ends_at_fk)
open VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open OnBytes.Slice (Sg)
open H2K.Pin (NTuple)
open Johnson.RunOne.Sound (bareB)
open Johnson.RunOne.KeyRows1 (n₁ R₁ open₁)
open LPFD

section
variable {Cells M Smp Rec : Type} (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (DK : WholeD) {W : Type}
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) ((Fk X N P).XiPub × (Fk X N P).S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₂ 0) (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₃ (Fk X N P).lastChainFirstTreeNumber)
      (((Fk X N P).XiPub × (Fk X N P).S₁ × (Fk X N P).S₂) × (Fk X N P).S₃) W ds)
    (dW wEnd : W)
    (B : BaseSt Cells M Smp Rec) (at_ : Where) (R : KRead Cells M) (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ)
    (coll : Strs → Rec → Prop) (notBad : List OnBytes.E → Strs → Prop) (off₂ off₃ : ℕ → ℕ)

/-- **«gives» from the two halves.** -/
theorem gives_of_halves (dB : RDT) (dt : List RDT) (nl : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
    (tbl : (Xi × FirstState) × (fr₁ (DK.at frS.P.T.a)).E.Str → Wit Cells Unit M → M)
    (hbase : ∀ k ∈ pinned (open₁ (n₁ (oneAt X)) 15), (at_ k).1 < (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block (Xi × FirstState) Key.Claim) (k₁.map held) 15))
    (fwd : ∀ a b rs gs, (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) 15 a → (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))).decide a.1 rs gs = .ok b.1 →
      StrsStay (Fk X N P) at_ (open₁ (n₁ (oneAt X)) 15) (strsOf (fr₁ (DK.at frS.P.T.a)) a.2) (strsOf (fr₁ (DK.at frS.P.T.a)) b.2) → (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) 16 b)
    (back : ∀ a b rs gs t t' w, (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) 15 a → (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))).decide a.1 rs gs = .ok b.1 →
      StrsStay (Fk X N P) at_ (open₁ (n₁ (oneAt X)) 15) (strsOf (fr₁ (DK.at frS.P.T.a)) a.2) (strsOf (fr₁ (DK.at frS.P.T.a)) b.2) → (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) 16 b →
      enterAndAsk (enterRanges X.Y.k.oneTime) (rangesParams N) a.1.2 = .ok t → leaveRanges a.1.2 t' = .ok b.1.2 → b.1.1 = a.1.1 →
      QN (rangesParams N) (NTuple (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) (rangesParams N) (nuOf (rangesParams N) nl t) rad rd) (t, a.2) →
      R₁ (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R 16 b w → R₁ (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R 15 a (layAt at_ [1] (fun _ => tbl a w) w)) :
    ∀ a τ b, (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) 15 a →
      (pieceOf (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))) (cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block (Xi × FirstState) Key.Claim) (k₁.map held) 15) (dB :: dt) [] (rest₁ 15 (dB :: dt))).ior.red.out a τ = some b →
      (∃ t t', enterAndAsk (enterRanges X.Y.k.oneTime) (rangesParams N) a.1.2 = .ok t ∧
        (leaveRanges a.1.2 t' = .ok b.1.2 ∧ b.1.1 = a.1.1) ∧
        QN (rangesParams N) (NTuple (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) (rangesParams N) (nuOf (rangesParams N) nl t) rad rd) (t, a.2)) →
      (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) 16 b ∧ ((Cl₁ X N P (DK.at frS.P.T.a) B at_ R) 16 b → (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) 15 a) := by
  intro a τ b ha hout ⟨t, t', h1, ⟨h2, h3⟩, hq⟩
  have hd := piece_decides_at _ a τ b hout
  have Hy := strsStay_of_out (Fk X N P) (fr₁ (DK.at frS.P.T.a)) at_ _ (open₁ (n₁ (oneAt X)) 15) hbase a b τ hout
  have hb := fwd a b _ _ ha hd Hy
  exact ⟨hb, fun ⟨w, hw⟩ => ⟨_, back a b _ _ t t' w ha hd Hy hb h1 h2 h3 hq hw⟩⟩

end

end Johnson.RunOne.Law.K12AtThe21

#print axioms Johnson.RunOne.Law.K12AtThe21.gives_of_halves
