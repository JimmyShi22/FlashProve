-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12FwdFactsH.lean: ROW 1.15 OF THE KEY FILE's TABLES: THE PROMISE's HALF WITH THE HISTORY IN FRONT: gives_of_halvesH's premise «fwd» (K12Left15H.lean) FROM FOUR FACTS AT THE BLOCK's decide's YES AT A REACHED STATE. MADE BY A PROGRAM's SUBSTITUTION OUT OF K12FwdFacts.lean's fwd_of_facts: "Hist₁ … 15 a →" in front of hdec's yes and of the conclusion's. IT MOVES THE WEIGHT; IT PAYS NONE.
OBJECT. gives_of_halvesH's premise fwd. USER. Whoever fills Left15JG at OnH by the two halves.
LETTERS. The35.lean's.
Limits. hdec is shown of no block here. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12FwdFacts
import Johnson.RunOne.Law.K12Left15H

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
open VerifiableInference.Desc.K12
open Johnson.RunOne.Sound (bareB)
open Johnson.RunOne.KeyRows1 (n₁ R₁ open₁ plan₁ readers₁ book₁ slots₁ free₁ meaning₁At)
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

/-- **The promise's half of row 1.15 from four facts at decide's yes AT A REACHED STATE.** fwd_of_facts (K12FwdFacts.lean) with the history in front of the yes: its conclusion is gives_of_halvesH's premise fwd. -/
theorem fwd_of_factsH (hl : (lookupsOf X.Y.k.oneTime).length = 2)
    (hdec : ∀ a rs gs b, Hist₁ (Fk X N P) (DK.at frS.P.T.a) 15 a → (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))).decide a rs gs = .ok b →
      (readers₁ (oneAt X)).marked a.2 = (readers₁ (oneAt X)).marked b.2 ∧
      (shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) (n₁ (oneAt X)) (slots₁ (oneAt X)) 15 a.2 = true → ∀ y, free₁ (Fk X N P) B.h₁ at_ (oneAt X) R coll 15 a y → ∀ k ∈ pinned (open₁ (n₁ (oneAt X)) 16), B.h₁.smp a (at_ k).1 (at_ k).2 = B.h₁.smp b (at_ k).1 (at_ k).2) ∧
      (shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) (n₁ (oneAt X)) (slots₁ (oneAt X)) 15 a.2 = true → shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) (n₁ (oneAt X)) (slots₁ (oneAt X)) 16 b.2 = true) ∧
      (shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) (n₁ (oneAt X)) (slots₁ (oneAt X)) 15 a.2 = true → ∀ y y', StrsStay (Fk X N P) at_ (open₁ (n₁ (oneAt X)) 15) y y' → free₁ (Fk X N P) B.h₁ at_ (oneAt X) R coll 15 a y → free₁ (Fk X N P) B.h₁ at_ (oneAt X) R coll 16 b y')) :
    ∀ a b rs gs, (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) 15 a → Hist₁ (Fk X N P) (DK.at frS.P.T.a) 15 a.1 → (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))).decide a.1 rs gs = .ok b.1 →
      StrsStay (Fk X N P) at_ (open₁ (n₁ (oneAt X)) 15) (strsOf (fr₁ (DK.at frS.P.T.a)) a.2) (strsOf (fr₁ (DK.at frS.P.T.a)) b.2) → (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) 16 b := by
  intro a b rs gs ha hh hd Hy
  obtain ⟨h1, h2, h3, h4⟩ := hdec a.1 rs gs b.1 hh hd
  have hn : n₁ (oneAt X) = 2 := hl
  exact KeyQuietSub.onAt_fwd_sub (Fk X N P) B.h₁ at_ (meaning₁At (oneAt X) R) _ _ _ _ (open₁ (n₁ (oneAt X)) 15) (open₁ (n₁ (oneAt X)) 16)
    (by rw [hn]; exact pins_sub) a.1 b.1 _ _ (fun hu => h1.trans hu) (fun hs hf => h2 hs _ hf) Hy (fun hs => h4 hs _ _ Hy) h3 ha


end

end Johnson.RunOne.Law.K12AtThe21

#print axioms Johnson.RunOne.Law.K12AtThe21.fwd_of_factsH
