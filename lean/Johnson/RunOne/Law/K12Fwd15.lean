-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Fwd15.lean: ROW 1.15 OF THE KEY FILE's TABLES: THE PROMISE's HALF, JOINED: gives_of_halvesH's premise «fwd» (K12Left15H.lean) FROM SIX PUBLIC PREMISES. One statement; its proof is one call of fwd_of_factsH (K12FwdFactsH.lean) fed with four facts at the block's yes (K12Facts15.lean: marked_15 · smp_15 · shape_15 · free_15). GENERAL IN THE TABLES' LETTERS B · at_ · R · coll: no filling is named.
OBJECT. gives_of_halvesH's premise fwd. USER. Whoever fills the structure Left15JG at OnH by the two halves.
LETTERS. The35.lean's.
THE SIX PREMISES, AND WHOSE EACH IS: hpl: the description's test on the plan · hft: the maker's literal 0 for the place's first tree (a caller has it from "N is the maker's": K12Facts15A.lean's numbers_parts) · hl: two lookups · hSm · horc: on the tables' letter B (at the tables' files' filling horc is rfl) · hcoll: on the tables' letter coll.
THE HISTORY IS NOT SPENT BY THIS HALF: it stands in the statement because the premise fwd has it.
Limits. It pays no field: «gives» wants «back» and hbase beside it. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Law.K12FwdFactsH
import Johnson.RunOne.Law.K12Facts15

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

/-- **The promise's half of row 1.15.** -/
theorem fwd_15 (hpl : (descriptionFromSource X N P).planOk = true) (hft : N.nums.firstTree = 0) (hl : (lookupsOf X.Y.k.oneTime).length = 2)
    (hSm : B.SmOnly) (horc : B.orc₁ = (plan₁ (oneAt X)).orc)
    (hcoll : ∀ (y y' : Strs) (r : Rec), y'.cell = y.cell → coll y' r → coll y r) :
    ∀ a b rs gs, (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) 15 a → Hist₁ (Fk X N P) (DK.at frS.P.T.a) 15 a.1 → (held (bareB (rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N : Block FirstState Key.Claim))).decide a.1 rs gs = .ok b.1 →
      StrsStay (Fk X N P) at_ (open₁ (n₁ (oneAt X)) 15) (strsOf (fr₁ (DK.at frS.P.T.a)) a.2) (strsOf (fr₁ (DK.at frS.P.T.a)) b.2) → (On₁ X N P (DK.at frS.P.T.a) B at_ R coll) 16 b :=
  fwd_of_factsH X N P DK B at_ R coll hl fun a rs gs b _ hd =>
    ⟨K12Facts15.marked_15 X a b,
      fun h15 _ hf => K12Facts15.smp_15 X N B at_ hSm horc hf.2.1.1 a b rs gs hd h15,
      K12Facts15.shape_15 X N P hpl hft a b rs gs hd,
      fun h15 => K12Facts15.free_15 X N P B at_ R coll hpl hcoll a b rs gs hd h15⟩

end

end Johnson.RunOne.Law.K12AtThe21

#print axioms Johnson.RunOne.Law.K12AtThe21.fwd_15
