-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Face/UndoOfFitsAt.lean: UndoOnBut (Johnson/Face/UndoOfFits.lean) at the description of the
byte format, wherever each accepted typed proof that the honest side makes Fits.
-/
import Johnson.Face.UndoOfFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Face

open Rom
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Prover OnBytes.WholeKey OnBytes.PublicAt OnBytes.FrontRoad
open VerifiableInference VerifiableInference.OnPublicFiles ZKCP.PublicRead
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

open VerifierAndGoals FlashProve
open Johnson.Prover.Print
open _root_.Run (digToBytes)


variable (S : (Z : PublicFiles) → DescriptionDataAtFiles (asDescriptionFiles Z)) (f₀ : DecodedProof) (Hb : CommitterAndProver FormBytes)
  (c₀ : Digest) (m₀ : List (Dig 256)) (Z : PublicFiles)

/-- the told record at Z -/
local notation "𝔗" => DescriptionDataAtFiles.layoutsByPublicReading (S Z) c₀ m₀
/-- its ground input -/
local notation "ℜ" => R (S Z) c₀ m₀

/-- **At all coins that can be drawn**: where the compiled verifier says yes to what the committer
and the prover return under the hash function, and these are not excepted, they are the parts of a
typed proof with no further token that Fits at the bytes of the digest that the public reading
returns. -/
def FitsAtCoins (h : (𝔗).D → HonestSide 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits)
    (Tr : (ℜ).Index → (ℜ).Instance → Prop) (Bad : FullKey 256 (ℜ).protocol (ℜ).offlineRoundSplits (ℜ).linkRoundSplits → RequestProof 256 (ℜ).protocol → Prop) : Prop
      :=
  ∀ (f : ZKCP.Oracle 256) (i : (ℜ).Index) (x : (ℜ).Instance), Tr i x →
    ∀ (c : DrawC 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits (h (readAt (𝔗) f)).KT (h (readAt (𝔗) f)).KL),
    DrawCOf (h (readAt (𝔗) f)) c →
    ∀ dP : DrawP 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits (h (readAt (𝔗) f)).KB,
    DrawPOf (h (readAt (𝔗) f)) dP →
    (verifyW (ℜ).queryLayout ((𝔗).Sd (readAt (𝔗) f)) ((𝔗).cA (readAt (𝔗) f)) (ℜ).fixedSample (ℜ).compilerParameters
      ((commitAt (ℜ).queryLayout ((𝔗).Sd (readAt (𝔗) f)) ((𝔗).cA (readAt (𝔗) f)) (h (readAt (𝔗) f)) i c).det
        (oraclesAt (𝔗) f (readAt (𝔗) f))).1 x
      ((proveAt (ℜ).queryLayout ((𝔗).cA (readAt (𝔗) f)) (ℜ).fixedSample (h (readAt (𝔗) f))
        ((commitAt (ℜ).queryLayout ((𝔗).Sd (readAt (𝔗) f)) ((𝔗).cA (readAt (𝔗) f)) (h (readAt (𝔗) f)) i
          c).det (oraclesAt (𝔗) f (readAt (𝔗) f))).2 x dP).det
        (oraclesAt (𝔗) f (readAt (𝔗) f)))).det (oraclesAt (𝔗) f (readAt (𝔗) f)) = true →
    ¬ Bad ((commitAt (ℜ).queryLayout ((𝔗).Sd (readAt (𝔗) f)) ((𝔗).cA (readAt (𝔗) f)) (h (readAt (𝔗) f)) i
        c).det (oraclesAt (𝔗) f (readAt (𝔗) f))).1
      ((proveAt (ℜ).queryLayout ((𝔗).cA (readAt (𝔗) f)) (ℜ).fixedSample (h (readAt (𝔗) f))
        ((commitAt (ℜ).queryLayout ((𝔗).Sd (readAt (𝔗) f)) ((𝔗).cA (readAt (𝔗) f)) (h (readAt (𝔗) f)) i
          c).det (oraclesAt (𝔗) f (readAt (𝔗) f))).2 x dP).det
        (oraclesAt (𝔗) f (readAt (𝔗) f))) →
    ∃ q : Johnson.Prover.Print.Typed (S Z), q.aux = [] ∧
      lowKey ((commitAt (ℜ).queryLayout ((𝔗).Sd (readAt (𝔗) f)) ((𝔗).cA (readAt (𝔗) f)) (h (readAt (𝔗) f)) i
        c).det (oraclesAt (𝔗) f (readAt (𝔗) f))).1 = ⟨q.cm, q.rcd⟩ ∧
      lowPrf ((commitAt (ℜ).queryLayout ((𝔗).Sd (readAt (𝔗) f)) ((𝔗).cA (readAt (𝔗) f)) (h (readAt (𝔗) f)) i
        c).det (oraclesAt (𝔗) f (readAt (𝔗) f))).1
        ((proveAt (ℜ).queryLayout ((𝔗).cA (readAt (𝔗) f)) (ℜ).fixedSample (h (readAt (𝔗) f))
          ((commitAt (ℜ).queryLayout ((𝔗).Sd (readAt (𝔗) f)) ((𝔗).cA (readAt (𝔗) f)) (h (readAt (𝔗) f)) i
            c).det (oraclesAt (𝔗) f (readAt (𝔗) f))).2 x dP).det
          (oraclesAt (𝔗) f (readAt (𝔗) f))) =
        ⟨q.copy, some q.piT, (q.cm', q.rcd', some q.piL), some q.piB⟩ ∧
      Fits (S Z) (digToBytes (cAt Z f)) q

/-- The parser at a form that the decoder takes. -/
theorem parse_at (hash : Hash) (prompt output : List Token) (B : FormBytes) (f : DecodedProof)
    (hdec : decodeD (digToBytes (cAt Z hash)) B = some f) :
    proofAt ((descriptionOnBytes S f₀ Hb).parse Z) prompt output B hash =
      (S Z).typedOf (digToBytes (cAt Z hash)) f := by
  show (S Z).typedOf (digToBytes (cAt Z hash))
    ((decodeD (digToBytes (cAt Z hash)) B).getD f₀) = _
  rw [hdec]
  rfl

set_option maxRecDepth 200000 in
/-- The byte format's parser at what the writer lays of a typed proof that Fits. -/
theorem parse_writer
    (encF : VerifierAndGoals.TypedProof ((descriptionOnBytes S f₀ Hb).F Z) ((descriptionOnBytes S f₀ Hb).P Z) → FormBytes)
    (hS : PublicS (S Z))
    (hW : ∀ q : Johnson.Prover.Print.Typed (S Z), q.aux = [] →
      encF ([], (⟨q.cm, q.rcd⟩, ⟨q.copy, some q.piT, (q.cm', q.rcd', some q.piL), some q.piB⟩)) =
        formOf (S Z) q)
    (q : Johnson.Prover.Print.Typed (S Z)) (e0 : q.aux = [])
    {f : ZKCP.Oracle 256} (hq : Fits (S Z) (digToBytes (cAt Z f)) q)
    (A : KeyRoot 256 (ℜ).protocol) (B : OfflineLinkOnlineProof 256 (ℜ).protocol (ℜ).offlineRoundSplits (ℜ).linkRoundSplits)
    (eA : A = ⟨q.cm, q.rcd⟩)
    (eB : B = ⟨q.copy, some q.piT, (q.cm', q.rcd', some q.piL), some q.piB⟩)
    (x' : List Token × List Token) (f' : ZKCP.Oracle 256) (hf : f' = f) :
    (((descriptionOnBytes S f₀ Hb).parse Z) x'.1 x'.2 (encF ([], (A, B)))).evaluate f' = ([], (A, B)) := by
  subst hf
  obtain ⟨f₁, hd, hp⟩ := decodeD_formOf (S Z) (digToBytes (cAt Z f')) q hS hq
  have hw : encF ([], (A, B)) = formOf (S Z) q := by
    subst eA eB
    exact hW q e0
  have h2 := parse_at S f₀ Hb Z f' x'.1 x'.2 (formOf (S Z) q) f₁ hd
  have h3 : (S Z).typedOf (digToBytes (cAt Z f')) f₁ =
      (([], A, B) : (S Z).Typed) := by
    unfold DescriptionDataAtFiles.typedOf
    rw [hp, e0]
    subst eA eB
    rfl
  rw [hw]
  exact h2.trans h3

set_option maxRecDepth 200000 in
set_option maxHeartbeats 2000000 in
/-- **THE PARSER UNDOES THE WRITER on what the honest side makes**, at the byte format's own parser,
for every relation Tr. -/
theorem undoOn_of_fitsAt (h : (𝔗).D → HonestSide 256 (ℜ).protocol (ℜ).LeafBody (ℜ).offlineRoundSplits (ℜ).linkRoundSplits) {J : Type}
    (idx : J → (ℜ).Index) (Tr : (ℜ).Index → (ℜ).Instance → Prop)
    (Bad : FullKey 256 (ℜ).protocol (ℜ).offlineRoundSplits (ℜ).linkRoundSplits → RequestProof 256 (ℜ).protocol → Prop)
    (encF : VerifierAndGoals.TypedProof ((descriptionOnBytes S f₀ Hb).F Z) ((descriptionOnBytes S f₀ Hb).P Z) → FormBytes)
    (hS : PublicS (S Z)) (hF : FitsAtCoins S c₀ m₀ Z h Tr Bad)
    (hW : ∀ q : Johnson.Prover.Print.Typed (S Z), q.aux = [] →
      encF ([], (⟨q.cm, q.rcd⟩, ⟨q.copy, some q.piT, (q.cm', q.rcd', some q.piL), some q.piB⟩)) =
        formOf (S Z) q) :
    UndoOnBut (descriptionOnBytes S f₀ Hb) Z c₀ m₀ (layoutsByPublicReadingAtDescriptionOfFields S (committerAndProverWithParser S Hb decodeD f₀) c₀ m₀ Z) h idx Tr
      ((descriptionOnBytes S f₀ Hb).parse Z) encF Bad := by
  refine undoOnBut_of_coins (descriptionOnBytes S f₀ Hb) Z c₀ m₀
    (layoutsByPublicReadingAtDescriptionOfFields S (committerAndProverWithParser S Hb decodeD f₀) c₀ m₀ Z) h idx Tr ((descriptionOnBytes S f₀ Hb).parse Z) encF
      Bad
    (layoutsByPublicReading_noCoin (S Z) c₀ m₀) ?_
  intro f i x hTr c hc dP hdP hy hBad x'
  obtain ⟨q, e0, e1, e2, hq⟩ := hF f i x hTr c hc dP hdP hy hBad
  exact parse_writer S f₀ Hb c₀ m₀ Z encF hS hW q e0 hq _ _ e1 e2 x' f rfl

end Johnson.Face

#print axioms Johnson.Face.parse_writer
#print axioms Johnson.Face.undoOn_of_fitsAt
