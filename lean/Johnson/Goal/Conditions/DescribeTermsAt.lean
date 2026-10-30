-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/DescribeTermsAt.lean: THE TEST FOR EMPTINESS OF
Johnson/Goal/Conditions/DescribeTerms.lean: at the slot of `G8_describeO`
(Johnson/PV/DescribeO.lean), with the written honest side (Johnson/Flat/CodingCells.lean), the laws
that opening-form binding still owes (`BindLaws`) are met together, under tests on numbers alone; so
the stored G9 holds there of the description with the terms laid in. Definitions, statements and
proofs. A slot, no member: g and H are letters.

Main names (namespace `VerifierAndGoals.Fit`).
  `decodes_of_eq`: the decoder's law at every honest side E that is `codingCells`, at every F and P
    (by substitution; `obj_decodes_index_full`).
  `termsO`: `HonestTerms` at the slot: T := `toldAtZ` (Johnson/PV/Describe.lean); φ := `phiO` at
    valid settings, none else; back := `backO` (Johnson/PV/DescribeBinds.lean) at valid settings,
    the matrix of a fixed index else. The coins' enumerations and algorithm, the provers and the
    randomness are letters.
  `slot_noCoin` … `slot_number`: the laws one by one.
  **`bindLaws_slotO`**: `BindLaws` at every Z that the reader reads, at tP := 8: the told law's six
    (`told_noCoin` … `told_code`, Johnson/PV/ToldMember.lean); the first of the wire's laws
    (`wiresOfFull`, Johnson/Flat/WiresAtSizes.lean); section (`section_backO`); decodes; total
    (`encTOf_total`); reading (`pub8_queries`, Johnson/Top/KeyTree.lean); number (the tree's depth
    is the code's a = 32 and the wiring has K + 1 blocks, both by definition; then arithmetic).
  **`G9_slotO_withTerms`**: the stored G9.

THE PREMISES, ALL. At every Z in scope: hE ((g Z).E is `codingCells`: an equation on a letter, met
by laying it so); hk wK dK wP dP (the five tests on numbers of `G8_describeO`); hK40 ((g Z).K + 2 <
2^40). Of the coins' algorithm, a letter: it asks at most q ≤ 2^40 queries (hq, hc).
NOT AMONG THEM: keySound, proofSound, the theorem on codes, meaning, carries, any law on a committer
or an extractor.

WHO READS EACH LETTER: as in Johnson/Goal/Conditions/DescribeTerms.lean. g: the verifier (all fields
but E's honest side and U's committer and prover); the committer (E; U's pol, KL, lay through the
public reading; the coding). H: its parse, the verifier; the rest is overwritten by `withTerms`.
NOTHING THAT THE VERIFIER READS STANDS UNDER "THERE IS".

Limits.
- `describeZO` lays an older coding of queries: IT IS NOT THE DESCRIPTION THAT RUNS.
- That a family g with hE and the tests on numbers exists is not shown.
- THE VERIFIER IS IDLE IN G9. THE COMMITTER IS TIED TO NO PROGRAM.
- `attribute [local irreducible] pub8`: without it Lean unfolds the public reading under `NoCoin`
  and `QueryBound` and ends in "maximum recursion depth". No limit is raised here; files beneath
  raise `maxRecDepth`.
- All limits of the files named above stand.
Terms: lean/GLOSSARY.md.

-/
import Johnson.PV.DescribeBinds
import Johnson.Goal.Conditions.DescribeTerms
import Johnson.Flat.CodingCells
import Johnson.Top.KeyTree

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open OnBytes.Maker.Page _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.K.Arm OnBytes.K.Arm.Pub OnBytes.K.Arm.ProofFront OnBytes.Tie
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open Inst.Model.Layout (kRef hRef)
open Inst.Model (ScalesAndPolicy Lawful)
open scoped ENNReal

/- The public reading is compared by its name: a statement that holds `NoCoin` or `QueryBound` of it
would else be unfolded along its eight queries. -/
attribute [local irreducible] pub8

/-- **The decoder's law at every honest side that is the written one.** -/
theorem decodes_of_eq (pp : ScalesAndPolicy) (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) numsRef pp))
    (hE : E = codingCells frS frZ 402653181 numsRef pp Subtype.val)
    (F : Files (DecR.configurationOfStoredTable (claimsReqAt (frS.toDecR frZ 402653181) numsRef pp) (relationsAndEncodingOfClaims _ E)))
    (P : F.Provers) (i : Cm.Idx) (r : (F.withProvers P).EncodingRandomness) (s : (F.withProvers P).OutOfDomainSeed) :
    (F.withProvers P).decodeIndex ((F.withProvers P).encodeIndex (Flat.matrixOf i) r) ((F.withProvers P).recOf (Flat.matrixOf i) r s) =
      some (Flat.matrixOf i) := by
  subst hE
  exact obj_decodes_index_full pp Subtype.val F P i r s

section AtPolicy
variable (g : (Z : PublicFiles) → FramePol numsRef (ppAtFiles Z.pol Z.KL))
  (H : SideZ fun Z => (g Z).toFrame)
  (ri : (Z : PublicFiles) → _root_.Iop.Enum ((slotO g H).input Z c₀ []).protocol.EncodingRandomness)
  (sl : PublicFiles → _root_.Iop.Enum (ℕ → Rom.Bits)) (b₀ : (Z : PublicFiles) → ((slotO g H).input Z c₀ []).LeafBody)
  (proveT : (Z : PublicFiles) → ((slotO g H).input Z c₀ []).Index × ((slotO g H).input Z c₀ []).protocol.EncodingRandomness ×
    (ℕ → Rom.Bits) → (l : List (((slotO g H).input Z c₀ []).Instance × Unit)) →
    Rom.OComp (rom 256) (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 ((slotO g H).input Z c₀ []).protocol
      ((slotO g H).input Z c₀ []).offlineRoundSplits ((slotO g H).input Z c₀ []).linkRoundSplits) l))
  (Rand : Type) (sample : RandomizedAlgorithm Rand)
  (coins : (Z : PublicFiles) → Rand →
    DeterministicAlgorithm (Fin (((slotO g H).input Z c₀ []).coinBound + 1)))
  (prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm H.Form)

/-- The honest side's terms at the slot. -/
def termsO : HonestTerms (slotO g H) where
  c₀ := fun _ => c₀
  m₀ := fun _ => []
  T := fun Z => toldAtZ (lettersAt (fun Z => (g Z).toFrame) H Z) Z
  φ := fun _ s M => if hv : settingsAreValid s = true then phiO hv M else none
  back := fun _ s w => if hv : settingsAreValid s = true then backO hv w
    else Flat.matrixOf (Cm.Idx.ofIndex Inst.Model.ScalesSanity.iZero)
  ri := ri
  sl := sl
  b₀ := b₀
  proveT := proveT
  Rand := Rand
  sample := sample
  coins := coins
  prove := prove

local notation "Qo" => termsO g H ri sl b₀ proveT Rand sample coins prove

theorem slot_noCoin (Z : PublicFiles) : ((Qo).T Z).Pub.NoCoin := told_noCoin (atZ (g Z).U Z)

theorem slot_asks (Z : PublicFiles) : ((Qo).T Z).Pub.AsksIn fun _ x => ((Qo).T Z).Pt x :=
  told_asks (atZ (g Z).U Z)

theorem slot_once (Z : PublicFiles) : NoRepeat ((Qo).T Z).Pub := told_once (atZ (g Z).U Z)

theorem slot_spare (Z : PublicFiles) : ∀ d x, ((Qo).T Z).Pt x → IsOther (((Qo).T Z).m d) x :=
  told_spare (atZ (g Z).U Z)

theorem slot_word (Z : PublicFiles) : ∀ d d', ((Qo).T Z).part d = ((Qo).T Z).part d' →
    (extractorOverOneHashFunction (((Qo).T Z).m d) (indexExtractorAtRootAndOutOfDomainSample ((slotO g H).input Z c₀ []).queryLayout)).Ei =
      (extractorOverOneHashFunction (((Qo).T Z).m d') (indexExtractorAtRootAndOutOfDomainSample ((slotO g H).input Z c₀ []).queryLayout)).Ei :=
  told_word (atZ (g Z).U Z)

theorem slot_code (Z : PublicFiles) : ZKCP.CodeIsOneToOne ((Qo).T Z).encT := told_code (atZ (g Z).U Z)

theorem slot_wire (Z : PublicFiles) (hk : kThree .two (g Z).DK frRds (g Z).DP ≤ (g Z).K)
    (wK : (g Z).DK.workFit = true) (dK : (g Z).DK.depthFit = true)
    (wP : (g Z).DP.workFit = true) (dP : (g Z).DP.depthFit = true) :
    ((slotO g H).input Z c₀ []).queryLayout.OKG :=
  (wiresOfFull _ (relationsAndEncodingOfClaims _ (g Z).E) (g Z).DK (g Z).DP (g Z).runK (g Z).runP
    (g Z).rK (g Z).rP (g Z).depthReq (g Z).early (g Z).salt (g Z).P (g Z).K
    (g Z).T₀.depthReqT hk wK dK wP dP).1

theorem slot_section (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (w : ModelWeights (settingsOfRead pp)) :
    (Qo).φ Z (settingsOfRead pp) ((Qo).back Z (settingsOfRead pp) w) = some w := by
  show (if hv : settingsAreValid (settingsOfRead pp) = true then
    phiO hv (if hv' : settingsAreValid (settingsOfRead pp) = true then backO hv' w
      else Flat.matrixOf (Cm.Idx.ofIndex Inst.Model.ScalesSanity.iZero)) else none) = some w
  rw [dif_pos (valid_of_read hr), dif_pos (valid_of_read hr)]
  exact section_backO (valid_of_read hr) w

theorem slot_back (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (w : ModelWeights (settingsOfRead pp)) :
    (Qo).back Z (settingsOfRead pp) w = Flat.matrixOf (indexOfWeights (valid_of_read hr) w) :=
  dif_pos (valid_of_read hr)

theorem slot_decodes (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (hE : (g Z).E = codingCells frS frZ 402653181 numsRef (ppAtFiles Z.pol Z.KL) Subtype.val)
    (w : ModelWeights (settingsOfRead pp)) (r : ((slotO g H).input Z c₀ []).protocol.EncodingRandomness)
    (sd : ((slotO g H).input Z c₀ []).protocol.OutOfDomainSeed) :
    ((slotO g H).input Z c₀ []).protocol.decodeIndex
      (((slotO g H).input Z c₀ []).protocol.encodeIndex ((Qo).back Z (settingsOfRead pp) w) r)
      (((slotO g H).input Z c₀ []).protocol.recOf ((Qo).back Z (settingsOfRead pp) w) r sd) =
      some ((Qo).back Z (settingsOfRead pp) w) := by
  rw [slot_back g H ri sl b₀ proveT Rand sample coins prove Z pp hr w]
  exact decodes_of_eq (ppAtFiles Z.pol Z.KL) (g Z).E hE _ (g Z).P _ r sd

theorem slot_total (Z : PublicFiles) : ∀ key, ((Qo).T Z).encT key ≠ none := encTOf_total (g Z).T₀

theorem slot_reading (Z : PublicFiles) : ((Qo).T Z).Pub.QueryBound 8 :=
  pub8_queries recordGround Z.pol Z.KL Z.lay

theorem slot_depth (Z : PublicFiles) : ((slotO g H).input Z c₀ []).queryLayout.depth = frS.P.T.a := rfl

theorem slot_K (Z : PublicFiles) : ((slotO g H).input Z c₀ []).queryLayout.K = (g Z).K + 1 := rfl

theorem slot_number (Z : PublicFiles) (hK40 : (g Z).K + 1 + 1 < 2 ^ 40) (q : ℕ) (hq : q ≤ 2 ^ 40) :
    q + ((Qo).tCommit Z 8 + 1) ≤ honestBudget := by
  have ha : frS.P.T.a = 32 := by decide
  show q + (8 + (2 * 2 ^ ((slotO g H).input Z c₀ []).queryLayout.depth +
    2 * (((slotO g H).input Z c₀ []).queryLayout.K + 1)) + 1) ≤ 2 ^ 48
  rw [slot_depth, slot_K, ha]
  have h1 : (2 : ℕ) ^ 32 = 4294967296 := by norm_num
  have h2 : (2 : ℕ) ^ 40 = 1099511627776 := by norm_num
  have h3 : (2 : ℕ) ^ 48 = 281474976710656 := by norm_num
  rw [h1, h3]
  rw [h2] at hK40 hq
  omega

/-- **THE LAWS THAT OPENING-FORM BINDING STILL OWES ARE MET TOGETHER AT THE SLOT.** -/
theorem bindLaws_slotO (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (hE : (g Z).E = codingCells frS frZ 402653181 numsRef (ppAtFiles Z.pol Z.KL) Subtype.val)
    (hk : kThree .two (g Z).DK frRds (g Z).DP ≤ (g Z).K) (wK : (g Z).DK.workFit = true)
    (dK : (g Z).DK.depthFit = true) (wP : (g Z).DP.workFit = true)
    (dP : (g Z).DP.depthFit = true) (hK40 : (g Z).K + 1 + 1 < 2 ^ 40) (q : ℕ) (hq : q ≤ 2 ^ 40)
    (hc : ∀ ρ, (coins Z ρ).toRandomized.QueryBound q) :
    BindLaws (Qo) Z (settingsOfRead pp) 8 q where
  noCoin := slot_noCoin g H ri sl b₀ proveT Rand sample coins prove Z
  asks := slot_asks g H ri sl b₀ proveT Rand sample coins prove Z
  once := slot_once g H ri sl b₀ proveT Rand sample coins prove Z
  spare := slot_spare g H ri sl b₀ proveT Rand sample coins prove Z
  word := slot_word g H ri sl b₀ proveT Rand sample coins prove Z
  code := slot_code g H ri sl b₀ proveT Rand sample coins prove Z
  wire := slot_wire g H Z hk wK dK wP dP
  section_ := slot_section g H ri sl b₀ proveT Rand sample coins prove Z pp hr
  decodes := slot_decodes g H ri sl b₀ proveT Rand sample coins prove Z pp hr hE
  total := slot_total g H ri sl b₀ proveT Rand sample coins prove Z
  reading := slot_reading g H ri sl b₀ proveT Rand sample coins prove Z
  coinsWithin := hc
  number := slot_number g H ri sl b₀ proveT Rand sample coins prove Z hK40 q hq

/-- **THE STORED G9 AT THE SLOT WITH THE TERMS LAID IN: UNDER TESTS ON NUMBERS AND hE ALONE.** -/
theorem G9_slotO_withTerms
    (hE : ∀ Z, InScope Z = true →
      (g Z).E = codingCells frS frZ 402653181 numsRef (ppAtFiles Z.pol Z.KL) Subtype.val)
    (hk : ∀ Z, InScope Z = true → kThree .two (g Z).DK frRds (g Z).DP ≤ (g Z).K)
    (wK : ∀ Z, InScope Z = true → (g Z).DK.workFit = true)
    (dK : ∀ Z, InScope Z = true → (g Z).DK.depthFit = true)
    (wP : ∀ Z, InScope Z = true → (g Z).DP.workFit = true)
    (dP : ∀ Z, InScope Z = true → (g Z).DP.depthFit = true)
    (hK40 : ∀ Z, InScope Z = true → (g Z).K + 1 + 1 < 2 ^ 40) (q : ℕ) (hq : q ≤ 2 ^ 40)
    (hc : ∀ Z ρ, (coins Z ρ).toRandomized.QueryBound q) :
    G9 fun _ => (slotO g H).withTerms (termsO g H ri sl b₀ proveT Rand sample coins prove) :=
  G9_withTerms (fun _ => slotO g H)
    (fun _ => termsO g H ri sl b₀ proveT Rand sample coins prove) 8 q
    (le_trans hq (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
    fun Z pp h₁ h₂ => bindLaws_slotO g H ri sl b₀ proveT Rand sample coins prove Z pp h₂ (hE Z h₁)
      (hk Z h₁) (wK Z h₁) (dK Z h₁) (wP Z h₁) (dP Z h₁) (hK40 Z h₁) q hq (hc Z)

end AtPolicy

end VerifierAndGoals.Fit

#print axioms VerifierAndGoals.Fit.decodes_of_eq
#print axioms VerifierAndGoals.Fit.bindLaws_slotO
#print axioms VerifierAndGoals.Fit.G9_slotO_withTerms
