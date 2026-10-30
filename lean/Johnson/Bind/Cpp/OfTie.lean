-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/OfTie.lean: WHAT FOLLOWS, BY CALLS ALONE, FROM THE TIE AND THE COUNT
(Johnson/Bind/Cpp/Defs.lean): the goals' own statements on soundness under the files' policy and on
binding, of the description theCpp T prove, whose commit field is Letters.commitAt at a letter T.
Statements and proofs. TieAt IS A HYPOTHESIS HERE; at theTwin g, where the frame's salts have 40
bytes, it is tieAt (Johnson/Bind/Cpp/TheTie.lean).
NOTHING HERE SAYS THAT A COMMITMENT OF THE RELEASE'S COMMITTING PROGRAM CAN BE OPENED ONLY TO THE
EXTRACTOR'S WEIGHTS, OR THAT THE EXTRACTOR GIVES THE WEIGHTS THAT THE PROGRAM COMMITTED TO.
"Binding" in this file is the opening form, BindsWith (VerifiableInference/MoreStatements.lean):
nobody opens a commitment, by naming weights and randomness from which the committer gives it, to
weights that the extractor does not give; at fixed randomness it yields that the extractor gives the
committed weights back (BindsWith.atRandomness). It is not the index binding of ZKCP/Defs.lean's
HasIndexBinding: the half on soundness has that form, for the claim "meets the policy" (the tie is
typed at exact match: sound_iff, VerifiableInference/Agreement.lean), and speaks of every
commitment, whoever made it.

Main names.
  General in the description (namespace VerifierAndGoals.Fit): verify_withHonest, extractor_withHonest,
    parse_withHonest, commit_withHonest (by definition); verifierWithin_withHonest;
    soundUnderPolicyAt_withHonest: soundness under the files' policy does not feel the honest side.
  Namespace Bind.Cpp:
  commit_is: THE COMMIT FIELD IS Letters.commitAt AT THE FULL SIZE's SHAPE: by definition.
  tieAt_of_cells: the tie from its core and the digits' text.
  cpp_is_of_verify: theCpp has the verifier and the extractor of the description of the theorem on
    soundness. extractor_D₀.
  **g8bits_cpp**: G8bits (Ladder/Bits.lean) of theCpp: NO HYPOTHESIS.
  bindsWith_of_tieAt: binding at one Z at 3 (t + 2 + 2 · 2^48 + 2)² / 2^256, from the tie there.
  **bindsAtZ_cpp**: THE BODY OF G9bits AT ONE Z: from "read", the tie and the count at Z.
  policy_and_binding_at_zGap_cpp, binds_at_zFull_cpp: at the goals' two named sets of public files.
  both: one experiment, one extractor: the opener names a seed, or coins, or any member of the
    written committer's coins at Z.
  g9bits_cpp: G9bits of theCpp, UNDER SaltInScope, WHICH IS NOT PROVED: it says that the planner
    returns at all files in scope that are read (saltInScope_iff, Johnson/Bind/Cpp/SaltAt.lean). If
    it were false, so would this goal be at theCpp (theTwin g) (argued, no theorem: at files in
    scope that the planner rejects, the extractor reads leaves with salts of no bytes and finds none
    of that committer's). NO TABLE MAY COUNT THIS AS G9bits OF theCpp. WHAT IS OFFERED ARE THE FORMS
    AT ONE Z.
The road of the error: bindsWith_plain_law (Johnson/Goal/Conditions/BindsTold.lean) at
epsBind honestBudget; BindsWith.ofCommit (Ladder/FitBinds.lean) with an algorithm that asks at most
2 queries (the files' digest; at a seed the coin key's digest); bindsWith_bits_of_square
(Johnson/Goal/HonestSideFree.lean). In numbers: the square form is about 2^-156 at t = 0 and 2^-126
at t = 2^64; bindingErrorInQueries is about 2^-101 and 2^-60: 124 bits per hash query, never below about
2^-101.
Limits. Those of Defs.lean and of the files that are called.
withHonest turns four fields: Rand, sample, commit, prove. The field P (the honest provers of the
three protocols, round by round: silent ones at descriptionOfDataOnBytes flashProveData), on which the types of keys and
proofs hang, stays D's, and so do Shown, shown, Form and parse. So a prover from weights to a
proof's bytes can be laid in; a description with other provers in P, another form or another parser
is not reached.
T IS A LETTER: its id may be any algorithm. With T a letter the tie is met by the written committer
itself, read off the table (tie_has_member, Johnson/Bind/Cpp/Vapid.lean): then these theorems say of
it what Johnson/Goal/Conditions/BindsTold.lean says already. The content is at T := theTwin g
(Johnson/Bind/Cpp/AtTwin.lean): theTwin g meets TieAt wherever the frame's salts have 40 bytes
(tieAt, Johnson/Bind/Cpp/TheTie.lean); THAT THEY HAVE 40 BYTES AT ANY Z IS NO THEOREM OF THE MAIN
LIBRARY.
THE VERIFIER IS IDLE in every statement on binding: nothing says that verify accepts a proof under a
commitment of this committer's make.
Only commitments that this committer makes are spoken of. The public files are fixed before the hash
function is sampled. descriptionOfDataOnBytes flashProveData names the format's second hash function: no row on G7' or
G7'bits may be counted at theCpp. Nothing on completeness or index privacy; nothing on any program.
Terms: lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Bind.Cpp.Defs
import Johnson.Goal.HonestSideFree
import Johnson.Goal.SameExtractorWide
import Johnson.Goal.Files.FilesReadProof
import Ladder.FitBindsBits
import Ladder.PackageTies

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

open scoped ENNReal

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles

variable {D : Description} (H : HonestSide D.Form)

theorem verify_withHonest (Z : PublicFiles) {Form : Type} (parse : Parser D Z Form) :
    verify (D.withHonest H) Z parse = verify D Z parse :=
  verify_honestSide D H.Rand H.sample H.commit H.prove Z parse

theorem extractor_withHonest : (D.withHonest H).extractor = D.extractor :=
  extractor_honestSide D H.Rand H.sample H.commit H.prove

theorem parse_withHonest : (D.withHonest H).parse = D.parse := rfl

theorem commit_withHonest : (D.withHonest H).commit = H.commit := rfl

theorem verifierWithin_withHonest (h : VerifierWithin D) : VerifierWithin (D.withHonest H) :=
  (verifierWithin_honestSide D H.Rand H.sample H.commit H.prove).2 h

/-- **Soundness under the files' policy does not feel the honest side**:
soundUnderPolicyAt_honestSide (Johnson/Goal/HonestSideFree.lean) at the four fields of H. -/
theorem soundUnderPolicyAt_withHonest (eps : ℕ → ℕ → ℝ≥0∞) (sound : SoundUnderPolicyAt D eps) :
    SoundUnderPolicyAt (D.withHonest H) eps :=
  soundUnderPolicyAt_honestSide D H.Rand H.sample H.commit H.prove (firstResult H.sample) eps sound

end VerifierAndGoals.Fit

noncomputable section

namespace Bind.Cpp
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.Flat OnBytes.Slice
open Bind.Twin (Shape Table)

variable (T : Letters)
  (prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm flashProveDescription.Form)

/-- **The commit field is Letters.commitAt at the full size's shape**, by definition. -/
theorem commit_is (o : SecondHashFunctionType) (Z : PublicFiles) (s : IntegerTransformer.Settings) (w : ModelWeights s)
    (ρ : Rand) : (theCpp T prove o).commit Z s w ρ = T.commitAt shapeFull Z (entryOf s w) ρ := rfl

/-- The tie from its core and the digits' text. -/
theorem tieAt_of_cells (Z : PublicFiles) (hE : EntryIs) (h : TieCellsAt T Z) : TieAt T Z :=
  fun s w x b hash => by
    rw [hE Z s w]
    exact h (backThe Z s w) x b hash

/- From here on Lean compares these by their names. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF riDigits fieldRows
  FlashProve.thePlan FlashProve.theItem

/-- The extractor of descriptionOfDataOnBytes flashProveData is the told structure's named one. (The like is said of
atSecondHashFunction theDescription by extractor_atOlder, Johnson/Goal/Conditions/BindsAtSecondHashFunction.lean, at the
description that reads its argument.) -/
theorem extractor_D₀ (Z : PublicFiles) (s : IntegerTransformer.Settings) :
    flashProveDescription.extractor Z s = (T₀ Z).extractorOn (phiThe Z s) := by
  have h := congrFun (congrFun
    (VerifierAndGoals.AtTheName.same_extractor_bound placeHolderNumberCoins OnBytes.secondHashFunction) Z) s
  rw [VerifierAndGoals.AtTheName.the_description_is] at h
  have e1 : (theBound placeHolderNumberCoins OnBytes.secondHashFunction).extractor Z s =
      fun commitment queryLog =>
        (((theTerms placeHolderNumberCoins).T Z).extractor commitment queryLog).bind
          ((theTerms placeHolderNumberCoins).φ Z s) := rfl
  rw [← h, e1, LayoutsByPublicReading.extractorOn_eq]
  rfl

/- And these. -/
attribute [local irreducible] descriptionOfDataOnBytes T₀ LayoutsByPublicReading.commitAtCoins

/-- **theCpp has the verifier and the extractor of the description of the theorem on soundness.** -/
theorem cpp_is_of_verify (o : SecondHashFunctionType) :
    atSecondHashFunction theDescription = flashProveDescription ∧
      (∀ (Z : PublicFiles) (Form : Type) (parse : Parser flashProveDescription Z Form),
        verify (theCpp T prove o) Z parse = verify flashProveDescription Z parse) ∧
      (theCpp T prove o).extractor = (atSecondHashFunction theDescription).extractor :=
  ⟨VerifierAndGoals.AtTheName.the_description_is, fun _ _ _ => rfl,
    VerifierAndGoals.AtTheName.the_description_is ▸ rfl⟩

/-- **G8bits: NO HYPOTHESIS.** Carried from the theorem of the name itself. -/
theorem g8bits_cpp : G8bits (theCpp T prove) := by
  have h := VerifierAndGoals.AtTheName.g8bits_of_verify
  unfold G8bits at h
  rw [VerifierAndGoals.AtTheName.the_description_is] at h
  exact ⟨verifierWithin_withHonest (cppSide T prove) h.1,
    soundUnderPolicyAt_withHonest (cppSide T prove) soundnessErrorInQueries h.2⟩

theorem coinsAlg_within (Z : PublicFiles) (ρ : Rand) :
    (coinsAlg T Z ρ).toRandomized.QueryBound 2 := by
  cases ρ with
  | inl seed => exact fun _ _ => trivial
  | inr x => exact fun _ => trivial

/-- The committer's own count. -/
theorem commit_count (Z : PublicFiles) (cnt : CountAt T Z) (s : IntegerTransformer.Settings)
    (w : ModelWeights s) (ρ : Rand) :
    (cppCommit T Z s w ρ).toRandomized.QueryBound (twinBudget + 2) := by
  cases ρ with
  | inl seed => exact fun c I => cnt _
  | inr x => exact queryBound_mono_det _ _ _ (Nat.le_add_right _ 2) (cnt _)

/-- It is within the honest side's budget. -/
theorem commit_within (Z : PublicFiles) (cnt : CountAt T Z) (s : IntegerTransformer.Settings)
    (w : ModelWeights s) (ρ : Rand) :
    (cppCommit T Z s w ρ).toRandomized.QueryBound honestBudget :=
  queryBound_mono_det _ _ _ (by unfold twinBudget honestBudget; norm_num)
    (commit_count T Z cnt s w ρ)

/-- The fold of "then some" behind the named extractor. -/
theorem extractor_fold (Z : PublicFiles) (s : IntegerTransformer.Settings) :
    (fun commitment queryLog =>
      ((T₀ Z).extractorOn (phiThe Z s) commitment queryLog).bind some) = flashProveDescription.extractor Z s := by
  funext commitment queryLog
  rw [extractor_D₀]
  cases (T₀ Z).extractorOn (phiThe Z s) commitment queryLog <;> rfl

/-- **BINDING AT ONE Z, FROM THE TIE THERE, at the square form**: the written committer's law at two
queries more: 3 (t + 2 + 2 · 2^48 + 2)² / 2^256. -/
theorem bindsWith_of_tieAt (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (tie : TieAt T Z) :
    BindsWith (systemOfRecord (atSecondHashFunction (theCpp T prove)) Z (settingsOfRead pp))
      ((atSecondHashFunction (theCpp T prove)).extractor Z (settingsOfRead pp))
      fun t => epsBind honestBudget (t + 2) := by
  have h0 := bindsWith_plain_law Z pp hr (placeHolderNumberCoins.b₀ Z)
    (.done (coins₀_nonempty Z).some)
    (fun w _ p o => prove Z (settingsOfRead pp) w (.inl 0) p o)
  have h1 := BindsWith.ofCommit _ (systemOfRecord (atSecondHashFunction (theCpp T prove)) Z (settingsOfRead pp))
    _ _ h0 some id (coinsAlg T Z) 2 (coinsAlg_within T Z) (fun _ => rfl)
    (fun w ρ hash => by
      cases ρ with
      | inl seed => exact (tie (settingsOfRead pp) w _ _ hash).symm
      | inr x => exact (tie (settingsOfRead pp) w x _ hash).symm)
  exact (extractor_fold Z (settingsOfRead pp)) ▸ h1

/-- **THE BODY OF G9bits AT ONE Z**: from "read", the tie and the count at Z. -/
theorem bindsAtZ_cpp (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (tie : TieAt T Z) (cnt : CountAt T Z) :
    (∀ w ρ, ((atSecondHashFunction (theCpp T prove)).commit Z (settingsOfRead pp) w ρ).toRandomized.QueryBound
        honestBudget) ∧
      BindsWith (systemOfRecord (atSecondHashFunction (theCpp T prove)) Z (settingsOfRead pp))
        ((atSecondHashFunction (theCpp T prove)).extractor Z (settingsOfRead pp)) bindingErrorInQueries :=
  ⟨fun w ρ => commit_within T Z cnt (settingsOfRead pp) w ρ,
    bindsWith_bits_of_square 2 (by norm_num) (bindsWith_of_tieAt T prove Z pp hr tie)⟩

/-- **G9bits, UNDER SaltInScope, WHICH IS NOT PROVED**; if it were false, so would this goal be at
theCpp (theTwin g) (argued). No table may count this as G9bits of theCpp: what is offered are the
forms at one Z. -/
theorem g9bits_cpp (salt : SaltInScope) (tie : Tie T) (cnt : Count T) :
    G9bits (theCpp T prove) :=
  fun Z pp hs hr => bindsAtZ_cpp T prove Z pp hr (tie Z (salt Z pp hs hr)) (cnt Z)

/-- **BOTH HALVES AT zGap, SPELLED OUT.** In scope; read; the policy (25856, 512, 1); but with
probability at most soundnessErrorInQueries t n nobody has an output accepted for which the extractor gives no weights,
or which does not meet that policy at the weights that it gives; and but with probability at most
bindingErrorInQueries t nobody opens a commitment of this committer's make to weights that the same extractor
does not give. A conjunction at one extractor, no join: nothing says that a commitment under which
verify accepts is of this committer's make. -/
theorem policy_and_binding_at_zGap_cpp (tie : TieAt T zGap) (cnt : CountAt T zGap) :
    InScope zGap = true ∧ ∃ pp, readFiles zGap = .ok pp ∧ pp.pol = ⟨25856, 512, 1⟩ ∧
      (∀ (Form : Type)
        (prv : ModelWeights (settingsOfRead pp) → (atSecondHashFunction (theCpp T prove)).Rand → List Token →
          List Token → RandomizedAlgorithm Form)
        (parse : Parser (atSecondHashFunction (theCpp T prove)) zGap Form) (n : ℕ), parse.Within n →
        SoundForWith (system (atSecondHashFunction (theCpp T prove)) zGap (settingsOfRead pp) Form prv parse)
          ((atSecondHashFunction (theCpp T prove)).extractor zGap (settingsOfRead pp))
          (Policy.MeetsPolicy (settingsOfRead pp) pp.pol) fun t => soundnessErrorInQueries t n) ∧
      BindsWith (systemOfRecord (atSecondHashFunction (theCpp T prove)) zGap (settingsOfRead pp))
        ((atSecondHashFunction (theCpp T prove)).extractor zGap (settingsOfRead pp)) bindingErrorInQueries :=
  let ⟨sc, pp, hr, hp⟩ := VerifierAndGoals.filesRead.other
  ⟨sc, pp, hr, hp, ((g8bits_cpp T prove).2 zGap pp sc hr).2,
    (bindsAtZ_cpp T prove zGap pp hr tie cnt).2⟩

/-- Binding at the stored full-size example's public files. -/
theorem binds_at_zFull_cpp (tie : TieAt T storedPublicFiles) (cnt : CountAt T storedPublicFiles) :
    InScope storedPublicFiles = true ∧ ∃ pp, readFiles storedPublicFiles = .ok pp ∧
      BindsWith (systemOfRecord (atSecondHashFunction (theCpp T prove)) storedPublicFiles (settingsOfRead pp))
        ((atSecondHashFunction (theCpp T prove)).extractor storedPublicFiles (settingsOfRead pp)) bindingErrorInQueries :=
  let ⟨sc, pp, hr, _⟩ := VerifierAndGoals.filesRead.full
  ⟨sc, pp, hr, (bindsAtZ_cpp T prove storedPublicFiles pp hr tie cnt).2⟩

/-- The coins' algorithm of the wider opener: a member of the written committer's coins is itself.
-/
def coinsBothAlg (Z : PublicFiles) : Rand ⊕ Coins₀ Z → DeterministicAlgorithm (Coins₀ Z)
  | .inl ρ => coinsAlg T Z ρ
  | .inr y => .done y

/-- **THE WIDER OPENER, IN ONE EXPERIMENT, AT THE SAME EXTRACTOR**: the opener names a seed, or
coins, or ANY member of the written committer's coins at Z (typed salts whose first 256 bits are
what it likes). It is systemOfRecord of no description: these coins' type hangs on Z, and the
written committer does not run. -/
theorem both (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) (tie : TieAt T Z)
    (b : (R₀ Z).LeafBody) (sample : RandomizedAlgorithm (Rand ⊕ Coins₀ Z))
    (prv : ModelWeights (settingsOfRead pp) → Rand ⊕ Coins₀ Z → List Token → List Token →
      RandomizedAlgorithm flashProveDescription.Form) :
    BindsWith ((systemOfRecord flashProveDescription Z (settingsOfRead pp)).withRandomness (Rand ⊕ Coins₀ Z) sample
      (fun w y => match y with
        | .inl ρ => cppCommit T Z (settingsOfRead pp) w ρ
        | .inr x => (T₀ Z).commitAtCoins b (backThe Z (settingsOfRead pp) w) x.1.1 x.1.2) prv)
      (flashProveDescription.extractor Z (settingsOfRead pp)) bindingErrorInQueries := by
  have h0 := bindsWith_plain_law Z pp hr b (.done (coins₀_nonempty Z).some)
    (fun w y p o => prv w (.inr y) p o)
  have h1 := BindsWith.ofCommit _
    ((systemOfRecord flashProveDescription Z (settingsOfRead pp)).withRandomness (Rand ⊕ Coins₀ Z) sample
      (fun w y => match y with
        | .inl ρ => cppCommit T Z (settingsOfRead pp) w ρ
        | .inr x => (T₀ Z).commitAtCoins b (backThe Z (settingsOfRead pp) w) x.1.1 x.1.2) prv)
    _ _ h0 some id (coinsBothAlg T Z) 2
    (fun y => by
      cases y with
      | inl ρ => exact coinsAlg_within T Z ρ
      | inr y => exact trivial)
    (fun _ => rfl)
    (fun w y hash => by
      cases y with
      | inl ρ =>
        cases ρ with
        | inl seed => exact (tie (settingsOfRead pp) w _ _ hash).symm
        | inr x => exact (tie (settingsOfRead pp) w x _ hash).symm
      | inr y => rfl)
  exact bindsWith_bits_of_square 2 (by norm_num) ((extractor_fold Z (settingsOfRead pp)) ▸ h1)

end Bind.Cpp

end

#print axioms VerifierAndGoals.Fit.verify_withHonest
#print axioms VerifierAndGoals.Fit.extractor_withHonest
#print axioms VerifierAndGoals.Fit.parse_withHonest
#print axioms VerifierAndGoals.Fit.commit_withHonest
#print axioms VerifierAndGoals.Fit.verifierWithin_withHonest
#print axioms VerifierAndGoals.Fit.soundUnderPolicyAt_withHonest
#print axioms Bind.Cpp.commit_is
#print axioms Bind.Cpp.tieAt_of_cells
#print axioms Bind.Cpp.extractor_D₀
#print axioms Bind.Cpp.cpp_is_of_verify
#print axioms Bind.Cpp.g8bits_cpp
#print axioms Bind.Cpp.coinsAlg_within
#print axioms Bind.Cpp.commit_count
#print axioms Bind.Cpp.commit_within
#print axioms Bind.Cpp.extractor_fold
#print axioms Bind.Cpp.bindsWith_of_tieAt
#print axioms Bind.Cpp.bindsAtZ_cpp
#print axioms Bind.Cpp.g9bits_cpp
#print axioms Bind.Cpp.policy_and_binding_at_zGap_cpp
#print axioms Bind.Cpp.binds_at_zFull_cpp
#print axioms Bind.Cpp.both
