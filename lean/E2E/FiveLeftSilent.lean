-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/FiveLeftSilent.lean: A WARNING, AS A THEOREM: `FiveLeft` (E2E/PrivacyAtDescription.lean), the
five fields of `OnBytes.WholeKey.PremW` that read provers, coins and simulators, HAS A MEMBER AT
EVERY INPUT WHOSE TYPE LeafBody HAS A MEMBER, and so at the input in view: honest sides that send each
round's fixed message and never stop (`silent`, Johnson/WholeKey/Foes.lean), with the six errors of
simulators and stops 0. So the PREMISE of `privacyFromFive_description` is met by provers that send
fixed messages. What its CONCLUSION says at this member is not shown here: a bound on its error
there is in E2E/ZetaAtCaps.lean. See the limits.

  `pow_bound`, `withinWin_mono`, `exists_window`, `exists_window3`: every wiring's trees lie within
    some window; a wider window holds what a narrower one holds; one window serves an input's three
    protocols.
  `winK`, `winJ`, `roundsOf`: such a window; a number of rounds that covers the three protocols.
  `saltE`, `runE`: enumerations, each member once, of the free bits of a table's salts and of a
    compiled run's coins. `runCoins`, `runCoins_law`: such a run's coins, and the law on them.
    `unit_ok`: the enumeration of the type with one member.
  `silentAt r b M ℓ ℓr`: the letters of the scheme's honest side at the input r: the silent honest
    sides; run values of the type with one member; ℓ free bits in a leaf's salt, behind a public
    start of zeros of the length that is left; ℓr bits in the string behind a slot's value.
  `coinNums r b ℓ ℓr`: the letters of the laws on coins that go with it.
  `coinsFit_silent`: `CoinsFit` holds of them, where ℓ is at most the length that the parameters ask
    of a leaf's salt.
  **`fiveLeft_silent`**: at every input r, every b, every number of copies and of sessions, every
    such ℓ and every ℓr, all sets of OOD seeds and all relations there are simulators with which
    `FiveLeft` holds of them, at all indices, at the numbers `indexPrivacyNumbers` with these six errors 0.
  `HasSilentMember r`, `hasSilentMember_of`, `bd_nonempty_built`,
  **`hasSilentMember_description`**: at `(atSecondHashFunction theDescription).input Z c m`, at every Z, c and m,
    there is such a b: so the member stands there, at every such ℓ (the whole salt's length among
    them) and every ℓr, with no letter left.

Limits.
  * IT IS A WARNING: THE MEMBER IS NO PROVER OF THE PROTOCOL. These sides send no message of the
    protocol. "Silent" is the other file's word: they send each round's fixed message, whatever they
    are handed; they never stop; and their external strings are the index's true encodings. They are
    not sides that send nothing. In the words of Johnson/WholeKey/Statement.lean on its own
    statement, to the letter:
    "NOTHING OF A PROTOCOL UNLESS COMPLETENESS OF THE SAME HONEST SIDES, AT A SMALL ERROR, STANDS
    BESIDE IT. Index privacy alone is cheap: silent honest sides, which send fixed messages, meet
    the premises on provers with error 0 (proved: silent_good, Johnson/WholeKey/Foes.lean). What
    they are meant to fail is completeness."
  * THE ERROR `zetaW` AT THIS MEMBER IS NOT COMPUTED HERE, AT NO ℓ. It is none of the six errors
    above, and it reads ℓ. So that the premise has this member shows by itself neither that the
    conclusion of `privacyFromFive_description` says something at it, nor that the error is small at
    it. A bound at 256 ≤ ℓ and bounded caps, and a number at named letters, at the member with caps
    of E2E/FiveLeftSilentCaps.lean: E2E/ZetaAtCaps.lean (`privacyWithBound_description`,
    `privacyWithNumber_description`).
    By a reading of `zetaW`'s text, not by a theorem: at ℓ = 0 it is 1 or more, and the conclusion
    is idle there. In the words of Johnson/WholeKey/Zeta.lean, to the letter:
    "A bound that is 1 or more makes a statement of index privacy trivially true: a bar on ζ at
    named letters is owed by whoever uses it."
  * At ℓ = 0 the laws on salts hold for a poor reason: the type of the free bits has one member, and
    the salts are constant.
  * That the silent sides fail completeness is shown nowhere here.
  * b: any value of the input's type of what a query's body may hold beside. Every honest side bears
    such a value: at an input whose type has no member there is no honest side, and `FiveLeft` has
    no member. That the type has a member is shown at the input in view (`bd_nonempty_built`), not
    at every input.

-/
import E2E.PrivacyAtDescription

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.Premises
open OnBytes.WholeKey OnBytes.Prover
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles (InnerCompilerInput)
open OnBytes.WholeKey.Member (pick pick_ok)
open VerifierAndGoals (PublicFiles)
open FlashProve (flashProveData)

/-! ## 1. A window -/

/-- A bound on the powers of two at a list's members. -/
theorem pow_bound : ∀ l : List ℕ, ∃ b, ∀ d ∈ l, 2 ^ d ≤ b
  | [] => ⟨0, fun _ h => absurd h List.not_mem_nil⟩
  | a :: l => by
      obtain ⟨b, hb⟩ := pow_bound l
      refine ⟨max (2 ^ a) b, fun d hd => ?_⟩
      rcases List.mem_cons.1 hd with rfl | h
      · exact le_max_left _ _
      · exact (hb d h).trans (le_max_right _ _)

variable {lam K : ℕ}

/-- A wider window holds what a narrower one holds. -/
theorem withinWin_mono {nK nJ nK' nJ' : ℕ} (hK : nK ≤ nK') (hJ : nJ ≤ nJ') :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A),
      WithinWin nK nJ s A W → WithinWin nK' nJ' s A W
  | [], _, _, _ => trivial
  | _ :: s, (_, A), (_, W), h =>
      ⟨⟨h.1.1.trans hK, h.1.2.1.trans hK, fun d hd => (h.1.2.2.1 d hd).trans hJ,
        fun d hd => (h.1.2.2.2 d hd).trans hJ⟩, withinWin_mono hK hJ s A W h.2⟩

/-- Every wiring's trees lie within some window. -/
theorem exists_window :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), ∃ nK nJ, WithinWin nK nJ s A W
  | [], _, _ => ⟨0, 0, trivial⟩
  | _ :: s, (_, A), (w, W) => by
      obtain ⟨k, j, h⟩ := exists_window s A W
      obtain ⟨b0, h0⟩ := pow_bound w.depth0
      obtain ⟨bJ, hJ⟩ := pow_bound w.depthJ
      exact ⟨max k (max w.depth0.length w.depthJ.length), max j (max b0 bJ),
        ⟨(le_max_left _ _).trans (le_max_right _ _), (le_max_right _ _).trans (le_max_right _ _),
          fun d hd => (h0 d hd).trans ((le_max_left _ _).trans (le_max_right _ _)),
          fun d hd => (hJ d hd).trans ((le_max_right _ _).trans (le_max_right _ _))⟩,
        withinWin_mono (le_max_left _ _) (le_max_left _ _) s A W h⟩

/-- One window for an input's three protocols. -/
theorem exists_window3 (r : InnerCompilerInput) :
    ∃ nK nJ, WithinWin nK nJ r.protocol.offline.shape r.offlineRoundSplits (wTC r.queryLayout).sh ∧
      WithinWin nK nJ r.protocol.link.shape r.linkRoundSplits (wLC r.queryLayout).sh ∧
      WithinWin nK nJ r.protocol.onlineBatch.loc.shape r.protocol.onlineBatch.ann (wBC r.queryLayout).sh := by
  obtain ⟨k1, j1, h1⟩ := exists_window r.protocol.offline.shape r.offlineRoundSplits (wTC r.queryLayout).sh
  obtain ⟨k2, j2, h2⟩ := exists_window r.protocol.link.shape r.linkRoundSplits (wLC r.queryLayout).sh
  obtain ⟨k3, j3, h3⟩ := exists_window r.protocol.onlineBatch.loc.shape r.protocol.onlineBatch.ann (wBC r.queryLayout).sh
  exact ⟨max k1 (max k2 k3), max j1 (max j2 j3),
    withinWin_mono (le_max_left _ _) (le_max_left _ _) _ _ _ h1,
    withinWin_mono ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_left _ _).trans (le_max_right _ _)) _ _ _ h2,
    withinWin_mono ((le_max_right _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _)) _ _ _ h3⟩

/-- Such a window: the number of trees. -/
def winK (r : InnerCompilerInput) : ℕ := (exists_window3 r).choose

/-- The number of leaves. -/
def winJ (r : InnerCompilerInput) : ℕ := (exists_window3 r).choose_spec.choose

/-- A number of rounds that covers the three protocols. -/
def roundsOf (r : InnerCompilerInput) : ℕ :=
  max r.protocol.offline.shape.length (max r.protocol.link.shape.length r.protocol.onlineBatch.loc.shape.length)

/-! ## 2. The letters -/

/-- The free bits of a table's salts, ℓ a salt: each member once. -/
def saltE (r : InnerCompilerInput) (ℓ : ℕ) : Enum (Fin (2 ^ r.queryLayout.depth) → Fin ℓ → Bool) :=
  @pick _ _ ⟨fun _ _ => false⟩

/-- The free bits of a compiled run's coins, at a request tree of depth dq: each member once. -/
def runE (r : InnerCompilerInput) (ℓ ℓr dq : ℕ) :
    Enum (RunBits 256 (roundsOf r) (winK r) (winJ r) r.compilerParameters.sFS ℓ ℓr dq) :=
  @pick _ _ ⟨(fun _ => false, fun _ _ _ _ _ => false, fun _ => false, fun _ _ => false)⟩

/-- The coins of a compiled run. -/
def runCoins (r : InnerCompilerInput) (b : r.LeafBody) (ℓ ℓr dq : ℕ) :
    Enum (Coins 256 (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)) :=
  coinsPre (lam := 256) (L := typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (roundsOf r) (winK r) (winJ r) r.compilerParameters.sFS ℓ
    ℓr dq b 0 [] (runE r ℓ ℓr dq)

/-- **The letters of the scheme's honest side, with the silent honest sides**, ℓ free bits in a
leaf's salt and ℓr bits in the string behind a slot's value. -/
def silentAt (r : InnerCompilerInput) (b : r.LeafBody) (M ℓ ℓr : ℕ) : AtRecs 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits where
  Hs := silent r.protocol
  dc := ⟨fun _ _ _ => Classical.dec _, fun _ _ _ => Classical.dec _, fun _ _ _ => Classical.dec _⟩
  b₀ := b
  capT := fun _ => 0
  capL := fun _ => 0
  capB := fun _ => 0
  M := M
  nm := id
  RV := Unit
  okV := fun _ => True
  rvT := fun _ => ()
  rvL := fun _ => ()
  rvB := fun _ => ()
  startT := fun _ _ _ _ => List.replicate (r.compilerParameters.sMT - ℓ) false
  startL := fun _ _ _ _ => List.replicate (r.compilerParameters.sMT - ℓ) false
  startB := fun _ _ _ _ => List.replicate (r.compilerParameters.sMT - ℓ) false
  pvT := fun _ => ()
  pvL := fun _ => ()
  pvB := fun _ => ()
  rtail := fun _ => []
  nR := roundsOf r
  nK := winK r
  nJ := winJ r
  fill := []
  ri := pick r.protocol.EncodingRandomness
  sl := saltsPre (List.replicate (r.compilerParameters.sMT - ℓ) false) (2 ^ r.queryLayout.depth) ℓ (saltE r ℓ)
  kT := (⟨0, fun _ => ()⟩ : Enum Unit)
  kL := (⟨0, fun _ => ()⟩ : Enum Unit)
  kB := (⟨0, fun _ => ()⟩ : Enum Unit)
  coT := runCoins r b ℓ ℓr r.queryLayout.depthReqT
  coL := runCoins r b ℓ ℓr r.queryLayout.depthReqL
  coB := runCoins r b ℓ ℓr r.queryLayout.depthReq

/-- The letters of the laws on coins that go with it: ℓ free bits in a leaf's salt, behind a public
start of zeros; ℓr bits in the string behind a slot's value. -/
def coinNums (r : InnerCompilerInput) (b : r.LeafBody) (ℓ ℓr : ℕ) : CoinNums r.LeafBody :=
  ⟨List.replicate (r.compilerParameters.sMT - ℓ) false, ℓ, ℓr, b, b, b, 0, 0, 0⟩

/-- The one enumeration of the type with one member lists it once. -/
theorem unit_ok : (⟨0, fun _ => ()⟩ : Enum Unit).OK :=
  ⟨fun a b _ => Subsingleton.elim (α := Fin 1) a b, fun _ => ⟨(0 : Fin 1), rfl⟩⟩

/-- The law on the coins of a compiled run holds of `runCoins`. -/
theorem runCoins_law (r : InnerCompilerInput) (b : r.LeafBody) (ℓ ℓr dq : ℕ) :
    RunLaw (runCoins r b ℓ ℓr dq) (roundsOf r) (winK r) (winJ r) r.compilerParameters.sFS ℓ ℓr dq b 0 :=
  runLaw_coinsPre (lam := 256) (L := typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (roundsOf r) (winK r) (winJ r)
    r.compilerParameters.sFS ℓ ℓr dq b 0 [] (runE r ℓ ℓr dq)
    (@pick_ok _ _ ⟨(fun _ => false, fun _ _ _ _ _ => false, fun _ => false, fun _ _ => false)⟩)

/-! ## 3. The member -/

/-- The laws on all coins hold of these letters, where ℓ is at most the salt's length. -/
theorem coinsFit_silent (r : InnerCompilerInput) (b : r.LeafBody) (M ℓ ℓr : ℕ) (hℓ : ℓ ≤ r.compilerParameters.sMT) :
    CoinsFit r.queryLayout r.compilerParameters (silentAt r b M ℓ ℓr) (coinNums r b ℓ ℓr) where
  ri := pick_ok _
  kT := unit_ok
  kL := unit_ok
  kB := unit_ok
  sl := saltsLaw_saltsPre _ _ ℓ (saltE r ℓ) (@pick_ok _ _ ⟨fun _ _ => false⟩)
  len₀ := by
    show (List.replicate (r.compilerParameters.sMT - ℓ) false).length + ℓ = r.compilerParameters.sMT
    rw [List.length_replicate]; exact Nat.sub_add_cancel hℓ
  okT := fun _ => trivial
  okL := fun _ => trivial
  okB := fun _ => trivial
  lenT := fun _ _ _ _ _ _ _ => by
    show (List.replicate (r.compilerParameters.sMT - ℓ) false).length + ℓ = r.compilerParameters.sMT
    rw [List.length_replicate]; exact Nat.sub_add_cancel hℓ
  lenL := fun _ _ _ _ _ _ _ => by
    show (List.replicate (r.compilerParameters.sMT - ℓ) false).length + ℓ = r.compilerParameters.sMT
    rw [List.length_replicate]; exact Nat.sub_add_cancel hℓ
  lenB := fun _ _ _ _ _ _ _ => by
    show (List.replicate (r.compilerParameters.sMT - ℓ) false).length + ℓ = r.compilerParameters.sMT
    rw [List.length_replicate]; exact Nat.sub_add_cancel hℓ
  coT := runCoins_law r b ℓ ℓr _
  coL := runCoins_law r b ℓ ℓr _
  coB := runCoins_law r b ℓ ℓr _
  rounds := ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩
  winT := (exists_window3 r).choose_spec.choose_spec.1
  winL := (exists_window3 r).choose_spec.choose_spec.2.1
  winB := (exists_window3 r).choose_spec.choose_spec.2.2

/-- **A warning: `FiveLeft` has a member at every input whose type LeafBody has one**: the silent honest
sides, with the six errors of simulators and stops 0, at every number ℓ of free bits in a leaf's
salt up to the salt's length. NO PROVER OF THE PROTOCOL: these sides send no message of the
protocol, and the error `zetaW` at them is not computed here (a bound at 256 ≤ ℓ:
E2E/ZetaAtCaps.lean). -/
theorem fiveLeft_silent (r : InnerCompilerInput) (b : r.LeafBody) (M s1 ℓ ℓr : ℕ) (hℓ : ℓ ≤ r.compilerParameters.sMT)
    (Gs : r.protocol.OutOfDomainSeed → Prop) (Ryes : r.Index → r.Instance → Prop) :
    ∃ Sm : Sims r.protocol, FiveLeft r (silentAt r b M ℓ ℓr) Sm (fun _ => True) Gs Ryes
      (coinNums r b ℓ ℓr) (indexPrivacyNumbers s1 0 0 0 0 0 0) := by
  obtain ⟨⟨Sm, hg⟩, hs⟩ := silent_good r.Index r.Instance 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits r.queryLayout Gs Ryes
  exact ⟨Sm, extEnc_silent r.protocol, ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl,
           fun _ _ _ _ _ _ _ _ _ => rfl⟩, hg, hs, coinsFit_silent r b M ℓ ℓr hℓ⟩

/-! ## 4. At the input in view, with no letter left -/

/-- The five fields have the silent member at the input r: at every number of copies and of
sessions, every number ℓ of free bits in a leaf's salt up to the salt's length, every ℓr, all sets
of OOD seeds and all relations. -/
def HasSilentMember (r : InnerCompilerInput) : Prop :=
  ∀ (M s1 ℓ ℓr : ℕ), ℓ ≤ r.compilerParameters.sMT → ∀ (Gs : r.protocol.OutOfDomainSeed → Prop) (Ryes : r.Index → r.Instance → Prop),
    ∃ (b : r.LeafBody) (Sm : Sims r.protocol), FiveLeft r (silentAt r b M ℓ ℓr) Sm (fun _ => True) Gs Ryes
      (coinNums r b ℓ ℓr) (indexPrivacyNumbers s1 0 0 0 0 0 0)

/-- It does wherever the input's type of what a query's body may hold beside has a member. -/
theorem hasSilentMember_of (r : InnerCompilerInput) (h : Nonempty r.LeafBody) : HasSilentMember r :=
  fun M s1 ℓ ℓr hℓ Gs Ryes => h.elim fun b => ⟨b, fiveLeft_silent r b M s1 ℓ ℓr hℓ Gs Ryes⟩

/-- That type has a member at the input of the value that the library builds: the empty list of
bits. -/
theorem bd_nonempty_built (Z : PublicFiles) (c : VerifiableInference.Digest)
    (m : (FlashProve.descriptionOfDataOnBytes flashProveData).More) :
    Nonempty ((FlashProve.descriptionOfDataOnBytes flashProveData).input Z c m).LeafBody := ⟨([] : List Bool)⟩

/-- **A warning, at the input at which the goals' verifier calls the compiled verifier**, at every
Z, c and m: the five fields have the silent member there. So the premise `FiveLeft` of
`PrivacyFromFive` can be met at that input. -/
theorem hasSilentMember_description (Z : PublicFiles) :
    ∀ (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More),
      HasSilentMember ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m) :=
  VerifierAndGoals.ofBuilt
    (Q := fun D => ∀ (c : VerifiableInference.Digest) (m : D.More),
      HasSilentMember (D.input Z c m))
    fun c m => hasSilentMember_of _ (bd_nonempty_built Z c m)

end AtPublicFiles.Premises

#print axioms AtPublicFiles.Premises.pow_bound
#print axioms AtPublicFiles.Premises.withinWin_mono
#print axioms AtPublicFiles.Premises.exists_window
#print axioms AtPublicFiles.Premises.exists_window3
#print axioms AtPublicFiles.Premises.unit_ok
#print axioms AtPublicFiles.Premises.runCoins_law
#print axioms AtPublicFiles.Premises.coinsFit_silent
#print axioms AtPublicFiles.Premises.fiveLeft_silent
#print axioms AtPublicFiles.Premises.hasSilentMember_of
#print axioms AtPublicFiles.Premises.bd_nonempty_built
#print axioms AtPublicFiles.Premises.hasSilentMember_description
