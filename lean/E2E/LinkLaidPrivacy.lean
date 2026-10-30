-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LinkLaidPrivacy.lean

Summary. linkLaidWithBound proves index privacy of a hashed scheme, in the random-oracle model, in
which the link proof's prover is explicit (explicitLinkProver b Z) and the other two are placeholders that
send fixed messages. With one explicit and two placeholder provers the error is at most 2 ^ -135
(one request, 2 ^ 64 queries), and proofs are produced, except with small probability. That is
linkLaidAtOnce: one copy, search limits of 2 ^ 40, the scheme's own run, and public files in scope
with a live description. What that is worth. Up to the error, the simulator, which is not given the
index, produces the adversary's whole view, these link proofs included: at one fixed digest, and
with placeholders for the other two provers. The heaviest limits. It covers no message of the other
two sub-protocols' own provers. Of the premises' clauses on the link prover only the one on its
simulator has content, so all else here holds for any link prover that never aborts, whatever it
sends.

In short (in full: E2E/ZetaAtCaps.lean): the step through hashing is proved, with an error
bound; the link's prover is explicit; the two that carry the first table's proof and the inference
are placeholders.

The index: in the release's use, the model's weights (Terms: E2E/HidingTerms.lean).

The scheme. It is stated at homeR b Z, the input at one fixed digest. Explicit: given as a Lean
term, not assumed to exist. explicitLinkProver b Z is meant as the protocol's own link prover; that it is
rests on the acceptance theorem, on two_plains and on inspection.

The bound (under Theorems) is the placeholders' own, because the link's two error terms are 0: its
interactive protocol is simulated exactly (homeExact, Johnson/LinkSim/AtHome/Home.lean, with
home_withheld, Johnson/LinkSim/AtHome/TwoViews.lean). Of laidAt's parameters the error reads only
the number of copies and the three search limits (by inspection of zetaW,
Johnson/WholeKey/Zeta.lean); laid_letters proves that these are the placeholders'.

Proofs are produced. Take search limits of at least 2 ^ 40 - 1. Then the first table's proof, all
link proofs and the session's proof are produced, except with probability at most
(M + 2) · 71 · 2 ^ -256 (linkLaidStrings). So in the scheme's own run the key holds the explicit
link prover's proofs, except with that probability; for the real experiment's view, at one copy,
that is clause 5 of E2E/LinkLaidAllAtOnce.lean.

The premises on Z. linkLaidWithBound and linkLaidStrings hold for public files in scope;
linkLaidAtOnce and that clause 5 ask for a live description as well.

The proof. All twenty premises of the library's conditional theorem hold (premW_laid), by
substituting the explicit link prover and its simulator homeSim Z for the link's placeholder
(premW_withLaid, Johnson/LinkSim/AtHome/CompileFit.lean).

Theorems, at `homeR b Z`.
  `premW_laid`: for public files Z in scope, at most 710,324 copies (M + 1), at most 688,127
    sessions per copy (s1), ℓ free bits in a leaf's salt with ℓ ≤ compilerParameters.sMT, and an enumeration E with
    E.OK (on E: Tests and notes, "The parameters"): the twenty premises (`PremW`,
    Johnson/WholeKey/Premises.lean) of `wholeKeyPrivacy` (Johnson/WholeKey/Main.lean; stated in
    Johnson/WholeKey/Statement.lean) hold for the three provers of `laidAt`, with the link's
    simulator `homeSim Z` and all seven error terms equal to 0: the three simulators', the three
    provers' aborts', and the OOD seeds'. The error of index privacy, `zetaW`, is none of these.
  `linkLaidWithBound` (`LinkLaidWithBound b Z`): for public files Z in scope: `ZKCP.Gen.PrivacyOn`
    holds for the scheme, with the simulator `simWholeKey` and the error `zetaW`; and for t oracle
    queries and n ≤ s1 requests `zetaW` is at most `boundZ (9 + CT + CL + CB) M t n`, the bound of
    `PrivacyWithBound` (E2E/ZetaAtCaps.lean). This is for at most 710,324 copies (M + 1), at most
    688,127 sessions per copy (s1), ℓ free bits in a leaf's salt with 256 ≤ ℓ ≤ compilerParameters.sMT, and search
    limits of at most CT, CL and CB.
  `linkLaidStrings` (`LinkLaidStrings b Z`): for public files Z in scope: with at least 2 ^ 40 tries
    in every search, in the scheme's own run (the committer, then the prover of one request) the
    first table's proof, all M + 1 link proofs and the session's proof are produced, except with
    probability at most (M + 2) · 71 · 2 ^ -256. This is the bound of E2E/StringsAllLinks.lean.
  `linkLaidAtOnce` (`LinkLaidAtOnce b Z`): for public files Z in scope with a live description:
    both, for one copy, ℓ := 320 and every search limit 2 ^ 40.

Limits, the weightiest first.
- Two of the three provers are placeholders. The provers for the first table's proof and for the
  sessions send each round's fixed message and no message of the protocol.
- It is stated at homeR b Z, the parameters with an all-zero digest, an empty second public reading
  and the field coinBound set to b Z. That verify is ever called at this digest is not proved.
- Of the twenty premises four have a clause on the link prover (ext, runVals, good, stops), and of
  these one has content, the clause on the simulator in good (Johnson/LinkSim/AtHome/SpecHome.lean).
  Every other statement here holds unchanged for any link prover that never aborts, whatever it
  sends.
- There is no negative test. The first clause of LinkLaidWithBound is not proved to fail, at these
  parameters, for a link prover that sends the index.
- No theorem here says that the explicit link prover's messages do not ignore the index, nor that
  there are two indices. That is two_plains (Johnson/LinkSim/AtHome/TwoPlains.lean), before hashing
  and coin by coin: of distributions over the coins nothing follows from it.
- Nothing here says that any verifier accepts. For the link's interactive verifier see
  AtFullSide/E2E/LinkLaidAccepted.lean and, at the hashed challenges,
  AtFullSide/E2E/LinkLaidHashedAccepted.lean. No lemma that ends in the hashed verifier's acceptance
  can be applied to laidAt (why: Tests and notes).
- LinkLaidWithBound bounds the search limits from above only. At limits of 0 a link proof is hardly
  ever produced, and the statement then says nothing about the explicit link prover. LinkLaidAtOnce
  has both bounds; its last clause is about the scheme's own run, not about the first clause's
  experiment.
- In laidAt's link the first compilerParameters.sMT - ℓ bits of a leaf's salt are zeros, not a value that the prover
  samples for the run.
- The parameters that premW_withLaid sets are that file's choice; whether they are those of the
  programs is not stated.
- Each use of the hash is an independent random oracle on structured inputs, and randomness is
  uniform. These statements claim nothing about executable code. (usual for a proof in the
  random-oracle model)
- All limits of premW_withLaid, privacyWithBound_description and fullAt_description hold.

Tests and notes.
- Why no lemma on the hashed verifier's acceptance applies. The placeholder provers do not meet what
  such a lemma asks. And the parameter fill is the empty list, so that SideFit's clauses on the
  runs' coins (Johnson/WholeKey/Complete.lean) fail for every ℓ ≥ 1 (by inspection, not proved
  here).
- The salt. For public files in scope with a live description, compilerParameters.sMT = 576 (sMT_home), hence
  ℓ := 320 (why: the notes of E2E/ZetaAtCaps.lean); LinkLaidWithBound admits every ℓ from 256 to
  compilerParameters.sMT.
- The parameters. No statement here depends on b: it sets only the field coinBound (InnerCompilerInput.reBound),
  which none of them reads. Ryes may be taken as True: R is any pair of relations. E, an enumeration
  of the free bits of the link's compiled run, is a parameter with the premise E.OK, and one exists
  (runBits_listed).
- "Produced" says that no search ran out and no prover aborted: nothing on length, format or
  acceptance. linkLaidStrings reads only the prover's two empty abort sets.
- The explicit link prover's input reads the index (`homeIn`, `homeExt`). But its plain messages are
  built by a total function (`layP`, Johnson/Prover/Link/LinkFrame.lean: "where the list's head is
  not of the item's sort the item is 0"), so that alone does not say what is sent.
- This folder's statements on the placeholder provers hold for each fixed digest and second reading;
  `premW_withLaid` is stated for this one choice.

Terms: E2E/HidingTerms.lean.

Helper lemmas without a docstring. All other definitions and lemmas have docstrings.
  `noProverSide_reBound`, `twelve_reBound`, `tries_reBound`, `fits_reBound`, `sMT_reBound`,
    `bd_reBound`: six statements on the parameters do not read the field `coinBound`.
  `noProverSide_home`, `twelve_home`, `tries_home`, `fits_home`, `sMT_home`: so they hold at
    `homeR b Z`.
  `endAt_of`, `atOnceAt_of`: `EndAt` and `AtOnceAt` from their premises, for arbitrary parameters.


-/
import E2E.ZetaAtCaps
import E2E.StringsAllLinks
import Johnson.LinkSim.AtHome.CompileFit

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.LinkLaid
open OnBytes.WholeKey OnBytes.Prover AtPublicFiles.Premises AtPublicFiles.ZetaAt AtPublicFiles.Shown
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.LinkSim.AtHome
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference.OnPublicFiles (InnerCompilerInput)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles input_reBound)
open FlashProve (flashProveData protocolDataWellFormed homeR flashProveDescription allZeroDigest)

/- Lean compares these by their names. -/
attribute [local irreducible] FlashProve.theCoding FlashProve.theKeyData FlashProve.theProofData
  FlashProve.protocolDataWellFormed FlashProve.theDeadPlan FlashProve.theKeyGate FlashProve.theProofGate
  FlashProve.theLinkGate FlashProve.theProvers FlashProve.theNamed LPFD.Full.GF LPFD.Full.mOneAt
  PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem
  FlashProve.riDigits FlashProve.fieldRows

/-! ## 1. Six statements on the parameters do not read the field `coinBound` -/

theorem noProverSide_reBound (R : InnerCompilerInput) (n : ℕ) {Gs : R.protocol.OutOfDomainSeed → Prop} {N : NumsW} {M : ℕ}
    {capT capL capB : ℕ → ℕ} (h : NoProverSide R.queryLayout R.seedQueries R.answerCode Gs N M capT capL capB) :
    NoProverSide (R.reBound n).queryLayout (R.reBound n).seedQueries (R.reBound n).answerCode Gs N M capT capL capB := h

theorem twelve_reBound (R : InnerCompilerInput) (n : ℕ) (h : Twelve R) : Twelve (R.reBound n) :=
  ⟨h.sMT, h.sFS, h.depth, h.lvT, h.lvL, h.lvB, h.rT, h.rL, h.rB, h.qT, h.qL, h.qB⟩

theorem tries_reBound (R : InnerCompilerInput) (n : ℕ) (h : Tries R) : Tries (R.reBound n) :=
  ⟨h.nT, h.nL, h.nB, h.bT, h.bL, h.bB⟩

theorem fits_reBound (R : InnerCompilerInput) (n : ℕ)
    (h : (∀ capT capL capB, LawFit R.queryLayout R.seedQueries capT capL capB) ∧ WiresFit R.queryLayout R.answerCode) :
    (∀ capT capL capB, LawFit (R.reBound n).queryLayout (R.reBound n).seedQueries capT capL capB) ∧
      WiresFit (R.reBound n).queryLayout (R.reBound n).answerCode := h

theorem sMT_reBound (R : InnerCompilerInput) (n k : ℕ) (h : R.compilerParameters.sMT = k) : (R.reBound n).compilerParameters.sMT = k := h

theorem bd_reBound (R : InnerCompilerInput) (n : ℕ) (h : Nonempty R.LeafBody) : Nonempty (R.reBound n).LeafBody := h

/-! ## 1b. Two applications, for arbitrary r -/

/-- The conclusion of `wholeKeyPrivacy` from `PremW`, for arbitrary r. -/
theorem privacy_of_premW (r : InnerCompilerInput) {a : AtRecs 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits} {Sm : Sims r.protocol}
    {ok : r.Index → Prop} {Gs : r.protocol.OutOfDomainSeed → Prop} {Ryes : r.Index → r.Instance → Prop} {c : CoinNums r.LeafBody}
    {N : NumsW} (R : ZKCP.Gen.RelPair r.Index r.Instance Unit Unit) (i₀ : r.Index)
    (hR : ∀ i x w, R.yes i x w → Ryes i x) (h : PremW r.queryLayout r.seedQueries r.answerCode r.compilerParameters a Sm ok Gs Ryes c N) :
    ZKCP.Gen.PrivacyOn R (wholeKeySchemeOverTypedOracles r a.side) 1
      (simWholeKey r.queryLayout r.seedQueries r.answerCode r.fixedSample a.side Sm i₀ N.s1 Gs Unit) (zetaW r.queryLayout r.seedQueries r.compilerParameters a c N) ok :=
  wholeKeyPrivacy r.Index r.Instance 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters a Sm ok Gs Ryes c N R i₀
    hR h

/-- The bound of E2E/ZetaCaps.lean from the twelve numbers, for arbitrary r and arbitrary parameters
a. -/
theorem zeta_of_twelve (r : InnerCompilerInput) (h : Twelve r) (a : AtRecs 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)
    (c : CoinNums r.LeafBody) (u : NumsW) (t n CT CL CB : ℕ) (hT : ∀ i, a.capT i ≤ CT)
    (hL : ∀ i, a.capL i ≤ CL) (hB : ∀ i, a.capB i ≤ CB)
    (hz : u.zT = 0 ∧ u.zL = 0 ∧ u.zO = 0 ∧ u.hT = 0 ∧ u.hL = 0 ∧ u.hO = 0 ∧ u.δ = 0)
    (hn : n ≤ u.s1) (hℓ : 256 ≤ c.ℓ) :
    zetaW r.queryLayout r.seedQueries r.compilerParameters a c u t n ≤ boundZ (9 + CT + CL + CB) a.M t n :=
  zetaW_le_caps r.queryLayout r.seedQueries r.compilerParameters a c u t n 256 CT CL CB hT hL hB hz hn hℓ h.sFS (Nat.le_refl 256)
    h.depth (le_of_eq_of_le (runLeaves_eq _ _ _) h.lvT) (le_of_eq_of_le (runLeaves_eq _ _ _) h.lvL)
    (le_of_eq_of_le (runLeaves_eq _ _ _) h.lvB) h.rT h.rL h.rB h.qT h.qL h.qB

/-- **The conclusion, for arbitrary parameters**: the conclusion of `wholeKeyPrivacy` for the
parameters a, and the bound on its error. -/
def EndAt (r : InnerCompilerInput) (a : AtRecs 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (Sm : Sims r.protocol) (c : CoinNums r.LeafBody)
    (N : NumsW) (R : ZKCP.Gen.RelPair r.Index r.Instance Unit Unit) (i₀ : r.Index) (s1 k M : ℕ) : Prop :=
  ZKCP.Gen.PrivacyOn R (wholeKeySchemeOverTypedOracles r a.side) 1
      (simWholeKey r.queryLayout r.seedQueries r.answerCode r.fixedSample a.side Sm i₀ s1 (fun _ => True) Unit)
      (zetaW r.queryLayout r.seedQueries r.compilerParameters a c N) (fun _ => True) ∧
    ∀ t n, n ≤ s1 → zetaW r.queryLayout r.seedQueries r.compilerParameters a c N t n ≤ boundZ k M t n

theorem endAt_of (r : InnerCompilerInput) {a : AtRecs 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits} {Sm : Sims r.protocol}
    {Ryes : r.Index → r.Instance → Prop} {c : CoinNums r.LeafBody} {N : NumsW}
    (R : ZKCP.Gen.RelPair r.Index r.Instance Unit Unit) (i₀ : r.Index) (hR : ∀ i x w, R.yes i x w → Ryes i x)
    (h : PremW r.queryLayout r.seedQueries r.answerCode r.compilerParameters a Sm (fun _ => True) (fun _ => True) Ryes c N) (h12 : Twelve r)
    (s1 M CT CL CB : ℕ) (e1 : N.s1 = s1) (e2 : a.M = M) (hT : ∀ i, a.capT i ≤ CT)
    (hL : ∀ i, a.capL i ≤ CL) (hB : ∀ i, a.capB i ≤ CB)
    (hz : N.zT = 0 ∧ N.zL = 0 ∧ N.zO = 0 ∧ N.hT = 0 ∧ N.hL = 0 ∧ N.hO = 0 ∧ N.δ = 0)
    (hℓ : 256 ≤ c.ℓ) : EndAt r a Sm c N R i₀ s1 (9 + CT + CL + CB) M := by
  subst e1
  subst e2
  exact ⟨privacy_of_premW r R i₀ hR h,
    fun t n hn => zeta_of_twelve r h12 a c N t n CT CL CB hT hL hB hz hn hℓ⟩

/-- **The bound with its number, and that the proofs are produced, for arbitrary parameters.** -/
def AtOnceAt (r : InnerCompilerInput) (a : AtRecs 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (Sm : Sims r.protocol) (c : CoinNums r.LeafBody)
    (N : NumsW) (R : ZKCP.Gen.RelPair r.Index r.Instance Unit Unit) (i₀ : r.Index) (s1 : ℕ) : Prop :=
  ZKCP.Gen.PrivacyOn R (wholeKeySchemeOverTypedOracles r a.side) 1
      (simWholeKey r.queryLayout r.seedQueries r.answerCode r.fixedSample a.side Sm i₀ s1 (fun _ => True) Unit)
      (zetaW r.queryLayout r.seedQueries r.compilerParameters a c N) (fun _ => True) ∧
    (∀ t, t ≤ 2 ^ 64 → zetaW r.queryLayout r.seedQueries r.compilerParameters a c N t 1 ≤ (2⁻¹ : ℝ≥0∞) ^ 135) ∧
    ∀ (i : r.Index) (x : r.Instance),
      PrFrom (Table.empty _) (runOf r a.side i x) {y | ¬ FullTo (a.side.M + 1) y} ≤
        ((a.side.M + 2 : ℕ) : ℝ≥0∞) * (71 * (2⁻¹ : ℝ≥0∞) ^ 256)

/-- The bound on all link proofs, for arbitrary r and any provers that never abort. -/
theorem full_side (r : InnerCompilerInput) (h : HonestSide 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (ht : Tries r)
    (hL : LawFit r.queryLayout r.seedQueries h.capT h.capL h.capB) (hW : WiresFit r.queryLayout r.answerCode) (hs : NeverStops h.st)
    (h1 : ∀ i, 2 ^ 40 ≤ h.capT i + 1) (h2 : ∀ i, 2 ^ 40 ≤ h.capL i + 1)
    (h3 : ∀ i, 2 ^ 40 ≤ h.capB i + 1) (i : r.Index) (x : r.Instance) :
    PrFrom (Table.empty _) (runOf r h i x) {y | ¬ FullTo (h.M + 1) y} ≤
      ((h.M + 2 : ℕ) : ℝ≥0∞) * (71 * (2⁻¹ : ℝ≥0∞) ^ 256) :=
  (full_law r.queryLayout r.seedQueries r.answerCode r.fixedSample h hL hW hs i x).trans
    (mul_le_mul' le_rfl (alpha_of_tries r ht h.capT h.capL h.capB h1 h2 h3))

theorem atOnceAt_of (r : InnerCompilerInput) {a : AtRecs 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits} {Sm : Sims r.protocol}
    {c : CoinNums r.LeafBody} {N : NumsW} {R : ZKCP.Gen.RelPair r.Index r.Instance Unit Unit} {i₀ : r.Index} {s1 : ℕ}
    (hE : EndAt r a Sm c N R i₀ s1 (9 + 2 ^ 40 + 2 ^ 40 + 2 ^ 40) 0) (h1 : 1 ≤ s1) (ht : Tries r)
    (hL : LawFit r.queryLayout r.seedQueries a.side.capT a.side.capL a.side.capB) (hW : WiresFit r.queryLayout r.answerCode)
    (hs : NeverStops a.side.st) (c1 : ∀ i, 2 ^ 40 ≤ a.side.capT i + 1)
    (c2 : ∀ i, 2 ^ 40 ≤ a.side.capL i + 1) (c3 : ∀ i, 2 ^ 40 ≤ a.side.capB i + 1) :
    AtOnceAt r a Sm c N R i₀ s1 :=
  ⟨hE.1, fun t ht' => (hE.2 t 1 h1).trans
      (zeta_number_caps t (2 ^ 40) (2 ^ 40) (2 ^ 40) ht' le_rfl le_rfl le_rfl),
    full_side r a.side ht hL hW hs c1 c2 c3⟩

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- What holds for the built parameters with the field `coinBound` set to b Z holds for `homeR b Z`. -/
theorem atHome {P : InnerCompilerInput → Prop} (h : P ((flashProveDescription.input Z allZeroDigest []).reBound (b Z))) :
    P (homeR b Z) := Eq.mpr (congrArg P (input_reBound flashProveDescription b Z allZeroDigest [])) h

/-! ## 2. This folder's statements on the built parameters, carried to `homeR b Z` -/

theorem noProverSide_home (scope : InScope Z = true) (M s1 : ℕ) (hM : M + 1 ≤ 710324)
    (hs : s1 ≤ 688127) (zT zL zO hT hL hO : ℝ≥0∞) (capT capL capB : ℕ → ℕ) :
    NoProverSide (homeR b Z).queryLayout (homeR b Z).seedQueries (homeR b Z).answerCode (fun _ => True)
      (indexPrivacyNumbers s1 zT zL zO hT hL hO) M capT capL capB :=
  atHome b Z (P := fun r => NoProverSide r.queryLayout r.seedQueries r.answerCode (fun _ => True)
      (indexPrivacyNumbers s1 zT zL zO hT hL hO) M capT capL capB)
    (noProverSide_reBound _ (b Z)
      (noProverSide_built Z scope M s1 hM hs zT zL zO hT hL hO capT capL capB allZeroDigest []))

theorem twelve_home (scope : InScope Z = true) : Twelve (homeR b Z) :=
  atHome b Z (P := Twelve) (twelve_reBound _ (b Z) (twelve_built Z scope allZeroDigest []))

theorem tries_home (scope : InScope Z = true) : Tries (homeR b Z) :=
  atHome b Z (P := Tries) (tries_reBound _ (b Z) (tries_built Z scope allZeroDigest []))

theorem fits_home : (∀ capT capL capB, LawFit (homeR b Z).queryLayout (homeR b Z).seedQueries capT capL capB) ∧
    WiresFit (homeR b Z).queryLayout (homeR b Z).answerCode :=
  atHome b Z (P := fun r => (∀ capT capL capB, LawFit r.queryLayout r.seedQueries capT capL capB) ∧ WiresFit r.queryLayout r.answerCode)
    (fits_reBound _ (b Z) (fits_built Z allZeroDigest []))

theorem sMT_home (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    (homeR b Z).compilerParameters.sMT = 576 :=
  atHome b Z (P := fun r => r.compilerParameters.sMT = 576)
    (sMT_reBound _ (b Z) 576 (sMT_built Z scope live allZeroDigest []))

/-- The type of b₀ below has a member. -/
theorem bd_home : Nonempty (homeR b Z).LeafBody :=
  atHome b Z (P := fun r => Nonempty r.LeafBody) (bd_reBound _ (b Z) (bd_nonempty_built Z allZeroDigest []))

/-! ## 3. The placeholder provers, and the same with the explicit link prover substituted -/

/-- The placeholder provers at `homeR b Z`. -/
abbrev fixedAt (b₀ : (homeR b Z).LeafBody) (M ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ) :
    AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits :=
  silentAtC (homeR b Z) b₀ M ℓ ℓr capT capL capB

/-- The type of the enumerations of the free bits of the link's compiled run. -/
abbrev BitsE (b₀ : (homeR b Z).LeafBody) (M ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ) : Type :=
  Enum (RunBits 256 (fixedAt b Z b₀ M ℓ ℓr capT capL capB).nR
    (fixedAt b Z b₀ M ℓ ℓr capT capL capB).nK (fixedAt b Z b₀ M ℓ ℓr capT capL capB).nJ
    (homeR b Z).compilerParameters.sFS (coinNums (homeR b Z) b₀ ℓ ℓr).ℓ (coinNums (homeR b Z) b₀ ℓ ℓr).ℓr
    (homeR b Z).queryLayout.depthReqL)

/-- **The same with the explicit link prover substituted for the link's placeholder.** Its run
values have the type Unit. -/
def laidAt (b₀ : (homeR b Z).LeafBody) (M ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ)
    (E : BitsE b Z b₀ M ℓ ℓr capT capL capB) :
    AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits :=
  withLaidLink b Z (fixedAt b Z b₀ M ℓ ℓr capT capL capB) (coinNums (homeR b Z) b₀ ℓ ℓr) () E

variable (b₀ : (homeR b Z).LeafBody) (M s1 ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ)
  (E : BitsE b Z b₀ M ℓ ℓr capT capL capB)

/-- Its link prover is the explicit one. -/
theorem laid_side : (laidAt b Z b₀ M ℓ ℓr capT capL capB E).Hs.Lk = explicitLinkProver b Z := rfl

/-- **What the scheme runs**: the strategy that `laidAt` plays for a link is that of `explicitLinkProver b Z`,
on the private input made of the index and both tables' randomness and seeds, and on both tables'
OOD samples. -/
theorem laid_plays (i : (homeR b Z).Index) (u v : (homeR b Z).protocol.EncodingRandomness × (homeR b Z).protocol.OutOfDomainSeed)
    (κ : (explicitLinkProver b Z).Coin) :
    (laidAt b Z b₀ M ℓ ℓr capT capL capB E).side.st.Lk i u v κ =
      (explicitLinkProver b Z).strat (i, u, v)
        ((homeR b Z).protocol.recOf i u.1 u.2, (homeR b Z).protocol.recOf i v.1 v.2) κ := rfl

/-- There is an E that lists each value once, at the very type at which the statements bind E. -/
theorem bitsE_listed : ∃ E' : BitsE b Z b₀ M ℓ ℓr capT capL capB, E'.OK :=
  runBits_listed _ _ _ _ _ _ _ _

/-- The simulator for the link is the named one; the other two are those of the placeholder provers.
-/
theorem laid_sims : (fitSims (b := b) (Z := Z) (fixedSims (homeR b Z).protocol)).Lk = homeSim Z ∧
    (fitSims (b := b) (Z := Z) (fixedSims (homeR b Z).protocol)).T = (fixedSims (homeR b Z).protocol).T ∧
    (fitSims (b := b) (Z := Z) (fixedSims (homeR b Z).protocol)).B = (fixedSims (homeR b Z).protocol).B :=
  ⟨rfl, rfl, rfl⟩

/-- **`PremW` holds for it**, at `homeR b Z`. -/
theorem premW_laid (scope : InScope Z = true) (hM : M + 1 ≤ 710324) (hs : s1 ≤ 688127)
    (hℓ : ℓ ≤ (homeR b Z).compilerParameters.sMT) (hE : E.OK) (Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop) :
    PremW (homeR b Z).queryLayout (homeR b Z).seedQueries (homeR b Z).answerCode (homeR b Z).compilerParameters
      (laidAt b Z b₀ M ℓ ℓr capT capL capB E) (fitSims (fixedSims (homeR b Z).protocol)) (fun _ => True)
      (fun _ => True) Ryes (coinNums (homeR b Z) b₀ ℓ ℓr) (fitNums (indexPrivacyNumbers s1 0 0 0 0 0 0)) :=
  premW_withLaid b Z (homeR b Z).seedQueries (homeR b Z).answerCode (fixedAt b Z b₀ M ℓ ℓr capT capL capB)
    (fixedSims (homeR b Z).protocol) (fun _ => True) (fun _ => True) Ryes
    (coinNums (homeR b Z) b₀ ℓ ℓr) (indexPrivacyNumbers s1 0 0 0 0 0 0) () E
    (premW_of_five (homeR b Z)
      (noProverSide_home b Z scope M s1 hM hs 0 0 0 0 0 0 capT capL capB)
      (fiveLeft_fixed (homeR b Z) b₀ M s1 ℓ ℓr capT capL capB hℓ (fun _ => True) Ryes))
    trivial hE

/-! ## 4. The conclusion of `wholeKeyPrivacy`, with the bound -/

/-- `EndAt` at `laidAt`. -/
def LinkLaidWithBound : Prop :=
  ∀ (b₀ : (homeR b Z).LeafBody) (M s1 ℓ ℓr CT CL CB : ℕ) (capT capL capB : ℕ → ℕ)
    (E : BitsE b Z b₀ M ℓ ℓr capT capL capB) (Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop)
    (R : ZKCP.Gen.RelPair (homeR b Z).Index (homeR b Z).Instance Unit Unit) (i₀ : (homeR b Z).Index),
    E.OK → M + 1 ≤ 710324 → s1 ≤ 688127 → 256 ≤ ℓ → ℓ ≤ (homeR b Z).compilerParameters.sMT →
    (∀ i, capT i ≤ CT) → (∀ i, capL i ≤ CL) → (∀ i, capB i ≤ CB) →
    (∀ i x w, R.yes i x w → Ryes i x) →
    EndAt (homeR b Z) (laidAt b Z b₀ M ℓ ℓr capT capL capB E) (fitSims (fixedSims (homeR b Z).protocol))
      (coinNums (homeR b Z) b₀ ℓ ℓr) (fitNums (indexPrivacyNumbers s1 0 0 0 0 0 0)) R i₀ s1 (9 + CT + CL + CB) M

/-- The parameters of `laidAt` that the error reads are the placeholder provers'. -/
theorem laid_letters : (laidAt b Z b₀ M ℓ ℓr capT capL capB E).M = M ∧
    (laidAt b Z b₀ M ℓ ℓr capT capL capB E).capT = capT ∧
    (laidAt b Z b₀ M ℓ ℓr capT capL capB E).capL = capL ∧
    (laidAt b Z b₀ M ℓ ℓr capT capL capB E).capB = capB := ⟨rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 1600000 in
/-- The second half: the bound. -/
theorem zeta_laid (scope : InScope Z = true) (CT CL CB : ℕ) (hℓ : 256 ≤ ℓ)
    (hT : ∀ i, capT i ≤ CT) (hL : ∀ i, capL i ≤ CL) (hB : ∀ i, capB i ≤ CB) (t n : ℕ)
    (hn : n ≤ s1) :
    zetaW (homeR b Z).queryLayout (homeR b Z).seedQueries (homeR b Z).compilerParameters (laidAt b Z b₀ M ℓ ℓr capT capL capB E)
      (coinNums (homeR b Z) b₀ ℓ ℓr) (fitNums (indexPrivacyNumbers s1 0 0 0 0 0 0)) t n ≤
      boundZ (9 + CT + CL + CB) M t n :=
  zeta_of_twelve (homeR b Z) (twelve_home b Z scope) (laidAt b Z b₀ M ℓ ℓr capT capL capB E)
    (coinNums (homeR b Z) b₀ ℓ ℓr) (fitNums (indexPrivacyNumbers s1 0 0 0 0 0 0)) t n CT CL CB hT hL hB
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hn hℓ

set_option maxHeartbeats 1600000 in
/-- **For public files Z in scope.** (The statement does not depend on b: by inspection, not
proved.) -/
theorem linkLaidWithBound (scope : InScope Z = true) : LinkLaidWithBound b Z :=
  fun b₀ M s1 ℓ ℓr CT CL CB capT capL capB E Ryes R i₀ hE hM hs hℓ hℓ' hT hL hB hR =>
    endAt_of (homeR b Z) R i₀ hR
      (premW_laid b Z b₀ M s1 ℓ ℓr capT capL capB E scope hM hs hℓ' hE Ryes)
      (twelve_home b Z scope) s1 M CT CL CB rfl rfl hT hL hB ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hℓ

/-! ## 5. The proofs are produced -/

/-- The three provers never abort: the explicit link prover's abort sets are empty by definition. -/
theorem neverStops_laid : NeverStops (laidAt b Z b₀ M ℓ ℓr capT capL capB E).side.st :=
  ⟨fun _ _ _ _ => @decide_eq_false _ ((laidAt b Z b₀ M ℓ ℓr capT capL capB E).dc.T _ _ _)
      fun h => h.elim (fun a => a) fun a => a,
    fun _ _ _ _ => @decide_eq_false _ ((laidAt b Z b₀ M ℓ ℓr capT capL capB E).dc.Lk _ _ _)
      fun h => h.elim (fun a => a) fun a => a,
    fun _ _ _ _ _ _ => @decide_eq_false _ ((laidAt b Z b₀ M ℓ ℓr capT capL capB E).dc.B _ _ _)
      fun h => h.elim (fun a => a) fun a => a⟩

/-- The statement that `linkLaidStrings` proves: see the header. -/
def LinkLaidStrings : Prop :=
  ∀ (capT capL capB : ℕ → ℕ), (∀ i, 2 ^ 40 ≤ capT i + 1) → (∀ i, 2 ^ 40 ≤ capL i + 1) →
    (∀ i, 2 ^ 40 ≤ capB i + 1) → ∀ (b₀ : (homeR b Z).LeafBody) (M ℓ ℓr : ℕ)
      (E : BitsE b Z b₀ M ℓ ℓr capT capL capB) (i : (homeR b Z).Index) (x : (homeR b Z).Instance),
      PrFrom (Table.empty _) (runOf (homeR b Z) (laidAt b Z b₀ M ℓ ℓr capT capL capB E).side i x)
        {y | ¬ FullTo (M + 1) y} ≤ ((M + 2 : ℕ) : ℝ≥0∞) * (71 * (2⁻¹ : ℝ≥0∞) ^ 256)

/-- **For public files Z in scope.** (The statement does not depend on b: by inspection, not
proved.) -/
theorem linkLaidStrings (scope : InScope Z = true) : LinkLaidStrings b Z :=
  fun capT capL capB h1 h2 h3 b₀ M ℓ ℓr E i x =>
    (full_law (homeR b Z).queryLayout (homeR b Z).seedQueries (homeR b Z).answerCode (homeR b Z).fixedSample
      (laidAt b Z b₀ M ℓ ℓr capT capL capB E).side ((fits_home b Z).1 capT capL capB)
      (fits_home b Z).2 (neverStops_laid b Z b₀ M ℓ ℓr capT capL capB E) i x).trans
      (mul_le_mul' le_rfl
        (alpha_of_tries (homeR b Z) (tries_home b Z scope) capT capL capB h1 h2 h3))

/-! ## 6. The bound with its number, and that the proofs are produced, for one choice of search
limits -/

/-- `AtOnceAt` at `homeR b Z` and `laidAt`, so with one explicit and two placeholder provers, with
one copy, ℓ := 320 and every search limit 2 ^ 40: the conclusion of `wholeKeyPrivacy`; its error is
at most 2 ^ -135 for one request and at most 2 ^ 64 queries; and for the same parameters the first
table's proof, the link proof and the session's proof are produced, except with probability at most
2 · 71 · 2 ^ -256. -/
def LinkLaidAtOnce : Prop :=
  ∀ (b₀ : (homeR b Z).LeafBody) (s1 ℓr : ℕ)
    (E : BitsE b Z b₀ 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) fun _ => 2 ^ 40)
    (Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop)
    (R : ZKCP.Gen.RelPair (homeR b Z).Index (homeR b Z).Instance Unit Unit) (i₀ : (homeR b Z).Index),
    E.OK → 1 ≤ s1 → s1 ≤ 688127 → (∀ i x w, R.yes i x w → Ryes i x) →
    AtOnceAt (homeR b Z)
      (laidAt b Z b₀ 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) E)
      (fitSims (fixedSims (homeR b Z).protocol)) (coinNums (homeR b Z) b₀ 320 ℓr)
      (fitNums (indexPrivacyNumbers s1 0 0 0 0 0 0)) R i₀ s1

set_option maxHeartbeats 1600000 in
/-- **For public files Z in scope with a live description.** (The statement does not depend on b: by
inspection, not proved.) -/
theorem linkLaidAtOnce (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    LinkLaidAtOnce b Z :=
  fun b₀ s1 ℓr E Ryes R i₀ hE h1 h2 hR =>
    atOnceAt_of (homeR b Z)
      (linkLaidWithBound b Z scope b₀ 0 s1 320 ℓr (2 ^ 40) (2 ^ 40) (2 ^ 40) (fun _ => 2 ^ 40)
        (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) E Ryes R i₀ hE (by norm_num) h2 (by norm_num)
        (by rw [sMT_home b Z scope live]; norm_num) (fun _ => le_rfl) (fun _ => le_rfl)
        (fun _ => le_rfl) hR)
      h1 (tries_home b Z scope) ((fits_home b Z).1 _ _ _) (fits_home b Z).2
      (neverStops_laid b Z b₀ 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) E)
      (fun _ => Nat.le_succ _) (fun _ => Nat.le_succ _) (fun _ => Nat.le_succ _)

end AtPublicFiles.LinkLaid

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.LinkLaid.noProverSide_reBound
#print axioms AtPublicFiles.LinkLaid.twelve_reBound
#print axioms AtPublicFiles.LinkLaid.tries_reBound
#print axioms AtPublicFiles.LinkLaid.fits_reBound
#print axioms AtPublicFiles.LinkLaid.sMT_reBound
#print axioms AtPublicFiles.LinkLaid.bd_reBound
#print axioms AtPublicFiles.LinkLaid.privacy_of_premW
#print axioms AtPublicFiles.LinkLaid.zeta_of_twelve
#print axioms AtPublicFiles.LinkLaid.endAt_of
#print axioms AtPublicFiles.LinkLaid.full_side
#print axioms AtPublicFiles.LinkLaid.atOnceAt_of
#print axioms AtPublicFiles.LinkLaid.atHome
#print axioms AtPublicFiles.LinkLaid.noProverSide_home
#print axioms AtPublicFiles.LinkLaid.twelve_home
#print axioms AtPublicFiles.LinkLaid.tries_home
#print axioms AtPublicFiles.LinkLaid.fits_home
#print axioms AtPublicFiles.LinkLaid.sMT_home
#print axioms AtPublicFiles.LinkLaid.bd_home
#print axioms AtPublicFiles.LinkLaid.laid_side
#print axioms AtPublicFiles.LinkLaid.laid_plays
#print axioms AtPublicFiles.LinkLaid.bitsE_listed
#print axioms AtPublicFiles.LinkLaid.laid_sims
#print axioms AtPublicFiles.LinkLaid.premW_laid
#print axioms AtPublicFiles.LinkLaid.laid_letters
#print axioms AtPublicFiles.LinkLaid.zeta_laid
#print axioms AtPublicFiles.LinkLaid.linkLaidWithBound
#print axioms AtPublicFiles.LinkLaid.neverStops_laid
#print axioms AtPublicFiles.LinkLaid.linkLaidStrings
#print axioms AtPublicFiles.LinkLaid.linkLaidAtOnce
