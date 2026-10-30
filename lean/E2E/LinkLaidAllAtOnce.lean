-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LinkLaidAllAtOnce.lean

What this file has. linkLaidEight proves the eight statements of E2E/StringsOpenInGame.lean, and a
ninth, for the scheme of E2E/LinkLaidPrivacy.lean. There the link proof's prover is the explicit one
(explicitLinkProver b Z), and the other two provers are placeholders that send fixed messages. Clauses 1 and
2: index privacy (ZKCP.Gen.PrivacyOn) with one explicit and two placeholder provers, error at most
2 ^ -135 (one request, 2 ^ 64 oracle queries); by clauses 5 and 8 proofs are produced. Which clause
is about what: E2E/StringsOpenInGame.lean. So by clause 5, against every adversary, the key in the
real experiment's view holds the explicit link prover's proof, except with probability at most
2 · 71 · 2 ^ -256. So by clauses 1 and 2 the simulator, which is not given the index, produces up to
the error the whole view, this link proof included; the other two provers' proofs in it are
placeholders'. It holds for public files in scope with a live description, at homeR b Z, the input
at one fixed digest; that verify is ever called at this digest is not proved.

Where this stands (in full: E2E/ZetaAtCaps.lean): the step through hashing is proved, with an error
bound; the link's prover is explicit; the two that carry the first table's proof and the inference
are placeholders.

The index: in the release's use, the model's weights (Terms: E2E/HidingTerms.lean).

Theorem.
  `linkLaidEight` (`LinkLaidEight b Z`; the statement itself is `EightAt`): at `homeR b Z`, for
    public files Z in scope with a live description: for `laid40`, which is `laidAt` with one copy,
    ℓ := 320 free bits in a leaf's salt and every search limit 2 ^ 40: clauses 1 to 8 of
    `AllAtOnce`, as the header of E2E/StringsOpenInGame.lean lists them, for this scheme; and
    9. in the scheme's own run the first table's proof, all link proofs (with one copy: one) and the
    session's proof are produced, except with probability at most 2 · 71 · 2 ^ -256: the bound of
    E2E/StringsAllLinks.lean.

Limits, the weightiest first.
- All limits of E2E/LinkLaidPrivacy.lean hold, and are told there: two of the three provers are
  placeholders; one fixed digest; nothing says that any verifier accepts; there is no negative test.
- Nor does any theorem here say that the explicit link prover's messages do not ignore the index;
  that is two_plains, before hashing and coin by coin.
- Clauses 3 to 7 and 9 read only that the explicit link prover never aborts: they say about it just
  what they say about a placeholder.
- All limits of E2E/StringsOpenInGame.lean and E2E/SessionsInGame.lean hold; among them: batches of
  at most one instance.

Tests and notes.
- The nine are not nine independent statements. Clause 6 is proved from 3 and clause 7 from 4.
  Clause 8 goes through clause 1: its bound is that clause's error and a term on the ideal
  experiment. With one copy "all link proofs" is one proof, and the ninth bound is twice the third.
- EightAt is general only in the structure of parameters. Two numbers are written into the
  definition: the bound of clause 2 and boundZ (9 + 2 ^ 40 + 2 ^ 40 + 2 ^ 40) 0. They are those of
  one copy and search limits of 2 ^ 40.
- `FullTo (0 + 1)` asks for the link proof at place 0 only. `eightAt_of` asks for `EndAt` at the two
  numbers that are written into the definition.

Terms: E2E/HidingTerms.lean.

Helper lemmas without a docstring. All other definitions and lemmas have docstrings.
  `scheme_side`, `opens_side`, `one_side`, `opensView_side`: clauses 3, 4, 6 and 7 for arbitrary r
    and any provers that never abort, from their premises.
  `readsSome_reBound`, `readsLink_reBound`, `readsSome_home`, `readsLink_home`, `instance_home`:
    three more statements hold at `homeR b Z`.


-/
import E2E.LinkLaidPrivacy
import E2E.GameAtAnySide
import E2E.StringsOpenInGame

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
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (flashProveData protocolDataWellFormed homeR flashProveDescription allZeroDigest)

/- Lean compares these by their names. -/
attribute [local irreducible] FlashProve.theCoding FlashProve.theKeyData FlashProve.theProofData
  FlashProve.protocolDataWellFormed FlashProve.theDeadPlan FlashProve.theKeyGate FlashProve.theProofGate
  FlashProve.theLinkGate FlashProve.theProvers FlashProve.theNamed LPFD.Full.GF LPFD.Full.mOneAt
  PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem
  FlashProve.riDigits FlashProve.fieldRows

/-! ## 1. Four clauses, for arbitrary r and any provers that never abort -/

section
variable (r : InnerCompilerInput) (h : HonestSide 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)

theorem scheme_side (ht : Tries r) (hL : LawFit r.queryLayout r.seedQueries h.capT h.capL h.capB)
    (hW : WiresFit r.queryLayout r.answerCode) (hs : NeverStops h.st) (h1 : ∀ i, 2 ^ 40 ≤ h.capT i + 1)
    (h2 : ∀ i, 2 ^ 40 ≤ h.capL i + 1) (h3 : ∀ i, 2 ^ 40 ≤ h.capB i + 1) (i : r.Index) (x : r.Instance) :
    PrFrom (Table.empty _) (runScheme r h i x) {z | ¬ AllStrings z} ≤ 71 * (2⁻¹ : ℝ≥0∞) ^ 256 :=
  le_of_eq_of_le (pr_runScheme r h i x _)
    ((strings_law r.queryLayout r.seedQueries r.answerCode r.fixedSample h hL hW hs i x).trans
      (alpha_of_tries r ht h.capT h.capL h.capB h1 h2 h3))

theorem opens_side (ht : Tries r) (hL : LawFit r.queryLayout r.seedQueries h.capT h.capL h.capB)
    (hW : WiresFit r.queryLayout r.answerCode) (hs : NeverStops h.st) (hR : ReadsSome r) (hK : ReadsLink r)
    (h1 : ∀ i, 2 ^ 40 ≤ h.capT i + 1) (h2 : ∀ i, 2 ^ 40 ≤ h.capL i + 1)
    (h3 : ∀ i, 2 ^ 40 ≤ h.capB i + 1) (i : r.Index) (x : r.Instance) :
    PrFrom (Table.empty _) (AtPublicFiles.Shown.runCoins r h i x) {z | ¬ Opens r h i z} ≤ 71 * (2⁻¹ : ℝ≥0∞) ^
        256 :=
  (opens_law (h := h) hL hW hs hR hK i x).trans
    (alpha_of_tries r ht h.capT h.capL h.capB h1 h2 h3)

theorem one_side (ht : Tries r) (hL : LawFit r.queryLayout r.seedQueries h.capT h.capL h.capB)
    (hW : WiresFit r.queryLayout r.answerCode) (hs : NeverStops h.st) (h1 : ∀ i, 2 ^ 40 ≤ h.capT i + 1)
    (h2 : ∀ i, 2 ^ 40 ≤ h.capL i + 1) (h3 : ∀ i, 2 ^ 40 ≤ h.capB i + 1) (i : r.Index) (x : r.Instance) :
    Rom.Pr (ZKCP.Gen.realExp (wholeKeySchemeOverTypedOracles r h) oneAdv (oneEnv x ()) i 1)
        (fun _ => {v | ¬ ∀ s ∈ v.sessions, ∀ y ∈ s, Strings (v.ivk, y.2)}) ≤ 71 * (2⁻¹ : ℝ≥0∞) ^ 256
            :=
  (pr_one_le (wholeKeySchemeOverTypedOracles r h) i x () fun k π => Strings (k, π)).trans
    (scheme_side r h ht hL hW hs h1 h2 h3 i x)

theorem opensView_side (ht : Tries r) (hL : LawFit r.queryLayout r.seedQueries h.capT h.capL h.capB)
    (hW : WiresFit r.queryLayout r.answerCode) (hs : NeverStops h.st) (hR : ReadsSome r) (hK : ReadsLink r)
    (h1 : ∀ i, 2 ^ 40 ≤ h.capT i + 1) (h2 : ∀ i, 2 ^ 40 ≤ h.capL i + 1)
    (h3 : ∀ i, 2 ^ 40 ≤ h.capB i + 1) (i : r.Index) (x : r.Instance) :
    PrFrom (Table.empty _) (gameCoins r h i x) {w | ¬ OpensView r h i x w} ≤ 71 * (2⁻¹ : ℝ≥0∞) ^ 256
        :=
  (pr_gameCoins_le r h i x).trans (opens_side r h ht hL hW hs hR hK h1 h2 h3 i x)

end

/-! ## 2. Three more statements at `homeR b Z` -/

theorem readsSome_reBound (R : InnerCompilerInput) (n : ℕ) (h : ReadsSome R) : ReadsSome (R.reBound n) :=
  ⟨h.T, h.B⟩

theorem readsLink_reBound (R : InnerCompilerInput) (n : ℕ) (h : ReadsLink R) : ReadsLink (R.reBound n) := h

variable (b : PublicFiles → ℕ) (Z : PublicFiles)

theorem readsSome_home (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    ReadsSome (homeR b Z) :=
  atHome b Z (P := ReadsSome)
    (readsSome_reBound _ (b Z) (readsSome_atFiles Z scope live allZeroDigest []))

theorem readsLink_home : ReadsLink (homeR b Z) :=
  atHome b Z (P := ReadsLink) (readsLink_reBound _ (b Z) (readsLink_atFiles Z allZeroDigest []))

theorem instance_home : Nonempty (homeR b Z).Instance :=
  atHome b Z (P := fun r => Nonempty r.Instance) ⟨(FlashProve.dataAtFiles flashProveData Z).G.z₀.1⟩

/-! ## 3. The eight clauses and the bound on all link proofs, for arbitrary parameters -/

/-- **The eight clauses of `AllAtOnce` with arbitrary parameters a in place of the placeholder
provers', and a ninth**, for arbitrary r. The bound of clause 2 and `boundZ (9 + 2 ^ 40 + 2 ^ 40 +
2 ^ 40) 0` are those of one copy and search limits of 2 ^ 40. -/
def EightAt (r : InnerCompilerInput) (a : AtRecs 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (Sm : Sims r.protocol) (c : CoinNums r.LeafBody)
    (N : NumsW) (R : ZKCP.Gen.RelPair r.Index r.Instance Unit Unit) (i₀ : r.Index) (s1 : ℕ) : Prop :=
  (ZKCP.Gen.PrivacyOn R (wholeKeySchemeOverTypedOracles r a.side) 1
      (simWholeKey r.queryLayout r.seedQueries r.answerCode r.fixedSample a.side Sm i₀ s1 (fun _ => True) Unit)
      (zetaW r.queryLayout r.seedQueries r.compilerParameters a c N) (fun _ => True) ∧
    ∀ t, t ≤ 2 ^ 64 → zetaW r.queryLayout r.seedQueries r.compilerParameters a c N t 1 ≤ (2⁻¹ : ℝ≥0∞) ^ 135) ∧
    (∀ (i : r.Index) (x : r.Instance),
      PrFrom (Table.empty _) (runScheme r a.side i x) {z | ¬ AllStrings z} ≤
        71 * (2⁻¹ : ℝ≥0∞) ^ 256) ∧
    (∀ (i : r.Index) (x : r.Instance),
      PrFrom (Table.empty _) (AtPublicFiles.Shown.runCoins r a.side i x) {z | ¬ Opens r a.side i z} ≤
        71 * (2⁻¹ : ℝ≥0∞) ^ 256) ∧
    (∀ (i : r.Index)
          (Vt : FullKey 256 r.protocol r.offlineRoundSplits r.linkRoundSplits → ZKCP.Gen.AdvVerifier
            (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)) r.Instance (RequestProof 256 r.protocol))
          (Ze : ZKCP.Gen.ViewEnv (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits))
            (FullKey 256 r.protocol r.offlineRoundSplits r.linkRoundSplits) r.Instance Unit (RequestProof 256 r.protocol)) (n : ℕ),
      Rom.Pr (ZKCP.Gen.realExp (wholeKeySchemeOverTypedOracles r a.side) Vt Ze i n)
        (fun _ => {v | ¬ KeyFull (a.side.M + 1) v.ivk}) ≤
          ((a.side.M + 2 : ℕ) : ℝ≥0∞) * (71 * (2⁻¹ : ℝ≥0∞) ^ 256)) ∧
    (∀ (i : r.Index) (x : r.Instance),
      Rom.Pr (ZKCP.Gen.realExp (wholeKeySchemeOverTypedOracles r a.side) oneAdv (oneEnv x ()) i 1)
        (fun _ => {v | ¬ ∀ s ∈ v.sessions, ∀ y ∈ s, Strings (v.ivk, y.2)}) ≤
          71 * (2⁻¹ : ℝ≥0∞) ^ 256) ∧
    (∀ (i : r.Index) (x : r.Instance),
      PrFrom (Table.empty _) (gameCoins r a.side i x) {w | ¬ OpensView r a.side i x w} ≤
        71 * (2⁻¹ : ℝ≥0∞) ^ 256) ∧
    (∀ (i : r.Index)
          (Ze : ZKCP.Gen.ViewEnv (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits))
            (FullKey 256 r.protocol r.offlineRoundSplits r.linkRoundSplits) r.Instance Unit (RequestProof 256 r.protocol)),
      ZKCP.Gen.ViewEnv.IsValid R 1 Ze i → ∀ (tV : ℕ)
          (Vt : FullKey 256 r.protocol r.offlineRoundSplits r.linkRoundSplits → ZKCP.Gen.AdvVerifier
            (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)) r.Instance (RequestProof 256 r.protocol)),
      (∀ ivk, (Vt ivk).QueryBound tV) → ∀ n, n ≤ s1 →
      Rom.Pr (ZKCP.Gen.realExp (wholeKeySchemeOverTypedOracles r a.side) Vt Ze i n)
        (fun _ => {v | BadView (fun π => π.piB = none) v}) ≤
          (n : ℝ≥0∞) * (46 * (2⁻¹ : ℝ≥0∞) ^ 256) +
            boundZ (9 + 2 ^ 40 + 2 ^ 40 + 2 ^ 40) 0 tV n) ∧
    ∀ (i : r.Index) (x : r.Instance),
      PrFrom (Table.empty _) (runOf r a.side i x) {y | ¬ FullTo (a.side.M + 1) y} ≤
        ((a.side.M + 2 : ℕ) : ℝ≥0∞) * (71 * (2⁻¹ : ℝ≥0∞) ^ 256)

/-- For arbitrary r: from `EndAt` at one copy and search limits of at most 2 ^ 40, and from what the
bounds on produced proofs ask of the parameters and of the provers. -/
theorem eightAt_of (r : InnerCompilerInput) {a : AtRecs 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits} {Sm : Sims r.protocol}
    {c : CoinNums r.LeafBody} {N : NumsW} {R : ZKCP.Gen.RelPair r.Index r.Instance Unit Unit} {i₀ : r.Index} {s1 : ℕ}
    (hE : EndAt r a Sm c N R i₀ s1 (9 + 2 ^ 40 + 2 ^ 40 + 2 ^ 40) 0) (h1 : 1 ≤ s1) (ht : Tries r)
    (hL : LawFit r.queryLayout r.seedQueries a.side.capT a.side.capL a.side.capB) (hW : WiresFit r.queryLayout r.answerCode)
    (hs : NeverStops a.side.st) (hRS : ReadsSome r) (hRL : ReadsLink r) (hx : Nonempty r.Instance)
    (hp : PathsFit r.queryLayout a.side) (hSm : ∀ n y ρ ans, none ∉ (Sm.B n y ρ ans).support)
    (c1 : ∀ i, 2 ^ 40 ≤ a.side.capT i + 1) (c2 : ∀ i, 2 ^ 40 ≤ a.side.capL i + 1)
    (c3 : ∀ i, 2 ^ 40 ≤ a.side.capB i + 1) : EightAt r a Sm c N R i₀ s1 :=
  ⟨⟨hE.1, fun t ht' => (hE.2 t 1 h1).trans
      (zeta_number_caps t (2 ^ 40) (2 ^ 40) (2 ^ 40) ht' le_rfl le_rfl le_rfl)⟩,
    scheme_side r a.side ht hL hW hs c1 c2 c3,
    opens_side r a.side ht hL hW hs hRS hRL c1 c2 c3,
    fun i Vt Ze n => hx.elim fun x₀ =>
      keyInGame_side r a.side x₀ ht hL hW hs c1 c2 c3 i Vt Ze n,
    one_side r a.side ht hL hW hs c1 c2 c3,
    opensView_side r a.side ht hL hW hs hRS hRL c1 c2 c3,
    fun i Ze hZ tV Vt hq n hn =>
      (sessionsInGame_side r a.side Sm i₀ s1 _ R hE.1 hp hSm ht hW c3 i Ze hZ tV Vt hq n hn).trans
        (add_le_add le_rfl (hE.2 tV n hn)),
    full_side r a.side ht hL hW hs c1 c2 c3⟩

/-! ## 4. At `homeR b Z` and `laidAt` -/

/-- `laidAt` with one copy, ℓ := 320 and every search limit 2 ^ 40. -/
abbrev laid40 (b₀ : (homeR b Z).LeafBody) (ℓr : ℕ)
    (E : BitsE b Z b₀ 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)) :
    AtRecs 256 (homeR b Z).protocol (homeR b Z).LeafBody (homeR b Z).offlineRoundSplits (homeR b Z).linkRoundSplits :=
  laidAt b Z b₀ 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) E

/-- `EightAt` at `homeR b Z` and `laid40`. -/
def LinkLaidEight : Prop :=
  ∀ (b₀ : (homeR b Z).LeafBody) (s1 ℓr : ℕ)
    (E : BitsE b Z b₀ 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) (fun _ => 2 ^ 40))
    (Ryes : (homeR b Z).Index → (homeR b Z).Instance → Prop)
    (R : ZKCP.Gen.RelPair (homeR b Z).Index (homeR b Z).Instance Unit Unit) (i₀ : (homeR b Z).Index),
    E.OK → 1 ≤ s1 → s1 ≤ 688127 → (∀ i x w, R.yes i x w → Ryes i x) →
    EightAt (homeR b Z) (laid40 b Z b₀ ℓr E) (fitSims (fixedSims (homeR b Z).protocol))
      (coinNums (homeR b Z) b₀ 320 ℓr) (fitNums (indexPrivacyNumbers s1 0 0 0 0 0 0)) R i₀ s1

set_option maxHeartbeats 1600000 in
/-- **For public files Z in scope with a live description.** (The statement does not depend on b: by
inspection, not proved.) -/
theorem linkLaidEight (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    LinkLaidEight b Z :=
  fun b₀ s1 ℓr E Ryes R i₀ hE h1 h2 hR =>
    have h576 : 320 ≤ (homeR b Z).compilerParameters.sMT := by rw [sMT_home b Z scope live]; norm_num
    eightAt_of (homeR b Z)
      (linkLaidWithBound b Z scope b₀ 0 s1 320 ℓr (2 ^ 40) (2 ^ 40) (2 ^ 40) (fun _ => 2 ^ 40)
        (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) E Ryes R i₀ hE (by norm_num) h2 (by norm_num) h576
        (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl) hR)
      h1 (tries_home b Z scope) ((fits_home b Z).1 _ _ _) (fits_home b Z).2
      (neverStops_laid b Z b₀ 0 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) (fun _ => 2 ^ 40) E)
      (readsSome_home b Z scope live) (readsLink_home b Z) (instance_home b Z)
      (pathsFit_of_prem (premW_laid b Z b₀ 0 s1 320 ℓr (fun _ => 2 ^ 40) (fun _ => 2 ^ 40)
        (fun _ => 2 ^ 40) E scope (by norm_num) h2 h576 hE Ryes))
      (fun _ _ _ _ hm => by cases (PMF.mem_support_pure_iff _ _).1 hm)
      (fun _ => Nat.le_succ _) (fun _ => Nat.le_succ _) (fun _ => Nat.le_succ _)

end AtPublicFiles.LinkLaid

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.LinkLaid.scheme_side
#print axioms AtPublicFiles.LinkLaid.opens_side
#print axioms AtPublicFiles.LinkLaid.one_side
#print axioms AtPublicFiles.LinkLaid.opensView_side
#print axioms AtPublicFiles.LinkLaid.readsSome_reBound
#print axioms AtPublicFiles.LinkLaid.readsLink_reBound
#print axioms AtPublicFiles.LinkLaid.readsSome_home
#print axioms AtPublicFiles.LinkLaid.readsLink_home
#print axioms AtPublicFiles.LinkLaid.instance_home
#print axioms AtPublicFiles.LinkLaid.eightAt_of
#print axioms AtPublicFiles.LinkLaid.linkLaidEight
