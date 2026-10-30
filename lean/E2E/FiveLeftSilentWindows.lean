-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/FiveLeftSilentWindows.lean

Summary. The placeholder provers' parameters (silentAt, E2E/FiveLeftSilent.lean; silentAtC,
E2E/FiveLeftSilentCaps.lean) with four things made arguments: the three numbers of the window of a
compiled run's leaf salts, and the filler, the fixed string that stands for a leaf's free bits
outside the window. silentAtN is silentAtC with seven fields replaced. silentAtC and silentAt are
silentAtN at the window that they pick by choice and at the empty filler (silentAtC_is,
silentAt_is: no premise).

Why. (1) silentAt takes two of its window's numbers by Classical.choose, so that nothing is known
of them but that the window is wide enough; no upper bound can be proved. (2) Its filler is empty.
SideFit (Johnson/WholeKey/Complete.lean), a premise of completeness, asks a length at every (round,
component, tree, leaf), outside the window too; with the empty filler it fails
(not_sideFit_silentC).

What this file has, for arbitrary parameters r.
  runEN, runCoinsN, silentAtN   the three definitions.
  Windows r nR nK nJ   the window is wide enough for the three protocols at r: the four clauses
      rounds, winT, winL, winB of CoinsFit (Johnson/WholeKey/Premises.lean), in their own words. It
      occurs among premises, and in conclusions that say that a window is wide enough.
  windows_chosen, windows_written, windows_of_twelve   three windows that are wide enough: the
      one picked by choice (AtPublicFiles.Premises.winK r, winJ r); the written one (AtPublicFiles.Bridge.winR,
      winK r.queryLayout, winJ r.queryLayout, E2E/BridgeCoins.lean: other definitions with the same short names); and,
      where Twelve r holds (E2E/ZetaAtInput.lean: for all public files in scope), the constants
      2 ^ 20, 2 ^ 39, 2 ^ 39.
  windows_iff   a window is wide enough exactly where its three numbers are at least the written
      one's. So the written window is the least.
  coinsFit_silentN_iff   CoinsFit holds for silentAtN exactly where ℓ ≤ sMT and the window is wide
      enough, whatever the filler. So where the window is too narrow, PremW fails.
  windows_of_coinsFit   for arbitrary parameters a of an honest side: CoinsFit gives Windows.
  fiveLeft_fixedN   the five premises of PremW on provers, coins and simulators, for every filler.
  premW_fill   PremW does not read the field fill. (silentAtN's argument fill also goes into the
      three fields coT, coL, coB; that CoinsFit for silentAtN does not depend on it is
      coinsFit_silentN_iff, whose right side does not name it.)
  sideFit_silentN_iff   SideFit holds for silentAtN exactly where the filler has ℓ bits (given
      ℓ ≤ sMT and that the encoding fits into the committed tree).
  not_sideFit_silentC   so it fails for silentAtC, for 1 ≤ ℓ ≤ sMT.

Limits.
- Nothing on hiding is new here. The three provers are the placeholders, which send fixed messages.
  Against silentAtC seven fields change: the window, the filler, and the three enumerations of the
  runs' coins. Where both windows are wide enough, the change concerns bits that no run reads and
  one public constant: that is by inspection of the compiled prover (chainO, treesO, treeO,
  OnBytes/Prover/Defs.lean), not proved (see the limit on a leaf's salt below). silentAtN is defined
  at every window; at one that is too narrow PremW fails (coinsFit_silentN_iff).
- coinsFit_silentN_iff is a projection: Windows is four of CoinsFit's nineteen clauses. It is no
  negative test on hiding: nothing says that the conclusion of wholeKeyPrivacy fails at a narrow
  window. No window is shown here to be too narrow at any parameters.
- Completeness is not proved of anything here. That any verifier accepts the placeholders' proofs is
  not proved. sideFit_silentN_iff removes one false premise for parameters that are built over
  silentAtN.
- silentAtN at another window or filler than silentAtC's is another scheme: other ranges of coins.
  Statements about silentAtC, fixedAt or laidAt (E2E/LinkLaidPrivacy.lean) say nothing of it.
- At the constants 2 ^ 20, 2 ^ 39, 2 ^ 39 the coins of one compiled run hold 2 ^ 99 · ℓ free bits
  for leaves. That is a mathematical object: no program draws it.
- That the constants are wide enough is shown under Twelve r only.
- For arbitrary r nothing bounds compilerParameters.sFS from above. At homeR b Z it is 256 (sFS_home, in
  E2E/LinkLaidAny.lean, which imports this file).
- runEN, runCoinsN, silentAtN and Windows are new definitions that occur in conclusions.
- This file imports E2E/BridgeCoins.lean for needK, needJ, leavesOf, withinWin_of_le, winR, winK and
  winJ, and with it E2E/BridgeAtRecs.lean, E2E/BridgePrivacy.lean and E2E/HonestFamily.lean.
- That a compiled prover takes a leaf's salt at places inside the wiring's trees only is not stated
  here.
- runEN is picked by choice: that it lists each value once is proved, its order is not written.

Terms: E2E/HidingTerms.lean.

Helper lemmas without a docstring. All other definitions and lemmas have docstrings.
  length_le_sum_pow, leavesOf_le_sum_pow, needK_le_lv, needJ_le_lv: the number of trees of a
    component, and the number of leaves of a tree, are at most the sum of 2 ^ d over all trees.
  leavesOf_le, need_le_of_withinWin: the converse of withinWin_of_le.
-/
import E2E.FiveLeftSilentCaps
import E2E.ZetaAtInput
import E2E.BridgeCoins
import Johnson.LinkSim.AtHome.CompileSide

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
open AtPublicFiles.Bridge (needK needJ leavesOf withinWin_of_le)
open AtPublicFiles.ZetaAt (Twelve lv)
open OnBytes.LinkSim.AtHome (fit_dress_coinsPre)

/-! ## 1. The definitions -/

/-- The free bits of a compiled run's coins in the window (nR, nK, nJ), at a request tree of depth
dq: an enumeration that lists each value once, picked by choice. -/
def runEN (r : InnerCompilerInput) (ℓ ℓr nR nK nJ dq : ℕ) : Enum (RunBits 256 nR nK nJ r.compilerParameters.sFS ℓ ℓr dq) :=
  @pick _ _ ⟨(fun _ => false, fun _ _ _ _ _ => false, fun _ => false, fun _ _ => false)⟩

/-- The coins of a compiled run: coinsPre (Johnson/WholeKey/CoinLaws.lean) at that window. -/
def runCoinsN (r : InnerCompilerInput) (b : r.LeafBody) (ℓ ℓr nR nK nJ : ℕ) (fill : Rom.Bits) (dq : ℕ) :
    Enum (Coins 256 (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)) :=
  coinsPre (lam := 256) (L := typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) nR nK nJ r.compilerParameters.sFS ℓ ℓr dq b 0 fill
    (runEN r ℓ ℓr nR nK nJ dq)

/-- **The placeholder provers' parameters with the window and the filler as arguments**: silentAtC
with seven fields replaced. All other fields are silentAtC's own.
fill: a public constant in the place of a salt outside the window: no coin; that no leaf of the
wiring's trees lies there is Windows', a premise of coinsFit_silentN. -/
def silentAtN (r : InnerCompilerInput) (b : r.LeafBody) (M ℓ ℓr nR nK nJ : ℕ) (fill : Rom.Bits)
    (capT capL capB : ℕ → ℕ) : AtRecs 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits :=
  { silentAtC r b M ℓ ℓr capT capL capB with
    nR := nR
    nK := nK
    nJ := nJ
    fill := fill
    coT := runCoinsN r b ℓ ℓr nR nK nJ fill r.queryLayout.depthReqT
    coL := runCoinsN r b ℓ ℓr nR nK nJ fill r.queryLayout.depthReqL
    coB := runCoinsN r b ℓ ℓr nR nK nJ fill r.queryLayout.depthReq }

/-- The window (nR, nK, nJ) is wide enough for the three protocols at r. -/
def Windows (r : InnerCompilerInput) (nR nK nJ : ℕ) : Prop :=
  (r.protocol.offline.shape.length ≤ nR ∧ r.protocol.link.shape.length ≤ nR ∧ r.protocol.onlineBatch.loc.shape.length ≤ nR) ∧
    WithinWin nK nJ r.protocol.offline.shape r.offlineRoundSplits (wTC r.queryLayout).sh ∧
    WithinWin nK nJ r.protocol.link.shape r.linkRoundSplits (wLC r.queryLayout).sh ∧
    WithinWin nK nJ r.protocol.onlineBatch.loc.shape r.protocol.onlineBatch.ann (wBC r.queryLayout).sh

/-! ## 2. silentAtC and silentAt are silentAtN at their own window and the empty filler -/

/-- **silentAtC is silentAtN at the window picked by choice and the empty filler.** -/
theorem silentAtC_is (r : InnerCompilerInput) (b : r.LeafBody) (M ℓ ℓr : ℕ) (capT capL capB : ℕ → ℕ) :
    silentAtC r b M ℓ ℓr capT capL capB =
      silentAtN r b M ℓ ℓr (roundsOf r) (winK r) (winJ r) [] capT capL capB := rfl

/-- **silentAt is silentAtN there, with search limits 0.** -/
theorem silentAt_is (r : InnerCompilerInput) (b : r.LeafBody) (M ℓ ℓr : ℕ) :
    silentAt r b M ℓ ℓr =
      silentAtN r b M ℓ ℓr (roundsOf r) (winK r) (winJ r) [] (fun _ => 0) (fun _ => 0)
        fun _ => 0 := rfl

/-! ## 3. Windows that are wide enough -/

/-- A wider window is wide enough too. -/
theorem Windows.mono {r : InnerCompilerInput} {nR nK nJ nR' nK' nJ' : ℕ} (h : Windows r nR nK nJ)
    (hR : nR ≤ nR') (hK : nK ≤ nK') (hJ : nJ ≤ nJ') : Windows r nR' nK' nJ' :=
  ⟨⟨h.1.1.trans hR, h.1.2.1.trans hR, h.1.2.2.trans hR⟩,
    withinWin_mono hK hJ _ _ _ h.2.1, withinWin_mono hK hJ _ _ _ h.2.2.1,
    withinWin_mono hK hJ _ _ _ h.2.2.2⟩

/-- The window that silentAt picks by choice. -/
theorem windows_chosen (r : InnerCompilerInput) : Windows r (roundsOf r) (winK r) (winJ r) :=
  ⟨⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩,
    (exists_window3 r).choose_spec.choose_spec.1, (exists_window3 r).choose_spec.choose_spec.2.1,
    (exists_window3 r).choose_spec.choose_spec.2.2⟩

/-- **The written window** (E2E/BridgeCoins.lean): the largest number of rounds, of trees of a
component, and of leaves of a tree. -/
theorem windows_written (r : InnerCompilerInput) :
    Windows r (AtPublicFiles.Bridge.winR (L := r.protocol)) (AtPublicFiles.Bridge.winK r.queryLayout) (AtPublicFiles.Bridge.winJ r.queryLayout) :=
  ⟨⟨(le_max_left _ _).trans (le_max_left _ _), (le_max_right _ _).trans (le_max_left _ _),
      le_max_right _ _⟩,
    withinWin_of_le _ _ _ _ _ ((le_max_left _ _).trans (le_max_left _ _))
      ((le_max_left _ _).trans (le_max_left _ _)),
    withinWin_of_le _ _ _ _ _ ((le_max_right _ _).trans (le_max_left _ _))
      ((le_max_right _ _).trans (le_max_left _ _)),
    withinWin_of_le _ _ _ _ _ (le_max_right _ _) (le_max_right _ _)⟩

theorem leavesOf_le {n : ℕ} : ∀ l : List ℕ, (∀ d ∈ l, 2 ^ d ≤ n) → leavesOf l ≤ n
  | [], _ => Nat.zero_le _
  | a :: l, h => by
      show max (2 ^ a) (leavesOf l) ≤ n
      exact max_le (h a List.mem_cons_self)
        (leavesOf_le l fun d hd => h d (List.mem_cons_of_mem _ hd))

theorem need_le_of_withinWin {lam K nK nJ : ℕ} :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), WithinWin nK nJ s A W →
      needK s A W ≤ nK ∧ needJ s A W ≤ nJ
  | [], _, _, _ => ⟨Nat.zero_le _, Nat.zero_le _⟩
  | _ :: s, (_, A), (w, W), h =>
      have ih := need_le_of_withinWin s A W h.2
      ⟨max_le (max_le h.1.1 h.1.2.1) ih.1,
        max_le (max_le (leavesOf_le w.depth0 h.1.2.2.1) (leavesOf_le w.depthJ h.1.2.2.2)) ih.2⟩

/-- **A window is wide enough exactly where its three numbers are at least the written
window's.** -/
theorem windows_iff (r : InnerCompilerInput) (nR nK nJ : ℕ) :
    Windows r nR nK nJ ↔
      AtPublicFiles.Bridge.winR (L := r.protocol) ≤ nR ∧ AtPublicFiles.Bridge.winK r.queryLayout ≤ nK ∧ AtPublicFiles.Bridge.winJ r.queryLayout ≤ nJ :=
  ⟨fun h =>
      have hT := need_le_of_withinWin _ _ _ h.2.1
      have hL := need_le_of_withinWin _ _ _ h.2.2.1
      have hB := need_le_of_withinWin _ _ _ h.2.2.2
      ⟨max_le (max_le h.1.1 h.1.2.1) h.1.2.2, max_le (max_le hT.1 hL.1) hB.1,
        max_le (max_le hT.2 hL.2) hB.2⟩,
    fun h => (windows_written r).mono h.1 h.2.1 h.2.2⟩

theorem length_le_sum_pow : ∀ l : List ℕ, l.length ≤ (l.map fun d => 2 ^ d).sum
  | [] => Nat.le_refl _
  | a :: l => by
      show l.length + 1 ≤ 2 ^ a + (l.map fun d => 2 ^ d).sum
      have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
      have h2 := length_le_sum_pow l
      omega

theorem leavesOf_le_sum_pow : ∀ l : List ℕ, leavesOf l ≤ (l.map fun d => 2 ^ d).sum
  | [] => Nat.le_refl _
  | a :: l => by
      show max (2 ^ a) (leavesOf l) ≤ 2 ^ a + (l.map fun d => 2 ^ d).sum
      exact max_le (Nat.le_add_right _ _) ((leavesOf_le_sum_pow l).trans (Nat.le_add_left _ _))

section
variable {lam K : ℕ}

theorem needK_le_lv : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), needK s A W ≤ lv s A W
  | [], _, _ => Nat.le_refl _
  | _ :: s, (_, A), (w, W) => by
      show max (max w.depth0.length w.depthJ.length) (needK s A W) ≤
        (w.depth0.map fun d => 2 ^ d).sum + (w.depthJ.map fun d => 2 ^ d).sum + lv s A W
      have h0 := length_le_sum_pow w.depth0
      have hJ := length_le_sum_pow w.depthJ
      have ih := needK_le_lv s A W
      exact max_le (max_le (by omega) (by omega)) (by omega)

theorem needJ_le_lv : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), needJ s A W ≤ lv s A W
  | [], _, _ => Nat.le_refl _
  | _ :: s, (_, A), (w, W) => by
      show max (max (leavesOf w.depth0) (leavesOf w.depthJ)) (needJ s A W) ≤
        (w.depth0.map fun d => 2 ^ d).sum + (w.depthJ.map fun d => 2 ^ d).sum + lv s A W
      have h0 := leavesOf_le_sum_pow w.depth0
      have hJ := leavesOf_le_sum_pow w.depthJ
      have ih := needJ_le_lv s A W
      exact max_le (max_le (by omega) (by omega)) (by omega)

end

/-- **One window for all parameters with Twelve.** -/
theorem windows_of_twelve (r : InnerCompilerInput) (h : Twelve r) : Windows r (2 ^ 20) (2 ^ 39) (2 ^ 39) :=
  have e37 : (2 : ℕ) ^ 37 ≤ 2 ^ 39 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have e25 : (2 : ℕ) ^ 25 ≤ 2 ^ 39 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  ⟨⟨h.rT, h.rL, h.rB⟩,
    withinWin_of_le _ _ _ _ _ ((needK_le_lv _ _ _).trans (h.lvT.trans e37))
      ((needJ_le_lv _ _ _).trans (h.lvT.trans e37)),
    withinWin_of_le _ _ _ _ _ ((needK_le_lv _ _ _).trans (h.lvL.trans e25))
      ((needJ_le_lv _ _ _).trans (h.lvL.trans e25)),
    withinWin_of_le _ _ _ _ _ ((needK_le_lv _ _ _).trans h.lvB) ((needJ_le_lv _ _ _).trans h.lvB)⟩

/-! ## 4. The conditions on coins hold exactly where the window is wide enough -/

/-- For arbitrary parameters a of an honest side: the conditions on coins say that a's window is
wide enough. -/
theorem windows_of_coinsFit {r : InnerCompilerInput} {a : AtRecs 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits} {c : CoinNums r.LeafBody}
    (h : CoinsFit r.queryLayout r.compilerParameters a c) : Windows r a.nR a.nK a.nJ := ⟨h.rounds, h.winT, h.winL, h.winB⟩

section
variable (r : InnerCompilerInput) (b : r.LeafBody) (M ℓ ℓr nR nK nJ : ℕ) (fill : Rom.Bits)
  (capT capL capB : ℕ → ℕ)

/-- The condition on the coins of a compiled run holds for runCoinsN, at every window and filler. -/
theorem runCoinsN_law (dq : ℕ) :
    RunLaw (runCoinsN r b ℓ ℓr nR nK nJ fill dq) nR nK nJ r.compilerParameters.sFS ℓ ℓr dq b 0 :=
  runLaw_coinsPre (lam := 256) (L := typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) nR nK nJ r.compilerParameters.sFS ℓ ℓr dq b 0 fill
    (runEN r ℓ ℓr nR nK nJ dq)
    (@pick_ok _ _ ⟨(fun _ => false, fun _ _ _ _ _ => false, fun _ => false, fun _ _ => false)⟩)

/-- The conditions on all coins hold for silentAtN, for every filler, where ℓ is at most the salt's
length and the window is wide enough. -/
theorem coinsFit_silentN (hℓ : ℓ ≤ r.compilerParameters.sMT) (hw : Windows r nR nK nJ) :
    CoinsFit r.queryLayout r.compilerParameters (silentAtN r b M ℓ ℓr nR nK nJ fill capT capL capB) (coinNums r b ℓ ℓr) where
  ri := (coinsFit_silent r b M ℓ ℓr hℓ).ri
  kT := (coinsFit_silent r b M ℓ ℓr hℓ).kT
  kL := (coinsFit_silent r b M ℓ ℓr hℓ).kL
  kB := (coinsFit_silent r b M ℓ ℓr hℓ).kB
  sl := (coinsFit_silent r b M ℓ ℓr hℓ).sl
  len₀ := (coinsFit_silent r b M ℓ ℓr hℓ).len₀
  okT := fun _ => trivial
  okL := fun _ => trivial
  okB := fun _ => trivial
  lenT := fun _ _ _ _ _ _ _ => (coinsFit_silent r b M ℓ ℓr hℓ).len₀
  lenL := fun _ _ _ _ _ _ _ => (coinsFit_silent r b M ℓ ℓr hℓ).len₀
  lenB := fun _ _ _ _ _ _ _ => (coinsFit_silent r b M ℓ ℓr hℓ).len₀
  coT := runCoinsN_law r b ℓ ℓr nR nK nJ fill _
  coL := runCoinsN_law r b ℓ ℓr nR nK nJ fill _
  coB := runCoinsN_law r b ℓ ℓr nR nK nJ fill _
  rounds := hw.1
  winT := hw.2.1
  winL := hw.2.2.1
  winB := hw.2.2.2

/-- **They hold exactly there.** So with a window that is too narrow, where the filler could stand
at a leaf of the wiring's trees, the conditions on coins fail, and PremW with them. -/
theorem coinsFit_silentN_iff :
    CoinsFit r.queryLayout r.compilerParameters (silentAtN r b M ℓ ℓr nR nK nJ fill capT capL capB) (coinNums r b ℓ ℓr) ↔
      ℓ ≤ r.compilerParameters.sMT ∧ Windows r nR nK nJ :=
  ⟨fun h => ⟨h.len₀ ▸ Nat.le_add_left _ _, windows_of_coinsFit h⟩,
    fun h => coinsFit_silentN r b M ℓ ℓr nR nK nJ fill capT capL capB h.1 h.2⟩

/-- **A warning: the placeholder provers meet FiveLeft, at every wide enough window and every
filler**, with the simulators named. They are no provers of the protocol. -/
theorem fiveLeft_fixedN (s1 : ℕ) (hℓ : ℓ ≤ r.compilerParameters.sMT) (hw : Windows r nR nK nJ)
    (Gs : r.protocol.OutOfDomainSeed → Prop) (Ryes : r.Index → r.Instance → Prop) :
    FiveLeft r (silentAtN r b M ℓ ℓr nR nK nJ fill capT capL capB) (fixedSims r.protocol) (fun _ => True)
      Gs Ryes (coinNums r b ℓ ℓr) (indexPrivacyNumbers s1 0 0 0 0 0 0) :=
  ⟨extEnc_silent r.protocol, ⟨fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl,
           fun _ _ _ _ _ _ _ _ _ => rfl⟩, fixedSims_good r.protocol r.queryLayout Gs Ryes,
    (silent_good r.Index r.Instance 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits r.queryLayout Gs Ryes).2,
    coinsFit_silentN r b M ℓ ℓr nR nK nJ fill capT capL capB hℓ hw⟩

end

/-- **PremW does not read the filler**, for arbitrary parameters. -/
theorem premW_fill {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (p : _root_.Compile.Params) (a : AtRecs lam L Bd aT aL)
    (f : Rom.Bits) (Sm : Sims L) (ok : I → Prop) (Gs : L.OutOfDomainSeed → Prop) (Ryes : I → X → Prop)
    (c : CoinNums Bd) (N : NumsW) :
    PremW W S cA p { a with fill := f } Sm ok Gs Ryes c N ↔ PremW W S cA p a Sm ok Gs Ryes c N :=
  ⟨fun h => ⟨h.ext, ⟨h.runVals.T, h.runVals.Lk, h.runVals.B⟩, h.reads, h.budget₀, h.budget₁, h.good,
      h.stops, h.seeds, h.freeT, h.freeL, h.freeB, h.wires, h.fmt, h.backT, h.backL, h.backB,
      h.plain, h.coherent, h.isLocal,
      ⟨h.coins.ri, h.coins.kT, h.coins.kL, h.coins.kB, h.coins.sl, h.coins.len₀, h.coins.okT,
        h.coins.okL, h.coins.okB, h.coins.lenT, h.coins.lenL, h.coins.lenB, h.coins.coT,
        h.coins.coL, h.coins.coB, h.coins.rounds, h.coins.winT, h.coins.winL, h.coins.winB⟩⟩,
    fun h => ⟨h.ext, ⟨h.runVals.T, h.runVals.Lk, h.runVals.B⟩, h.reads, h.budget₀, h.budget₁,
      h.good, h.stops, h.seeds, h.freeT, h.freeL, h.freeB, h.wires, h.fmt, h.backT, h.backL,
      h.backB, h.plain, h.coherent, h.isLocal,
      ⟨h.coins.ri, h.coins.kT, h.coins.kL, h.coins.kB, h.coins.sl, h.coins.len₀, h.coins.okT,
        h.coins.okL, h.coins.okB, h.coins.lenT, h.coins.lenL, h.coins.lenB, h.coins.coT,
        h.coins.coL, h.coins.coB, h.coins.rounds, h.coins.winT, h.coins.winL, h.coins.winB⟩⟩⟩

/-! ## 5. The lengths that completeness asks are met exactly where the filler has ℓ bits -/

section
variable (r : InnerCompilerInput) (b : r.LeafBody) (M ℓ ℓr nR nK nJ : ℕ) (fill : Rom.Bits)
  (capT capL capB : ℕ → ℕ)

/-- **With a filler of exactly ℓ bits all four clauses of SideFit hold**, where ℓ is at most the
salt's length and the encoding fits into the committed tree. -/
theorem sideFit_silentN (hℓ : ℓ ≤ r.compilerParameters.sMT) (hf : fill.length = ℓ) (hn : r.protocol.wordLength ≤ 2 ^ r.queryLayout.depth) :
    SideFit r.queryLayout r.compilerParameters (silentAtN r b M ℓ ℓr nR nK nJ fill capT capL capB).side where
  sl := fun a j hj => by
    have hj' : j < 2 ^ r.queryLayout.depth := lt_of_lt_of_le hj hn
    show (if j < 2 ^ r.queryLayout.depth then
      (if h : j < 2 ^ r.queryLayout.depth then List.replicate (r.compilerParameters.sMT - ℓ) false ++ List.ofFn _ else [])
      else []).length = r.compilerParameters.sMT
    rw [if_pos hj', dif_pos hj', List.length_append, List.length_replicate, List.length_ofFn]
    exact Nat.sub_add_cancel hℓ
  coT := fun a _ => fit_dress_coinsPre (L' := typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)
    (fun _ _ _ => List.replicate (r.compilerParameters.sMT - ℓ) false) (fun _ => []) nR nK nJ r.compilerParameters.sFS ℓ ℓr
    r.queryLayout.depthReqT r.compilerParameters.sMT b 0 fill fill (runEN r ℓ ℓr nR nK nJ r.queryLayout.depthReqT)
    (fun _ _ _ => by rw [List.length_replicate]; exact Nat.sub_add_cancel hℓ) hf
    (Nat.two_pow_pos _) a
  coL := fun a _ => fit_dress_coinsPre (L' := typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)
    (fun _ _ _ => List.replicate (r.compilerParameters.sMT - ℓ) false) (fun _ => []) nR nK nJ r.compilerParameters.sFS ℓ ℓr
    r.queryLayout.depthReqL r.compilerParameters.sMT b 0 fill fill (runEN r ℓ ℓr nR nK nJ r.queryLayout.depthReqL)
    (fun _ _ _ => by rw [List.length_replicate]; exact Nat.sub_add_cancel hℓ) hf
    (Nat.two_pow_pos _) a
  coB := fun a _ => fit_dress_coinsPre (L' := typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)
    (fun _ _ _ => List.replicate (r.compilerParameters.sMT - ℓ) false) (fun _ => []) nR nK nJ r.compilerParameters.sFS ℓ ℓr
    r.queryLayout.depthReq r.compilerParameters.sMT b 0 fill fill (runEN r ℓ ℓr nR nK nJ r.queryLayout.depthReq)
    (fun _ _ _ => by rw [List.length_replicate]; exact Nat.sub_add_cancel hℓ) hf
    (Nat.two_pow_pos _) a

/-- With any other filler the clause coT of SideFit fails: at round nR, which lies outside this
window whatever nK and nJ are, the first table's run is handed a leaf's salt of sMT - ℓ bits and
the filler. -/
theorem not_coT_silentN (hℓ : ℓ ≤ r.compilerParameters.sMT) (hf : fill.length ≠ ℓ) :
    ¬ ∀ a c, ((silentAtN r b M ℓ ℓr nR nK nJ fill capT capL capB).side.dressT
      ((silentAtN r b M ℓ ℓr nR nK nJ fill capT capL capB).side.rvT
        ((silentAtN r b M ℓ ℓr nR nK nJ fill capT capL capB).side.kT.e c))
      ((silentAtN r b M ℓ ℓr nR nK nJ fill capT capL capB).side.coT.e a)).Fit r.compilerParameters.sMT r.compilerParameters.sFS
        r.queryLayout.depthReqT := fun h => by
  have e := (h 0 0).leaf nR false 0 0
  change (List.replicate (r.compilerParameters.sMT - ℓ) false ++
    (if nR < nR ∧ 0 < nK ∧ 0 < nJ then _ else fill)).length = r.compilerParameters.sMT at e
  rw [if_neg (fun hh => Nat.lt_irrefl _ hh.1), List.length_append, List.length_replicate] at e
  exact hf (by omega)

/-- **With any other filler SideFit fails.** -/
theorem not_sideFit_silentN (hℓ : ℓ ≤ r.compilerParameters.sMT) (hf : fill.length ≠ ℓ) :
    ¬ SideFit r.queryLayout r.compilerParameters (silentAtN r b M ℓ ℓr nR nK nJ fill capT capL capB).side := fun h =>
  not_coT_silentN r b M ℓ ℓr nR nK nJ fill capT capL capB hℓ hf h.coT

/-- **SideFit holds exactly where the filler has ℓ bits.** -/
theorem sideFit_silentN_iff (hℓ : ℓ ≤ r.compilerParameters.sMT) (hn : r.protocol.wordLength ≤ 2 ^ r.queryLayout.depth) :
    SideFit r.queryLayout r.compilerParameters (silentAtN r b M ℓ ℓr nR nK nJ fill capT capL capB).side ↔ fill.length = ℓ :=
  ⟨fun h => Classical.byContradiction fun hf =>
      not_sideFit_silentN r b M ℓ ℓr nR nK nJ fill capT capL capB hℓ hf h,
    fun hf => sideFit_silentN r b M ℓ ℓr nR nK nJ fill capT capL capB hℓ hf hn⟩

/-- **So it fails for silentAtC**, for 1 ≤ ℓ ≤ sMT. -/
theorem not_sideFit_silentC (h1 : 1 ≤ ℓ) (hℓ : ℓ ≤ r.compilerParameters.sMT) :
    ¬ SideFit r.queryLayout r.compilerParameters (silentAtC r b M ℓ ℓr capT capL capB).side :=
  not_sideFit_silentN r b M ℓ ℓr (roundsOf r) (winK r) (winJ r) [] capT capL capB hℓ
    (Nat.ne_of_lt h1)

end

end AtPublicFiles.Premises

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Premises.runEN
#print axioms AtPublicFiles.Premises.runCoinsN
#print axioms AtPublicFiles.Premises.silentAtN
#print axioms AtPublicFiles.Premises.Windows
#print axioms AtPublicFiles.Premises.silentAtC_is
#print axioms AtPublicFiles.Premises.silentAt_is
#print axioms AtPublicFiles.Premises.Windows.mono
#print axioms AtPublicFiles.Premises.windows_chosen
#print axioms AtPublicFiles.Premises.windows_written
#print axioms AtPublicFiles.Premises.leavesOf_le
#print axioms AtPublicFiles.Premises.need_le_of_withinWin
#print axioms AtPublicFiles.Premises.windows_iff
#print axioms AtPublicFiles.Premises.length_le_sum_pow
#print axioms AtPublicFiles.Premises.leavesOf_le_sum_pow
#print axioms AtPublicFiles.Premises.needK_le_lv
#print axioms AtPublicFiles.Premises.needJ_le_lv
#print axioms AtPublicFiles.Premises.windows_of_twelve
#print axioms AtPublicFiles.Premises.windows_of_coinsFit
#print axioms AtPublicFiles.Premises.runCoinsN_law
#print axioms AtPublicFiles.Premises.coinsFit_silentN
#print axioms AtPublicFiles.Premises.coinsFit_silentN_iff
#print axioms AtPublicFiles.Premises.fiveLeft_fixedN
#print axioms AtPublicFiles.Premises.premW_fill
#print axioms AtPublicFiles.Premises.sideFit_silentN
#print axioms AtPublicFiles.Premises.not_coT_silentN
#print axioms AtPublicFiles.Premises.not_sideFit_silentN
#print axioms AtPublicFiles.Premises.sideFit_silentN_iff
#print axioms AtPublicFiles.Premises.not_sideFit_silentC
