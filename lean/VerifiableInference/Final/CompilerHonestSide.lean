-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Final/CompilerHonestSide.lean: THE COMPILER'S OWN HONEST SIDE. What honestSide gives for any protocol, any wiring, any
three provers and any settings, and what it leaves to the settings.

1.  WHAT IS CLAIMED: facts about the function honestSide. Nothing is claimed of a protocol; this file proves neither completeness nor
    zero knowledge of the protocol.
2.  THE LAWS ON ALL COINS: CoinsFit has nineteen clauses. Twelve hold at honestSide whatever the provers and the settings (the four
    enumerations of finite types list each member once; the law on the tables' salts; the three laws on a run's coins; the rounds and
    the three windows). The other seven are CompiledSettings.Lengths, and CoinsFit holds EXACTLY where they do (coinsFit_honestSide_iff).
3.  THE SEVEN: the public start of a table's salt and the free bits make the strict format's length; the three provers' coins give
    run values of the right form; at such values, with a first salt of the right length, a leaf's public start and the free bits make
    that length, in each of the three kinds of run. CoinsFit asks the last three within the window of rounds alone.
4.  THE LENGTHS THAT COMPLETENESS ASKS: SideFit holds, given the seven at every round, EXACTLY where the filler has as many bits as a
    leaf's free part, the three slots fit the request tree, and the table fits the tree or the salts are empty (sideFit_honestSide_iff).
    The table's fit is public: it is a law of the layout (QueryLayout.OKG.fits).
5.  AT CONSTANT STARTS (plainSettings) every one of these is met, for any protocol, wiring and provers, where the start of a salt and
    its free bits have the right length and the slots fit: plainSettings_fit. So these premises can be met together.
    And the run values tie nothing there: runValues_plain_holds.
6.  THE CHOICE IS THE COMPILER'S: enumerations are classical, so no program samples by them. Constant starts part from the salts of the
    programs; run values that stand in the plain parts owe RunValuesAreSent. ℓ IS FREE: where it is 0 all this holds and the error of
    index privacy says nothing (Tests.error_of_no_free_bit).
-/
import VerifiableInference.Final.CompilerTheorems

set_option autoImplicit false
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open AtPublicFiles.Bridge (pickAll pickAll_ok winR winK winJ withinWin_of_le)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {L : HolographicProtocol I X} {offlineRoundMarks : RoundSplits L.offline.shape} {linkRoundMarks : RoundSplits L.link.shape}

/-! ## 1 The seven clauses of CoinsFit that are the settings' -/

/-- **What the settings owe on lengths.** rounds: the rounds at which a leaf's start is asked. -/
structure CompiledSettings.Lengths {w : HashLayout L offlineRoundMarks linkRoundMarks} {provers : HonestProvers L} (s : CompiledSettings w provers)
    (rounds : ℕ → Prop) : Prop where
  tableSalt : s.coinNumbers.pre₀.length + s.coinNumbers.ℓ = w.compilerParameters.sMT
  valuesOffline : ∀ κ, s.wellFormed (s.runValuesOffline κ)
  valuesLink : ∀ κ, s.wellFormed (s.runValuesLink κ)
  valuesOnline : ∀ κ, s.wellFormed (s.runValuesOnline κ)
  startsOffline : ∀ v i b salt, s.wellFormed v → rounds i → salt.length = w.compilerParameters.sFS →
    (s.saltStartOffline v i b salt).length + s.coinNumbers.ℓ = w.compilerParameters.sMT
  startsLink : ∀ v i b salt, s.wellFormed v → rounds i → salt.length = w.compilerParameters.sFS →
    (s.saltStartLink v i b salt).length + s.coinNumbers.ℓ = w.compilerParameters.sMT
  startsOnline : ∀ v i b salt, s.wellFormed v → rounds i → salt.length = w.compilerParameters.sFS →
    (s.saltStartOnline v i b salt).length + s.coinNumbers.ℓ = w.compilerParameters.sMT

variable {w : HashLayout L offlineRoundMarks linkRoundMarks} {provers : HonestProvers L} {s : CompiledSettings w provers}

/-- What holds at every round holds at fewer. -/
theorem CompiledSettings.Lengths.mono {r r' : ℕ → Prop} (h : s.Lengths r) (hr : ∀ i, r' i → r i) : s.Lengths r' where
  tableSalt := h.tableSalt
  valuesOffline := h.valuesOffline
  valuesLink := h.valuesLink
  valuesOnline := h.valuesOnline
  startsOffline := fun v i b t hv hi => h.startsOffline v i b t hv (hr i hi)
  startsLink := fun v i b t hv hi => h.startsLink v i b t hv (hr i hi)
  startsOnline := fun v i b t hv hi => h.startsOnline v i b t hv (hr i hi)

/-! ## 2 CoinsFit at honestSide -/

/-- **The laws on all coins at honestSide, from the seven.** The twelve others hold at any provers and settings. -/
theorem coinsFit_honestSide (h : s.Lengths fun i => i < winR (L := L)) :
    CoinsFit w.queryLayout w.compilerParameters (honestSide w provers s) s.coinNumbers where
  ri := pickAll_ok _
  kT := pickAll_ok _
  kL := pickAll_ok _
  kB := pickAll_ok _
  sl := saltsLaw_saltsPre _ _ _ (pickAll _) (pickAll_ok _)
  len₀ := h.tableSalt
  okT := h.valuesOffline
  okL := h.valuesLink
  okB := h.valuesOnline
  lenT := h.startsOffline
  lenL := h.startsLink
  lenB := h.startsOnline
  coT := runLaw_coinsPre _ _ _ _ _ _ _ _ _ _ (pickAll _) (pickAll_ok _)
  coL := runLaw_coinsPre _ _ _ _ _ _ _ _ _ _ (pickAll _) (pickAll_ok _)
  coB := runLaw_coinsPre _ _ _ _ _ _ _ _ _ _ (pickAll _) (pickAll_ok _)
  rounds := ⟨le_trans (le_max_left _ _) (le_max_left _ _),
    le_trans (le_max_right _ _) (le_max_left _ _), le_max_right _ _⟩
  winT := withinWin_of_le _ _ _ _ _ (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_trans (le_max_left _ _) (le_max_left _ _))
  winL := withinWin_of_le _ _ _ _ _ (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_trans (le_max_right _ _) (le_max_left _ _))
  winB := withinWin_of_le _ _ _ _ _ (le_max_right _ _) (le_max_right _ _)

/-- **They hold exactly there**: at honestSide CoinsFit asks the seven and nothing else. -/
theorem coinsFit_honestSide_iff :
    CoinsFit w.queryLayout w.compilerParameters (honestSide w provers s) s.coinNumbers ↔
      s.Lengths fun i => i < winR (L := L) :=
  ⟨fun h => ⟨h.len₀, h.okT, h.okL, h.okB, h.lenT, h.lenL, h.lenB⟩, coinsFit_honestSide⟩

/-! ## 3 SideFit at honestSide -/

/-- Coins of the form coinsPre, after dress, have the strict format's lengths, where a start is asked at first salts of the right
length alone. (fit_dress_coinsPre, Johnson/LinkSim/AtHome/CompileSide.lean:78, asks it at every string.) -/
theorem fit_dress {I' X' : Type} {lam : ℕ} {L' : BatchProtocolWithLeafBody I' X'}
    (start : ℕ → Bool → Bits → Bits) (rtail : ℕ → Bits) (nR nK nJ sFS ℓ ℓr dq sMT : ℕ)
    (pad : Body L') (slot : ℕ) (fill fill' : Bits) (E : Enum (RunBits lam nR nK nJ sFS ℓ ℓr dq))
    (hs : ∀ i b t, t.length = sFS → (start i b t).length + ℓ = sMT) (hf : fill.length = ℓ)
    (hslot : slot < 2 ^ dq)
    (e : Fin ((coinsPre (L := L') nR nK nJ sFS ℓ ℓr dq pad slot fill' E).n + 1)) :
    (dress start rtail nR nK nJ fill
      ((coinsPre (L := L') nR nK nJ sFS ℓ ℓr dq pad slot fill' E).e e)).Fit sMT sFS dq where
  salt := List.length_ofFn
  leaf := fun i b k j => by
    have h0 := hs i b (List.ofFn (E.e e).1) List.length_ofFn
    show (start i b (List.ofFn (E.e e).1) ++ if i < nR ∧ k < nK ∧ j < nJ then
      ((coinsPre (L := L') nR nK nJ sFS ℓ ℓr dq pad slot fill' E).e e).leaf i b k j
      else fill).length = sMT
    by_cases hw : i < nR ∧ k < nK ∧ j < nJ
    · rw [if_pos hw]
      show (start i b _ ++ if h : i < nR ∧ k < nK ∧ j < nJ then List.ofFn _ else fill').length = sMT
      rw [dif_pos hw, List.length_append, List.length_ofFn]
      exact h0
    · rw [if_neg hw, List.length_append, hf]
      exact h0
  slot := hslot
  path := List.length_ofFn

/-- What SideFit asks beyond the seven. -/
structure CompiledSettings.SideLengths {w : HashLayout L offlineRoundMarks linkRoundMarks} {provers : HonestProvers L} (s : CompiledSettings w provers) : Prop where
  /-- outside the window the filler stands for a leaf's free bits -/
  filler : s.windowFiller.length = s.coinNumbers.ℓ
  slotOffline : s.coinNumbers.slotT < 2 ^ w.queryLayout.depthReqT
  slotLink : s.coinNumbers.slotL < 2 ^ w.queryLayout.depthReqL
  slotOnline : s.coinNumbers.slotB < 2 ^ w.queryLayout.depthReq
  /-- the table fits the tree (a law of the layout: QueryLayout.OKG.fits), or no salt has a bit -/
  table : w.compilerParameters.sMT = 0 ∨ L.wordLength ≤ 2 ^ w.queryLayout.depth

/-- **SideFit at honestSide: a general twin of sideFit_silentP**, at any provers. -/
theorem sideFit_honestSide (h : s.Lengths fun _ => True) (hs : s.SideLengths) :
    SideFit w.queryLayout w.compilerParameters (honestSide w provers s).side where
  sl := fun a j hj => by
    by_cases hj' : j < 2 ^ w.queryLayout.depth
    · show (if j < 2 ^ w.queryLayout.depth then
        (if h : j < 2 ^ w.queryLayout.depth then s.coinNumbers.pre₀ ++ List.ofFn _ else []) else []).length =
          w.compilerParameters.sMT
      rw [if_pos hj', dif_pos hj', List.length_append, List.length_ofFn]
      exact h.tableSalt
    · rcases hs.table with h0 | hn
      · show (if j < 2 ^ w.queryLayout.depth then _ else []).length = w.compilerParameters.sMT
        rw [if_neg hj', h0]
        rfl
      · exact absurd (lt_of_lt_of_le hj hn) hj'
  coT := fun a c => fit_dress (L' := typedOracleCarrier L w.LeafBody offlineRoundMarks linkRoundMarks)
    (s.saltStartOffline (s.runValuesOffline ((pickAll _).e c))) s.slotTail _ _ _ w.compilerParameters.sFS
    s.coinNumbers.ℓ s.coinNumbers.ℓr w.queryLayout.depthReqT w.compilerParameters.sMT s.coinNumbers.padT
    s.coinNumbers.slotT s.windowFiller s.windowFiller (pickAll _)
    (fun i b t ht => h.startsOffline _ i b t (h.valuesOffline _) trivial ht) hs.filler hs.slotOffline a
  coL := fun a c => fit_dress (L' := typedOracleCarrier L w.LeafBody offlineRoundMarks linkRoundMarks)
    (s.saltStartLink (s.runValuesLink ((pickAll _).e c))) s.slotTail _ _ _ w.compilerParameters.sFS
    s.coinNumbers.ℓ s.coinNumbers.ℓr w.queryLayout.depthReqL w.compilerParameters.sMT s.coinNumbers.padL
    s.coinNumbers.slotL s.windowFiller s.windowFiller (pickAll _)
    (fun i b t ht => h.startsLink _ i b t (h.valuesLink _) trivial ht) hs.filler hs.slotLink a
  coB := fun a c => fit_dress (L' := typedOracleCarrier L w.LeafBody offlineRoundMarks linkRoundMarks)
    (s.saltStartOnline (s.runValuesOnline ((pickAll _).e c))) s.slotTail _ _ _ w.compilerParameters.sFS
    s.coinNumbers.ℓ s.coinNumbers.ℓr w.queryLayout.depthReq w.compilerParameters.sMT s.coinNumbers.padB
    s.coinNumbers.slotB s.windowFiller s.windowFiller (pickAll _)
    (fun i b t ht => h.startsOnline _ i b t (h.valuesOnline _) trivial ht) hs.filler hs.slotOnline a

/-- Beyond the window a leaf's salt is its start and the filler: so a filler of another length gives a leaf of another length. -/
theorem filler_of_leaf {I' X' : Type} {lam : ℕ} {L' : BatchProtocolWithLeafBody I' X'} (start : ℕ → Bool → Bits → Bits) (rtail : ℕ → Bits)
    (nR nK nJ : ℕ) (fill : Bits) (co : Coins lam L') {sMT ℓ : ℕ} {b : Bool} {k j : ℕ}
    (hl : ((dress start rtail nR nK nJ fill co).leaf nR b k j).length = sMT)
    (h0 : (start nR b co.salt).length + ℓ = sMT) : fill.length = ℓ := by
  have e : (start nR b co.salt ++ if nR < nR ∧ k < nK ∧ j < nJ then co.leaf nR b k j else fill).length = sMT := hl
  rw [if_neg (fun z => lt_irrefl _ z.1), List.length_append] at e
  omega

/-- **A TEST THAT CAN FAIL: SideFit asks each of these.** Given the seven at every round, a filler of another length, a slot too large
or a table too long, with salts that have bits, breaks SideFit. -/
theorem sideLengths_of_sideFit (h : s.Lengths fun _ => True)
    (hF : SideFit w.queryLayout w.compilerParameters (honestSide w provers s).side) : s.SideLengths := by
  have f := hF.coT ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩
  refine ⟨?_, f.slot, (hF.coL ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩).slot,
    (hF.coB ⟨0, Nat.succ_pos _⟩ ⟨0, Nat.succ_pos _⟩).slot, ?_⟩
  · exact filler_of_leaf _ _ _ _ _ _ _ (f.leaf (winR (L := L)) false 0 0)
      (h.startsOffline _ (winR (L := L)) false _ (h.valuesOffline _) trivial f.salt)
  · by_contra hc
    push_neg at hc
    have e := hF.sl ⟨0, Nat.succ_pos _⟩ (2 ^ w.queryLayout.depth) hc.2
    have e' : (if 2 ^ w.queryLayout.depth < 2 ^ w.queryLayout.depth then _ else ([] : Bits)).length =
      w.compilerParameters.sMT := e
    rw [if_neg (lt_irrefl _)] at e'
    exact hc.1 e'.symm

/-- **They hold exactly there.** -/
theorem sideFit_honestSide_iff (h : s.Lengths fun _ => True) :
    SideFit w.queryLayout w.compilerParameters (honestSide w provers s).side ↔ s.SideLengths :=
  ⟨sideLengths_of_sideFit h, sideFit_honestSide h⟩

/-- **The premise SettingsFit, from the settings' lengths.** -/
theorem settingsFit_of (h : s.Lengths fun _ => True) (hs : s.SideLengths) : SettingsFit w provers s :=
  ⟨coinsFit_honestSide (h.mono fun _ _ => trivial), sideFit_honestSide h hs⟩

/-! ## 4 Constant starts -/

/-- At plain starts the run values tie nothing, at any provers. -/
theorem runValues_plain_holds : Spec.runValues_plain := by
  intro I X L offlineRoundMarks linkRoundMarks w provers s inRange h
  have hs : Subsingleton s.RunValues := by rw [h]; infer_instance
  exact ⟨fun _ _ _ _ _ _ _ => hs.elim _ _, fun _ _ _ _ _ _ _ => hs.elim _ _,
    fun _ _ _ _ _ _ _ _ _ => hs.elim _ _⟩

/-- **Settings with constant starts**: no run value; every leaf's salt starts with one fixed string; a filler of ℓ bits. -/
def plainSettings (w : HashLayout L offlineRoundMarks linkRoundMarks) (provers : HonestProvers L) (leafFiller : w.LeafBody)
    (limitOffline limitLink limitOnline : ℕ → ℕ) (furtherCopies : ℕ) (copyNumber : ℕ → ℕ)
    (start : Bits) (slotTail : ℕ → Bits) (coins : CoinNums w.LeafBody) : CompiledSettings w provers where
  leafFiller := leafFiller
  searchLimitOffline := limitOffline
  searchLimitLink := limitLink
  searchLimitOnline := limitOnline
  furtherCopies := furtherCopies
  copyNumber := copyNumber
  RunValues := Unit
  wellFormed := fun _ => True
  runValuesOffline := fun _ => ()
  runValuesLink := fun _ => ()
  runValuesOnline := fun _ => ()
  readOffline := fun _ => ()
  readLink := fun _ => ()
  readOnline := fun _ => ()
  saltStartOffline := fun _ _ _ _ => start
  saltStartLink := fun _ _ _ _ => start
  saltStartOnline := fun _ _ _ _ => start
  slotTail := slotTail
  windowFiller := List.replicate coins.ℓ false
  coinNumbers := coins

/-- **NOT EMPTY: at constant starts the settings' premises are met together**, for any protocol, wiring and provers, where the starts
and the free bits make a salt's length, the slots fit and the table fits. RunValuesAreSent holds there by runValues_plain_holds. -/
theorem plainSettings_fit (w : HashLayout L offlineRoundMarks linkRoundMarks) (provers : HonestProvers L) (leafFiller : w.LeafBody)
    (limitOffline limitLink limitOnline : ℕ → ℕ) (furtherCopies : ℕ) (copyNumber : ℕ → ℕ)
    (start : Bits) (slotTail : ℕ → Bits) (coins : CoinNums w.LeafBody)
    (hpre : coins.pre₀.length + coins.ℓ = w.compilerParameters.sMT)
    (hstart : start.length + coins.ℓ = w.compilerParameters.sMT)
    (hT : coins.slotT < 2 ^ w.queryLayout.depthReqT) (hL : coins.slotL < 2 ^ w.queryLayout.depthReqL)
    (hB : coins.slotB < 2 ^ w.queryLayout.depthReq) (hn : L.wordLength ≤ 2 ^ w.queryLayout.depth) :
    SettingsFit w provers (plainSettings w provers leafFiller limitOffline limitLink limitOnline furtherCopies
      copyNumber start slotTail coins) :=
  settingsFit_of
    ⟨hpre, fun _ => trivial, fun _ => trivial, fun _ => trivial, fun _ _ _ _ _ _ _ => hstart,
      fun _ _ _ _ _ _ _ => hstart, fun _ _ _ _ _ _ _ => hstart⟩
    ⟨List.length_replicate .., hT, hL, hB, Or.inr hn⟩

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.CompiledSettings.Lengths.mono
#print axioms VerifiableInference.Compilation.coinsFit_honestSide
#print axioms VerifiableInference.Compilation.coinsFit_honestSide_iff
#print axioms VerifiableInference.Compilation.fit_dress
#print axioms VerifiableInference.Compilation.filler_of_leaf
#print axioms VerifiableInference.Compilation.sideFit_honestSide
#print axioms VerifiableInference.Compilation.sideLengths_of_sideFit
#print axioms VerifiableInference.Compilation.sideFit_honestSide_iff
#print axioms VerifiableInference.Compilation.settingsFit_of
#print axioms VerifiableInference.Compilation.runValues_plain_holds
#print axioms VerifiableInference.Compilation.plainSettings_fit
