-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/ThreeArms.lean: the key's arm, the entry's arm and the proof's arm in one
experiment over one hash function, each with a coding of its own: the sum of their three bounds.

The experiment: the committer runs and publishes the first root with its record. One prover runs and
names Test's proof string; the further root, its record and Link's proof string; an instance and the
session's proof string. The three arms run, each asking the one function through its own coding (mT,
mL, mB). The two logs of strings are kept apart.

What is said: except with probability at most the sum of the three arms' bounds, if all three arms
say yes, then the word that the committer's own log of strings determines under the first root
decodes, with the committer's record, to an index i, and the instance has a witness for i.

Why three codings: each arm is given a coding of its own, so that nothing is asked of how one file's
chains' labels stand to another's (the labels: OnBytes/Params/Chains.lean). The codings must agree
on the leaf and node oracles (`SameTrees`, WordCodings.lean): then the arms' words are the same
words.

Main names:
  `OutP3`: what the prover names.
  `exp3A`: the experiment.
  `pr3T`, `pr3L`, `mk3B`: the prover followed by a projection; committer and prover as one maker:
    what each arm's own theorem is applied at.
  `exp3A_le_T`, `exp3A_le_L`, `exp3A_le_B`: at each function, an event on one arm's part of the
    outcome is at most as likely as in that arm's own experiment.
  `three_arms_holds`: all three accept, and what one of them promises fails.
  `three_arms`: all three accept, and the committer's word does not decode to an index for which the
    instance has a witness.

Limits: those of KeyAnsStage.lean, LinkAnsKeyStage.lean and ProofAnsStage.lean, and:
  * Soundness alone; one random function; typed values, not bytes; one W, S, cA and r₀ for the three
    arms.
  * The 27 premises are laws of letters here. The three on soundness are the third, fourth and fifth
    clauses of `HolographicProtocol.SoundAtR` (Hiop/RecInterface.lean). That all can be met together is not shown;
    until it is, the theorem may be true and empty.
  * I, X, Wn and Rno are letters: nothing here says what an index, an instance or a witness is at
    the programs' protocol.
  * "Publish" means: hand a typed root and a typed record to the arms. The instance is the prover's
    to name, after the committer has published.
  * Where the committer has hashed nothing at a place under its root, the word has the fixed filling
    there.
  * No coding is given, and that three codings exist which meet `SameTrees` and each spell their own
    file's calls as the programs do is not shown.
  * The calls of committer and prover are counted once in each arm's bound, so three times.
  * These are the three arms, not the whole compiled verifier: what it tests beside them (the number
    of the copy; the choice of the link by a leaf) is not here, nor is any test of a commitment ID.
  * No yes is shown.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.KeyAnsStage
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsKeyStage
import Johnson.TypedOracleCompiler.RecCompile.ProofAnsStage
import Johnson.TypedOracleCompiler.RecCompile.WordCodings

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)}

/-- what the prover names: Test's proof string; the further root, its record, Link's proof string;
an instance and the session's proof string -/
abbrev OutP3 (lam : ℕ) (L : HolographicProtocol I X) (aT : RoundSplits L.offline.shape) (aL : RoundSplits L.link.shape) : Type :=
  OneProtocolProof lam (batTC L aT) × Out3 lam L aL × (X × OneProtocolProof lam L.onlineBatch)

/-- The experiment over one hash function: the committer; the prover; the three arms, each through
its own coding; with the two logs of strings. -/
def exp3A (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (VT : OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (VL : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (VB : OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (mT mL mB : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) {St : Type}
    (Ct : OComp (rom lam) ((Dig lam × L.Rec) × St))
    (Pt : St → OComp (rom lam) (OutP3 lam L aT aL)) :
    OComp (rom lam) ((((Dig lam × L.Rec) × St) × Trace (rom lam)) ×
      (OutP3 lam L aT aL × Trace (rom lam)) × Bool × Bool × Bool) :=
  Ct.withTrace.bind fun a => (Pt a.1.2).withTrace.bind fun b =>
    ((VT (a.1.1.1, a.1.1.2, b.1.1)).overOne mT).bind fun vT =>
    ((VL (a.1.1.1, b.1.2.1.1, a.1.1.2, b.1.2.1.2.1, b.1.2.1.2.2)).overOne mL).bind fun vL =>
    ((VB (b.1.2.1.1, b.1.2.2.1, b.1.2.1.2.1, b.1.2.2.2)).overOne mB).bind fun vB =>
      OComp.pure (a, b, vT, vL, vB)

/-- the prover, then Test's proof string alone -/
def pr3T {St : Type} (Pt : St → OComp (rom lam) (OutP3 lam L aT aL)) (st : St) :
    OComp (rom lam) (OneProtocolProof lam (batTC L aT)) :=
  (Pt st).bind fun b => OComp.pure b.1

/-- the prover, then what the entry's arm takes -/
def pr3L {St : Type} (Pt : St → OComp (rom lam) (OutP3 lam L aT aL)) (st : St) :
    OComp (rom lam) (Out3 lam L aL) :=
  (Pt st).bind fun b => OComp.pure b.2.1

/-- committer and prover as one maker of what the proof's arm takes: the further root, the instance,
the further record, the session's proof string -/
def mk3B {St : Type} (Ct : OComp (rom lam) ((Dig lam × L.Rec) × St))
    (Pt : St → OComp (rom lam) (OutP3 lam L aT aL)) : OComp (rom lam) (OutBA lam L) :=
  Ct.bind fun a => (Pt a.2).bind fun b => OComp.pure (b.2.1.1, b.2.2.1, b.2.1.2.1, b.2.2.2)

section
variable {VT : OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
  {VL : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
  {VB : OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool} (hT : ∀ z, (VT z).NoCoin)
  (hL : ∀ z, (VL z).NoCoin) (hB : ∀ z, (VB z).NoCoin)
  (mT mL mB : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) {St : Type}
  (Ct : OComp (rom lam) ((Dig lam × L.Rec) × St)) (Pt : St → OComp (rom lam) (OutP3 lam L aT aL))

include hT hL hB

/-- At each function: an event on the committer's part and the key's arm's verdict is at most as
likely as in the key's arm's own experiment. -/
theorem exp3A_le_T (E : (((Dig lam × L.Rec) × St) × Trace (rom lam)) → Bool → Prop)
    (g : Fam (rom lam)) :
    PrCoins g (exp3A W VT VL VB mT mL mB Ct Pt) {x | E x.1 x.2.2.1} ≤
      PrCoins g (expT W VT mT Ct (pr3T Pt)) {x | E x.1 x.2.2} := by
  unfold PrCoins exp3A expT pr3T
  simp only [withTrace_map, OComp.bind_assoc, OComp.bind, OComp.runEager_bind, OComp.runEager]
  refine pr_bind_le_bind _ _ _ _ _ fun a _ => pr_bind_le_bind _ _ _ _ _ fun b _ => ?_
  rw [armT_overOne hT, arm_overOne hL, armB_overOne hB]
  simp only [PMF.pure_bind]
  exact pr_pure_le_pure fun h => h

/-- The same for the entry's arm. -/
theorem exp3A_le_L
    (E : (((Dig lam × L.Rec) × St) × Trace (rom lam)) → (Out3 lam L aL × Trace (rom lam)) → Bool →
      Prop) (g : Fam (rom lam)) :
    PrCoins g (exp3A W VT VL VB mT mL mB Ct Pt)
        {x | E x.1 (x.2.1.1.2.1, x.2.1.2) x.2.2.2.1} ≤
      PrCoins g (exp3 W VL mL Ct (pr3L Pt)) {x | E x.1 x.2.1 x.2.2} := by
  unfold PrCoins exp3A exp3 pr3L
  simp only [withTrace_map, OComp.bind_assoc, OComp.bind, OComp.runEager_bind, OComp.runEager]
  refine pr_bind_le_bind _ _ _ _ _ fun a _ => pr_bind_le_bind _ _ _ _ _ fun b _ => ?_
  rw [armT_overOne hT, arm_overOne hL, armB_overOne hB]
  simp only [PMF.pure_bind]
  exact pr_pure_le_pure fun h => h

/-- The same for the proof's arm: its maker's log is the committer's, then the prover's. -/
theorem exp3A_le_B (E : OutBA lam L × Trace (rom lam) → Bool → Prop) (g : Fam (rom lam)) :
    PrCoins g (exp3A W VT VL VB mT mL mB Ct Pt)
        {x | E ((x.2.1.1.2.1.1, x.2.1.1.2.2.1, x.2.1.1.2.1.2.1, x.2.1.1.2.2.2), x.1.2 ++ x.2.1.2)
          x.2.2.2.2} ≤
      PrCoins g (expB W VB mB (mk3B Ct Pt)) {x | E x.1 x.2} := by
  unfold PrCoins exp3A expB mk3B
  simp only [Rom.withTrace_bind, OComp.withTrace, OComp.bind_assoc, OComp.bind,
    OComp.runEager_bind, OComp.runEager, List.append_nil]
  refine pr_bind_le_bind _ _ _ _ _ fun a _ => pr_bind_le_bind _ _ _ _ _ fun b _ => ?_
  rw [armT_overOne hT, arm_overOne hL, armB_overOne hB]
  simp only [PMF.pure_bind]
  exact pr_pure_le_pure fun h => h

end

/-- The three arms in one experiment. All three accept, and what one of them promises fails of the
word y that the committer's own log of strings determines under the first root and the word y' that
both logs determine under the further root (read through mT), with probability at most the sum of
the three arms' bounds, each of the form n εs + 2 (n + 1)² / 2^lam: at n = 3 (tC + tP + 1 + tVT), at
n = 5 (tC + tP + 1 + tVL) and at n = 3 (tC + tP + tVB); tC bounds the committer's calls (hC) and tP
the prover's at every state (hP). The premises are those of `armT_pr_key` (hsT, hlT, hcT, `OKTA W`,
hbT, `IsArmT`), of `arm_pr_key` (hsL, hlL, hcL, `OKLA W`, hbL, `IsArm`, `HeadSeeds`) and of
`armB_pr_maker` (hsB, hlB, hco, `OKBA W`, hbB, `IsArmB`, `HeadSeedB`), at one `AnsOK cA`, one
`S.Law εs` and lam not 0; and mL and mB agree with mT on the leaf and node oracles (`SameTrees`). -/
theorem three_arms_holds {Wn : Type} (Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
    {VT : OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {VL : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {VB : OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)} {r₀ : L.Rec}
    {εT : Err L.offline.shape} {εL : Err L.link.shape} {εB : Err L.onlineBatch.loc.shape} {εs : ℝ≥0∞}
    (hsT : L.offline.Sound (fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) εT)
    (hlT : L.offline.IsLocal) (hcT : aT.Coherent) (hWT : OKTA W)
    (hbT : Err.Below (Err.timesShared (2 ^ W.depthReqT) aT εT) εs) (hVT : IsArmT W S cA VT)
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hcL : aL.Coherent) (hWL : OKLA W)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs) (hVL : IsArm W S cA VL)
    (hHL : HeadSeeds W S VL)
    (hsB : ∀ rec, (L.batAt rec).SndBKT L.maxBatchSize L.early L.late (L.relB Rno rec)
      (fun x y τ => wit (x, rec) y τ) εB)
    (hlB : L.onlineBatch.loc.IsLocal) (hco : L.onlineBatch.ann.Coherent) (hWB : OKBA W) (hbB : Err.Below εB εs)
    (hVB : IsArmB W S cA r₀ VB) (hHB : HeadSeedB W S VB)
    (hA : AnsOK cA) (hSd : S.Law εs) (hlam : 0 < lam)
    (mT mL mB : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (hmL : SameTrees W mT mL)
    (hmB : SameTrees W mT mB) {St : Type} (Ct : OComp (rom lam) ((Dig lam × L.Rec) × St))
    (Pt : St → OComp (rom lam) (OutP3 lam L aT aL))
    (tC tP : ℕ) (hC : Ct.QueryBound tC) (hP : ∀ st, (Pt st).QueryBound tP) :
    Rom.Pr (exp3A W VT VL VB mT mL mB Ct Pt)
        (fun _ => {x | x.2.2.1 = true ∧ x.2.2.2.1 = true ∧ x.2.2.2.2 = true ∧
          ¬ (KeyHoldsAt L (extEnc W (singleTr mT x.1.2) x.1.1.1.1) x.1.1.1.2 ∧
            LinkHoldsAt L (extEnc W (singleTr mT x.1.2) x.1.1.1.1)
              (extEnc W (singleTr mT (x.1.2 ++ x.2.1.2)) x.2.1.1.2.1.1) x.1.1.1.2
              x.2.1.1.2.1.2.1 ∧
            ProofHoldsAt L (fun i x => ∃ w, Rno i x w)
              (extEnc W (singleTr mT (x.1.2 ++ x.2.1.2)) x.2.1.1.2.1.1) x.2.1.1.2.2.1
              x.2.1.1.2.1.2.1)}) ≤
      ((((tC + tP + 1 + tVT W) * (1 + 2) : ℕ) : ℝ≥0∞) * εs +
        2 * (((tC + tP + 1 + tVT W) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam) +
      (((((tC + tP + 1 + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((tC + tP + 1 + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam) +
      ((((tC + tP + tVB W) * (1 + 2) : ℕ) : ℝ≥0∞) * εs +
        2 * (((tC + tP + tVB W) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam)) := by
  have hnT : ∀ z, (VT z).NoCoin := fun z => noCoin_of_detBound (hVT.det z)
  have hnL : ∀ z, (VL z).NoCoin := fun z => noCoin_of_detBound (hVL.det z)
  have hnB : ∀ z, (VB z).NoCoin := fun z => noCoin_of_detBound (hVB.det z)
  have hPT : ∀ st, (pr3T Pt st).QueryBound tP := fun st => by
    have h : (pr3T Pt st).QueryBound (tP + 0) := (hP st).bind fun _ => trivial
    exact h
  have hPL : ∀ st, (pr3L Pt st).QueryBound tP := fun st => by
    have h : (pr3L Pt st).QueryBound (tP + 0) := (hP st).bind fun _ => trivial
    exact h
  have hMk : (mk3B Ct Pt).QueryBound (tC + tP) := by
    have h : (mk3B Ct Pt).QueryBound (tC + (tP + 0)) :=
      hC.bind fun a => (hP a.2).bind fun _ => trivial
    exact h
  have bT := armT_pr_key hsT hlT hcT hWT hA hSd hbT hVT hlam mT Ct (pr3T Pt) tC tP hC hPT
  have bL := arm_pr_key hsL hlL hcL hWL hA hSd hbL hVL hHL hlam mL Ct (pr3L Pt) tC tP hC hPL
  have bB := armB_pr_maker Rno wit hsB hlB hco hWB hA hSd hbB hVB hHB hlam mB (mk3B Ct Pt)
    (tC + tP) hMk
  -- the three events, on the one experiment
  have cT : Rom.Pr (exp3A W VT VL VB mT mL mB Ct Pt)
      (fun _ => {x | x.2.2.1 = true ∧
        ¬ KeyHoldsAt L (extEnc W (singleTr mT x.1.2) x.1.1.1.1) x.1.1.1.2}) ≤ _ :=
    le_trans (MeasureTheory.lintegral_mono fun g =>
      exp3A_le_T hnT hnL hnB mT mL mB Ct Pt
        (fun a v => v = true ∧ ¬ KeyHoldsAt L (extEnc W (singleTr mT a.2) a.1.1.1) a.1.1.2) g) bT
  have cL : Rom.Pr (exp3A W VT VL VB mT mL mB Ct Pt)
      (fun _ => {x | x.2.2.2.1 = true ∧
        ¬ LinkHoldsAt L (extEnc W (singleTr mL x.1.2) x.1.1.1.1)
          (extEnc W (singleTr mL (x.1.2 ++ x.2.1.2)) x.2.1.1.2.1.1) x.1.1.1.2
          x.2.1.1.2.1.2.1}) ≤ _ :=
    le_trans (MeasureTheory.lintegral_mono fun g =>
      exp3A_le_L hnT hnL hnB mT mL mB Ct Pt
        (fun a b v => v = true ∧
          ¬ LinkHoldsAt L (extEnc W (singleTr mL a.2) a.1.1.1)
            (extEnc W (singleTr mL (a.2 ++ b.2)) b.1.1) a.1.1.2 b.1.2.1) g) bL
  have cB : Rom.Pr (exp3A W VT VL VB mT mL mB Ct Pt)
      (fun _ => {x | x.2.2.2.2 = true ∧
        ¬ ProofHoldsAt L (fun i x => ∃ w, Rno i x w)
          (extEnc W (singleTr mB (x.1.2 ++ x.2.1.2)) x.2.1.1.2.1.1) x.2.1.1.2.2.1
          x.2.1.1.2.1.2.1}) ≤ _ :=
    le_trans (MeasureTheory.lintegral_mono fun g =>
      exp3A_le_B hnT hnL hnB mT mL mB Ct Pt
        (fun o v => v = true ∧
          ¬ ProofHoldsAt L (fun i x => ∃ w, Rno i x w) (extEnc W (singleTr mB o.2) o.1.1) o.1.2.1
            o.1.2.2.1) g) bB
  rw [Pr_eq_law] at cT cL cB ⊢
  refine le_trans ?_ (add_le_add cT (add_le_add cL cB))
  refine le_trans (pr_mono _ ?_)
    (le_trans (pr_union_le _ _ _) (add_le_add le_rfl (pr_union_le _ _ _)))
  rintro x ⟨h1, h2, h3, h4⟩
  by_cases hk : KeyHoldsAt L (extEnc W (singleTr mT x.1.2) x.1.1.1.1) x.1.1.1.2
  · refine Or.inr ?_
    by_cases hl : LinkHoldsAt L (extEnc W (singleTr mT x.1.2) x.1.1.1.1)
        (extEnc W (singleTr mT (x.1.2 ++ x.2.1.2)) x.2.1.1.2.1.1) x.1.1.1.2 x.2.1.1.2.1.2.1
    · refine Or.inr ⟨h3, fun hp => h4 ⟨hk, hl, ?_⟩⟩
      rw [extEnc_codings hlam hmB]
      exact hp
    · refine Or.inl ⟨h2, fun hl' => hl ?_⟩
      rw [extEnc_codings hlam hmL, extEnc_codings hlam hmL]
      exact hl'
  · exact Or.inl ⟨h1, hk⟩

/-- All three arms accept, and the word that the committer's own log of strings determines under the
first root (read through mT) does not decode, with the committer's record, to an index for which the
instance that the prover names has a witness: with probability at most the sum of three bounds,
each of the form n εs + 2 (n + 1)² / 2^lam: at n = 3 (tC + tP + 1 + tVT), at
n = 5 (tC + tP + 1 + tVL) and at n = 3 (tC + tP + tVB); tC bounds the committer's calls (hC) and tP
the prover's at every state (hP). The premises are those of `armT_pr_key` (hsT, hlT, hcT, `OKTA W`,
hbT, `IsArmT`), of `arm_pr_key` (hsL, hlL, hcL, `OKLA W`, hbL, `IsArm`, `HeadSeeds`) and of
`armB_pr_maker` (hsB, hlB, hco, `OKBA W`, hbB, `IsArmB`, `HeadSeedB`), at one `AnsOK cA`, one
`S.Law εs` and lam not 0; and mL and mB agree with mT on the leaf and node oracles (`SameTrees`). -/
theorem three_arms {Wn : Type} (Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
    {VT : OutTA lam L aT → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {VL : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {VB : OutBA lam L → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)} {r₀ : L.Rec}
    {εT : Err L.offline.shape} {εL : Err L.link.shape} {εB : Err L.onlineBatch.loc.shape} {εs : ℝ≥0∞}
    (hsT : L.offline.Sound (fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) εT)
    (hlT : L.offline.IsLocal) (hcT : aT.Coherent) (hWT : OKTA W)
    (hbT : Err.Below (Err.timesShared (2 ^ W.depthReqT) aT εT) εs) (hVT : IsArmT W S cA VT)
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hcL : aL.Coherent) (hWL : OKLA W)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs) (hVL : IsArm W S cA VL)
    (hHL : HeadSeeds W S VL)
    (hsB : ∀ rec, (L.batAt rec).SndBKT L.maxBatchSize L.early L.late (L.relB Rno rec)
      (fun x y τ => wit (x, rec) y τ) εB)
    (hlB : L.onlineBatch.loc.IsLocal) (hco : L.onlineBatch.ann.Coherent) (hWB : OKBA W) (hbB : Err.Below εB εs)
    (hVB : IsArmB W S cA r₀ VB) (hHB : HeadSeedB W S VB)
    (hA : AnsOK cA) (hSd : S.Law εs) (hlam : 0 < lam)
    (mT mL mB : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) (hmL : SameTrees W mT mL)
    (hmB : SameTrees W mT mB) {St : Type} (Ct : OComp (rom lam) ((Dig lam × L.Rec) × St))
    (Pt : St → OComp (rom lam) (OutP3 lam L aT aL))
    (tC tP : ℕ) (hC : Ct.QueryBound tC) (hP : ∀ st, (Pt st).QueryBound tP) :
    Rom.Pr (exp3A W VT VL VB mT mL mB Ct Pt)
        (fun _ => {x | x.2.2.1 = true ∧ x.2.2.2.1 = true ∧ x.2.2.2.2 = true ∧
          ¬ ∃ i, L.decodeIndex (extEnc W (singleTr mT x.1.2) x.1.1.1.1) x.1.1.1.2 = some i ∧
            ∃ w, Rno i x.2.1.1.2.2.1 w}) ≤
      ((((tC + tP + 1 + tVT W) * (1 + 2) : ℕ) : ℝ≥0∞) * εs +
        2 * (((tC + tP + 1 + tVT W) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam) +
      (((((tC + tP + 1 + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((tC + tP + 1 + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam) +
      ((((tC + tP + tVB W) * (1 + 2) : ℕ) : ℝ≥0∞) * εs +
        2 * (((tC + tP + tVB W) * (1 + 2) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam)) := by
  refine le_trans ?_ (three_arms_holds Rno wit hsT hlT hcT hWT hbT hVT hsL hlL hcL hWL hbL hVL hHL
    hsB hlB hco hWB hbB hVB hHB hA hSd hlam mT mL mB hmL hmB Ct Pt tC tP hC hP)
  rw [Pr_eq_law, Pr_eq_law]
  refine pr_mono _ ?_
  rintro x ⟨h1, h2, h3, h4⟩
  exact ⟨h1, h2, h3, fun h => h4 (holds_three h.1 h.2.1 h.2.2)⟩

end TypedOracleCompiler.Compile.Batch.Cms
