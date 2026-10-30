-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/KeyAns.lean: the key's arm of the compiled verifier with records, with the
answers alone in the first query: the like of LinkAns.lean for Test and one root.

The key's arm recomputes the seed of one table from its root, compares it with the record's seed,
and runs the compiled Test on the root and the record. The first query of Test's chain holds the
root and a code of the record's answers (`cmsTA`, CmsAns.lean), and nothing of the seed. So the
first query determines the instance of Test only together with the trace: the seed of the root is
what the root's two seed queries have given. The lane (`laneTA`, CmsAns.lean) reads the answers off
the list and the seed off the trace so far. That is a fixed instance along a chain only if the seed
queries of the root stand before the chain's first query. So the theorem of this file is on traces
that have that order (`SeedsFirstT`) and hold the answers of one family of oracle functions.

Main names:
  `OKTA W`: what the arm asks of the wires.
  `KeyHoldsAt`, `KeyHolds`: what the arm promises: the record's seed is no collision seed of the
    word, and word and record decode to something.
  `OutTA`, `VTA`, `VTA'`, `tVT`: what a maker puts out; the arm with the strict and with the lax
    Test; a bound on its typed queries.
  `BadTA`, `badTA_mono`, `badTA_rare`: the set of traces outside which the arm is sound: a hash
    event, the event of Test's lane, or the seed's; it is never undone; it is rare.
  `SeedsFirstT`: before each first query of a chain of Test stand the seed queries of its root.
  `testA_key`: Test's clause outside the hash events and the event of Test's lane.
  `testA_sound'`, `testA_sound`: the theorem at the lax Test with the seed's test, and at `VTA`.
  `yes_VTA`, `yes_VTA'`: what a yes of either arm holds. `detBound_VTA`, `detBound_VTA'`: a bound on
    an arm's queries; it draws no coin.

The proofs are those of LinkAns.lean, and of Test's clause in `cmsA_bcs` (CmsAns.lean), with idle
lanes in the place of Link's and of the session's.

Limits: soundness alone; typed oracles; traces with the order and one family's answers. Test's
soundness round by round is a premise. No statement in probabilities joins `badTA_rare` and
`testA_sound'` here. That the laws of the whole verifier's wires (`OKA`, CmsAns.lean) give `OKTA` is
plain from the fields and is not stated. The limits in the head of KeyAnsPr.lean hold of this file
too.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.CmsAns

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam))

/-- What the key's arm asks of the wires. -/
structure OKTA : Prop where
  /-- the laws of Test's wire -/
  T : (wTC W).OKG
  /-- the wire by which the word under a root is built -/
  ext : W.B.ext.OK
  prjE_emb : ∀ s, W.prjE (W.embE s) = some s
  prjT_emb : ∀ p a, W.prjT p (W.embT p a) = some a
  extDepth : W.T.ext.depth = W.depth
  extT : ∀ p, W.T.ext.which p = 0 ∧ W.T.ext.leaf p = p.val

/-- What the key's arm promises, said of a word and a record: the record's seed is no collision seed
of the word, and word and record decode to something. -/
def KeyHoldsAt (L : HolographicProtocol I X) (y : Fin L.wordLength → L.Symbol) (rec : L.Rec) : Prop :=
  ¬ L.hasCollisionAt y rec.1 ∧ L.decodeIndex y rec ≠ none

/-- What the key's arm promises of a trace, a root and a record. -/
def KeyHolds (tr : Tc W) (cm : Dig lam) (rec : L.Rec) : Prop :=
  KeyHoldsAt L (extEnc W tr cm) rec

/-- what a maker puts out: a root, a record, Test's proof string -/
abbrev OutTA (lam : ℕ) (L : HolographicProtocol I X) (aT : RoundSplits L.offline.shape) : Type :=
  Dig lam × L.Rec × OneProtocolProof lam (batTC L aT)

/-- The key's arm with the strict Test. -/
def VTA (p : Params) (cm : Dig lam) (rec : L.Rec) (π : OneProtocolProof lam (batTC L aT)) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  (outOfDomainSeedIs W S cm rec.1).bind fun s0 =>
  (verifyOfflineProof W cA p cm rec π).bind fun b =>
  OComp.pure (s0 && b)

/-- The same arm with the lax Test. -/
def VTA' (cm : Dig lam) (rec : L.Rec) (π : OneProtocolProof lam (batTC L aT)) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  (outOfDomainSeedIs W S cm rec.1).bind fun s0 =>
  (vTA' W cA cm rec π).bind fun b =>
  OComp.pure (s0 && b)

/-- a bound on the number of typed queries of the key's arm -/
def tVT : ℕ := 2 + tVQB (wTC W) W.depthReqT

/-- The set of traces outside which the key's arm is sound. This is said under the hypotheses that
stand in the statement itself, which this comment does not list; it is no claim that they hold. -/
def BadTA (εT : Err L.offline.shape) (tr : Tc W) : Prop :=
  (EM tr ∨ EF tr) ∨ StepEvent (fun pre e =>
    stepS W (laneTA W S cA εT) (laneNil W Tag.link) (laneNil W Tag.onl) pre e ∨
      stepSeed W S pre e) tr

variable {W S cA}

/-- A trace in `BadTA` stays in it when entries are appended. -/
theorem badTA_mono {εT : Err L.offline.shape} {tr : Tc W} (tr' : Tc W) (h : BadTA W S cA εT tr) :
    BadTA W S cA εT (tr ++ tr') := by
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl (h.append tr'))
  · exact Or.inl (Or.inr (h.append tr'))
  · exact Or.inr (StepEvent.append h tr')

/-- An algorithm with at most t queries ends in `BadTA` with probability at most
t εs + 2 (t + 1)² / 2^lam, under the law of lazy sampling. Premises: the seed's law at εs
(`S.Law εs`), the bound on the rounds' errors (hbT), the laws of Test's wire (hW). -/
theorem badTA_rare {εT : Err L.offline.shape} {εs : ℝ≥0∞} (hSd : S.Law εs)
    (hbT : Err.Below (Err.timesShared (2 ^ W.depthReqT) aT εT) εs) (hW : (wTC W).OKG) {β : Type}
    (A : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) β) (t : ℕ) (hA : A.QueryBound t) :
    pr A.withTrace.law {o | BadTA W S cA εT o.2} ≤
      (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  have h := pr_stepEvent_le (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))
    (fun pre e =>
      stepS W (laneTA W S cA εT) (laneNil W Tag.link) (laneNil W Tag.onl) pre e ∨
        stepSeed W S pre e)
    (fun _ => εs)
    (fun pre e he hs => hs.elim
      (fun hs => hs.elim (fun h1 => h1.1 he) fun h1 =>
        h1.elim (fun h2 => h2.1 he) fun h2 => h2.1 he)
      fun h1 => h1.1 he)
    (fun pre o q _ => pr_step4_le W S rfl rfl rfl rfl rfl rfl (laneTA_ok W S cA εT hW)
      (laneNil_ok W Tag.link _) (laneNil_ok W Tag.onl _) hbT trivial trivial hSd pre o q) A t hA
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  calc
    pr A.withTrace.law {o | BadTA W S cA εT o.2} ≤
        pr A.withTrace.law {o | EM o.2 ∨ EF o.2} +
          pr A.withTrace.law
            {o | StepEvent (fun pre e =>
              stepS W (laneTA W S cA εT) (laneNil W Tag.link) (laneNil W Tag.onl) pre e ∨
                stepSeed W S pre e) o.2} :=
      pr_union_le _ _ _
    _ ≤ 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam + (t : ℝ≥0∞) * εs := add_le_add (hashEvents A t hA) h
    _ ≤ (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
        rw [add_comm]
        gcongr
        exact Nat.le_succ t

variable (W S)

/-- The order: before each first query of a chain of Test (round 0, a head (F1)) stand the seed
queries of the first entry of its list. -/
def SeedsFirstT (tr : Tc W) : Prop :=
  ∀ (pre : Tc W) (q : FbIn lam (typedOracleCarrier L Bd aT aL) Tag.test) (a : FsAns lam W.K) (post : Tc W)
    (cms : List (Dig lam)) (x : Option L.XC) (salt : Bits),
    tr = pre ++ fbE Tag.test q a :: post → q.round = 0 → q.head = Head.f1 cms x salt →
    ∀ c ∈ cms.take 1, SeedAsked W S pre c

variable {W S}

/-- Test's clause. On a trace tr that holds the answers of one family g of oracle functions (hg) and
has the order (`SeedsFirstT`), outside E_M, E_F and the event of Test's lane, in which the test of
the seed and the lax Test run and say yes: the record's seed is a collision seed of the word, or
word and record decode to something. Premises: Test is sound round by round, with the errors εT, for
that language (hsT); Test's verifier is local (hlT); the annotation aT is coherent (hcT); the wires
that Test reads have their laws (`OKTA W`); the code of the answers is one to one, with one length
(`AnsOK cA`; the length is not read by this arm). -/
theorem testA_key {εT : Err L.offline.shape}
    (hsT : L.offline.Sound (fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) εT)
    (hlT : L.offline.IsLocal) (hcT : aT.Coherent) (hW : OKTA W) (hA : AnsOK cA) {tr : Tc W}
    {g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))} (hg : ∀ e ∈ tr, e.2.2 = g e.1 e.2.1)
    (hfirst : SeedsFirstT W S tr) {cm : Dig lam} {rec : L.Rec} {π : OneProtocolProof lam (batTC L aT)}
    (hM : ¬ EM tr) (hF : ¬ EF tr) (hS : ¬ StepEvent (laneTA W S cA εT).step tr)
    (hs0 : RunsIn tr (outOfDomainSeedIs W S cm rec.1) true) (hrun : RunsIn tr (vTA' W cA cm rec π) true) :
    L.hasCollisionAt (extEnc W tr cm) rec.1 ∨ L.decodeIndex (extEnc W tr cm) rec ≠ none :=
  mem_of_accepted_at Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none)
    W.embE hW.T hlT hcT
    (Lg := fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none)
    (stTA W S cA εT) W.prjT hW.prjT_emb some (fun _ => rfl)
    (Err.timesShared (2 ^ W.depthReqT) aT εT) hM hF
    hS
    (cmsTA cA cm rec.2) rec π (extEnc W tr cm)
    (fun _ => stOf L.offline εT (extEnc W tr cm) rec)
    (fun _ _ h => absurd rfl h)
    (fun hL => stOf_start hsT _ rec hL)
    (fun τ m _ h => stOf_prover _ rec τ m h)
    (fun τ _ h => stOf_full _ rec τ h) hrun
    (fun pre q a post l cur htr hours => by
      have hsub : pre ⊆ tr := fun e he => by rw [htr]; exact List.mem_append_left _ he
      -- the seed queries of the root stand in the trace before this query
      have hsd : ∀ c ∈ (cmsTA cA cm rec.2).take 1, SeedAsked W S pre c := by
        rcases ours_first0 _ hours with ⟨⟨salt, hq⟩, hr⟩ | ⟨q1, a1, salt, hm, hq, hr⟩
        · exact hfirst pre q a post _ _ salt htr hr hq
        · obtain ⟨p1, p2, hp⟩ := List.append_of_mem hm
          intro c hc
          refine (hfirst p1 q1 a1 (p2 ++ fbE Tag.test q a :: post) _ _ salt ?_ hr hq c
            hc).mono ?_
          · rw [htr, hp]
            simp
          · intro e he
            rw [hp]
            exact List.mem_append_left _ he
      have e1 : seedIn W S pre cm = some rec.1 :=
        seedIn_of_run hg hsub (hsd cm (by simp [cmsTA])) hs0
      have e4 : extEnc W pre cm = extEnc W tr cm :=
        extEnc_before htr hM (ours_cms _ a hours _ (by simp [cmsTA]))
      show ((seedIn W S pre cm).bind fun s =>
          (ansOutT cA (cmsTA cA cm rec.2)).map fun an => (s, an)).map
        (stOf L.offline εT (extEnc W pre cm)) = _
      rw [e1, ansOutT_cmsTA hA, e4]
      rfl)
    (fun p a sl h => by
      change extLeaf tr W.T.ext.depth ((cmsTA cA cm rec.2).getD (W.T.ext.which p) default)
        (W.T.ext.leaf p) = _ at h
      rw [hW.extDepth, (hW.extT p).1, (hW.extT p).2] at h
      have h' : extLeaf tr W.depth cm p.val = some ⟨W.embE a, sl⟩ := h
      exact hW.ext.build_rd _ p a (by rw [h']; exact hW.prjE_emb a))

/-- The key's arm is sound, at the lax Test. On a trace tr that holds the answers of one family g of
oracle functions (hg), has the order (`SeedsFirstT`) and lies outside `BadTA`, in which the test of
the seed and the lax Test run and say yes: the seed is no collision seed of the word, and word and
record decode to something. The premises are those of `testA_key`. -/
theorem testA_sound' {εT : Err L.offline.shape}
    (hsT : L.offline.Sound (fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) εT)
    (hlT : L.offline.IsLocal) (hcT : aT.Coherent) (hW : OKTA W) (hA : AnsOK cA) {tr : Tc W}
    {g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))} (hg : ∀ e ∈ tr, e.2.2 = g e.1 e.2.1)
    (hfirst : SeedsFirstT W S tr) {cm : Dig lam} {rec : L.Rec} {π : OneProtocolProof lam (batTC L aT)}
    (hB : ¬ BadTA W S cA εT tr) (hs0 : RunsIn tr (outOfDomainSeedIs W S cm rec.1) true)
    (hrun : RunsIn tr (vTA' W cA cm rec π) true) : KeyHolds W tr cm rec := by
  have hM : ¬ EM tr := fun h => hB (Or.inl (Or.inl h))
  have hF : ¬ EF tr := fun h => hB (Or.inl (Or.inr h))
  have hc0 : ¬ L.hasCollisionAt (extEnc W tr cm) rec.1 := seed_not_coll' hM hF (fun h => hB (Or.inr h)) hs0
  have key := testA_key hsT hlT hcT hW hA hg hfirst hM hF
    (fun ⟨pre, e, post, h1, h2⟩ => hB (Or.inr ⟨pre, e, post, h1, Or.inl (Or.inl h2)⟩)) hs0 hrun
  exact ⟨hc0, key.resolve_left hc0⟩

/-- A yes of the arm with the strict Test holds the yes of the seed's test and of the lax Test, at a
proof string that may differ in its paths' form. Premise: the laws of Test's wire (hT). -/
theorem yes_VTA (hT : (wTC W).OKG) (p : Params) {tr : Tc W} {cm : Dig lam} {rec : L.Rec}
    {π : OneProtocolProof lam (batTC L aT)} (hrun : RunsIn tr (VTA W S cA p cm rec π) true) :
    RunsIn tr (outOfDomainSeedIs W S cm rec.1) true ∧ ∃ π', RunsIn tr (vTA' W cA cm rec π') true := by
  unfold VTA at hrun
  simp only [runsIn_bind_iff, runsIn_pure_iff] at hrun
  obtain ⟨s0, hs0, b, hb, habc⟩ := hrun
  simp only [Bool.and_eq_true] at habc
  obtain ⟨rfl, rfl⟩ := habc
  obtain ⟨_, _, hb'⟩ := runsIn_verifyB_of_strict hT hb
  exact ⟨hs0, _, hb'⟩

/-- The same of the arm with the lax Test. -/
theorem yes_VTA' {tr : Tc W} {cm : Dig lam} {rec : L.Rec} {π : OneProtocolProof lam (batTC L aT)}
    (hrun : RunsIn tr (VTA' W S cA cm rec π) true) :
    RunsIn tr (outOfDomainSeedIs W S cm rec.1) true ∧ ∃ π', RunsIn tr (vTA' W cA cm rec π') true := by
  unfold VTA' at hrun
  simp only [runsIn_bind_iff, runsIn_pure_iff] at hrun
  obtain ⟨s0, hs0, b, hb, habc⟩ := hrun
  simp only [Bool.and_eq_true] at habc
  obtain ⟨rfl, rfl⟩ := habc
  exact ⟨hs0, _, hb⟩

/-- The key's arm is sound, at `VTA`: the conclusion of `testA_sound'` from a yes of `VTA`. The
premises are those of `testA_key`. -/
theorem testA_sound {εT : Err L.offline.shape}
    (hsT : L.offline.Sound (fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none) εT)
    (hlT : L.offline.IsLocal) (hcT : aT.Coherent) (hW : OKTA W) (hA : AnsOK cA) (p : Params)
    {tr : Tc W} {g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))}
    (hg : ∀ e ∈ tr, e.2.2 = g e.1 e.2.1) (hfirst : SeedsFirstT W S tr) {cm : Dig lam}
    {rec : L.Rec} {π : OneProtocolProof lam (batTC L aT)} (hB : ¬ BadTA W S cA εT tr)
    (hrun : RunsIn tr (VTA W S cA p cm rec π) true) : KeyHolds W tr cm rec :=
  let ⟨hs0, _, hb⟩ := yes_VTA hW.T p hrun
  testA_sound' hsT hlT hcT hW hA hg hfirst hB hs0 hb

variable (W S cA)

/-- The arm with the lax Test draws no coin and asks at most `tVT W` queries. -/
theorem detBound_VTA' (cm : Dig lam) (rec : L.Rec) (π : OneProtocolProof lam (batTC L aT)) :
    DetBound (VTA' W S cA cm rec π) (tVT W) := by
  unfold VTA' tVT
  refine ((detBound_seedIs W S _ _).bind (t := tVQB (wTC W) W.depthReqT + 0) fun _ =>
    (detBound_verifyB _ _ _ _ _ _ _ _ _ _ _).bind (t := 0) fun _ => detBound_pure _ _).mono ?_
  omega

/-- The arm with the strict Test draws no coin and asks at most `tVT W` queries. -/
theorem detBound_VTA (p : Params) (cm : Dig lam) (rec : L.Rec) (π : OneProtocolProof lam (batTC L aT)) :
    DetBound (VTA W S cA p cm rec π) (tVT W) := by
  unfold VTA tVT
  refine ((detBound_seedIs W S _ _).bind (t := tVQB (wTC W) W.depthReqT + 0) fun _ =>
    (detBound_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _).bind (t := 0) fun _ => detBound_pure _ _).mono ?_
  omega

end TypedOracleCompiler.Compile.Batch.Cms
