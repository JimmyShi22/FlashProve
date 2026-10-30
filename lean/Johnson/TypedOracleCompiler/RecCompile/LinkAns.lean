-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/LinkAns.lean: the entry's arm with the answers alone in the first query.

A record is a seed with answers. In LinkOnly.lean the first query of Link's chain holds the two
roots and a code of the two whole records. Here the first query holds the two roots and a code of
the two records' answers (`cmsLA`), and nothing of the seeds, which the verifier recomputes from the
roots. That is meant to follow the programs; the tie is the coding's matter.

Then the first query does not determine the instance of Link by itself. It does so together with
the trace: the seed of a root is what the root's two seed queries (Seeds.lean) have given. So the
lane (`laneLA`) reads the answers off the list and the seeds off the trace so far (`seedIn`). That
is a fixed instance along a chain only if the seed queries of the two roots stand before the chain's
first query. A cheating prover need not ask in that order, and to ask late is no rare event. So this
file's theorem is on traces that have the order (`SeedsFirst`) and hold the answers of one family of
oracle functions. LinkAnsPr.lean lifts both conditions, for every algorithm, at a price on the
number of queries.

  `AnsOK cA`       the code of the answers is one to one, and all codes have one length
  `OKLA W`, `OKL.toA`   what is asked of the wires; the laws `OKL` of LinkOnly.lean give it
  `cmsLA`, `verifyLinkProof`, `vLA'`, `VLA`, `VLA'`   the list; the compiled Link, strict and lax; the entry's
                   arm with the one and with the other
  `seedIn`         the seed that a root's two seed queries have given in a trace
  `laneLA`, `BadLA`, `badLA_mono`, `badLA_rare`   the lane; the set of traces; as in LinkOnly.lean
  `SeedsFirst`     before each first query of a chain of Link stand the seed queries of its two
                   roots
  `linkA_key`      Link's clause outside E_M, E_F and the event of Link's lane
  `linkA_sound'`   the theorem at the lax Link and the two seeds' tests
  `linkA_sound`    the theorem at `VLA`
  `yes_VLA`, `yes_VLA'`   what a yes of either arm holds
  `detBound_VLA`, `detBound_VLA'`   a bound on an arm's queries; it draws no coin

Limits: soundness alone; typed oracles. The limits in the head of LinkAnsPr.lean hold of this file
too.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.LinkOnly
import Johnson.TypedOracleCompiler.RecCompile.LaneAt
import Johnson.TypedOracleCompiler.RecCompile.First0

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- What is asked of the code of a record's answers. -/
structure AnsOK (cA : L.OutOfDomainAnswer → List (Dig lam)) : Prop where
  inj : Function.Injective cA
  /-- all answers are written with one number of digests: so two in a row can be told apart -/
  len : ∀ a a', (cA a).length = (cA a').length

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam))

/-- What the entry's arm asks of the wires: `OKL` (LinkOnly.lean) without the laws of the code of a
whole record, which this arm does not read. -/
structure OKLA : Prop where
  /-- the laws of Link's wire -/
  Lk : (wLC W).OKG
  /-- the wire by which the word under a root is built -/
  ext : W.B.ext.OK
  prjE_emb : ∀ s, W.prjE (W.embE s) = some s
  prjL_emb : ∀ p a, W.prjL p (W.embL p a) = some a
  extDepth : W.Lk.ext.depth = W.depth
  extL : (∀ p, W.Lk.ext.which (.inl p) = 0 ∧ W.Lk.ext.leaf (.inl p) = p.val) ∧
    ∀ p, W.Lk.ext.which (.inr p) = 1 ∧ W.Lk.ext.leaf (.inr p) = p.val

/-- The laws `OKL W S` of LinkOnly.lean give `OKLA W`: the field on the record's code is dropped. -/
theorem OKL.toA {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
    (h : OKL W S) : OKLA W :=
  ⟨h.Lk, h.ext, h.prjE_emb, h.prjL_emb, h.extDepth, h.extL⟩

/-- the list that a link's chain is handed: the two roots, then the answers of the two records -/
def cmsLA (cm cm' : Dig lam) (an an' : L.OutOfDomainAnswer) : List (Dig lam) := cm :: cm' :: (cA an ++ cA an')

/-- The compiled Link, with the answers alone in the list. -/
def verifyLinkProof (p : Params) (cm cm' : Dig lam) (rec rec' : L.Rec) (π : OneProtocolProof lam (batLC L aL)) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  verifyOneProtocol p.sMT p.sFS Tag.link (batLC L aL) (wLC W) W.embL id (fun _ => none) W.embE W.depthReqL
    (cmsLA cA cm cm' rec.2 rec'.2) (rec, rec') π

/-- The same without the strict format: the lax Link, which `VLA'` and `armL` (LinkAnsPr.lean)
run. -/
def vLA' (cm cm' : Dig lam) (rec rec' : L.Rec) (π : OneProtocolProof lam (batLC L aL)) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  verifyB Tag.link (batLC L aL) (wLC W) W.embL id (fun _ => none) W.embE W.depthReqL
    (cmsLA cA cm cm' rec.2 rec'.2) (rec, rec') π

/-- The entry's arm of the verifier: the two seeds, the compiled Link, then the conjunction. -/
def VLA (p : Params) (cm cm' : Dig lam) (rec rec' : L.Rec) (π : OneProtocolProof lam (batLC L aL)) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  (outOfDomainSeedIs W S cm rec.1).bind fun s0 =>
  (outOfDomainSeedIs W S cm' rec'.1).bind fun s1 =>
  (verifyLinkProof W cA p cm cm' rec rec' π).bind fun b =>
  OComp.pure (s0 && s1 && b)

/-- The same arm with the lax Link. -/
def VLA' (cm cm' : Dig lam) (rec rec' : L.Rec) (π : OneProtocolProof lam (batLC L aL)) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  (outOfDomainSeedIs W S cm rec.1).bind fun s0 =>
  (outOfDomainSeedIs W S cm' rec'.1).bind fun s1 =>
  (vLA' W cA cm cm' rec rec' π).bind fun b =>
  OComp.pure (s0 && s1 && b)

/-! ## What is read off a trace and off the list -/

/-- the two seed queries of the root c have been asked in the trace -/
def SeedAsked (pre : Tc W) (c : Dig lam) : Prop :=
  ∃ aa : FsAns lam W.K × FsAns lam W.K,
    fbE S.t (seedQ0 W S c) aa.1 ∈ pre ∧ fbE S.t (seedQ1 W S (link aa.1)) aa.2 ∈ pre

open Classical in
/-- the seed that the two seed queries of a root have given in a trace; none if they are not there;
where a trace holds several answers, one is picked by choice -/
def seedIn (pre : Tc W) (c : Dig lam) : Option L.OutOfDomainSeed :=
  if h : SeedAsked W S pre c then some (S.seed (Classical.choose h).2.1) else none

variable {W S}

/-- In a part of a trace with one family's answers: if the seed queries of a root stand in the part,
and the verifier's test of the seed s runs in the whole, the seed read off the part is s. -/
theorem seedIn_of_run {g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))} {tr pre : Tc W}
    (hg : ∀ e ∈ tr, e.2.2 = g e.1 e.2.1) (hsub : pre ⊆ tr) {c : Dig lam} {s : L.OutOfDomainSeed}
    (h : SeedAsked W S pre c) (hs : RunsIn tr (outOfDomainSeedIs W S c s) true) :
    seedIn W S pre c = some s := by
  obtain ⟨a0, a1, m0, m1, rfl⟩ := runsIn_seedIs hs
  unfold seedIn
  rw [dif_pos h]
  obtain ⟨c0, c1⟩ := Classical.choose_spec h
  have e0 : (Classical.choose h).1 = a0 :=
    (show (Classical.choose h).1 = g (OracleName.fb S.t) (seedQ0 W S c) from hg _ (hsub c0)).trans
      (show a0 = g (OracleName.fb S.t) (seedQ0 W S c) from hg _ m0).symm
  rw [e0] at c1
  have e1 : (Classical.choose h).2 = a1 :=
    (show (Classical.choose h).2 = g (OracleName.fb S.t) (seedQ1 W S (link a0)) from hg _ (hsub c1)).trans
      (show a1 = g (OracleName.fb S.t) (seedQ1 W S (link a0)) from hg _ m1).symm
  rw [e1]

variable (W S)

open Classical in
/-- the answers of the two records, read back from the list: what stands behind the two first places
-/
def ansOut (cms : List (Dig lam)) : Option (L.OutOfDomainAnswer × L.OutOfDomainAnswer) :=
  if h : ∃ aa : L.OutOfDomainAnswer × L.OutOfDomainAnswer, cms.drop 2 = cA aa.1 ++ cA aa.2 then some (Classical.choose h)
  else none

/-- Off the list of a link's chain the two records' answers are read back, if the code of the
answers is one to one with one length (`AnsOK cA`). -/
theorem ansOut_cmsLA {cA : L.OutOfDomainAnswer → List (Dig lam)} (hA : AnsOK cA) (cm cm' : Dig lam)
    (an an' : L.OutOfDomainAnswer) : ansOut cA (cmsLA cA cm cm' an an') = some (an, an') := by
  have h : ∃ aa : L.OutOfDomainAnswer × L.OutOfDomainAnswer, (cmsLA cA cm cm' an an').drop 2 = cA aa.1 ++ cA aa.2 :=
    ⟨(an, an'), rfl⟩
  unfold ansOut
  rw [dif_pos h]
  have e : cA an ++ cA an' = cA (Classical.choose h).1 ++ cA (Classical.choose h).2 :=
    Classical.choose_spec h
  obtain ⟨e1, e2⟩ := List.append_inj e (hA.len _ _)
  exact congrArg some (Prod.ext (hA.inj e1.symm) (hA.inj e2.symm))

/-- the instance of Link that a trace and a list determine: the seeds off the trace, at the two
first places of the list; the answers off the list -/
def instLA (pre : Tc W) (cms : List (Dig lam)) : Option (L.Rec × L.Rec) :=
  (seedIn W S pre (cms.getD 0 default)).bind fun s =>
  (seedIn W S pre (cms.getD 1 default)).bind fun s' =>
  (ansOut cA cms).map fun aa => ((s, aa.1), (s', aa.2))

/-- the state of Link's lane -/
def stLA (εL : Err L.link.shape) (pre : Tc W) (cms : List (Dig lam)) (_ : Option L.XC) :
    Option (PTr L.link.shape → Bool) :=
  (instLA W S cA pre cms).map
    (stOf L.link εL (extEnc W pre (cms.getD 0 default), extEnc W pre (cms.getD 1 default)))

/-- Link's lane: the state reads the answers off the list and the seeds off the trace. -/
def laneLA (εL : Err L.link.shape) : Lane W :=
  laneAt W Tag.link (batLC L aL) (wLC W).sh W.prjL some
    (Err.timesShared (2 ^ W.depthReqL) aL εL) (stLA W S cA εL)

/-- Its laws, at as many slots as Link's request tree has leaves. Premise: the laws of Link's wire
(hW). -/
theorem laneLA_ok (εL : Err L.link.shape) (hW : (wLC W).OKG) :
    (laneLA W S cA εL).OK (2 ^ W.depthReqL) :=
  laneAt_ok hW.sh fun pre cms xs => by
    refine cast (congrArg (JointLaw (2 ^ W.depthReqL) L.link.shape aL
        (Err.timesShared (2 ^ W.depthReqL) aL εL)) ?_)
      (stOf_jointA L.link aL εL (2 ^ W.depthReqL)
        (extEnc W pre (cms.getD 0 default), extEnc W pre (cms.getD 1 default))
        fun j => (xs j).bind fun _ => instLA W S cA pre cms)
    funext j
    cases xs j <;> rfl

/-- The set of traces outside which the entry's arm is sound. This is said under the hypotheses that
stand in the statement itself, which this comment does not list; it is no claim that they hold. -/
def BadLA (εL : Err L.link.shape) (tr : Tc W) : Prop :=
  (EM tr ∨ EF tr) ∨ StepEvent (fun pre e =>
    stepS W (laneNil W Tag.test) (laneLA W S cA εL) (laneNil W Tag.onl) pre e ∨
      stepSeed W S pre e) tr

variable {W S cA}

/-- A trace in `BadLA` stays in it when entries are appended. -/
theorem badLA_mono {εL : Err L.link.shape} {tr : Tc W} (tr' : Tc W) (h : BadLA W S cA εL tr) :
    BadLA W S cA εL (tr ++ tr') := by
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl (h.append tr'))
  · exact Or.inl (Or.inr (h.append tr'))
  · exact Or.inr (StepEvent.append h tr')

/-- An algorithm with at most t queries ends in `BadLA` with probability at most
t εs + 2 (t + 1)² / 2^lam, under the law of lazy sampling. Premises: the seed's law at εs
(`S.Law εs`), the bound on the rounds' errors (hbL), the laws of Link's wire (hW). -/
theorem badLA_rare {εL : Err L.link.shape} {εs : ℝ≥0∞} (hSd : S.Law εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs) (hW : (wLC W).OKG) {β : Type}
    (A : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) β) (t : ℕ) (hA : A.QueryBound t) :
    pr A.withTrace.law {o | BadLA W S cA εL o.2} ≤
      (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  have h := pr_stepEvent_le (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))
    (fun pre e =>
      stepS W (laneNil W Tag.test) (laneLA W S cA εL) (laneNil W Tag.onl) pre e ∨
        stepSeed W S pre e)
    (fun _ => εs)
    (fun pre e he hs => hs.elim
      (fun hs => hs.elim (fun h1 => h1.1 he) fun h1 =>
        h1.elim (fun h2 => h2.1 he) fun h2 => h2.1 he)
      fun h1 => h1.1 he)
    (fun pre o q _ => pr_step4_le W S rfl rfl rfl rfl rfl rfl (laneNil_ok W Tag.test _)
      (laneLA_ok W S cA εL hW) (laneNil_ok W Tag.onl _) trivial hbL trivial hSd pre o q) A t hA
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  calc
    pr A.withTrace.law {o | BadLA W S cA εL o.2} ≤
        pr A.withTrace.law {o | EM o.2 ∨ EF o.2} +
          pr A.withTrace.law
            {o | StepEvent (fun pre e =>
              stepS W (laneNil W Tag.test) (laneLA W S cA εL) (laneNil W Tag.onl) pre e ∨
                stepSeed W S pre e) o.2} :=
      pr_union_le _ _ _
    _ ≤ 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam + (t : ℝ≥0∞) * εs := add_le_add (hashEvents A t hA) h
    _ ≤ (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
        rw [add_comm]
        gcongr
        exact Nat.le_succ t

variable (W S)

/-- The order: before each first query of a chain of Link (round 0, a head (F1)) stand the seed
queries of the two first entries of its list. -/
def SeedsFirst (tr : Tc W) : Prop :=
  ∀ (pre : Tc W) (q : FbIn lam (typedOracleCarrier L Bd aT aL) Tag.link) (a : FsAns lam W.K) (post : Tc W)
    (cms : List (Dig lam)) (x : Option L.XC) (salt : Bits),
    tr = pre ++ fbE Tag.link q a :: post → q.round = 0 → q.head = Head.f1 cms x salt →
    ∀ c ∈ cms.take 2, SeedAsked W S pre c

variable {W S}

/-- A root's seed queries that stand in a trace stand in every trace that holds its entries. -/
theorem SeedAsked.mono {pre pre' : Tc W} {c : Dig lam} (h : SeedAsked W S pre c)
    (hsub : pre ⊆ pre') : SeedAsked W S pre' c :=
  let ⟨aa, h0, h1⟩ := h
  ⟨aa, hsub h0, hsub h1⟩

/-- Link's clause. On a trace tr that holds the answers of one family g of oracle functions (hg) and
has the order (`SeedsFirst`), outside E_M, E_F and the event of Link's lane, in which the tests of
the two seeds and the lax Link run and say yes: the first table decodes to nothing, or the further
record's seed is a collision seed, or the further table decodes to what the first decodes to.
Premises: Link is sound round by round, with the errors εL, for the language "the first table
decodes to nothing, or the further record's seed is a collision seed of the further word, or the
further table decodes to what the first decodes to" (hsL); Link's verifier is local (hlL); the
annotation aL is coherent (hcL); the wires that Link reads have their laws (`OKLA W`); the code of
the answers is one to one, with one length (`AnsOK cA`). -/
theorem linkA_key {εL : Err L.link.shape}
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hcL : aL.Coherent) (hW : OKLA W) (hA : AnsOK cA) {tr : Tc W}
    {g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))} (hg : ∀ e ∈ tr, e.2.2 = g e.1 e.2.1)
    (hfirst : SeedsFirst W S tr)
    {cm cm' : Dig lam} {rec rec' : L.Rec} {π : OneProtocolProof lam (batLC L aL)}
    (hM : ¬ EM tr) (hF : ¬ EF tr) (hS : ¬ StepEvent (laneLA W S cA εL).step tr)
    (hs0 : RunsIn tr (outOfDomainSeedIs W S cm rec.1) true) (hs1 : RunsIn tr (outOfDomainSeedIs W S cm' rec'.1) true)
    (hrun : RunsIn tr (vLA' W cA cm cm' rec rec' π) true) :
    L.decodeIndex (extEnc W tr cm) rec = none ∨ L.hasCollisionAt (extEnc W tr cm') rec'.1 ∨
      L.decodeIndex (extEnc W tr cm') rec' = L.decodeIndex (extEnc W tr cm) rec :=
  mem_of_accepted_at Tag.link (batLC L aL) (wLC W) W.embL id (fun _ => none)
    W.embE hW.Lk hlL hcL
    (Lg := fun rr y =>
      L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1)
    (stLA W S cA εL) W.prjL hW.prjL_emb some (fun _ => rfl)
    (Err.timesShared (2 ^ W.depthReqL) aL εL) hM hF
    hS
    (cmsLA cA cm cm' rec.2 rec'.2) (rec, rec') π (extEnc W tr cm, extEnc W tr cm')
    (fun _ => stOf L.link εL (extEnc W tr cm, extEnc W tr cm') (rec, rec'))
    (fun _ _ h => absurd rfl h)
    (fun hL => stOf_start hsL _ (rec, rec') hL)
    (fun τ m _ h => stOf_prover _ (rec, rec') τ m h)
    (fun τ _ h => stOf_full _ (rec, rec') τ h) hrun
    (fun pre q a post l cur htr hours => by
      have hsub : pre ⊆ tr := fun e he => by rw [htr]; exact List.mem_append_left _ he
      -- the seed queries of the two roots stand in the trace before this query
      have hsd : ∀ c ∈ (cmsLA cA cm cm' rec.2 rec'.2).take 2, SeedAsked W S pre c := by
        rcases ours_first0 _ hours with ⟨⟨salt, hq⟩, hr⟩ | ⟨q1, a1, salt, hm, hq, hr⟩
        · exact hfirst pre q a post _ _ salt htr hr hq
        · obtain ⟨p1, p2, hp⟩ := List.append_of_mem hm
          intro c hc
          refine (hfirst p1 q1 a1 (p2 ++ fbE Tag.link q a :: post) _ _ salt ?_ hr hq c
            hc).mono ?_
          · rw [htr, hp]
            simp
          · intro e he
            rw [hp]
            exact List.mem_append_left _ he
      have e1 : seedIn W S pre cm = some rec.1 :=
        seedIn_of_run hg hsub (hsd cm (by simp [cmsLA])) hs0
      have e2 : seedIn W S pre cm' = some rec'.1 :=
        seedIn_of_run hg hsub (hsd cm' (by simp [cmsLA])) hs1
      have hocc := ours_cms _ a hours
      have e4 : extEnc W pre cm = extEnc W tr cm :=
        extEnc_before htr hM (hocc _ (by simp [cmsLA]))
      have e5 : extEnc W pre cm' = extEnc W tr cm' :=
        extEnc_before htr hM (hocc _ (by simp [cmsLA]))
      show ((seedIn W S pre cm).bind fun s => (seedIn W S pre cm').bind fun s' =>
          (ansOut cA (cmsLA cA cm cm' rec.2 rec'.2)).map fun aa => ((s, aa.1), (s', aa.2))).map
        (stOf L.link εL (extEnc W pre cm, extEnc W pre cm')) = _
      rw [e1, e2, ansOut_cmsLA hA, e4, e5]
      rfl)
    (fun p a sl h => agreeLkL hW.ext hW.prjE_emb hW.extDepth hW.extL _ p a sl h)

/-- The entry's arm is sound, at the lax Link. On a trace tr that holds the answers of one family g
of oracle functions (hg), has the order (`SeedsFirst`) and lies outside `BadLA`, in which the tests
of the two seeds and the lax Link run and say yes: neither seed is a collision seed of its word, and
the first table decodes to nothing or the further table decodes to what the first decodes to.
Premises: Link is sound round by round, with the errors εL, for the language "the first table
decodes to nothing, or the further record's seed is a collision seed of the further word, or the
further table decodes to what the first decodes to" (hsL); Link's verifier is local (hlL); the
annotation aL is coherent (hcL); the wires that Link reads have their laws (`OKLA W`); the code of
the answers is one to one, with one length (`AnsOK cA`). -/
theorem linkA_sound' {εL : Err L.link.shape}
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hcL : aL.Coherent) (hW : OKLA W) (hA : AnsOK cA) {tr : Tc W}
    {g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))} (hg : ∀ e ∈ tr, e.2.2 = g e.1 e.2.1)
    (hfirst : SeedsFirst W S tr)
    {cm cm' : Dig lam} {rec rec' : L.Rec} {π : OneProtocolProof lam (batLC L aL)}
    (hB : ¬ BadLA W S cA εL tr) (hs0 : RunsIn tr (outOfDomainSeedIs W S cm rec.1) true)
    (hs1 : RunsIn tr (outOfDomainSeedIs W S cm' rec'.1) true)
    (hrun : RunsIn tr (vLA' W cA cm cm' rec rec' π) true) :
    ¬ L.hasCollisionAt (extEnc W tr cm) rec.1 ∧ ¬ L.hasCollisionAt (extEnc W tr cm') rec'.1 ∧
      (L.decodeIndex (extEnc W tr cm) rec = none ∨
        L.decodeIndex (extEnc W tr cm') rec' = L.decodeIndex (extEnc W tr cm) rec) := by
  have hM : ¬ EM tr := fun h => hB (Or.inl (Or.inl h))
  have hF : ¬ EF tr := fun h => hB (Or.inl (Or.inr h))
  have hc0 : ¬ L.hasCollisionAt (extEnc W tr cm) rec.1 := seed_not_coll' hM hF (fun h => hB (Or.inr h)) hs0
  have hc1 : ¬ L.hasCollisionAt (extEnc W tr cm') rec'.1 := seed_not_coll' hM hF (fun h => hB (Or.inr h)) hs1
  refine ⟨hc0, hc1, ?_⟩
  have key := linkA_key hsL hlL hcL hW hA hg hfirst hM hF
    (fun ⟨pre, e, post, h1, h2⟩ =>
      hB (Or.inr ⟨pre, e, post, h1, Or.inl (Or.inr (Or.inl h2))⟩)) hs0 hs1 hrun
  exact key.imp_right fun h => h.resolve_left hc1

/-- The entry's arm is sound, at `VLA`: the conclusion of `linkA_sound'` from a yes of `VLA` in a
trace that holds the answers of one family of oracle functions (hg), has the order (`SeedsFirst`)
and lies outside `BadLA`. Premises: Link is sound round by round, with the errors εL, for the
language "the first table decodes to nothing, or the further record's seed is a collision seed of
the further word, or the further table decodes to what the first decodes to" (hsL); Link's verifier
is local (hlL); the annotation aL is coherent (hcL); the wires that Link reads have their laws
(`OKLA W`); the code of the answers is one to one, with one length (`AnsOK cA`). -/
theorem linkA_sound {εL : Err L.link.shape}
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hcL : aL.Coherent) (hW : OKLA W) (hA : AnsOK cA) (p : Params)
    {tr : Tc W} {g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))}
    (hg : ∀ e ∈ tr, e.2.2 = g e.1 e.2.1) (hfirst : SeedsFirst W S tr)
    {cm cm' : Dig lam} {rec rec' : L.Rec} {π : OneProtocolProof lam (batLC L aL)}
    (hB : ¬ BadLA W S cA εL tr) (hrun : RunsIn tr (VLA W S cA p cm cm' rec rec' π) true) :
    ¬ L.hasCollisionAt (extEnc W tr cm) rec.1 ∧ ¬ L.hasCollisionAt (extEnc W tr cm') rec'.1 ∧
      (L.decodeIndex (extEnc W tr cm) rec = none ∨
        L.decodeIndex (extEnc W tr cm') rec' = L.decodeIndex (extEnc W tr cm) rec) := by
  unfold VLA at hrun
  simp only [runsIn_bind_iff, runsIn_pure_iff] at hrun
  obtain ⟨s0, hs0, s1, hs1, b, hb, habc⟩ := hrun
  simp only [Bool.and_eq_true] at habc
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := habc
  obtain ⟨_, _, hb'⟩ := runsIn_verifyB_of_strict hW.Lk hb
  exact linkA_sound' hsL hlL hcL hW hA hg hfirst hB hs0 hs1 hb'

/-- A yes of the arm with the strict Link holds the yes of the two seeds' tests and of the lax Link,
at a proof string that may differ in its paths' form. Premise: the laws of Link's wire (hLk). -/
theorem yes_VLA (hLk : (wLC W).OKG) (p : Params) {tr : Tc W} {cm cm' : Dig lam} {rec rec' : L.Rec}
    {π : OneProtocolProof lam (batLC L aL)} (hrun : RunsIn tr (VLA W S cA p cm cm' rec rec' π) true) :
    RunsIn tr (outOfDomainSeedIs W S cm rec.1) true ∧ RunsIn tr (outOfDomainSeedIs W S cm' rec'.1) true ∧
      ∃ π', RunsIn tr (vLA' W cA cm cm' rec rec' π') true := by
  unfold VLA at hrun
  simp only [runsIn_bind_iff, runsIn_pure_iff] at hrun
  obtain ⟨s0, hs0, s1, hs1, b, hb, habc⟩ := hrun
  simp only [Bool.and_eq_true] at habc
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := habc
  obtain ⟨_, _, hb'⟩ := runsIn_verifyB_of_strict hLk hb
  exact ⟨hs0, hs1, _, hb'⟩

/-- The same of the arm with the lax Link. -/
theorem yes_VLA' {tr : Tc W} {cm cm' : Dig lam} {rec rec' : L.Rec}
    {π : OneProtocolProof lam (batLC L aL)} (hrun : RunsIn tr (VLA' W S cA cm cm' rec rec' π) true) :
    RunsIn tr (outOfDomainSeedIs W S cm rec.1) true ∧ RunsIn tr (outOfDomainSeedIs W S cm' rec'.1) true ∧
      ∃ π', RunsIn tr (vLA' W cA cm cm' rec rec' π') true := by
  unfold VLA' at hrun
  simp only [runsIn_bind_iff, runsIn_pure_iff] at hrun
  obtain ⟨s0, hs0, s1, hs1, b, hb, habc⟩ := hrun
  simp only [Bool.and_eq_true] at habc
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := habc
  exact ⟨hs0, hs1, _, hb⟩

variable (W S cA)

/-- The arm with the lax Link draws no coin and asks at most `tVL W` queries. -/
theorem detBound_VLA' (cm cm' : Dig lam) (rec rec' : L.Rec) (π : OneProtocolProof lam (batLC L aL)) :
    DetBound (VLA' W S cA cm cm' rec rec' π) (tVL W) := by
  unfold VLA' tVL
  refine ((detBound_seedIs W S _ _).bind (t := 2 + (tVQB (wLC W) W.depthReqL + 0)) fun _ =>
    (detBound_seedIs W S _ _).bind (t := tVQB (wLC W) W.depthReqL + 0) fun _ =>
      (detBound_verifyB _ _ _ _ _ _ _ _ _ _ _).bind (t := 0) fun _ =>
        detBound_pure _ _).mono ?_
  omega

/-- The arm with the strict Link draws no coin and asks at most `tVL W` queries. -/
theorem detBound_VLA (p : Params) (cm cm' : Dig lam) (rec rec' : L.Rec)
    (π : OneProtocolProof lam (batLC L aL)) : DetBound (VLA W S cA p cm cm' rec rec' π) (tVL W) := by
  unfold VLA tVL
  refine ((detBound_seedIs W S _ _).bind (t := 2 + (tVQB (wLC W) W.depthReqL + 0)) fun _ =>
    (detBound_seedIs W S _ _).bind (t := tVQB (wLC W) W.depthReqL + 0) fun _ =>
      (detBound_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _).bind (t := 0) fun _ =>
        detBound_pure _ _).mono ?_
  omega

end TypedOracleCompiler.Compile.Batch.Cms
