-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/CmsAns.lean: the compiled verifier for an object with records, with THE
ANSWERS ALONE in each chain's first query: the key's test and the session beside the link.

A record is a seed with answers. In Cms.lean of this folder the first query of each of the three
chains holds a code of the whole record. By a reading of the programs' text (nothing in this folder
shows it) they hash the roots and the answers, and recompute the seeds from the roots. LinkAns.lean
has the link with the answers alone. Here the key's test (`verifyOfflineProof`) and the session (`verifyOnlineProof`) are written
likewise, and the three stand in one verifier (`verifyAtFullKey`) and one set of traces (`BadA`). The session's
request holds a fixed record in the record's place.

Each lane reads the answers off the first query's list and the seed off the trace so far
(`seedIn`, LinkAns.lean). So the statements are on traces that hold the answers of one family of
oracle functions and in which the seed queries of a first query's roots stand before it
(`SeedsFirstAll`). CmsAnsPr.lean lifts both conditions, for every algorithm.

Two things to watch, as in LinkAns.lean: a repeated query causes no event (a trace lists it again;
the events ask `e ∉ pre`); what is asked first is a function of the query alone, not of the oracle
functions.

Main names:
  `cmsTA`, `cmsBA`, `xinBA`, `verifyOfflineProof`, `vTA'`, `verifyOnlineProof`, `vBA'`, `verifyAtFullKey`: the lists, the request, the
    compiled verifiers, strict and lax.
  `laneTA`, `laneBA`, `BadA`: the lanes; the set of traces.
  `OKA`: the laws of the wires and of the answers' code.
  `BcsAtA`, `cmsA_bcs`: what holds outside a rare event; from `SoundAtR` and the premises that the
    theorem's comment lists.
Limits: soundness alone; typed oracles; one clause, index binding.

-/
import Johnson.TypedOracleCompiler.RecCompile.LinkAns
import Johnson.TypedOracleCompiler.RecCompile.CmsBcs

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal

variable {I X Wn : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec)

/-- the list that the key's chain is handed: the root, then the record's answers -/
def cmsTA (cm : Dig lam) (an : L.OutOfDomainAnswer) : List (Dig lam) := cm :: cA an

/-- the list that a session's chain is handed: the root (twice), then the record's answers -/
def cmsBA (cm : Dig lam) (an : L.OutOfDomainAnswer) : List (Dig lam) := cm :: cm :: cA an

/-- the session's request: the instance, with a fixed record in the record's place -/
def xinBA (a : X × L.Rec) : Option L.XC := some (some a.1, r₀, r₀)

def verifyOfflineProof (p : Params) (cm : Dig lam) (rec : L.Rec) (π : OneProtocolProof lam (batTC L aT)) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  verifyOneProtocol p.sMT p.sFS Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none) W.embE W.depthReqT
    (cmsTA cA cm rec.2) rec π

def vTA' (cm : Dig lam) (rec : L.Rec) (π : OneProtocolProof lam (batTC L aT)) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  verifyB Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none) W.embE W.depthReqT
    (cmsTA cA cm rec.2) rec π

def verifyOnlineProof (p : Params) (cm : Dig lam) (x : X) (rec : L.Rec) (π : OneProtocolProof lam L.onlineBatch) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  verifyOneProtocol p.sMT p.sFS Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀) W.embE W.depthReq
    (cmsBA cA cm rec.2) (x, rec) π

def vBA' (cm : Dig lam) (x : X) (rec : L.Rec) (π : OneProtocolProof lam L.onlineBatch) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  verifyB Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀) W.embE W.depthReq
    (cmsBA cA cm rec.2) (x, rec) π

/-- The verifier: `VC` (Cms.lean) with the three compiled verifiers at the answers alone. -/
def verifyAtFullKey (p : Params) (v : FullKey lam L aT aL) (x : X) (π : RequestProof lam L) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  match v.piT, v.links[π.leaf]?, π.piB with
  | some πT, some (cmj, recj, some πL), some πB =>
      (outOfDomainSeedIs W S v.cm v.rcd.1).bind fun s0 =>
      (outOfDomainSeedIs W S cmj recj.1).bind fun sj =>
      (verifyOfflineProof W cA p v.cm v.rcd πT).bind fun a =>
      (verifyLinkProof W cA p v.cm cmj v.rcd recj πL).bind fun b =>
      (verifyOnlineProof W cA r₀ p cmj x recj πB).bind fun c =>
      OComp.pure (S.num π.copy πB.plains && s0 && sj && a && b && c)
  | _, _, _ => OComp.pure false

/-- The laws of the wires and of the answers' code. -/
structure OKA : Prop where
  base : W.OKG
  T    : (wTC W).OKG
  Lk   : (wLC W).OKG
  B    : (wBC W).OKG
  ans  : AnsOK cA

/-! ## What is read off the list -/

open Classical in
/-- the answers of the key's record, read back from the list: what stands behind the first place -/
def ansOutT (cms : List (Dig lam)) : Option L.OutOfDomainAnswer :=
  if h : ∃ an : L.OutOfDomainAnswer, cms.drop 1 = cA an then some (Classical.choose h) else none

theorem ansOutT_cmsTA {cA : L.OutOfDomainAnswer → List (Dig lam)} (hA : AnsOK cA) (cm : Dig lam) (an : L.OutOfDomainAnswer) :
    ansOutT cA (cmsTA cA cm an) = some an := by
  have h : ∃ a : L.OutOfDomainAnswer, (cmsTA cA cm an).drop 1 = cA a := ⟨an, rfl⟩
  unfold ansOutT
  rw [dif_pos h]
  exact congrArg some (hA.inj (Classical.choose_spec h).symm)

open Classical in
/-- the answers of a session's record, read back from the list: what stands behind the two first
places -/
def ansOutB (cms : List (Dig lam)) : Option L.OutOfDomainAnswer :=
  if h : ∃ an : L.OutOfDomainAnswer, cms.drop 2 = cA an then some (Classical.choose h) else none

theorem ansOutB_cmsBA {cA : L.OutOfDomainAnswer → List (Dig lam)} (hA : AnsOK cA) (cm : Dig lam) (an : L.OutOfDomainAnswer) :
    ansOutB cA (cmsBA cA cm an) = some an := by
  have h : ∃ a : L.OutOfDomainAnswer, (cmsBA cA cm an).drop 2 = cA a := ⟨an, rfl⟩
  unfold ansOutB
  rw [dif_pos h]
  exact congrArg some (hA.inj (Classical.choose_spec h).symm)

/-! ## The lanes -/

/-- the record that a trace and the key's list determine -/
def instTA (pre : Tc W) (cms : List (Dig lam)) : Option L.Rec :=
  (seedIn W S pre (cms.getD 0 default)).bind fun s => (ansOutT cA cms).map fun an => (s, an)

def stTA (εT : Err L.offline.shape) (pre : Tc W) (cms : List (Dig lam)) (_ : Option L.XC) :
    Option (PTr L.offline.shape → Bool) :=
  (instTA W S cA pre cms).map (stOf L.offline εT (extEnc W pre (cms.getD 0 default)))

def laneTA (εT : Err L.offline.shape) : Lane W :=
  laneAt W Tag.test (batTC L aT) (wTC W).sh W.prjT some
    (Err.timesShared (2 ^ W.depthReqT) aT εT) (stTA W S cA εT)

theorem laneTA_ok (εT : Err L.offline.shape) (hW : (wTC W).OKG) :
    (laneTA W S cA εT).OK (2 ^ W.depthReqT) :=
  laneAt_ok hW.sh fun pre cms xs => by
    refine cast (congrArg (JointLaw (2 ^ W.depthReqT) L.offline.shape aT
        (Err.timesShared (2 ^ W.depthReqT) aT εT)) ?_)
      (stOf_jointA L.offline aT εT (2 ^ W.depthReqT) (extEnc W pre (cms.getD 0 default))
        fun j => (xs j).bind fun _ => instTA W S cA pre cms)
    funext j
    cases xs j <;> rfl

/-- the record that a trace and a session's list determine -/
def recBA (pre : Tc W) (cms : List (Dig lam)) : Option L.Rec :=
  (seedIn W S pre (cms.getD 0 default)).bind fun s => (ansOutB cA cms).map fun an => (s, an)

def stBA (State : (oneExternalString L.wordLength L.Symbol).Str → X × L.Rec → PTr L.onlineBatch.loc.shape → Bool) (pre : Tc W)
    (cms : List (Dig lam)) (xo : Option L.XC) : Option (PTr L.onlineBatch.loc.shape → Bool) :=
  (recBA W S cA pre cms).bind fun rec =>
    (xo.bind fun a => a.1).map fun x => State (extEnc W pre (cms.getD 0 default)) (x, rec)

def laneBA (εB : Err L.onlineBatch.loc.shape)
    (State : (oneExternalString L.wordLength L.Symbol).Str → X × L.Rec → PTr L.onlineBatch.loc.shape → Bool) : Lane W :=
  laneAt W Tag.onl L.onlineBatch (wBC W).sh W.prjB some εB (stBA W S cA State)

/-- The set of traces outside which the verifier is sound. This is said under the hypotheses that
stand in the statement itself, which this comment does not list; it is no claim that they hold. -/
def BadA (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape)
    (State : (oneExternalString L.wordLength L.Symbol).Str → X × L.Rec → PTr L.onlineBatch.loc.shape → Bool) (tr : Tc W) : Prop :=
  (EM tr ∨ EF tr) ∨ StepEvent (fun pre e =>
    stepS W (laneTA W S cA εT) (laneLA W S cA εL) (laneBA W S cA εB State) pre e ∨
      stepSeed W S pre e) tr

/-- THE ORDER, at all three tags: before each first query of a chain (round 0, a head (F1)) stand
the seed queries of the two first entries of its list. -/
def SeedsFirstAll (tr : Tc W) : Prop :=
  ∀ (t : Tag) (pre : Tc W) (q : FbIn lam (typedOracleCarrier L Bd aT aL) t) (a : FsAns lam W.K) (post : Tc W)
    (cms : List (Dig lam)) (x : Option L.XC) (salt : Bits),
    tr = pre ++ fbE t q a :: post → q.round = 0 → q.head = Head.f1 cms x salt →
    ∀ c ∈ cms.take 2, SeedAsked W S pre c

variable {W S}

/-- On a trace that has the order: before each query of a chain of ours stand the seed queries of
the two first entries of our list. -/
theorem seedAsked_of_ours {tr : Tc W} (hfirst : SeedsFirstAll W S tr) (C : Ctx W)
    {pre : Tc W} {q : FbIn lam (typedOracleCarrier L Bd aT aL) C.t} {a : FsAns lam W.K} {post : Tc W}
    {l : List (Rec lam W.K (typedOracleCarrier L Bd aT aL) C.t)} {cur : Item lam (typedOracleCarrier L Bd aT aL) C.t}
    (htr : tr = pre ++ fbE C.t q a :: post) (hours : Ours C pre q l cur) :
    ∀ c ∈ C.cms.take 2, SeedAsked W S pre c := by
  rcases ours_first0 C hours with ⟨⟨salt, hq⟩, hr⟩ | ⟨q1, a1, salt, hm, hq, hr⟩
  · exact hfirst C.t pre q a post _ _ salt htr hr hq
  · obtain ⟨p1, p2, hp⟩ := List.append_of_mem hm
    intro c hc
    refine (hfirst C.t p1 q1 a1 (p2 ++ fbE C.t q a :: post) _ _ salt ?_ hr hq c hc).mono ?_
    · rw [htr, hp]
      simp
    · intro e he
      rw [hp]
      exact List.mem_append_left _ he

variable (W S)

/-- What holds outside a rare event, on traces with one family's answers that have the order and
hold the verifier's queries. -/
def BcsAtA (Rt : I → X → Prop) (εs : ℝ≥0∞) : Prop :=
  ∃ Bad : Tc W → Prop,
    (∀ (β : Type) (A : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) β) (t : ℕ), A.QueryBound t →
      pr A.withTrace.law {o | Bad o.2} ≤ (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam) ∧
    (∀ tr tr', Bad tr → Bad (tr ++ tr')) ∧
    (∀ tr cm s, ¬ Bad tr → RunsIn tr (outOfDomainSeedIs W S cm s) true → ¬ L.hasCollisionAt (extEnc W tr cm) s) ∧
    (∀ tr (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) cm rec π,
      (∀ e ∈ tr, e.2.2 = g e.1 e.2.1) → SeedsFirstAll W S tr → ¬ Bad tr →
      RunsIn tr (outOfDomainSeedIs W S cm rec.1) true → RunsIn tr (vTA' W cA cm rec π) true →
      L.hasCollisionAt (extEnc W tr cm) rec.1 ∨ L.decodeIndex (extEnc W tr cm) rec ≠ none) ∧
    (∀ tr (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) cm cm' rec rec' π,
      (∀ e ∈ tr, e.2.2 = g e.1 e.2.1) → SeedsFirstAll W S tr → ¬ Bad tr →
      RunsIn tr (outOfDomainSeedIs W S cm rec.1) true → RunsIn tr (outOfDomainSeedIs W S cm' rec'.1) true →
      RunsIn tr (vLA' W cA cm cm' rec rec' π) true →
      L.decodeIndex (extEnc W tr cm) rec = none ∨ L.hasCollisionAt (extEnc W tr cm') rec'.1 ∨
      L.decodeIndex (extEnc W tr cm') rec' = L.decodeIndex (extEnc W tr cm) rec) ∧
    (∀ tr (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) cm x rec π,
      (∀ e ∈ tr, e.2.2 = g e.1 e.2.1) → SeedsFirstAll W S tr → ¬ Bad tr →
      RunsIn tr (outOfDomainSeedIs W S cm rec.1) true → RunsIn tr (vBA' W cA r₀ cm x rec π) true →
      L.decodeIndex (extEnc W tr cm) rec = none ∨ ∃ i, L.decodeIndex (extEnc W tr cm) rec = some i ∧ Rt i x) ∧
    (∀ tr tr' cm, ¬ Bad (tr ++ tr') → Announced W tr cm → extEnc W tr cm = extEnc W (tr ++ tr') cm)

/-- The clauses of `BcsAtA`, with the answers alone in the first queries. Under: `SoundAtR` at
explicit lists of errors; the seed's law `S.Law εs`; every round's error at most εs, a shared
round's of the key's test and of the link counted once for each leaf of that call's request tree;
the three verifiers read their oracles at the declared positions alone (`IsLocal`); the three lists
of marks (which rounds are shared) are coherent; `OKA`. -/
theorem cmsA_bcs (Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn) (eR : ℕ)
    (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape) (εs : ℝ≥0∞)
    (hS : L.SoundAtR Rno wit eR εT εL εB) (hSd : S.Law εs)
    (hbT : Err.Below (Err.timesShared (2 ^ W.depthReqT) aT εT) εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs)
    (hbB : Err.Below εB εs) (hlT : L.offline.IsLocal) (hlL : L.link.IsLocal)
    (hlB : L.onlineBatch.loc.IsLocal) (hcT : aT.Coherent) (hcL : aL.Coherent)
    (hco : L.onlineBatch.ann.Coherent) (hW : OKA W cA) :
    BcsAtA W S cA r₀ (fun i x => ∃ w, Rno i x w) εs := by
  choose h0 St h1 h2 h3 h4 h5 using fun rec =>
    (Iop.sndBKT_laws X Wn _ (L.batAt rec) L.maxBatchSize L.early L.late (L.relB Rno rec)
      (fun x y τ => wit (x, rec) y τ) εB).1 (hS.sndB rec)
  let State : (oneExternalString L.wordLength L.Symbol).Str → X × L.Rec → PTr L.onlineBatch.loc.shape → Bool :=
    fun y a => St a.2 y a.1
  have oT : (laneTA W S cA εT).OK (2 ^ W.depthReqT) := laneTA_ok W S cA εT hW.T
  have oL : (laneLA W S cA εL).OK (2 ^ W.depthReqL) := laneLA_ok W S cA εL hW.Lk
  have oB : (laneBA W S cA εB State).OK L.maxBatchSize := by
    refine laneAt_ok hW.B.sh fun pre cms xs => ?_
    cases hr : recBA W S cA pre cms with
    | none =>
      refine cast (congrArg (JointLaw L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann εB) ?_)
        (Iop.BatchOne.jointLaw_none L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann εB)
      funext j
      show none = (xs j).bind (stBA W S cA State pre cms)
      cases xs j with
      | none => rfl
      | some xo =>
        show none = stBA W S cA State pre cms xo
        unfold stBA
        rw [hr]
        rfl
    | some rec =>
      refine cast (congrArg (JointLaw L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann εB) ?_)
        (h5 rec (extEnc W pre (cms.getD 0 default))
          fun j => (xs j).bind fun xo => xo.bind fun a => a.1)
      funext j
      show Option.map (St rec (extEnc W pre (cms.getD 0 default)))
          ((xs j).bind fun xo => xo.bind fun a => a.1) = (xs j).bind (stBA W S cA State pre cms)
      cases xs j with
      | none => rfl
      | some xo =>
        show Option.map (St rec (extEnc W pre (cms.getD 0 default))) (xo.bind fun a => a.1) =
          stBA W S cA State pre cms xo
        unfold stBA
        rw [hr]
        rfl
  refine ⟨BadA W S cA εT εL εB State, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro β A t hA
    have h := pr_stepEvent_le (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))
      (fun pre e =>
        stepS W (laneTA W S cA εT) (laneLA W S cA εL) (laneBA W S cA εB State) pre e ∨
          stepSeed W S pre e)
      (fun _ => εs)
      (fun pre e he hs => hs.elim
        (fun hs => hs.elim (fun h1 => h1.1 he) fun h1 =>
          h1.elim (fun h2 => h2.1 he) fun h2 => h2.1 he)
        fun h1 => h1.1 he)
      (fun pre o q _ => pr_step4_le W S rfl rfl rfl rfl rfl hW.base.slots oT oL oB hbT hbL hbB hSd
        pre o q) A t hA
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
    calc
      pr A.withTrace.law {o | BadA W S cA εT εL εB State o.2} ≤
          pr A.withTrace.law {o | EM o.2 ∨ EF o.2} +
            pr A.withTrace.law
              {o | StepEvent (fun pre e =>
                stepS W (laneTA W S cA εT) (laneLA W S cA εL) (laneBA W S cA εB State) pre e ∨
                  stepSeed W S pre e) o.2} :=
        pr_union_le _ _ _
      _ ≤ 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam + (t : ℝ≥0∞) * εs := add_le_add (hashEvents A t hA) h
      _ ≤ (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
          rw [add_comm]
          gcongr
          exact Nat.le_succ t
  · rintro tr tr' ((h | h) | h)
    · exact Or.inl (Or.inl (h.append tr'))
    · exact Or.inl (Or.inr (h.append tr'))
    · exact Or.inr (StepEvent.append h tr')
  · intro tr cm s hB hrun
    exact seed_not_coll' (fun h => hB (Or.inl (Or.inl h))) (fun h => hB (Or.inl (Or.inr h)))
      (fun h => hB (Or.inr h)) hrun
  · intro tr g cm rec π hg hfirst hB hs0 hrun
    have hM : ¬ EM tr := fun h => hB (Or.inl (Or.inl h))
    have hF : ¬ EF tr := fun h => hB (Or.inl (Or.inr h))
    exact mem_of_accepted_at Tag.test (batTC L aT) (wTC W) W.embT id (fun _ => none)
      W.embE hW.T hlT hcT
      (Lg := fun rec y => L.hasCollisionAt y rec.1 ∨ L.decodeIndex y rec ≠ none)
      (stTA W S cA εT) W.prjT hW.base.prjT_emb some (fun _ => rfl)
      (Err.timesShared (2 ^ W.depthReqT) aT εT) hM hF
      (fun ⟨pre, e, post, h1, h2⟩ => hB (Or.inr ⟨pre, e, post, h1, Or.inl (Or.inl h2)⟩))
      (cmsTA cA cm rec.2) rec π (extEnc W tr cm)
      (fun _ => stOf L.offline εT (extEnc W tr cm) rec)
      (fun _ _ h => absurd rfl h)
      (fun hL => stOf_start hS.sndT _ rec hL)
      (fun τ m _ h => stOf_prover _ rec τ m h)
      (fun τ _ h => stOf_full _ rec τ h) hrun
      (fun pre q a post l cur htr hours => by
        have hsub : pre ⊆ tr := fun e he => by rw [htr]; exact List.mem_append_left _ he
        have hsd := seedAsked_of_ours hfirst _ htr hours
        have e1 : seedIn W S pre cm = some rec.1 :=
          seedIn_of_run hg hsub (hsd cm (by simp [cmsTA])) hs0
        have e4 : extEnc W pre cm = extEnc W tr cm :=
          extEnc_before htr hM (ours_cms _ a hours _ (by simp [cmsTA]))
        show ((seedIn W S pre cm).bind fun s =>
            (ansOutT cA (cmsTA cA cm rec.2)).map fun an => (s, an)).map
          (stOf L.offline εT (extEnc W pre cm)) = _
        rw [e1, ansOutT_cmsTA hW.ans, e4]
        rfl)
      (fun p a sl h => by
        change extLeaf tr W.T.ext.depth ((cmsTA cA cm rec.2).getD (W.T.ext.which p) default)
          (W.T.ext.leaf p) = _ at h
        rw [hW.base.extDepth.1, (hW.base.extT p).1, (hW.base.extT p).2] at h
        exact extEnc_apply hW.base h)
  · intro tr g cm cm' rec rec' π hg hfirst hB hs0 hs1 hrun
    have hM : ¬ EM tr := fun h => hB (Or.inl (Or.inl h))
    have hF : ¬ EF tr := fun h => hB (Or.inl (Or.inr h))
    exact mem_of_accepted_at Tag.link (batLC L aL) (wLC W) W.embL id (fun _ => none)
      W.embE hW.Lk hlL hcL
      (Lg := fun rr y =>
        L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1)
      (stLA W S cA εL) W.prjL hW.base.prjL_emb some (fun _ => rfl)
      (Err.timesShared (2 ^ W.depthReqL) aL εL) hM hF
      (fun ⟨pre, e, post, h1, h2⟩ =>
        hB (Or.inr ⟨pre, e, post, h1, Or.inl (Or.inr (Or.inl h2))⟩))
      (cmsLA cA cm cm' rec.2 rec'.2) (rec, rec') π (extEnc W tr cm, extEnc W tr cm')
      (fun _ => stOf L.link εL (extEnc W tr cm, extEnc W tr cm') (rec, rec'))
      (fun _ _ h => absurd rfl h)
      (fun hL => stOf_start hS.sndL _ (rec, rec') hL)
      (fun τ m _ h => stOf_prover _ (rec, rec') τ m h)
      (fun τ _ h => stOf_full _ (rec, rec') τ h) hrun
      (fun pre q a post l cur htr hours => by
        have hsub : pre ⊆ tr := fun e he => by rw [htr]; exact List.mem_append_left _ he
        have hsd := seedAsked_of_ours hfirst _ htr hours
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
        rw [e1, e2, ansOut_cmsLA hW.ans, e4, e5]
        rfl)
      (fun p a sl h => agreeLk hW.base _ p a sl h)
  · intro tr g cm x rec π hg hfirst hB hs0 hrun
    have hM : ¬ EM tr := fun h => hB (Or.inl (Or.inl h))
    have hF : ¬ EF tr := fun h => hB (Or.inl (Or.inr h))
    exact mem_of_accepted_at Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀) W.embE hW.B hlB hco
      (Lg := fun a y => L.decodeIndex y a.2 = none ∨ ∃ i, L.decodeIndex y a.2 = some i ∧ ∃ w, Rno i a.1 w)
      (stBA W S cA State) W.prjB hW.base.prjB_emb some (fun _ => rfl) εB hM hF
      (fun ⟨pre, e, post, h1, h2⟩ =>
        hB (Or.inr ⟨pre, e, post, h1, Or.inl (Or.inr (Or.inr h2))⟩))
      (cmsBA cA cm rec.2) (x, rec) π (extEnc W tr cm)
      (fun i => St rec (extEnc W tr cm) (instR L x i))
      (fun n hn _ => h0 rec n hn)
      (fun _ => by
        show St rec _ (instR L x 0) _ = false
        rw [instR_zero (h0 rec)]
        exact h1 rec _ x)
      (fun τ m _ h => by
        have h' : St rec (extEnc W tr cm) (instR L x (τ.idx - 1)) (.atP τ) = false := h
        show St rec (extEnc W tr cm) (instR L x τ.idx) _ = false
        rcases instR_step (h0 rec) x τ.idx with e | ⟨e1, e2, e3⟩
        · rw [e] at h'
          exact h2 rec _ _ τ m h'
        · rw [e2] at h'
          rw [e3]
          exact h2 rec _ x τ m (h3 rec _ x τ e1 h'))
      (fun τ hL h => Bool.eq_false_iff.2 fun hacc => hL (by
        have h' : St rec (extEnc W tr cm) (instR L x ((L.batAt rec).loc.shape.length - 1))
            (.full τ) = false := h
        rw [instR_last (h0 rec)] at h'
        rcases h4 rec _ x τ h' hacc with h7 | ⟨i, hi, hr⟩
        · exact Or.inl h7
        · exact Or.inr ⟨i, hi, _, hr⟩)) hrun
      (fun pre q a post l cur htr hours => by
        have hsub : pre ⊆ tr := fun e he => by rw [htr]; exact List.mem_append_left _ he
        have hsd := seedAsked_of_ours hfirst _ htr hours
        have e1 : seedIn W S pre cm = some rec.1 :=
          seedIn_of_run hg hsub (hsd cm (by simp [cmsBA])) hs0
        have e4 : extEnc W pre cm = extEnc W tr cm :=
          extEnc_before htr hM (ours_cms _ a hours _ (by simp [cmsBA]))
        have e : instX (typedOracleCarrier L Bd aT aL) (xinBA r₀ (x, rec)) l.length =
            some (some (instR L x l.length), r₀, r₀) := by
          unfold instX instR
          show (match L.late with
            | some n => if n ≤ l.length then xinBA r₀ (x, rec)
                else (xinBA r₀ (x, rec)).map (typedOracleCarrier L Bd aT aL).early
            | none => (xinBA r₀ (x, rec)).map (typedOracleCarrier L Bd aT aL).early) = _
          cases L.late with
          | none => rfl
          | some n => by_cases hn : n ≤ l.length <;> simp only [hn, if_true, if_false] <;> rfl
        rw [e]
        show ((seedIn W S pre cm).bind fun s =>
            (ansOutB cA (cmsBA cA cm rec.2)).map fun an => (s, an)).bind (fun rc =>
          (some (instR L x l.length)).map fun x' => State (extEnc W pre cm) (x', rc)) = _
        rw [e1, ansOutB_cmsBA hW.ans, e4]
        rfl)
      (fun p a sl h => by
        change extLeaf tr W.B.ext.depth ((cmsBA cA cm rec.2).getD (W.B.ext.which p) default)
          (W.B.ext.leaf p) = _ at h
        rw [hW.base.extDepth.2.2, (hW.base.extB p).1, (hW.base.extB p).2] at h
        exact extEnc_apply hW.base h)
  · intro tr tr' cm hB hann
    exact extEnc_stable (fun h => hB (Or.inl (Or.inl h)))
      (List.prefix_append _ _) (occursIn_of_announced hann)

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms TypedOracleCompiler.Compile.Batch.Cms.cmsA_bcs
