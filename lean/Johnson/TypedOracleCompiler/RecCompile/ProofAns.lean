-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/ProofAns.lean: the proof's arm of the compiled verifier with records, with
the root and the record's answers alone in the list of the session's first query: its definitions,
the set of traces outside which it is sound, and its soundness on a trace.

The proof's arm is the test of a record's seed followed by the session's compiled verifier (`vBA'`,
`verifyOnlineProof`, CmsAns.lean) on a root, an instance, a record and a proof string. It is to the session what
the entry's arm (LinkAns.lean) is to Link and the key's arm (KeyAns.lean) to Test.

  `OKBA`            what the arm asks of the wires
  `ProofHoldsAt`, `ProofHolds`   what the arm promises: the record's seed is no collision seed of
                    the word under the root; and word and record decode to nothing, or to an index
                    that stands in the relation to the instance
  `OutBA`, `VBA`, `VBA'`, `tVB`   what a maker puts out; the arm with the strict and with the lax
                    session; a bound on its queries
  `BadBA`, `badBA_mono`, `badBA_rare`   the set of traces, and that it is rare
  `SeedsFirstB`     the order: the seed queries of the root stand before each first query of a chain
                    of the session
  `SessAt`, `sessA_key`   the session's clause: there are states of its rounds at which its lane has
                    its law and a yes on a trace outside the lane's event holds the clause
  `sessA_sound'`    the theorem on a trace, at the lax session with the seed's test
  `yes_VBA`, `yes_VBA'`, `detBound_VBA`, `detBound_VBA'`   what a yes of either arm holds; a bound
                    on an arm's queries, and that it draws no coin
  `holds_three`     what the three arms promise of two given words, put together: a step of logic

The session's soundness is a hypothesis: the fifth clause of `HolographicProtocol.SoundAtR`
(Hiop/RecInterface.lean), round by round with a witness, at the batch's number of slots. Nothing in
this folder shows it of a protocol. In it the error of a shared round is the joint one, over all
slots of the batch (`JointLaw`, Iop/Batch.lean): so hbB bounds the joint errors, and no factor for
the slots stands in the bound.

Limits: soundness alone; typed oracles. No statement in probabilities joins `badBA_rare` and
`sessA_sound'` here.
  * The way out: "word and record decode to nothing". The arm alone says nothing of an index then.
    `holds_three` closes it, given what the key's and the entry's arm promise of the same words.
  * The chain of the session holds `L.early x` in its first query and x itself in the query of the
    round `L.late`. Where `L.late` is none, the rest of x is hashed nowhere: two instances with one
    early part have one chain, and that a yes binds the rest is a load of hsB (its clause on full
    transcripts is then said at the state of `L.early x`).
  * No accepted run is shown: nothing here says that an arm ever says yes. The premises that
    `armB_pr`'s docstring names are laws of letters in these three files.
    Johnson/Flat/ProofArmAt.lean [not in this library] pays all but hsB and hbB at the three files'
    object and a written wiring.
  * Of the whole verifier's clauses (`verifyAtFullKey`, CmsAns.lean) the arm leaves out the test of the copy's
    number in the plain parts (`S.num`) and the choice of a link by the proof's leaf.
  * The limits in the head of LinkAnsPr.lean on the record's wire and on a coding hold here too.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.CmsAns
import Johnson.TypedOracleCompiler.RecCompile.KeyAns
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsTwoStage

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
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec)

/-- What the proof's arm asks of the wires. -/
structure OKBA : Prop where
  /-- the laws of the session's wire -/
  B : (wBC W).OKG
  /-- the wire by which the word under a root is built (it follows from B; kept as in `OKLA`) -/
  ext : W.B.ext.OK
  prjE_emb : ∀ s, W.prjE (W.embE s) = some s
  prjB_emb : ∀ p a, W.prjB p (W.embB p a) = some a
  extDepth : W.B.ext.depth = W.depth
  extB : ∀ p, W.B.ext.which p = 0 ∧ W.B.ext.leaf p = p.val
  /-- the batch has as many slots as the request tree has leaves -/
  slots : L.maxBatchSize = 2 ^ W.depthReq

/-- What the proof's arm promises, said of a word, an instance and a record: the record's seed is no
collision seed of the word; word and record decode to nothing, or to an index that stands in the
relation Rt to the instance. -/
def ProofHoldsAt (L : HolographicProtocol I X) (Rt : I → X → Prop) (y : Fin L.wordLength → L.Symbol) (x : X) (rec : L.Rec) :
    Prop :=
  ¬ L.hasCollisionAt y rec.1 ∧ (L.decodeIndex y rec = none ∨ ∃ i, L.decodeIndex y rec = some i ∧ Rt i x)

/-- What the proof's arm promises of a trace, a root, an instance and a record. -/
def ProofHolds (Rt : I → X → Prop) (tr : Tc W) (cm : Dig lam) (x : X) (rec : L.Rec) : Prop :=
  ProofHoldsAt L Rt (extEnc W tr cm) x rec

/-- What the three arms promise of two given words, put together: the first word and record decode
to an index that stands in the relation to the instance. A step on given words and records: no
statement in probabilities. -/
theorem holds_three {Rt : I → X → Prop} {y y' : Fin L.wordLength → L.Symbol} {x : X} {rec rec' : L.Rec}
    (hK : KeyHoldsAt L y rec) (hL : LinkHoldsAt L y y' rec rec')
    (hP : ProofHoldsAt L Rt y' x rec') : ∃ i, L.decodeIndex y rec = some i ∧ Rt i x := by
  have e : L.decodeIndex y' rec' = L.decodeIndex y rec := hL.2.2.resolve_left hK.2
  rcases hP.2 with h | ⟨i, hi, hr⟩
  · exact absurd (e ▸ h) hK.2
  · exact ⟨i, e ▸ hi, hr⟩

/-- what a maker puts out: a root, an instance, a record, the session's proof string -/
abbrev OutBA (lam : ℕ) (L : HolographicProtocol I X) : Type :=
  Dig lam × X × L.Rec × OneProtocolProof lam L.onlineBatch

/-- The proof's arm with the strict session. -/
def VBA (p : Params) (cm : Dig lam) (x : X) (rec : L.Rec) (π : OneProtocolProof lam L.onlineBatch) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  (outOfDomainSeedIs W S cm rec.1).bind fun s0 =>
  (verifyOnlineProof W cA r₀ p cm x rec π).bind fun b =>
  OComp.pure (s0 && b)

/-- The same arm with the lax session. -/
def VBA' (cm : Dig lam) (x : X) (rec : L.Rec) (π : OneProtocolProof lam L.onlineBatch) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  (outOfDomainSeedIs W S cm rec.1).bind fun s0 =>
  (vBA' W cA r₀ cm x rec π).bind fun b =>
  OComp.pure (s0 && b)

/-- a bound on the number of queries of the proof's arm -/
def tVB : ℕ := 2 + tVQB (wBC W) W.depthReq

/-- The set of traces outside which the proof's arm is sound, at states `State` of the session's
rounds. This is said under the hypotheses that stand in the statement itself, which this comment
does not list; it is no claim that they hold. -/
def BadBA (εB : Err L.onlineBatch.loc.shape)
    (State : (oneExternalString L.wordLength L.Symbol).Str → X × L.Rec → PTr L.onlineBatch.loc.shape → Bool) (tr : Tc W) : Prop :=
  (EM tr ∨ EF tr) ∨ StepEvent (fun pre e =>
    stepS W (laneNil W Tag.test) (laneNil W Tag.link) (laneBA W S cA εB State) pre e ∨
      stepSeed W S pre e) tr

variable {W S cA r₀}

/-- A trace in `BadBA` stays in it when entries are appended. -/
theorem badBA_mono {εB : Err L.onlineBatch.loc.shape}
    {State : (oneExternalString L.wordLength L.Symbol).Str → X × L.Rec → PTr L.onlineBatch.loc.shape → Bool} {tr : Tc W}
    (tr' : Tc W) (h : BadBA W S cA εB State tr) : BadBA W S cA εB State (tr ++ tr') := by
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl (h.append tr'))
  · exact Or.inl (Or.inr (h.append tr'))
  · exact Or.inr (StepEvent.append h tr')

/-- An algorithm with at most t queries ends in `BadBA` with probability at most
t εs + 2 (t + 1)² / 2^lam, under the law of lazy sampling. Premises: the seed's law at εs
(`S.Law εs`), the bound on the rounds' errors (hbB), the law of the session's lane (oB), the number
of slots (hN). -/
theorem badBA_rare {εB : Err L.onlineBatch.loc.shape}
    {State : (oneExternalString L.wordLength L.Symbol).Str → X × L.Rec → PTr L.onlineBatch.loc.shape → Bool} {εs : ℝ≥0∞}
    (hSd : S.Law εs) (hbB : Err.Below εB εs) (oB : (laneBA W S cA εB State).OK L.maxBatchSize)
    (hN : L.maxBatchSize = 2 ^ W.depthReq) {β : Type}
    (A : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) β) (t : ℕ) (hA : A.QueryBound t) :
    pr A.withTrace.law {o | BadBA W S cA εB State o.2} ≤
      (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  have h := pr_stepEvent_le (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))
    (fun pre e =>
      stepS W (laneNil W Tag.test) (laneNil W Tag.link) (laneBA W S cA εB State) pre e ∨
        stepSeed W S pre e)
    (fun _ => εs)
    (fun pre e he hs => hs.elim
      (fun hs => hs.elim (fun h1 => h1.1 he) fun h1 =>
        h1.elim (fun h2 => h2.1 he) fun h2 => h2.1 he)
      fun h1 => h1.1 he)
    (fun pre o q _ => pr_step4_le W S rfl rfl rfl rfl rfl hN (laneNil_ok W Tag.test _)
      (laneNil_ok W Tag.link _) oB trivial trivial hbB hSd pre o q) A t hA
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  calc
    pr A.withTrace.law {o | BadBA W S cA εB State o.2} ≤
        pr A.withTrace.law {o | EM o.2 ∨ EF o.2} +
          pr A.withTrace.law
            {o | StepEvent (fun pre e =>
              stepS W (laneNil W Tag.test) (laneNil W Tag.link) (laneBA W S cA εB State) pre e ∨
                stepSeed W S pre e) o.2} :=
      pr_union_le _ _ _
    _ ≤ 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam + (t : ℝ≥0∞) * εs := add_le_add (hashEvents A t hA) h
    _ ≤ (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
        rw [add_comm]
        gcongr
        exact Nat.le_succ t

variable (W S)

/-- The order: before each first query of a chain of the session (round 0, a head (F1)) stand the
seed queries of the first entry of its list. -/
def SeedsFirstB (tr : Tc W) : Prop :=
  ∀ (pre : Tc W) (q : FbIn lam (typedOracleCarrier L Bd aT aL) Tag.onl) (a : FsAns lam W.K) (post : Tc W)
    (cms : List (Dig lam)) (x : Option L.XC) (salt : Bits),
    tr = pre ++ fbE Tag.onl q a :: post → q.round = 0 → q.head = Head.f1 cms x salt →
    ∀ c ∈ cms.take 1, SeedAsked W S pre c

variable {W S}

variable (W S cA r₀)

/-- The session's clause at states `State` of its rounds: its lane has its law at the batch's number
of slots; and on a trace tr that holds the answers of one family g of oracle functions and has the
order, outside E_M, E_F and the event of the session's lane, in which the test of the seed and the
lax session run and say yes: word and record decode to nothing, or to an index that stands in the
relation Rt to the instance. -/
def SessAt (Rt : I → X → Prop) (εB : Err L.onlineBatch.loc.shape)
    (State : (oneExternalString L.wordLength L.Symbol).Str → X × L.Rec → PTr L.onlineBatch.loc.shape → Bool) : Prop :=
  (laneBA W S cA εB State).OK L.maxBatchSize ∧
    ∀ (tr : Tc W) (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) (cm : Dig lam) (x : X)
      (rec : L.Rec) (π : OneProtocolProof lam L.onlineBatch),
      (∀ e ∈ tr, e.2.2 = g e.1 e.2.1) → SeedsFirstB W S tr → ¬ EM tr → ¬ EF tr →
      ¬ StepEvent (laneBA W S cA εB State).step tr →
      RunsIn tr (outOfDomainSeedIs W S cm rec.1) true → RunsIn tr (vBA' W cA r₀ cm x rec π) true →
      L.decodeIndex (extEnc W tr cm) rec = none ∨ ∃ i, L.decodeIndex (extEnc W tr cm) rec = some i ∧ Rt i x

variable {W S cA r₀}

/-- There are such states. Premises: the session is sound round by round with a witness, with the
errors εB, at the batch's number of slots, at every record (hsB: the fifth clause of
`HolographicProtocol.SoundAtR`); its verifier is local (hlB); its annotation is coherent (hco); the wires that the
session reads have their laws (`OKBA W`); the code of the answers is one to one, with one length
(`AnsOK cA`). -/
theorem sessA_key {Wn : Type} (Rno : I → X → Wn → Prop)
    (wit : X × L.Rec → (oneExternalString L.wordLength L.Symbol).Str → Tr L.onlineBatch.loc.shape → Wn)
    {εB : Err L.onlineBatch.loc.shape}
    (hsB : ∀ rec, (L.batAt rec).SndBKT L.maxBatchSize L.early L.late (L.relB Rno rec)
      (fun x y τ => wit (x, rec) y τ) εB)
    (hlB : L.onlineBatch.loc.IsLocal) (hco : L.onlineBatch.ann.Coherent) (hW : OKBA W) (hA : AnsOK cA) :
    ∃ State, SessAt W S cA r₀ (fun i x => ∃ w, Rno i x w) εB State := by
  choose h0 St h1 h2 h3 h4 h5 using fun rec =>
    (Iop.sndBKT_laws X Wn _ (L.batAt rec) L.maxBatchSize L.early L.late (L.relB Rno rec)
      (fun x y τ => wit (x, rec) y τ) εB).1 (hsB rec)
  let State : (oneExternalString L.wordLength L.Symbol).Str → X × L.Rec → PTr L.onlineBatch.loc.shape → Bool :=
    fun y a => St a.2 y a.1
  refine ⟨State, ?_, ?_⟩
  · refine laneAt_ok hW.B.sh fun pre cms xs => ?_
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
  · intro tr g cm x rec π hg hfirst hM hF hS hs0 hrun
    exact mem_of_accepted_at Tag.onl L.onlineBatch (wBC W) W.embB id (xinBA r₀) W.embE hW.B hlB hco
      (Lg := fun a y => L.decodeIndex y a.2 = none ∨ ∃ i, L.decodeIndex y a.2 = some i ∧ ∃ w, Rno i a.1 w)
      (stBA W S cA State) W.prjB hW.prjB_emb some (fun _ => rfl) εB hM hF
      hS
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
        -- the seed queries of the root stand in the trace before this query
        have hsd : ∀ c ∈ (cmsBA cA cm rec.2).take 1, SeedAsked W S pre c := by
          rcases ours_first0 _ hours with ⟨⟨salt, hq⟩, hr⟩ | ⟨q1, a1, salt, hm, hq, hr⟩
          · exact hfirst pre q a post _ _ salt htr hr hq
          · obtain ⟨p1, p2, hp⟩ := List.append_of_mem hm
            intro c hc
            refine (hfirst p1 q1 a1 (p2 ++ fbE Tag.onl q a :: post) _ _ salt ?_ hr hq c
              hc).mono ?_
            · rw [htr, hp]
              simp
            · intro e he
              rw [hp]
              exact List.mem_append_left _ he
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
        rw [e1, ansOutB_cmsBA hA, e4]
        rfl)
      (fun p a sl h => by
        change extLeaf tr W.B.ext.depth ((cmsBA cA cm rec.2).getD (W.B.ext.which p) default)
          (W.B.ext.leaf p) = _ at h
        rw [hW.extDepth, (hW.extB p).1, (hW.extB p).2] at h
        have h' : extLeaf tr W.depth cm p.val = some ⟨W.embE a, sl⟩ := h
        exact hW.ext.build_rd _ p a (by rw [h']; exact hW.prjE_emb a))

/-- The proof's arm is sound, at the lax session, at states with the session's clause. On a trace tr
that holds the answers of one family g of oracle functions (hg), has the order (`SeedsFirstB`) and
lies outside `BadBA`, in which the test of the seed and the lax session run and say yes: what the
arm promises holds. -/
theorem sessA_sound' {Rt : I → X → Prop} {εB : Err L.onlineBatch.loc.shape}
    {State : (oneExternalString L.wordLength L.Symbol).Str → X × L.Rec → PTr L.onlineBatch.loc.shape → Bool}
    (hSt : SessAt W S cA r₀ Rt εB State) {tr : Tc W}
    {g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))} (hg : ∀ e ∈ tr, e.2.2 = g e.1 e.2.1)
    (hfirst : SeedsFirstB W S tr) {cm : Dig lam} {x : X} {rec : L.Rec} {π : OneProtocolProof lam L.onlineBatch}
    (hB : ¬ BadBA W S cA εB State tr) (hs0 : RunsIn tr (outOfDomainSeedIs W S cm rec.1) true)
    (hrun : RunsIn tr (vBA' W cA r₀ cm x rec π) true) : ProofHolds W Rt tr cm x rec := by
  have hM : ¬ EM tr := fun h => hB (Or.inl (Or.inl h))
  have hF : ¬ EF tr := fun h => hB (Or.inl (Or.inr h))
  have hc0 : ¬ L.hasCollisionAt (extEnc W tr cm) rec.1 := seed_not_coll' hM hF (fun h => hB (Or.inr h)) hs0
  exact ⟨hc0, hSt.2 tr g cm x rec π hg hfirst hM hF
    (fun ⟨pre, e, post, h1, h2⟩ => hB (Or.inr ⟨pre, e, post, h1, Or.inl (Or.inr (Or.inr h2))⟩))
    hs0 hrun⟩

/-- A yes of the arm with the strict session holds the yes of the seed's test and of the lax
session, at a proof string that may differ in its paths' form. Premise: the laws of the session's
wire (hB). -/
theorem yes_VBA (hB : (wBC W).OKG) (p : Params) {tr : Tc W} {cm : Dig lam} {x : X} {rec : L.Rec}
    {π : OneProtocolProof lam L.onlineBatch} (hrun : RunsIn tr (VBA W S cA r₀ p cm x rec π) true) :
    RunsIn tr (outOfDomainSeedIs W S cm rec.1) true ∧ ∃ π', RunsIn tr (vBA' W cA r₀ cm x rec π') true := by
  unfold VBA at hrun
  simp only [runsIn_bind_iff, runsIn_pure_iff] at hrun
  obtain ⟨s0, hs0, b, hb, habc⟩ := hrun
  simp only [Bool.and_eq_true] at habc
  obtain ⟨rfl, rfl⟩ := habc
  obtain ⟨_, _, hb'⟩ := runsIn_verifyB_of_strict hB hb
  exact ⟨hs0, _, hb'⟩

/-- The same of the arm with the lax session. -/
theorem yes_VBA' {tr : Tc W} {cm : Dig lam} {x : X} {rec : L.Rec} {π : OneProtocolProof lam L.onlineBatch}
    (hrun : RunsIn tr (VBA' W S cA r₀ cm x rec π) true) :
    RunsIn tr (outOfDomainSeedIs W S cm rec.1) true ∧ ∃ π', RunsIn tr (vBA' W cA r₀ cm x rec π') true := by
  unfold VBA' at hrun
  simp only [runsIn_bind_iff, runsIn_pure_iff] at hrun
  obtain ⟨s0, hs0, b, hb, habc⟩ := hrun
  simp only [Bool.and_eq_true] at habc
  obtain ⟨rfl, rfl⟩ := habc
  exact ⟨hs0, _, hb⟩

variable (W S cA r₀)

/-- The arm with the lax session draws no coin and asks at most `tVB W` queries. -/
theorem detBound_VBA' (cm : Dig lam) (x : X) (rec : L.Rec) (π : OneProtocolProof lam L.onlineBatch) :
    DetBound (VBA' W S cA r₀ cm x rec π) (tVB W) := by
  unfold VBA' tVB
  refine ((detBound_seedIs W S _ _).bind (t := tVQB (wBC W) W.depthReq + 0) fun _ =>
    (detBound_verifyB _ _ _ _ _ _ _ _ _ _ _).bind (t := 0) fun _ => detBound_pure _ _).mono ?_
  omega

/-- The arm with the strict session draws no coin and asks at most `tVB W` queries. -/
theorem detBound_VBA (p : Params) (cm : Dig lam) (x : X) (rec : L.Rec) (π : OneProtocolProof lam L.onlineBatch) :
    DetBound (VBA W S cA r₀ p cm x rec π) (tVB W) := by
  unfold VBA tVB
  refine ((detBound_seedIs W S _ _).bind (t := tVQB (wBC W) W.depthReq + 0) fun _ =>
    (detBound_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _).bind (t := 0) fun _ => detBound_pure _ _).mono ?_
  omega

end TypedOracleCompiler.Compile.Batch.Cms
