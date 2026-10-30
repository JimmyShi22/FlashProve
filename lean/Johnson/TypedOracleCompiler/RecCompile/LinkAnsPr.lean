-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/LinkAnsPr.lean: the entry's arm with the answers alone in the first query,
for every algorithm, as a bound on a probability.

LinkAns.lean proves the entry's arm sound on traces in which the seed queries of a chain's two roots
stand before the chain's first query. A cheating prover need not ask in that order. Here the order
is had in the analysis alone: the algorithm that is judged (the maker of roots, records and proof
string, joined with the verifier's run) is wrapped so that it asks, before each first query of a
chain of Link, the seed queries of that query's two roots (`between`,
OnBytes/Slice/WrapBetween.lean). Under every fixed family of oracle functions the wrapped algorithm
has the same output; its trace is the old one with entries laid in; it asks at most five times as
many queries.

Two things that such an argument must mind, and where they are met.
  * A seed query may be asked again later, by the maker or by the verifier. The events of this
    analysis are caused by new entries alone: each asks that its entry stand nowhere before it in
    the trace (`stepSeed_new`; a lane's step, E_M and E_F likewise). So a repeat causes none. That
    is the events' clause, no property of the log, which holds repeats.
  * The wrapping is a map on algorithms that does not look at the oracle functions. What is laid in
    may read answers: the second seed query holds the first answer's chain value.

  `askSeed`, `askSeeds`, `preSeeds`   what is asked before a query
  `seedsFirst_of_asksFirst`          a trace that asks first has the order of LinkAns.lean
  `extEnc_lenB`                      the word under a root does not see the entries laid in
  `linkA_fixes`                      outside `BadLA` the word under a root is fixed once the root's
                                     first seed query is asked
  `LinkHolds`                        the conclusion of `linkA_sound`
  `IsArm`, `armS`, `armL`            an arm; the entry's arm with the strict Link, with the lax Link
  `arm_lift`                         the lift on one log: outside `BadLA` of the lengthened log the
                                     conclusion holds of the log itself
  `joinedA`, `joinedLA`              the maker, then an arm; then the arm with the strict Link
  `arm_pr`, `linkA_pr`               the bound: the arm accepts and the conclusion fails, on the
                                     trace of the maker and the arm, with probability at most
                                     n εs + 2 (n + 1)² / 2^lam at n = 5 (t + tVL)

Limits: soundness alone; typed oracles (the step to one hash function: LinkAnsOne.lean).
  * In this file the two words are those that the whole trace determines, the verifier's queries
    included. On traces outside `BadLA` they are fixed from the root's first seed query on
    (`linkA_fixes`). In probabilities: LinkAnsStay.lean (they stay), LinkAnsMaker.lean (they are the
    maker's), LinkAnsTwoStage.lean (the first is the committer's).
  * Where the first table decodes to nothing, nothing is said of the further table.
  * The factor 5: n = 5 (t + tVL), where the two halves of LinkOnly.lean, joined, would have
    t + tVL.
  * `AnsOK cA` is met by nothing shown in this folder (Johnson/Flat/EntryArm.lean meets it at a
    written code).
  * The record's wire S is fixed before the oracle is drawn, `S.cfg` with it: a digest in a table's
    name that is itself an answer of the oracle is not modelled.
  * No wire is made at an annotation with shared rounds. If Link has shared rounds, the joining
    query (F4) repeats the whole list, answers included.
  * What a coding owes: a map, one to one and fixed before the oracle, that sends the typed first
    query, the two seed queries and every later typed query to the programs' calls. With the answers
    alone in Link's first query such a map can spell that query as roots and answers. None is given,
    in this folder or in Johnson/Flat/: nothing there ties a typed point to a byte string, or `cA`
    to the statement's items.
  * No accepted run is shown: nothing here says that an arm ever says yes. The premises that
    `arm_pr`'s docstring names are laws of letters here. Johnson/Flat/EntryArm.lean
    and EntryWire.lean [not in this library] pay them at the entry file's
    protocol and a written wiring, Link's soundness under the theorem on codes as a hypothesis.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.LinkAns
import OnBytes.TypedOracleCompiler.Compile.Batch.Local
import OnBytes.Slice.WrapBetween

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal
open OnBytes.Slice

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-! ## Tools on logs -/

section Tools
variable {Sp : OSpec} {α β : Type}

/-- the log of one algorithm and then another, under g -/
theorem log_bind (g : Fam Sp) (c : OComp Sp α) (k : α → OComp Sp β) :
    ((c.bind k).withTrace.det g).2 =
      (c.withTrace.det g).2 ++ ((k (c.withTrace.det g).1).withTrace.det g).2 := by
  rw [Rom.withTrace_bind, OComp.det_bind, OComp.det_bind]
  rfl

/-- an outcome of one algorithm and then another, with its log -/
theorem support_withTrace_bind (g : Fam Sp) (c : OComp Sp α) (k : α → OComp Sp β) :
    ∀ o ∈ ((c.bind k).withTrace.runEager g).support,
      ∃ a ∈ (c.withTrace.runEager g).support, ∃ b ∈ ((k a.1).withTrace.runEager g).support,
        o = (b.1, a.2 ++ b.2) := by
  intro o ho
  rw [Rom.withTrace_bind, OComp.runEager_bind, PMF.mem_support_bind_iff] at ho
  obtain ⟨a, ha, ho⟩ := ho
  rw [OComp.runEager_bind, PMF.mem_support_bind_iff] at ho
  obtain ⟨b, hb, ho⟩ := ho
  refine ⟨a, ha, b, hb, ?_⟩
  simpa [OComp.runEager] using ho

/-- a law and its image under a map: an event that the map carries into another, on the support -/
theorem pr_le_pr_map (μ : PMF α) (φ : α → β) (E : Set α) (E' : Set β)
    (h : ∀ o ∈ μ.support, o ∈ E → φ o ∈ E') : pr μ E ≤ pr (μ.map φ) E' := by
  have h1 := pr_bind_le_bind μ PMF.pure (fun a => PMF.pure (φ a)) E E'
    fun a ha => pr_pure_le_pure (h a ha)
  rwa [PMF.bind_pure, show (μ.bind fun a => PMF.pure (φ a)) = μ.map φ from
    PMF.bind_pure_comp φ μ] at h1

end Tools

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)

/-! ## What is asked before a query -/

/-- ask the two seed queries of a root -/
def askSeed (c : Dig lam) : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Unit :=
  (OComp.ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (OracleName.fb S.t) (seedQ0 W S c)).bind fun a0 =>
    (OComp.ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (OracleName.fb S.t)
      (seedQ1 W S (link (show FsAns lam W.K from a0)))).bind fun _ => OComp.pure ()

/-- ask the seed queries of each root of a list -/
def askSeeds : List (Dig lam) → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Unit
  | [] => OComp.pure ()
  | c :: l => (askSeed W S c).bind fun _ => askSeeds l

/-- before a first query of a chain of Link: the seed queries of the two first entries of its list
-/
def preLink (q : FbIn lam (typedOracleCarrier L Bd aT aL) Tag.link) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Unit :=
  if q.round = 0 then
    match q.head with
    | .f1 cms _ _ => askSeeds W S (cms.take 2)
    | _ => OComp.pure ()
  else OComp.pure ()

/-- what is asked before a query: nothing, but before a first query of a chain of Link -/
def preSeeds : (o : OracleName) → domOf lam (typedOracleCarrier L Bd aT aL) o → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Unit
  | OracleName.fb Tag.link, q => preLink W S q
  | _, _ => OComp.pure ()

/-- `preSeeds`, typed as a wrapping of algorithms over the typed oracles wants it -/
abbrev preS : (o : (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)).ι) →
    (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)).Dom o → OComp (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) Unit :=
  preSeeds W S

/-- To ask a root's two seed queries draws no coin and takes two queries. -/
theorem detBound_askSeed (c : Dig lam) : DetBound (askSeed W S c) 2 := by
  unfold askSeed
  exact (detBound_ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) _ _).bind (t := 1) fun a0 =>
    (detBound_ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) _ _).bind (t := 0) fun _ =>
      detBound_pure _ _

/-- For a list of roots: no coin, two queries a root. -/
theorem detBound_askSeeds : ∀ l : List (Dig lam), DetBound (askSeeds W S l) (2 * l.length)
  | [] => detBound_pure _ _
  | c :: l => ((detBound_askSeed W S c).bind fun _ => detBound_askSeeds l).mono (by
      simp only [List.length_cons]
      omega)

/-- What is asked before a query of Link's chain: no coin, at most four queries. -/
theorem detBound_preLink (q : FbIn lam (typedOracleCarrier L Bd aT aL) Tag.link) :
    DetBound (preLink W S q) 4 := by
  unfold preLink
  split
  · split
    · rename_i cms _ _ _
      exact (detBound_askSeeds W S _).mono (by
        have := List.length_take_le 2 cms
        omega)
    · exact detBound_pure _ _
  · exact detBound_pure _ _

/-- What is asked before any query: no coin, at most four queries. -/
theorem detBound_preSeeds (o : OracleName) (q : domOf lam (typedOracleCarrier L Bd aT aL) o) :
    DetBound (preSeeds W S o q) 4 := by
  cases o with
  | fb t => cases t <;> first | exact detBound_preLink W S q | exact detBound_pure _ _
  | _ => exact detBound_pure _ _

variable (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))

/-- the log of the two seed queries of a root -/
theorem log_askSeed (c : Dig lam) :
    ((askSeed W S c).withTrace.det g).2 =
      [fbE S.t (seedQ0 W S c) (g (OracleName.fb S.t) (seedQ0 W S c)),
        fbE S.t (seedQ1 W S (link (show FsAns lam W.K from g (OracleName.fb S.t) (seedQ0 W S c))))
          (g (OracleName.fb S.t)
            (seedQ1 W S (link (show FsAns lam W.K from g (OracleName.fb S.t) (seedQ0 W S c)))))] := rfl

/-- In the log of `askSeeds` at a list stand the seed queries of each root of the list. -/
theorem seedAsked_log : ∀ (l : List (Dig lam)) (c : Dig lam), c ∈ l →
    SeedAsked W S ((askSeeds W S l).withTrace.det g).2 c
  | c' :: l, c, hc => by
    have e : ((askSeeds W S (c' :: l)).withTrace.det g).2 =
        ((askSeed W S c').withTrace.det g).2 ++ ((askSeeds W S l).withTrace.det g).2 :=
      log_bind g _ _
    rw [e]
    rcases List.mem_cons.1 hc with rfl | hc
    · rw [log_askSeed]
      exact ⟨((show FsAns lam W.K from g (OracleName.fb S.t) (seedQ0 W S c)),
          (show FsAns lam W.K from g (OracleName.fb S.t)
            (seedQ1 W S (link (show FsAns lam W.K from g (OracleName.fb S.t) (seedQ0 W S c)))))),
        List.mem_append_left _ List.mem_cons_self,
        List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    · exact (seedAsked_log l c hc).mono fun x hx => List.mem_append_right _ hx

/-- every entry of that log is a query to the seeds' oracle in a round other than 0 -/
theorem round_log : ∀ (l : List (Dig lam)), ∀ x ∈ ((askSeeds W S l).withTrace.det g).2,
    ∃ (q : FbIn lam (typedOracleCarrier L Bd aT aL) S.t) (a : FsAns lam W.K), x = fbE S.t q a ∧ q.round ≠ 0
  | [], x, hx => absurd hx List.not_mem_nil
  | c :: l, x, hx => by
    have e : ((askSeeds W S (c :: l)).withTrace.det g).2 =
        ((askSeed W S c).withTrace.det g).2 ++ ((askSeeds W S l).withTrace.det g).2 :=
      log_bind g _ _
    rw [e, log_askSeed] at hx
    rcases List.mem_append.1 hx with h | h
    · rcases List.mem_cons.1 h with rfl | h
      · exact ⟨_, _, rfl, by simp [seedQ0]⟩
      · rw [List.mem_singleton.1 h]
        exact ⟨_, _, rfl, by simp [seedQ1]⟩
    · exact round_log l x h

/-- nothing is asked before a query in a round other than 0 -/
theorem preSeeds_round {t : Tag} (q : FbIn lam (typedOracleCarrier L Bd aT aL) t) (h : q.round ≠ 0) :
    preSeeds W S (OracleName.fb t) q = OComp.pure () := by
  cases t
  · rfl
  · show preLink W S q = _
    unfold preLink
    rw [if_neg h]
  · rfl

/-- every entry of the log of what is asked before a query is such a query -/
theorem round_preSeeds (o : OracleName) (q : domOf lam (typedOracleCarrier L Bd aT aL) o) :
    ∀ x ∈ ((preSeeds W S o q).withTrace.det g).2,
      ∃ (q' : FbIn lam (typedOracleCarrier L Bd aT aL) S.t) (a : FsAns lam W.K),
        x = fbE S.t q' a ∧ q'.round ≠ 0 := by
  intro x hx
  cases o with
  | fb t =>
    cases t with
    | link =>
      have hx' : x ∈ ((preLink W S q).withTrace.det g).2 := hx
      unfold preLink at hx'
      split at hx'
      · split at hx'
        · exact round_log W S g _ x hx'
        · exact absurd hx' List.not_mem_nil
      · exact absurd hx' List.not_mem_nil
    | _ => exact absurd hx List.not_mem_nil
  | _ => exact absurd hx List.not_mem_nil

/-- What is asked before a query asks nothing for its own queries. -/
theorem idle_preSeeds (o : OracleName) (q : domOf lam (typedOracleCarrier L Bd aT aL) o) :
    ∀ x ∈ ((preSeeds W S o q).withTrace.det g).2,
      ((preSeeds W S x.1 x.2.1).withTrace.det g).2 = [] := by
  intro x hx
  obtain ⟨q', a, rfl, hr⟩ := round_preSeeds W S g o q x hx
  show ((preSeeds W S (OracleName.fb S.t) q').withTrace.det g).2 = []
  rw [preSeeds_round W S q' hr]
  rfl

/-- A trace that asks first has the order. -/
theorem seedsFirst_of_asksFirst (σ : Tc W) (h : AsksFirst (preS W S) g σ) :
    SeedsFirst W S σ := by
  intro pre q a post cms x salt htr hr hq c hc
  have hb := asksFirst_before (preS W S) g σ h (idle_preSeeds W S g) pre (fbE Tag.link q a) post
    htr
  have e : preSeeds W S (OracleName.fb Tag.link) q = askSeeds W S (cms.take 2) := by
    show preLink W S q = _
    unfold preLink
    rw [if_pos hr, hq]
  have hb' : ∀ x ∈ ((askSeeds W S (cms.take 2)).withTrace.det g).2, x ∈ pre := by
    rw [← e]
    exact hb
  exact (seedAsked_log W S g _ c hc).mono hb'

/-! ## The word under a root does not see the entries laid in -/

/-- is the entry no query to a Fiat-Shamir oracle? -/
def notFb (e : QA (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) : Bool :=
  match e.1 with
  | OracleName.fb _ => false
  | _ => true

/-- The word under a root does not see the queries to the Fiat-Shamir oracles. -/
theorem extEnc_filter (tr : Tc W) (cm : Dig lam) :
    extEnc W (tr.filter (notFb W)) cm = extEnc W tr cm := by
  have h : ∀ d c j, extLeaf (tr.filter (notFb W)) d c j = extLeaf tr d c j := by
    intro d c j
    unfold extLeaf
    refine Local.preimage_filter (pairM lam W.K (typedOracleCarrier L Bd aT aL)) _ ?_ ?_ tr _ c
    · rintro ⟨o, q, r⟩ ho
      cases o <;> first | rfl | (simp [notFb] at ho)
    · rintro ⟨o, q, r⟩ ho
      cases o <;> first | rfl | (simp [notFb] at ho)
  simp only [extEnc, h]

/-- The entries laid in are queries to a Fiat-Shamir oracle. -/
theorem filter_lenB : ∀ σ : Tc W,
    (lenB (preS W S) g σ).filter (notFb W) = σ.filter (notFb W)
  | [] => rfl
  | e :: σ => by
    show (((preSeeds W S e.1 e.2.1).withTrace.det g).2 ++ e :: lenB (preS W S) g σ).filter
      (notFb W) = _
    have h0 : (((preSeeds W S e.1 e.2.1).withTrace.det g).2).filter (notFb W) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx
      obtain ⟨q', a, rfl, -⟩ := round_preSeeds W S g e.1 e.2.1 x hx
      simp [notFb, fbE]
    rw [List.filter_append, h0, List.nil_append, List.filter_cons, List.filter_cons, filter_lenB σ]

/-- So the word under a root does not see the entries laid in. -/
theorem extEnc_lenB (σ : Tc W) (cm : Dig lam) :
    extEnc W (lenB (preS W S) g σ) cm = extEnc W σ cm := by
  rw [← extEnc_filter W (lenB (preS W S) g σ), filter_lenB, extEnc_filter]

/-! ## The words stay -/

/-- Outside the set `BadLA` the word under a root is fixed once the first query of the root's seed
is asked: what the entry's arm promises of the words at the end of a trace, it promises of the words
as they were then. No other premise. -/
theorem linkA_fixes {cA : L.OutOfDomainAnswer → List (Dig lam)} {εL : Err L.link.shape} {tr tr' : Tc W}
    (hB : ¬ BadLA W S cA εL (tr ++ tr')) {cm : Dig lam} {a0 : FsAns lam W.K}
    (h : fbE S.t (seedQ0 W S cm) a0 ∈ tr) : extEnc W tr cm = extEnc W (tr ++ tr') cm :=
  seed_fixes (fun hM => hB (Or.inl (Or.inl hM))) h

/-! ## The bound -/

variable (cA : L.OutOfDomainAnswer → List (Dig lam))

/-- What the entry's arm promises of a trace, two roots and two records. -/
def LinkHolds (tr : Tc W) (cm cm' : Dig lam) (rec rec' : L.Rec) : Prop :=
  ¬ L.hasCollisionAt (extEnc W tr cm) rec.1 ∧ ¬ L.hasCollisionAt (extEnc W tr cm') rec'.1 ∧
    (L.decodeIndex (extEnc W tr cm) rec = none ∨
      L.decodeIndex (extEnc W tr cm') rec' = L.decodeIndex (extEnc W tr cm) rec)

/-- what a maker puts out: two roots, two records, Link's proof string -/
abbrev OutLA (lam : ℕ) (L : HolographicProtocol I X) (aL : RoundSplits L.link.shape) : Type :=
  Dig lam × Dig lam × L.Rec × L.Rec × OneProtocolProof lam (batLC L aL)

/-- An arm: an algorithm on what a maker puts out that draws no coin, asks at most `tVL` queries,
and whose yes holds the yes of the two seeds' tests and of the lax Link at some proof string. -/
structure IsArm (V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool) : Prop where
  det : ∀ z, DetBound (V z) (tVL W)
  yes : ∀ z tr, RunsIn tr (V z) true →
    RunsIn tr (outOfDomainSeedIs W S z.1 z.2.2.1.1) true ∧ RunsIn tr (outOfDomainSeedIs W S z.2.1 z.2.2.2.1.1) true ∧
      ∃ π', RunsIn tr (vLA' W cA z.1 z.2.1 z.2.2.1 z.2.2.2.1 π') true

/-- the arm with the strict Link -/
def armS (p : Params) (z : OutLA lam L aL) : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  VLA W S cA p z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2

/-- the arm with the lax Link -/
def armL (z : OutLA lam L aL) : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  VLA' W S cA z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2

/-- The entry's arm with the strict Link is an arm. Premise: the laws of Link's wire (hLk). -/
theorem isArm_armS (hLk : (wLC W).OKG) (p : Params) : IsArm W S cA (armS W S cA p) :=
  ⟨fun _ => detBound_VLA W S cA p _ _ _ _ _, fun _ _ h => yes_VLA hLk p h⟩

/-- The entry's arm with the lax Link is an arm. -/
theorem isArm_armL : IsArm W S cA (armL W S cA) :=
  ⟨fun _ => detBound_VLA' W S cA _ _ _ _ _, fun _ _ h => yes_VLA' h⟩

/-- The maker, then an arm on what the maker has put out. -/
def joinedA (V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool)
    (A : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (OutLA lam L aL)) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (OutLA lam L aL × Bool) :=
  A.bind fun z => (V z).bind fun b => OComp.pure (z, b)

/-- The maker, then the entry's arm of the verifier on what the maker has put out. -/
def joinedLA (p : Params) (A : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (OutLA lam L aL)) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (OutLA lam L aL × Bool) :=
  joinedA W (armS W S cA p) A

variable {W S cA}

/-- A maker with at most t queries, then an arm: at most t + `tVL W` queries. -/
theorem joinedA_queryBound {V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    (hV : IsArm W S cA V) {A : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (OutLA lam L aL)}
    {t : ℕ} (hA : A.QueryBound t) : (joinedA W V A).QueryBound (t + tVL W) := by
  have h : (joinedA W V A).QueryBound (t + (tVL W + 0)) := by
    unfold joinedA
    exact hA.bind fun z => (hV.det z).queryBound.bind fun _ => trivial
  exact h.mono (by omega)

/-- The lift, on one log: for every family f of oracle functions and every log σ with f's answers
(hans) in which an arm (`IsArm`) accepts: if the lengthened log lies outside `BadLA`, what the arm
promises holds of σ itself. No order is asked of σ. Premises: Link is sound round by round, with the
errors εL, for the language "the first table decodes to nothing, or the further record's seed is a
collision seed of the further word, or the further table decodes to what the first decodes to"
(hsL); Link's verifier is local (hlL); the annotation aL is coherent (hcL); the wires that Link
reads have their laws (`OKLA W`); the code of the answers is one to one, with one length
(`AnsOK cA`). -/
theorem arm_lift {εL : Err L.link.shape}
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hcL : aL.Coherent) (hW : OKLA W) (hA : AnsOK cA)
    {V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool} (hV : IsArm W S cA V)
    (f : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) {σ : Tc W}
    (hans : ∀ e ∈ σ, e.2.2 = f e.1 e.2.1) {z : OutLA lam L aL} (hrun : RunsIn σ (V z) true)
    (hnb : ¬ BadLA W S cA εL (lenB (preS W S) f σ)) :
    LinkHolds W σ z.1 z.2.1 z.2.2.1 z.2.2.2.1 := by
  have hn : ∀ o q, (preSeeds W S o q).NoCoin := fun o q =>
    noCoin_of_detBound (detBound_preSeeds W S o q)
  obtain ⟨hs0, hs1, _, hb⟩ := hV.yes z _ (hrun.mono fun e he => mem_lenB (preS W S) f _ e he)
  have h := linkA_sound' hsL hlL hcL hW hA (lenB_ans (preS W S) hn f _ hans)
    (seedsFirst_of_asksFirst W S f _ ⟨_, rfl⟩) hnb hs0 hs1 hb
  unfold LinkHolds
  simpa only [extEnc_lenB] using h

/-- An arm (`IsArm`) is sound against every maker: it accepts, and what it promises fails on the
trace of the maker and the arm, with probability at most n εs + 2 (n + 1)² / 2^lam, where
n = 5 (t + tVL) and t bounds the maker's queries (hq). Premises: Link is sound round by round, with
the errors εL, for the language "the first table decodes to nothing, or the further record's seed is
a collision seed of the further word, or the further table decodes to what the first decodes to"
(hsL); Link's verifier is local (hlL); the annotation aL is coherent (hcL); the wires that Link
reads have their laws (`OKLA W`); the code of the answers is one to one, with one length
(`AnsOK cA`); the seed's law at εs (`S.Law εs`); no round's error, counted as often as the request
tree has leaves where the round is shared, is above εs (hbL). -/
theorem arm_pr {εL : Err L.link.shape} {εs : ℝ≥0∞}
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hcL : aL.Coherent) (hW : OKLA W) (hA : AnsOK cA) (hSd : S.Law εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs)
    {V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool} (hV : IsArm W S cA V)
    (A : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (OutLA lam L aL)) (t : ℕ) (hq : A.QueryBound t) :
    Rom.Pr (joinedA W V A).withTrace
        (fun _ => {o | o.1.2 = true ∧
          ¬ LinkHolds W o.2 o.1.1.1 o.1.1.2.1 o.1.1.2.2.1 o.1.1.2.2.2.1}) ≤
      (((t + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  have hn : ∀ o q, (preSeeds W S o q).NoCoin := fun o q =>
    noCoin_of_detBound (detBound_preSeeds W S o q)
  have hpt : ∀ f : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)),
      PrCoins f (joinedA W V A).withTrace
          {o | o.1.2 = true ∧ ¬ LinkHolds W o.2 o.1.1.1 o.1.1.2.1 o.1.1.2.2.1 o.1.1.2.2.2.1} ≤
        PrCoins f (between (preS W S) (joinedA W V A)).withTrace
          {o | BadLA W S cA εL o.2} := by
    intro f
    unfold PrCoins
    rw [between_law (preS W S) hn f]
    refine pr_le_pr_map _ _ _ _ fun o ho => ?_
    rintro ⟨hacc, hbad⟩
    show BadLA W S cA εL (lenB (preS W S) f o.2)
    by_contra hnb
    -- the outcome falls into the maker's and the arm's
    obtain ⟨a, -, b, hb, rfl⟩ := support_withTrace_bind f A _ o ho
    obtain ⟨c, hc, d, hd, rfl⟩ := support_withTrace_bind f _ _ b hb
    have hd' : d = ((a.1, c.1), []) := by
      simpa [OComp.withTrace, OComp.runEager] using hd
    subst hd'
    have hc1 : c.1 = true := hacc
    have hrun : RunsIn c.2 (V a.1) true := by
      have := runsIn_of_mem_support (hV.det a.1) f c hc
      rwa [hc1] at this
    exact hbad (arm_lift hsL hlL hcL hW hA hV f (support_withTrace_ans f _ _ ho)
      (hrun.mono fun e he => List.mem_append_right _ (List.mem_append_left _ he)) hnb)
  calc
    Rom.Pr (joinedA W V A).withTrace
          (fun _ => {o | o.1.2 = true ∧
            ¬ LinkHolds W o.2 o.1.1.1 o.1.1.2.1 o.1.1.2.2.1 o.1.1.2.2.2.1}) ≤
        Rom.Pr (between (preS W S) (joinedA W V A)).withTrace
          (fun _ => {o | BadLA W S cA εL o.2}) :=
      MeasureTheory.lintegral_mono hpt
    _ = pr (between (preS W S) (joinedA W V A)).withTrace.law
          {o | BadLA W S cA εL o.2} := Pr_eq_law _ _
    _ ≤ _ := badLA_rare hSd hbL hW.Lk _ _
        (between_bound (preS W S) 4 (fun o q => (detBound_preSeeds W S o q).queryBound) _ _
          (joinedA_queryBound hV hq))

/-- The entry's arm is sound against every maker: `arm_pr` at the arm with the strict Link, under
the premises of `arm_pr`: the arm accepts, and what it promises fails on the trace of the maker and
the arm, with probability at most n εs + 2 (n + 1)² / 2^lam, where n = 5 (t + tVL) and t bounds the
maker's queries (hq). -/
theorem linkA_pr {εL : Err L.link.shape} {εs : ℝ≥0∞}
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hcL : aL.Coherent) (hW : OKLA W) (hA : AnsOK cA) (hSd : S.Law εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs) (p : Params)
    (A : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (OutLA lam L aL)) (t : ℕ) (hq : A.QueryBound t) :
    Rom.Pr (joinedLA W S cA p A).withTrace
        (fun _ => {o | o.1.2 = true ∧
          ¬ LinkHolds W o.2 o.1.1.1 o.1.1.2.1 o.1.1.2.2.1 o.1.1.2.2.2.1}) ≤
      (((t + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam :=
  arm_pr hsL hlL hcL hW hA hSd hbL (isArm_armS W S cA hW.Lk p) A t hq

end TypedOracleCompiler.Compile.Batch.Cms
