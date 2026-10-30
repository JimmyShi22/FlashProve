-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/Seeds.lean: the seed of a table's record, drawn by two nested queries at one
tag, over the compiler's verifier side in lean/OnBytes/TypedOracleCompiler/. Definitions, the
seed's event, and what the compiled verifier for an object with records needs of them.

The record of an encoded index begins with a seed, which the verifier recomputes from the root of
the tree over the index. Here the drawing is meant to follow the programs; the tie is the coding's
matter: a first query holds the table's
name (the root; then what else the name holds: `OutOfDomainSampleQueryLayout.cfg`, `OutOfDomainSampleQueryLayout.shape`); a second query holds the
chain value of the first answer; the seed is read off the second answer. Both queries go to the
Fiat-Shamir oracle of one tag, whichever table it is: there is no role.

How the two queries are typed. The first: round 1 with a head (F1). The second: round 2 with a head
(F2), whose chain field is the first answer's chain value.
  * A head (F1) stands in a chain in round 0 only, so the first query is no rooted query
    (`rooted`, OnBytes/TypedOracleCompiler/Compile/Batch/Rooted.lean), and a second query whose chain field leads
    back to it is none either (`not_step_seed`): the answer to one query causes at most one event.
  * The chain value stands in the second query as a chain field, so the event E_F covers it: outside
    E_F the first query comes before the second, and no other query has that chain value
    (`mem_of_link_occurs`, `predF_eq`). That is what ties the seed to the root.
  * The root is the first entry of the head's list, so it occurs at the first query: outside E_M
    the word under it is fixed from then on.
The numbers 1 and 2 are names of typed points. Which strings stand for them is the matter of the
encoding of the queries (`Rom.OracleCoding`), not of this file.

Main names:
  `OutOfDomainSampleQueryLayout`, `OutOfDomainSampleQueryLayout.OK`, `OutOfDomainSampleQueryLayout.Law`: the wire of the record, its law, and what is used of the map
    from digests to seeds.
  `seedQ0`, `seedQ1`, `outOfDomainSeedIs`: the two queries; "ask both: is the seed s?".
  `seedQ0_inj`: two roots have two first queries.
  `detBound_seedIs`, `runsIn_seedIs`: two queries; what a run in a trace says.
  `stepSeed`: the entry is a new second query whose chain field leads back to the first query of a
    root, and its seed is a collision seed of the word that the trace determines under that root.
  `pr_step4_le`: the answer to one query causes a lane's event or the seed's with probability at
    most εs.
  `stepSeed_new`: the seed's event is caused by a new entry.
  `seed_not_coll`: outside E_M, E_F and the seed's event, a seed that the verifier has recomputed
    is no collision seed of the word under its root.
  `seed_fixes`: outside E_M the word under a root is fixed once the root's first query is asked.

Limits: soundness' side alone. Nothing says here which strings the two queries are, nor that the
name's further entries are those of the table. `S.cfg` and `S.shape` are one for all tables, which
is right only if the two tables' names differ in the root alone; `S.pl1` is fixed, which is right
only if the programs' round call for a seed holds no nonce. `S.num` is a letter under no law.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.Carrier
import OnBytes.TypedOracleCompiler.Compile.Batch.Sound
import OnBytes.TypedOracleCompiler.Compile.Batch.GlueTools

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam : ℕ}

/-- The wire of the record: the tag of the seeds' queries; what a table's name holds behind the
root; the fixed plain parts of the two queries; how K digests give a seed; how a record is written
as a list of digests; where a session's proof string holds the number of the stored copy. -/
structure OutOfDomainSampleQueryLayout (lam K : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) where
  /-- the tag of the Fiat-Shamir oracle that gives the seeds: one for all tables -/
  t : Tag
  /-- the digests of a table's name behind the root -/
  cfg : List (Dig lam)
  /-- the rest of a table's name; it rides in the salt's field of the first query (F1) -/
  shape : Bits
  pl0 : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) t) (annOf (typedOracleCarrier L Bd aT aL) t)
  pl1 : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) t) (annOf (typedOracleCarrier L Bd aT aL) t)
  seed : (Fin K → Dig lam) → L.OutOfDomainSeed
  code : L.Rec → List (Dig lam)
  /-- meant as: do the plain parts of a session's proof string hold this number of a stored copy, at
  the place where the first query of the session's chain takes it in? A letter; no law. -/
  num : ℕ → Plains L.onlineBatch.loc.shape → Bool
  /-- equality of seeds, as data: the verifier compares two seeds -/
  decS : DecidableEq L.OutOfDomainSeed

structure OutOfDomainSampleQueryLayout.OK {K : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} (S : OutOfDomainSampleQueryLayout lam K L Bd aT aL) : Prop where
  inj : Function.Injective S.code
  /-- all records are written with one number of digests: so two in a row can be told apart -/
  len : ∀ r r', (S.code r).length = (S.code r').length

/-- What is used of the map from digests to seeds: for every word, the seed of K uniform digests is
a collision seed with probability at most εs. -/
def OutOfDomainSampleQueryLayout.Law {K : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} (S : OutOfDomainSampleQueryLayout lam K L Bd aT aL) (εs : ℝ≥0∞) : Prop :=
  ∀ y, pr (unif (Fin K → Dig lam)) {a | L.hasCollisionAt y (S.seed a)} ≤ εs

variable {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)

/-- The first query of a seed: the table's name, with the root first. -/
def seedQ0 (cm : Dig lam) : FbIn lam (typedOracleCarrier L Bd aT aL) S.t :=
  ⟨1, .f1 (cm :: S.cfg) none S.shape, [], S.pl0⟩

/-- The second query of a seed: the chain value of the first answer. -/
def seedQ1 (v : Bits) : FbIn lam (typedOracleCarrier L Bd aT aL) S.t := ⟨2, .f2 none v, [], S.pl1⟩

theorem seedQ0_inj {cm cm' : Dig lam} (h : seedQ0 W S cm = seedQ0 W S cm') : cm = cm' := by
  have h2 := congrArg (fun z : FbIn lam (typedOracleCarrier L Bd aT aL) S.t => z.head) h
  simpa [seedQ0] using h2

theorem seedQ1_inj {v v' : Bits} (h : seedQ1 W S v = seedQ1 W S v') : v = v' := by
  have h2 := congrArg (fun z : FbIn lam (typedOracleCarrier L Bd aT aL) S.t => z.head) h
  simpa [seedQ1] using h2

/-- ask the two queries of the seed at the root cm; is the seed s? -/
def outOfDomainSeedIs (cm : Dig lam) (s : L.OutOfDomainSeed) : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  (OComp.ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (OracleName.fb S.t)
    (seedQ0 W S cm)).bind fun a0 =>
    (OComp.ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) (OracleName.fb S.t)
      (seedQ1 W S (link (show FsAns lam W.K from a0)))).bind fun a1 =>
      OComp.pure (@decide _ (S.decS (S.seed (show FsAns lam W.K from a1).1) s))

theorem detBound_seedIs (cm : Dig lam) (s : L.OutOfDomainSeed) : DetBound (outOfDomainSeedIs W S cm s) 2 := by
  unfold outOfDomainSeedIs
  exact (detBound_ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) _ _).bind (t := 1) fun a0 =>
    (detBound_ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) _ _).bind (t := 0) fun a1 =>
      detBound_pure _ _

variable {W S}

theorem runsIn_seedIs {tr : Tc W} {cm : Dig lam} {s : L.OutOfDomainSeed}
    (h : RunsIn tr (outOfDomainSeedIs W S cm s) true) :
    ∃ a0 a1 : FsAns lam W.K, fbE S.t (seedQ0 W S cm) a0 ∈ tr ∧
      fbE S.t (seedQ1 W S (link a0)) a1 ∈ tr ∧ S.seed a1.1 = s := by
  unfold outOfDomainSeedIs at h
  obtain ⟨a0, h0, h2⟩ := (runsIn_bind_iff _ _ _).1 h
  obtain ⟨a1, h1, h3⟩ := (runsIn_bind_iff _ _ _).1 h2
  refine ⟨a0, a1, runsIn_ask_iff.1 h0, runsIn_ask_iff.1 h1, ?_⟩
  have h4 := runsIn_pure_iff.1 h3
  simpa using h4

variable (W S)

/-! ## The seed's event -/

/-- The entry e, after the trace pre, is a new second query of a seed; its chain field leads back,
in pre, to the first query at a root cm; and its seed is a collision seed of the word that pre
determines under cm. -/
def stepSeed (pre : Tc W) (e : QA (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) : Prop :=
  e ∉ pre ∧ ∃ (v : Bits) (a : FsAns lam W.K) (cm : Dig lam) (a0 : FsAns lam W.K),
    e = fbE S.t (seedQ1 W S v) a ∧ predF S.t pre 1 v = some (seedQ0 W S cm, a0) ∧
      L.hasCollisionAt (extEnc W pre cm) (S.seed a.1)

theorem stepSeed_new {pre : Tc W} {e : QA (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))}
    (h : stepSeed W S pre e) : e ∉ pre := h.1

/-- A second query whose chain field leads back to a seed's first query is no rooted query: it
causes no lane's event. -/
theorem not_step_seed (ℓ : Lane W) (pre : Tc W) (v : Bits) (a : FsAns lam W.K) (cm : Dig lam)
    (a0 : FsAns lam W.K) (hp : predF S.t pre 1 v = some (seedQ0 W S cm, a0)) :
    ¬ ℓ.step pre (fbE S.t (seedQ1 W S v) a) := by
  obtain ⟨t', s, A, ws, pS, pP, ε, st⟩ := ℓ
  rintro ⟨-, q', a', D, he, hr, -⟩
  have ht : S.t = t' := OracleName.fb.inj (congrArg Sigma.fst he)
  subst ht
  obtain ⟨rfl, -⟩ := fbE_inj he
  have h0 : rooted S.t pre 2 (.f2 none v) = none := by
    show viaTail (rooted S.t pre 1) pre 1 v = none
    unfold viaTail
    rw [hp]
    rfl
  exact absurd (h0.symm.trans hr) (by simp)

theorem pr_seed_le {εs : ℝ≥0∞} (hS : S.Law εs) (y : Fin L.wordLength → L.Symbol) :
    pr (unif (FsAns lam W.K)) {a | L.hasCollisionAt y (S.seed a.1)} ≤ εs := by
  have h1 : pr (unif (FsAns lam W.K)) {a | L.hasCollisionAt y (S.seed a.1)}
      = pr ((unif (FsAns lam W.K)).map Prod.fst) {b | L.hasCollisionAt y (S.seed b)} := by
    rw [pr_map]; rfl
  rw [h1, map_fst_unif]
  exact hS y

/-- The answer to one query causes one of the four events with probability at most εs: a query
belongs to one of them only. -/
theorem pr_step4_le {ℓT ℓL ℓB : Lane W} (hT : ℓT.t = Tag.test) (hL : ℓL.t = Tag.link)
    (hB : ℓB.t = Tag.onl) {NT NL NB : ℕ} (hNT : NT = 2 ^ W.depthReqT) (hNL : NL = 2 ^ W.depthReqL)
    (hNB : NB = 2 ^ W.depthReq) (oT : ℓT.OK NT) (oL : ℓL.OK NL)
    (oB : ℓB.OK NB) {εs : ℝ≥0∞} (bT : Err.Below ℓT.ε εs) (bL : Err.Below ℓL.ε εs)
    (bB : Err.Below ℓB.ε εs) (hS : S.Law εs)
    (pre : Tc W) (o : OracleName) (q : domOf lam (typedOracleCarrier L Bd aT aL) o) :
    pr (unif ((typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)).Rng o))
        {r | stepS W ℓT ℓL ℓB pre (⟨o, q, r⟩ : QA (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) ∨
          stepSeed W S pre (⟨o, q, r⟩ : QA (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))} ≤ εs := by
  by_cases h : ∃ v cm a0,
      (⟨o, q⟩ : Σ o, domOf lam (typedOracleCarrier L Bd aT aL) o) = ⟨OracleName.fb S.t, seedQ1 W S v⟩ ∧
        predF S.t pre 1 v = some (seedQ0 W S cm, a0)
  · obtain ⟨v, cm, a0, h, hp⟩ := h
    cases h
    refine le_trans (pr_mono _ ?_) (pr_seed_le W S hS (extEnc W pre cm))
    rintro r ((h | h | h) | ⟨-, v', a, cm', a0', he, hp', hc⟩)
    · exact absurd h (not_step_seed W S _ pre v r cm a0 hp)
    · exact absurd h (not_step_seed W S _ pre v r cm a0 hp)
    · exact absurd h (not_step_seed W S _ pre v r cm a0 hp)
    · obtain ⟨hq, rfl⟩ := fbE_inj he
      obtain rfl := seedQ1_inj W S hq
      rw [hp] at hp'
      obtain rfl := seedQ0_inj W S (congrArg Prod.fst (Option.some.inj hp'))
      exact hc
  · refine le_trans (pr_mono _ ?_) (pr_stepS_le hT hL hB hNT hNL hNB oT oL oB bT bL bB pre o q)
    rintro r (h1 | ⟨-, v, a, cm, a0, he, hp, -⟩)
    · exact h1
    · refine absurd ⟨v, cm, a0, ?_, hp⟩ h
      have he' : (⟨o, q, r⟩ : QA (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))) =
          ⟨OracleName.fb S.t, seedQ1 W S v, a⟩ := he
      cases he'
      rfl

variable {W S}

/-! ## What holds outside the events -/

/-- Outside E_M, E_F and the seed's event: a seed that the verifier has recomputed at a root is no
collision seed of the word that the trace determines under that root. -/
theorem seed_not_coll {tr : Tc W} (hM : ¬ EM tr) (hF : ¬ EF tr)
    (hS : ¬ StepEvent (stepSeed W S) tr) {cm : Dig lam} {s : L.OutOfDomainSeed}
    (h : RunsIn tr (outOfDomainSeedIs W S cm s) true) : ¬ L.hasCollisionAt (extEnc W tr cm) s := by
  obtain ⟨a0, a1, h0, h1, rfl⟩ := runsIn_seedIs h
  intro hc
  obtain ⟨pre, post, htr, hnew⟩ := List.eq_append_cons_of_mem h1
  have hne : fbE S.t (seedQ0 W S cm) a0 ≠ fbE S.t (seedQ1 W S (link a0)) a1 := fun e => by
    have h2 := congrArg (fun z : FbIn lam (typedOracleCarrier L Bd aT aL) S.t => z.round) (fbE_inj e).1
    simp [seedQ0, seedQ1] at h2
  have h0' : fbE S.t (seedQ0 W S cm) a0 ∈ pre :=
    mem_of_link_occurs hF htr h0 (evF_answer_fbE _ _ _)
      (evF_occurs_chain a1 (by simp [chainFields, seedQ1])) hne
  have hsub : pre ⊆ tr := fun e he => by rw [htr]; exact List.mem_append_left _ he
  have hp : predF S.t pre 1 (link a0) = some (seedQ0 W S cm, a0) := predF_eq hF hsub h0'
  refine hS ⟨pre, _, post, htr, hnew, link a0, a1, cm, a0, rfl, hp, ?_⟩
  rw [extEnc_before htr hM ⟨fbE S.t (seedQ0 W S cm) a0, List.mem_append_left _ h0',
    evM_occurs_cms (q := seedQ0 W S cm) a0 (cms := cm :: S.cfg) (x := none) (sl := S.shape) rfl
      (by simp)⟩]
  exact hc

/-- The same where the seed's event stands beside the lanes' in one event. -/
theorem seed_not_coll' {ℓT ℓL ℓB : Lane W} {tr : Tc W} (hM : ¬ EM tr) (hF : ¬ EF tr)
    (hS : ¬ StepEvent (fun pre e => stepS W ℓT ℓL ℓB pre e ∨ stepSeed W S pre e) tr)
    {cm : Dig lam} {s : L.OutOfDomainSeed} (h : RunsIn tr (outOfDomainSeedIs W S cm s) true) :
    ¬ L.hasCollisionAt (extEnc W tr cm) s :=
  seed_not_coll hM hF (fun ⟨pre, e, post, h1, h2⟩ => hS ⟨pre, e, post, h1, Or.inr h2⟩) h

/-- Outside E_M the word under a root is fixed once the first query of the root's seed is asked. -/
theorem seed_fixes {tr tr' : Tc W} (hM : ¬ EM (tr ++ tr')) {cm : Dig lam} {a0 : FsAns lam W.K}
    (h : fbE S.t (seedQ0 W S cm) a0 ∈ tr) : extEnc W tr cm = extEnc W (tr ++ tr') cm :=
  extEnc_stable hM (List.prefix_append _ _)
    ⟨fbE S.t (seedQ0 W S cm) a0, h,
      evM_occurs_cms (q := seedQ0 W S cm) a0 (cms := cm :: S.cfg) (x := none) (sl := S.shape) rfl
        (by simp)⟩

end TypedOracleCompiler.Compile.Batch.Cms
