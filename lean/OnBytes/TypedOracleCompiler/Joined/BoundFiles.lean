-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/BoundFiles.lean: several compiled verifiers against one set of oracles and one
adversary: one bad event, paid once, outside which each verifier's yes means "in its language".

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

Why. A verification reads several files. Each file is one batch protocol under a tag of its own.
OnBytes/TypedOracleCompiler/Joined/Bound.lean has soundness of one compiled verifier with its event under "there
is"; adding such statements up would pay the hash term once for each file.
Here the event of each file is kept as a lane, and the lanes are put into one event
(`BadL`, OnBytes/TypedOracleCompiler/Joined/Lanes.lean).

Main names:
  `LaneFor W t N V okC Lg extY εs ℓ`: the lane ℓ serves the verifier V: it has the tag t, is well
    formed, has round errors at most εs, and outside the two hash events and its state event a yes
    of V means "in the language";
  `laneFor_of_snd`: a written protocol with (Snd-B) has such a lane (the hypotheses of
    `soundLane` without hN);
  `LaneFor.mem`: the same outside the bad event of a list that holds the lane;
  `LaneFor.of_yes`: a verifier that says yes only where V does is served by the same lane;
  `SoundLane`: "V has a lane", with the lane and the number of slots under "there is";
    `SoundLane.soundAt`: it gives `SoundAt`;
  `badL_rare_of_tags`: lanes with different tags: n εs + 2 (n + 1)² / 2^lam for all together;
  `Sound3`, `sound3`: three verifiers under three different tags, as one proposition.

Limits: as in OnBytes/TypedOracleCompiler/Joined/Bound.lean. One wire record W of the oracles; the depth of the
request tree, and so the number of slots, goes by the tag (`QueryLayout.dReq`,
OnBytes/TypedOracleCompiler/Compile/Batch/Oracles.lean): files under different tags may differ in it. The three
predicates on the outer roots are free letters: whoever states a theorem pins them, as in `SoundAt`.
The error εs is free too: where n εs + 2 (n + 1)² / 2^lam is 1 or more the bound on the event says
nothing, and at εs of 1 or more `Sound3` and `SoundAt` hold of every verifier that asks a query
before it says yes, whatever the languages are (take "the trace is not empty" as the event). This is
by reading: no theorem states it.
There are three tags, and `sound3` uses all: a further kind of query under one of these tags (a
record's seed) must be seen to cause no lane's state event, or be paid for. Two files under one tag
pay the sum of their bounds (`badL_rare`, OnBytes/TypedOracleCompiler/Joined/Lanes.lean): not said here.
No other file of the library uses `sound3` yet.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.Bound
import OnBytes.TypedOracleCompiler.Joined.Lanes

noncomputable section

namespace TypedOracleCompiler.Joined
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L}

/-- The lane ℓ serves the verifier V. -/
structure LaneFor (W : QueryLayout lam L) (t : Tag) (N : ℕ) {Y P : Type} {E : ExtSpec}
    (V : List (Dig lam) → Y → P → TypedOracleComputation lam W.K L Bool) (okC : List (Dig lam) → Prop)
    (Lg : Y → E.Str → Prop) (extY : Tc W → List (Dig lam) → E.Str) (εs : ℝ≥0∞) (ℓ : Lane W) :
    Prop where
  /-- its queries have the tag t -/
  tag : ℓ.t = t
  /-- it is well formed -/
  ok : ℓ.OK N
  /-- its round errors, as probabilities, are at most εs -/
  below : Err.Below ℓ.ε εs
  /-- outside the two hash events and the lane's state event, a yes means "in the language" -/
  yes : ∀ (tr : Tc W) cms x π, okC cms → ¬ EM tr → ¬ EF tr → ¬ StepEvent ℓ.step tr →
    RunsIn tr (V cms x π) true → Lg x (extY tr cms)

/-- A written protocol with (Snd-B) has a lane that serves its compiled verifier (without the
strict-format check): under the hypotheses of `soundLane` without hN. -/
theorem laneFor_of_snd {Y : Type} {E : ExtSpec} {early : Y → Y} (Z : Written W Y E)
    (R : ReadBack Z early) {N : ℕ} {Lg : Y → E.Str → Prop} {ε : Err Z.Q.loc.shape} {εs : ℝ≥0∞}
    (hsnd : Z.Q.SndBL N early L.late Lg ε) (hε : Err.Below ε εs) (hOK : Z.wq.OKG)
    (hloc : Z.Q.loc.IsLocal) (hco : Z.Q.ann.Coherent) (okC : List (Dig lam) → Prop)
    (extY : Tc W → List (Dig lam) → E.Str)
    (hext : ∀ (tr : Tc W) cms x (π : OneProtocolProof lam Z.Q), okC cms → ¬ EM tr →
      ExtReads (⟨tr, Z.t, cms, Z.xin x, π.salt, π.rtreq, π.slot⟩ : Ctx W) Z.wq.ext Z.embE extY) :
    ∃ ℓ : Lane W, LaneFor W Z.t N Z.verifyLax okC Lg extY εs ℓ := by
  obtain ⟨h0, State, h1, h2, hs, h3, h4⟩ := hsnd
  exact ⟨laneJ Z R ε State extY, rfl, laneOf_ok hOK.sh h4, hε,
    fun tr cms x π hC hM hF hS hrun =>
      mem_of_snd Z R hOK hloc hco ε State h0 h1 h2 hs h3 extY hM hF hS cms x π hrun
        (hext tr cms x π hC hM)⟩

/-- A verifier that says yes only where V does is served by the same lane. -/
theorem LaneFor.of_yes {t : Tag} {N : ℕ} {Y P P' : Type} {E : ExtSpec}
    {V : List (Dig lam) → Y → P → TypedOracleComputation lam W.K L Bool}
    {V' : List (Dig lam) → Y → P' → TypedOracleComputation lam W.K L Bool} {okC : List (Dig lam) → Prop}
    {Lg : Y → E.Str → Prop} {extY : Tc W → List (Dig lam) → E.Str} {εs : ℝ≥0∞} {ℓ : Lane W}
    (h : LaneFor W t N V okC Lg extY εs ℓ)
    (hV : ∀ (tr : Tc W) cms x π', RunsIn tr (V' cms x π') true → ∃ π, RunsIn tr (V cms x π) true) :
    LaneFor W t N V' okC Lg extY εs ℓ :=
  ⟨h.tag, h.ok, h.below, fun tr cms x π' hC hM hF hS hrun => by
    obtain ⟨π, hπ⟩ := hV tr cms x π' hrun
    exact h.yes tr cms x π hC hM hF hS hπ⟩

/-- Outside the bad event of a list that holds the lane, a yes means "in the language". -/
theorem LaneFor.mem {t : Tag} {N : ℕ} {Y P : Type} {E : ExtSpec}
    {V : List (Dig lam) → Y → P → TypedOracleComputation lam W.K L Bool} {okC : List (Dig lam) → Prop}
    {Lg : Y → E.Str → Prop} {extY : Tc W → List (Dig lam) → E.Str} {εs : ℝ≥0∞} {ℓ : Lane W}
    (h : LaneFor W t N V okC Lg extY εs ℓ) {ℓs : List (Lane W)} (hm : ℓ ∈ ℓs) {tr : Tc W}
    (hB : ¬ BadL ℓs tr) {cms : List (Dig lam)} {x : Y} {π : P} (hC : okC cms)
    (hrun : RunsIn tr (V cms x π) true) : Lg x (extY tr cms) := by
  obtain ⟨hM, hF, hS, -⟩ := not_badL hB
  exact h.yes tr cms x π hC hM hF (hS ℓ hm) hrun

/-- Lanes with different tags, each well formed, with as many slots as its tag's request tree has
leaves, and with round errors at most εs: an algorithm with
at most n queries causes their bad event with probability at most n εs + 2 (n + 1)² / 2^lam. -/
theorem badL_rare_of_tags {ℓs : List (Lane W)} (htag : ℓs.Pairwise fun a b => a.t ≠ b.t)
    (ok : ∀ ℓ ∈ ℓs, ℓ.OK (2 ^ W.dReq ℓ.t)) {εs : ℝ≥0∞}
    (b : ∀ ℓ ∈ ℓs, Err.Below ℓ.ε εs) (β : Type) (A : TypedOracleComputation lam W.K L β) (n : ℕ)
    (hA : A.QueryBound n) :
    pr A.withTrace.law {o | BadL ℓs o.2} ≤
      (n : ℝ≥0∞) * εs + 2 * ((n + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam :=
  badL_rare ok (fun _ => εs) b
    (fun t₀ => (payAt_le_of_pairwise (fun _ => εs) t₀ ℓs htag fun _ _ => le_rfl).1) β A n hA

/-- **A compiled verifier V has a lane**: the form in which a statement on several verifiers takes
one of them: the lane is kept, so that all lanes can be put into one event and the event be paid
once. -/
def SoundLane (W : QueryLayout lam L) (t : Tag) {Y P : Type} {E : ExtSpec}
    (V : List (Dig lam) → Y → P → TypedOracleComputation lam W.K L Bool) (okC : List (Dig lam) → Prop)
    (Lg : Y → E.Str → Prop) (extY : Tc W → List (Dig lam) → E.Str) (εs : ℝ≥0∞) : Prop :=
  ∃ (ℓ : Lane W) (N : ℕ), N = 2 ^ W.dReq t ∧ LaneFor W t N V okC Lg extY εs ℓ

/-- A verifier with a lane is sound by itself. -/
theorem SoundLane.soundAt {t : Tag} {Y P : Type} {E : ExtSpec}
    {V : List (Dig lam) → Y → P → TypedOracleComputation lam W.K L Bool} {okC : List (Dig lam) → Prop}
    {Lg : Y → E.Str → Prop} {extY : Tc W → List (Dig lam) → E.Str} {εs : ℝ≥0∞}
    (h : SoundLane W t V okC Lg extY εs) : SoundAt W V okC Lg extY εs := by
  obtain ⟨ℓ, N, hN, hl⟩ := h
  exact ⟨BadJ ℓ, fun β A n hA => badJ_rare ℓ (hl.tag ▸ hN) hl.ok hl.below A n hA, badJ_mono ℓ,
    fun tr cms x π hC hB hrun => hl.yes tr cms x π hC (fun e => hB (Or.inl (Or.inl e)))
      (fun e => hB (Or.inl (Or.inr e))) (fun e => hB (Or.inr e)) hrun⟩

section Three
variable {Y₁ Y₂ Y₃ P₁ P₂ P₃ : Type} {E₁ E₂ E₃ : ExtSpec}

/-- **Three compiled verifiers are sound together**, as one proposition: one event on traces that is
rare for every algorithm with at most n queries, is never undone, and outside which a yes of each
verifier means that its statement, with its external strings read off the trace, is in its
language. -/
def Sound3 (W : QueryLayout lam L) (V₁ : List (Dig lam) → Y₁ → P₁ → TypedOracleComputation lam W.K L Bool)
    (V₂ : List (Dig lam) → Y₂ → P₂ → TypedOracleComputation lam W.K L Bool)
    (V₃ : List (Dig lam) → Y₃ → P₃ → TypedOracleComputation lam W.K L Bool) (ok₁ ok₂ ok₃ : List (Dig lam) → Prop)
    (Lg₁ : Y₁ → E₁.Str → Prop) (Lg₂ : Y₂ → E₂.Str → Prop) (Lg₃ : Y₃ → E₃.Str → Prop)
    (ext₁ : Tc W → List (Dig lam) → E₁.Str) (ext₂ : Tc W → List (Dig lam) → E₂.Str)
    (ext₃ : Tc W → List (Dig lam) → E₃.Str) (εs : ℝ≥0∞) : Prop :=
  ∃ Bad : Tc W → Prop,
    (∀ (β : Type) (A : TypedOracleComputation lam W.K L β) (n : ℕ), A.QueryBound n →
      pr A.withTrace.law {o | Bad o.2} ≤ _root_.Compile.Joined.bound n εs lam) ∧
    (∀ tr tr', Bad tr → Bad (tr ++ tr')) ∧
    (∀ tr cms x π, ok₁ cms → ¬ Bad tr → RunsIn tr (V₁ cms x π) true → Lg₁ x (ext₁ tr cms)) ∧
    (∀ tr cms x π, ok₂ cms → ¬ Bad tr → RunsIn tr (V₂ cms x π) true → Lg₂ x (ext₂ tr cms)) ∧
    ∀ tr cms x π, ok₃ cms → ¬ Bad tr → RunsIn tr (V₃ cms x π) true → Lg₃ x (ext₃ tr cms)

/-- From a lane for each, under three different tags, each with as many slots as its tag's request
tree has leaves. The hash term is paid once, and εs once for each query: a query belongs to one
tag. -/
theorem sound3 {t₁ t₂ t₃ : Tag} (h12 : t₁ ≠ t₂) (h13 : t₁ ≠ t₃) (h23 : t₂ ≠ t₃) {N₁ N₂ N₃ : ℕ}
    (hN₁ : N₁ = 2 ^ W.dReq t₁) (hN₂ : N₂ = 2 ^ W.dReq t₂) (hN₃ : N₃ = 2 ^ W.dReq t₃)
    {V₁ : List (Dig lam) → Y₁ → P₁ → TypedOracleComputation lam W.K L Bool}
    {V₂ : List (Dig lam) → Y₂ → P₂ → TypedOracleComputation lam W.K L Bool}
    {V₃ : List (Dig lam) → Y₃ → P₃ → TypedOracleComputation lam W.K L Bool} {ok₁ ok₂ ok₃ : List (Dig lam) → Prop}
    {Lg₁ : Y₁ → E₁.Str → Prop} {Lg₂ : Y₂ → E₂.Str → Prop} {Lg₃ : Y₃ → E₃.Str → Prop}
    {ext₁ : Tc W → List (Dig lam) → E₁.Str} {ext₂ : Tc W → List (Dig lam) → E₂.Str}
    {ext₃ : Tc W → List (Dig lam) → E₃.Str} {εs : ℝ≥0∞}
    (l₁ : ∃ ℓ, LaneFor W t₁ N₁ V₁ ok₁ Lg₁ ext₁ εs ℓ)
    (l₂ : ∃ ℓ, LaneFor W t₂ N₂ V₂ ok₂ Lg₂ ext₂ εs ℓ)
    (l₃ : ∃ ℓ, LaneFor W t₃ N₃ V₃ ok₃ Lg₃ ext₃ εs ℓ) :
    Sound3 W V₁ V₂ V₃ ok₁ ok₂ ok₃ Lg₁ Lg₂ Lg₃ ext₁ ext₂ ext₃ εs := by
  obtain ⟨a, ha⟩ := l₁
  obtain ⟨b, hb⟩ := l₂
  obtain ⟨c, hc⟩ := l₃
  have hall : ∀ ℓ ∈ [a, b, c], ℓ.OK (2 ^ W.dReq ℓ.t) ∧ Err.Below ℓ.ε εs := by
    intro ℓ hℓ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓ
    rcases hℓ with rfl | rfl | rfl
    · exact ⟨by rw [ha.tag, ← hN₁]; exact ha.ok, ha.below⟩
    · exact ⟨by rw [hb.tag, ← hN₂]; exact hb.ok, hb.below⟩
    · exact ⟨by rw [hc.tag, ← hN₃]; exact hc.ok, hc.below⟩
  have htag : [a, b, c].Pairwise fun x y => x.t ≠ y.t := by
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_true]
    exact ⟨⟨by rw [ha.tag, hb.tag]; exact h12, by rw [ha.tag, hc.tag]; exact h13⟩,
      by rw [hb.tag, hc.tag]; exact h23⟩
  refine ⟨BadL [a, b, c],
    badL_rare_of_tags htag (fun ℓ h => (hall ℓ h).1) fun ℓ h => (hall ℓ h).2,
    fun tr tr' => badL_mono tr tr', fun tr cms x π hC hB hr => ha.mem (by simp) hB hC hr,
    fun tr cms x π hC hB hr => hb.mem (by simp) hB hC hr,
    fun tr cms x π hC hB hr => hc.mem (by simp) hB hC hr⟩

end Three

end TypedOracleCompiler.Joined
