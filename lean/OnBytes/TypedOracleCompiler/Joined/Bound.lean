-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/Bound.lean: soundness of the compiled verifier of ONE batch protocol, from the
protocol's round-by-round soundness: the bad event, its probability, and "accepted outside the bad
event means: in the language".

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

Why. A file with three hash chains is typed as one batch protocol: the first chain's rounds are
local rounds, the first seal is the joining round's slot value, the second chain's rounds are shared
rounds, a seam holds both seals, and the third chain's rounds are local rounds again. The lemma on
one protocol of OnBytes/TypedOracleCompiler/Compile/Batch/SoundOurs.lean (`mem_of_accepted_ours`) is general in the
protocol, so the way through the joins is that lemma. This file puts it into the form that a top
statement calls: its hypotheses are (Snd-B) in the library's own form (`BatchInteractiveOracleProof.SndBL`,
Iop/Batch.lean), the laws of the wiring, and two named records.

Main names:
  `instAt early late x i`: the instance that a chain has taken in with the query of round i;
  `ExtReads C we embE extY`: what is asked of the reading `extY` of the external strings off a
    trace: it does not move at the queries of the accepted proof's own chain (`stable`), and a leaf
    that the trace determines under an outer root gives the symbol read (`agrees`);
  `ReadBack Z early`: how what a written protocol lays into the queries is read back;
  `laneJ`, `BadJ`: the protocol as a lane of the analysis; the bad event: a hash event (`EM`, `EF`)
    or the lane's state event;
  `badJ_rare`: an algorithm with at most t queries causes it with probability at most
    t εs + 2 (t + 1)² / 2^lam; `badJ_mono`: it is never undone;
  `mem_of_snd`: outside the three events an accepted proof string has its statement in the language;
  `SoundAt`, `soundLane`: the three together, with the event under "there is".

The bound is not a sum over the chains. εs bounds every round's error of the joined list of rounds;
the slot value and the seals cost no term of their own: that a link value names its query is the
hash event `EF`, and that a root names its leaves is `EM`; both are paid in 2 (t + 1)² / 2^lam.

Limits: nothing here says that (Snd-B) holds of any protocol, that any wiring is lawful, or that
any reading has `ExtReads`: these are hypotheses. `ExtReads` can be met by a reading of strings
under outer roots (`ExtReads.of_occurs`); of a value that is read off another chain's queries its
clause `stable` holds only if those queries stand before the accepted string's own first query.
Nothing on the honest prover. One protocol under one tag: several protocols in one world are another
file's matter. The probability in `badJ_rare` and `SoundAt` is over the family of typed oracles
(`typedOracleFamily lam W.K L`), lazily drawn: nothing here carries it to one hash function. The verifier is
`verifyLax`: without the strict-format check. The errors ε are (Snd-B)'s for a vector of N instances
at once (`JointLaw`, Iop/Batch.lean), N the number of leaves of the tag's request tree: whoever
brings (Snd-B) pays the factor for slots inside ε.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.SoundOurs
import OnBytes.TypedOracleCompiler.Joined.Wire
import Compile.Joined.Worst

noncomputable section

namespace TypedOracleCompiler.Joined
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L}

/-! ## The instance that a chain has taken in -/

/-- the instance that the chain of a slot with the instance x has taken in with the query of round
i: `early x` up to the round `late`, x from there on -/
def instAt {Y : Type} (early : Y → Y) (late : Option ℕ) (x : Y) (i : ℕ) : Y :=
  match late with
  | some n => if n ≤ i then x else early x
  | none => early x

section InstAt
variable {Y : Type} {early : Y → Y} {late : Option ℕ} {s : Shape} {A : RoundSplits s}
  (h0 : ∀ n, late = some n → 0 < n ∧ RoundSplits.LocalTo n s A)
include h0

theorem instAt_zero {x : Y} : instAt early late x 0 = early x := by
  unfold instAt
  cases hl : late with
  | none => rfl
  | some n => simp [Nat.pos_iff_ne_zero.1 (h0 n hl).1]

/-- Under h0: from round j - 1 to round j the instance stays, or j is the round `late`. -/
theorem instAt_step (x : Y) (j : ℕ) :
    instAt early late x (j - 1) = instAt early late x j ∨
    (late = some j ∧ instAt early late x (j - 1) = early x ∧ instAt early late x j = x) := by
  unfold instAt
  cases hl : late with
  | none => exact Or.inl rfl
  | some n =>
    have hn := (h0 n hl).1
    by_cases h1 : n ≤ j - 1
    · exact Or.inl (by simp [h1, show n ≤ j by omega])
    · by_cases h2 : n ≤ j
      · obtain rfl : n = j := by omega
        exact Or.inr ⟨rfl, by simp [h1], by simp⟩
      · exact Or.inl (by simp [h1, h2])

theorem instAt_last {x : Y} :
    instAt early late x (s.length - 1) = if late.isSome then x else early x := by
  unfold instAt
  cases hl : late with
  | none => rfl
  | some n =>
    have := (h0 n hl).2.lt_length
    simp [show n ≤ s.length - 1 by omega]

end InstAt

/-! ## The two named records -/

/-- What is asked of a reading `extY` of the external strings off a trace, for the accepted proof
with the fixed data C. To discharge it for a string under an outer root: `stable` by "what a trace
determines under a root that has occurred does not change outside `EM`", `agrees` by the definition
of the reading. -/
structure ExtReads (C : Ctx W) {E : ExtSpec} (we : WireE E) (embE : E.Sym → Body L)
    (extY : Tc W → List (Dig lam) → E.Str) : Prop where
  /-- the reading is the same before each query of the proof's own chain and at the end -/
  stable : ∀ pre (q : FbIn lam L C.t) (a : FsAns lam W.K) post l cur,
    C.tr = pre ++ fbE C.t q a :: post → Ours C pre q l cur → extY pre C.cms = extY C.tr C.cms
  /-- a leaf that the trace determines under its outer root holds the symbol that is read -/
  agrees : ∀ p a sl,
    extLeaf C.tr we.depth (C.cms.getD (we.which p) default) (we.leaf p) = some ⟨embE a, sl⟩ →
    E.rd (extY C.tr C.cms) p = a

/-- It is enough that the reading is stable at every Fiat-Shamir query of the tag behind which the
first two outer roots have occurred. -/
theorem ExtReads.of_occurs (C : Ctx W) {E : ExtSpec} {we : WireE E} {embE : E.Sym → Body L}
    {extY : Tc W → List (Dig lam) → E.Str}
    (hstab : ∀ pre (q : FbIn lam L C.t) (a : FsAns lam W.K) post,
      C.tr = pre ++ fbE C.t q a :: post →
      (∀ c ∈ C.cms.take 2, (evM lam W.K L).OccursIn (pre ++ [fbE C.t q a]) c) →
      extY pre C.cms = extY C.tr C.cms)
    (hagree : ∀ p a sl,
      extLeaf C.tr we.depth (C.cms.getD (we.which p) default) (we.leaf p) = some ⟨embE a, sl⟩ →
      E.rd (extY C.tr C.cms) p = a) : ExtReads C we embE extY :=
  ⟨fun pre q a post _ _ htr hours => hstab pre q a post htr (ours_cms C a hours), hagree⟩

/-- How what a written protocol (`Written`, OnBytes/TypedOracleCompiler/Joined/Wire.lean) lays into the queries is
read back: a leaf's body as an oracle symbol, a query's plain part as the protocol's, a query's
instance as the protocol's. To discharge the laws: the three maps of Z are one-to-one, and these are
their inverses. -/
structure ReadBack {Y : Type} {E : ExtSpec} (Z : Written W Y E) (early : Y → Y) where
  prjS : (p : OPos Z.Q.loc.shape) → Body L → Option (OSym Z.Q.loc.shape p)
  prjP : PlainPart (shapeOf L Z.t) (annOf L Z.t) → Option (PlainPart Z.Q.loc.shape Z.Q.ann)
  xout : Option X → Option Y
  /-- a symbol that was written is read back -/
  prjS_emb : ∀ p a, prjS p (Z.embS p a) = some a
  /-- a plain part that was written is read back -/
  prjP_emb : ∀ z, prjP (Z.embP z) = some z
  /-- what a chain's queries hold of an instance up to round i is read back as `instAt`: so it
  determines `early x`, and x itself from the round `L.late` on, if there is such a round -/
  xout_in : ∀ x i, xout (instX L (Z.xin x) i) = some (instAt early L.late x i)

/-! ## The lane and the bad event -/

section Lane
variable {Y : Type} {E : ExtSpec} {early : Y → Y}

/-- the protocol as a lane of the analysis -/
def laneJ (Z : Written W Y E) (R : ReadBack Z early) (ε : Err Z.Q.loc.shape)
    (State : E.Str → Y → PTr Z.Q.loc.shape → Bool) (extY : Tc W → List (Dig lam) → E.Str) :
    Lane W :=
  laneOf W Z.t Z.Q Z.wq.sh R.prjS R.prjP ε State R.xout extY

/-- the bad event of one lane: a hash event, or the lane's state event -/
def BadJ (ℓ : Lane W) (tr : Tc W) : Prop := (EM tr ∨ EF tr) ∨ StepEvent ℓ.step tr

/-- The bad event is never undone. -/
theorem badJ_mono (ℓ : Lane W) (tr tr' : Tc W) (h : BadJ ℓ tr) : BadJ ℓ (tr ++ tr') := by
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl (h.append tr'))
  · exact Or.inl (Or.inr (h.append tr'))
  · exact Or.inr (StepEvent.append h tr')

/-- Given the entries before it, a query causes the lane's state event with probability at most εs,
at whichever oracle it stands. -/
theorem pr_laneStep_le (ℓ : Lane W) {N : ℕ} (hN : N = 2 ^ W.dReq ℓ.t) (hOK : ℓ.OK N) {εs : ℝ≥0∞}
    (hε : Err.Below ℓ.ε εs) (pre : Tc W) (o : Compile.Batch.OracleName) (q : domOf lam L o) :
    pr (unif ((typedOracleFamily lam W.K L).Rng o)) {r | ℓ.step pre (⟨o, q, r⟩ : QA (typedOracleFamily lam W.K L))} ≤ εs := by
  by_cases ho : o = Compile.Batch.OracleName.fb ℓ.t
  · subst ho
    exact Lane.pr_step_le ℓ hN hOK hε pre q
  · refine le_trans (le_of_eq (pr_eq_zero_of_forall_not_mem _ ?_)) (zero_le _)
    rintro r - h
    exact ho (Lane.step_oracle h)

/-- An algorithm with at most t queries causes the bad event with probability at most
t εs + 2 (t + 1)² / 2^lam. -/
theorem badJ_rare (ℓ : Lane W) {N : ℕ} (hN : N = 2 ^ W.dReq ℓ.t) (hOK : ℓ.OK N) {εs : ℝ≥0∞}
    (hε : Err.Below ℓ.ε εs) {β : Type} (A : TypedOracleComputation lam W.K L β) (n : ℕ) (hA : A.QueryBound n) :
    pr A.withTrace.law {o | BadJ ℓ o.2} ≤
      (n : ℝ≥0∞) * εs + 2 * ((n + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  have h := pr_stepEvent_le (S := typedOracleFamily lam W.K L) ℓ.step (fun _ => εs)
    (fun pre e he hs => hs.1 he) (fun pre o q _ => pr_laneStep_le ℓ hN hOK hε pre o q) A n hA
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  calc
    pr A.withTrace.law {o | (EM o.2 ∨ EF o.2) ∨ StepEvent ℓ.step o.2} ≤
        pr A.withTrace.law {o | EM o.2 ∨ EF o.2} +
          pr A.withTrace.law {o | StepEvent ℓ.step o.2} := pr_union_le _ _ _
    _ ≤ 2 * (n : ℝ≥0∞) ^ 2 / 2 ^ lam + (n : ℝ≥0∞) * εs := add_le_add (hashEvents A n hA) h
    _ ≤ (n : ℝ≥0∞) * εs + 2 * ((n + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
        rw [add_comm]
        gcongr
        exact Nat.le_succ n

/-! ## Accepted, outside the events: in the language -/

/-- One protocol, from the clauses of (Snd-B) in the late form for a state function `State`: outside
`EM`, `EF` and the lane's state event, if the compiled verifier of a slot accepts and all its
queries are in the trace, then the statement of x and the external strings read off the trace is in
the language. h0, h1, h2, hs, h3 are the clauses of `BatchInteractiveOracleProof.SndBL` (Iop/Batch.lean) but for the
law on verifier messages. -/
theorem mem_of_snd (Z : Written W Y E) (R : ReadBack Z early) (hOK : Z.wq.OKG)
    (hloc : Z.Q.loc.IsLocal) (hco : Z.Q.ann.Coherent) {Lg : Y → E.Str → Prop}
    (ε : Err Z.Q.loc.shape) (State : E.Str → Y → PTr Z.Q.loc.shape → Bool)
    (h0 : ∀ n, L.late = some n → 0 < n ∧ RoundSplits.LocalTo n Z.Q.loc.shape Z.Q.ann)
    (h1 : ∀ y x, ¬ Lg x y → State y (early x) (PTr.empty Z.Q.loc.shape) = false)
    (h2 : ∀ y x (τ : AtP Z.Q.loc.shape) (m : τ.round.Msg),
      State y x (.atP τ) = false → State y x (.atV (τ.snoc m)) = false)
    (hs : ∀ y x (τ : AtP Z.Q.loc.shape), ¬ Lg x y → L.late = some τ.idx →
      State y (early x) (.atP τ) = false → State y x (.atP τ) = false)
    (h3 : ∀ y x (τ : Tr Z.Q.loc.shape), ¬ Lg x y →
      State y (if L.late.isSome then x else early x) (.full τ) = false →
      Z.Q.loc.accept x y τ = false)
    (extY : Tc W → List (Dig lam) → E.Str) {tr : Tc W} (hM : ¬ EM tr) (hF : ¬ EF tr)
    (hS : ¬ StepEvent (laneJ Z R ε State extY).step tr) (cms : List (Dig lam)) (x : Y)
    (π : OneProtocolProof lam Z.Q) (hrun : RunsIn tr (Z.verifyLax cms x π) true)
    (hext : ExtReads (⟨tr, Z.t, cms, Z.xin x, π.salt, π.rtreq, π.slot⟩ : Ctx W) Z.wq.ext Z.embE
      extY) :
    Lg x (extY tr cms) :=
  mem_of_accepted_ours Z.t Z.Q Z.wq Z.embS Z.embP Z.xin Z.embE hOK hloc hco (Lg := Lg) State
    R.prjS R.prjS_emb R.prjP R.prjP_emb R.xout extY ε hM hF hS cms x π
    (instAt early L.late x) (R.xout_in x) (fun n hn _ => h0 n hn)
    (fun y hL => by rw [instAt_zero h0]; exact h1 y x hL)
    (fun y τ m hL h => by
      rcases instAt_step (early := early) h0 x τ.idx with e | ⟨e1, e2, e3⟩
      · rw [e] at h; exact h2 y _ τ m h
      · rw [e2] at h; rw [e3]; exact h2 y x τ m (hs y x τ hL e1 h))
    (fun y τ hL h => h3 y x τ hL (by rw [← instAt_last (early := early) h0]; exact h))
    hrun hext.stable hext.agrees

/-- **A compiled verifier V is sound**, as one proposition: there is an event on traces that is rare
for every algorithm with at most n queries (`bound`, Compile/Joined/Worst.lean: n εs + 2 (n + 1)² /
2^lam), is never undone, and outside which every accepted proof
string has its statement, with the external strings read off the trace, in the language. `okC` says
with which lists of outer roots the verifier is called (how many there are): a reading of the
external strings can be stable only under roots that stand in the first query. At an `okC` that
holds of no list the third clause is empty: whoever states a theorem with `SoundAt` pins `okC` to
the lists with which the verifier that runs is called.
At εs of 1 or more `SoundAt` holds of every verifier that asks a query before it says yes (take "the
trace is not empty" as the event), and where 2^lam is at most 2 of every verifier (take every
trace): there the proposition says nothing. This is by reading: no theorem states it. -/
def SoundAt (W : QueryLayout lam L) {P : Type} (V : List (Dig lam) → Y → P → TypedOracleComputation lam W.K L Bool)
    (okC : List (Dig lam) → Prop) (Lg : Y → E.Str → Prop)
    (extY : Tc W → List (Dig lam) → E.Str) (εs : ℝ≥0∞) : Prop :=
  ∃ Bad : Tc W → Prop,
    (∀ (β : Type) (A : TypedOracleComputation lam W.K L β) (n : ℕ), A.QueryBound n →
      pr A.withTrace.law {o | Bad o.2} ≤ _root_.Compile.Joined.bound n εs lam) ∧
    (∀ tr tr', Bad tr → Bad (tr ++ tr')) ∧
    ∀ tr cms x π, okC cms → ¬ Bad tr → RunsIn tr (V cms x π) true → Lg x (extY tr cms)

/-- The compiled verifier of one written protocol, without the strict-format check, is sound: from
(Snd-B) of the protocol, with every round's error at most εs; a lawful wiring; a local verifier; a
coherent annotation; as many slots as the tag's request tree has leaves; the read-back; a reading of
the external strings that has `ExtReads` outside the hash event `EM`, at the lists of outer roots
with `okC`. -/
theorem soundLane (Z : Written W Y E) (R : ReadBack Z early) {N : ℕ} {Lg : Y → E.Str → Prop}
    {ε : Err Z.Q.loc.shape} {εs : ℝ≥0∞} (hsnd : Z.Q.SndBL N early L.late Lg ε)
    (hε : Err.Below ε εs) (hN : N = 2 ^ W.dReq Z.t) (hOK : Z.wq.OKG) (hloc : Z.Q.loc.IsLocal)
    (hco : Z.Q.ann.Coherent) (okC : List (Dig lam) → Prop) (extY : Tc W → List (Dig lam) → E.Str)
    (hext : ∀ (tr : Tc W) cms x (π : OneProtocolProof lam Z.Q), okC cms → ¬ EM tr →
      ExtReads (⟨tr, Z.t, cms, Z.xin x, π.salt, π.rtreq, π.slot⟩ : Ctx W) Z.wq.ext Z.embE extY) :
    SoundAt W Z.verifyLax okC Lg extY εs := by
  obtain ⟨h0, State, h1, h2, hs, h3, h4⟩ := hsnd
  have hl : (laneJ Z R ε State extY).OK N := laneOf_ok hOK.sh h4
  refine ⟨BadJ (laneJ Z R ε State extY), fun β A n hA => badJ_rare _ hN hl hε A n hA,
    badJ_mono _, fun tr cms x π hC hB hrun => ?_⟩
  have hM : ¬ EM tr := fun h => hB (Or.inl (Or.inl h))
  exact mem_of_snd Z R hOK hloc hco ε State h0 h1 h2 hs h3 extY hM
    (fun h => hB (Or.inl (Or.inr h))) (fun h => hB (Or.inr h)) cms x π hrun
    (hext tr cms x π hC hM)

end Lane

end TypedOracleCompiler.Joined
