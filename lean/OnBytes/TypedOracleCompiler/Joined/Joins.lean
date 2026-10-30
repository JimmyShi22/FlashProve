-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/Joins.lean: what stands between the three chains of a file, as the compiled
verifier asks for it.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

OnBytes/TypedOracleCompiler/Joined/Verifier.lean recomputes the three chains of a file one after the other and hands
the phase from one to the next. Here is what these phases are where the chains run in a trace, and
which queries the verifier makes at the two joins.

  The first chain ends in `.loc ρ₁`: ρ₁ is its last chaining value.
  The second chain begins with the joining round. The verifier asks g at ρ₁; the answer c is the
    slot value, the first seal. Then it asks the Fiat-Shamir oracle in format (F4), which holds the
    request root of the argument string. The chain ends in `.shr ρ₀ c`: ρ₀, its last chaining
    value, is the second seal.
  The third chain begins with a query in format (F3), which holds ρ₀ and c. It ends in `.aft ρ c`,
    with the same c: so the check in the request tree is made at the first seal.

Main names:
  `loc_of_allLo`, `shr_of_allSh`, `aft_of_allLo`: local rounds keep a chain before the joining
    round, shared rounds keep it shared, later local rounds keep it behind; the slot value stays.
  `qFirst₁`, `qSeal₁`, `qFirst₂`, `qFirst₃`: the first query of each chain, and the query to g.
  `run₁_ends`, `run₂_joins`, `run₃_joins`: the three chains of a file.
  `joins_of_yes`: all of it, from a yes of `verifyFile`.
  `slot_of_yes`: from a yes: the first seal, the leaf and the climb in the request tree
    (OnBytes/TypedOracleCompiler/Joined/After.lean), and the query (F4) that holds the request root.

At a written file these queries are those of OnBytes/TypedOracleCompiler/Joined/Queries.lean,
and the theorems are said in its names: OnBytes/TypedOracleCompiler/Joined/Asked.lean [not in this library]; so here
read: not proved in this library.

Limits: statements on one trace. Nothing here says that a seal binds what stands before it: see
OnBytes/TypedOracleCompiler/Joined/Seal.lean. The numbers of the two rounds are written as the chains count them;
`nJ_eq` and `n3_eq` say that they are `Chains.nJ` and `Chains.n3`.
No other file of the library uses `slot_of_yes` yet.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.OursFirst
import OnBytes.TypedOracleCompiler.Joined.Verifier
import OnBytes.TypedOracleCompiler.Joined.After

noncomputable section

namespace TypedOracleCompiler.Joined
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} {Y : Type} {E : ExtSpec}

/-! ## Phases -/

/-- all rounds are shared -/
def AllShA : (s : Shape) → RoundSplits s → Prop
  | [], _ => True
  | _ :: s, (a, A) => a.kind = Kind.sh ∧ AllShA s A

theorem allShA_const : ∀ s : Shape, AllShA s (RoundSplits.const (RAnn.ofShared .sh) s)
  | [] => trivial
  | _ :: s => ⟨rfl, allShA_const s⟩

section Phases
variable {tr : Trace (typedOracleFamily lam K L)} {t : Tag} {cms : List (Dig lam)} {x : Option X} {salt : Bits}
  {rtreq : Dig lam}

/-- local rounds before the joining round: the chain stays before it -/
theorem loc_of_allLo :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ρ₁ : Bits) (ph' : Phase lam)
        (rts : List (Dig lam)) (pls : Plains s) (ρ : Rho s) (R : RootsOfChain lam s),
      AllLoA s A →
      RunsIn tr (recomputeChain (K := K) t cms x salt rtreq s A ws embP i (.loc ρ₁) rts pls)
        (some (ρ, R, ph')) →
      ∃ ρ', ph' = .loc ρ'
  | [], _, _, _, _, ρ₁, ph', _, _, _, _, _, h => by
      have h1 : some (((), (), .loc ρ₁) : Unit × Unit × Phase lam) = some ((), (), ph') :=
        runsIn_pure_iff.1 h
      cases h1
      exact ⟨ρ₁, rfl⟩
  | _ :: s, (_, A), (_, ws), embP, i, ρ₁, ph', rts, (pl, pls), (_, ρ), (_, R), hA, h => by
      obtain ⟨cur, ans, ph₁, rts', hv, -, -, hr⟩ := runsIn_chainB_cons h
      cases hv with
      | f2 _ root ans hk => exact loc_of_allLo s A ws _ (i + 1) _ ph' rts' pls ρ R hA.2 hr
      | join _ rtj rt0 c ans hk hg => rw [hA.1] at hk; cases hk

/-- shared rounds behind the joining round: the chain stays shared, with its slot value -/
theorem shr_of_allSh :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ρ₀ : Bits) (c : Dig lam)
        (ph' : Phase lam) (rts : List (Dig lam)) (pls : Plains s) (ρ : Rho s) (R : RootsOfChain lam s),
      AllShA s A →
      RunsIn tr (recomputeChain (K := K) t cms x salt rtreq s A ws embP i (.shr ρ₀ c) rts pls)
        (some (ρ, R, ph')) →
      ∃ ρ', ph' = .shr ρ' c
  | [], _, _, _, _, ρ₀, c, ph', _, _, _, _, _, h => by
      have h1 : some (((), (), .shr ρ₀ c) : Unit × Unit × Phase lam) = some ((), (), ph') :=
        runsIn_pure_iff.1 h
      cases h1
      exact ⟨ρ₀, rfl⟩
  | _ :: s, (_, A), (_, ws), embP, i, ρ₀, c, ph', rts, (pl, pls), (_, ρ), (_, R), hA, h => by
      obtain ⟨cur, ans, ph₁, rts', hv, -, -, hr⟩ := runsIn_chainB_cons h
      cases hv with
      | f5 _ _ root ans hk => exact shr_of_allSh s A ws _ (i + 1) _ c ph' rts' pls ρ R hA.2 hr
      | f3 _ _ root ans hk => rw [hA.1] at hk; cases hk

/-- local rounds behind the shared ones: the chain stays behind them, with its slot value -/
theorem aft_of_allLo :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ρ₃ : Bits) (c : Dig lam)
        (ph' : Phase lam) (rts : List (Dig lam)) (pls : Plains s) (ρ : Rho s) (R : RootsOfChain lam s),
      RunsIn tr (recomputeChain (K := K) t cms x salt rtreq s A ws embP i (.aft ρ₃ c) rts pls)
        (some (ρ, R, ph')) →
      ∃ ρ', ph' = .aft ρ' c
  | [], _, _, _, _, ρ₃, c, ph', _, _, _, _, h => by
      have h1 : some (((), (), .aft ρ₃ c) : Unit × Unit × Phase lam) = some ((), (), ph') :=
        runsIn_pure_iff.1 h
      cases h1
      exact ⟨ρ₃, rfl⟩
  | _ :: s, (_, A), (_, ws), embP, i, ρ₃, c, ph', rts, (pl, pls), (_, ρ), (_, R), h => by
      obtain ⟨cur, ans, ph₁, rts', hv, -, -, hr⟩ := runsIn_chainB_cons h
      cases hv with
      | f2' _ _ root ans hk => exact aft_of_allLo s A ws _ (i + 1) _ c ph' rts' pls ρ R hr

end Phases

/-! ## The queries at the joins -/

/-- the joining round's number, as the chains count it -/
theorem nJ_eq (G : Chains) : 0 + G.c₁.length = G.nJ := by
  simp [Chains.nJ]

/-- the number of the third chain's first round, as the chains count it -/
theorem n3_eq (G : Chains) : 0 + G.c₁.length + G.c₂.length = G.n3 := by
  simp only [Chains.n3, List.length_cons]
  omega

section Queries
variable (t : Tag) {G : Chains} (D : Desc G Y E)
  (embP : PlainPart G.sh G.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam D.batch)

/-- The first chain's first query, in format (F1): it holds the outer roots, the early part of the
instance and the salt of the argument string; rt: the roots of the round. -/
def qFirst₁ (rt : List (Dig lam)) : FbIn lam L t :=
  ⟨0, .f1 cms ((xin x).map L.early) π.salt, rt,
    emb₁ t embP (Sum.inl (Sum.inr ((RAnn.allLocal G.rF).plain (pls₁ D π).1).2) :
      PlainPart (G.rF :: G.s₁) (RAnn.allLocal G.rF, RoundSplits.allLocal G.s₁))⟩

/-- The query to g in the joining round: it holds the first chain's last chaining value ρ₁. Its
answer is the slot value: the first seal. -/
def qSeal₁ (ρ₁ : Bits) (rt : List (Dig lam)) : JoiningRoundQuery lam L t :=
  ⟨0 + G.c₁.length, ρ₁, rt,
    emb₂ t embP (Sum.inl (Sum.inr (G.aJ.plain (pls₂ D π).1).2) :
      PlainPart (G.rJ :: G.s₂) (G.aJ, RoundSplits.const (RAnn.ofShared .sh) G.s₂))⟩

/-- The second chain's first query, in format (F4): it holds the outer roots and the request root of
the argument string. -/
def qFirst₂ (rt : List (Dig lam)) : FbIn lam L t :=
  ⟨0 + G.c₁.length, .f4 cms (List.ofFn π.rtreq), rt,
    emb₂ t embP (Sum.inl (Sum.inl (G.aJ.plain (pls₂ D π).1).1) :
      PlainPart (G.rJ :: G.s₂) (G.aJ, RoundSplits.const (RAnn.ofShared .sh) G.s₂))⟩

/-- The third chain's first query, in format (F3): it holds the second chain's last chaining value
ρ₀, the second seal, and the slot value c, the first seal. -/
def qFirst₃ (ρ₀ : Bits) (c : Dig lam) (rt : List (Dig lam)) : FbIn lam L t :=
  ⟨0 + G.c₁.length + G.c₂.length, .f3 ρ₀ (List.ofFn c), rt,
    emb₃ t embP (Sum.inl (Sum.inr ((RAnn.allLocal G.r3).plain (pls₃ D π).1).2) :
      PlainPart (G.r3 :: G.s₃) (RAnn.allLocal G.r3, RoundSplits.allLocal G.s₃))⟩

end Queries

/-! ## The three chains of a file -/

section Chains
variable {tr : Trace (typedOracleFamily lam K L)} (t : Tag) {G : Chains} (D : Desc G Y E)
  (wq : ProtocolQueryLayout lam K D.batch) (embP : PlainPart G.sh G.ann → PlainPart (shapeOf L t) (annOf L t))
  (xin : Y → Option X) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam D.batch)

/-- The first chain: its first query is in the trace, and it ends before the joining round. -/
theorem run₁_ends {a : Out lam G.c₁}
    (h : RunsIn tr (run₁ t D wq embP xin cms x π) (some a)) :
    ∃ (rt : List (Dig lam)) (ans : FsAns lam K) (ρ₁ : Bits),
      fbE t (qFirst₁ t D embP xin cms x π rt) ans ∈ tr ∧ a.2.2 = .loc ρ₁ := by
  obtain ⟨⟨c0, ρ⟩, ⟨rt, R⟩, ph'⟩ := a
  have h' : RunsIn tr (recomputeChain (K := K) t cms (xin x) π.salt π.rtreq (G.rF :: G.s₁)
      (RAnn.allLocal G.rF, RoundSplits.allLocal G.s₁) ((wire₁ wq).1, (wire₁ wq).2) (emb₁ t embP) 0 .first
      π.roots ((pls₁ D π).1, (pls₁ D π).2)) (some ((c0, ρ), (rt, R), ph')) := h
  obtain ⟨cur, ans, ph₁, rts', hv, hq, -, hr⟩ := runsIn_chainB_cons h'
  cases hv with
  | f1 root ans hk =>
    obtain ⟨ρ₁, e⟩ := loc_of_allLo G.s₁ _ _ _ _ _ ph' rts' _ ρ R (allLoA_allLocal G.s₁) hr
    exact ⟨root, ans, ρ₁, hq, e⟩

/-- The second chain, from `.loc ρ₁`: the query to g at ρ₁ is in the trace with an answer c, the
query (F4) is in the trace, and the chain ends shared, with the slot value c. -/
theorem run₂_joins (hG : G.Laws) {a : Out lam G.c₁} {b : Out lam G.c₂} {ρ₁ : Bits}
    (ha : a.2.2 = .loc ρ₁) (h : RunsIn tr (run₂ t D wq embP xin cms x π a) (some b)) :
    ∃ (rtj rt0 : List (Dig lam)) (c : Dig lam) (ans : FsAns lam K) (ρ₀ : Bits),
      gE t (qSeal₁ t D embP π ρ₁ rtj) c ∈ tr ∧ fbE t (qFirst₂ t D embP cms π rt0) ans ∈ tr ∧
        b.2.2 = .shr ρ₀ c := by
  obtain ⟨⟨c0, ρ⟩, ⟨rt, R⟩, ph'⟩ := b
  unfold run₂ at h
  rw [ha] at h
  have h' : RunsIn tr (recomputeChain (K := K) t cms (xin x) π.salt π.rtreq (G.rJ :: G.s₂)
      (G.aJ, RoundSplits.const (RAnn.ofShared .sh) G.s₂) ((wire₂ wq).1, (wire₂ wq).2) (emb₂ t embP)
      (0 + G.c₁.length) (.loc ρ₁) (π.roots.drop (RootsOfChain.count G.c₁ a.2.1))
      ((pls₂ D π).1, (pls₂ D π).2)) (some ((c0, ρ), (rt, R), ph')) := h
  obtain ⟨cur, ans, ph₁, rts', hv, hq, -, hr⟩ := runsIn_chainB_cons h'
  cases hv with
  | f2 _ root ans hk => rw [hG.kindJ] at hk; cases hk
  | join _ rtj rt0 c ans hk hg =>
    obtain ⟨ρ₀, e⟩ := shr_of_allSh G.s₂ _ _ _ _ _ c ph' rts' _ ρ R (allShA_const G.s₂) hr
    exact ⟨rtj, rt0, c, ans, ρ₀, hg, hq, e⟩

/-- The third chain, from `.shr ρ₀ c`: the query (F3) at ρ₀ and c is in the trace, and the chain
ends with the same slot value c. -/
theorem run₃_joins {a : Out lam G.c₁} {b : Out lam G.c₂} {d : Out lam G.c₃} {ρ₀ : Bits}
    {c : Dig lam} (hb : b.2.2 = .shr ρ₀ c)
    (h : RunsIn tr (run₃ t D wq embP xin cms x π a b) (some d)) :
    ∃ (rt : List (Dig lam)) (ans : FsAns lam K) (ρ₃ : Bits),
      fbE t (qFirst₃ t D embP π ρ₀ c rt) ans ∈ tr ∧ d.2.2 = .aft ρ₃ c := by
  obtain ⟨⟨c0, ρ⟩, ⟨rt, R⟩, ph'⟩ := d
  unfold run₃ at h
  rw [hb] at h
  have h' : RunsIn tr (recomputeChain (K := K) t cms (xin x) π.salt π.rtreq (G.r3 :: G.s₃)
      (RAnn.allLocal G.r3, RoundSplits.allLocal G.s₃) ((wire₃ wq).1, (wire₃ wq).2) (emb₃ t embP)
      (0 + G.c₁.length + G.c₂.length) (.shr ρ₀ c)
      ((π.roots.drop (RootsOfChain.count G.c₁ a.2.1)).drop (RootsOfChain.count G.c₂ b.2.1))
      ((pls₃ D π).1, (pls₃ D π).2)) (some ((c0, ρ), (rt, R), ph')) := h
  obtain ⟨cur, ans, ph₁, rts', hv, hq, -, hr⟩ := runsIn_chainB_cons h'
  cases hv with
  | f5 _ _ root ans hk =>
    have hk' : Kind.lo = Kind.sh := hk
    cases hk'
  | f3 _ _ root ans hk =>
    obtain ⟨ρ₃, e⟩ := aft_of_allLo G.s₃ _ _ _ _ _ c ph' rts' _ ρ R hr
    exact ⟨root, ans, ρ₃, hq, e⟩

end Chains

/-! ## From a yes -/

section Yes
variable {tr : Trace (typedOracleFamily lam K L)} (sMT sFS : ℕ) (t : Tag) {G : Chains} (D : Desc G Y E)
  (wq : ProtocolQueryLayout lam K D.batch) (embS : (p : OPos G.sh) → OSym G.sh p → Body L)
  (embP : PlainPart G.sh G.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam D.batch)

/-- Where the verifier of a file says yes in a trace: the three chains run to values a, b, d, each
from where the chain before it ended. The first ends in `.loc ρ₁`, the second in `.shr ρ₀ c`, the
third in `.aft ρ₃ c`. The first queries of the three chains and the query to g are in the trace: g
is asked at ρ₁ and answers c; (F3) holds ρ₀ and c. The part behind the chains says yes in the phase
`.aft ρ₃ c`. -/
theorem joins_of_yes (hG : G.Laws)
    (h : RunsIn tr (verifyFile sMT sFS t D wq embS embP xin embE depthReq cms x π) true) :
    ∃ (a : Out lam G.c₁) (b : Out lam G.c₂) (d : Out lam G.c₃) (ρ₁ ρ₀ ρ₃ : Bits) (c : Dig lam)
      (rt1 rtj rt0 rt3 : List (Dig lam)) (ans1 ans2 ans3 : FsAns lam K),
      RunsIn tr (run₁ t D wq embP xin cms x π) (some a) ∧
      RunsIn tr (run₂ t D wq embP xin cms x π a) (some b) ∧
      RunsIn tr (run₃ t D wq embP xin cms x π a b) (some d) ∧
      a.2.2 = .loc ρ₁ ∧ b.2.2 = .shr ρ₀ c ∧ d.2.2 = .aft ρ₃ c ∧
      fbE t (qFirst₁ t D embP xin cms x π rt1) ans1 ∈ tr ∧
      gE t (qSeal₁ t D embP π ρ₁ rtj) c ∈ tr ∧
      fbE t (qFirst₂ t D embP cms π rt0) ans2 ∈ tr ∧
      fbE t (qFirst₃ t D embP π ρ₀ c rt3) ans3 ∈ tr ∧
      proofHasStrictFormat sMT sFS D.batch wq depthReq x π (glue a b d).1 (glue a b d).2.1 (.aft ρ₃ c) = true ∧
      RunsIn tr (checkPrunedOpenings D.batch wq embS embE depthReq cms x π (glue a b d).1 (glue a b d).2.1
        (.aft ρ₃ c)) true := by
  obtain ⟨a, b, d, ha, hb, hd, hs, hA⟩ :=
    (runsIn_verifyFile_iff sMT sFS t D wq embS embP xin embE depthReq cms x π).1 h
  obtain ⟨rt1, ans1, ρ₁, q1, e1⟩ := run₁_ends t D wq embP xin cms x π ha
  obtain ⟨rtj, rt0, c, ans2, ρ₀, qg, q2, e2⟩ := run₂_joins t D wq embP xin cms x π hG e1 hb
  obtain ⟨rt3, ans3, ρ₃, q3, e3⟩ := run₃_joins t D wq embP xin cms x π e2 hd
  have e : (glue a b d).2.2 = .aft ρ₃ c := e3
  rw [e] at hs hA
  exact ⟨a, b, d, ρ₁, ρ₀, ρ₃, c, rt1, rtj, rt0, rt3, ans1, ans2, ans3, ha, hb, hd, e1, e2, e3, q1,
    qg, q2, q3, hs, hA⟩

/-- Where the verifier of a file says yes in a trace, the first seal is bound to the request root
that the second chain's first query holds: g is asked at some ρ₁ and answers c; the request tree's
leaf query at c, with `π.rsalt` behind it, is in the trace; the climb from its answer along
`π.path`, from the place `π.slot`, ends in `π.rtreq`; and the query (F4), which holds `π.rtreq`,
is in the trace.
"Bound" is said of this one trace: these entries stand in it. That a seal binds what stands before
it is not said here (the Limits of this file). -/
theorem slot_of_yes (hG : G.Laws)
    (h : RunsIn tr (verifyFile sMT sFS t D wq embS embP xin embE depthReq cms x π) true) :
    ∃ (ρ₁ : Bits) (c : Dig lam) (rtj rt0 : List (Dig lam)) (ans2 : FsAns lam K) (e : Dig lam),
      gE t (qSeal₁ t D embP π ρ₁ rtj) c ∈ tr ∧
      (⟨OracleName.rleaf, List.ofFn c ++ π.rsalt, e⟩ : QA (typedOracleFamily lam K L)) ∈ tr ∧
      ClimbReq tr π.path π.slot e π.rtreq ∧
      π.path.length = depthReq ∧ π.slot < 2 ^ depthReq ∧
      fbE t (qFirst₂ t D embP cms π rt0) ans2 ∈ tr := by
  obtain ⟨a, b, d, ρ₁, ρ₀, ρ₃, c, rt1, rtj, rt0, rt3, ans1, ans2, ans3, -, -, -, -, -, -, -, qg, q2,
    -, -, hA⟩ := joins_of_yes sMT sFS t D wq embS embP xin embE depthReq cms x π hG h
  obtain ⟨hl, hs, e, he, hc⟩ := request_of_yes hA (c := c) rfl
  exact ⟨ρ₁, c, rtj, rt0, ans2, e, qg, he, hc, hl, hs, q2⟩

end Yes

end TypedOracleCompiler.Joined
