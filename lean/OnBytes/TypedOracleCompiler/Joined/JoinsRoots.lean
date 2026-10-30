-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/JoinsRoots.lean: the queries between the three chains of a file, with their roots
written out.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

OnBytes/TypedOracleCompiler/Joined/Joins.lean says that the first query of each chain and the query to g are in the
trace where the verifier of a file says yes; there the roots that these queries hold are some lists.
Here they are said: each is the next stretch of `π.roots`, the one list of roots of the argument
string, as long as the round's component has trees.

  The first chain's first query holds the first roots of the list.
  The second chain starts with the roots that the first has left. The query to g holds the first of
    these, for the trees of the slot's component of the joining round; the query (F4) holds the
    next, for the trees of the shared component.
  The third chain's first query holds the first of the roots that the first two chains have left.

How many roots a chain has taken is counted in what it yields (`RootsOfChain.count`).

Main names:
  `rts₂`, `rts₃`: the roots that are left for the second and for the third chain.
  `run₁_asks`, `run₂_asks`, `run₃_asks`: the three chains.
  `asks_of_yes`: all of it, from a yes of `verifyFile`.

Limits: statements on one trace. Nothing is said of the roots of later rounds of a chain: for these
see `flat_of_runsIn` (OnBytes/TypedOracleCompiler/Joined/Roots.lean).
OnBytes/TypedOracleCompiler/Joined/JoinsAt.lean uses `run₂_asks` and `rts₂`; no other file of the library uses
`run₁_asks`, `run₃_asks`, `asks_of_yes` or `rts₃` yet.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Joined.Joins
import OnBytes.TypedOracleCompiler.Joined.Roots

noncomputable section

namespace TypedOracleCompiler.Joined
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} {Y : Type} {E : ExtSpec}

/-! ## The first round's roots -/

/-- a round that takes roots for the slot's component alone: they are the first of the list -/
theorem take_of_flat_own {r : Round} {s : Shape} {rt l : List (Dig lam)} {R : RootsOfChain lam s}
    (h : RT.flat (r :: s) ((none, some rt), R) <+: l) : rt = l.take rt.length := by
  have h1 : rt ++ [] ++ RT.flat s R <+: l := h
  rw [List.append_nil] at h1
  exact List.prefix_iff_eq_take.1 ((List.prefix_append _ _).trans h1)

/-- the joining round: the roots for the slot's component are the first of the list, those for the
shared component the next -/
theorem take_of_flat_join {r : Round} {s : Shape} {rtj rt0 l : List (Dig lam)} {R : RootsOfChain lam s}
    (h : RT.flat (r :: s) ((some rt0, some rtj), R) <+: l) :
    rtj = l.take rtj.length ∧ rt0 = (l.drop rtj.length).take rt0.length := by
  have h1 : rtj ++ rt0 ++ RT.flat s R <+: l := h
  obtain ⟨u, rfl⟩ := h1
  constructor <;> simp [List.append_assoc]

/-! ## The three chains of a file -/

section Chains
variable {tr : Trace (typedOracleFamily lam K L)} (t : Tag) {G : Chains} (D : Desc G Y E)
  (wq : ProtocolQueryLayout lam K D.batch) (embP : PlainPart G.sh G.ann → PlainPart (shapeOf L t) (annOf L t))
  (xin : Y → Option X) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam D.batch)

/-- the roots that the first chain has left -/
def rts₂ (a : Out lam G.c₁) : List (Dig lam) := π.roots.drop (RootsOfChain.count G.c₁ a.2.1)

/-- the roots that the first two chains have left -/
def rts₃ (a : Out lam G.c₁) (b : Out lam G.c₂) : List (Dig lam) :=
  (π.roots.drop (RootsOfChain.count G.c₁ a.2.1)).drop (RootsOfChain.count G.c₂ b.2.1)

/-- The first chain: its first query, with the first roots of the list, is in the trace, and the
chain ends before the joining round. -/
theorem run₁_asks {a : Out lam G.c₁}
    (h : RunsIn tr (run₁ t D wq embP xin cms x π) (some a)) :
    ∃ (ans : FsAns lam K) (ρ₁ : Bits),
      fbE t (qFirst₁ t D embP xin cms x π (π.roots.take (wire₁ wq).1.depthJ.length)) ans ∈ tr ∧
        a.2.2 = .loc ρ₁ := by
  obtain ⟨⟨c0, ρ⟩, ⟨rt, R⟩, ph'⟩ := a
  have h' : RunsIn tr (recomputeChain (K := K) t cms (xin x) π.salt π.rtreq (G.rF :: G.s₁)
      (RAnn.allLocal G.rF, RoundSplits.allLocal G.s₁) ((wire₁ wq).1, (wire₁ wq).2) (emb₁ t embP) 0 .first
      π.roots ((pls₁ D π).1, (pls₁ D π).2)) (some ((c0, ρ), (rt, R), ph')) := h
  have hp := flat_prefix_of_runsIn t cms (xin x) π.salt π.rtreq _ _ _ _ _ _ _ _ _ _ _ h'
  obtain ⟨cur, ans, ph₁, rts', hv, hq, -, hr, hfl⟩ := runsIn_chainB_cons_flags h'
  cases hv with
  | f1 root ans hk =>
    obtain ⟨ρ₁, e⟩ := loc_of_allLo G.s₁ _ _ _ _ _ ph' rts' _ ρ R (allLoA_allLocal G.s₁) hr
    have hroot := take_of_flat_own hp
    rw [(hfl.2 root rfl).1] at hroot
    subst hroot
    exact ⟨ans, ρ₁, hq, e⟩

/-- The second chain, from `.loc ρ₁`: the query to g at ρ₁, with the first of the roots that are
left, is in the trace with an answer c; the query (F4), with the next roots, is in the trace; and
the chain ends shared, with the slot value c. -/
theorem run₂_asks (hG : G.Laws) {a : Out lam G.c₁} {b : Out lam G.c₂} {ρ₁ : Bits}
    (ha : a.2.2 = .loc ρ₁) (h : RunsIn tr (run₂ t D wq embP xin cms x π a) (some b)) :
    ∃ (c : Dig lam) (ans : FsAns lam K) (ρ₀ : Bits),
      gE t (qSeal₁ t D embP π ρ₁ ((rts₂ D π a).take (wire₂ wq).1.depthJ.length)) c ∈ tr ∧
      fbE t (qFirst₂ t D embP cms π
        (((rts₂ D π a).drop (wire₂ wq).1.depthJ.length).take (wire₂ wq).1.depth0.length)) ans ∈ tr ∧
      b.2.2 = .shr ρ₀ c := by
  obtain ⟨⟨c0, ρ⟩, ⟨rt, R⟩, ph'⟩ := b
  unfold run₂ at h
  rw [ha] at h
  have h' : RunsIn tr (recomputeChain (K := K) t cms (xin x) π.salt π.rtreq (G.rJ :: G.s₂)
      (G.aJ, RoundSplits.const (RAnn.ofShared .sh) G.s₂) ((wire₂ wq).1, (wire₂ wq).2) (emb₂ t embP)
      (0 + G.c₁.length) (.loc ρ₁) (rts₂ D π a)
      ((pls₂ D π).1, (pls₂ D π).2)) (some ((c0, ρ), (rt, R), ph')) := h
  have hp := flat_prefix_of_runsIn t cms (xin x) π.salt π.rtreq _ _ _ _ _ _ _ _ _ _ _ h'
  obtain ⟨cur, ans, ph₁, rts', hv, hq, -, hr, hfl⟩ := runsIn_chainB_cons_flags h'
  cases hv with
  | f2 _ root ans hk => rw [hG.kindJ] at hk; cases hk
  | join _ rtj rt0 c ans hk hg =>
    obtain ⟨ρ₀, e⟩ := shr_of_allSh G.s₂ _ _ _ _ _ c ph' rts' _ ρ R (allShA_const G.s₂) hr
    obtain ⟨hj, h0⟩ := take_of_flat_join hp
    rw [(hfl.2 rtj rfl).1] at hj h0
    rw [(hfl.1 rt0 rfl).1] at h0
    subst hj
    subst h0
    exact ⟨c, ans, ρ₀, hg, hq, e⟩

/-- The third chain, from `.shr ρ₀ c`: the query (F3) at ρ₀ and c, with the first of the roots that
are left, is in the trace, and the chain ends with the same slot value c. -/
theorem run₃_asks {a : Out lam G.c₁} {b : Out lam G.c₂} {d : Out lam G.c₃} {ρ₀ : Bits}
    {c : Dig lam} (hb : b.2.2 = .shr ρ₀ c)
    (h : RunsIn tr (run₃ t D wq embP xin cms x π a b) (some d)) :
    ∃ (ans : FsAns lam K) (ρ₃ : Bits),
      fbE t (qFirst₃ t D embP π ρ₀ c ((rts₃ D π a b).take (wire₃ wq).1.depthJ.length)) ans ∈ tr ∧
        d.2.2 = .aft ρ₃ c := by
  obtain ⟨⟨c0, ρ⟩, ⟨rt, R⟩, ph'⟩ := d
  unfold run₃ at h
  rw [hb] at h
  have h' : RunsIn tr (recomputeChain (K := K) t cms (xin x) π.salt π.rtreq (G.r3 :: G.s₃)
      (RAnn.allLocal G.r3, RoundSplits.allLocal G.s₃) ((wire₃ wq).1, (wire₃ wq).2) (emb₃ t embP)
      (0 + G.c₁.length + G.c₂.length) (.shr ρ₀ c) (rts₃ D π a b)
      ((pls₃ D π).1, (pls₃ D π).2)) (some ((c0, ρ), (rt, R), ph')) := h
  have hp := flat_prefix_of_runsIn t cms (xin x) π.salt π.rtreq _ _ _ _ _ _ _ _ _ _ _ h'
  obtain ⟨cur, ans, ph₁, rts', hv, hq, -, hr, hfl⟩ := runsIn_chainB_cons_flags h'
  cases hv with
  | f5 _ _ root ans hk =>
    have hk' : Kind.lo = Kind.sh := hk
    cases hk'
  | f3 _ _ root ans hk =>
    obtain ⟨ρ₃, e⟩ := aft_of_allLo G.s₃ _ _ _ _ _ c ph' rts' _ ρ R hr
    have hroot := take_of_flat_own hp
    rw [(hfl.2 root rfl).1] at hroot
    subst hroot
    exact ⟨ans, ρ₃, hq, e⟩

end Chains

/-! ## From a yes -/

section Yes
variable {tr : Trace (typedOracleFamily lam K L)} (sMT sFS : ℕ) (t : Tag) {G : Chains} (D : Desc G Y E)
  (wq : ProtocolQueryLayout lam K D.batch) (embS : (p : OPos G.sh) → OSym G.sh p → Body L)
  (embP : PlainPart G.sh G.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam D.batch)

/-- Where the verifier of a file says yes in a trace: the three chains run to values a, b, d, each
from where the chain before it ended, and end in `.loc ρ₁`, `.shr ρ₀ c`, `.aft ρ₃ c`. The first
queries of the three chains and the query to g are in the trace, each with its stretch of
`π.roots`. -/
theorem asks_of_yes (hG : G.Laws)
    (h : RunsIn tr (verifyFile sMT sFS t D wq embS embP xin embE depthReq cms x π) true) :
    ∃ (a : Out lam G.c₁) (b : Out lam G.c₂) (d : Out lam G.c₃) (ρ₁ ρ₀ ρ₃ : Bits) (c : Dig lam)
      (ans1 ans2 ans3 : FsAns lam K),
      RunsIn tr (run₁ t D wq embP xin cms x π) (some a) ∧
      RunsIn tr (run₂ t D wq embP xin cms x π a) (some b) ∧
      RunsIn tr (run₃ t D wq embP xin cms x π a b) (some d) ∧
      a.2.2 = .loc ρ₁ ∧ b.2.2 = .shr ρ₀ c ∧ d.2.2 = .aft ρ₃ c ∧
      fbE t (qFirst₁ t D embP xin cms x π (π.roots.take (wire₁ wq).1.depthJ.length)) ans1 ∈ tr ∧
      gE t (qSeal₁ t D embP π ρ₁ ((rts₂ D π a).take (wire₂ wq).1.depthJ.length)) c ∈ tr ∧
      fbE t (qFirst₂ t D embP cms π
        (((rts₂ D π a).drop (wire₂ wq).1.depthJ.length).take (wire₂ wq).1.depth0.length)) ans2 ∈
          tr ∧
      fbE t (qFirst₃ t D embP π ρ₀ c ((rts₃ D π a b).take (wire₃ wq).1.depthJ.length)) ans3 ∈
        tr := by
  obtain ⟨a, b, d, ha, hb, hd, -, -⟩ :=
    (runsIn_verifyFile_iff sMT sFS t D wq embS embP xin embE depthReq cms x π).1 h
  obtain ⟨ans1, ρ₁, q1, e1⟩ := run₁_asks t D wq embP xin cms x π ha
  obtain ⟨c, ans2, ρ₀, qg, q2, e2⟩ := run₂_asks t D wq embP xin cms x π hG e1 hb
  obtain ⟨ans3, ρ₃, q3, e3⟩ := run₃_asks t D wq embP xin cms x π e2 hd
  exact ⟨a, b, d, ρ₁, ρ₀, ρ₃, c, ans1, ans2, ans3, ha, hb, hd, e1, e2, e3, q1, qg, q2, q3⟩

end Yes

end TypedOracleCompiler.Joined
