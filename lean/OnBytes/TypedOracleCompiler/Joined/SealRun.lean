-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/SealRun.lean: an accepted run of the compiled verifier lays the joined chains
into the trace.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

OnBytes/TypedOracleCompiler/Joined/Seal.lean says what a seal binds, of chains of queries in a trace (`Leads`,
`Three`). This file ties that to the verifier: if the compiled verifier of one slot
(`verifyB`, OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean) accepts and all its queries are in the trace,
then its own queries form such chains. So "the first seal", "the slot", "the binding root" and "the
second seal" can be said of the typed values of a run.

Main names:
  `Behind t tr cms xo salt rtreq ph`: what the verifier's chain has laid into the trace when it
    stands in the phase ph: the chains so far, with the heads of their oldest queries.
  `Behind.step`, `behind_of_chainB`: one round; all rounds.
  `opensIn_of_reqCheck`: a yes of the check in the request tree: the slot value stands at the
    slot's leaf under the request root, by queries of the trace.
  `parts_of_accepted`: an accepted run holds a run of the chain and, once the chain has joined, a
    yes of the check in the request tree.
  `three_of_accepted`: if the chain ends behind a last stretch of local rounds: `Three`, with the
    first query (F1) at our outer roots, instance and salt, and (F4) at our request root.

What stands between the chains of a file, and what binds it:
  the slot's salt: `OneProtocolProof.rsalt`. It is cut off by the view of the request tree's leaf
    (`rleaf_view`, OnBytes/TypedOracleCompiler/Joined/ExtractReads.lean). No seal names it. It costs no event.
  the last chain's own random bytes: they ride in the plain part of the round between the shared
    chain and the last chain, and are hashed in (F3). `Three.unique` names that query, so they are
    bound. Nothing here asks that the decision reads them. They cost no event.
  the shared chain's own random bytes: they ride in the plain part of the joining round. Of that
    plain part the slot's share is hashed in the query to g and the shared one in (F4);
    `Three.unique` names both queries. They cost no event.
  the instance: (F1) holds `L.early` of it. The whole stands in the query of the round `L.late`, if
    there is one; else what `L.early` drops is named by no seal.
  the binding root: `OneProtocolProof.rtreq`, in (F4): `Three.unique_shared`, `slot_of_root`; paid in `EM`.
  both seals: link values; paid in `EF`.
  the answers of the record over the chains: part of the instance, and free data in the plain part
    of the joining round. The decision of the protocol is the one place that can compare the two:
    no theorem here says that it does. They cost no event.
  the seeds of that record: NOT bound by anything here. They are drawn by queries of their own,
    outside this verifier; for these files they are part of the instance.

Limits: statements on one trace; nothing on probability. Nothing on the openings of trees.
No other file of the library uses `three_of_accepted`, `parts_of_accepted` or `behind_of_accepted`
yet.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Runs
import OnBytes.TypedOracleCompiler.Joined.Seal

namespace TypedOracleCompiler.Joined
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Compile (Tag posOf RunsIn runsIn_bind_iff runsIn_pure_iff runsIn_ask_iff bind_eq
  opensIn_of_climbsIn climbM)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## The chain -/

/-- What the verifier's chain has laid into the trace when it stands in a phase. In the first local
rounds: a chain from a first query (F1) with our outer roots, instance and salt to the chaining
value. In the shared rounds: that chain up to the query to g, whose answer is the slot value, and
a chain from (F4) with our request root to the chaining value. In the last local rounds: both, and
a chain from (F3), which holds the shared chain's last value and the slot value. -/
def Behind (t : Tag) (tr : Trace (typedOracleFamily lam K L)) (cms : List (Dig lam)) (xo : Option X)
    (salt : Bits) (rtreq : Dig lam) : Phase lam → Prop
  | .first => True
  | .loc ρ => ∃ q₁ l₁, q₁.head = .f1 cms xo salt ∧ Leads t tr q₁ l₁ ρ
  | .shr ρ0 c => ∃ q₁ l₁ qg q₂ l₂, q₁.head = .f1 cms xo salt ∧ Leads t tr q₁ l₁ qg.ρ ∧
      gE t qg c ∈ tr ∧ q₂.head = .f4 cms (List.ofFn rtreq) ∧ Leads t tr q₂ l₂ ρ0
  | .aft ρ c => ∃ q₁ l₁ qg q₂ l₂ ρ0 q₃ l₃, q₁.head = .f1 cms xo salt ∧ Leads t tr q₁ l₁ qg.ρ ∧
      gE t qg c ∈ tr ∧ q₂.head = .f4 cms (List.ofFn rtreq) ∧ Leads t tr q₂ l₂ ρ0 ∧
      q₃.head = .f3 ρ0 (List.ofFn c) ∧ Leads t tr q₃ l₃ ρ

/-- One round of the verifier's chain. -/
theorem Behind.step {t : Tag} {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s}
    {tr : Trace (typedOracleFamily lam K L)} {cms : List (Dig lam)} {x : Option X} {salt : Bits}
    {rtreq : Dig lam} {embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)} {i : ℕ}
    {pl : r.Plain} {ph ph₁ : Phase lam} {cur : Item lam L t} {ans : FsAns lam K}
    {rt : RtC lam × RtC lam} (h : VStep tr cms x salt rtreq embP i pl ph cur ans ph₁ rt)
    (hm : fbE t cur.q ans ∈ tr) (hb : Behind t tr cms (x.map L.early) salt rtreq ph) :
    Behind t tr cms (x.map L.early) salt rtreq ph₁ := by
  cases h with
  | f1 root ans hk => exact ⟨_, _, rfl, .first hm rfl⟩
  | f2 ρ root ans hk =>
    obtain ⟨q₁, l₁, e, hl⟩ := hb
    exact ⟨q₁, _, e, .next hl hm rfl rfl⟩
  | join ρ rtj rt0 c ans hk hg =>
    obtain ⟨q₁, l₁, e, hl⟩ := hb
    refine ⟨q₁, l₁, _, _, _, e, ?_, hg, rfl, .first hm rfl⟩
    exact hl
  | f5 ρ0 c root ans hk =>
    obtain ⟨q₁, l₁, qg, q₂, l₂, e, hl, hg, e2, hl2⟩ := hb
    exact ⟨q₁, l₁, qg, q₂, _, e, hl, hg, e2, .next hl2 hm rfl rfl⟩
  | f3 ρ0 c root ans hk =>
    obtain ⟨q₁, l₁, qg, q₂, l₂, e, hl, hg, e2, hl2⟩ := hb
    exact ⟨q₁, l₁, qg, q₂, l₂, ρ0, _, _, e, hl, hg, e2, hl2, rfl, .first hm rfl⟩
  | f2' ρ c root ans hk =>
    obtain ⟨q₁, l₁, qg, q₂, l₂, ρ0, q₃, l₃, e, hl, hg, e2, hl2, e3, hl3⟩ := hb
    exact ⟨q₁, l₁, qg, q₂, l₂, ρ0, q₃, _, e, hl, hg, e2, hl2, e3, .next hl3 hm rfl rfl⟩

/-- All rounds: a run of the verifier's chain in the trace leads from `Behind` at its first phase to
`Behind` at its last. -/
theorem behind_of_chainB {tr : Trace (typedOracleFamily lam K L)} {t : Tag} {cms : List (Dig lam)}
    {x : Option X} {salt : Bits} {rtreq : Dig lam} :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph ph' : Phase lam)
        (rts : List (Dig lam)) (pls : Plains s) (ρ : Rho s) (RTs : RootsOfChain lam s),
      Behind t tr cms (x.map L.early) salt rtreq ph →
      RunsIn tr (recomputeChain (K := K) t cms x salt rtreq s A ws embP i ph rts pls) (some (ρ, RTs, ph')) →
      Behind t tr cms (x.map L.early) salt rtreq ph'
  | [], _, _, _, _, ph, ph', _, _, _, _, hb, h => by
      have h1 : some (((), (), ph) : Unit × Unit × Phase lam) = some ((), (), ph') :=
        runsIn_pure_iff.1 h
      cases h1
      exact hb
  | _ :: s, (_, A), (_, ws), embP, i, ph, ph', rts, (pl, pls), (_, ρ), (_, RTs), hb, h => by
      obtain ⟨cur, ans, ph₁, rts', hv, hm, -, hr⟩ := runsIn_chainB_cons h
      exact behind_of_chainB s A ws _ (i + 1) ph₁ ph' rts' pls ρ RTs (hb.step hv hm) hr

/-! ## The request tree -/

/-- A yes of the check in the request tree: the slot value stands at the slot's leaf under the
request root, by queries of the trace. -/
theorem opensIn_of_reqCheck {tr : Trace (typedOracleFamily lam K L)} {d : ℕ} {rtreq : Dig lam} {slot : ℕ}
    {path : List (Dig lam)} {c : Dig lam} {rs : Bits}
    (hr : RunsIn tr (reqCheck (K := K) (L := L) d rtreq slot path c rs) true) :
    (pairR lam K L).OpensIn tr (posOf d slot) (List.ofFn c) rtreq := by
  unfold reqCheck at hr
  split at hr
  · rename_i hc
    have h' : RunsIn tr ((askTypedOracle (K := K) (L := L) OracleName.rleaf (List.ofFn c ++ rs)).bind fun dg =>
        (climbM rnodeV path slot dg).bind fun r => OComp.pure (decide (r = rtreq))) true := hr
    obtain ⟨dg, hd, h2⟩ := (runsIn_bind_iff _ _ _).1 h'
    obtain ⟨r, hr', h3⟩ := (runsIn_bind_iff _ _ _).1 h2
    have hd' : (⟨OracleName.rleaf, List.ofFn c ++ rs, dg⟩ : QA (typedOracleFamily lam K L)) ∈ tr := runsIn_ask_iff.1 hd
    have ht : (List.ofFn c ++ rs).take lam = List.ofFn c := by
      rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp)]
    have hrt : r = rtreq := of_decide_eq_true (runsIn_pure_iff.1 h3)
    rw [← hrt]
    exact opensIn_of_climbsIn (pairR lam K L) (rleaf_recorded_iff.2 ⟨_, ht, hd'⟩) d path r hc.1
      ((runsIn_climbM_req_iff path slot dg r).1 hr')
  · cases runsIn_pure_iff.1 hr

/-! ## The verifier -/

section Verifier
variable {t : Tag} {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} {wq : ProtocolQueryLayout lam K Q}
  {embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L}
  {embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)} {xin : Y → Option X}
  {embE : E.Sym → Body L} {d : ℕ} {cms : List (Dig lam)} {x : Y} {π : OneProtocolProof lam Q}
  {tr : Trace (typedOracleFamily lam K L)}

/-- An accepted run of the compiled verifier of a slot holds a run of the chain and, once the chain
has joined, a yes of the check in the request tree at the slot value. -/
theorem parts_of_accepted (hrun : RunsIn tr (verifyB t Q wq embS embP xin embE d cms x π) true) :
    ∃ ρ rts ph, RunsIn tr (recomputeChainOfProof t Q wq embP xin cms x π) (some (ρ, rts, ph)) ∧
      ∀ c, ph.slotVal = some c →
        RunsIn tr (reqCheck (K := K) (L := L) d π.rtreq π.slot π.path c π.rsalt) true := by
  letI := wq.decO
  letI := wq.ext.dec
  unfold verifyB afterB at hrun
  obtain ⟨r, hr, h2⟩ := (runsIn_bind_iff _ _ _).1 hrun
  cases r with
  | none => cases runsIn_pure_iff.1 h2
  | some z =>
    obtain ⟨ρ, rts, ph⟩ := z
    refine ⟨ρ, rts, ph, hr, fun c hc => ?_⟩
    dsimp only at h2
    split at h2
    · split at h2
      · rw [bind_eq] at h2
        obtain ⟨ok, -, h3⟩ := (runsIn_bind_iff _ _ _).1 h2
        simp only [hc] at h3
        rw [bind_eq] at h3
        obtain ⟨y, hy, h4⟩ := (runsIn_bind_iff _ _ _).1 h3
        have h5 := Bool.and_eq_true_iff.1 (runsIn_pure_iff.1 h4)
        obtain ⟨-, rfl⟩ := Bool.and_eq_true_iff.1 h5.1
        exact hy
      · cases runsIn_pure_iff.1 h2
    · cases runsIn_pure_iff.1 h2

/-- An accepted run lays the chains into the trace: `Behind` at the phase in which its chain
ends. -/
theorem behind_of_accepted (hrun : RunsIn tr (verifyB t Q wq embS embP xin embE d cms x π) true) :
    ∃ ρ rts ph, RunsIn tr (recomputeChainOfProof t Q wq embP xin cms x π) (some (ρ, rts, ph)) ∧
      Behind t tr cms ((xin x).map L.early) π.salt π.rtreq ph := by
  obtain ⟨ρ, rts, ph, hr, -⟩ := parts_of_accepted hrun
  exact ⟨ρ, rts, ph, hr, behind_of_chainB _ _ _ _ 0 .first ph _ _ ρ rts trivial hr⟩

theorem chainFields_f1 {q : FbIn lam L t} {cs : List (Dig lam)} {xo : Option X} {sl : Bits}
    (h : q.head = .f1 cs xo sl) : chainFields q = [] := by
  unfold chainFields; rw [h]

/-- **An accepted run lays three joined chains into the trace**, if its chain ends behind a last
stretch of local rounds, in the chaining value v with the slot value c. The first chain starts at
(F1) with our outer roots, instance and salt; the shared chain at (F4) with our outer roots and
request root; the slot value stands at our slot's leaf under that root. -/
theorem three_of_accepted (hrun : RunsIn tr (verifyB t Q wq embS embP xin embE d cms x π) true) :
    ∃ ρ rts ph, RunsIn tr (recomputeChainOfProof t Q wq embP xin cms x π) (some (ρ, rts, ph)) ∧
      ∀ v c, ph = .aft v c →
        ∃ q₁ l₁ qg q₂ l₂ ρ0 q₃ l₃, Three t tr d π.slot q₁ l₁ qg c q₂ l₂ ρ0 q₃ l₃ v ∧
          q₁.head = .f1 cms ((xin x).map L.early) π.salt ∧
          q₂.head = .f4 cms (List.ofFn π.rtreq) := by
  obtain ⟨ρ, rts, ph, hr, hreq⟩ := parts_of_accepted hrun
  refine ⟨ρ, rts, ph, hr, ?_⟩
  rintro v c rfl
  obtain ⟨q₁, l₁, qg, q₂, l₂, ρ0, q₃, l₃, e, hl, hg, e2, hl2, e3, hl3⟩ :=
    behind_of_chainB _ _ _ _ 0 .first (.aft v c) _ _ ρ rts trivial hr
  exact ⟨q₁, l₁, qg, q₂, l₂, ρ0, q₃, l₃,
    ⟨chainFields_f1 e, hl, hg, ⟨cms, π.rtreq, e2, opensIn_of_reqCheck (hreq c rfl)⟩, hl2, e3, hl3⟩,
    e, e2⟩

end Verifier

end TypedOracleCompiler.Joined
