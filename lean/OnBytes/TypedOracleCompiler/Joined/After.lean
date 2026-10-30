-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/After.lean: what a yes of the compiled verifier says of the part behind the
chain, and above all of the request tree, query by query.

OnBytes/TypedOracleCompiler/ holds the verifier side of the compiler beneath `innerCompiledVerifier`. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

Behind its chain the compiled verifier of one slot (`checkPrunedOpenings`,
OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean) walks the forests of openings, checks the slot value in the
request tree if the chain has joined (`reqPart`, `reqCheck`), and asks the local verifier. Here a
run of that part within a trace is taken apart.

Main names:
  `runsIn_afterBO_iff`: the part behind the chain runs to yes exactly if the forests are there and
    within the limits, their walks run to yes, the request tree's check runs to yes, and the local
    verifier accepts the transcript that is built from the openings.
  `runsIn_reqPart_iff`: the request tree's check, by the phase in which the chain has ended.
  `ClimbReq tr path j c r`: the queries to the request tree's node oracle that lead from the digest
    c at place j along path to r are entries of the trace; `climbReq_iff`: that is a run of the
    climb.
  `sides j c s`: the two digests under a node on the way up from place j, the one computed so far on
    the left if j is even.
  `runsIn_reqCheck_iff`: the check runs to yes exactly if the path has depthReq digests, the slot's
    number is below 2^depthReq, the leaf query at the slot value with the string behind it is an
    entry of the trace, and the climb from its answer ends in the request root.
  `request_of_yes`: all this from a yes of the part behind the chain, once the chain has joined.
  `extReq_of_yes`: outside the event E_M the slot value is then what the trace determines at the
    slot's leaf under the request root.
    What the trace determines there is the first lam bits of the input of the leaf's query: of the
    string behind the slot value (`π.rsalt`) this says nothing.

Limits: nothing here speaks of the chain, of how the slot value came about, or of a bound.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Hash

noncomputable section

namespace TypedOracleCompiler.Joined
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} {tr : Trace (typedOracleFamily lam K L)}

/-! ## The request tree's check -/

/-- the two digests under a node on the way up from place j: the digest computed so far is the left
one if j is even -/
def sides (j : ℕ) (c s : Dig lam) : Dig lam × Dig lam := if j % 2 = 0 then (c, s) else (s, c)

/-- The queries to the request tree's node oracle that lead from the digest c at place j along the
path to the digest r are entries of the trace. -/
def ClimbReq (tr : Trace (typedOracleFamily lam K L)) : List (Dig lam) → ℕ → Dig lam → Dig lam → Prop
  | [], _, c, r => c = r
  | s :: ss, j, c, r =>
      ∃ u, (⟨OracleName.rnode, (List.ofFn (sides j c s).1, List.ofFn (sides j c s).2), u⟩ :
          QA (typedOracleFamily lam K L)) ∈ tr ∧ ClimbReq tr ss (j / 2) u r

/-- `ClimbReq` is a run of the verifier's climb in the request tree. -/
theorem climbReq_iff : ∀ (path : List (Dig lam)) (j : ℕ) (c r : Dig lam),
    ClimbReq tr path j c r ↔ RunsIn tr (climbM (rnodeV (K := K) (L := L)) path j c) r
  | [], _, c, r => by
      rw [runsIn_climbM_req_iff]
      exact Iff.rfl
  | s :: ss, j, c, r => by
      rw [runsIn_climbM_req_iff]
      show (∃ u, _ ∧ ClimbReq tr ss (j / 2) u r) ↔
        ∃ u, (∃ e ∈ tr, (pairR lam K L).node e = some (sides j c s, u)) ∧
          ClimbsIn (pairR lam K L) tr ss (j / 2) u r
      refine exists_congr fun u => and_congr rnode_recorded_iff.symm ?_
      rw [climbReq_iff ss (j / 2) u r, runsIn_climbM_req_iff]

/-- The check in the request tree runs to yes exactly if the path has depthReq digests, the slot's
number is below 2^depthReq, the leaf query at the slot value c with the string rs behind it is an
entry of the trace, and the climb from its answer along the path ends in the request root. -/
theorem runsIn_reqCheck_iff (depthReq : ℕ) (rtreq : Dig lam) (slot : ℕ) (path : List (Dig lam))
    (c : Dig lam) (rs : Bits) :
    RunsIn tr (reqCheck (K := K) (L := L) depthReq rtreq slot path c rs) true ↔
      path.length = depthReq ∧ slot < 2 ^ depthReq ∧
        ∃ d, (⟨OracleName.rleaf, List.ofFn c ++ rs, d⟩ : QA (typedOracleFamily lam K L)) ∈ tr ∧
          ClimbReq tr path slot d rtreq := by
  unfold reqCheck
  split
  · rename_i hc
    show RunsIn tr ((askTypedOracle (K := K) (L := L) OracleName.rleaf (List.ofFn c ++ rs)).bind fun dg =>
        (climbM rnodeV path slot dg).bind fun r => OComp.pure (decide (r = rtreq))) true ↔ _
    rw [runsIn_bind_iff]
    constructor
    · rintro ⟨d, hd, h2⟩
      obtain ⟨r, hr, h3⟩ := (runsIn_bind_iff _ _ _).1 h2
      obtain rfl : r = rtreq := of_decide_eq_true (runsIn_pure_iff.1 h3)
      exact ⟨hc.1, hc.2, d, runsIn_ask_iff.1 hd, (climbReq_iff path slot d r).2 hr⟩
    · rintro ⟨-, -, d, hd, hr⟩
      exact ⟨d, runsIn_ask_iff.2 hd, (runsIn_bind_iff _ _ _).2
        ⟨rtreq, (climbReq_iff path slot d rtreq).1 hr, runsIn_pure_iff.2 (decide_eq_true rfl)⟩⟩
  · rename_i hc
    constructor
    · intro h
      cases runsIn_pure_iff.1 h
    · rintro ⟨h1, h2, -⟩
      exact absurd ⟨h1, h2⟩ hc

section Slot
variable {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}

/-- The request tree's share: nothing before the chain has joined; afterwards the check at the slot
value. -/
theorem runsIn_reqPart_iff (depthReq : ℕ) (π : OneProtocolProof lam Q) (ph : Phase lam) :
    RunsIn tr (reqPart (K := K) (L := L) depthReq π ph) true ↔
      ∀ c, ph.slotVal = some c →
        RunsIn tr (reqCheck (K := K) (L := L) depthReq π.rtreq π.slot π.path c π.rsalt) true := by
  unfold reqPart
  cases hs : ph.slotVal with
  | none => exact ⟨fun _ _ h => (by cases h), fun _ => runsIn_pure_iff.2 rfl⟩
  | some c => exact ⟨fun h _ e => (by cases e; exact h), fun h => h c rfl⟩

variable (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)
  (ρ : Rho Q.loc.shape) (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam)

/-- The part behind the chain runs to yes exactly if the forests are there and within the limits,
their walks run to yes, the request tree's check runs to yes, and the local verifier accepts the
transcript that is built from the openings. -/
theorem runsIn_afterBO_iff :
    RunsIn tr (checkPrunedOpenings Q wq embS embE depthReq cms x π ρ rts ph) true ↔
      ∃ Fs, forestsOf Q wq embS embE cms x π ρ rts = some Fs ∧
        ((flatF Fs).length ≤ wq.nOpen ∧
          (flatF Fs).all (fun c => c.wellFormed && decide (c.depth ≤ wq.maxDepth)) = true) ∧
        RunsIn tr (runForests (K := K) Fs (readsF Fs)) true ∧
        RunsIn tr (reqPart (K := K) (L := L) depthReq π ph) true ∧
        Q.loc.accept x (wq.ext.build fun p => (π.ext p).map Opening.sym)
          (mkTr Q.loc.shape Q.ann wq.sh rts π.plains ρ π.opens) = true := by
  unfold checkPrunedOpenings
  cases hF : forestsOf Q wq embS embE cms x π ρ rts with
  | none =>
    exact ⟨fun h => (by cases runsIn_pure_iff.1 h), fun ⟨_, h, _⟩ => (by cases h)⟩
  | some Fs =>
    show RunsIn tr (if _ then afterF Q wq depthReq x π ρ rts ph Fs (readsF Fs) else pure false)
      true ↔ _
    split
    · rename_i hc
      unfold afterF
      rw [runsIn_bind_iff]
      constructor
      · rintro ⟨ok, hok, h2⟩
        obtain ⟨okr, hokr, h3⟩ := (runsIn_bind_iff _ _ _).1 h2
        have h5 := Bool.and_eq_true_iff.1 (runsIn_pure_iff.1 h3)
        obtain ⟨rfl, rfl⟩ := Bool.and_eq_true_iff.1 h5.1
        exact ⟨Fs, rfl, hc, hok, hokr, h5.2⟩
      · rintro ⟨Fs', e, -, hok, hokr, hacc⟩
        cases e
        refine ⟨true, hok, (runsIn_bind_iff _ _ _).2 ⟨true, hokr, runsIn_pure_iff.2 ?_⟩⟩
        rw [hacc]
        rfl
    · rename_i hc
      constructor
      · intro h
        cases runsIn_pure_iff.1 h
      · rintro ⟨Fs', e, hc', -⟩
        cases e
        exact absurd hc' hc

variable {wq embS embE depthReq cms x π ρ rts ph}

/-- **The request tree's share of a yes.** If the part behind the chain runs to yes and the chain
has joined with the slot value c, then the request path has depthReq digests, the slot's number is
below 2^depthReq, the leaf query at c with the string `π.rsalt` behind it is an entry of the trace,
and the climb from its answer along the path ends in the request root `π.rtreq`. -/
theorem request_of_yes (h : RunsIn tr (checkPrunedOpenings Q wq embS embE depthReq cms x π ρ rts ph) true)
    {c : Dig lam} (hc : ph.slotVal = some c) :
    π.path.length = depthReq ∧ π.slot < 2 ^ depthReq ∧
      ∃ d, (⟨OracleName.rleaf, List.ofFn c ++ π.rsalt, d⟩ : QA (typedOracleFamily lam K L)) ∈ tr ∧
        ClimbReq tr π.path π.slot d π.rtreq := by
  obtain ⟨_, _, _, _, hr, _⟩ := (runsIn_afterBO_iff wq embS embE depthReq cms x π ρ rts ph).1 h
  exact (runsIn_reqCheck_iff depthReq π.rtreq π.slot π.path c π.rsalt).1
    ((runsIn_reqPart_iff depthReq π ph).1 hr c hc)

/-- Outside E_M the slot value is then what the trace determines at the slot's leaf under the
request root. -/
theorem extReq_of_yes (hM : ¬ EM tr)
    (h : RunsIn tr (checkPrunedOpenings Q wq embS embE depthReq cms x π ρ rts ph) true)
    {c : Dig lam} (hc : ph.slotVal = some c) :
    extReq tr depthReq π.rtreq π.slot = some (List.ofFn c) := by
  obtain ⟨_, _, _, _, hr, _⟩ := (runsIn_afterBO_iff wq embS embE depthReq cms x π ρ rts ph).1 h
  exact (extReq_of_check hM ((runsIn_reqPart_iff depthReq π ph).1 hr c hc)).2

end Slot

end TypedOracleCompiler.Joined
