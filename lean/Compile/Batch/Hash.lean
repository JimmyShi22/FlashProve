-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Hash.lean: the hash events are rare; outside them extraction from a trace is stable.

The file proves three groups of lemmas on traces over the typed oracles of
Compile/Batch/Oracles.lean (one random oracle for each kind of query). They are for both kinds of
Merkle trees: those over prover messages and over encodings of the index (`leaf`, `node`; "trees
over oracles" in the comments below), and request trees (`rleaf`, `rnode`; over the slots of a
batch). An algorithm with at most t queries causes one of the hash events `EM`, `EF`
(Compile/Batch/Events.lean; E_M, E_F in the comments below) with probability at most 2 t² / 2^lam
(`hashEvents`). `EM`: the answer of a new Merkle query occurs earlier in the trace; `EF`: the
chaining value of a new query collides with an earlier value (the docstrings there have the
clauses). Extraction is stable: outside `EM`, what is extracted under a digest that occurs in a
prefix of the trace is the same in the whole trace (`extLeaf_stable`, `extReq_stable`,
`extEnc_stable`). Openings agree with extraction: outside `EM`, extraction finds the leaf of every
well-formed check of an opening (`Check.wellFormed`) that succeeds with its queries answered from
the trace (`extLeaf_of_check`, `extReq_of_check`).

The general lemmas are in Hash/MerklePure.lean, Compile/MerkleList.lean, Rom/OneCount.lean,
Compile/HashEvents.lean and Compile/MerkleRom.lean.

The step of reading the leaves of a Merkle tree off the list of an algorithm's random-oracle
queries, without rewinding, is public: Paul Valiant, "Incrementally Verifiable Computation or Proofs
of Knowledge Imply Time/Space Efficiency", TCC 2008 (LNCS 4948, pages 1-18); Eli Ben-Sasson,
Alessandro Chiesa and Nicholas Spooner, "Interactive Oracle Proofs", ePrint 2016/116, state it as a
procedure ("Valiant's extractor"). This library assumes no result of these papers: it proves its own
form of the step.
-/
import Compile.Batch.Events
import Compile.HashEvents
import Compile.MerkleRom

noncomputable section

namespace Compile.Batch
open Iop Rom Prob Merkle
open scoped ENNReal

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-! ## Part 1. The hash events -/

theorem length_toList_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by cases o <;> simp

theorem length_node_occ_le (r : Dig lam) (q : Bits × Bits) :
    (r :: ((digOf (lam := lam) q.1).toList ++ (digOf (lam := lam) q.2).toList)).length ≤ 3 := by
  have h1 := length_toList_le (digOf (lam := lam) q.1)
  have h2 := length_toList_le (digOf (lam := lam) q.2)
  simp only [List.length_cons, List.length_append]
  omega

theorem length_rootFields_le {t : Tag} (q : FbIn lam L t) : (rootFields q).length ≤ 3 := by
  obtain ⟨i, hd, rt, pl⟩ := q
  have h0 := length_toList_le rt
  cases hd with
  | f1 cms x s =>
    have := List.length_take_le 2 cms
    simp only [rootFields, List.length_append]
    omega
  | f2 xl ρ =>
    simp only [rootFields, List.length_append, List.length_nil]
    omega
  | f3 ρ c =>
    simp only [rootFields, List.length_append, List.length_nil]
    omega
  | f4 cms rtreq =>
    have := List.length_take_le 1 cms
    have h2 := length_toList_le (digOf (lam := lam) rtreq)
    simp only [rootFields, List.length_append]
    omega
  | f5 ρ =>
    simp only [rootFields, List.length_append, List.length_nil]
    omega

theorem length_evM_occ_le (e : QA (spec lam K L)) : ((evM lam K L).occ e).length ≤ 3 := by
  obtain ⟨o, q, r⟩ := e
  cases o with
  | leaf => exact (by decide : (1 : ℕ) ≤ 3)
  | node => exact length_node_occ_le _ _
  | rleaf => exact (by decide : (1 : ℕ) ≤ 3)
  | rnode => exact length_node_occ_le _ _
  | fb t => exact length_rootFields_le (show FbIn lam L t from q)
  | g t => exact le_trans (length_toList_le (show JoiningRoundQuery lam L t from q).rt) (by decide)
  | ann => exact (by decide : (1 : ℕ) ≤ 3)
  | other => exact Nat.zero_le _
  | fbw t k => exact Nat.zero_le _

theorem length_evF_occ_le (e : QA (spec lam K L)) : ((evF lam K L).occ e).length ≤ 3 := by
  obtain ⟨o, q, r⟩ := e
  cases o with
  | leaf => exact Nat.zero_le _
  | node => exact Nat.zero_le _
  | rleaf => exact (by decide : (1 : ℕ) ≤ 3)
  | rnode => exact Nat.zero_le _
  | fb t =>
    change (List.ofFn (show (Fin K → Dig lam) × Dig lam from r).2 ::
        chainFields (show FbIn lam L t from q)).length ≤ 3
    unfold chainFields
    cases (show FbIn lam L t from q).head <;> simp
  | g t => exact (by decide : (2 : ℕ) ≤ 3)
  | ann => exact Nat.zero_le _
  | other => exact Nat.zero_le _
  | fbw t k => exact Nat.zero_le _

/-- The step that causes E_M or E_F. -/
def stepMF (pre : Trace (spec lam K L)) (e : QA (spec lam K L)) : Prop :=
  stepOf (evM lam K L) pre e ∨ stepOf (evF lam K L) pre e

theorem EM_or_EF_iff (tr : Trace (spec lam K L)) : EM tr ∨ EF tr ↔ StepEvent stepMF tr := by
  rw [EM, EF, hashEvent_iff_stepEvent, hashEvent_iff_stepEvent]
  exact (stepEvent_or _ _ tr).symm

/-- After a trace of length n, the answer of a new query causes E_M or E_F with probability at most
3 n / 2^λ. -/
theorem pr_stepMF_le (pre : Trace (spec lam K L)) (o : OracleName) (q : domOf lam L o) :
    pr (unif ((spec lam K L).Rng o)) {r | stepMF pre (⟨o, q, r⟩ : QA (spec lam K L))}
      ≤ ((3 * pre.length : ℕ) : ℝ≥0∞) / 2 ^ lam := by
  have hM : ((evM lam K L).occAll pre).length ≤ 3 * pre.length :=
    Merkle.Events.length_occAll_le length_evM_occ_le pre
  have hF : ((evF lam K L).occAll pre).length ≤ 3 * pre.length :=
    Merkle.Events.length_occAll_le length_evF_occ_le pre
  have hdiv : ∀ n : ℕ, n ≤ 3 * pre.length →
      (n : ℝ≥0∞) / Fintype.card (Dig lam) ≤
        ((3 * pre.length : ℕ) : ℝ≥0∞) / 2 ^ lam := fun n hn => by
    rw [card_dig]
    exact ENNReal.div_le_div_right (Nat.cast_le.2 hn) _
  have merkle : ∀ S : Set (Dig lam), (∀ r ∈ S, r ∈ (evM lam K L).occAll pre) →
      pr (unif (Dig lam)) S ≤ ((3 * pre.length : ℕ) : ℝ≥0∞) / 2 ^ lam := fun S hS =>
    le_trans (pr_mono _ hS)
      ((pr_unif_mem_le (C := Dig lam) id Function.injective_id _).trans (hdiv _ hM))
  cases o with
  | leaf =>
    refine merkle _ ?_
    rintro r (⟨-, c, hc, hm⟩ | ⟨-, c, hc, -⟩)
    · cases Option.some.inj hc; exact hm
    · cases hc
  | node =>
    refine merkle _ ?_
    rintro r (⟨-, c, hc, hm⟩ | ⟨-, c, hc, -⟩)
    · cases Option.some.inj hc; exact hm
    · cases hc
  | rleaf =>
    refine merkle _ ?_
    rintro r (⟨-, c, hc, hm⟩ | ⟨-, c, hc, -⟩)
    · cases Option.some.inj hc; exact hm
    · cases hc
  | rnode =>
    refine merkle _ ?_
    rintro r (⟨-, c, hc, hm⟩ | ⟨-, c, hc, -⟩)
    · cases Option.some.inj hc; exact hm
    · cases hc
  | fb t =>
    refine le_trans (pr_mono _ ?_)
      ((pr_unif_snd_mem_le (A := Fin K → Dig lam) (C := Dig lam)
          List.ofFn List.ofFn_injective _).trans (hdiv _ hF))
    rintro r (⟨-, c, hc, -⟩ | ⟨-, c, hc, hm⟩)
    · cases hc
    · cases Option.some.inj hc; exact hm
  | g t =>
    refine le_trans (pr_mono _ ?_)
      ((pr_unif_mem_le (C := Dig lam) List.ofFn List.ofFn_injective _).trans (hdiv _ hF))
    rintro r (⟨-, c, hc, -⟩ | ⟨-, c, hc, hm⟩)
    · cases hc
    · cases Option.some.inj hc; exact hm
  | ann =>
    refine le_trans (le_of_eq (pr_eq_zero_of_forall_not_mem _ ?_)) (zero_le _)
    rintro r - (⟨-, c, hc, -⟩ | ⟨-, c, hc, -⟩)
    · cases hc
    · cases hc
  | other =>
    refine le_trans (le_of_eq (pr_eq_zero_of_forall_not_mem _ ?_)) (zero_le _)
    rintro r - (⟨-, c, hc, -⟩ | ⟨-, c, hc, -⟩)
    · cases hc
    · cases hc
  | fbw t k =>
    refine le_trans (le_of_eq (pr_eq_zero_of_forall_not_mem _ ?_)) (zero_le _)
    rintro r - (⟨-, c, hc, -⟩ | ⟨-, c, hc, -⟩)
    · cases hc
    · cases hc

/-- For an algorithm with at most t queries, one of the two hash events occurs with probability at
most 2 t² / 2^lam. -/
theorem hashEvents {β : Type} (A : TypedOracleComputation lam K L β) (t : ℕ) (hA : A.QueryBound t) :
    pr A.withTrace.law {o | EM o.2 ∨ EF o.2} ≤ 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  have h := pr_stepEvent_le (S := spec lam K L) stepMF (fun n => ((3 * n : ℕ) : ℝ≥0∞) / 2 ^ lam)
    (fun pre e he hs => hs.elim (fun h1 => h1.1 he) (fun h1 => h1.1 he))
    (fun pre o q _ => pr_stepMF_le pre o q) A t hA
  have hset : {o : β × Trace (spec lam K L) | EM o.2 ∨ EF o.2} = {x | StepEvent stepMF x.2} :=
    Set.ext fun x => EM_or_EF_iff x.2
  rw [hset]
  refine h.trans ?_
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum]
  refine mul_le_mul' ?_ le_rfl
  have := three_sum_range_le t
  calc ((∑ v ∈ Finset.range t, 3 * v : ℕ) : ℝ≥0∞) ≤ ((2 * t ^ 2 : ℕ) : ℝ≥0∞) := Nat.cast_le.2 this
    _ = 2 * (t : ℝ≥0∞) ^ 2 := by push_cast; rfl

/-- Neither event is ever undone. -/
theorem EM.append {tr : Trace (spec lam K L)} (h : EM tr) (tr' : Trace (spec lam K L)) :
    EM (tr ++ tr') :=
  Merkle.Events.HashEvent.of_prefix (List.prefix_append tr tr') h

theorem EF.append {tr : Trace (spec lam K L)} (h : EF tr) (tr' : Trace (spec lam K L)) :
    EF (tr ++ tr') :=
  Merkle.Events.HashEvent.of_prefix (List.prefix_append tr tr') h

/-! ## Part 2. Entries of the trace -/

section Views
variable {tr : Trace (spec lam K L)}

theorem nodeView_ofFn (q : Dig lam × Dig lam) (u : Dig lam) :
    nodeView (List.ofFn q.1, List.ofFn q.2) u = some (q, u) := by
  unfold nodeView
  rw [digOf_ofFn, digOf_ofFn]

theorem eq_of_nodeView {q' : Bits × Bits} {r : Dig lam} {q : Dig lam × Dig lam}
    {u : Dig lam} (h : nodeView q' r = some (q, u)) :
    q' = (List.ofFn q.1, List.ofFn q.2) ∧ r = u := by
  obtain ⟨h1, h2, h3⟩ := nodeView_eq_some h
  exact ⟨Prod.ext (eq_ofFn_of_digOf h1) (eq_ofFn_of_digOf h2), h3⟩

theorem node_recorded_iff {q : Dig lam × Dig lam} {u : Dig lam} :
    (∃ e ∈ tr, (pairM lam K L).node e = some (q, u)) ↔
    (⟨OracleName.node, (List.ofFn q.1, List.ofFn q.2), u⟩ : QA (spec lam K L)) ∈ tr := by
  constructor
  · rintro ⟨⟨o, q', r⟩, he, h⟩
    cases o <;> first
      | (obtain ⟨h1, h2⟩ := eq_of_nodeView h
         have h1' : q' = (List.ofFn q.1, List.ofFn q.2) := h1
         have h2' : r = u := h2
         subst h1' h2'
         exact he)
      | cases h
  · intro h; exact ⟨_, h, nodeView_ofFn q u⟩

theorem leaf_recorded_iff {x : LeafIn L} {u : Dig lam} :
    (∃ e ∈ tr, (pairM lam K L).leaf e = some (x, u)) ↔
    (⟨OracleName.leaf, x, u⟩ : QA (spec lam K L)) ∈ tr := by
  constructor
  · rintro ⟨⟨o, q', r⟩, he, h⟩
    cases o <;> first | (cases Option.some.inj h; exact he) | cases h
  · intro h; exact ⟨_, h, rfl⟩

theorem rnode_recorded_iff {q : Dig lam × Dig lam} {u : Dig lam} :
    (∃ e ∈ tr, (pairR lam K L).node e = some (q, u)) ↔
    (⟨OracleName.rnode, (List.ofFn q.1, List.ofFn q.2), u⟩ : QA (spec lam K L)) ∈ tr := by
  constructor
  · rintro ⟨⟨o, q', r⟩, he, h⟩
    cases o <;> first
      | (obtain ⟨h1, h2⟩ := eq_of_nodeView h
         have h1' : q' = (List.ofFn q.1, List.ofFn q.2) := h1
         have h2' : r = u := h2
         subst h1' h2'
         exact he)
      | cases h
  · intro h; exact ⟨_, h, nodeView_ofFn q u⟩

theorem rleaf_recorded_iff {x : Bits} {u : Dig lam} :
    (∃ e ∈ tr, (pairR lam K L).leaf e = some (x, u)) ↔
    (⟨OracleName.rleaf, x, u⟩ : QA (spec lam K L)) ∈ tr := by
  constructor
  · rintro ⟨⟨o, q', r⟩, he, h⟩
    cases o <;> first | (cases Option.some.inj h; exact he) | cases h
  · intro h; exact ⟨_, h, rfl⟩

end Views

/-! ## Part 3. Stability of extraction -/

/-- For trees over oracles: outside E_M, under a digest that occurs in a prefix of the trace,
extraction gives the same in the prefix and in the trace. -/
theorem extLeaf_stable {tr' tr : Trace (spec lam K L)} (h : ¬ EM tr) (hp : tr' <+: tr) {c : Dig lam}
    (ho : (evM lam K L).OccursIn tr' c) (d j : ℕ) : extLeaf tr' d c j = extLeaf tr d c j :=
  (pairM lam K L).preimage_stable h hp (posOf d j) ho

/-- `extLeaf_stable` for request trees. -/
theorem extReq_stable {tr' tr : Trace (spec lam K L)} (h : ¬ EM tr) (hp : tr' <+: tr) {c : Dig lam}
    (ho : (evM lam K L).OccursIn tr' c) (d j : ℕ) : extReq tr' d c j = extReq tr d c j :=
  (pairR lam K L).preimage_stable h hp (posOf d j) ho

/-- Extraction reads Merkle queries only: an entry that is no Merkle query changes nothing. -/
theorem preimage_concat {Y : Type} (V : Merkle.OraclePair (evM lam K L) Y)
    (pre : Trace (spec lam K L)) (e : QA (spec lam K L))
    (hl : V.leaf e = none) (hn : V.node e = none) :
    ∀ {t : Merkle.Shape} (p : t.Pos) (c : Dig lam),
      V.preimage (pre ++ [e]) p c = V.preimage pre p c := by
  have h1 : ∀ c, firstPre V.leaf (pre ++ [e]) c = firstPre V.leaf pre c := fun c => by
    rw [firstPre_append]
    have : firstPre V.leaf [e] c = none := firstPre_eq_none_iff.2 fun e' he' q hq => by
      rw [List.mem_singleton.1 he', hl] at hq
      cases hq
    rw [this, Option.or_none]
  have h2 : ∀ c, firstPre V.node (pre ++ [e]) c = firstPre V.node pre c := fun c => by
    rw [firstPre_append]
    have : firstPre V.node [e] c = none := firstPre_eq_none_iff.2 fun e' he' q hq => by
      rw [List.mem_singleton.1 he', hn] at hq
      cases hq
    rw [this, Option.or_none]
  intro t p
  induction p with
  | here => exact h1
  | left p ih =>
      intro c
      simp only [OraclePair.preimage, h2, ih]
  | right p ih =>
      intro c
      simp only [OraclePair.preimage, h2, ih]

/-- An announced digest occurs. -/
theorem occursIn_of_announced {W : QueryLayout lam L} {tr : Tc W} {cm : Dig lam} (h : Announced W tr cm) :
    (evM lam W.K L).OccursIn tr cm :=
  ⟨_, h, List.mem_cons_self⟩

/-- `extLeaf_stable` for the string under the root of an encoded index. -/
theorem extEnc_stable {W : QueryLayout lam L} {tr' tr : Tc W} {cm : Dig lam} (h : ¬ EM tr)
    (hp : tr' <+: tr) (ho : (evM lam W.K L).OccursIn tr' cm) :
    extEnc W tr' cm = extEnc W tr cm := by
  unfold extEnc
  congr 1
  funext q
  rw [extLeaf_stable h hp ho]

/-! ## Part 4. Openings and extraction -/

theorem runsIn_climbM_iff {tr : Trace (spec lam K L)} :
    ∀ (path : List (Dig lam)) (j : ℕ) (c r : Dig lam),
      RunsIn tr (climbM (hashTreeNode (K := K) (L := L)) path j c) r ↔
      ClimbsIn (pairM lam K L) tr path j c r
  | [], _, c, r => by
      simp only [climbM, pure_eq, runsIn_pure_iff, ClimbsIn]
  | s :: ss, j, c, r => by
      by_cases hb : j % 2 = 0
      · have e : climbM (hashTreeNode (K := K) (L := L)) (s :: ss) j c
            = (hashTreeNode c s).bind fun u => climbM hashTreeNode ss (j / 2) u := by
          simp only [climbM, if_pos hb]; rfl
        rw [e, runsIn_bind_iff]
        simp only [ClimbsIn, if_pos hb, node_recorded_iff, runsIn_climbM_iff ss]
        exact exists_congr fun u => and_congr_left fun _ => runsIn_ask_iff
      · have e : climbM (hashTreeNode (K := K) (L := L)) (s :: ss) j c
            = (hashTreeNode s c).bind fun u => climbM hashTreeNode ss (j / 2) u := by
          simp only [climbM, if_neg hb]; rfl
        rw [e, runsIn_bind_iff]
        simp only [ClimbsIn, if_neg hb, node_recorded_iff, runsIn_climbM_iff ss]
        exact exists_congr fun u => and_congr_left fun _ => runsIn_ask_iff

theorem runsIn_climbM_req_iff {tr : Trace (spec lam K L)} :
    ∀ (path : List (Dig lam)) (j : ℕ) (c r : Dig lam),
      RunsIn tr (climbM (rnodeV (K := K) (L := L)) path j c) r ↔
      ClimbsIn (pairR lam K L) tr path j c r
  | [], _, c, r => by
      simp only [climbM, pure_eq, runsIn_pure_iff, ClimbsIn]
  | s :: ss, j, c, r => by
      by_cases hb : j % 2 = 0
      · have e : climbM (rnodeV (K := K) (L := L)) (s :: ss) j c
            = (rnodeV c s).bind fun u => climbM rnodeV ss (j / 2) u := by
          simp only [climbM, if_pos hb]; rfl
        rw [e, runsIn_bind_iff]
        simp only [ClimbsIn, if_pos hb, rnode_recorded_iff, runsIn_climbM_req_iff ss]
        exact exists_congr fun u => and_congr_left fun _ => runsIn_ask_iff
      · have e : climbM (rnodeV (K := K) (L := L)) (s :: ss) j c
            = (rnodeV s c).bind fun u => climbM rnodeV ss (j / 2) u := by
          simp only [climbM, if_neg hb]; rfl
        rw [e, runsIn_bind_iff]
        simp only [ClimbsIn, if_neg hb, rnode_recorded_iff, runsIn_climbM_req_iff ss]
        exact exists_congr fun u => and_congr_left fun _ => runsIn_ask_iff

/-- For a tree over oracles: outside E_M, if a well-formed check succeeds within the trace,
extraction finds its leaf input. -/
theorem extLeaf_of_check {tr : Trace (spec lam K L)} (c : Check lam L) (h : ¬ EM tr)
    (hw : c.wellFormed = true) (hr : RunsIn tr (runCheck (K := K) c) true) :
    extLeaf tr c.depth c.root c.j = some c.inp := by
  have hl : c.path.length = c.depth := by
    simp only [Check.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hw
    exact hw.1
  have h' : RunsIn tr ((askTypedOracle (K := K) (L := L) OracleName.leaf c.inp).bind fun d =>
      (climbM hashTreeNode c.path c.j d).bind fun r => OComp.pure (decide (r = c.root))) true := hr
  obtain ⟨d, hd, h2⟩ := (runsIn_bind_iff _ _ _).1 h'
  obtain ⟨r, hr', h3⟩ := (runsIn_bind_iff _ _ _).1 h2
  have hd' : (⟨OracleName.leaf, c.inp, d⟩ : QA (spec lam K L)) ∈ tr := runsIn_ask_iff.1 hd
  have hrt : r = c.root := of_decide_eq_true (runsIn_pure_iff.1 h3)
  refine (pairM lam K L).preimage_of_opensIn h ?_
  rw [← hrt]
  exact opensIn_of_climbsIn (pairM lam K L) (leaf_recorded_iff.2 hd') c.depth c.path r hl
    ((runsIn_climbM_iff c.path c.j d r).1 hr')

/-- For the request tree: outside E_M, if the check succeeds within the trace, the slot number is
below 2^d and extraction finds the slot value there. -/
theorem extReq_of_check {tr : Trace (spec lam K L)} (h : ¬ EM tr) {d : ℕ} {rtreq : Dig lam}
    {slot : ℕ} {path : List (Dig lam)} {c : Dig lam}
    (hr : RunsIn tr (reqCheck (K := K) (L := L) d rtreq slot path c) true) :
    slot < 2 ^ d ∧ extReq tr d rtreq slot = some (List.ofFn c) := by
  unfold reqCheck at hr
  split at hr
  · rename_i hc
    have h' : RunsIn tr ((askTypedOracle (K := K) (L := L) OracleName.rleaf (List.ofFn c)).bind fun dg =>
        (climbM rnodeV path slot dg).bind fun r => OComp.pure (decide (r = rtreq))) true := hr
    obtain ⟨dg, hd, h2⟩ := (runsIn_bind_iff _ _ _).1 h'
    obtain ⟨r, hr', h3⟩ := (runsIn_bind_iff _ _ _).1 h2
    have hd' : (⟨OracleName.rleaf, List.ofFn c, dg⟩ : QA (spec lam K L)) ∈ tr := runsIn_ask_iff.1 hd
    have hrt : r = rtreq := of_decide_eq_true (runsIn_pure_iff.1 h3)
    refine ⟨hc.2, (pairR lam K L).preimage_of_opensIn h ?_⟩
    rw [← hrt]
    exact opensIn_of_climbsIn (pairR lam K L) (rleaf_recorded_iff.2 hd') d path r hc.1
      ((runsIn_climbM_req_iff path slot dg r).1 hr')
  · cases runsIn_pure_iff.1 hr

/-- What extraction finds in a request tree is the input of a query to `rleaf` in the trace. -/
theorem rleaf_mem_of_extReq {tr : Trace (spec lam K L)} {d : ℕ} {rtreq : Dig lam} {c : Bits}
    {j : ℕ} (h : extReq tr d rtreq j = some c) :
    ∃ u, (⟨OracleName.rleaf, c, u⟩ : QA (spec lam K L)) ∈ tr := by
  have h1 := (pairR lam K L).preimage_eq_bind_leafLabel tr (posOf d j) rtreq
  rw [show (pairR lam K L).preimage tr (posOf d j) rtreq = some c from h] at h1
  obtain ⟨u, -, hu⟩ := Option.bind_eq_some_iff.1 h1.symm
  obtain ⟨e, he, hq⟩ := exists_of_firstPre hu
  exact ⟨u, rleaf_recorded_iff.1 ⟨e, he, hq⟩⟩

end Compile.Batch
