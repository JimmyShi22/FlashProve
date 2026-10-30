-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/HonestKeySound.lean: under an honest key no false instance is accepted, with the
round-by-round error charged to the prover's and the verifier's queries alone (a bound on a chance,
under the hypotheses of `Spec.honestSoundBK`): the scheme with batches and the links in the key,
over the compiler's typed oracles, at any wire with `QueryLayout.OKG` (rounds may have proof of work).

This file is about soundness of the compiled argument where the key is made honestly.
Definitions, statements and proofs.

Why: index binding (`epsB`, Compile/Batch/SpecBinding.lean) charges εs to every query of the
committer. At the honest committer's own number of queries (all trees, every try of every search)
that bound is poor. But the proof in Compile/Batch/Sound.lean (`bcsSoundBatchG`) can be taken apart:
its rare event is "a hash event, or a state event of one of three lanes (Test, Link, a session)"; a
lane's state event happens at that lane's own Fiat-Shamir oracle only; the clause on an accepted
session uses the session's lane alone. And in the scheme with the links in the key
(Compile/Batch/StarK.lean) the verifier takes the further encoding's root out of the key. So under
an honest key Test and Link need not be sound: the root is that of a tree that the honest committer
built over an honest encoding of i.

Main names:
  `ZKCP.Gen.honestExp A i Pt`: the experiment: (ivk, isk) ← C(i), the honest committer; (x', π') ←
    Pt(ivk, isk), any prover, handed both keys; b ← V(ivk, x', π'); the outcome is (b, x')
    (`wrongExp`, ZKCP/HonestKey.lean, over a family of oracles).
  `BcsOnlAt W Rno εs`: there is an event Bad on traces: (1) for every algorithm "c, then g" whose
    first part asks no query at the sessions' Fiat-Shamir oracle (`OracleName.fb Tag.onl`,
    Compile/Batch/Oracles.lean), c with at most tc queries and g with at most tg: Pr[Bad] ≤ tg · εs
    + 2 (tc + tg)² / 2^λ; (2) outside Bad there is no collision event E_M; (3) outside Bad an
    accepted session has its instance in the language of what is extracted under its root, or
    nothing decodes under that root.
    In that last case every instance counts as in: the opposite of ZKCP's convention, where the
    language of "none" is empty. `BcsAt` (Compile/Batch/SpecSoundG.lean) has the same disjunct. It
    is harmless for `honestSoundBK`: honest encodings decode.
  `Spec.bcsOnl`: (Snd-B) (`SndBL`) with all errors at most εs; a session's verifier local
    (`InteractiveOracleProof.IsLocal`, Iop/InteractiveOracleProof.lean); the annotation coherent; `W.OKG` ⇒ `BcsOnlAt W Rno εs`.
  `Spec.honest_links`: `W.OKG`; whatever the honest committer can put out on a path whose queries
    are entries of tr, tr without the collision event E_M (`EM`, Compile/Batch/Events.lean) ⇒ under
    every root in the key's list of links the extractor finds an honest encoding of i.
  `Spec.honestSoundBK`: `L.Wired`; `BcsOnlAt W Rno εs`; `W.OKG`; C(i) asks no query at the sessions'
    Fiat-Shamir oracle and at most tC queries; Pt at most tP ⇒
    Pr [ b = 1 ∧ ¬ Rno i x' ] ≤ (tP + tVB W) · εs + 2 (tC + tP + tVB W)² / 2^λ.
    No extractor occurs in the conclusion: the index is the one that went in. Neither (Snd-T) nor
    (Snd-L) is asked.

Limits: the chance is also over the committer's coins: an average over honest keys. The prover puts
out one pair. tC, tP count queries to the typed oracles, a long answer once. That C(i) asks no query
at the sessions' oracle is a premise here; it is a theorem for every wire (a walk of the committer's
program: `honestKey_notOnl`, CompileK/HonestKeyWalkProofs.lean). This file says nothing on a key
that was not made honestly: that is index binding.

Terms: lean/GLOSSARY.md.
-/
import Compile.Batch.Sound
import Compile.Batch.GlueBinding
import Compile.Batch.ExtractionSeed
import Compile.Batch.StarKE
import CompileK.HonestKeyCount

set_option autoImplicit false

noncomputable section

namespace ZKCP.Gen

/-- The experiment with the honest committer and any prover, which is handed both keys: over a
family of oracles. -/
def honestExp {S : Rom.OSpec} {I X W IVK ISK Pf : Type} (A : Arg S I X W IVK ISK Pf) (i : I)
    (Pt : IVK × ISK → Rom.OComp S (X × Pf)) : Rom.OComp S (Bool × X) :=
  (A.C i).bind fun k => (Pt k).bind fun o => (A.V k.1 o.1 o.2).bind fun b => .pure (b, o.1)

end ZKCP.Gen

namespace Compile.Batch
open Iop Rom Prob MeasureTheory Compile.Extr Compile.Batch.Cmpl Compile.Batch.Extr
open Compile.Batch.CompleteUnif (OnlyQ NotFb)
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- What the session's lane gives, for one wire. -/
def BcsOnlAt (W : QueryLayout lam L) (Rno : I → X → Prop) (εs : ℝ≥0∞) : Prop :=
  ∃ Bad : Tc W → Prop,
    (∀ (α β : Type) (c : TypedOracleComputation lam W.K L α) (g : α → TypedOracleComputation lam W.K L β) (tc tg : ℕ), OnlyQ (S := spec lam W.K L) (NotFb Tag.onl) c → c.QueryBound tc → (∀ a, (g a).QueryBound tg) →
      pr (c.bind g).withTrace.law {o | Bad o.2} ≤
        (tg : ℝ≥0∞) * εs + 2 * ((tc + tg : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam) ∧
    (∀ tr, ¬ Bad tr → ¬ EM tr) ∧
    (∀ tr cm x π, ¬ Bad tr → RunsIn tr (vB W cm x π) true →
      L.decodeIndex (extEnc W tr cm) = none ∨ ∃ i, L.decodeIndex (extEnc W tr cm) = some i ∧ Rno i x)

namespace Spec

/-- The session's lane alone. -/
def bcsOnl : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (Rno : I → X → Prop) (εs : ℝ≥0∞),
    (∃ ε,
      Err.Below ε εs ∧
      L.onlineBatch.SndBL L.maxBatchSize L.early L.late
        (fun x y => L.decodeIndex y = none ∨ ∃ i, L.decodeIndex y = some i ∧ Rno i x) ε) →
    L.onlineBatch.loc.IsLocal → L.onlineBatch.ann.Coherent → W.OKG → BcsOnlAt W Rno εs

/-- States, under the hypotheses below: under every root in the honest key's list of links stands an
honest encoding of i. -/
def honest_links : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params), W.OKG →
    ∀ (i : I) (f : Fam (spec lam W.K L)) (tr : Tc W) (k : IVK lam L × ISK lam L), k ∈
        OutsIn f tr (C W WP p i) →
      ¬ EM tr → ∀ e ∈ linksOf (keyOf k.2.1), ∃ r, extEnc W tr e.1 = L.encodeIndex i r

/-- States, under the hypotheses below, the bound below on the chance that a false instance is
accepted under an honest key. -/
def honestSoundBK : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (Rno : I → X → Prop) (εs : ℝ≥0∞),
    L.Wired → BcsOnlAt W Rno εs → W.OKG →
    ∀ (i : I) (tC tP : ℕ) (Pt : IVKK lam L × ISK lam L → TypedOracleComputation lam W.K L (X × PrfK lam L)),
      OnlyQ (S := spec lam W.K L) (NotFb Tag.onl) (C W WP p i) →
      (C W WP p i).QueryBound tC → (∀ k, (Pt k).QueryBound tP) →
      Rom.Pr (ZKCP.Gen.honestExp (argBK W WP p) i Pt) (fun _ => {o | o.1 = true ∧ ¬ Rno i o.2}) ≤ ((tP + tVB W : ℕ) : ℝ≥0∞) * εs + 2 * ((tC + (tP + tVB W) : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam

end Spec

/-! ## The session's lane -/

theorem bcsOnl : Spec.bcsOnl := by
  intro I X lam L W Rno εs hS hlB hco hW
  obtain ⟨εB, hbB, hB0, State, hB1, hB2, hBs, hB3, hB4⟩ := hS
  have oB : (laneB W εB State).OK L.maxBatchSize := laneOf_ok hW.B.sh hB4
  refine ⟨fun tr => (EM tr ∨ EF tr) ∨ StepEvent (laneB W εB State).step tr,
    ?_,
    fun tr h hM => h (Or.inl (Or.inl hM)),
    ?_⟩
  · intro α β c g tc tg hc hqc hqg
    have h := pr_stepEvent_behind
      (S := spec lam W.K L) (laneB W εB State).step εs (NotFb Tag.onl) (fun pre e he hs => hs.1 he)
      (fun pre o q _ => by
        by_cases ho : o = OracleName.fb Tag.onl
        · subst ho
          exact le_trans (pr_mono _ fun r h => h)
            (Lane.pr_step_le (laneB W εB State) hW.slots oB hbB pre q)
        · refine le_trans (le_of_eq (pr_eq_zero_of_forall_not_mem _ ?_)) (zero_le _)
          rintro r - h
          exact ho (Lane.step_oracle h))
      (fun pre o q r hn hs => hn (Lane.step_oracle hs)) c g tg hc hqg
    calc
      pr (c.bind g).withTrace.law {o | (EM o.2 ∨ EF o.2) ∨ StepEvent (laneB W εB State).step o.2} ≤
          pr (c.bind g).withTrace.law {o | EM o.2 ∨ EF o.2} +
            pr (c.bind g).withTrace.law {o | StepEvent (laneB W εB State).step o.2} :=
        pr_union_le _ _ _
      _ ≤ 2 * ((tc + tg : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam + (tg : ℝ≥0∞) * εs :=
        add_le_add (hashEvents (c.bind g) (tc + tg) (hqc.bind hqg)) h
      _ = (tg : ℝ≥0∞) * εs + 2 * ((tc + tg : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := add_comm _ _
  · intro tr cm x π hB hrun
    have hM : ¬ EM tr := fun h => hB (Or.inl (Or.inl h))
    exact mem_of_accepted Tag.onl L.onlineBatch W.B _ id some (fun s => some (.inl s)) hW.B hlB hco
      (Lg := fun x y => L.decodeIndex y = none ∨ ∃ i, L.decodeIndex y = some i ∧ Rno i x) State
      (prjSym Tag.onl) (fun p a => prjSym_emb Tag.onl p a) some (fun _ => rfl) id
      (fun tr cms => extEnc W tr (cms.getD 0 default)) εB hM (fun h => hB (Or.inl (Or.inr h)))
      (fun ⟨pre, e, post, h1, h2⟩ => hB (Or.inr ⟨pre, e, post, h1, h2⟩)) [cm] x π
      (instB L x) (instX_some L x) (fun n hn _ => hB0 n hn)
      (fun y hL => by rw [instB_zero hB0]; exact hB1 y x hL)
      (fun y τ m hL h => by
        rcases instB_step hB0 x τ.idx with h1 | ⟨h1, h2, h3⟩
        · rw [h1] at h; exact hB2 y _ τ m h
        · rw [h2] at h; rw [h3]; exact hB2 y x τ m (hBs y x τ hL h1 h))
      (fun y τ hL h => hB3 y x τ hL (by rw [← instB_last hB0]; exact h)) hrun
      (fun pre q a post htr hocc => extEnc_before htr hM (hocc _ (by simp)))
      (fun p a sl h => by
        rw [hW.extDepth.2.2, (hW.extB p).1, (hW.extB p).2] at h
        exact extEnc_apply hW h)

/-! ## The honest committer's trees -/

section Leaves
variable {W : QueryLayout lam L} (WP : WireBP L) (p : Params) {f : Fam (spec lam W.K L)} {tr : Tc W}

/-- States: under the node's root the extractor finds the node's own encoding of i. -/
def GoodNd (W : QueryLayout lam L) (tr : Tc W) (i : I) (nd : Node lam L) : Prop :=
  extEnc W tr nd.tree.root = L.encodeIndex i nd.r

/-- A postcondition, which does not read the store, for the runs of a program (`eraseR`,
Compile/Batch/RealQ.lean: its ghost names written back), under the oracle functions f, on paths all
of whose queries are entries of tr; from every store. -/
def TriHk (f : Fam (spec lam W.K L)) (tr : Tc W) {α : Type} (c : St lam W.K L α) (Q : α → Prop) :
    Prop :=
  ∀ vs, ∀ o ∈ OutsIn f tr (eraseR c vs), Q o.1

theorem TriHk.bind {α β : Type} {c : St lam W.K L α} {g : α → St lam W.K L β} {Q : α → Prop}
    {Rr : β → Prop} (h : TriHk f tr c Q) (hg : ∀ a, Q a → TriHk f tr (g a) Rr) :
    TriHk f tr (c.bind g) Rr := by
  intro vs o ho
  rw [eraseR_bind] at ho
  obtain ⟨x, hx, hox⟩ := mem_outsIn_bind.1 ho
  exact hg x.1 (h vs x hx) x.2 o hox

theorem triHk_top {α : Type} (c : St lam W.K L α) : TriHk f tr c fun _ => True := fun _ _ _ =>
  trivial

theorem triHk_pure {α : Type} {a : α} {Q : α → Prop} (h : Q a) :
    TriHk f tr (Step.pure a : St lam W.K L α) Q := by
  intro vs o ho
  rw [eraseR_pure] at ho
  obtain rfl : o = (a, vs) := ho
  exact h

theorem triHk_nodeP' (hW : W.OKG) (hEM : ¬ EM tr) (i : I) :
    TriHk f tr (nodeP' W WP p i) (GoodNd W tr i) := by
  intro vs o ho
  rw [eraseR_nodeP'] at ho
  obtain ⟨hok, hin⟩ := triI_nodeP' WP p i vs o ho
  refine extEnc_eqG hW fun q => ?_
  have h3 := extLeaf_of_tree hEM hok hin (j := q.val) (lt_of_lt_of_le q.isLt hW.fits)
  rw [Cmpl.encLeaf_val] at h3
  exact ⟨_, h3⟩

theorem triHk_leavesC (hW : W.OKG) (hEM : ¬ EM tr) (i : I) (root : Node lam L) :
    ∀ n, TriHk f tr (leavesC W WP p i root n) fun ls => ∀ lf ∈ ls, GoodNd W tr i lf.node
  | 0 => triHk_pure (fun _ h => absurd h (List.not_mem_nil))
  | n + 1 =>
    TriHk.bind (triHk_nodeP' WP p hW hEM i) fun nd hnd =>
        TriHk.bind (triHk_top _) fun π _ =>
            TriHk.bind (triHk_leavesC hW hEM i root n) fun rest hr =>
      triHk_pure (fun lf hlf => by
        rcases List.mem_cons.1 hlf with rfl | h
        · exact hnd
        · exact hr lf h)

theorem triHk_Cp (hW : W.OKG) (hEM : ¬ EM tr) (i : I) :
    TriHk f tr (Cp W WP p i) fun o => ∀ lf ∈ o.2.leaves, GoodNd W tr i lf.node :=
  TriHk.bind (triHk_top _) fun root _ =>
    TriHk.bind (triHk_top _) fun _ _ =>
      TriHk.bind (triHk_leavesC WP p hW hEM i root (p.M + 1)) fun _ hls => triHk_pure hls

end Leaves

theorem honest_links : Spec.honest_links := by
  intro I X lam L W WP p hW i f tr k hk hEM e he
  have eC : C W WP p i = (eraseR (Cp W WP p i) []).bind fun o => .pure (o.1.1, (o.1.2, o.2)) :=
    realQ_bind _ _
  rw [eC] at hk
  obtain ⟨o, ho, hko⟩ := mem_outsIn_bind.1 hk
  obtain rfl : k = (o.1.1, (o.1.2, o.2)) := hko
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
  obtain ⟨lf, hlf, rfl⟩ := List.mem_map.1 hx
  exact ⟨lf.node.r, triHk_Cp WP p hW hEM i [] o ho lf hlf⟩

/-! ## The theorem -/

/-- An event on outputs is bounded by an event on traces that it forces. -/
theorem Pr_le_trace {S : OSpec} {α : Type} (c : OComp S α) (E : Set α) (B : Trace S → Prop)
    (h : ∀ f, ∀ o ∈ Outs f c.withTrace, o.1 ∈ E → B o.2) :
    Rom.Pr c (fun _ => E) ≤ pr c.withTrace.law {o | B o.2} := by
  rw [← Pr_eq_law]
  refine lintegral_mono fun f => ?_
  show PrCoins f c E ≤ PrCoins f c.withTrace {o | B o.2}
  unfold PrCoins
  rw [← runEager_withTrace_fst f c, pr_map]
  exact pr_mono_support _ fun o ho hE => h f o ho hE

/-- The deterministic part, under the hypotheses below: outside Bad, what V accepts under an honest
key is true at i. -/
theorem coreH (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (hwd : L.Wired) (hW : W.OKG)
    {Rno : I → X → Prop} {Bad : Tc W → Prop} (hM : ∀ tr, ¬ Bad tr → ¬ EM tr)
    (hO : ∀ tr cm x π, ¬ Bad tr → RunsIn tr (vB W cm x π) true →
      L.decodeIndex (extEnc W tr cm) = none ∨ ∃ i, L.decodeIndex (extEnc W tr cm) = some i ∧ Rno i x)
    (i : I) (f : Fam (spec lam W.K L)) (tr : Tc W) (k : IVK lam L × ISK lam L)
    (hk : k ∈ OutsIn f tr (C W WP p i)) (x : X) (π : PrfK lam L)
    (hrun : RunsIn tr (V W p k.1 x (reK (linksOf (keyOf k.2.1)) (liftK π))) true) (hnb : ¬ Bad tr) :
    Rno i x := by
  unfold reK at hrun
  cases hl : (linksOf (keyOf k.2.1))[(liftK π).leaf]? with
  | none =>
    rw [hl] at hrun
    unfold V at hrun
    cases hT : k.1.piT <;> simp only [hT] at hrun
      <;> exact absurd (runsIn_pure_iff.1 hrun) (by simp)
  | some e =>
    rw [hl] at hrun
    obtain ⟨r, hr⟩ :=
      honest_links I X lam L W WP p hW i f tr k hk (hM tr hnb) e (List.mem_of_getElem? hl)
    unfold V at hrun
    split at hrun
    · rename_i πT πL πB _ _ _
      split_ifs at hrun
      · simp only [bind_eq, pure_eq, runsIn_bind_iff, runsIn_pure_iff] at hrun
        obtain ⟨a, ha, b, hb, c, hc, habc⟩ := hrun
        simp only [Bool.and_eq_true] at habc
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := habc
        obtain ⟨_, _, hc'⟩ := runsIn_verifyB_of_strict hW.B hc
        rcases hO tr e.1 x _ hnb hc' with h | ⟨i', hi', hR⟩
        · rw [hr, hwd.dec_enc] at h
          cases h
        · rw [hr, hwd.dec_enc] at hi'
          cases hi'
          exact hR
      · exact absurd (runsIn_pure_iff.1 hrun) (by simp)
    · exact absurd (runsIn_pure_iff.1 hrun) (by simp)

theorem honestSoundBK : Spec.honestSoundBK := by
  intro I X lam L W WP p Rno εs hwd hB hW i tC tP Pt hOn hC hP
  obtain ⟨Bad, hrare, hM, hO⟩ := hB
  have eE : ZKCP.Gen.honestExp (argBK W WP p) i Pt = (C W WP p i).bind fun k =>
      (Pt ((k.1, linksOf (keyOf k.2.1)), k.2)).bind fun o =>
          (V W p k.1 o.1 (reK (linksOf (keyOf k.2.1)) (liftK o.2))).bind fun b =>
              .pure (b, o.1) := by
    show ((C W WP p i).bind fun o => OComp.pure ((o.1, linksOf (keyOf o.2.1)), o.2)).bind _ = _
    rw [OComp.bind_assoc]
    rfl
  rw [eE]
  refine le_trans (Pr_le_trace _ _ Bad fun f o ho hE => ?_)
    (hrare _ _ (C W WP p i) _ tC (tP + tVB W) hOn hC fun k =>
      ((hP _).bind fun o => ((detBound_V W p k.1 o.1 _).queryBound.bind (t := 0) fun _ => trivial)))
  by_contra hnb
  rw [Compile.withTrace_bind] at ho
  obtain ⟨a, ha, ho⟩ := mem_outs_bind.1 ho
  obtain ⟨b, hb, ho⟩ := mem_outs_bind.1 ho
  obtain rfl := mem_outs_pure.1 ho
  rw [Compile.withTrace_bind] at hb
  obtain ⟨c, hc, hb⟩ := mem_outs_bind.1 hb
  obtain ⟨d, hd, hb⟩ := mem_outs_bind.1 hb
  obtain rfl := mem_outs_pure.1 hb
  rw [Compile.withTrace_bind] at hd
  obtain ⟨e, he, hd⟩ := mem_outs_bind.1 hd
  obtain ⟨g, hg, hd⟩ := mem_outs_bind.1 hd
  obtain rfl := mem_outs_pure.1 hd
  obtain rfl := mem_outs_pure.1 (show g ∈ Outs f (OComp.pure ((e.1, c.1.1), [])) from hg)
  have hrun : RunsIn e.2
      (V W p a.1.1 c.1.1 (reK (linksOf (keyOf a.1.2.1)) (liftK c.1.2))) true := by
    have := runsIn_of_mem_support
      (detBound_V W p a.1.1 c.1.1 (reK (linksOf (keyOf a.1.2.1)) (liftK c.1.2))) f e he
    have h1 : e.1 = true := hE.1
    rwa [h1] at this
  exact hE.2
    (coreH W WP p hwd hW hM hO i f _ a.1
      (OutsIn.mono (List.subset_append_left _ _) (outsIn_of_withTrace ha)) c.1.1 c.1.2
      (hrun.mono fun z hz =>
        List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ hz))) hnb)

end Compile.Batch
