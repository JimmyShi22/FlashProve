-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/LinkOnly.lean: the entry's arm alone: the seeds of two tables and the
compiled Link, with its soundness as a statement of its own.

`VL` is the part of the compiled verifier with records (`VC`, Cms.lean of this folder) that reads an
entry: it recomputes the seeds of the first and of a further table, runs the compiled Link on the
two roots and the two records, and forms the conjunction. No Test, no session.

  `OKL W S`: what is asked of the wires: the laws of Link's own wire, of the record's wire, and the
    few lines of `QueryLayout.OKG` that Link's clause reads. Nothing on the rounds of Test or of the
    session.
  `BadL W S εL`: a set of traces: a hash event (E_M, E_F), the event of Link's lane, or the seed's.
  `badL_rare`: an algorithm with at most t queries ends in it with probability at most t εs + 2 (t +
    1)² / 2^lam.
  `badL_mono`: it is never undone.
  `link_sound`: outside it, if `VL` accepts with its queries answered from the trace: neither seed
    is a collision seed of the word that the trace determines under its root, and the further table
    decodes to what the first decodes to, unless the first decodes to nothing.
  `detBound_VL`: a bound on its queries; it draws no coin.

The proof is that of `cms_bcs` (CmsBcs.lean), with an idle lane in the place of Test's and of the
session's.

Limits: soundness alone; typed oracles. The file has two halves at the level of traces (`badL_rare`,
`link_sound`) and no statement in probabilities that joins them. LinkAnsPr.lean of this folder has
one (`linkA_pr`), for the arm with the answers alone in the first query, at five times the number of
queries. That the first table decodes to something is Test's clause, not this file's.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.CmsGlue

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal

/-- A determined leaf under one of a link's two roots gives the symbol of the extracted string:
`agreeLk` (Bcs.lean) from the four lines of `QueryLayout.OKG` that its proof reads. -/
theorem agreeLkL {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L} (hext : W.B.ext.OK)
    (hprj : ∀ s, W.prjE (W.embE s) = some s) (hd : W.Lk.ext.depth = W.depth)
    (hL : (∀ p, W.Lk.ext.which (.inl p) = 0 ∧ W.Lk.ext.leaf (.inl p) = p.val) ∧
      ∀ p, W.Lk.ext.which (.inr p) = 1 ∧ W.Lk.ext.leaf (.inr p) = p.val) {tr : Tc W}
    {cm cm' : Dig lam} (rest : List (Dig lam)) (p : (twoExternalStrings L.wordLength L.Symbol).Pos)
    (a : (twoExternalStrings L.wordLength L.Symbol).Sym) (sl : Bits)
    (h : extLeaf tr W.Lk.ext.depth ((cm :: cm' :: rest).getD (W.Lk.ext.which p) default)
        (W.Lk.ext.leaf p) = some ⟨W.embE a, sl⟩) :
    (twoExternalStrings L.wordLength L.Symbol).rd (extEnc W tr cm, extEnc W tr cm') p = a := by
  have ap : ∀ {c : Dig lam} {q : Fin L.wordLength} {b : L.Symbol},
      extLeaf tr W.depth c q.val = some ⟨W.embE b, sl⟩ → extEnc W tr c q = b := fun {c q b} h' =>
    hext.build_rd _ q b (by rw [h']; exact hprj b)
  rw [hd] at h
  cases p with
  | inl p =>
    rw [(hL.1 p).1, (hL.1 p).2] at h
    exact ap h
  | inr p =>
    rw [(hL.2 p).1, (hL.2 p).2] at h
    exact ap h

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)

/-- The entry's arm of the verifier: the two seeds, the compiled Link, then the conjunction. -/
def VL (p : Params) (cm cm' : Dig lam) (rec rec' : L.Rec) (π : OneProtocolProof lam (batLC L aL)) :
    TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool :=
  (outOfDomainSeedIs W S cm rec.1).bind fun s0 =>
  (outOfDomainSeedIs W S cm' rec'.1).bind fun s1 =>
  (vLC W S p cm cm' rec rec' π).bind fun b =>
  OComp.pure (s0 && s1 && b)

/-- What the entry's arm asks of the wires. -/
structure OKL : Prop where
  /-- the laws of Link's wire -/
  Lk : (wLC W).OKG
  /-- the laws of the record's wire -/
  seed : S.OK
  /-- the wire by which the word under a root is built -/
  ext : W.B.ext.OK
  prjE_emb : ∀ s, W.prjE (W.embE s) = some s
  prjL_emb : ∀ p a, W.prjL p (W.embL p a) = some a
  extDepth : W.Lk.ext.depth = W.depth
  extL : (∀ p, W.Lk.ext.which (.inl p) = 0 ∧ W.Lk.ext.leaf (.inl p) = p.val) ∧
    ∀ p, W.Lk.ext.which (.inr p) = 1 ∧ W.Lk.ext.leaf (.inr p) = p.val

/-- The wires of the whole verifier have what the entry's arm asks. -/
theorem OKC.toL {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
    (h : OKC W S) : OKL W S :=
  ⟨h.Lk, h.seed, h.base.B.ext, h.base.prjE_emb, h.base.prjL_emb, h.base.extDepth.2.1, h.base.extL⟩

/-- An idle lane: no round, no state. It has no event. -/
def laneNil (t : Tag) : Lane W where
  t := t
  s := []
  A := PUnit.unit
  ws := ()
  prjS := fun p => nomatch p
  prjP := fun _ => none
  ε := ()
  state := fun _ _ _ => none

theorem laneNil_ok (t : Tag) (N : ℕ) : (laneNil W t).OK N :=
  ⟨trivial, fun _ _ xs => by
    refine cast (congrArg (JointLaw N [] PUnit.unit ()) ?_)
      (Iop.BatchOne.jointLaw_none N [] PUnit.unit ())
    funext j
    cases xs j <;> rfl⟩

/-- The set of traces outside which the entry's arm is sound. -/
def BadL (εL : Err L.link.shape) (tr : Tc W) : Prop :=
  (EM tr ∨ EF tr) ∨ StepEvent (fun pre e =>
    stepS W (laneNil W Tag.test) (laneLC W S εL) (laneNil W Tag.onl) pre e ∨ stepSeed W S pre e) tr

variable {W S}

theorem badL_mono {εL : Err L.link.shape} {tr : Tc W} (tr' : Tc W) (h : BadL W S εL tr) :
    BadL W S εL (tr ++ tr') := by
  rcases h with (h | h) | h
  · exact Or.inl (Or.inl (h.append tr'))
  · exact Or.inl (Or.inr (h.append tr'))
  · exact Or.inr (StepEvent.append h tr')

theorem badL_rare {εL : Err L.link.shape} {εs : ℝ≥0∞} (hSd : S.Law εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs) (hW : OKL W S) {β : Type}
    (A : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) β) (t : ℕ) (hA : A.QueryBound t) :
    pr A.withTrace.law {o | BadL W S εL o.2} ≤
      (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  have oL : (laneLC W S εL).OK (2 ^ W.depthReqL) :=
    laneOfC_ok hW.Lk.sh fun y _ _ => stOf_jointA L.link aL εL (2 ^ W.depthReqL) y _
  have h := pr_stepEvent_le (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL))
    (fun pre e =>
      stepS W (laneNil W Tag.test) (laneLC W S εL) (laneNil W Tag.onl) pre e ∨ stepSeed W S pre e)
    (fun _ => εs)
    (fun pre e he hs => hs.elim
      (fun hs => hs.elim (fun h1 => h1.1 he) fun h1 =>
        h1.elim (fun h2 => h2.1 he) fun h2 => h2.1 he)
      fun h1 => h1.1 he)
    (fun pre o q _ => pr_step4_le W S rfl rfl rfl rfl rfl rfl (laneNil_ok W Tag.test _) oL
      (laneNil_ok W Tag.onl _) trivial hbL trivial hSd pre o q) A t hA
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  calc
    pr A.withTrace.law {o | BadL W S εL o.2} ≤
        pr A.withTrace.law {o | EM o.2 ∨ EF o.2} +
          pr A.withTrace.law
            {o | StepEvent (fun pre e =>
              stepS W (laneNil W Tag.test) (laneLC W S εL) (laneNil W Tag.onl) pre e ∨
                stepSeed W S pre e) o.2} :=
      pr_union_le _ _ _
    _ ≤ 2 * (t : ℝ≥0∞) ^ 2 / 2 ^ lam + (t : ℝ≥0∞) * εs := add_le_add (hashEvents A t hA) h
    _ ≤ (t : ℝ≥0∞) * εs + 2 * ((t + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
        rw [add_comm]
        gcongr
        exact Nat.le_succ t

/-- The entry's arm is sound. This is said under the hypotheses that stand in the statement itself,
which this comment does not list; it is no claim that they hold. -/
theorem link_sound {εL : Err L.link.shape}
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hcL : aL.Coherent) (hW : OKL W S) (p : Params) {tr : Tc W}
    {cm cm' : Dig lam} {rec rec' : L.Rec} {π : OneProtocolProof lam (batLC L aL)} (hB : ¬ BadL W S εL tr)
    (hrun : RunsIn tr (VL W S p cm cm' rec rec' π) true) :
    ¬ L.hasCollisionAt (extEnc W tr cm) rec.1 ∧ ¬ L.hasCollisionAt (extEnc W tr cm') rec'.1 ∧
      (L.decodeIndex (extEnc W tr cm) rec = none ∨
        L.decodeIndex (extEnc W tr cm') rec' = L.decodeIndex (extEnc W tr cm) rec) := by
  have hM : ¬ EM tr := fun h => hB (Or.inl (Or.inl h))
  have hF : ¬ EF tr := fun h => hB (Or.inl (Or.inr h))
  unfold VL at hrun
  simp only [runsIn_bind_iff, runsIn_pure_iff] at hrun
  obtain ⟨s0, hs0, s1, hs1, b, hb, habc⟩ := hrun
  simp only [Bool.and_eq_true] at habc
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := habc
  have hc0 : ¬ L.hasCollisionAt (extEnc W tr cm) rec.1 := seed_not_coll' hM hF (fun h => hB (Or.inr h)) hs0
  have hc1 : ¬ L.hasCollisionAt (extEnc W tr cm') rec'.1 := seed_not_coll' hM hF (fun h => hB (Or.inr h)) hs1
  obtain ⟨_, _, hb'⟩ := runsIn_verifyB_of_strict hW.Lk hb
  refine ⟨hc0, hc1, ?_⟩
  have key : L.decodeIndex (extEnc W tr cm) rec = none ∨ L.hasCollisionAt (extEnc W tr cm') rec'.1 ∨
      L.decodeIndex (extEnc W tr cm') rec' = L.decodeIndex (extEnc W tr cm) rec :=
    mem_of_acceptedC Tag.link (batLC L aL) (wLC W) _ id (fun _ => none)
      W.embE hW.Lk hlL hcL
      (Lg := fun rr y =>
        L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1)
      (stOf L.link εL) W.prjL hW.prjL_emb some (fun _ => rfl) (xoutLC W S)
      (fun tr cms => (extEnc W tr (cms.getD 0 default), extEnc W tr (cms.getD 1 default)))
      (Err.timesShared (2 ^ W.depthReqL) aL εL) hM hF
      (fun ⟨pre, e, post, h1, h2⟩ =>
        hB (Or.inr ⟨pre, e, post, h1, Or.inl (Or.inr (Or.inl h2))⟩))
      (cmsL W S cm cm' rec rec') (rec, rec') _
      (fun _ => (rec, rec')) (fun _ => xoutLC_cmsL W S hW.seed cm cm' rec rec' _)
      (fun _ _ h => absurd rfl h)
      (fun y hL => stOf_start hsL y (rec, rec') hL)
      (fun y τ m _ h => stOf_prover y (rec, rec') τ m h)
      (fun y τ _ h => stOf_full y (rec, rec') τ h) hb'
      (fun pre q a post htr hocc =>
        Prod.ext (extEnc_before htr hM (hocc _ (by simp [cmsL])))
          (extEnc_before htr hM (hocc _ (by simp [cmsL]))))
      (fun p a sl h => agreeLkL hW.ext hW.prjE_emb hW.extDepth hW.extL _ p a sl h)
  exact key.imp_right fun h => h.resolve_left hc1

variable (W S)

/-- a bound on the number of queries of the entry's arm -/
def tVL : ℕ := 4 + tVQB (wLC W) W.depthReqL

theorem detBound_VL (p : Params) (cm cm' : Dig lam) (rec rec' : L.Rec)
    (π : OneProtocolProof lam (batLC L aL)) : DetBound (VL W S p cm cm' rec rec' π) (tVL W) := by
  unfold VL tVL
  refine ((detBound_seedIs W S _ _).bind (t := 2 + (tVQB (wLC W) W.depthReqL + 0)) fun _ =>
    (detBound_seedIs W S _ _).bind (t := tVQB (wLC W) W.depthReqL + 0) fun _ =>
      (detBound_verifyBS _ _ _ _ _ _ _ _ _ _ _ _ _).bind (t := 0) fun _ =>
        detBound_pure _ _).mono ?_
  omega

end TypedOracleCompiler.Compile.Batch.Cms
