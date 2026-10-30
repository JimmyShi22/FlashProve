-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/LinkAnsStay.lean: two statements in probabilities behind the entry's arm with
the answers alone: the words stay; the words are read off the maker's log of strings.

  `Stays W S tr`    in the trace tr the word under a root is fixed once the root's first seed query
                    is asked: it is the same at every beginning of tr that holds that query and at
                    tr
  `arm_pr_stay`     over the typed oracles, for every maker: but for the bound of `arm_pr`, an arm's
                    yes holds what it promises, and the words stay
  `arm_pr_strings`  `arm_pr_hash` (LinkAnsMore.lean) with the words read off the one-block entries
                    of the maker's log of strings, then the arm's log
  `blocks_eq_one`, `blocks_leaf`, `blocks_node`   a leaf and a node are one block of the hash
                    function under every coding, by counting, if lam is not 0

Limits: those in the heads of LinkAnsPr.lean and LinkAnsOne.lean, and:
  * In this file `arm_pr_stay` is over the typed oracles alone (LinkAnsMaker.lean: `arm_pr_stay_one`
    carries it to one hash function).
  * In `arm_pr_strings` the arm's log is its typed log at `readBlocks m g`, computed inside the
    event. The strings that the arm asks are logged nowhere.
  * Of the maker's log of strings the entries at one-block oracles are read. Its entries at the
    Fiat-Shamir oracles are dropped, whichever block they ask (where K is not 0; a word does not see
    them in any case).
  * In `arm_pr_strings` the words are those at the end of both logs (LinkAnsMaker.lean:
    `arm_pr_maker` reads them off the maker's log alone).

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsMore

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Iop.BatchH4 (ProverLaw VerLaw)
open scoped ENNReal
open OnBytes.Slice

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)}

/-- An oracle whose answers are the strings of lam bits is one block of the hash function under
every coding, if lam is not 0: by counting. -/
theorem blocks_eq_one {Sp : OSpec} (hlam : 0 < lam) (m : OracleCoding Sp lam) (o : Sp.ι)
    (e : Sp.Rng o ≃ (Fin lam → Bool)) : m.blocks o = 1 := by
  have h := Fintype.card_congr (e.symm.trans (m.rng o))
  simp only [Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at h
  have h2 : 2 ≤ 2 ^ lam := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ lam := Nat.pow_le_pow_right (by norm_num) hlam
  have h3 : (2 ^ lam) ^ 1 = (2 ^ lam) ^ m.blocks o := by rw [pow_one]; exact h
  exact (Nat.pow_right_injective h2 h3).symm

/-- A leaf is one block of the hash function under every coding, if lam is not 0. -/
theorem blocks_leaf (hlam : 0 < lam) (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) :
    m.blocks OracleName.leaf = 1 := blocks_eq_one hlam m OracleName.leaf (Equiv.refl _)

/-- A node is one block of the hash function under every coding, if lam is not 0. -/
theorem blocks_node (hlam : 0 < lam) (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam) :
    m.blocks OracleName.node = 1 := blocks_eq_one hlam m OracleName.node (Equiv.refl _)

/-- An event that lies in another on the support has at most its probability. -/
theorem pr_mono_support {α : Type} (μ : PMF α) (E E' : Set α)
    (h : ∀ o ∈ μ.support, o ∈ E → o ∈ E') : pr μ E ≤ pr μ E' := by
  have h1 := pr_le_pr_map μ id E E' h
  rwa [PMF.map_id] at h1

/-- In an outcome of the maker joined with an arm, a yes is a run of the arm in the log. -/
theorem runsIn_joinedA {V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool} {n : ℕ}
    (hV : ∀ z, DetBound (V z) n) (A : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (OutLA lam L aL))
    (f : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))
    (o : (OutLA lam L aL × Bool) × Tc W) (ho : o ∈ ((joinedA W V A).withTrace.runEager f).support)
    (hacc : o.1.2 = true) : RunsIn o.2 (V o.1.1) true := by
  obtain ⟨a, -, b, hb, rfl⟩ := support_withTrace_bind f A _ o ho
  obtain ⟨c, hc, d, hd, rfl⟩ := support_withTrace_bind f _ _ b hb
  have hd' : d = ((a.1, c.1), []) := by
    simpa [OComp.withTrace, OComp.runEager] using hd
  subst hd'
  have hc1 : c.1 = true := hacc
  have hrun : RunsIn c.2 (V a.1) true := by
    have := runsIn_of_mem_support (hV a.1) f c hc
    rwa [hc1] at this
  exact hrun.mono fun e he => List.mem_append_right _ (List.mem_append_left _ he)

/-- The words stay: the word under a root is the same at every beginning of the trace that holds the
root's first seed query and at the whole trace. -/
def Stays (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (tr : Tc W) : Prop :=
  ∀ (tr1 tr2 : Tc W) (cm : Dig lam) (a0 : FsAns lam W.K), tr = tr1 ++ tr2 →
    fbE S.t (seedQ0 W S cm) a0 ∈ tr1 → extEnc W tr1 cm = extEnc W tr cm

/-- An arm is sound against every maker, and the words stay: the event "the arm accepts and what it
promises fails, or the words do not stay", on the trace of the maker and the arm, has probability at
most n εs + 2 (n + 1)² / 2^lam, where n = 5 (t + tVL) and t bounds the maker's queries. The premises
are those of `arm_pr` (LinkAnsPr.lean): Link's soundness round by round (hsL), its locality (hlL),
the annotation's coherence (hcL), `OKLA W`, `AnsOK cA`, `S.Law εs`, the bound on the rounds' errors
(hbL), `IsArm`. -/
theorem arm_pr_stay {V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)}
    {εL : Err L.link.shape} {εs : ℝ≥0∞}
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hcL : aL.Coherent) (hW : OKLA W) (hA : AnsOK cA) (hSd : S.Law εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs) (hV : IsArm W S cA V)
    (A : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (OutLA lam L aL)) (t : ℕ) (hq : A.QueryBound t) :
    Rom.Pr (joinedA W V A).withTrace
        (fun _ => {o | (o.1.2 = true ∧
          ¬ LinkHolds W o.2 o.1.1.1 o.1.1.2.1 o.1.1.2.2.1 o.1.1.2.2.2.1) ∨ ¬ Stays W S o.2}) ≤
      (((t + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  refine le_trans ?_ (badLA_len_rare (cA := cA) (εL := εL) hSd hbL hW.Lk _ _
    (joinedA_queryBound hV hq))
  refine MeasureTheory.lintegral_mono fun f => ?_
  refine pr_mono_support _ _ _ fun o ho hE => ?_
  show BadLA W S cA εL (lenB (preS W S) f o.2)
  by_contra hnb
  rcases hE with ⟨hacc, hbad⟩ | hst
  · exact hbad (arm_lift hsL hlL hcL hW hA hV f (support_withTrace_ans f _ _ ho)
      (runsIn_joinedA hV.det A f o ho hacc) hnb)
  · refine hst fun tr1 tr2 cm a0 htr hm => ?_
    rw [htr] at hnb ⊢
    exact linkA_fixes_len f hnb hm

/-- `arm_pr_hash` with the words read off the maker's log of strings: the maker runs, then the arm,
both asking the one function; the arm accepts, and what it promises fails on the one-block entries
of the maker's log of strings followed by the arm's log, with probability at most
n εs + 2 (n + 1)² / 2^lam, where n = 5 (t + tVL) and t bounds the maker's queries (hq). The premises
are those of `arm_pr` (LinkAnsPr.lean): Link's soundness round by round (hsL), its locality (hlL),
the annotation's coherence (hcL), `OKLA W`, `AnsOK cA`, `S.Law εs`, the bound on the rounds' errors
(hbL), `IsArm`. lam is not 0; m is any coding. -/
theorem arm_pr_strings {V : OutLA lam L aL → TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) Bool}
    {S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL} {cA : L.OutOfDomainAnswer → List (Dig lam)}
    {εL : Err L.link.shape} {εs : ℝ≥0∞}
    (hsL : L.link.Sound
      (fun rr y => L.decodeIndex y.1 rr.1 = none ∨ L.hasCollisionAt y.2 rr.2.1 ∨ L.decodeIndex y.2 rr.2 = L.decodeIndex y.1 rr.1) εL)
    (hlL : L.link.IsLocal) (hcL : aL.Coherent) (hW : OKLA W) (hA : AnsOK cA) (hSd : S.Law εs)
    (hbL : Err.Below (Err.timesShared (2 ^ W.depthReqL) aL εL) εs) (hV : IsArm W S cA V)
    (hlam : 0 < lam) (m : OracleCoding (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) lam)
    (A : OComp (rom lam) (OutLA lam L aL)) (t : ℕ) (hq : A.QueryBound t) :
    Rom.Pr (A.withTrace.bind fun o => ((V o.1).overOne m).bind fun b => OComp.pure (o, b))
        (fun g => {x | x.2 = true ∧
          ¬ LinkHolds W (singleTr m x.1.2 ++ (runA W V (readBlocks m g) x.1.1).2) x.1.1.1 x.1.1.2.1
            x.1.1.2.2.1 x.1.1.2.2.2.1}) ≤
      (((t + tVL W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + tVL W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  refine le_trans ?_ (arm_pr_hash hsL hlL hcL hW hA hSd hbL hV m A t hq)
  refine MeasureTheory.lintegral_mono fun g => ?_
  refine pr_mono_support _ _ _ fun x hx hE => ?_
  have hx' : x.1 ∈ (A.withTrace.runEager g).support := by
    rw [OComp.runEager_bind, PMF.mem_support_bind_iff] at hx
    obtain ⟨o, ho, hx⟩ := hx
    rw [OComp.runEager_bind, PMF.mem_support_bind_iff] at hx
    obtain ⟨b, -, hx⟩ := hx
    have e : x = (o, b) := by simpa [OComp.runEager] using hx
    rw [e]
    exact ho
  exact ⟨hE.1, fun h => hE.2 ((linkHolds_logOne V m (blocks_leaf hlam m) (blocks_node hlam m) g x.1
    (support_withTrace_ans g A x.1 hx') _ _ _ _).1 h)⟩

end TypedOracleCompiler.Compile.Batch.Cms
