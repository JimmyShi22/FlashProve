-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/WordTwoStage.lean: two makers over one hash function, the first of which
publishes a root: but for a small probability the word that the first maker's log of strings
determines under that root is the word that both logs determine.

Purpose: the step "what was hashed before a root was published fixes the word under it", free of any
arm: the two makers are arbitrary algorithms on strings, and no verifier runs.
Johnson/TypedOracleCompiler/RecCompile/LinkAnsTwoStage.lean has the step inside the entry file's bound; here it
stands alone, for every object L and every coding m.

Main names. `Merkle.Events.HashEvent.insert`: an event that is no Merkle query, laid into a trace,
does not undo the hash event. `blocks_ann`: the announcing oracle, whose answer holds nothing, is
not one block of the hash function, if lam is not 0. `extEnc_up`: the word off a lifted log is the
word off the one-block entries of the log of strings. `word_two`: one outcome, at a fixed family F.
`word_pr_two`: the bound 2 (tC + tP + 1)² / 2^lam.

How. `EM` (OnBytes/TypedOracleCompiler/Compile/Batch/Events.lean) is the hash event of the four Merkle oracles: the
answer of a new query occurs at an earlier entry. In the analysis alone the root is announced behind
the first stage, by one query to the typed oracle `OracleName.ann`; outside `EM` the word under an announced
root does not change (`extEnc_stable`). THE EXPERIMENT ITSELF HOLDS NO SUCH QUERY: it is counted in
the bound (the + 1) and stands in no log of the statement. The price is `hashEvents`
(OnBytes/TypedOracleCompiler/Compile/Batch/Hash.lean) at the typed algorithm "first maker, announcement, second
maker".

Limits.
- The root in the event is what the first stage puts out, not any root: of a root that the
  second stage makes nothing is said.
- m is any coding, FIXED BEFORE THE FUNCTION IS DRAWN. For a coding that hangs on answers of the
  function: Johnson/TypedOracleCompiler/RecCompile/WordPub.lean.
- The bound says nothing where 2 (tC + tP + 1)² is 2^lam or more. Where it is used lam is 256.
- No committer, no key, no commitment ID, no decoder and no index stand here: nothing on soundness
  (index binding included), opening-form binding, correctness of extraction or no two openings.
- `HashEvent.of_filter` is taken from OnBytes/TypedOracleCompiler/Compile/Batch/HashSingle.lean.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsTwoStage
import OnBytes.TypedOracleCompiler.Compile.Batch.HashSingle

set_option autoImplicit false

noncomputable section

namespace Merkle.Events
variable {E D : Type} {Ev : Merkle.Events E D}

/-- An event that is no Merkle query, laid into a trace, does not undo the hash event. -/
theorem HashEvent.insert {A B : List E} {x : E} (hx : Ev.answer x = none)
    (h : Ev.HashEvent (A ++ B)) : Ev.HashEvent (A ++ x :: B) := by
  obtain ⟨pre, e, post, c, htr, hne, ha, ho⟩ := h
  have hex : e ≠ x := fun hh => by rw [hh, hx] at ha; cases ha
  rcases List.append_eq_append_iff.1 htr with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
  · -- pre = A ++ a', B = a' ++ e :: post
    refine ⟨A ++ x :: a', e, post, c, by rw [h2]; simp, ?_, ha, ho.mono ?_⟩
    · intro hh
      rcases List.mem_append.1 hh with hh | hh
      · exact hne (by rw [h1]; exact List.mem_append_left _ hh)
      · rcases List.mem_cons.1 hh with hh | hh
        · exact hex hh
        · exact hne (by rw [h1]; exact List.mem_append_right _ hh)
    · rw [h1]
      intro y hy
      rcases List.mem_append.1 hy with hy | hy
      · exact List.mem_append_left _ hy
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ hy)
  · -- A = pre ++ c', e :: post = c' ++ B
    cases c' with
    | nil =>
      have hB : B = e :: post := by simpa using h2.symm
      have hA : A = pre := by simpa using h1
      refine ⟨A ++ [x], e, post, c, by rw [hB]; simp, ?_, ha, ho.mono ?_⟩
      · intro hh
        rcases List.mem_append.1 hh with hh | hh
        · exact hne (hA ▸ hh)
        · exact hex (List.mem_singleton.1 hh)
      · rw [hA]
        exact fun y hy => List.mem_append_left _ hy
    | cons d c'' =>
      obtain ⟨e1, e2⟩ := List.cons.inj h2
      subst e1
      exact ⟨pre, e, c'' ++ x :: B, c, by rw [h1]; simp, hne, ha, ho⟩

end Merkle.Events

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L}

/-- The announcing oracle, whose answer holds nothing, is no block of the hash function. -/
theorem blocks_ann (hlam : 0 < lam) (m : OracleCoding (typedOracleFamily lam W.K L) lam) : m.blocks OracleName.ann ≠ 1 := by
  intro hb
  have h := Fintype.card_congr (m.rng OracleName.ann)
  rw [hb] at h
  have h1 : Fintype.card ((typedOracleFamily lam W.K L).Rng OracleName.ann) = 1 := Fintype.card_unit
  rw [h1] at h
  simp only [Fintype.card_pi, Fintype.card_bool, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, pow_one] at h
  have h2 : 2 ≤ 2 ^ lam := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ lam := Nat.pow_le_pow_right (by norm_num) hlam
  omega

/-- The word under a root off a lifted log is the word off the one-block entries of the log of
strings. -/
theorem extEnc_up (hlam : 0 < lam) (m : OracleCoding (typedOracleFamily lam W.K L) lam) (F : Fam (typedOracleFamily lam W.K L))
    (tr : Trace (rom lam)) (hans : ∀ e ∈ tr, e.2.2 = glue m F e.1 e.2.1) (cm : Dig lam) :
    extEnc W (upTr m F tr) cm = extEnc W (singleTr m tr) cm := by
  rw [← extEnc_single W m (Cms.blocks_eq_one hlam m OracleName.leaf (Equiv.refl _))
    (Cms.blocks_eq_one hlam m OracleName.node (Equiv.refl _)) (upTr m F tr), single_upTr,
    Cms.retr_of_ans (glue m F) tr hans]

/-- **One outcome.** -/
theorem word_two (hlam : 0 < lam) (m : OracleCoding (typedOracleFamily lam W.K L) lam) (F : Fam (typedOracleFamily lam W.K L))
    (cm : Dig lam) (trC trP : Trace (rom lam))
    (hans : ∀ e ∈ trC ++ trP, e.2.2 = glue m F e.1 e.2.1)
    (hM : ¬ EM ((upTr m F trC ++ [annE W cm (F OracleName.ann cm)]) ++ upTr m F trP)) :
    ¬ EM (singleTr m (trC ++ trP)) ∧
      extEnc W (singleTr m trC) cm = extEnc W (singleTr m (trC ++ trP)) cm := by
  have hl := Cms.blocks_eq_one hlam m (OracleName.leaf : (typedOracleFamily lam W.K L).ι) (Equiv.refl _)
  have hn := Cms.blocks_eq_one hlam m (OracleName.node : (typedOracleFamily lam W.K L).ι) (Equiv.refl _)
  have hu : upTr m F (trC ++ trP) = upTr m F trC ++ upTr m F trP := List.map_append
  have hansC : ∀ e ∈ trC, e.2.2 = glue m F e.1 e.2.1 := fun e he =>
    hans e (List.mem_append_left _ he)
  constructor
  · intro h
    rw [← Cms.retr_of_ans (glue m F) (trC ++ trP) hans, ← single_upTr] at h
    have h1 : EM (upTr m F (trC ++ trP)) :=
      Merkle.Events.HashEvent.of_filter _ h
    rw [hu] at h1
    refine hM ?_
    rw [List.append_assoc]
    exact Merkle.Events.HashEvent.insert rfl h1
  · have hann : Announced W (upTr m F trC ++ [annE W cm (F OracleName.ann cm)]) cm :=
      List.mem_append_right _ (List.mem_singleton.2 rfl)
    have h1 := extEnc_stable (W := W) hM (List.prefix_append _ _) (occursIn_of_announced hann)
    rw [extEnc_ann] at h1
    have h2 : extEnc W ((upTr m F trC ++ [annE W cm (F OracleName.ann cm)]) ++ upTr m F trP) cm =
        extEnc W (upTr m F (trC ++ trP)) cm := by
      rw [← extEnc_single W m hl hn, ← extEnc_single W m hl hn (upTr m F (trC ++ trP)), hu]
      congr 1
      unfold single
      rw [List.filter_append, List.filter_append, List.filter_append]
      have : [annE W cm (F OracleName.ann cm)].filter (fun e => decide (m.blocks e.1 = 1)) = [] :=
        List.filter_eq_nil_iff.2 fun e he => by
          rw [List.mem_singleton.1 he]
          simpa using blocks_ann hlam m
      rw [this, List.append_nil]
    rw [← extEnc_up hlam m F trC hansC, ← extEnc_up hlam m F (trC ++ trP) hans, h1, h2]

/-- **The bound.** Two makers over one hash function, the first of which publishes a root: but for
probability 2 (tC + tP + 1)² / 2^lam the one-block entries of both logs are outside the hash event,
and the word that the first log determines under the root is the word that both determine. -/
theorem word_pr_two (hlam : 0 < lam) (m : OracleCoding (typedOracleFamily lam W.K L) lam) {St Y : Type}
    (Ct : OComp (rom lam) (Dig lam × St)) (Pt : St → OComp (rom lam) Y) (tC tP : ℕ)
    (hC : Ct.QueryBound tC) (hP : ∀ st, (Pt st).QueryBound tP) :
    Rom.Pr (Ct.withTrace.bind fun a => (Pt a.1.2).withTrace.bind fun b => OComp.pure (a, b))
        (fun _ => {x | EM (singleTr m (x.1.2 ++ x.2.2)) ∨
          extEnc W (singleTr m x.1.2) x.1.1.1 ≠ extEnc W (singleTr m (x.1.2 ++ x.2.2)) x.1.1.1}) ≤
      2 * ((tC + tP + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  have hJ : ((down m Ct).bind fun a =>
      (OComp.ask (S := typedOracleFamily lam W.K L) OracleName.ann a.1).bind fun _ =>
        (down m (Pt a.2)).bind fun _ => OComp.pure ()).QueryBound (tC + tP + 1) := by
    have h : ((down m Ct).bind fun a =>
        (OComp.ask (S := typedOracleFamily lam W.K L) OracleName.ann a.1).bind fun _ =>
          (down m (Pt a.2)).bind fun _ => OComp.pure ()).QueryBound (tC + (1 + (tP + 0))) :=
      (queryBound_down m Ct tC hC).bind fun a =>
        (detBound_ask (S := typedOracleFamily lam W.K L) OracleName.ann a.1).queryBound.bind fun _ =>
          (queryBound_down m (Pt a.2) tP (hP a.2)).bind fun _ => trivial
    exact h.mono (by omega)
  have hE := hashEvents _ _ hJ
  rw [← Pr_eq_law] at hE
  refine le_trans ?_ hE
  rw [Pr_down m]
  refine MeasureTheory.lintegral_mono fun F => ?_
  unfold PrCoins
  rw [runEager_down]
  simp only [Rom.withTrace_bind, OComp.bind_assoc, OComp.ask, OComp.withTrace,
    OComp.bind, OComp.runEager_bind, OComp.runEager, withTrace_down, PMF.bind_map,
    Function.comp_def]
  refine pr_bind_le_bind _ _ _ _ _ fun a ha => pr_bind_le_bind _ _ _ _ _ fun b hb => ?_
  refine pr_pure_le_pure ?_
  intro hbad
  by_contra hnb
  have hM : ¬ EM ((upTr m F a.2 ++ [annE W a.1.1 (F OracleName.ann a.1.1)]) ++ upTr m F b.2) :=
    fun h => hnb (Or.inl (by simpa [annE] using h))
  have hansC := OnBytes.Slice.support_withTrace_ans (glue m F) Ct a ha
  have hansP := OnBytes.Slice.support_withTrace_ans (glue m F) (Pt a.1.2) b hb
  have hans : ∀ e ∈ a.2 ++ b.2, e.2.2 = glue m F e.1 e.2.1 := fun e he =>
    (List.mem_append.1 he).elim (hansC e) (hansP e)
  obtain ⟨h1, h2⟩ := word_two (W := W) hlam m F a.1.1 a.2 b.2 hans hM
  rcases hbad with h | h
  · exact h1 h
  · exact h h2

end TypedOracleCompiler.Compile.Batch

#print axioms Merkle.Events.HashEvent.insert
#print axioms TypedOracleCompiler.Compile.Batch.blocks_ann
#print axioms TypedOracleCompiler.Compile.Batch.extEnc_up
#print axioms TypedOracleCompiler.Compile.Batch.word_two
#print axioms TypedOracleCompiler.Compile.Batch.word_pr_two
