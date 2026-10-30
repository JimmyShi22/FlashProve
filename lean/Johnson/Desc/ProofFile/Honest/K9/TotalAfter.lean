-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TotalAfter.lean: FOR THE ITEM "totalB": THE RUNS BEHIND THE BATCHING RETURN; THE
FOURTH CONJUNCT; AND THE TWO JOINS. Statements and proofs ON THE VERIFIER's TEXT and on the
named sentences of Honest/K9/TotalFront.lean; no goal is stated.
  `afterIn_step`   one step of the frame's fold of the runs behind the batching, at a run that returns (the library has
      the way back, from a yes of the fold to its pieces: `afterIn_cons`, Johnson/Desc/First/TailClaims/K8SitsLink.lean)
  `lsTail_returns`   where K9's lens reads a part: the law's text of the first run behind returns; the state behind
      has the reply, the ledger and the tail's slice laid (`LsLaid`)
  `tests_reply`     the law's text of the last run behind leaves the reply
  `tables_of_counts`   the counts but the first hold "the tables are held": so the tables are there
  **`rw_front`**      the item's fourth conjunct at s' from `K9L.rowsFit` at what is fixed at s and the three numbers'
      ride
**`join_plain`**    `JoinPlain` (Honest/K9/TotalFront.lean) HOLDS: at every thread, link and letters: from
`SeatedFree`, `SealLaw`, the sentences on the state in front (`FrontShares`), the two halves of the converse of the
library's ties at the two runs behind, and `K8Behind`: the item's four conjuncts at every stand, where the letter test
says nothing
`freeSlot_leaves`, **`join_layers`**   `JoinLayers` HOLDS: the like at a feed-forward segment, where that kind's own
run stands between the two: it leaves the reply, the ledger and the smallness test's state (the library's
`k4_freeSlot_wrote`)
THREE PREMISES OF EACH JOIN ARE PINS, WHICH THE PROOFS DO NOT SPEND: that the two runs rLs, rTs are what the
approximate range proof's own block lists under the two names, at the link's lengths nU: they stand in the statements
so that `KindOver` and `SeatOver` speak of one run.
No member; the two joins are called by no line.
WHAT IS NOT CLAIMED. Any of the named sentences, `SealLaw` or `SeatedFree` at any thread or link. Nothing on any
property.

-/
import Johnson.Desc.ProofFile.Honest.K9.TotalBehind
import Johnson.Desc.First.Batch.Law.ShutYes
import Johnson.Desc.First.Link.Law.K4Quiet
import Johnson.Desc.First.StateOut
import Johnson.Desc.First.StateLedger
import Johnson.Desc.First.TailClaims.EquationsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

/-- One step of the fold of the runs behind the batching. -/
theorem afterIn_step (bs : List (Block S Claim)) (o : ℕ × String) (l : List (ℕ × String)) (e e' : S)
    (run : S → Except String S) (hl : ((bs[o.1]?).bind fun b => b.after.lookup o.2) = some run)
    (hr : run e = .ok e') : afterIn bs (o :: l) e = afterIn bs l e' := by
  rw [JoinAtBlocks.afterIn_eq, JoinAtBlocks.afterIn_eq, List.foldl_cons]
  congr 1
  simp [JoinAtBlocks.stepA, Except.bind, hl, named, hr]

/-- The law's text of the first run behind returns wherever K9's lens reads a part. -/
theorem lsTail_returns (e : S) (a : Desc.K9.Part) (ha : Desc.K9.atS.get? e = some a) :
    ∃ z, K9L.k8LsTail e = .ok z ∧ ProofFile.sameReply e z = true ∧ z.fork? = e.fork? ∧ LsLaid e z := by
  obtain ⟨hf, tl, htl⟩ := get_parts e a ha
  refine ⟨e.putTl { tl with lsTail := a.F.LS.extract tl.slotA tl.slotB }, ?_, ?_, S.fork_putTl e _,
    a.F, tl, hf, htl, TailClaims.Law.tl_putTl e tl _ htl⟩
  · unfold K9L.k8LsTail
    rw [hf, htl]
    rfl
  · unfold ProofFile.sameReply
    rw [S.out_putTl]
    exact beq_self_eq_true _

/-- The law's text of the last run behind leaves the reply. -/
theorem tests_reply (nU : Array ℕ) (e t : S) (h : K9L.k8Tests nU e = .ok t) : ProofFile.sameReply e t = true := by
  obtain ⟨F, tl, g, _, _, _, _, _, rfl⟩ := K9L.k8Tests_ok nU e t h
  unfold ProofFile.sameReply
  rw [S.out_putFork, S.out_putTl]
  exact beq_self_eq_true _

/-- Among the counts but the first stands "the tables are held": so the tables are there. -/
theorem tables_of_counts (w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere) (s : S)
    (hc : ((Desc.K9.countsAt w.1 w.2.1).tail.all fun q => q.2 s) = true) : (S.funs? s).isSome = true := by
  have hT : Desc.K9.tablesHeld s = true := by
    obtain ⟨q, n, x⟩ := w
    cases q <;> simp only [Desc.K9.countsAt, List.tail_cons, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true] at hc
    · exact hc
    · exact hc
    · exact hc.2.2
  cases hf : s.funs? with
  | some f => rfl
  | none =>
    cases ht : s.tl? <;> simp [Desc.K9.tablesHeld, hf, ht] at hT

section
variable {α : Type} {sub : First.ModelPart} {l : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where} {φ : S → α}
  {Ok : α × Option K9L.Pub9 → Prop} {nU : Array ℕ} {u : HTailF2}
  {π : α → Option HTailF2 × Option (Array HFun)}
  {tmOf : ℕ × String → ℕ → α × Option K9L.Pub9 → K9L.Bound Cb.Gl.E → List (ℕ × Cb.Gl.E)}
  {lenOf : ℕ × String → α × Option K9L.Pub9 → ℕ}

/-- **The item's fourth conjunct at s', from what is fixed at s.** a: K9's part at s. -/
theorem rw_front (A : SealLaw sub l Lk p φ Ok nU u π tmOf lenOf) (s s' : S) (a : Desc.K9.Part)
    (ha : Desc.K9.atS.get? s = some a) (hnum : K9L.numOf u s' = K9L.numOf u s)
    (hW : K9L.rowsFit p.rows π (K9L.fixed9 φ s)) : Desc.K9.rowsFit p.rows s' = true := by
  have h1 : s'.tl?.map (TailClaims.Law.blank u) = s.tl?.map (TailClaims.Law.blank u) := congrArg Prod.fst hnum
  have h2 : s'.funs? = s.funs? := congrArg (fun x => x.2.1) hnum
  have h3 : s'.fork?.map (·.planClaimsF) = s.fork?.map (·.planClaimsF) := congrArg (fun x => x.2.2) hnum
  unfold Desc.K9.rowsFit
  cases ht : s'.tl? with
  | none => rfl
  | some tl =>
    cases hf : s'.funs? with
    | none => rfl
    | some funs =>
      cases hF : s'.fork? with
      | none => rfl
      | some F =>
        show decide (F.planClaimsF + OnBytes.Tie.Pv.Tail.Port.topOf tl funs ≤ p.rows) = true
        rw [ht] at h1
        rw [hf] at h2
        rw [hF, Desc.K9.get_fork s a ha] at h3
        have e3 : F.planClaimsF = a.F.planClaimsF := Option.some.inj h3
        have hq : π (K9L.fixed9 φ s).1 = (some (TailClaims.Law.blank u tl), some funs) := by
          show π (φ s) = _
          rw [A.reads s, ← h1, ← h2]
          rfl
        have h := hW (K9L.pubOf a) _ funs (by show (Desc.K9.atS.get? s).map K9L.pubOf = _; rw [ha]; rfl) hq
        exact decide_eq_true (by rw [e3]; exact h)

variable {V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S Claim V W X Pb} {b : ℕ} {own : List (ℕ × ℕ)}
  {rdW : T.Wt → ℕ × ℕ → Sound.MsgQ}

/-- **THE JOIN, where two runs stand behind the batching.** -/
theorem join_plain : JoinPlain sub l Lk p φ Ok nU u π tmOf lenOf T b own rdW := by
  intro c Z k w rw test share8 rLs rTs pW Front Sd A hrw hq FS hlen _ _ _ hS0 hK0 hS1 hK1 h8 κ s m En ds y cols s' x z
    G St v hFront htest
  have hs := St.step.2
  have hOk := FS.ready κ s m En ds y cols s' x z G St
  obtain ⟨hfree, hsh8⟩ := hq s' htest
  have hcs := FS.counts κ s m En ds y cols s' x z G St
  have htests := tests_pass Sd A T.ft s s' _ cols _ hs hOk hfree (FS.lens κ s m En ds y cols s' x z G St hOk) hcs
  obtain ⟨hFx, hgood, hnum, bp, hbp, _⟩ := behind_fixed A T.ft s s' _ cols _ hs hOk
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (LinkJoin.parts_batch Lk p A.share.hb₁ T.ft s _ cols s' _ hs).1
  -- the first run behind
  obtain ⟨z₁, hz₁, hr₁, hf₁, hl₁⟩ := lsTail_returns s' bp hbp
  have hfun : (S.funs? s).isSome = true := tables_of_counts w s hcs
  have hfun' : (S.funs? s').isSome = true := by rw [(shows_same A s s' hFx).2]; exact hfun
  obtain ⟨o0, run0, ho0, hat0, hrun0⟩ := hS0
  obtain ⟨o1, run1, ho1, hat1, hrun1⟩ := hS1
  have e0 := hrun0 s' z₁ (hK0 s' z₁ hz₁ hfun') hr₁
  obtain ⟨bg, hbg, _, hsz⟩ := hgood
  have hmem0 : o0 ∈ First.orderAfterOf sub := by
    rw [← A.seg.orderAfter]; exact List.mem_of_getElem? ho0
  obtain ⟨a₁, ha₁, _, g₁, _, f₁⟩ := A.runs.hquiet o0 hmem0 run0 hat0 (K9L.fixed9 φ s) s' bg z₁ hFx
    ⟨bg, hbg, ‹_›, hsz⟩ hbg hsz e0
  have hfun₁ : (S.funs? z₁).isSome = true := by rw [(shows_same A s z₁ f₁).2]; exact hfun
  -- the last run behind
  obtain ⟨t, ht⟩ := h8 κ s m En ds y cols s' x z G St htests hsh8 z₁ f₁ g₁ hf₁ hl₁
  have e1 := hrun1 z₁ t (hK1 z₁ t ht hfun₁) (tests_reply nU z₁ t ht)
  have hord : Lk.orderAfter = [o0, o1] := by
    match hL : Lk.orderAfter, hlen, ho0, ho1 with
    | [q0, q1], _, h0, h1 =>
      obtain rfl := Option.some.inj h0
      obtain rfl := Option.some.inj h1
      rfl
  have hafter : Lk.runBehind s' = .ok t := by
    unfold Link.runBehind
    rw [htests, hord]
    show afterIn Lk.hear [o0, o1] s' = .ok t
    rw [afterIn_step Lk.hear o0 [o1] s' z₁ run0 hat0 e0, afterIn_step Lk.hear o1 [] z₁ t run1 hat1 e1]
    rfl
  refine ⟨⟨t, hafter, FS.totalIn κ s m En ds y cols s' x z G St t hafter, ?_⟩, ?_⟩
  · exact totalQ_front A own (rdW v) T.ft s s' t _ cols _ hs hOk hafter a ha fun o ho n c hc =>
      FS.back o ho κ s m En ds y cols s' x z G St a v ha hOk (hFront o ho) n c hc
  · rw [hrw]
    exact rw_front A s s' a ha hnum (FS.rw κ s m En ds y cols s' x z G St)

/-- What K4's run behind the batching leaves: the reply, the ledger, the smallness test's state. -/
theorem freeSlot_leaves {p4 : OnBytes.Desc.First.K4.Par} {run4 : S → Except String S}
    (hr : (OnBytes.Desc.First.K4.blockAtC p4).after.lookup "free-slot" = some run4) (e r : S)
    (h : run4 e = .ok r) : ProofFile.sameReply e r = true ∧ r.fork? = e.fork? ∧ r.tl? = e.tl? := by
  obtain ⟨a, hh, rfl⟩ := K4Run.k4_freeSlot_wrote hr h
  refine ⟨beq_self_eq_true _, ?_, ?_⟩
  · simp [S.fork?, hh]
  · simp [S.tl?, hh]

/-- **THE JOIN, at a feed-forward segment: three runs behind.** -/
theorem join_layers : JoinLayers sub l Lk p φ Ok nU u π tmOf lenOf T b own rdW := by
  intro c Z k w rw test share8 share4 rLs rTs run4 p4 pW Front Sd A hrw hq FS hlen _ _ _ hS0 hK0 hr4 hS1 hS2 hK2 h8 h4
    κ s m En ds y cols s' x z G St v hFront htest
  have hs := St.step.2
  have hOk := FS.ready κ s m En ds y cols s' x z G St
  obtain ⟨hfree, hsh8, hsh4⟩ := hq s' htest
  have hcs := FS.counts κ s m En ds y cols s' x z G St
  have htests := tests_pass Sd A T.ft s s' _ cols _ hs hOk hfree (FS.lens κ s m En ds y cols s' x z G St hOk) hcs
  obtain ⟨hFx, hgood, hnum, bp, hbp, _⟩ := behind_fixed A T.ft s s' _ cols _ hs hOk
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (LinkJoin.parts_batch Lk p A.share.hb₁ T.ft s _ cols s' _ hs).1
  obtain ⟨z₁, hz₁, hr₁, hf₁, F₁, tl₁, hF₁, htl₁, hl₁⟩ := lsTail_returns s' bp hbp
  have hfun : (S.funs? s).isSome = true := tables_of_counts w s hcs
  have hfun' : (S.funs? s').isSome = true := by rw [(shows_same A s s' hFx).2]; exact hfun
  obtain ⟨o0, run0, ho0, hat0, hrun0⟩ := hS0
  obtain ⟨o1, run1, ho1, hat1, hrun1⟩ := hS1
  obtain ⟨o2, run2, ho2, hat2, hrun2⟩ := hS2
  have hmem : ∀ j o, Lk.orderAfter[j]? = some o → o ∈ First.orderAfterOf sub := fun j o h => by
    rw [← A.seg.orderAfter]; exact List.mem_of_getElem? h
  have e0 := hrun0 s' z₁ (hK0 s' z₁ hz₁ hfun') hr₁
  obtain ⟨bg, hbg, hhand, hsz⟩ := hgood
  obtain ⟨a₁, ha₁, _, g₁, _, f₁⟩ := A.runs.hquiet o0 (hmem 0 o0 ho0) run0 hat0 (K9L.fixed9 φ s) s' bg z₁ hFx
    ⟨bg, hbg, hhand, hsz⟩ hbg hsz e0
  -- K4's run
  obtain ⟨z₂, hz₂⟩ := h4 κ s m En ds y cols s' x z G St htests hsh4 z₁ hz₁
  obtain ⟨hr₂, hf₂, htl₂⟩ := freeSlot_leaves hr4 z₁ z₂ hz₂
  have e1 := hrun1 z₁ z₂ hz₂ hr₂
  obtain ⟨bg₁, hbg₁, hhand₁, hsz₁⟩ := g₁
  obtain ⟨a₂, ha₂, _, g₂, _, f₂⟩ := A.runs.hquiet o1 (hmem 1 o1 ho1) run1 hat1 (K9L.fixed9 φ s) z₁ bg₁ z₂ f₁
    ⟨bg₁, hbg₁, hhand₁, hsz₁⟩ hbg₁ hsz₁ e1
  have hfun₂ : (S.funs? z₂).isSome = true := by rw [(shows_same A s z₂ f₂).2]; exact hfun
  -- the last run behind
  obtain ⟨t, ht⟩ := h8 κ s m En ds y cols s' x z G St htests hsh8 z₂ f₂ g₂ (hf₂.trans hf₁)
    ⟨F₁, tl₁, hF₁, htl₁, htl₂.trans hl₁⟩
  have e2 := hrun2 z₂ t (hK2 z₂ t ht hfun₂) (tests_reply nU z₂ t ht)
  have hord : Lk.orderAfter = [o0, o1, o2] := by
    match hL : Lk.orderAfter, hlen, ho0, ho1, ho2 with
    | [q0, q1, q2], _, h0, h1, h2 =>
      obtain rfl := Option.some.inj h0
      obtain rfl := Option.some.inj h1
      obtain rfl := Option.some.inj h2
      rfl
  have hafter : Lk.runBehind s' = .ok t := by
    unfold Link.runBehind
    rw [htests, hord]
    show afterIn Lk.hear [o0, o1, o2] s' = .ok t
    rw [afterIn_step Lk.hear o0 [o1, o2] s' z₁ run0 hat0 e0, afterIn_step Lk.hear o1 [o2] z₁ z₂ run1 hat1 e1,
      afterIn_step Lk.hear o2 [] z₂ t run2 hat2 e2]
    rfl
  refine ⟨⟨t, hafter, FS.totalIn κ s m En ds y cols s' x z G St t hafter, ?_⟩, ?_⟩
  · exact totalQ_front A own (rdW v) T.ft s s' t _ cols _ hs hOk hafter a ha fun o ho n c hc =>
      FS.back o ho κ s m En ds y cols s' x z G St a v ha hOk (hFront o ho) n c hc
  · rw [hrw]
    exact rw_front A s s' a ha hnum (FS.rw κ s m En ds y cols s' x z G St)

end

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.freeSlot_leaves
#print axioms ProofFile.Honest.K9.join_layers
#print axioms ProofFile.Honest.K9.rw_front
#print axioms ProofFile.Honest.K9.join_plain
#print axioms ProofFile.Honest.K9.afterIn_step
#print axioms ProofFile.Honest.K9.lsTail_returns
#print axioms ProofFile.Honest.K9.tests_reply
#print axioms ProofFile.Honest.K9.tables_of_counts
