-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/SilentAnswers.lean: THE SILENT READER (Law/K6SilentCode.lean: k6Silent)
ANSWERS AT THE OUTPUT HEAD's FOUR RUNS "norm" | "policy" | "logits" | "join" BEHIND THE ACCEPT OF
THE HEAD's OWN SUB-PROTOCOL: the premise hR of Law/K6FormsInT.lean's k6_formsInT. A TOTALITY: the
tables of reads can be made; at the state with the tables laid all the kind's letters are there;
each run accepts; the reader's own test on its claims says yes. Statements and proofs.

  squares_size     the squares' point has lPd + lt coordinates where the head's hearing returns.
  covered_answers  the covered positions are there: from the state's own test on the request's words
                   and a heard reply that is a token of the vocabulary.
  reads_some, reads_with   the seat's reader of the reads' places answers.
  row0_entryAt, entriesRow0_of_reads   EntriesRow0 (k6_formsInT's premise hRow), PAID.
  ownRow_of_row0   a form on row 0 of the reads' array passes the reader's test on entries, where
                   that array has one own row.
  own_answers, join_answers   the reader answers, from the letters.
  letters_behind   behind the accept: the tables, the letters and what the two above ask of them.
  four_answer      MAIN: see its docstring.

BY K6's and K7's files' Came.behind_all | hear_sizes | zt_size_at | hear_parts · norm_parts ·
level_r_size · letters_front · k6_run_answers · join_iff · claims_row0 | keyVector_row0.
WHAT IT IS NOT. An implication. NAMED PREMISES THAT NOBODY PAYS HERE: two tests with code on public
numbers THAT HAVE RUN NOWHERE (tabsPlanB · readsPlanB) · P.h = W.hS · 5 ≤ lmbH · K6States · K6Back ·
the covered positions at t · the array of the reads at t: there, with a column, as wide as the
vector of reads, AND WITH ONE OWN ROW (no item of the table of joints says the last) · of what the
lookup heard: the norm's columns' point has ls coordinates; lmbH ≤ kT + 5; six calls; six weights;
the join's debt unpaid; the form left for the join names no entry. Nothing on what the reader
answers. Nothing on soundness.
LETTERS. R stands under "there is" in the top's conclusion: tied by k6Silent's own answer.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.TablesAnswer
import Johnson.Desc.Kinds.Law.WeightTwinAt
import Johnson.Desc.Kinds.Law.NormSquares
import Johnson.Desc.Kinds.Law.K6Silent
import Johnson.Desc.Kinds.Law.K6FormsInT
import Johnson.Desc.Kinds.Law.K6RecordPaid
import Johnson.Desc.Kinds.Law.K6SilentRides
import Johnson.Desc.Kinds.Law.ReaderRides
import Johnson.Top.H.K3SeatFits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Fork Aff)
open VerifiableInference.Desc.First (S HeadOwn)
open Norm (lt ls lPd)

section Classes
variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In]

/-- The squares' point, where the head's hearing returns. -/
theorem squares_size {F G : Fork} {rs left : List Fmt.RoundView} {H : HeardAll} (hW : WellLaid F)
    (h : hear F rs = some (H, G, left)) : H.1.squares.r.size = lPd + lt := by
  obtain ⟨Fa, Fb, l1, hN, _⟩ := Came.hear_parts hW h
  obtain ⟨p0, p1, tS, p2, tP, F1, F2, F3, _, hp, _, _, hlev, _⟩ := norm_parts hW hN
  rw [level_r_size hlev, zS_size _ (drawPoint_size hp)]

end Classes

/-- **The covered positions are there**: the state's own test on the request's words says yes, and
the heard reply is a token of the vocabulary. -/
theorem covered_answers (T V : Nat) (s : S) (y : Nat) (hy : s.replyTok? = some y) (hyV : y < V)
    (hq : s.reqOk T V = true) : ∃ cov, s.covered T V = .ok cov := by
  unfold S.reqOk at hq
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hq
  obtain ⟨⟨h1, h2⟩, h3⟩ := hq
  have hT : s.reqT = T := by
    unfold S.reqT
    omega
  unfold S.tokv at h2
  unfold S.rowR S.rowE at h3
  rw [hT] at h2 h3
  unfold S.covered
  rw [hy]
  unfold S.coveredAt
  simp only [hyV, decide_true, Bool.not_true, Bool.false_eq_true, if_false, h1, beq_self_eq_true,
    h2, h3]
  exact ⟨_, rfl⟩

/-- The seat's reader of the reads' places answers: the tables are laid, the array is there with a
column, and each of the twelve tables is there, long enough. -/
theorem reads_some (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (s : S) (o : HeadOwn) (F : Fork)
    (tr : OnBytes.Model.HTree) (tt : OnBytes.Model.Head.Tables) (ho : s.here = .head o)
    (hF : s.fork? = some F) (ht : o.t = some tt) (htr : F.trees[iU3]? = some tr) (hK : tr.K ≠ 0)
    (hneed : ((readsNeed h).all fun n =>
      (tt.tab.find? fun e => e.1 == n.1).any fun e => Nat.ble n.2 e.2.2) = true) :
    ∃ x, (seatAt h iU3).reads s = some x := by
  unfold seatAt
  simp only [ho, hF, ht, Option.bind_some, htr]
  rw [if_neg (by simp [hK, hneed])]
  exact ⟨_, rfl⟩

/-- The same at a state into which tables are laid. -/
theorem reads_with (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (t : S) (o : HeadOwn) (F : Fork)
    (tr : OnBytes.Model.HTree) (tt : OnBytes.Model.Head.Tables) (ho : t.here = .head o)
    (hF : t.fork? = some F) (htr : F.trees[iU3]? = some tr) (hK : tr.K ≠ 0)
    (hneed : ((readsNeed h).all fun n =>
      (tt.tab.find? fun e => e.1 == n.1).any fun e => Nat.ble n.2 e.2.2) = true) :
    ∃ x, (seatAt h iU3).reads { t with here := .head { o with t := some tt } } = some x := by
  refine reads_some h iU3 _ _ F tr tt rfl ?_ rfl htr hK hneed
  unfold S.fork? at hF ⊢
  rw [ho] at hF
  exact hF

/-- The form at a position below the array's width names row 0 alone. -/
theorem row0_entryAt (iU3 K3 pos : Nat) (h : pos < K3) : Row0 iU3 K3 (entryAt iU3 K3 pos) := by
  intro x hx
  unfold entryAt at hx
  rw [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h] at hx
  obtain rfl : x = { tree := iU3, row := 0, idx := pos, coef := OnBytes.oneE } := by
    simpa [Aff.ent] using hx
  exact ⟨rfl, rfl, h⟩

/-- **EntriesRow0, PAID**: where the seat's reader of the reads' places answers and each table ends
below the array's width. -/
theorem entriesRow0_of_reads (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (s : S)
    (x : FinalNorm.Reads × Reads) (hx : (seatAt h iU3).reads s = some x)
    (hB : ∀ o tt F tr, s.here = .head o → o.t = some tt → s.fork? = some F →
      F.trees[iU3]? = some tr → ∀ y ∈ tt.tab, y.2.1 + y.2.2 ≤ tr.K) :
    ∃ F tr, s.fork? = some F ∧ F.trees[iU3]? = some tr ∧
      @EntriesRow0 (sizesOf h) iU3 tr.K x.1 x.2 := by
  obtain ⟨o, F, tt, tr, ho, hF, ht, htr, _, a1, a2, a3⟩ := reads_are h iU3 s x hx
  obtain ⟨w1, w2⟩ := reads_within h iU3 s x hx tt o ho ht
  have hb := hB o tt F tr ho ht hF htr
  letI := sizesOf h
  refine ⟨F, tr, hF, htr, ⟨fun r i hi => ?_, fun i hi => ?_, fun r i hi => ?_⟩⟩
  · obtain ⟨t, h1, h2, h3⟩ := w1 r
    rw [a1 r i, h2]
    have := hb t (List.mem_of_find?_eq_some h1)
    exact row0_entryAt _ _ _ (by omega)
  · obtain ⟨t, h1, h2, h3⟩ := w2 .wideAtKeys
    have hi' : i < t.2.2 := by
      refine Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hi ?_) h3
      exact Nat.div_le_div_right (Nat.le_add_right _ _)
    rw [a2 i, show firstOf tt "hf@Z" = t.2.1 from h2]
    have := hb t (List.mem_of_find?_eq_some h1)
    exact row0_entryAt _ _ _ (by omega)
  · obtain ⟨t, h1, h2, h3⟩ := w2 r
    rw [a3 r i, h2]
    have := hb t (List.mem_of_find?_eq_some h1)
    exact row0_entryAt _ _ _ (by omega)

/-- A form with Row0 passes the reader's test on entries, where the array has one own row. -/
theorem ownRow_of_row0 {iU3 K3 : Nat} {f : Form} (h : Row0 iU3 K3 f) {F : Fork}
    {tr : OnBytes.Model.HTree} (htr : F.trees[iU3]? = some tr) (hR : tr.R = 1) :
    f.ents.all (K9.ownRow F) = true := by
  rw [← Array.all_toList, List.all_eq_true]
  intro x hx
  obtain ⟨e1, e2, _⟩ := h x hx
  unfold K9.ownRow
  rw [e1, htr]
  simp [hR, e2]

/-- **THE SILENT READER ANSWERS AT THE HEAD's THREE OWN RUNS**, where the tables can be made and the
letters are there. -/
theorem own_answers (W : OnBytes.Model.Verify.Public) (P : K8.ReadsQuiet.PH) (l piece b : Nat)
    (states : Nat → List (K9.RunOf S))
    (K : K6States W.hS (readsOf W) (parOf W.hS (workOf W)) l piece states b)
    (KB : K6Back W.hS (readsOf W) (parOf W.hS (workOf W)) l piece states b) (t e : S)
    (v : Given × Behind × Places) (he : withTables P t = some e)
    (hv : lettersAt (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) e = .ok v)
    (hB : (letI := v.1
      letI := v.2.1
      HeardBare))
    (hd : (letI := v.1
      Norm.S2 ∣ Norm.d))
    (F : Fork) (tr : OnBytes.Model.HTree) (hF : e.fork? = some F)
    (htr : F.trees[readsOf W]? = some tr) (hR1 : tr.R = 1)
    (hRow : (letI := v.1
      letI := v.2.1
      EntriesRow0 (readsOf W) tr.K v.2.2.final v.2.2.head))
    (name : String) (hn : name = "norm" ∨ name = "policy" ∨ name = "logits") :
    ∃ R, k6Silent P states b name t = some R := by
  obtain ⟨run, run', hf, hrun, _⟩ := K.own name hn
  obtain ⟨fs, lk⟩ : ∃ fs, (claimsSeat v).lookup name = some fs := by
    rcases hn with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  have hy := k6_run_answers W.hS (readsOf W) l piece (parOf W.hS (workOf W)) name run' hrun 0 e
    v.1 v.2.1 v.2.2 fs hv lk
  have hs := KB.own name run run' hf hrun 0 e _ hy rfl
  have hck : ((fs.map asClaim).all fun c => c.runs.isEmpty && c.eqFirst.isNone &&
      c.form.ents.all (K9.ownRow F)) = true := by
    rw [List.all_eq_true]
    intro c hc
    obtain ⟨f, hfm, rfl⟩ := List.mem_map.1 hc
    letI := v.1
    letI := v.2.1
    letI := v.2.2
    have h0 := claims_row0 hRow hB hd name fs lk f hfm
    have h1 : f.ents.all (K9.ownRow F) = true := ownRow_of_row0 h0 htr hR1
    show ((asClaim f).runs.isEmpty && (asClaim f).eqFirst.isNone &&
      f.ents.all (K9.ownRow F)) = true
    rw [h1]
    rfl
  unfold k6Silent
  rw [he]
  show ∃ R, K9.readerOf states b name e = some R
  unfold K9.readerOf
  rw [hf]
  simp only [Option.bind_some]
  rw [hs, hF]
  simp only
  rw [hF]
  simp only [Option.bind_some]
  rw [if_pos hck]
  exact ⟨_, rfl⟩

/-- **THE SILENT READER ANSWERS AT "join"**, where the tables can be made and the letters are there;
the lookup's debt on the join is not yet paid; one key vector and one heard scalar a call. -/
theorem join_answers (W : OnBytes.Model.Verify.Public) (P : K8.ReadsQuiet.PH) (l piece b : Nat)
    (states : Nat → List (K9.RunOf S))
    (K : K6States W.hS (readsOf W) (parOf W.hS (workOf W)) l piece states b)
    (KB : K6Back W.hS (readsOf W) (parOf W.hS (workOf W)) l piece states b) (t e : S)
    (v : Given × Behind × Places) (he : withTables P t = some e)
    (hv : lettersAt (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) e = .ok v)
    (hB : (letI := v.1
      letI := v.2.1
      HeardBare))
    (hd : (letI := v.1
      Norm.S2 ∣ Norm.d))
    (hJ : (letI := v.1
      JVa ≤ JV))
    (F : Fork) (tr : OnBytes.Model.HTree) (hF : e.fork? = some F)
    (htr : F.trees[readsOf W]? = some tr) (hR1 : tr.R = 1)
    (hRow : (letI := v.1
      letI := v.2.1
      EntriesRow0 (readsOf W) tr.K v.2.2.final v.2.2.head))
    (gk : OnBytes.Model.Forest.Heard) (hgk : e.lookHeard? = some gk)
    (hun : K3.unpaid F gk.owedJoin = true) (hbare : gk.cEnd.ents = #[])
    (hsz : ((keyVectorsAt v).size == gk.shape.calls.size &&
      gk.e.size == gk.shape.calls.size) = true) :
    ∃ R, k6Silent P states b "join" t = some R := by
  obtain ⟨run, hf, _⟩ := K.join
  have hkeys : callerKeys (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) e =
      some (keyVectorsAt v) := by
    unfold callerKeys
    rw [hv]
    rfl
  have hy := (join_iff (callerKeys (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W))) 0 e
    ([asClaim (Came.joinForm gk (keyVectorsAt v))], e.putFork (F.paid gk.owedJoin))).2
    ⟨F, gk, keyVectorsAt v, hF, hgk, hun, hkeys, hsz, rfl⟩
  have hs := KB.join run hf 0 e _ hy (by rw [out_putFork])
  have h0 : Row0 (readsOf W) tr.K (Came.joinForm gk (keyVectorsAt v)) := by
    refine joinForm_has (kept_row0 (readsOf W) tr.K) gk (keyVectorsAt v) (fun c hc => ?_)
      (row0_bare hbare)
    have hlen : c < v.1.calls.length := by
      simpa [keyVectorsAt] using hc
    letI := v.1
    letI := v.2.1
    letI := v.2.2
    unfold keyVectorsAt
    rw [Came.getD_map_toArray v.1.calls _ c hlen (Aff.ofConst zeroE) (0, [])]
    exact keyVector_row0 hRow hB hd hJ _ _
  have hck : ([asClaim (Came.joinForm gk (keyVectorsAt v))].all fun c =>
      c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (K9.ownRow F)) = true := by
    have h1 : (Came.joinForm gk (keyVectorsAt v)).ents.all (K9.ownRow F) = true :=
      ownRow_of_row0 h0 htr hR1
    show ((asClaim (Came.joinForm gk (keyVectorsAt v))).runs.isEmpty &&
      (asClaim (Came.joinForm gk (keyVectorsAt v))).eqFirst.isNone &&
      (Came.joinForm gk (keyVectorsAt v)).ents.all (K9.ownRow F) && true) = true
    rw [h1]
    rfl
  unfold k6Silent
  rw [he]
  show ∃ R, K9.readerOf states b "join" e = some R
  unfold K9.readerOf
  rw [hf]
  simp only [Option.bind_some]
  rw [hs, hF]
  simp only
  rw [VerifiableInference.OnPublicFiles.fork_putFork e F _ hF]
  simp only [Option.bind_some]
  rw [if_pos hck]
  exact ⟨_, rfl⟩

/-- **BEHIND THE ACCEPT OF THE HEAD's OWN SUB-PROTOCOL THE TABLES CAN BE MADE, AND AT THE STATE WITH
THE TABLES LAID ALL THE KIND's LETTERS ARE THERE.** -/
theorem letters_behind (W : OnBytes.Model.Verify.Public) (l : Nat) {s t : S}
    {rv : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : (blockAt W.hS (readsOf W) (workOf W) l).decide s rv gs = .ok t)
    (hWL : WellLaid ((seatAt W.hS (readsOf W)).ledger s)) (hcan : Canonical rv)
    (hplan : (parOf W.hS (workOf W)).ok = true) (P : K8.ReadsQuiet.PH) (hP : P.h = W.hS)
    (hB : tabsPlanB P.h P.L P.hp = true) (hRB : readsPlanB P.h P.hp = true)
    (hcov : ∃ cov, t.covered P.h.T P.h.V = .ok cov)
    (hfeat : hasFeatures (parOf W.hS (workOf W)))
    (hzj : ∀ gk, s.lookHeard? = some gk → W.hS.ls ≤ (OnBytes.Model.Head.zjOf P.L gk 0).size)
    (h4 : 5 ≤ W.hS.lmbH)
    (h5 : ∀ gk, s.lookHeard? = some gk → W.hS.lmbH ≤ gk.shape.kT + 5)
    (F : Fork) (tr : OnBytes.Model.HTree) (hF : t.fork? = some F)
    (htr : F.trees[readsOf W]? = some tr) (hK : tr.K ≠ 0) (hwide : P.hp.nU.getD 2 0 ≤ tr.K) :
    ∃ e v, withTables P t = some e ∧
      lettersAt (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) e = .ok v ∧
      e.fork? = some F ∧ e.lookHeard? = t.lookHeard? ∧
      (letI := v.1
       letI := v.2.1
       HeardBare) ∧
      (letI := v.1
       Norm.S2 ∣ Norm.d) ∧
      (letI := v.1
       JVa ≤ JV) ∧
      (letI := v.1
       letI := v.2.1
       EntriesRow0 (readsOf W) tr.K v.2.2.final v.2.2.head) ∧ v.1.calls.length = 6 := by
  obtain ⟨a0, _, _, _, ha0, hop, _, _⟩ := Came.decide_record _ _ _ _ hd
  obtain ⟨g, H, F1, a, gk, Q, hg, hh, ha, hgk, ht, hg', hH', _⟩ :=
    Came.behind_all W l hd hWL hcan
  obtain rfl : a0 = a := by
    rw [ha0] at ha
    injection ha
  obtain ⟨cov, hcov⟩ := hcov
  have hzt := Came.zt_size_at W hg hplan
  have hsq := squares_size hWL hh
  have hnm := (Came.hear_sizes hWL hh).1
  have hlk : s.lookHeard? = some gk := by
    unfold S.lookHeard?
    rw [ha0]
    simp [hop, hgk]
  obtain ⟨z, y, _, _, _, hgeq⟩ := Came.given_ok _ _ s g hg
  have hsz : g.sizes = sizesOf W.hS := by rw [hgeq]; rfl
  have els : W.hS.ls = (ls : Nat) := by
    show (sizesOf W.hS).ls = g.sizes.ls
    rw [hsz]
  have elt : W.hS.lt = (lt : Nat) := by
    show (sizesOf W.hS).lt = g.sizes.lt
    rw [hsz]
  have hls' : (ls : Nat) ≤ lPd := by
    refine Came.ls_le_lPd ?_ (sizes_of_plan _ _ s g hplan hg).1
    have h0 : (letI := sizesOf W.hS
      0 < Norm.d) := hfeat
    rw [← hsz] at h0
    exact h0
  have hla : P.h.la = P.h.ls + P.h.lt := by
    unfold tabsPlanB at hB
    simp only [Bool.and_eq_true, beq_iff_eq] at hB
    exact hB.1.1.1.2
  obtain ⟨t0, ht0, tt, htt, htab⟩ := tables_answers P.h P.L P.hp cov (heardOf gk H) hB
    (by
      show P.h.la ≤ H.1.squares.r.size
      rw [hsq, hla, hP, els, elt]
      omega)
    (by rw [hP]; exact hzj gk hlk)
    (by
      show H.2.1.normed.r.size = P.h.lt
      rw [hnm, hzt, hP, elt])
    (by rw [hP]; exact h4) (by rw [hP]; exact h5 gk hlk)
  have hneed : ((readsNeed W.hS).all fun n =>
      (tt.tab.find? fun e => e.1 == n.1).any fun e => Nat.ble n.2 e.2.2) = true := by
    unfold readsPlanB at hRB
    rw [ht0, hP] at hRB
    rw [htab]
    exact hRB
  obtain ⟨o1, hhere, hx1, hop1⟩ : ∃ o1 : HeadOwn, t.here = .head o1 ∧
      o1.x = some (heardOf gk H) ∧ o1.opened = true := by
    rw [ht]
    exact ⟨_, rfl, rfl, hop⟩
  obtain ⟨x, hx⟩ := reads_with W.hS (readsOf W) t o1 F tr tt hhere hF htr hK hneed
  have he := (withTables_iff P t _).2 ⟨o1, cov, _, tt, hhere, hop1, hcov, hx1, htt, rfl⟩
  have hFe := (fork_withTables he).1.trans hF
  obtain ⟨F', tr', hF', htr', hRow⟩ := entriesRow0_of_reads W.hS (readsOf W) _ x hx
    (below_of_width P _ (readsOf W) (fun e' F2 tr2 he' hF2 htr2 => by
      obtain rfl := Option.some.inj (he.symm.trans he')
      obtain rfl : F = F2 := Option.some.inj (hFe.symm.trans hF2)
      obtain rfl : tr = tr2 := Option.some.inj (htr.symm.trans htr2)
      exact hwide) _ · · · · he)
  obtain rfl : F = F' := Option.some.inj (hFe.symm.trans hF')
  obtain rfl : tr = tr' := Option.some.inj (htr.symm.trans htr')
  obtain ⟨hd, hJ⟩ := sizes_of_plan _ _ _ g hplan hg'
  refine ⟨_, _, he, letters_front W.hS (readsOf W) _ (front_withTables he) g H x hg' hH' hx, hFe,
    (fork_withTables he).2, heardBare_of_hear hWL hh, hd, hJ, ?_, ?_⟩
  · show @EntriesRow0 g.sizes (readsOf W) tr.K x.1 x.2
    rw [hsz]
    exact hRow
  · have e6 : g.calls = (@fromLookup (parOf W.hS (workOf W)).sizes
        (parOf W.hS (workOf W)).floor z.1 z.2).calls :=
      congrArg (fun q : Given => q.calls) hgeq
    show g.calls.length = 6
    rw [e6]
    exact @Came.calls_length (parOf W.hS (workOf W)).sizes (parOf W.hS (workOf W)).floor z.1 z.2

/-- **THE SILENT READER ANSWERS AT THE HEAD's FOUR RUNS BEHIND THE ACCEPT OF THE HEAD's OWN
SUB-PROTOCOL.** s: the verifier's state in front; t: behind. -/
theorem four_answer (W : OnBytes.Model.Verify.Public) (l : Nat)
    (blk : VerifiableInference.Desc.Block S Unit) (hb : blockOf W l = some blk) (s t : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (Sound.below blk).decide s rs gs = .ok t) (hOn : K6On W s) (P : K8.ReadsQuiet.PH)
    (hP : P.h = W.hS) (hB : tabsPlanB P.h P.L P.hp = true) (hRB : readsPlanB P.h P.hp = true)
    (hcov : ∃ cov, t.covered P.h.T P.h.V = .ok cov)
    (hzj : ∀ gk, s.lookHeard? = some gk → W.hS.ls ≤ (OnBytes.Model.Head.zjOf P.L gk 0).size)
    (h4 : 5 ≤ W.hS.lmbH)
    (h5 : ∀ gk, s.lookHeard? = some gk → W.hS.lmbH ≤ gk.shape.kT + 5)
    (F : Fork) (tr : OnBytes.Model.HTree) (hF : t.fork? = some F)
    (htr : F.trees[readsOf W]? = some tr) (hK : tr.K ≠ 0) (hwide : P.hp.nU.getD 2 0 ≤ tr.K)
    (hR1 : tr.R = 1) (piece b : Nat) (states : Nat → List (K9.RunOf S))
    (K : K6States W.hS (readsOf W) (parOf W.hS (workOf W)) l piece states b)
    (KB : K6Back W.hS (readsOf W) (parOf W.hS (workOf W)) l piece states b)
    (gk : OnBytes.Model.Forest.Heard) (hgk : t.lookHeard? = some gk)
    (hun : K3.unpaid F gk.owedJoin = true) (hbare : gk.cEnd.ents = #[])
    (hc6 : gk.shape.calls.size = 6) (he6 : gk.e.size = 6) (name : String) (hn : K6Name name) :
    ∃ R, k6Silent P states b name t = some R := by
  obtain ⟨hcan, hd⟩ := canonical_of_below blk s t rs gs h
  obtain ⟨i, hu, rfl⟩ := Option.map_eq_some_iff.mp hb
  have hr : readsOf W = i := by
    unfold readsOf
    rw [hu]
    rfl
  subst hr
  obtain ⟨e, v, he, hv, hFe, hlk, hBr, hdS, hJ, hRow, h6⟩ := letters_behind W l hd hOn.1 hcan
    hOn.2.1 P hP hB hRB hcov hOn.2.2.1 hzj h4 h5 F tr hF htr hK hwide
  rcases hn with hn | hn | hn | rfl
  · exact own_answers W P l piece b states K KB t e v he hv hBr hdS F tr hFe htr hR1 hRow name
      (Or.inl hn)
  · exact own_answers W P l piece b states K KB t e v he hv hBr hdS F tr hFe htr hR1 hRow name
      (Or.inr (Or.inl hn))
  · exact own_answers W P l piece b states K KB t e v he hv hBr hdS F tr hFe htr hR1 hRow name
      (Or.inr (Or.inr hn))
  · refine join_answers W P l piece b states K KB t e v he hv hBr hdS hJ F tr hFe htr hR1 hRow gk
      (hlk.trans hgk) hun hbare ?_
    have e1 : (keyVectorsAt v).size = 6 := by
      simp [keyVectorsAt, h6]
    rw [e1, hc6, he6]
    rfl

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.covered_answers
#print axioms VerifiableInference.Desc.Kinds.Head.Law.four_answer
#print axioms VerifiableInference.Desc.Kinds.Head.Law.letters_behind
#print axioms VerifiableInference.Desc.Kinds.Head.Law.own_answers
#print axioms VerifiableInference.Desc.Kinds.Head.Law.join_answers
