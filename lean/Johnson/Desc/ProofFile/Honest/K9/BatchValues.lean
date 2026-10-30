-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/BatchValues.lean: THE BATCHING's ONE TEST ON VALUES IN THE TABLE OF STEPS ON SHAPES (`cellV`,
Johnson/AtFull/Shape/BatchCells.lean) ACCEPTS AT A STATE IN FRONT OF THE BATCHING, FROM EACH ROW's OWN TEST AT THAT STATE ALONE. The table's
test asks that the open ledger is empty and, behind the draw, each row's test `pre` AT THE STATE IN FRONT OF THAT ROW's RUN, along the
runs that return (`preAllT`, BatchTerms.lean). A row's kind knows the state s in front of the batching. Here the way from s over the
draw and over the runs in front of the row is paid once, for every row whose test reads what the runs leave.

WHAT IS CARRIED from the state t₁ behind the draw to a state u in front of a row's run.
  `Along t₁ u`        every reading of the state that rests under the runs' four writings (`FieldRests`,
                     Johnson/Desc/First/Link/Law/KeepsAny.lean) has at u its value at t₁; the ledger's core is the same (`Kept`); a ledger
                     with its sizes has gone on to a later one with its sizes (Honest/K9/RunsCarry.lean)
  `AlongFront t₁ u`   and, in front of the entry "K8.equations": the smallness test's record and the list of tables are those of t₁

  `preAllT_true`, `preAllT_append`    the tests along the runs, from an invariant: by the list that is left; by a stretch of the order
  `run_of_table`       a yes of a row's guarded run is a yes of the run that stands in the description's list at that entry
  `along_step`, `front_step`          a yes of a row's run hands the invariant on
  **`preAll_of_ties`**   the order cut at "K8.equations" (`PlainTies`): the tests along the whole order, from the rows' tests under the invariant
  **`eqPre_along`**      the row "K8.equations": its test `eqPreB` holds at u: the tables are held (a premise at s); the coefficients on the
                     window are 0 since the draw; no column of a drawn matrix has the weight 0 at the drawn element (the named fall
                     `K8.k8Front` is silent at s)
  **`cellV_of_ties`**    so `cellV` at s, at the one round of the draw
  `own_along`, `look_along`           what a feed-forward segment's rounds returned, and what the first lookup returned, are at u as at s
  `later_along`, `valsT_later`, **`valsTS_along`**   the ledger at u is a later state of the ledger at s; so the attention kind's test, which reads
                     values under slots that are filled, holds at u where it holds at s
  **`cellV_lay`**, **`cellV_att`**, **`cellV_head`**   under the library's hypothesis `AtMgA`, at the seated link of each sort of segment: from "the
                     ledger is empty", the fall's silence, "the tables are held", and the kind's own test at s (`planEnvB`; `valsTS`,
                     with the ledger's sizes; `endsS`)

Limits. The premises at s are shown of no state here. The round is written as the draw's one element; that the thread's rounds are of that form is not said here. `cellV` is true
where the draw refuses, and asks nothing behind a run that refuses. The full size and the hash function `secondHashFunction` alone. This file
proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.PlainAtSeat
import Johnson.Desc.ProofFile.Honest.K9.RunTables
import Johnson.Desc.ProofFile.Honest.K9.BatAtHead
import Johnson.Desc.ProofFile.Honest.K9.RunsCarry
import Johnson.Desc.ProofFile.Honest.K9.GoodAtt
import Johnson.Desc.ProofFile.Honest.K9.GoodAttLook
import Johnson.Desc.First.Att.Claims.LeftLater
import Johnson.Desc.ProofFile.Honest.K8.EqAllFront
import Johnson.Desc.First.TailClaims.K8SitsBetween
import Johnson.Desc.K8.Honest.EqAllBools

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (FieldRests)
open VerifiableInference.Desc.K9.Shape (guardRun guardRun_iff)
open VerifiableInference.Desc.First.K8.Honest (eqPreB liveColsB liveColsB_iff headPre headPost)
open VerifiableInference.Desc.First.TailClaims.Law (partOf partOf_some)
open VerifiableInference.Desc.First.K8.Honest (attPre)
open H2K5.Honest (valsT valsTS)
open Johnson.AtFull.Shape (preAllT batchVT cellV tabOf rowsLay rowsAtt rowsHead endsS)
open P5J (AtMgA)

/-! ## The tests along the runs -/

section
variable {runT : ℕ × String → Desc.K9.Shape.Run} {preT : ℕ × String → ℕ → S → Bool}

/-- From an invariant that is read with the list of entries that is left. -/
theorem preAllT_true (I : List (ℕ × String) → S → Prop)
    (hpre : ∀ o os n s, I (o :: os) s → preT o n s = true)
    (hrun : ∀ o os n s y, I (o :: os) s → runT o n s = .ok y → I os y.2) :
    ∀ os n s, I os s → preAllT runT preT os n s = true
  | [], _, _, _ => rfl
  | o :: os, n, s, h => by
    show (preT o n s && match runT o n s with
      | .ok y => preAllT runT preT os (n + y.1.length) y.2
      | .error _ => true) = true
    rw [hpre o os n s h, Bool.true_and]
    cases hy : runT o n s with
    | error e => rfl
    | ok y => exact preAllT_true I hpre hrun os _ _ (hrun o os n s y h hy)

/-- Over a stretch of the order, from an invariant of that stretch. -/
theorem preAllT_append (J : S → Prop) (rest : List (ℕ × String)) :
    ∀ os : List (ℕ × String), (∀ o ∈ os, ∀ n u, J u → preT o n u = true) →
      (∀ o ∈ os, ∀ n u y, J u → runT o n u = .ok y → J y.2) →
      (∀ n u, J u → preAllT runT preT rest n u = true) →
      ∀ n u, J u → preAllT runT preT (os ++ rest) n u = true
  | [], _, _, hr, n, u, h => hr n u h
  | o :: os, hp, hs, hr, n, u, h => by
    show (preT o n u && match runT o n u with
      | .ok y => preAllT runT preT (os ++ rest) (n + y.1.length) y.2
      | .error _ => true) = true
    rw [hp o (by simp) n u h, Bool.true_and]
    cases hy : runT o n u with
    | error e => rfl
    | ok y =>
      exact preAllT_append J rest os (fun o' ho' => hp o' (List.mem_cons_of_mem _ ho'))
        (fun o' ho' => hs o' (List.mem_cons_of_mem _ ho')) hr _ _ (hs o (by simp) n u y h hy)

end

/-! ## What is carried -/

/-- **From the state behind the draw to a state in front of a row's run.** -/
structure Along (t₁ u : S) : Prop where
  rest : ∀ {γ : Type} (f : S → γ), FieldRests f → f u = f t₁
  core : Kept t₁ u
  later : Desc.K9.CF S.lookHeard? t₁ u

/-- The same in front of the entry "K8.equations". -/
def AlongFront (t₁ u : S) : Prop := Along t₁ u ∧ u.tl? = t₁.tl? ∧ u.funs? = t₁.funs?

theorem Along.refl (t : S) : Along t t := ⟨fun _ _ => rfl, Kept.refl t, (Desc.K9.preCF _).refl t⟩

section
variable {Lk : Link S Claim} {rows : List ((ℕ × String) × Johnson.AtFull.Shape.Row)} {i : ℕ} {pre post : List (ℕ × String)}

/-- A yes of a row's guarded run is a yes of the run in the description's list. -/
theorem run_of_table (tied : ∀ (j : ℕ) (o : ℕ × String), Lk.order[j]? = some o → Tied Lk j (tabOf rows o).run)
    {j : ℕ} {o : ℕ × String} (hj : Lk.order[j]? = some o) {n : ℕ} {u : S} {y : List Claim × S}
    (hy : guardRun ProofFile.sameReply (tabOf rows o).run n u = .ok y) :
    ∃ r, claimsRunOf Lk.hear o = some r ∧ r n u = .ok y := by
  obtain ⟨h1, h2⟩ := (guardRun_iff _ _ _ _ _).1 hy
  obtain ⟨r, hr⟩ := (tied j o hj).there o hj
  refine ⟨r, hr, (tied j o hj).lifts o r hj hr n u y h1 ?_⟩
  unfold ProofFile.sameReply at h2
  exact (beq_iff_eq.1 h2).symm

variable (tied : ∀ (j : ℕ) (o : ℕ × String), Lk.order[j]? = some o → Tied Lk j (tabOf rows o).run)
  (rests : ∀ {γ : Type} (g : S → γ), FieldRests g → ∀ (j : ℕ) (o : ℕ × String) (r : ClaimsRun), Lk.order[j]? = some o →
    claimsRunOf Lk.hear o = some r → ∀ m e z, r m e = .ok z → g z.2 = g e)
  (cores : ∀ (j : ℕ) (o : ℕ × String) (r : ClaimsRun), Lk.order[j]? = some o → claimsRunOf Lk.hear o = some r → RunKeeps r)
  (carries : ∀ (j : ℕ) (o : ℕ × String) (r : ClaimsRun), Lk.order[j]? = some o → claimsRunOf Lk.hear o = some r →
    ∀ n u y, r n u = .ok y → Desc.K9.CF S.lookHeard? u y.2)
  (PT : PlainTies Lk i pre post)
include tied rests cores carries

theorem along_step {t₁ u : S} {o : ℕ × String} (ho : o ∈ Lk.order) {n : ℕ} {y : List Claim × S} (h : Along t₁ u)
    (hy : guardRun ProofFile.sameReply (tabOf rows o).run n u = .ok y) : Along t₁ y.2 := by
  obtain ⟨j, hj⟩ := List.getElem?_of_mem ho
  obtain ⟨r, hr, hz⟩ := run_of_table tied hj hy
  exact ⟨fun f R => (rests f R j o r hj hr n u y hz).trans (h.rest f R), h.core.trans (cores j o r hj hr n u y hz),
    (Desc.K9.preCF _).trans _ _ _ h.later (carries j o r hj hr n u y hz)⟩

include PT

theorem front_step {t₁ u : S} {o : ℕ × String} (ho : o ∈ pre) {n : ℕ} {y : List Claim × S} (h : AlongFront t₁ u)
    (hy : guardRun ProofFile.sameReply (tabOf rows o).run n u = .ok y) : AlongFront t₁ y.2 := by
  have hO : o ∈ Lk.order := by
    rw [PT.order]
    exact List.mem_append_left _ ho
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hO
  obtain ⟨r, hr, hz⟩ := run_of_table tied hj hy
  obtain ⟨f, hu, hp⟩ := PT.pre o ho r hr
  have d := hp.data n u y (hu n u y.1 y.2 hz)
  exact ⟨along_step tied rests cores carries hO h.1 hy, d.1.trans h.2.1, d.2.trans h.2.2⟩

/-- **The tests along the whole order.** -/
theorem preAll_of_ties {t₁ : S}
    (hpre : ∀ o ∈ pre, ∀ n u, Along t₁ u → (tabOf rows o).pre n u = true)
    (heq : ∀ n u, AlongFront t₁ u → (tabOf rows (i, "K8.equations")).pre n u = true)
    (hpost : ∀ o ∈ post, ∀ n u, Along t₁ u → (tabOf rows o).pre n u = true) :
    preAllT (fun o => guardRun ProofFile.sameReply (tabOf rows o).run) (fun o => (tabOf rows o).pre) Lk.order 0 t₁ =
      true := by
  have hE : (i, "K8.equations") ∈ Lk.order := by
    rw [PT.order]
    simp
  have hP : ∀ o ∈ post, o ∈ Lk.order := by
    intro o ho
    rw [PT.order]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ ho)
  have key : preAllT (fun o => guardRun ProofFile.sameReply (tabOf rows o).run) (fun o => (tabOf rows o).pre)
      (pre ++ (i, "K8.equations") :: post) 0 t₁ = true := by
    refine preAllT_append (AlongFront t₁) _ pre (fun o ho n u h => hpre o ho n u h.1)
      (fun o ho n u y h hy => front_step tied rests cores carries PT ho h hy) ?_ 0 t₁ ⟨Along.refl t₁, rfl, rfl⟩
    intro n u h
    show ((tabOf rows (i, "K8.equations")).pre n u &&
      match guardRun ProofFile.sameReply (tabOf rows (i, "K8.equations")).run n u with
      | .ok y => preAllT (fun o => guardRun ProofFile.sameReply (tabOf rows o).run) (fun o => (tabOf rows o).pre) post
          (n + y.1.length) y.2
      | .error _ => true) = true
    rw [heq n u h, Bool.true_and]
    cases hy : guardRun ProofFile.sameReply (tabOf rows (i, "K8.equations")).run n u with
    | error e => rfl
    | ok y =>
      have hA : Along t₁ y.2 := along_step tied rests cores carries hE h.1 hy
      have k := preAllT_append (runT := fun o => guardRun ProofFile.sameReply (tabOf rows o).run)
        (preT := fun o => (tabOf rows o).pre) (Along t₁) [] post (fun o ho n u h => hpost o ho n u h)
        (fun o ho n u y h hy => along_step tied rests cores carries (hP o ho) h hy) (fun _ _ _ => rfl)
        (n + y.1.length) y.2 hA
      rw [List.append_nil] at k
      exact k
  rw [PT.order]
  exact key

end

/-! ## The row "K8.equations" -/

/-- **Its test holds at every state in front of its run.** -/
theorem eqPre_along {p : Desc.K9.Where} {s t₁ u : S} {tr : UInt64 × UInt64 × UInt64}
    (hd : (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne (E.ofTriple tr)⟩] [] = .ok t₁)
    (front : K8.k8Front s [⟨[tr], [], [], none⟩] = none)
    (held : ∀ tl funs, s.tl? = some tl → s.funs? = some funs → tl.funsHeld funs = true)
    (h : AlongFront t₁ u) : eqPreB u = true := by
  obtain ⟨a, ha⟩ := draw_open p s t₁ _ hd
  obtain ⟨a₁, h1, hl⟩ := draw_facts p s t₁ _ a ha hd
  obtain ⟨a', ha', L⟩ := kept_finds a a₁ _ hl t₁ u h1 h.1.core
  have e := draw_is p s t₁ _ a ha hd
  have et : u.tl? = s.tl? := by rw [h.2.1, e, set_tl]
  have ef : u.funs? = s.funs? := by rw [h.2.2, e, VerifiableInference.Desc.First.K8.Honest.set_funs]
  unfold eqPreB
  cases hq : partOf u with
  | none => rfl
  | some q =>
    obtain ⟨q1, q2, q3⟩ := partOf_some.1 hq
    have hF : a'.F = q.F := Option.some.inj ((Desc.K9.get_fork u a' ha').symm.trans q2)
    have hs : s.tl? = some q.tl := et.symm.trans q1
    have hz : K8.zeroColumnWeight q.tl (E.ofTriple tr) = none := by
      simpa [K8.k8Front, hs] using front
    have c1 : q.tl.funsHeld q.funs = true := held q.tl q.funs hs (ef.symm.trans q3)
    have c2 : (q.F.LS.extract q.tl.slotA q.tl.slotB).all isZeroE = true :=
      window_zero q.F.LS (hF ▸ L.empty) _ _
    have c3 : liveColsB q.tl q.funs q.F.theta = true := by
      rw [← hF, L.chi]
      exact (liveColsB_iff _ _ _).2 (K8.liveCols_of_front q.tl q.funs _ hz)
    show (q.tl.funsHeld q.funs && (q.F.LS.extract q.tl.slotA q.tl.slotB).all isZeroE &&
      liveColsB q.tl q.funs q.F.theta) = true
    rw [c1, c2, c3]
    rfl

/-! ## The table's test at the state in front -/

/-- **`cellV` at s, from the rows' tests under the invariant.** -/
theorem cellV_of_ties {Lk : Link S Claim} {rows : List ((ℕ × String) × Johnson.AtFull.Shape.Row)} {i : ℕ} {pre post : List (ℕ × String)}
    (tied : ∀ (j : ℕ) (o : ℕ × String), Lk.order[j]? = some o → Tied Lk j (tabOf rows o).run)
    (rests : ∀ {γ : Type} (g : S → γ), FieldRests g → ∀ (j : ℕ) (o : ℕ × String) (r : ClaimsRun), Lk.order[j]? = some o →
      claimsRunOf Lk.hear o = some r → ∀ m e z, r m e = .ok z → g z.2 = g e)
    (cores : ∀ (j : ℕ) (o : ℕ × String) (r : ClaimsRun), Lk.order[j]? = some o → claimsRunOf Lk.hear o = some r → RunKeeps r)
    (carries : ∀ (j : ℕ) (o : ℕ × String) (r : ClaimsRun), Lk.order[j]? = some o → claimsRunOf Lk.hear o = some r →
      ∀ n u y, r n u = .ok y → Desc.K9.CF S.lookHeard? u y.2)
    (PT : PlainTies Lk i pre post) {p : Desc.K9.Where} {s : S} {tr : UInt64 × UInt64 × UInt64}
    (empty : ∀ F, s.fork? = some F → Desc.K9.ledgerEmpty F = true)
    (front : K8.k8Front s [⟨[tr], [], [], none⟩] = none)
    (held : ∀ tl funs, s.tl? = some tl → s.funs? = some funs → tl.funsHeld funs = true)
    (heq : ∀ n u, (tabOf rows (i, "K8.equations")).pre n u = eqPreB u)
    (hrow : ∀ t₁, (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne (E.ofTriple tr)⟩] [] = .ok t₁ →
      ∀ o, o ∈ pre ∨ o ∈ post → ∀ n u, Along t₁ u → (tabOf rows o).pre n u = true) :
    cellV p rows Lk.order s [⟨[], drawnOne (E.ofTriple tr)⟩] [] = true := by
  unfold cellV batchVT
  have e1 : (s.fork?.map Desc.K9.ledgerEmpty).getD true = true := by
    cases hF : s.fork? with
    | none => rfl
    | some F => exact empty F hF
  rw [e1, Bool.true_and]
  cases hd : (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne (E.ofTriple tr)⟩] [] with
  | error e => rfl
  | ok t₁ =>
    exact preAll_of_ties tied rests cores carries PT (fun o ho => hrow t₁ hd o (Or.inl ho))
      (fun n u hu => by rw [heq]; exact eqPre_along hd front held hu) (fun o ho => hrow t₁ hd o (Or.inr ho))

/-- What a feed-forward segment's own rounds returned is at u what it was at s. -/
theorem own_along {p : Desc.K9.Where} {s t₁ u : S} {x : E}
    (hd : (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁)
    (h : Along t₁ u) : u.own? = s.own? := by
  obtain ⟨a, ha⟩ := draw_open p s t₁ _ hd
  rw [h.rest S.own? rests_own, draw_is p s t₁ _ a ha hd, set_own]

/-- What the first lookup returned is at u what it was at s. -/
theorem look_along {p : Desc.K9.Where} {s t₁ u : S} {x : E}
    (hd : (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁)
    (h : Along t₁ u) : u.lookHeard? = s.lookHeard? := by
  rw [h.rest S.lookHeard? fieldRests_lookHeard, draw_look p s t₁ x hd]

/-- The ledger at u is a later state of the ledger at s. -/
theorem later_along {p : Desc.K9.Where} {s t₁ u : S} {x : E}
    (hd : (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁)
    (sized : ∀ F, s.fork? = some F → PscRun.Sized F) (h : Along t₁ u) :
    ∀ F, s.fork? = some F → ∃ G, u.fork? = some G ∧ PscRun.Later F G := by
  intro F hF
  obtain ⟨G, hG, k⟩ := (draw_stateKept p s t₁ x hd).side F hF
  have hz := k.later.sized (sized F hF)
  obtain ⟨G', hG', ⟨a1, a2, a3⟩, hz'⟩ := h.later.2 G hG hz
  exact ⟨G', hG', k.later.trans ⟨a1, a2, fun _ => hz', a3⟩⟩

/-- The attention kind's two tests on values pass to a later ledger. -/
theorem valsT_later {A : Attention.Plan} {gl : Forest.Heard} {hd5 : Att.P.Heard} {F G : Fork}
    (lt : PscRun.Later F G) (hv : valsT A gl hd5 F = true) : valsT A gl hd5 G = true := by
  unfold valsT at hv ⊢
  cases e : Att.P.ptsFrom (Att.P.parCOf A).geo gl.zk hd5 F with
  | none =>
    rw [e] at hv
    cases hv
  | some q =>
    rw [e] at hv
    rw [K5Law.ptsFrom_later lt e]
    exact hv

/-- **The attention kind's test at s holds at u.** -/
theorem valsTS_along {A : Attention.Plan} {p : Desc.K9.Where} {s t₁ u : S} {x : E}
    (hd : (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁)
    (sized : ∀ F, s.fork? = some F → PscRun.Sized F) (h : Along t₁ u) (hv : valsTS A s = true) :
    valsTS A u = true := by
  unfold valsTS at hv
  cases hh : s.here with
  | att a =>
    rw [hh] at hv
    cases h5 : a.heard5 with
    | none => simp [h5] at hv
    | some hd5 =>
      cases hg : a.g with
      | none => simp [h5, hg] at hv
      | some gl =>
        have hv' : valsT A gl hd5 a.F = true := by simpa [h5, hg] using hv
        have s5 : s.heard5? = some hd5 := by
          unfold S.heard5?
          rw [hh]
          exact h5
        have sg : s.look? = some gl := by
          unfold S.look?
          rw [hh]
          exact hg
        have sF : s.fork? = some a.F := by
          unfold S.fork?
          rw [hh]
        have u5 : u.heard5? = some hd5 := by
          rw [h.rest S.heard5? rests_heard5, draw_heard5 p s t₁ x hd]
          exact s5
        have ug : u.look? = some gl := by
          rw [h.rest S.look? fieldRests_look, draw_look2 p s t₁ x hd]
          exact sg
        obtain ⟨G, uF, lt⟩ := later_along hd sized h a.F sF
        unfold S.heard5? at u5
        unfold S.look? at ug
        unfold S.fork? at uF
        unfold valsTS
        cases hu : u.here with
        | att a' =>
          rw [hu] at u5 ug uF
          have e5 : a'.heard5 = some hd5 := u5
          have eg : a'.g = some gl := ug
          have eF : a'.F = G := Option.some.inj uF
          show (match a'.heard5, a'.g with
            | some h, some gl => valsT A gl h a'.F
            | _, _ => false) = true
          rw [e5, eg, eF]
          exact valsT_later lt hv'
        | between => rw [hu] at u5; cases u5
        | lay _ => rw [hu] at u5; cases u5
        | head _ => rw [hu] at u5; cases u5
        | fin _ => rw [hu] at u5; cases u5
        | mem _ => rw [hu] at u5; cases u5
  | between => rw [hh] at hv; cases hv
  | lay _ => rw [hh] at hv; cases hv
  | head _ => rw [hh] at hv; cases hv
  | fin _ => rw [hh] at hv; cases hv
  | mem _ => rw [hh] at hv; cases hv

/-! ## Under the library's hypothesis -/

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {k : ℕ} {Lk : Link S ProofFile.Cl}
  {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}

/-- **At the feed-forward segment 2 g.** -/
theorem cellV_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    (Sd : SeatedFree cF Zp (2 * g) k Lk p w) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {s : S} {tr : UInt64 × UInt64 × UInt64}
    (empty : ∀ F, s.fork? = some F → Desc.K9.ledgerEmpty F = true)
    (front : K8.k8Front s [⟨[tr], [], [], none⟩] = none)
    (held : ∀ tl funs, s.tl? = some tl → s.funs? = some funs → tl.funsHeld funs = true)
    (env : OnBytes.Desc.First.K4.Rt.planEnvB Bs.G₀.W.layers s = true) :
    cellV p (rowsLay Bs.G₀.W g) Lk.order s [⟨[], drawnOne (E.ofTriple tr)⟩] [] = true := by
  have hl : 2 * g < 25 := by omega
  obtain ⟨Bs', hB', tied⟩ := tied_lay h hg Sd
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans hB')
  refine cellV_of_ties tied (fun g R => rests_at_head h hl Sd g R) (cores_at_head h hl Sd)
    (carries_at_head h hl Sd)
    (plainTies_lay_at_head h hg Sd) empty front held (fun _ _ => rfl) ?_
  intro t₁ hd o ho n u hu
  have hE : OnBytes.Desc.First.K4.Rt.planEnvB Bs.G₀.W.layers u = true := by
    unfold OnBytes.Desc.First.K4.Rt.planEnvB at env ⊢
    rw [own_along hd hu]
    exact env
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with (rfl | rfl | rfl | rfl | rfl) | rfl
  · rfl
  · rfl
  · exact hE
  · rfl
  · rfl
  · exact hE

/-- **At the attention segment 2 g + 1.** -/
theorem cellV_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    (Sd : SeatedFree cF Zp (2 * g + 1) k Lk p w) {Bs : ProofFile.PureBase} {A : Attention.Plan}
    {q : VerifiableInference.Desc.First.Look.P} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hA : Bs.G₀.W.A[g]? = some A)
    (hq : VerifiableInference.Desc.First.Look.placeAt Bs.G₀.W (2 * g + 1) false = some q) {s : S}
    {tr : UInt64 × UInt64 × UInt64} (empty : ∀ F, s.fork? = some F → Desc.K9.ledgerEmpty F = true)
    (front : K8.k8Front s [⟨[tr], [], [], none⟩] = none)
    (held : ∀ tl funs, s.tl? = some tl → s.funs? = some funs → tl.funsHeld funs = true)
    (sized : ∀ F, s.fork? = some F → PscRun.Sized F) (vals : valsTS A s = true) :
    cellV p (rowsAtt A q.lm) Lk.order s [⟨[], drawnOne (E.ofTriple tr)⟩] [] = true := by
  have hl : 2 * g + 1 < 25 := by omega
  obtain ⟨Bs', A', q', hB', hA', hq', tied⟩ := tied_att h hg Sd
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans hB')
  obtain rfl : A = A' := Option.some.inj (hA.symm.trans hA')
  obtain rfl : q = q' := Option.some.inj (hq.symm.trans hq')
  refine cellV_of_ties tied (fun g R => rests_at_head h hl Sd g R) (cores_at_head h hl Sd)
    (carries_at_head h hl Sd)
    (plainTies_att_at_head h hg Sd) empty front held (fun _ _ => rfl) ?_
  intro t₁ hd o ho n u hu
  have hE : valsTS A u = true := valsTS_along hd sized hu vals
  simp only [attPre, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · exact hE
  · exact hE
  · exact hE
  · exact hE
  · exact hE
  · rfl
  · rfl

/-- **At the last segment.** -/
theorem cellV_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Sd : SeatedFree cF Zp 24 k Lk p w)
    {Bs : ProofFile.PureBase} {iU3 : ℕ} {q : VerifiableInference.Desc.First.Look.P}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (hU : Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3)
    (hq : VerifiableInference.Desc.First.Look.placeAt Bs.G₀.W 24 false = some q) {s : S}
    {tr : UInt64 × UInt64 × UInt64} (empty : ∀ F, s.fork? = some F → Desc.K9.ledgerEmpty F = true)
    (front : K8.k8Front s [⟨[tr], [], [], none⟩] = none)
    (held : ∀ tl funs, s.tl? = some tl → s.funs? = some funs → tl.funsHeld funs = true)
    (ends : endsS (Kinds.Head.parOf Bs.G₀.W.hS (Kinds.Head.Law.workAtW Bs.G₀.W)) s = true) :
    cellV p (rowsHead Bs.G₀.W iU3 q.lm) Lk.order s [⟨[], drawnOne (E.ofTriple tr)⟩] [] = true := by
  have hl : 24 < 25 := by omega
  obtain ⟨Bs', iU3', q', hB', hU', hq', tied⟩ := tied_head h Sd
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans hB')
  obtain rfl : iU3 = iU3' := Option.some.inj (hU.symm.trans hU')
  obtain rfl : q = q' := Option.some.inj (hq.symm.trans hq')
  refine cellV_of_ties tied (fun g R => rests_at_head h hl Sd g R) (cores_at_head h hl Sd)
    (carries_at_head h hl Sd)
    (plainTies_head_at_head h Sd) empty front held (fun _ _ => rfl) ?_
  intro t₁ hd o ho n u hu
  have hE : endsS (Kinds.Head.parOf Bs.G₀.W.hS (Kinds.Head.Law.workAtW Bs.G₀.W)) u = true := by
    unfold endsS at ends ⊢
    rw [look_along hd hu]
    exact ends
  simp only [headPre, headPost, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
  · rfl
  · rfl
  · exact hE
  · exact hE
  · exact hE
  · rfl
  · rfl
  · rfl
  · exact hE
  · rfl

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.preAllT_true
#print axioms ProofFile.Honest.K9.preAllT_append
#print axioms ProofFile.Honest.K9.run_of_table
#print axioms ProofFile.Honest.K9.along_step
#print axioms ProofFile.Honest.K9.front_step
#print axioms ProofFile.Honest.K9.preAll_of_ties
#print axioms ProofFile.Honest.K9.eqPre_along
#print axioms ProofFile.Honest.K9.cellV_of_ties
#print axioms ProofFile.Honest.K9.own_along
#print axioms ProofFile.Honest.K9.look_along
#print axioms ProofFile.Honest.K9.later_along
#print axioms ProofFile.Honest.K9.valsT_later
#print axioms ProofFile.Honest.K9.valsTS_along
#print axioms ProofFile.Honest.K9.cellV_lay
#print axioms ProofFile.Honest.K9.cellV_att
#print axioms ProofFile.Honest.K9.cellV_head
