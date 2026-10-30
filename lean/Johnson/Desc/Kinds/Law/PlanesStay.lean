-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/PlanesStay.lean: the output head's row's clause on "planes" AT THE RECORD AT
WHICH THE LOOKUP'S RUN "planes" RUNS, from what lies behind piece 5 of the head's link and a
relation between the two records.

Law/HeadPlanesFive.lean and Law/HeadPlanesTie.lean speak at the record right behind the block that
makes the head's tables (piece 5). The run "planes" runs later: behind the smallness test's draw,
the digits' sending, the digits' lookup, the merge and the batching's own rounds, and behind five
other runs of claims. Here it is said what of the record the law on "planes" reads (SamePlanes),
that this is enough, which blocks and runs are shown to leave it, and which are owed.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law).
  SamePlanes s s': the request's words and the heard reply are the same; and where s stands in the
      head's link, so does s', with the same: opened; what the head heard (x); the tables (t); what
      the lookup left (lookHeard); and, of the record of the smallness test, the matrices, the list
      of tables, the number of matrices and the arrays' numbers. NOTHING IS ASKED OF THE LEDGER.
  SamePlanes.refl, SamePlanes.trans.
  lie_stays, look_stays: TabsLie, and "the two homes of what the lookup returned agree", go over.
  same_laid, same_putLink, same_putFork; commit_same: a yes of K1.commitAtS (a sending) leaves it.
  same_putTl; k8_same: a yes of the smallness test's block (the draw: First.K8.approximateRangeProofDrawKind at First.K8.atS)
      leaves it.
  k6_runs_same: the head's own four runs of claims leave it.
  front_same: every run of the head's two lists of adding leaves it, IF the lookup's runs and the
      merge's run do (Law/HeadRunsCarry.lean's headRuns_carry at this relation).
  look_planes_run: at the head's link the block lookClaims W l (Johnson/Stored/HeadAddsAtS.lean)
      states the run "planes" at lmbH and at the head's readers at the plan's array of the reads.
  run_array: a yes of that run gives the array of the reads in the record's ledger, with a column.
  rowPlanes_at_run: THE ROW'S CLAUSE AT THE RUN'S OWN RECORD sP: the run's claims are the three
      forms of which K6OutP speaks; and K6OutP IFF K6InP, from the smallness test's tie at the
      record s3 behind piece 5.
  rowPlanes_run_steps: the same from Block.step of the two blocks at pieces 4 and 5.

Every letter under "there is", and the clause that pins it. lie_stays: o' by TabsLie.here.
run_array, rowPlanes_at_run: o' by TabsLie.here; tr by the ledger's list at the array's number; r by
callerReaders. rowPlanes_run_steps: o, cov, x, t by TabsLie's fields at s3.
Letters under "for all" that one premise alone reads: n (the run does not read it); claim.

WHO OWES SamePlanes, BLOCK BY BLOCK, from behind piece 5 to the run (the head's link of the first
chain). Shown here: a sending (pieces 5 and 7: commit_same); the smallness test's draw (piece 6:
k8_same); the head's own runs "norm", "join", "policy". OWED, each by its kind's files: the digits'
lookup at piece 8 and the step without a round behind it · the merge at piece 9 and the step behind
it · the batching's own rounds at piece 10 · the lookup's runs "objects" and "guests", which stand
in front of "planes" in the head's order. No text of these is opened here.

Premises that nobody pays here. SamePlanes s3 sP. And Law/HeadPlanesTie.lean's: the tie at s3 · hK
(the plan's number of reads is at most the array's width, AT sP's LEDGER) · the world at row 0 · h4
· hsh. htr and hK0 have fallen: the run's yes gives them.
Limits. The tie is asked at s3, the record in front of the smallness test's block; the cells are
named off s3's record of that test. No values are shown at which the premises hold together. No
draw, no error term, nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.HeadPlanesTie
import Johnson.Desc.Kinds.Law.HeadPlanesFive
import Johnson.Desc.Kinds.Law.HeadRunsCarry
import Johnson.Desc.Kinds.Law.PlanesRefuses
import Johnson.Desc.First.Look.K3CallerAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model OnBytes.K.Kc
open Cb Cb.Fo Cb.Fo.NumsEq TwV Fo Meaning.Planes
open Cb.Fo.Pin
open OnBytes.Tie.Pv.Tail Cb.Pv.Tail
open Meaning.Reads (cellA)
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.K8 (TieOf TieAt)
open VerifiableInference.Desc.K8
open Planes

/-- **The second record holds all that the law on "planes" reads of the first.** Nothing is asked of
the ledger. -/
structure SamePlanes (s s' : S) : Prop where
  req : s'.req = s.req
  reply : s'.out.reply = s.out.reply
  head : ∀ o, s.here = .head o → ∃ o', s'.here = .head o' ∧ o'.opened = o.opened ∧ o'.x = o.x ∧
    o'.t = o.t ∧ o'.lookHeard = o.lookHeard ∧ o'.tl.mats = o.tl.mats ∧ o'.tl.funs = o.tl.funs ∧
    o'.tl.NM = o.tl.NM ∧ o'.tl.ix = o.tl.ix

theorem SamePlanes.refl (s : S) : SamePlanes s s :=
  ⟨rfl, rfl, fun o h => ⟨o, h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem SamePlanes.trans {s s' s'' : S} (a : SamePlanes s s') (b : SamePlanes s' s'') :
    SamePlanes s s'' := by
  refine ⟨b.req.trans a.req, b.reply.trans a.reply, fun o h => ?_⟩
  obtain ⟨o1, h1, a1, a2, a3, a4, a5, a6, a7, a8⟩ := a.head o h
  obtain ⟨o2, h2, b1, b2, b3, b4, b5, b6, b7, b8⟩ := b.head o1 h1
  exact ⟨o2, h2, b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6,
    b7.trans a7, b8.trans a8⟩

/-- The covered positions read the request's words and the heard reply alone. -/
theorem covered_same {s s' : S} (a : SamePlanes s s') (T V : Nat) :
    s'.covered T V = s.covered T V := by
  unfold S.covered S.replyTok? S.coveredAt
  rw [a.req, a.reply]

section
variable {h : Model.Head.Shape} {L : Model.Head.HL} {hp : Model.Head.HPlanH2} {s s' : S}
  {o : HeadOwn} {cov : Model.Head.Covered} {x : Model.Head.Heard} {t : Model.Head.Tables}

/-- **The tables lie in the second record as in the first.** -/
theorem lie_stays (Z : TabsLie h L hp s o cov x t) (a : SamePlanes s s') :
    ∃ o', TabsLie h L hp s' o' cov x t ∧ o'.lookHeard = o.lookHeard := by
  obtain ⟨o', h', a1, a2, a3, a4, a5, a6, a7, a8⟩ := a.head o Z.here
  exact ⟨o', ⟨h', a1.trans Z.opened, (covered_same a h.T h.V).trans Z.covered, a2.trans Z.heard,
    a3.trans Z.laid, Z.made, a5.trans Z.mats, a6.trans Z.funs, a7.trans Z.nm, a8.trans Z.ix⟩, a4⟩

/-- The two homes of what the lookup returned agree in the second record as in the first. -/
theorem look_stays (Z : TabsLie h L hp s o cov x t) (a : SamePlanes s s')
    (hlk : s.look? = s.lookHeard?) : s'.look? = s'.lookHeard? := by
  obtain ⟨o', Z', e⟩ := lie_stays Z a
  have h1 : s.lookHeard? = some x.g1 := lookHeard_of_lie Z hlk
  have h2 : o.lookHeard = some x.g1 := by
    simpa [S.lookHeard?, Z.here, Z.opened] using h1
  simp [S.look?, S.lookHeard?, Z'.here, Z'.opened, Z'.heard, e, h2]

end

/-! ## Who leaves it -/

theorem same_laid {Lt : Type} (s : S) (d) : SamePlanes s (K1.laid (L := Lt) s d) :=
  ⟨rfl, rfl, fun o h => ⟨o, h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem same_putLink (s : S) (L : LinkCtx) : SamePlanes s (s.putLink L) := by
  refine ⟨?_, ?_, fun o h => ?_⟩
  · unfold S.putLink
    split <;> (try split) <;> rfl
  · unfold S.putLink
    split <;> (try split) <;> rfl
  · by_cases ho : o.opened = true
    · exact ⟨{ o with L := L }, by simp [S.putLink, h, ho], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨o, by simp [S.putLink, h, ho], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem same_putFork (s : S) (F : Fork) : SamePlanes s (s.putFork F) := by
  refine ⟨?_, ?_, fun o h => ?_⟩
  · unfold S.putFork
    split <;> (try split) <;> rfl
  · unfold S.putFork
    split <;> (try split) <;> rfl
  · by_cases ho : o.opened = true
    · exact ⟨{ o with F := F }, by simp [S.putFork, h, ho], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨o, by simp [S.putFork, h, ho], rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **A yes of a sending's block leaves it.** -/
theorem commit_same {Cl : Type} {P : K1.Par} {link moment : Nat} {arrays : Option (List Nat)}
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : (K1.commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    SamePlanes s s' := by
  simp only [K1.commitAtS] at hd
  split at hd
  · obtain ⟨y, _, rfl⟩ := map_ok hd
    exact ((same_laid s _).trans (same_putLink _ _)).trans (same_putFork _ _)
  · cases hd

/-- Laying a record of the smallness test with the same matrices, list of tables, number of matrices
and arrays' numbers leaves it. -/
theorem same_putTl (s : S) {tl tl' : HTailF2} (ht : s.tl? = some tl) (e1 : tl'.mats = tl.mats)
    (e2 : tl'.funs = tl.funs) (e3 : tl'.NM = tl.NM) (e4 : tl'.ix = tl.ix) :
    SamePlanes s (s.putTl tl') := by
  refine ⟨?_, ?_, fun o h => ?_⟩
  · unfold S.putTl
    split <;> (try split) <;> rfl
  · unfold S.putTl
    split <;> (try split) <;> rfl
  · by_cases ho : o.opened = true
    · have et : o.tl = tl := by
        simpa [S.tl?, h, ho] using ht
      subst et
      exact ⟨{ o with tl := tl' }, by simp [S.putTl, h, ho], rfl, rfl, rfl, rfl, e1, e2, e3, e4⟩
    · simp [S.tl?, h, ho] at ht

/-- **A yes of the smallness test's block (the draw) leaves it.** -/
theorem k8_same {Cl : Type} (p : First.K8.Par) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (hd : (First.K8.approximateRangeProofDrawKind (Cl := Cl) First.K8.atS p).decide s rs gs = .ok s') :
    SamePlanes s s' := by
  obtain ⟨r, _, _, _, _, _, _, _, _, _, hl⟩ := First.K8.decide_ok First.K8.atS p s s' rs gs hd
  obtain ⟨tl, ht, rfl⟩ := First.K8.atS_lay s s' _ _ hl
  exact same_putTl s ht rfl rfl rfl rfl

/-- **The head's own four runs of claims leave it.** -/
theorem k6_runs_same (W : OnBytes.Model.Verify.Public) (l : Nat) (b6 : Block S Claim)
    (hb : blockClaims W l = some b6) : RunsHave SamePlanes b6 :=
  k6_have SamePlanes W l SamePlanes.refl (fun s F g _ _ => same_putFork s _) b6 hb

/-- **Every run of the head's two lists of adding leaves it, if the lookup's runs and the merge's
run do.** -/
theorem front_same (W : OnBytes.Model.Verify.Public) (l : Nat)
    (hlook : ∀ b, lookClaims W l = some b → RunsHave SamePlanes b)
    (hmerge : ∀ n s y, Johnson.Desc.First.ForkMerge.headMergeClaim n s = .ok y →
      SamePlanes s y.2)
    (runs : List RunAtS) (h : frontRuns W l = some runs ∨ backRuns W l = some runs) :
    ∀ r ∈ runs, ∀ n s cl s', r.2 n s = .ok (cl, s') → SamePlanes s s' :=
  headRuns_carry SamePlanes W l SamePlanes.refl (fun s F g _ _ => same_putFork s _) hlook hmerge
    runs h

/-! ## The run -/

/-- **At the head's link the lookup's block, as the head's adding calls it, states the run "planes"
at lmbH and at the head's readers at the plan's array of the reads.** -/
theorem look_planes_run {W : OnBytes.Model.Verify.Public} {l : Nat}
    (hl : l = (if W.p4 then 2 else 1) * W.NGr) {b : Block S Claim}
    (hb : lookClaims W l = some b) :
    ("planes", K3.planesRun (K3.seatCalls asClaim) W.hS.lmbH
      (callerReaders (planesAt (readsOf W)))) ∈ b.claims := by
  unfold lookClaims at hb
  cases hU : W.H.tl.ix.U.getD 2 none with
  | none => simp [hU] at hb
  | some i =>
    cases hp : First.Look.placeAt W l false with
    | none => simp [hU, hp] at hb
    | some p =>
      simp only [hU, hp, Option.bind_eq_bind, Option.bind_some, pure, Option.some.injEq] at hb
      subst hb
      obtain ⟨pl, hpl, rfl⟩ := Option.map_eq_some_iff.mp hp
      rw [hl] at hpl
      have e1 : (First.Look.P.ofPlace (Params.settingOf W.P.frame) false pl).lm = W.hS.lmbH :=
        (First.Look.lookAt_head hpl).2.2.1
      have e2 : readsOf W = i := by
        unfold readsOf
        rw [hU]
        rfl
      rw [← e1, e2]
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- **A yes of the run gives the array of the reads in the record's ledger, with a column.** -/
theorem run_array {Cl : Type} (claim : Aff → Cl) (W : OnBytes.Model.Verify.Public) (lm n : Nat)
    (sP : S) (y : List Cl × S)
    (hy : K3.planesRun (K3.seatCalls claim) lm (callerReaders (planesAt (readsOf W))) n sP =
      .ok y) :
    ∃ (o' : HeadOwn) (tr : HTree), sP.here = .head o' ∧ sP.fork? = some o'.F ∧
      o'.F.trees[readsOf W]? = some tr ∧ tr.K ≠ 0 := by
  obtain ⟨_, r, _, hr, _⟩ := planesRun_at claim W lm n sP y hy
  unfold callerReaders at hr
  obtain ⟨f, hf, _⟩ := Option.map_eq_some_iff.mp hr
  obtain ⟨o', F, _, tr, ho, hF, _, htr, hK, _⟩ := planesAt_some (readsOf W) sP f hf
  have e : F = o'.F := by
    unfold S.fork? at hF
    rw [ho] at hF
    dsimp only at hF
    split at hF
    · exact (Option.some.inj hF).symm
    · cases hF
  subst e
  exact ⟨o', tr, ho, hF, htr, hK⟩

/-- **The row's clause on "planes" at the run's own record.** s3: the record behind piece 5, in
which the tables lie; sP: the record at which the run runs. -/
theorem rowPlanes_at_run {pol KL : ByteArray} {layout : Option ByteArray}
    {W : OnBytes.Model.Verify.Public} (hW : Verify.publicOf pol KL layout = .ok W) {s3 sP : S}
    {o : HeadOwn} {cov : Model.Head.Covered} {x : Model.Head.Heard} {t : Model.Head.Tables}
    (Z : TabsLie W.hS W.HLy W.H s3 o cov x t) (hlk : s3.look? = s3.lookHeard?)
    (hst : SamePlanes s3 sP) {Cl : Type} (claim : Aff → Cl) (n : Nat) (y : List Cl × S)
    (hy : K3.planesRun (K3.seatCalls claim) W.hS.lmbH (callerReaders (planesAt (readsOf W))) n
      sP = .ok y) :
    ∃ o' tr r, TabsLie W.hS W.HLy W.H sP o' cov x t ∧ o'.F.trees[readsOf W]? = some tr ∧
      tr.K ≠ 0 ∧ callerReaders (planesAt (readsOf W)) sP = some r ∧
      y.1 = (planeForms x.g1 W.hS.lmbH (fun e col => (r.1 e col).getD {})
        fun col => (r.2 col).getD {}).toList.map claim ∧
      (x.g1.shape = W.HLy.fs → W.H.nU.getD 2 0 ≤ tr.K →
        ∀ (Wt : Type) (A : Wt → Nat → Nat → Nat → Cb.Gl.E) (w : Wt), TieAt A s3 w →
          ∀ (ν : _root_.Fo.Pl → Cb.Gl.E) (Wd : World Cb.Gl.E),
            (∀ pos < tr.K, Wd.entry (readsOf W) 0 pos = A w (readsOf W) 0 pos) →
            (∀ r < 2 ^ W.hS.lmbH, ∀ c < planeCols x.g1.shape W.hS.lmbH,
              cellA o.tl (A w) (W.hS.NHf + 1 + 1) r c = ν (.cell r c)) →
            (K6OutP W W.hS.lmbH sP Wd ↔ K6InP W.hS.lmbH sP Wd ν)) := by
  obtain ⟨o', Z', _⟩ := lie_stays Z hst
  have hlk' := look_stays Z hst hlk
  obtain ⟨gk, r, hgk, hr, hy1⟩ := planesRun_at claim W W.hS.lmbH n sP y hy
  obtain rfl : x.g1 = gk := Option.some.inj ((lookHeard_of_lie Z' hlk').symm.trans hgk)
  obtain ⟨o2, tr, ho2, _, htr, hK0⟩ := run_array claim W W.hS.lmbH n sP y hy
  have eo : o2 = o' := by
    have := ho2.symm.trans Z'.here
    cases this
    rfl
  subst eo
  refine ⟨o2, tr, r, Z', htr, hK0, hr, hy1, fun hsh hK Wt A w htie ν Wd hWd h4 => ?_⟩
  obtain ⟨tl, htl, ht⟩ := htie
  obtain rfl : o.tl = tl := Option.some.inj ((tl_of_lie Z).symm.trans htl)
  have eU : Port.u3Of o.tl = readsOf W := u3_of_lie Z
  have hA := k6_readsAll_of_tie Z ht hK (Nat.le_of_eq (k6_NM hW).symm) Wd.entry
    (by rw [eU]; exact hWd)
  rw [eU, Z.mats, ← Z'.mats, Z.funs, ← Z'.funs] at hA
  exact rowPlanes_public hW Z' hlk' hsh htr hK0 ν h4 Wd hA

/-- **The same from Block.step of the two blocks at pieces 4 and 5.** -/
theorem rowPlanes_run_steps {pol KL : ByteArray} {layout : Option ByteArray}
    {W : OnBytes.Model.Verify.Public} (hW : Verify.publicOf pol KL layout = .ok W) (l : Nat)
    {ms : List (Nat × Nat)} {b4 : Block S Claim} (hb : seatedClaims W l ms = some b4)
    {q : Params.First} {gp : _root_.Desc.Plain.GPar} {moment : Nat} {arrays : Option (List Nat)}
    {name : String} {s0 s1 s3 sP : S} {ft : Nat} {rs0 rs : List Fmt.RoundView} {cols0 cols : List OpenedColumn}
    {n4 n5 : Nat} (h4 : b4.step ft s0 rs0 cols0 = .ok (s1, n4))
    (h5 : ((K1.laterAt q gp l 5 moment arrays).andThen name
      (ReadsQuiet.head ⟨⟨1, some l, 5, .K1⟩, W.hS, W.HLy, W.H⟩)).step ft s1 rs cols =
        .ok (s3, n5))
    (hst : SamePlanes s3 sP) {Cl : Type} (claim : Aff → Cl) (n : Nat) (y : List Cl × S)
    (hy : K3.planesRun (K3.seatCalls claim) W.hS.lmbH (callerReaders (planesAt (readsOf W))) n
      sP = .ok y) :
    ∃ o cov x t, TabsLie W.hS W.HLy W.H s3 o cov x t ∧
    ∃ o' tr r, TabsLie W.hS W.HLy W.H sP o' cov x t ∧ o'.F.trees[readsOf W]? = some tr ∧
      tr.K ≠ 0 ∧ callerReaders (planesAt (readsOf W)) sP = some r ∧
      y.1 = (planeForms x.g1 W.hS.lmbH (fun e col => (r.1 e col).getD {})
        fun col => (r.2 col).getD {}).toList.map claim ∧
      (x.g1.shape = W.HLy.fs → W.H.nU.getD 2 0 ≤ tr.K →
        ∀ (Wt : Type) (A : Wt → Nat → Nat → Nat → Cb.Gl.E) (w : Wt), TieAt A s3 w →
          ∀ (ν : _root_.Fo.Pl → Cb.Gl.E) (Wd : World Cb.Gl.E),
            (∀ pos < tr.K, Wd.entry (readsOf W) 0 pos = A w (readsOf W) 0 pos) →
            (∀ r < 2 ^ W.hS.lmbH, ∀ c < planeCols x.g1.shape W.hS.lmbH,
              cellA o.tl (A w) (W.hS.NHf + 1 + 1) r c = ν (.cell r c)) →
            (K6OutP W W.hS.lmbH sP Wd ↔ K6InP W.hS.lmbH sP Wd ν)) := by
  obtain ⟨hlk, o, cov, x, t, Z, _⟩ := rowPlanes_five_byStep W l hb h4 h5
  exact ⟨o, cov, x, t, Z, rowPlanes_at_run hW Z hlk hst claim n y hy⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.lie_stays
#print axioms VerifiableInference.Desc.Kinds.Head.Law.look_stays
#print axioms VerifiableInference.Desc.Kinds.Head.Law.commit_same
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k8_same
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_runs_same
#print axioms VerifiableInference.Desc.Kinds.Head.Law.front_same
#print axioms VerifiableInference.Desc.Kinds.Head.Law.look_planes_run
#print axioms VerifiableInference.Desc.Kinds.Head.Law.run_array
#print axioms VerifiableInference.Desc.Kinds.Head.Law.rowPlanes_at_run
#print axioms VerifiableInference.Desc.Kinds.Head.Law.rowPlanes_run_steps
