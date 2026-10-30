-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/PassSmall.lean: one whole use of `forms_back` and `formsIn_fwd`
(Reads/FormsPass.lean): "forms" and its public test, at a run of the output head's own claims, pass
the approximate range proof's sub-protocol in the output head's segment, with no premise on the pass
left.

Why. `Fwd`, `Rides` and `More` are premises of the two laws on passing. Where the approximate range
proof's sub-protocol accepts, it writes its own part of the state and nothing else
(`decide_atS_iff`, Johnson/Desc/First/K8/HearMeans.lean). So all three can be paid there.

What is shown.
  `kept_withTables`: `KeptMore` passes to the two states with the reads' tables laid silently.
  `fwd_both`: **`Fwd` at the readers of a segment, under `KeptMore` in both directions, with no
    premise on whether the run itself or the second reader answers.**
  `reader_head`, `forms_head`: where a reader answers at such a run, the state stands in the output
    head's segment, opened.
  `keptMore_tl`: two states of the output head's segment that differ in the approximate range
    proof's part alone, with one list of matrices, one list of tables and one number of matrices.
  `seg_head`, `rides_same`, `more_same`: the open segment's part at such a state; `Rides` and `More`
    between two parts with one context, one ledger and one statement with its book.
  `pass_small`: what the pass gives, in one: both parts, `Fwd`, `Rides`, `More`.
  `pass_small_test`: **the test in front gives the test behind.**
  `pass_small_back`: **under the test in front, "forms" behind gives "forms" in front.**

Premises of the last two: the sub-protocol's accept; the name is not "K8.equations"; the run that
the segment states under the name is one of the kind's own (`runsBy`); the segment's second reader
is `k6Silent`. These speak of the segment and its readers, not of the pass.

Limits. The three own runs alone: not "join". No state is shown at which the sub-protocol accepts
and the test in front holds. Nothing on soundness.


-/
import Johnson.Desc.Reads.FwdHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.Pass

open OnBytes.Model (HTailF2)
open OnBytes.PscRun (Later)
open VerifiableInference.Desc (Claim Link)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K9 (Part segAt? readerOf RunOf LinkHoles statesOfLink readersOfLink
  formsIn lateOk mergeOf)
open VerifiableInference.Desc.Sound (MsgQ Rides formsQ)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law (withTables withTables_iff k6Silent)
open VerifiableInference.Reads.AtSeat (KeptAll covered_congr)

/-- KeptMore passes to the two states with the tables laid silently. -/
theorem kept_withTables {iU3 : ℕ} {s s' e : S} (k : KeptMore iU3 s s')
    (P : VerifiableInference.Desc.K8.ReadsQuiet.PH) (hw : withTables P s = some e) :
    ∃ e', withTables P s' = some e' ∧ KeptMore iU3 e e' := by
  obtain ⟨a, cov, x, tt, ha, hop, hcov, hx, ht, rfl⟩ := (withTables_iff P s e).1 hw
  obtain ⟨o', ho', a1, a2, a3, _, a5, a6, a7, a8⟩ := k.all.own a ha
  refine ⟨{ s' with here := .head { o' with t := some tt } },
    (withTables_iff P s' _).2 ⟨o', cov, x, tt, ho', a1.trans hop,
      (covered_congr k.all.req k.all.reply _ _).trans hcov, a2.trans hx, ht, rfl⟩, ?_⟩
  refine ⟨⟨k.all.req, k.all.reply, fun o ho => ?_⟩, fun o1 o2 h1 h2 => ?_, fun o1 o2 h1 h2 => ?_,
    fun o1 o2 h1 h2 => ?_⟩
  · obtain rfl : { a with t := some tt } = o := VerifiableInference.Desc.First.Here.head.inj ho
    exact ⟨{ o' with t := some tt }, rfl, a1, a2, a3, rfl, a5, a6, a7, a8⟩
  · obtain rfl : { a with t := some tt } = o1 := VerifiableInference.Desc.First.Here.head.inj h1
    obtain rfl : { o' with t := some tt } = o2 := VerifiableInference.Desc.First.Here.head.inj h2
    exact k.sq a o' ha ho'
  · obtain rfl : { a with t := some tt } = o1 := VerifiableInference.Desc.First.Here.head.inj h1
    obtain rfl : { o' with t := some tt } = o2 := VerifiableInference.Desc.First.Here.head.inj h2
    exact k.later a o' ha ho'
  · obtain rfl : { a with t := some tt } = o1 := VerifiableInference.Desc.First.Here.head.inj h1
    obtain rfl : { o' with t := some tt } = o2 := VerifiableInference.Desc.First.Here.head.inj h2
    exact k.rows a o' ha ho'

section
variable {names : List String} {runs : Given → Behind → Places → List (String × List Form)}
  {keys : Given → Behind → Places → List Form} {toCl : Form → Claim} {p : Par}
  {h : OnBytes.Model.Head.Shape} {iU3 : ℕ}

/-- **Fwd under KeptMore in both directions.** -/
theorem fwd_both {s s' : S} (H : LinkHoles) (l : Link S Claim)
    (P : VerifiableInference.Desc.K8.ReadsQuiet.PH) (b : ℕ) {name : String}
    (hne : (name == "K8.equations") = false)
    (hst : ∀ r, ((statesOfLink l b).find? fun r => r.1 == name) = some r →
      r ∈ runsBy names runs keys toCl p (seatAt h iU3))
    (hsil : H.silent = k6Silent P (statesOfLink l)) (k : KeptMore iU3 s s')
    (k' : KeptMore iU3 s' s) : Fwd (readersOfLink H l) b name s s' := by
  cases h1 : readerOf (statesOfLink l) b name s with
  | some R₁ => exact fwd_of_run H l b hne hst k (by rw [h1]; rfl)
  | none =>
    have h2 : readerOf (statesOfLink l) b name s' = none := by
      cases h2 : readerOf (statesOfLink l) b name s' with
      | none => rfl
      | some R' =>
        have h3 := reader_fwd k' (statesOfLink l) b name hst h2
        rw [h1] at h3
        cases h3
    intro R hR
    have hR' : (if (name == "K8.equations") = true then H.small s
      else
        match readerOf (statesOfLink l) b name s with
        | some R => some R
        | Option.none => H.silent b name s) = some R := hR
    rw [hne, h1, hsil] at hR'
    have hR'' : (withTables P s).bind (readerOf (statesOfLink l) b name) = some R := hR'
    obtain ⟨e, he, h4⟩ := Option.bind_eq_some_iff.1 hR''
    obtain ⟨e', he', ke⟩ := kept_withTables k P he
    show (if (name == "K8.equations") = true then H.small s'
      else
        match readerOf (statesOfLink l) b name s' with
        | some R => some R
        | Option.none => H.silent b name s') = some R
    rw [hne, h2, hsil]
    show (withTables P s').bind (readerOf (statesOfLink l) b name) = some R
    rw [he', Option.bind_some]
    exact reader_fwd ke (statesOfLink l) b name hst h4

/-- Where the run's reader answers, the state stands in the output head's segment, opened. -/
theorem reader_head {s : S} (states : ℕ → List (RunOf S)) (b : ℕ) (name : String)
    (hst : ∀ r, ((states b).find? fun r => r.1 == name) = some r →
      r ∈ runsBy names runs keys toCl p (seatAt h iU3))
    {R : VerifiableInference.Desc.K9.Read} (hR : readerOf states b name s = some R) :
    ∃ o, s.here = .head o ∧ o.opened = true := by
  unfold readerOf at hR
  obtain ⟨r, hf, hR⟩ := Option.bind_eq_some_iff.1 hR
  have hc := hst r hf
  cases hz : r.2 0 s with
  | error e =>
    rw [hz] at hR
    cases hR
  | ok z =>
    obtain ⟨g, bh, pl, fs, hl, -, -⟩ := VerifiableInference.Reads.AtSeat.letters_of_run hc hz
    obtain ⟨o, ho⟩ := head_of_letters hl
    refine ⟨o, ho, ?_⟩
    by_cases hop : o.opened = true
    · exact hop
    · have hF : s.fork? = none := by
        unfold S.fork?
        rw [ho]
        simp [hop]
      rw [hz, hF] at hR
      cases hR

/-- The like for the readers of a segment. -/
theorem forms_head {s : S} (H : LinkHoles) (l : Link S Claim)
    (P : VerifiableInference.Desc.K8.ReadsQuiet.PH) (b : ℕ) {name : String}
    (hne : (name == "K8.equations") = false)
    (hst : ∀ r, ((statesOfLink l b).find? fun r => r.1 == name) = some r →
      r ∈ runsBy names runs keys toCl p (seatAt h iU3))
    (hsil : H.silent = k6Silent P (statesOfLink l)) {R : VerifiableInference.Desc.K9.Read}
    (hR : (readersOfLink H l).forms b name s = some R) :
    ∃ o, s.here = .head o ∧ o.opened = true := by
  cases h1 : readerOf (statesOfLink l) b name s with
  | some R₁ => exact reader_head (statesOfLink l) b name hst h1
  | none =>
    have hR' : (if (name == "K8.equations") = true then H.small s
      else
        match readerOf (statesOfLink l) b name s with
        | some R => some R
        | Option.none => H.silent b name s) = some R := hR
    rw [hne, h1, hsil] at hR'
    have hR'' : (withTables P s).bind (readerOf (statesOfLink l) b name) = some R := hR'
    obtain ⟨e, he, _⟩ := Option.bind_eq_some_iff.1 hR''
    obtain ⟨a, _, _, _, ha, hop, _⟩ := (withTables_iff P s e).1 he
    exact ⟨a, ha, hop⟩

end

/-- Two states that differ in the approximate range proof's part alone. -/
theorem keptMore_tl (iU3 : ℕ) (s : S) (o : HeadOwn) (t1 t2 : HTailF2)
    (h1 : t2.mats = t1.mats) (h2 : t2.funs = t1.funs) (h3 : t2.NM = t1.NM) :
    KeptMore iU3 { s with here := .head { o with tl := t1 } }
      { s with here := .head { o with tl := t2 } } := by
  refine ⟨⟨rfl, rfl, fun o1 e1 => ?_⟩, fun o1 o2 e1 e2 => ?_, fun o1 o2 e1 e2 => ?_,
    fun o1 o2 e1 e2 => ?_⟩
  · obtain rfl : { o with tl := t1 } = o1 := VerifiableInference.Desc.First.Here.head.inj e1
    exact ⟨{ o with tl := t2 }, rfl, rfl, rfl, rfl, rfl, h1, h2, h3, rfl⟩
  · obtain rfl : { o with tl := t1 } = o1 := VerifiableInference.Desc.First.Here.head.inj e1
    obtain rfl : { o with tl := t2 } = o2 := VerifiableInference.Desc.First.Here.head.inj e2
    rfl
  · obtain rfl : { o with tl := t1 } = o1 := VerifiableInference.Desc.First.Here.head.inj e1
    obtain rfl : { o with tl := t2 } = o2 := VerifiableInference.Desc.First.Here.head.inj e2
    exact Later.refl _
  · obtain rfl : { o with tl := t1 } = o1 := VerifiableInference.Desc.First.Here.head.inj e1
    obtain rfl : { o with tl := t2 } = o2 := VerifiableInference.Desc.First.Here.head.inj e2
    exact fun _ => rfl

/-- The open segment's part at an opened state of the output head's segment. -/
theorem seg_head {s : S} {o : HeadOwn} (ho : s.here = .head o) (hop : o.opened = true) :
    ∃ a, segAt? s = some a ∧ a.L = o.L ∧ a.F = o.F ∧ a.d.st = s.st ∧ a.d.book = s.book := by
  have hL : s.link? = some o.L := by
    unfold S.link?
    rw [ho]
    simp [hop]
  have hF : s.fork? = some o.F := by
    unfold S.fork?
    rw [ho]
    simp [hop]
  have hT : s.tl? = some o.tl := by
    unfold S.tl?
    rw [ho]
    simp [hop]
  unfold segAt?
  rw [hL, hF, hT]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-- Two parts with one context, one ledger and one statement with its book. -/
theorem rides_same (own : List (ℕ × ℕ)) {a b : Part} (hL : b.L = a.L) (hF : b.F = a.F)
    (hs : b.d.st = a.d.st) (hb : b.d.book = a.d.book) : Rides own a b :=
  ⟨by rw [hL], by rw [hL], fun _ _ _ h => by rw [hL]; exact h, fun _ h => by rw [hL]; exact h,
    fun _ _ h => by rw [hb]; exact h, fun _ _ _ _ => by rw [hs]; exact ⟨rfl, rfl⟩,
    fun _ _ _ => by rw [hF]; exact ⟨rfl, rfl⟩⟩

theorem more_same {late : List (ℕ × OnBytes.E × OnBytes.E)} {a b : Part} {s s' : S}
    (hF : b.F = a.F) (hm : mergeOf s' = mergeOf s) (hl : lateOk late a = true) :
    More late a b s s' :=
  ⟨by rw [hF], fun _ h => by rw [hF]; exact h, by rw [hF], by rw [hF], Or.inl hm, by
    unfold lateOk at hl ⊢
    rw [hF]
    exact hl⟩

section
variable {names : List String} {runs : Given → Behind → Places → List (String × List Form)}
  {keys : Given → Behind → Places → List Form} {toCl : Form → Claim} {p : Par}
  {h : OnBytes.Model.Head.Shape} {iU3 : ℕ}

/-- What the pass gives, in one: both parts, Fwd, Rides and More. -/
theorem pass_small (q : VerifiableInference.Desc.First.K8.ParW) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (hd : (VerifiableInference.Desc.First.K8.whole q).decide s rs gs = .ok s') (H : LinkHoles)
    (l : Link S Claim) (P : VerifiableInference.Desc.K8.ReadsQuiet.PH) (own : List (ℕ × ℕ))
    (b : ℕ) {name : String} (hne : (name == "K8.equations") = false)
    (hst : ∀ r, ((statesOfLink l b).find? fun r => r.1 == name) = some r →
      r ∈ runsBy names runs keys toCl p (seatAt h iU3))
    (hsil : H.silent = k6Silent P (statesOfLink l))
    (hin : formsIn (readersOfLink H l) own b name s = true) :
    ∃ a c, segAt? s = some a ∧ segAt? s' = some c ∧ Fwd (readersOfLink H l) b name s s' ∧
      Rides own a c ∧ ∀ R, (readersOfLink H l).forms b name s = some R → More R.late a c s s' := by
  have hd' : (VerifiableInference.Desc.First.K8.approximateRangeProofDrawKind (Cl := Claim)
      VerifiableInference.Desc.First.K8.atS q.toPar).decide s rs gs = .ok s' := hd
  obtain ⟨r, rfl⟩ := VerifiableInference.Desc.First.K8.decide_one _ q.toPar s s' rs gs hd'
  obtain ⟨tl, ht, hm⟩ := (VerifiableInference.Desc.First.K8.decide_atS_iff q.toPar s s' r gs).1 hd'
  have es := hm.2.2.2.2.2.2.2.2
  have hin' := hin
  unfold formsIn at hin'
  cases ha : segAt? s with
  | none =>
    rw [ha] at hin'
    cases hin'
  | some a =>
    cases hR : (readersOfLink H l).forms b name s with
    | none =>
      rw [ha, hR] at hin'
      cases hin'
    | some R₀ =>
      rw [ha, hR] at hin'
      obtain ⟨hlate, _⟩ := Eq.mp (Bool.and_eq_true _ _) hin'
      obtain ⟨o, ho, hop⟩ := forms_head H l P b hne hst hsil hR
      have etl : o.tl = tl := by
        unfold S.tl? at ht
        rw [ho] at ht
        have ht' : (if o.opened = true then some o.tl else none) = some tl := ht
        rw [if_pos hop] at ht'
        exact Option.some.inj ht'
      have e0 : s = { s with here := .head { o with tl := tl } } := by
        rw [← etl]
        cases s
        dsimp only at ho
        subst ho
        rfl
      have e1 : s' = { s with here := .head { o with tl :=
          { tl with cfF := r.drawn.trits.toArray,
                    cfFirst := VerifiableInference.Desc.First.K8.firstColumns q.toPar } } } := by
        rw [es]
        unfold S.putTl
        rw [ho]
        simp [hop]
      have k1 : KeptMore iU3 s s' := by
        rw [e1]
        conv => arg 2; rw [e0]
        exact keptMore_tl iU3 s o _ _ rfl rfl rfl
      have k2 : KeptMore iU3 s' s := by
        rw [e1]
        conv => arg 3; rw [e0]
        exact keptMore_tl iU3 s o _ _ rfl rfl rfl
      obtain ⟨a', ha', aL, aF, as, ab⟩ := seg_head ho hop
      obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
      have ho' : s'.here = .head { o with tl :=
          { tl with cfF := r.drawn.trits.toArray,
                    cfFirst := VerifiableInference.Desc.First.K8.firstColumns q.toPar } } := by
        rw [e1]
      obtain ⟨c, hc, cL, cF, cs, cb⟩ := seg_head ho' hop
      have est : s'.st = s.st := by rw [e1]
      have ebk : s'.book = s.book := by rw [e1]
      have emg : mergeOf s' = mergeOf s := by
        unfold mergeOf
        rw [ho', ho]
      refine ⟨a', c, rfl, hc, fwd_both H l P b hne hst hsil k1 k2,
        rides_same own (cL.trans aL.symm) (cF.trans aF.symm) (cs.trans (est.trans as.symm))
          (cb.trans (ebk.trans ab.symm)), fun R hR' => ?_⟩
      obtain rfl : R₀ = R := Option.some.inj hR'
      exact more_same (cF.trans aF.symm) emg hlate

/-- **The test in front gives the test behind.** -/
theorem pass_small_test (q : VerifiableInference.Desc.First.K8.ParW) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hd : (VerifiableInference.Desc.First.K8.whole q).decide s rs gs = .ok s') (H : LinkHoles)
    (l : Link S Claim) (P : VerifiableInference.Desc.K8.ReadsQuiet.PH) (own : List (ℕ × ℕ))
    (b : ℕ) {name : String} (hne : (name == "K8.equations") = false)
    (hst : ∀ r, ((statesOfLink l b).find? fun r => r.1 == name) = some r →
      r ∈ runsBy names runs keys toCl p (seatAt h iU3))
    (hsil : H.silent = k6Silent P (statesOfLink l))
    (hin : formsIn (readersOfLink H l) own b name s = true) :
    formsIn (readersOfLink H l) own b name s' = true := by
  obtain ⟨a, c, ha, hc, hf, hr, hM⟩ := pass_small q hd H l P own b hne hst hsil hin
  exact formsIn_fwd _ own b name s s' a c ha hc hf hr hM hin

/-- **Under the test in front, "forms" behind gives "forms" in front.** -/
theorem pass_small_back (q : VerifiableInference.Desc.First.K8.ParW) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hd : (VerifiableInference.Desc.First.K8.whole q).decide s rs gs = .ok s') (H : LinkHoles)
    (l : Link S Claim) (P : VerifiableInference.Desc.K8.ReadsQuiet.PH) (own : List (ℕ × ℕ))
    (b : ℕ) {name : String} (hne : (name == "K8.equations") = false)
    (hst : ∀ r, ((statesOfLink l b).find? fun r => r.1 == name) = some r →
      r ∈ runsBy names runs keys toCl p (seatAt h iU3))
    (hsil : H.silent = k6Silent P (statesOfLink l))
    (hin : formsIn (readersOfLink H l) own b name s = true) (rd : ℕ × ℕ → MsgQ)
    (hq : formsQ (readersOfLink H l) own b name s' rd) :
    formsQ (readersOfLink H l) own b name s rd := by
  obtain ⟨a, c, ha, hc, hf, hr, _⟩ := pass_small q hd H l P own b hne hst hsil hin
  exact forms_back _ own b name s s' a c rd ha hc hf hin hr hq

end

end VerifiableInference.Reads.Pass

#print axioms VerifiableInference.Reads.Pass.kept_withTables
#print axioms VerifiableInference.Reads.Pass.fwd_both
#print axioms VerifiableInference.Reads.Pass.reader_head
#print axioms VerifiableInference.Reads.Pass.forms_head
#print axioms VerifiableInference.Reads.Pass.keptMore_tl
#print axioms VerifiableInference.Reads.Pass.seg_head
#print axioms VerifiableInference.Reads.Pass.rides_same
#print axioms VerifiableInference.Reads.Pass.more_same
#print axioms VerifiableInference.Reads.Pass.pass_small
#print axioms VerifiableInference.Reads.Pass.pass_small_test
#print axioms VerifiableInference.Reads.Pass.pass_small_back
