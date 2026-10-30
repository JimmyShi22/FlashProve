-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/JoinFwd.lean: the reader of the run "join" at the output head answers behind what
it answers in front; and "forms" with its public test, at that run, pass the approximate range
proof's sub-protocol.

Why. The output head's sub-protocol states four runs of claims. Reads/ReaderFwd.lean reaches its
three own runs. The fourth, "join", is the lookup's (`K3.joinRun`,
Johnson/Desc/First/Look/K3Runs.lean) at the output head's key vectors (`callerKeys`,
Johnson/Desc/Kinds/HeadCaller.lean). It reads one thing more of the ledger: the mark that its claim
is not yet added. It returns the state with that mark set.

What is stated and shown.
  `joinF_any`: the routine that makes the claim reads nothing of the ledger: it makes the same form
    at every ledger and sets the one mark.
  `KeptJoin iU3 s s'`: `KeptMore`, and: where the claim is not yet added in front, it is not yet
    added behind.
  `keys_fwd`, `join_fwd`: the key vectors; the run.
  `fork_put`: tools on the state.
  `reader_join_fwd`: **what `readerOf` answers in front at "join" it answers behind.**
  `fwd_of_readers`: the dispatch of Reads/FwdHead.lean and Reads/PassSmall.lean once more, general
    in the run: `Fwd` at the readers of a segment from the one direction of `readerOf` at three
    pairs of states.
  `keptJoin_tl`, `keptJoin_at`, `keptJoin_tables`: two states that differ in the approximate range
    proof's part alone; the two states with the tables laid silently.
  `join_head`: where the reader answers at "join", the state stands in the output head's segment,
    opened.
  `pass_small_join`: **the test in front gives the test behind, and under it "forms" behind gives
    "forms" in front, at "join", across the approximate range proof's sub-protocol.**

Limits. `KeptJoin` is shown of that one sub-protocol alone. No state is shown at which its accept
and the test in front hold together. Nothing on soundness.


-/
import Johnson.Desc.Reads.PassSmall
import Johnson.Desc.Reads.KeptRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.Pass

open OnBytes.Model (Fork Aff HTailF2)
open OnBytes.PscRun (Later)
open OnBytes.Desc.First.P1 (bind_some pure_some must_some change_some)
open VerifiableInference.Desc (Claim Link K3.joinRun K3.seatCalls K3.unpaid)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.Look (joinF joinAddedF paidF)
open VerifiableInference.Desc.K8 (ReadsQuiet.bind_ok ReadsQuiet.named_ok)
open VerifiableInference.Desc.K9 (Part segAt? readerOf RunOf ownRow lateOf LinkHoles statesOfLink
  readersOfLink formsIn mergeOf)
open VerifiableInference.Desc.Sound (MsgQ formsQ)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law (lateOf_got withTables withTables_iff k6Silent)

/-- The routine that makes the claim reads nothing of the ledger. -/
theorem joinF_any (g : OnBytes.Model.Forest.Heard) (KF : Array Aff) (F F' : Fork)
    (x : Aff × Fork × OnBytes.K.Kc.Tape) (h : joinF g KF F [] = some x) :
    x.2.1 = F.paid g.owedJoin ∧ joinF g KF F' [] = some (x.1, F'.paid g.owedJoin, []) := by
  obtain ⟨f, G, u⟩ := x
  unfold joinF at h ⊢
  obtain ⟨_, F1, t1, h1, h⟩ := bind_some.1 h
  obtain ⟨hc, rfl, rfl⟩ := must_some.1 h1
  obtain ⟨_, F2, t2, h2, h⟩ := bind_some.1 h
  unfold joinAddedF paidF at h2
  obtain ⟨e2, rfl⟩ := change_some.1 h2
  obtain ⟨ef, rfl, rfl⟩ := pure_some.1 h
  refine ⟨(Option.some.inj e2).symm, ?_⟩
  refine bind_some.2 ⟨(), F', [], must_some.2 ⟨hc, rfl, rfl⟩, ?_⟩
  refine bind_some.2 ⟨(), F'.paid g.owedJoin, [], ?_, pure_some.2 ⟨ef, rfl, rfl⟩⟩
  unfold joinAddedF paidF
  exact change_some.2 ⟨rfl, rfl⟩

/-- What the reader of "join" reads is kept. -/
structure KeptJoin (iU3 : ℕ) (s s' : S) : Prop where
  more : KeptMore iU3 s s'
  mark : ∀ (o o' : HeadOwn) (g : OnBytes.Model.Forest.Heard), s.here = .head o →
    s'.here = .head o' → o.lookHeard = some g → K3.unpaid o.F g.owedJoin = true →
    K3.unpaid o'.F g.owedJoin = true

/-- The key vectors. -/
theorem keys_fwd {iU3 : ℕ} {s s' : S} (k : KeptMore iU3 s s') (p : Par)
    (h : OnBytes.Model.Head.Shape) {KF : Array Form}
    (hk : callerKeys p (seatAt h iU3) s = some KF) :
    (∃ o, s.here = .head o) ∧ callerKeys p (seatAt h iU3) s' = some KF := by
  unfold callerKeys at hk ⊢
  dsimp only at hk ⊢
  cases hl : lettersAt p (seatAt h iU3) s with
  | error e =>
    rw [hl] at hk
    cases hk
  | ok v =>
    rw [hl] at hk
    rw [letters_fwd k p h hl]
    exact ⟨head_of_letters hl, hk⟩

/-- The ledger that was just written is read back, at an opened state of the head's segment. -/
theorem fork_put {s : S} {o : HeadOwn} (ho : s.here = .head o) (hop : o.opened = true)
    (G : Fork) : s.fork? = some o.F ∧ (s.putFork G).fork? = some G := by
  constructor
  · unfold S.fork?
    rw [ho]
    simp [hop]
  · unfold S.putFork S.fork?
    rw [ho]
    simp [hop]

/-- The run. -/
theorem join_fwd {iU3 : ℕ} {s s' : S} (k : KeptJoin iU3 s s') (claim : Aff → Claim) (p : Par)
    (h : OnBytes.Model.Head.Shape) {n : ℕ} {y : List Claim × S}
    (hr : K3.joinRun (K3.seatCalls claim) (callerKeys p (seatAt h iU3)) n s = .ok y) :
    ∃ (o o' : HeadOwn) (i : ℕ), s.here = .head o ∧ s'.here = .head o' ∧ o.opened = true ∧
      o'.opened = true ∧ y.2 = s.putFork (o.F.paid i) ∧
      K3.joinRun (K3.seatCalls claim) (callerKeys p (seatAt h iU3)) n s' =
        .ok (y.1, s'.putFork (o'.F.paid i)) := by
  unfold K3.joinRun at hr ⊢
  obtain ⟨F, h1, r1⟩ := ReadsQuiet.bind_ok hr
  obtain ⟨g, h2, r2⟩ := ReadsQuiet.bind_ok r1
  obtain ⟨_, h3, r3⟩ := ReadsQuiet.bind_ok r2
  obtain ⟨KF, h4, r4⟩ := ReadsQuiet.bind_ok r3
  obtain ⟨x, h5, r5⟩ := ReadsQuiet.bind_ok r4
  have hF : s.fork? = some F := ReadsQuiet.named_ok h1
  have hg : s.lookHeard? = some g := ReadsQuiet.named_ok h2
  obtain ⟨⟨o, ho⟩, hK'⟩ := keys_fwd k.more p h (ReadsQuiet.named_ok h4)
  obtain ⟨o', ho', a1, _⟩ := k.more.all.own o ho
  have hop : o.opened = true := by
    by_cases hop : o.opened = true
    · exact hop
    · unfold S.fork? at hF
      rw [ho] at hF
      simp [hop] at hF
  have hop' : o'.opened = true := a1.trans hop
  have eF : F = o.F := by
    rw [(fork_put ho hop o.F).1] at hF
    exact (Option.some.inj hF).symm
  subst eF
  have hlg : o.lookHeard = some g := by
    unfold S.lookHeard? at hg
    rw [ho] at hg
    simpa [hop] using hg
  have hu : K3.unpaid o.F g.owedJoin = true := by
    cases hb : K3.unpaid o.F g.owedJoin with
    | true => rfl
    | false =>
      rw [hb] at h3
      cases h3
  obtain ⟨e1, e2⟩ := joinF_any g KF o.F o'.F x (ReadsQuiet.named_ok h5)
  have ey := Except.ok.inj r5
  refine ⟨o, o', g.owedJoin, ho, ho', hop, hop', ?_, ?_⟩
  · rw [← ey]
    show s.putFork x.2.1 = _
    rw [e1]
  · have f1 : (K3.seatCalls claim).fork s' = some o'.F := (fork_put ho' hop' o'.F).1
    have f2 : (K3.seatCalls claim).heard s' = some g := by
      show s'.lookHeard? = some g
      rw [look_fwd k.more.all ho]
      exact hg
    rw [f1, f2, hK']
    show ((do
      VerifiableInference.Desc.need "K3 join: it is made once" (K3.unpaid o'.F g.owedJoin)
      let x ← VerifiableInference.Desc.named "K3 join: one form and one weight a call"
        (joinF g KF o'.F [])
      pure ([(K3.seatCalls claim).claim x.1], (K3.seatCalls claim).mark s' x.2.1)) :
        Except String (List Claim × S)) = _
    rw [k.mark o o' g ho ho' hlg hu, e2, ← ey]
    rfl

/-- **What the reader answers in front at "join" it answers behind.** -/
theorem reader_join_fwd {iU3 : ℕ} {s s' : S} (k : KeptJoin iU3 s s') (claim : Aff → Claim)
    (p : Par) (h : OnBytes.Model.Head.Shape) (states : ℕ → List (RunOf S)) (b : ℕ)
    (name : String)
    (hst : ∀ r, ((states b).find? fun r => r.1 == name) = some r →
      r.2 = K3.joinRun (K3.seatCalls claim) (callerKeys p (seatAt h iU3)))
    {R : VerifiableInference.Desc.K9.Read} (hR : readerOf states b name s = some R) :
    readerOf states b name s' = some R := by
  unfold readerOf at hR ⊢
  obtain ⟨r, hf, hR⟩ := Option.bind_eq_some_iff.1 hR
  rw [hf, Option.bind_some]
  have hc := hst r hf
  cases hz : r.2 0 s with
  | error e =>
    rw [hz] at hR
    cases hR
  | ok z =>
    have hz' := hz
    rw [hc] at hz'
    obtain ⟨o, o', i, ho, ho', hop, hop', ez, hb⟩ := join_fwd k claim p h hz'
    rw [← hc] at hb
    rw [hz, (fork_put ho hop o.F).1] at hR
    rw [hb, (fork_put ho' hop' o'.F).1]
    have hR' : ((z.2.fork?).bind fun G =>
        if (z.1.all fun c => c.runs.isEmpty && c.eqFirst.isNone &&
          c.form.ents.all (ownRow o.F)) = true then
          some ({ forms := z.1.map (·.form), late := lateOf o.F G } :
            VerifiableInference.Desc.K9.Read) else none) = some R := hR
    rw [ez, (fork_put ho hop (o.F.paid i)).2, Option.bind_some,
      lateOf_got o.F (o.F.paid i) rfl] at hR'
    show (((s'.putFork (o'.F.paid i)).fork?).bind fun G =>
        if (z.1.all fun c => c.runs.isEmpty && c.eqFirst.isNone &&
          c.form.ents.all (ownRow o'.F)) = true then
          some ({ forms := z.1.map (·.form), late := lateOf o'.F G } :
            VerifiableInference.Desc.K9.Read) else none) = some R
    have eo : ownRow o'.F = ownRow o.F := funext (ownRow_fwd (k.more.rows o o' ho ho'))
    rw [(fork_put ho' hop' (o'.F.paid i)).2, Option.bind_some,
      lateOf_got o'.F (o'.F.paid i) rfl, eo]
    exact hR'

/-- The dispatch, general in the run. -/
theorem fwd_of_readers {s s' : S} (H : LinkHoles) (l : Link S Claim)
    (P : VerifiableInference.Desc.K8.ReadsQuiet.PH) (b : ℕ) {name : String}
    (hne : (name == "K8.equations") = false) (hsil : H.silent = k6Silent P (statesOfLink l))
    (f1 : ∀ R, readerOf (statesOfLink l) b name s = some R →
      readerOf (statesOfLink l) b name s' = some R)
    (f2 : ∀ R, readerOf (statesOfLink l) b name s' = some R →
      readerOf (statesOfLink l) b name s = some R)
    (f3 : ∀ e, withTables P s = some e → ∃ e', withTables P s' = some e' ∧
      ∀ R, readerOf (statesOfLink l) b name e = some R →
        readerOf (statesOfLink l) b name e' = some R) :
    Fwd (readersOfLink H l) b name s s' := by
  intro R hR
  cases h1 : readerOf (statesOfLink l) b name s with
  | some R₁ =>
    have e : R₁ = R := Option.some.inj ((readers_of_run H l b hne h1).symm.trans hR)
    subst e
    exact readers_of_run H l b hne (f1 R₁ h1)
  | none =>
    have h2 : readerOf (statesOfLink l) b name s' = none := by
      cases h2 : readerOf (statesOfLink l) b name s' with
      | none => rfl
      | some R' =>
        have h3 := f2 R' h2
        rw [h1] at h3
        cases h3
    have hR' : (if (name == "K8.equations") = true then H.small s
      else
        match readerOf (statesOfLink l) b name s with
        | some R => some R
        | Option.none => H.silent b name s) = some R := hR
    rw [hne, h1, hsil] at hR'
    have hR'' : (withTables P s).bind (readerOf (statesOfLink l) b name) = some R := hR'
    obtain ⟨e, he, h4⟩ := Option.bind_eq_some_iff.1 hR''
    obtain ⟨e', he', ke⟩ := f3 e he
    show (if (name == "K8.equations") = true then H.small s'
      else
        match readerOf (statesOfLink l) b name s' with
        | some R => some R
        | Option.none => H.silent b name s') = some R
    rw [hne, h2, hsil]
    show (withTables P s').bind (readerOf (statesOfLink l) b name) = some R
    rw [he', Option.bind_some]
    exact ke R h4

/-- Two states that differ in the approximate range proof's part alone. -/
theorem keptJoin_tl (iU3 : ℕ) (s : S) (o : HeadOwn) (t1 t2 : HTailF2) (h1 : t2.mats = t1.mats)
    (h2 : t2.funs = t1.funs) (h3 : t2.NM = t1.NM) :
    KeptJoin iU3 { s with here := .head { o with tl := t1 } }
      { s with here := .head { o with tl := t2 } } := by
  refine ⟨keptMore_tl iU3 s o t1 t2 h1 h2 h3, fun o1 o2 g e1 e2 _ hu => ?_⟩
  obtain rfl : { o with tl := t1 } = o1 := VerifiableInference.Desc.First.Here.head.inj e1
  obtain rfl : { o with tl := t2 } = o2 := VerifiableInference.Desc.First.Here.head.inj e2
  exact hu

/-- KeptJoin passes to the two states with the tables laid silently. -/
theorem keptJoin_tables {iU3 : ℕ} {s s' e : S} (k : KeptJoin iU3 s s')
    (P : VerifiableInference.Desc.K8.ReadsQuiet.PH) (hw : withTables P s = some e) :
    ∃ e', withTables P s' = some e' ∧ KeptJoin iU3 e e' := by
  obtain ⟨e', he', km⟩ := kept_withTables k.more P hw
  refine ⟨e', he', km, fun o1 o2 g e1 e2 hg hu => ?_⟩
  obtain ⟨a, _, _, tt, ha, _, _, _, _, rfl⟩ := (withTables_iff P s e).1 hw
  obtain ⟨a', _, _, tt', ha', _, _, _, _, rfl⟩ := (withTables_iff P s' e').1 he'
  obtain rfl : { a with t := some tt } = o1 := VerifiableInference.Desc.First.Here.head.inj e1
  obtain rfl : { a' with t := some tt' } = o2 := VerifiableInference.Desc.First.Here.head.inj e2
  exact k.mark a a' g ha ha' hg hu

/-- A state and the same state with another part of the approximate range proof: both ways. -/
theorem keptJoin_at (iU3 : ℕ) {s : S} {o : HeadOwn} (ho : s.here = .head o) (t2 : HTailF2)
    (h1 : t2.mats = o.tl.mats) (h2 : t2.funs = o.tl.funs) (h3 : t2.NM = o.tl.NM) :
    KeptJoin iU3 s { s with here := .head { o with tl := t2 } } ∧
      KeptJoin iU3 { s with here := .head { o with tl := t2 } } s := by
  have e0 : s = { s with here := .head { o with tl := o.tl } } := by
    cases s
    dsimp only at ho
    subst ho
    rfl
  have k1 := keptJoin_tl iU3 s o o.tl t2 h1 h2 h3
  have k2 := keptJoin_tl iU3 s o t2 o.tl h1.symm h2.symm h3.symm
  rw [← e0] at k1 k2
  exact ⟨k1, k2⟩

/-- Where the reader answers at "join", the state stands in the head's segment, opened. -/
theorem join_head {iU3 : ℕ} {s : S} (claim : Aff → Claim) (p : Par)
    (h : OnBytes.Model.Head.Shape) (states : ℕ → List (RunOf S)) (b : ℕ) (name : String)
    (hst : ∀ r, ((states b).find? fun r => r.1 == name) = some r →
      r.2 = K3.joinRun (K3.seatCalls claim) (callerKeys p (seatAt h iU3)))
    {R : VerifiableInference.Desc.K9.Read} (hR : readerOf states b name s = some R) :
    ∃ o, s.here = .head o ∧ o.opened = true := by
  unfold readerOf at hR
  obtain ⟨r, hf, hR⟩ := Option.bind_eq_some_iff.1 hR
  cases hz : r.2 0 s with
  | error e =>
    rw [hz] at hR
    cases hR
  | ok z =>
    rw [hst r hf] at hz
    unfold K3.joinRun at hz
    obtain ⟨F, h1, hz⟩ := ReadsQuiet.bind_ok hz
    obtain ⟨g, _, hz⟩ := ReadsQuiet.bind_ok hz
    obtain ⟨_, _, hz⟩ := ReadsQuiet.bind_ok hz
    obtain ⟨KF, h4, _⟩ := ReadsQuiet.bind_ok hz
    have hF : s.fork? = some F := ReadsQuiet.named_ok h1
    have hk : callerKeys p (seatAt h iU3) s = some KF := ReadsQuiet.named_ok h4
    unfold callerKeys at hk
    dsimp only at hk
    cases hl : lettersAt p (seatAt h iU3) s with
    | error e =>
      rw [hl] at hk
      cases hk
    | ok v =>
      obtain ⟨o, ho⟩ := head_of_letters hl
      refine ⟨o, ho, ?_⟩
      by_cases hop : o.opened = true
      · exact hop
      · unfold S.fork? at hF
        rw [ho] at hF
        simp [hop] at hF

/-- **"forms" and its test, at "join", pass the approximate range proof's sub-protocol.** -/
theorem pass_small_join {iU3 : ℕ} (q : VerifiableInference.Desc.First.K8.ParW) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hd : (VerifiableInference.Desc.First.K8.whole q).decide s rs gs = .ok s') (H : LinkHoles)
    (l : Link S Claim) (P : VerifiableInference.Desc.K8.ReadsQuiet.PH) (own : List (ℕ × ℕ))
    (b : ℕ) {name : String} (hne : (name == "K8.equations") = false) (claim : Aff → Claim)
    (p : Par) (h : OnBytes.Model.Head.Shape)
    (hst : ∀ r, ((statesOfLink l b).find? fun r => r.1 == name) = some r →
      r.2 = K3.joinRun (K3.seatCalls claim) (callerKeys p (seatAt h iU3)))
    (hsil : H.silent = k6Silent P (statesOfLink l))
    (hin : formsIn (readersOfLink H l) own b name s = true) (rd : ℕ × ℕ → MsgQ) :
    formsIn (readersOfLink H l) own b name s' = true ∧
      (formsQ (readersOfLink H l) own b name s' rd →
        formsQ (readersOfLink H l) own b name s rd) := by
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
      have hh : ∃ o, s.here = .head o ∧ o.opened = true := by
        cases h1 : readerOf (statesOfLink l) b name s with
        | some R₁ => exact join_head claim p h (statesOfLink l) b name hst h1
        | none =>
          have hR' : (if (name == "K8.equations") = true then H.small s
            else
              match readerOf (statesOfLink l) b name s with
              | some R => some R
              | Option.none => H.silent b name s) = some R₀ := hR
          rw [hne, h1, hsil] at hR'
          have hR'' : (withTables P s).bind (readerOf (statesOfLink l) b name) = some R₀ := hR'
          obtain ⟨e, he, _⟩ := Option.bind_eq_some_iff.1 hR''
          obtain ⟨a0, _, _, _, ha0, hop0, _⟩ := (withTables_iff P s e).1 he
          exact ⟨a0, ha0, hop0⟩
      obtain ⟨o, ho, hop⟩ := hh
      have etl : o.tl = tl := by
        unfold S.tl? at ht
        rw [ho] at ht
        have ht' : (if o.opened = true then some o.tl else none) = some tl := ht
        rw [if_pos hop] at ht'
        exact Option.some.inj ht'
      have e1 : s' = { s with here := .head { o with tl :=
          { tl with cfF := r.drawn.trits.toArray,
                    cfFirst := VerifiableInference.Desc.First.K8.firstColumns q.toPar } } } := by
        rw [es]
        unfold S.putTl
        rw [ho]
        simp [hop]
      obtain ⟨k1, k2⟩ := keptJoin_at iU3 ho
        { tl with cfF := r.drawn.trits.toArray,
                  cfFirst := VerifiableInference.Desc.First.K8.firstColumns q.toPar }
        (by rw [etl]) (by rw [etl]) (by rw [etl])
      rw [← e1] at k1 k2
      have hf : Fwd (readersOfLink H l) b name s s' :=
        fwd_of_readers H l P b hne hsil
          (fun R hR1 => reader_join_fwd k1 claim p h (statesOfLink l) b name hst hR1)
          (fun R hR1 => reader_join_fwd k2 claim p h (statesOfLink l) b name hst hR1)
          (fun e he => by
            obtain ⟨e', he', ke⟩ := keptJoin_tables k1 P he
            exact ⟨e', he', fun R hR1 =>
              reader_join_fwd ke claim p h (statesOfLink l) b name hst hR1⟩)
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
      have hr := rides_same own (cL.trans aL.symm) (cF.trans aF.symm)
        (cs.trans (est.trans as.symm)) (cb.trans (ebk.trans ab.symm))
      refine ⟨formsIn_fwd _ own b name s s' a' c ha hc hf hr (fun R hR' => ?_) hin,
        fun hq => forms_back _ own b name s s' a' c rd ha hc hf hin hr hq⟩
      obtain rfl : R₀ = R := Option.some.inj (hR.symm.trans hR')
      exact more_same (cF.trans aF.symm) emg hlate

end VerifiableInference.Reads.Pass

#print axioms VerifiableInference.Reads.Pass.joinF_any
#print axioms VerifiableInference.Reads.Pass.keys_fwd
#print axioms VerifiableInference.Reads.Pass.fork_put
#print axioms VerifiableInference.Reads.Pass.join_fwd
#print axioms VerifiableInference.Reads.Pass.reader_join_fwd
#print axioms VerifiableInference.Reads.Pass.fwd_of_readers
#print axioms VerifiableInference.Reads.Pass.keptJoin_tl
#print axioms VerifiableInference.Reads.Pass.keptJoin_tables
#print axioms VerifiableInference.Reads.Pass.keptJoin_at
#print axioms VerifiableInference.Reads.Pass.join_head
#print axioms VerifiableInference.Reads.Pass.pass_small_join
