-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/PassFifth.lean: the readers of the output head's four runs of claims, across the
place at which the reads' tables are laid.

Why. That place is a commitment with a quiet step laid behind it (`ReadsQuiet.head`,
Johnson/Desc/K8/ReadsQuiet.lean). In front of it the runs are silent and the second reader answers:
the run, called at the state e with the tables laid silently (`withTables`,
Johnson/Desc/Kinds/Law/K6SilentCode.lean). Behind it the runs answer themselves. The quiet step also
lays the approximate range proof's part anew, with its list of tables closed. So `KeptMore`
(Reads/ReaderFwd.lean), which asks that list to stand, does not hold from e to the state behind. But
no reader of the four runs reads that part.

What is shown.
  `letters_tl`: the kind's letters do not hang on the approximate range proof's part of the state.
  `run_alike`, `reader_alike`, `reader_join_alike`: tools: two states with the same letters, the
    same ledger and the same values left by the lookup: what `readerOf` answers at the one it
    answers at the other.
  `reader_tl`, `reader_join_tl`: so what `readerOf` answers does not hang on that part, at a run of
    the kind's own claims and at "join". In one direction.
  `keptJoin_fifth`: where the commitment accepts from s to s₁ and the quiet step from s₁ to s', and
    `withTables` answers e at s: there is a state u such that s' is u but for the approximate range
    proof's part, and `KeptJoin` holds from e to u. It does not hold from e to s'.
  `reader_fifth`, `reader_join_fifth`: **what `readerOf` answers at e it answers at s'.**
  `fwd_hole`: `fwd_of_hole` (Reads/FwdHead.lean) once more, with the readers' one direction in
    `KeptMore`'s place, general in the run.

Limits. "The run is silent in front" stays a premise of `fwd_hole`. `Rides` across the commitment is
not shown. Nothing on soundness.


-/
import Johnson.Desc.Reads.KeptMoreCommit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.Pass

open OnBytes.Model (Fork Aff HTailF2)
open VerifiableInference.Desc (Claim Link K3.joinRun K3.seatCalls)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K8 (ReadsQuiet.head ReadsQuiet.head_ok ReadsQuiet.bind_ok
  ReadsQuiet.named_ok)
open VerifiableInference.Desc.K9 (readerOf RunOf ownRow lateOf LinkHoles statesOfLink readersOfLink)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law (withTables withTables_iff k6Silent)
open VerifiableInference.Reads.AtSeat (covered_congr run_returns)

/-- The kind's letters do not hang on the approximate range proof's part. -/
theorem letters_tl (p : Par) (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) (s : S) (o : HeadOwn)
    (t1 t2 : HTailF2) :
    lettersAt p (seatAt h iU3) { s with here := .head { o with tl := t2 } } =
      lettersAt p (seatAt h iU3) { s with here := .head { o with tl := t1 } } := by
  have e1 : (seatAt h iU3).lookup { s with here := .head { o with tl := t2 } } =
      (seatAt h iU3).lookup { s with here := .head { o with tl := t1 } } := rfl
  have e2 : Reply.token (seatAt h iU3).toSeat { s with here := .head { o with tl := t2 } } =
      Reply.token (seatAt h iU3).toSeat { s with here := .head { o with tl := t1 } } := rfl
  have e3 : (seatAt h iU3).request { s with here := .head { o with tl := t2 } } =
      (seatAt h iU3).request { s with here := .head { o with tl := t1 } } := rfl
  have e4 : (seatAt h iU3).heard { s with here := .head { o with tl := t2 } } =
      (seatAt h iU3).heard { s with here := .head { o with tl := t1 } } := rfl
  have e5 : (seatAt h iU3).reads { s with here := .head { o with tl := t2 } } =
      (seatAt h iU3).reads { s with here := .head { o with tl := t1 } } := by
    unfold seatAt
    dsimp only
    unfold S.fork?
    dsimp only
    by_cases hop : o.opened = true
    · rw [if_pos hop]
    · rw [if_neg hop]
  unfold lettersAt given
  rw [e1, e2, e3, e4, e5]

/-- A run of the kind's own claims, at two states with the same letters. -/
theorem run_alike {Cl : Type} {names : List String}
    {runs : Given → Behind → Places → List (String × List Form)}
    {keys : Given → Behind → Places → List Form} {toCl : Form → Cl} {p : Par}
    {h : OnBytes.Model.Head.Shape} {iU3 : ℕ} {s s' : S}
    (hl : lettersAt p (seatAt h iU3) s' = lettersAt p (seatAt h iU3) s)
    {c : String × (ℕ → S → Except String (List Cl × S))}
    (hc : c ∈ runsBy names runs keys toCl p (seatAt h iU3)) {n : ℕ} {y : List Cl × S}
    (hr : c.2 n s = .ok y) : c.2 n s' = .ok (y.1, s') := by
  unfold runsBy at hc
  obtain ⟨name, -, rfl⟩ := List.mem_map.1 hc
  dsimp only at hr ⊢
  obtain ⟨⟨g, b, x⟩, h1, hr⟩ := ReadsQuiet.bind_ok hr
  obtain ⟨fs, h2, hr⟩ := ReadsQuiet.bind_ok hr
  rw [hl, h1]
  show (do
    let fs ← VerifiableInference.Desc.named "the run is there" ((runs g b x).lookup name)
    pure (fs.map toCl,
      if names.head? == some name then (seatAt h iU3).setKeyForms s' (keys g b x) else s')) = _
  rw [h2]
  have e := congrArg Prod.fst (Except.ok.inj hr)
  show Except.ok (fs.map toCl,
    if names.head? == some name then (seatAt h iU3).setKeyForms s' (keys g b x) else s') = _
  have e' : fs.map toCl = y.1 := e
  rw [e']
  congr 2
  split <;> rfl

/-- The reader, at two states with the same letters and the same ledger. -/
theorem reader_alike {names : List String}
    {runs : Given → Behind → Places → List (String × List Form)}
    {keys : Given → Behind → Places → List Form} {toCl : Form → Claim} {p : Par}
    {h : OnBytes.Model.Head.Shape} {iU3 : ℕ} {s s' : S}
    (hl : lettersAt p (seatAt h iU3) s' = lettersAt p (seatAt h iU3) s)
    (hF : s'.fork? = s.fork?) (states : ℕ → List (RunOf S)) (b : ℕ) (name : String)
    (hst : ∀ r, ((states b).find? fun r => r.1 == name) = some r →
      r ∈ runsBy names runs keys toCl p (seatAt h iU3))
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
    have ez : z.2 = s := run_returns h iU3 hc hz
    cases hFs : s.fork? with
    | none =>
      rw [hz, hFs] at hR
      cases hR
    | some F =>
      rw [hz, hFs] at hR
      rw [run_alike hl hc hz, hF, hFs]
      have hR' : ((z.2.fork?).bind fun G =>
          if (z.1.all fun c => c.runs.isEmpty && c.eqFirst.isNone &&
            c.form.ents.all (ownRow F)) = true then
            some ({ forms := z.1.map (·.form), late := lateOf F G } :
              VerifiableInference.Desc.K9.Read) else none) = some R := hR
      rw [ez, hFs] at hR'
      show ((s'.fork?).bind fun G =>
          if (z.1.all fun c => c.runs.isEmpty && c.eqFirst.isNone &&
            c.form.ents.all (ownRow F)) = true then
            some ({ forms := z.1.map (·.form), late := lateOf F G } :
              VerifiableInference.Desc.K9.Read) else none) = some R
      rw [hF, hFs]
      exact hR'

/-- The like at "join". -/
theorem reader_join_alike (claim : Aff → Claim) (p : Par) (h : OnBytes.Model.Head.Shape)
    (iU3 : ℕ) {s s' : S} (hl : lettersAt p (seatAt h iU3) s' = lettersAt p (seatAt h iU3) s)
    (hF : s'.fork? = s.fork?) (hg : s'.lookHeard? = s.lookHeard?)
    (hp : ∀ G : Fork, (s'.putFork G).fork? = (s.putFork G).fork?)
    (states : ℕ → List (RunOf S)) (b : ℕ) (name : String)
    (hst : ∀ r, ((states b).find? fun r => r.1 == name) = some r →
      r.2 = K3.joinRun (K3.seatCalls claim) (callerKeys p (seatAt h iU3)))
    {R : VerifiableInference.Desc.K9.Read} (hR : readerOf states b name s = some R) :
    readerOf states b name s' = some R := by
  unfold readerOf at hR ⊢
  obtain ⟨r, hf, hR⟩ := Option.bind_eq_some_iff.1 hR
  rw [hf, Option.bind_some]
  rw [hst r hf] at hR ⊢
  cases hz : K3.joinRun (K3.seatCalls claim) (callerKeys p (seatAt h iU3)) 0 s with
  | error e =>
    rw [hz] at hR
    cases hR
  | ok z =>
    have hz0 := hz
    unfold K3.joinRun at hz0
    obtain ⟨F, h1, r1⟩ := ReadsQuiet.bind_ok hz0
    obtain ⟨g, h2, r2⟩ := ReadsQuiet.bind_ok r1
    obtain ⟨u, h3, r3⟩ := ReadsQuiet.bind_ok r2
    obtain ⟨KF, h4, r4⟩ := ReadsQuiet.bind_ok r3
    obtain ⟨x, h5, r5⟩ := ReadsQuiet.bind_ok r4
    have ey := Except.ok.inj r5
    have hFs : s.fork? = some F := ReadsQuiet.named_ok h1
    have hz' : K3.joinRun (K3.seatCalls claim) (callerKeys p (seatAt h iU3)) 0 s' =
        .ok (z.1, s'.putFork x.2.1) := by
      unfold K3.joinRun
      have f1 : (K3.seatCalls claim).fork s' = (K3.seatCalls claim).fork s := hF
      have f2 : (K3.seatCalls claim).heard s' = (K3.seatCalls claim).heard s := hg
      have f3 : callerKeys p (seatAt h iU3) s' = callerKeys p (seatAt h iU3) s := by
        unfold callerKeys
        rw [hl]
      rw [f1, f2, f3, h1]
      show ((do
        let g ← VerifiableInference.Desc.named "K3 join: nothing was heard"
          ((K3.seatCalls claim).heard s)
        VerifiableInference.Desc.need "K3 join: it is made once"
          (VerifiableInference.Desc.K3.unpaid F g.owedJoin)
        let KF ← VerifiableInference.Desc.named "K3 join: the caller's keys"
          (callerKeys p (seatAt h iU3) s)
        let x ← VerifiableInference.Desc.named "K3 join: one form and one weight a call"
          (VerifiableInference.Desc.First.Look.joinF g KF F [])
        pure ([(K3.seatCalls claim).claim x.1], (K3.seatCalls claim).mark s' x.2.1)) :
          Except String (List Claim × S)) = _
      rw [h2]
      show ((do
        VerifiableInference.Desc.need "K3 join: it is made once"
          (VerifiableInference.Desc.K3.unpaid F g.owedJoin)
        let KF ← VerifiableInference.Desc.named "K3 join: the caller's keys"
          (callerKeys p (seatAt h iU3) s)
        let x ← VerifiableInference.Desc.named "K3 join: one form and one weight a call"
          (VerifiableInference.Desc.First.Look.joinF g KF F [])
        pure ([(K3.seatCalls claim).claim x.1], (K3.seatCalls claim).mark s' x.2.1)) :
          Except String (List Claim × S)) = _
      rw [h3]
      show ((do
        let KF ← VerifiableInference.Desc.named "K3 join: the caller's keys"
          (callerKeys p (seatAt h iU3) s)
        let x ← VerifiableInference.Desc.named "K3 join: one form and one weight a call"
          (VerifiableInference.Desc.First.Look.joinF g KF F [])
        pure ([(K3.seatCalls claim).claim x.1], (K3.seatCalls claim).mark s' x.2.1)) :
          Except String (List Claim × S)) = _
      rw [h4]
      show ((do
        let x ← VerifiableInference.Desc.named "K3 join: one form and one weight a call"
          (VerifiableInference.Desc.First.Look.joinF g KF F [])
        pure ([(K3.seatCalls claim).claim x.1], (K3.seatCalls claim).mark s' x.2.1)) :
          Except String (List Claim × S)) = _
      rw [h5, ← ey]
      rfl
    have ez : z.2 = s.putFork x.2.1 := by
      rw [← ey]
      rfl
    rw [hz, hFs] at hR
    rw [hz', hF, hFs]
    have hR' : ((z.2.fork?).bind fun G =>
        if (z.1.all fun c => c.runs.isEmpty && c.eqFirst.isNone &&
          c.form.ents.all (ownRow F)) = true then
          some ({ forms := z.1.map (·.form), late := lateOf F G } :
            VerifiableInference.Desc.K9.Read) else none) = some R := hR
    rw [ez] at hR'
    show (((s'.putFork x.2.1).fork?).bind fun G =>
        if (z.1.all fun c => c.runs.isEmpty && c.eqFirst.isNone &&
          c.form.ents.all (ownRow F)) = true then
          some ({ forms := z.1.map (·.form), late := lateOf F G } :
            VerifiableInference.Desc.K9.Read) else none) = some R
    rw [hp]
    exact hR'

/-- What the reader answers does not hang on the approximate range proof's part. -/
theorem reader_tl {names : List String}
    {runs : Given → Behind → Places → List (String × List Form)}
    {keys : Given → Behind → Places → List Form} {toCl : Form → Claim} {p : Par}
    {h : OnBytes.Model.Head.Shape} {iU3 : ℕ} (s : S) (o : HeadOwn) (t1 t2 : HTailF2)
    (states : ℕ → List (RunOf S)) (b : ℕ) (name : String)
    (hst : ∀ r, ((states b).find? fun r => r.1 == name) = some r →
      r ∈ runsBy names runs keys toCl p (seatAt h iU3))
    {R : VerifiableInference.Desc.K9.Read}
    (hR : readerOf states b name { s with here := .head { o with tl := t1 } } = some R) :
    readerOf states b name { s with here := .head { o with tl := t2 } } = some R :=
  reader_alike (letters_tl p h iU3 s o t1 t2) rfl states b name hst hR

/-- Nor at "join". -/
theorem reader_join_tl (claim : Aff → Claim) (p : Par) (h : OnBytes.Model.Head.Shape) (iU3 : ℕ)
    (s : S) (o : HeadOwn) (t1 t2 : HTailF2) (states : ℕ → List (RunOf S)) (b : ℕ)
    (name : String)
    (hst : ∀ r, ((states b).find? fun r => r.1 == name) = some r →
      r.2 = K3.joinRun (K3.seatCalls claim) (callerKeys p (seatAt h iU3)))
    {R : VerifiableInference.Desc.K9.Read}
    (hR : readerOf states b name { s with here := .head { o with tl := t1 } } = some R) :
    readerOf states b name { s with here := .head { o with tl := t2 } } = some R :=
  reader_join_alike claim p h iU3 (letters_tl p h iU3 s o t1 t2) rfl rfl (fun G => by
    unfold S.putFork S.fork?
    by_cases hop : o.opened = true <;> simp [hop]) states b name hst hR

/-- Across the commitment and the quiet step. -/
theorem keptJoin_fifth {Cl : Type} (Pc : VerifiableInference.Desc.K1.Par) (link moment : ℕ)
    (arrays : Option (List ℕ)) (P : VerifiableInference.Desc.K8.ReadsQuiet.PH) {s s₁ s' e : S}
    {rs rs' : List Fmt.RoundView} {gs gs' : List (List (ℕ × List UInt64))}
    (hcom : (VerifiableInference.Desc.K1.commitAtS (Cl := Cl) Pc link moment arrays).decide s rs
      gs = .ok s₁)
    (hq : (ReadsQuiet.head P).decide s₁ rs' gs' = .ok s') (hw : withTables P s = some e)
    (i : ℕ) :
    ∃ (o : HeadOwn) (tl' : HTailF2), s' = { s₁ with here := .head { o with tl := tl' } } ∧
      KeptJoin i e { s₁ with here := .head { o with tl := o.tl } } := by
  obtain ⟨a, cov, x, tt, ha, hop, hcov, hx, ht, rfl⟩ := (withTables_iff P s e).1 hw
  have k := keptJoin_commit Pc link moment arrays hcom i
  obtain ⟨a1, ha1, b1, b2, b3, _, b5, b6, b7, b8⟩ := k.more.all.own a ha
  obtain ⟨a2, cov', x', t', tl', ha2, _, hcov', hx', ht', _, es'⟩ := ReadsQuiet.head_ok hq
  obtain rfl : a1 = a2 := by
    rw [ha1] at ha2
    exact VerifiableInference.Desc.First.Here.head.inj ha2
  obtain rfl : cov = cov' := by
    rw [covered_congr k.more.all.req k.more.all.reply, hcov] at hcov'
    exact Except.ok.inj hcov'
  obtain rfl : x = x' := by
    rw [b2, hx] at hx'
    exact Option.some.inj hx'
  obtain rfl : tt = t' := by
    rw [ht] at ht'
    exact Except.ok.inj ht'
  refine ⟨{ a1 with t := some tt }, tl', es', ⟨⟨k.more.all.req, k.more.all.reply, fun o ho => ?_⟩,
    fun o1 o2 h1 h2 => ?_, fun o1 o2 h1 h2 => ?_, fun o1 o2 h1 h2 => ?_⟩,
    fun o1 o2 g h1 h2 hg hu => ?_⟩
  · obtain rfl : { a with t := some tt } = o := VerifiableInference.Desc.First.Here.head.inj ho
    exact ⟨_, rfl, b1, b2, b3, rfl, b5, b6, b7, b8⟩
  · obtain rfl : { a with t := some tt } = o1 := VerifiableInference.Desc.First.Here.head.inj h1
    obtain rfl := VerifiableInference.Desc.First.Here.head.inj h2
    exact k.more.sq a a1 ha ha1
  · obtain rfl : { a with t := some tt } = o1 := VerifiableInference.Desc.First.Here.head.inj h1
    obtain rfl := VerifiableInference.Desc.First.Here.head.inj h2
    exact k.more.later a a1 ha ha1
  · obtain rfl : { a with t := some tt } = o1 := VerifiableInference.Desc.First.Here.head.inj h1
    obtain rfl := VerifiableInference.Desc.First.Here.head.inj h2
    exact k.more.rows a a1 ha ha1
  · obtain rfl : { a with t := some tt } = o1 := VerifiableInference.Desc.First.Here.head.inj h1
    obtain rfl := VerifiableInference.Desc.First.Here.head.inj h2
    exact k.mark a a1 g ha ha1 hg hu

/-- **What the reader answers at e it answers behind the place**, at a run of the kind's own. -/
theorem reader_fifth {Cl : Type} {names : List String}
    {runs : Given → Behind → Places → List (String × List Form)}
    {keys : Given → Behind → Places → List Form} {toCl : Form → Claim} {p : Par}
    {h : OnBytes.Model.Head.Shape} {iU3 : ℕ} (Pc : VerifiableInference.Desc.K1.Par)
    (link moment : ℕ) (arrays : Option (List ℕ)) (P : VerifiableInference.Desc.K8.ReadsQuiet.PH)
    {s s₁ s' e : S} {rs rs' : List Fmt.RoundView} {gs gs' : List (List (ℕ × List UInt64))}
    (hcom : (VerifiableInference.Desc.K1.commitAtS (Cl := Cl) Pc link moment arrays).decide s rs
      gs = .ok s₁)
    (hq : (ReadsQuiet.head P).decide s₁ rs' gs' = .ok s') (hw : withTables P s = some e)
    (states : ℕ → List (RunOf S)) (b : ℕ) (name : String)
    (hst : ∀ r, ((states b).find? fun r => r.1 == name) = some r →
      r ∈ runsBy names runs keys toCl p (seatAt h iU3))
    {R : VerifiableInference.Desc.K9.Read} (hR : readerOf states b name e = some R) :
    readerOf states b name s' = some R := by
  obtain ⟨o, tl', es', kj⟩ := keptJoin_fifth Pc link moment arrays P hcom hq hw iU3
  rw [es']
  exact reader_tl s₁ o o.tl tl' states b name hst (reader_fwd kj.more states b name hst hR)

/-- The like at "join". -/
theorem reader_join_fifth {Cl : Type} {iU3 : ℕ} (claim : Aff → Claim) (p : Par)
    (h : OnBytes.Model.Head.Shape) (Pc : VerifiableInference.Desc.K1.Par) (link moment : ℕ)
    (arrays : Option (List ℕ)) (P : VerifiableInference.Desc.K8.ReadsQuiet.PH) {s s₁ s' e : S}
    {rs rs' : List Fmt.RoundView} {gs gs' : List (List (ℕ × List UInt64))}
    (hcom : (VerifiableInference.Desc.K1.commitAtS (Cl := Cl) Pc link moment arrays).decide s rs
      gs = .ok s₁)
    (hq : (ReadsQuiet.head P).decide s₁ rs' gs' = .ok s') (hw : withTables P s = some e)
    (states : ℕ → List (RunOf S)) (b : ℕ) (name : String)
    (hst : ∀ r, ((states b).find? fun r => r.1 == name) = some r →
      r.2 = K3.joinRun (K3.seatCalls claim) (callerKeys p (seatAt h iU3)))
    {R : VerifiableInference.Desc.K9.Read} (hR : readerOf states b name e = some R) :
    readerOf states b name s' = some R := by
  obtain ⟨o, tl', es', kj⟩ := keptJoin_fifth Pc link moment arrays P hcom hq hw iU3
  rw [es']
  exact reader_join_tl claim p h iU3 s₁ o o.tl tl' states b name hst
    (reader_join_fwd kj claim p h states b name hst hR)

/-- Where the run is silent in front and the second reader answers: general in the run. -/
theorem fwd_hole {s s' : S} (H : LinkHoles) (l : Link S Claim)
    (P : VerifiableInference.Desc.K8.ReadsQuiet.PH) (b : ℕ) {name : String}
    (hne : (name == "K8.equations") = false) (hsil : H.silent = k6Silent P (statesOfLink l))
    (hno : readerOf (statesOfLink l) b name s = none)
    (k : ∀ e, withTables P s = some e → ∀ R, readerOf (statesOfLink l) b name e = some R →
      readerOf (statesOfLink l) b name s' = some R) :
    Fwd (readersOfLink H l) b name s s' := by
  intro R hR
  have hR' : (if (name == "K8.equations") = true then H.small s
    else
      match readerOf (statesOfLink l) b name s with
      | some R => some R
      | Option.none => H.silent b name s) = some R := hR
  rw [hne, hno, hsil] at hR'
  have hR'' : (withTables P s).bind (readerOf (statesOfLink l) b name) = some R := hR'
  obtain ⟨e, he, h1⟩ := Option.bind_eq_some_iff.1 hR''
  exact readers_of_run H l b hne (k e he R h1)

end VerifiableInference.Reads.Pass

#print axioms VerifiableInference.Reads.Pass.letters_tl
#print axioms VerifiableInference.Reads.Pass.run_alike
#print axioms VerifiableInference.Reads.Pass.reader_alike
#print axioms VerifiableInference.Reads.Pass.reader_join_alike
#print axioms VerifiableInference.Reads.Pass.reader_tl
#print axioms VerifiableInference.Reads.Pass.reader_join_tl
#print axioms VerifiableInference.Reads.Pass.keptJoin_fifth
#print axioms VerifiableInference.Reads.Pass.reader_fifth
#print axioms VerifiableInference.Reads.Pass.reader_join_fifth
#print axioms VerifiableInference.Reads.Pass.fwd_hole
