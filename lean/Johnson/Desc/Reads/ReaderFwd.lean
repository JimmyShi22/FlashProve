-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/ReaderFwd.lean: the reader of the output head's three own runs of claims answers
behind what it answers in front, across every step that keeps what the reader reads.

Why. `forms_back` and `formsIn_fwd` (Reads/FormsPass.lean) take `Fwd`: what the reader answers at
the state in front it answers at the state behind. The reader of a run is the run itself, called at
the state (`readerOf`, Johnson/Desc/First/Batch/ReaderOf.lean). `KeptAll` (Reads/RowAtSeat.lean) was
cut to another use and holds too little for that.

What is stated and shown.
  `KeptMore iU3 s s'`: `KeptAll`, and where both states stand in the output head's segment: the same
    state of the squares' sumcheck; the ledger behind is later than the ledger in front
    (`OnBytes.PscRun.Later`); every array has as many own rows. Derived from the reader's text: of
    `KeptAll`'s ten equations the three on the approximate range proof's part are not spent here.
  `look_fwd`, `request_fwd`, `given_fwd`, `heard_fwd`, `reads_fwd`: the seat's readers, one by one.
  `letters_fwd`: **where all the kind's letters are there in front, the same letters are there
    behind.**
  `run_fwd`: where a run of the kind's own claims accepts in front, it accepts behind with the same
    claims, and returns the state behind.
  `ownRow_fwd`, `head_of_letters`: tools: the reader's test on an entry reads the number of own rows
    alone; where all the letters are there, the state stands in the output head's segment.
  `reader_fwd`: **what `readerOf` answers in front at such a run it answers behind.**

Limits. The run "join" is not reached: it also reads a mark in the ledger's list of owed claims.
`KeptMore` is a premise: it is shown here of no sub-protocol. One direction. Nothing on soundness.


-/
import Johnson.Desc.Reads.KeptSmall
import Johnson.Desc.Reads.ClaimsAtRecord
import Johnson.Desc.Reads.LedgerFwd
import Johnson.Desc.Reads.FormsPass
import Johnson.Desc.Kinds.Law.K6Silent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.Pass

open OnBytes.Model (Fork Ent)
open OnBytes.PscRun (Later)
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K8 (ReadsQuiet.bind_ok ReadsQuiet.named_ok)
open VerifiableInference.Desc.K9 (readerOf RunOf ownRow lateOf)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law (lateOf_got)
open VerifiableInference.Reads.AtSeat (KeptAll run_returns)

/-- What the reader of the output head's own runs reads is kept. -/
structure KeptMore (iU3 : ℕ) (s s' : S) : Prop where
  all : KeptAll iU3 s s'
  sq : ∀ o o' : HeadOwn, s.here = .head o → s'.here = .head o' → o'.squaresP = o.squaresP
  later : ∀ o o' : HeadOwn, s.here = .head o → s'.here = .head o' → Later o.F o'.F
  rows : ∀ o o' : HeadOwn, s.here = .head o → s'.here = .head o' →
    ∀ t : ℕ, (o'.F.trees[t]?).map (·.R) = (o.F.trees[t]?).map (·.R)

theorem look_fwd {iU3 : ℕ} {s s' : S} (k : KeptAll iU3 s s') {o : HeadOwn}
    (ho : s.here = .head o) : s'.lookHeard? = s.lookHeard? := by
  obtain ⟨o', ho', a1, _, a3, _⟩ := k.own o ho
  unfold S.lookHeard?
  rw [ho, ho']
  show (if o'.opened = true then o'.lookHeard else none) =
    if o.opened = true then o.lookHeard else none
  rw [a1, a3]

theorem request_fwd {iU3 : ℕ} {s s' : S} (k : KeptAll iU3 s s') : requestOf s' = requestOf s := by
  unfold requestOf S.tokv S.rowR S.rowE S.reqT
  rw [k.req]

theorem given_fwd {iU3 : ℕ} {s s' : S} (k : KeptAll iU3 s s') {o : HeadOwn}
    (ho : s.here = .head o) (p : Par) (h : OnBytes.Model.Head.Shape) :
    given p (seatAt h iU3) s' = given p (seatAt h iU3) s := by
  have e1 : (seatAt h iU3).lookup s' = (seatAt h iU3).lookup s := by
    show (s'.lookHeard?.map fun g => (g.zx, fun c => g.zk.getD c #[])) =
      s.lookHeard?.map fun g => (g.zx, fun c => g.zk.getD c #[])
    rw [look_fwd k ho]
  have e2 : Reply.token (seatAt h iU3).toSeat s' = Reply.token (seatAt h iU3).toSeat s := by
    show (s'.out.reply).map _ = (s.out.reply).map _
    rw [k.reply]
  have e3 : (seatAt h iU3).request s' = (seatAt h iU3).request s := request_fwd k
  unfold given
  rw [e1, e2, e3]

theorem heard_fwd {iU3 : ℕ} {s s' : S} (k : KeptMore iU3 s s') (h : OnBytes.Model.Head.Shape)
    {H : HeardAll} (hH : (seatAt h iU3).heard s = some H) :
    (∃ o, s.here = .head o) ∧ (seatAt h iU3).heard s' = some H := by
  have hH' : (match s.here with
    | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
      allOf o.F x (some (keptOf q x.wpl.sL))
    | _ => none) = some H := hH
  cases ho : s.here with
  | head o =>
    rw [ho] at hH'
    obtain ⟨o', ho', _, a2, _⟩ := k.all.own o ho
    refine ⟨⟨o, rfl⟩, ?_⟩
    show (match s'.here with
      | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
        allOf o.F x (some (keptOf q x.wpl.sL))
      | _ => none) = some H
    rw [ho']
    show (o'.squaresP.bind fun q => o'.x.bind fun x =>
      allOf o'.F x (some (keptOf q x.wpl.sL))) = some H
    rw [k.sq o o' ho ho', a2]
    obtain ⟨q, hq, h1⟩ := Option.bind_eq_some_iff.1 hH'
    obtain ⟨x, hx, h2⟩ := Option.bind_eq_some_iff.1 h1
    rw [hq, hx]
    exact allOf_fwd (k.later o o' ho ho') h2
  | _ =>
    rw [ho] at hH'
    cases hH'

theorem reads_fwd {iU3 : ℕ} {s s' : S} (k : KeptAll iU3 s s') {o : HeadOwn}
    (ho : s.here = .head o) (h : OnBytes.Model.Head.Shape) :
    (seatAt h iU3).reads s' = (seatAt h iU3).reads s := by
  obtain ⟨o', ho', a1, _, _, a4, _, _, _, a8⟩ := k.own o ho
  unfold seatAt
  dsimp only
  unfold S.fork?
  rw [ho, ho']
  dsimp only
  rw [a1]
  by_cases hop : o.opened = true
  · rw [if_pos hop, if_pos hop]
    dsimp only
    rw [a4]
    cases ht : o.t with
    | none => rfl
    | some tt =>
      cases h1 : o.F.trees[iU3]? with
      | none =>
        rw [h1] at a8
        cases h2 : o'.F.trees[iU3]? with
        | none => rfl
        | some tr' =>
          rw [h2] at a8
          cases a8
      | some tr =>
        rw [h1] at a8
        cases h2 : o'.F.trees[iU3]? with
        | none =>
          rw [h2] at a8
          cases a8
        | some tr' =>
          rw [h2] at a8
          have eK : tr'.K = tr.K := Option.some.inj a8
          simp only [Option.bind_some]
          rw [eK]
  · rw [if_neg hop, if_neg hop]

/-- **The same letters behind.** -/
theorem letters_fwd {iU3 : ℕ} {s s' : S} (k : KeptMore iU3 s s') (p : Par)
    (h : OnBytes.Model.Head.Shape) {v : Given × Behind × Places}
    (hl : lettersAt p (seatAt h iU3) s = .ok v) : lettersAt p (seatAt h iU3) s' = .ok v := by
  unfold lettersAt at hl ⊢
  obtain ⟨g, hg, hl⟩ := ReadsQuiet.bind_ok hl
  obtain ⟨H, hH, hl⟩ := ReadsQuiet.bind_ok hl
  obtain ⟨⟨o, ho⟩, hH'⟩ := heard_fwd k h (ReadsQuiet.named_ok hH)
  rw [given_fwd k.all ho p h, hg, hH', reads_fwd k.all ho h]
  rw [ReadsQuiet.named_ok hH] at hH
  exact hl

/-- A run of the kind's own claims. -/
theorem run_fwd {Cl : Type} {names : List String}
    {runs : Given → Behind → Places → List (String × List Form)}
    {keys : Given → Behind → Places → List Form} {toCl : Form → Cl} {p : Par}
    {h : OnBytes.Model.Head.Shape} {iU3 : ℕ} {s s' : S} (k : KeptMore iU3 s s')
    {c : String × (ℕ → S → Except String (List Cl × S))}
    (hc : c ∈ runsBy names runs keys toCl p (seatAt h iU3)) {n : ℕ} {y : List Cl × S}
    (hr : c.2 n s = .ok y) : c.2 n s' = .ok (y.1, s') := by
  unfold runsBy at hc
  obtain ⟨name, -, rfl⟩ := List.mem_map.1 hc
  dsimp only at hr ⊢
  obtain ⟨⟨g, b, x⟩, h1, hr⟩ := ReadsQuiet.bind_ok hr
  obtain ⟨fs, h2, hr⟩ := ReadsQuiet.bind_ok hr
  rw [letters_fwd k p h h1]
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

/-- The reader's test on an entry. -/
theorem ownRow_fwd {F G : Fork}
    (hR : ∀ t : ℕ, (G.trees[t]?).map (·.R) = (F.trees[t]?).map (·.R))
    (x : Ent) : ownRow G x = ownRow F x := by
  unfold ownRow
  have e := hR x.tree
  cases h1 : F.trees[x.tree]? with
  | none =>
    rw [h1] at e
    cases h2 : G.trees[x.tree]? with
    | none => rfl
    | some T' =>
      rw [h2] at e
      cases e
  | some T =>
    rw [h1] at e
    cases h2 : G.trees[x.tree]? with
    | none =>
      rw [h2] at e
      cases e
    | some T' =>
      rw [h2] at e
      have eR : T'.R = T.R := Option.some.inj e
      show (T'.R == 1 && x.row == 0) = (T.R == 1 && x.row == 0)
      rw [eR]

/-- Where all the kind's letters are there, the state stands in the output head's segment. -/
theorem head_of_letters {p : Par} {h : OnBytes.Model.Head.Shape} {iU3 : ℕ} {s : S}
    {v : Given × Behind × Places} (hl : lettersAt p (seatAt h iU3) s = .ok v) :
    ∃ o, s.here = .head o := by
  unfold lettersAt at hl
  obtain ⟨g, _, hl⟩ := ReadsQuiet.bind_ok hl
  obtain ⟨H, hH, _⟩ := ReadsQuiet.bind_ok hl
  have hH' : (match s.here with
    | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
      allOf o.F x (some (keptOf q x.wpl.sL))
    | _ => none) = some H := ReadsQuiet.named_ok hH
  cases ho : s.here with
  | head o => exact ⟨o, rfl⟩
  | _ =>
    rw [ho] at hH'
    cases hH'

/-- **What the reader answers in front at a run of the kind's own claims it answers behind.** -/
theorem reader_fwd {names : List String}
    {runs : Given → Behind → Places → List (String × List Form)}
    {keys : Given → Behind → Places → List Form} {toCl : Form → Claim} {p : Par}
    {h : OnBytes.Model.Head.Shape} {iU3 : ℕ} {s s' : S} (k : KeptMore iU3 s s')
    (states : ℕ → List (RunOf S)) (b : ℕ) (name : String)
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
    obtain ⟨g, bh, pl, fs, hl, -, -⟩ := VerifiableInference.Reads.AtSeat.letters_of_run hc hz
    obtain ⟨o, ho⟩ := head_of_letters hl
    obtain ⟨o', ho', a1, _⟩ := k.all.own o ho
    have ez : z.2 = s := run_returns h iU3 hc hz
    by_cases hop : o.opened = true
    · have hF : s.fork? = some o.F := by
        unfold S.fork?
        rw [ho]
        simp [hop]
      have hF' : s'.fork? = some o'.F := by
        unfold S.fork?
        rw [ho']
        simp [a1, hop]
      rw [hz, hF] at hR
      rw [run_fwd k hc hz, hF']
      have hR' : ((z.2.fork?).bind fun G =>
          if (z.1.all fun c => c.runs.isEmpty && c.eqFirst.isNone &&
            c.form.ents.all (ownRow o.F)) = true then
            some ({ forms := z.1.map (·.form), late := lateOf o.F G } :
              VerifiableInference.Desc.K9.Read) else none) = some R := hR
      rw [ez, hF, Option.bind_some, lateOf_got o.F o.F rfl] at hR'
      show ((s'.fork?).bind fun G =>
          if (z.1.all fun c => c.runs.isEmpty && c.eqFirst.isNone &&
            c.form.ents.all (ownRow o'.F)) = true then
            some ({ forms := z.1.map (·.form), late := lateOf o'.F G } :
              VerifiableInference.Desc.K9.Read) else none) = some R
      have eo : ownRow o'.F = ownRow o.F := funext (ownRow_fwd (k.rows o o' ho ho'))
      rw [hF', Option.bind_some, lateOf_got o'.F o'.F rfl, eo]
      exact hR'
    · have hF : s.fork? = none := by
        unfold S.fork?
        rw [ho]
        simp [hop]
      rw [hz, hF] at hR
      cases hR

end VerifiableInference.Reads.Pass

#print axioms VerifiableInference.Reads.Pass.look_fwd
#print axioms VerifiableInference.Reads.Pass.request_fwd
#print axioms VerifiableInference.Reads.Pass.given_fwd
#print axioms VerifiableInference.Reads.Pass.heard_fwd
#print axioms VerifiableInference.Reads.Pass.reads_fwd
#print axioms VerifiableInference.Reads.Pass.letters_fwd
#print axioms VerifiableInference.Reads.Pass.run_fwd
#print axioms VerifiableInference.Reads.Pass.ownRow_fwd
#print axioms VerifiableInference.Reads.Pass.head_of_letters
#print axioms VerifiableInference.Reads.Pass.reader_fwd
