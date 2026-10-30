-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Own.lean: CONDITIONAL: the frame of the sentence "the forms that an
attention segment's own runs of claims gather are worth 0, with each entry of the array of its
tables read as the stated function of the committed cells" (`formsTQ`,
Johnson/Desc/Sound/FormsQ.lean), at the verifier's state just behind the lay of the segment's own
rounds, for the three runs "first", "keys" and "second": it follows from what the claims say
(`SayAt`, Johnson/Desc/First/Att/Claims/SayAt.lean) in that sentence's own world.

The sentence has five clauses: the open segment's part is there; the reader returns the run's
forms; its late slots pass a test; each form passes a public test; each form is worth 0. Here the
first four are paid by the library's laws on the state behind the lay, and the fifth is carried
back to `SayAt`, which is an equivalence of the library's (`say_at`). No algebra is in this file.
The run "keys" gathers no form: its sentence holds of the empty list and says nothing on a value.

Main names:
  `worldBehind St own s a h G rd`: the sentence's world at the state behind the lay.
  `formsTQ_of`: the sentence from its clauses, at a reader that returns forms and no late slot.
  `own_of_zero`: the three runs' sentences, from "every gathered form is worth 0".
  `own_of_say`: the same from `SayAt`.
  `own_of_runs`: **the same with the runs' returns taken from the library's `RunsReturn`**
    (Johnson/Desc/First/Att/K05MadeAt.lean): `SayAt` is asked at whatever the claims' reading at the
    state returns.

THE PREMISES OF `own_of_runs`, AND WHAT THE LIBRARY HAS FOR EACH:
  hRd: the reader Rd returns what the generic reader at the segment's runs returns:
    `hRds_of_link` (Johnson/Desc/First/Att/K05ReadersLink.lean) has the like, at every name but
    "K8.equations", of the readers made of a link (`readersOfLink`), at what the link's own blocks
    state (`statesOfLink`) in the place of the segment's runs. That the two agree, and that the
    reader in a caller's sentence is that one, are further ties, not shown here.
  hh: the hearing of the segment's own rounds returns: a clause of the block's yes.
  hz: the ledger in front is sized: a field of `FrontAll`
    (Johnson/Desc/First/Att/K05BehindWorth.lean).
  Rt: `runsReturn_at` (Johnson/Desc/First/Att/K05RunsReturn.lean), under tests on public data
    (`K5Public`), what the lookup leaves (`K3LeftOutIs`), `FrontAll`, and that every slot which the
    lookup's last claim names is filled (`FilledA`); also three equations between the stored plan
    and the planner's, that the segment is open at the state, and that the hearing of
    its own rounds returns at the parameters' `p.own` (the same as hh where x is `p.own`).
  gf: a test with code on public numbers (`GeoFits`).
  U: three facts on the state in front (`U3There`, Johnson/Desc/First/Att/K05FormsMade.lean).
  hg: what the lookup returned is laid in the open segment.
  hS: `SayAt`: the algebra; not in this file.
`FrontAll` and `U3There` both follow from one list on the state in front, of six tests with code, a
bound on the ledger's slots, and equations (`DoorYes`, Johnson/Desc/First/Att/K05DoorYes.lean: by
`frontAll_of_door` and `u3There_of_sheet`).

Limits. That any premise is met at a state of an honest run is not shown here. That `DoorYes`
follows from the promise which the table of the verifier's blocks carries in front of this block is
not shown in this file; on it see Johnson/Desc/K5/Honest/Law/DoorNarrow.lean and DoorAtHead.lean,
which show it conditionally. That the table's item on the segment's own forms
stands for just these three runs at piece 2 is not in this file. "join" and the lookup's "planes"
are not spoken of.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05MadeAt
import Johnson.Desc.First.Att.Claims.SayAt
import Johnson.Desc.Sound.FormsQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc (First.S First.AttOwn named)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (behind partAt hear runsN GeoFits U3There RunsReturn)
open VerifiableInference.Desc.K9 (affInT lateOk Read Readers segAt? mergeOf readerOf)
open VerifiableInference.Desc.Sound (GQ Stated worldOwn dataQ formsTQ MsgQ)

/-- The world in which the sentence evaluates the forms, at the state behind the lay: the slots off
the ledger behind the hearing and the mask row, no late slot; each array's cells off the witness's
tables, the arrays of the second sending read through the letter St. -/
noncomputable def worldBehind (St : Stated) (own : List (ℕ × ℕ)) (s : First.S) (a : First.AttOwn)
    (h : P.Heard) (G : Fork) (rd : ℕ × ℕ → MsgQ) : World GQ :=
  worldOwn (partAt s a G none) [] (St.at1 (behind s a h G) (dataQ own (partAt s a G none) rd))

/-- The sentence from its clauses, at a reader that returns the forms l and no late slot.
Conditional on these clauses: hp, hm, hr, ha, h0. -/
theorem formsTQ_of (Rd : Readers) (St : Stated) (own : List (ℕ × ℕ)) {b : ℕ} {name : String}
    {s : First.S} {l : List Aff} {part : VerifiableInference.Desc.K9.Part} (rd : ℕ × ℕ → MsgQ)
    (hp : segAt? s = some part) (hm : mergeOf s = none)
    (hr : Rd.forms b name s = some { forms := l, late := [] })
    (ha : ∀ f ∈ l, affInT own none [] part f = true)
    (h0 : ∀ f ∈ l, f.value Reading.gl (worldOwn part [] (St.at1 s (dataQ own part rd))) = 0) :
    formsTQ Rd St own b name s rd :=
  ⟨part, { forms := l, late := [] }, hp, hr, rfl, fun f hf => ⟨by rw [hm]; exact ha f hf, h0 f hf⟩⟩

section
variable {s : First.S} {a : First.AttOwn} {x : Params.AttentionRounds} {rs : List Fmt.RoundView}
  {h : P.Heard} {G : Fork} {i : P.Runs.In} {K : ℕ}

/-- **The three runs' sentences, from "every gathered form is worth 0".** Conditional; the premises
are those listed in the file's head, with the runs' returns written out, and h0. -/
theorem own_of_zero (Rd : Readers) (St : Stated) (A : Attention.Plan) (own : List (ℕ × ℕ))
    (hRd : ∀ (name : String) (R : Read), (name == "K8.equations") = false →
      readerOf (fun _ => runsN A) 2 name (behind s a h G) = some R →
      Rd.forms 2 name (behind s a h G) = some R)
    (hh : hear x (a.F, rs, 0) = some (h, G, [], 0)) (hz : OnBytes.Model.Road.Sized a.F)
    (hin : P.inOf (P.seatCO (P.parCOf A)) (P.parCOf A) (behind s a h G) = some (i, K))
    {l₁ l₂ : List Aff} {j : P.Runs.JoinsP} (h1 : P.Runs.firstRun i K = some (l₁, j))
    (h2 : P.Runs.secondRun i K = some l₂) {kf : Array Aff}
    (hk : P.keysOfK (P.seatCO (P.parCOf A)) (P.parCOf A) (behind s a h G) = some kf)
    (gf : GeoFits (P.parCOf A).geo x) (U : U3There own s a (P.parCOf A)) (rd : ℕ × ℕ → MsgQ)
    (h0 : K5Law.AllZero Reading.gl (worldBehind St own s a h G rd) (l₁ ++ l₂)) :
    ∀ name ∈ ["first", "keys", "second"], formsTQ Rd St own 2 name (behind s a h G) rd := by
  have hT := P.k5_forms_there own hh hz hin h1 h2 gf U none
  have hG : (behind s a h G).fork? = some G := rfl
  have hm : mergeOf (behind s a h G) = none := rfl
  intro name hn
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hn
  rcases hn with rfl | rfl | rfl
  · refine formsTQ_of (l := l₁) Rd St own rd P.segAt_behind hm (hRd _ _ rfl
      (P.readerOf_runN (P.find_first A) ?_ hG
        fun f hf => P.all_ownRow (hT f (List.mem_append_left _ hf)).2))
      (fun f hf => (hT f (List.mem_append_left _ hf)).1)
      fun f hf => h0 f (List.mem_append_left _ hf)
    show named "K5.first" (P.firstK _ _ _) = _
    unfold P.firstK
    simp [hin, h1, named]
  · refine formsTQ_of (l := []) Rd St own rd P.segAt_behind hm (hRd _ _ rfl
      (P.readerOf_runN (P.find_keys A) ?_ hG fun f hf => by cases hf))
      (fun f hf => by cases hf) fun f hf => by cases hf
    show named "K5.keys" (P.keysK _ _ _) = _
    unfold P.keysK
    simp [hk, named]
  · refine formsTQ_of (l := l₂) Rd St own rd P.segAt_behind hm (hRd _ _ rfl
      (P.readerOf_runN (P.find_second A) ?_ hG
        fun f hf => P.all_ownRow (hT f (List.mem_append_right _ hf)).2))
      (fun f hf => (hT f (List.mem_append_right _ hf)).1)
      fun f hf => h0 f (List.mem_append_right _ hf)
    show named "K5.second" (P.secondK _ _ _) = _
    unfold P.secondK
    simp [hin, h2, named]

/-- **The same from what the claims say.** Conditional: as `own_of_zero`, with hg: what the lookup
returned is laid in the open segment, and hS: `SayAt` in the sentence's world, in the place of
h0. -/
theorem own_of_say (Rd : Readers) (St : Stated) (A : Attention.Plan) (own : List (ℕ × ℕ))
    (hRd : ∀ (name : String) (R : Read), (name == "K8.equations") = false →
      readerOf (fun _ => runsN A) 2 name (behind s a h G) = some R →
      Rd.forms 2 name (behind s a h G) = some R)
    (hh : hear x (a.F, rs, 0) = some (h, G, [], 0)) (hz : OnBytes.Model.Road.Sized a.F)
    (hin : P.inOf (P.seatCO (P.parCOf A)) (P.parCOf A) (behind s a h G) = some (i, K))
    {l₁ l₂ : List Aff} {j : P.Runs.JoinsP} (h1 : P.Runs.firstRun i K = some (l₁, j))
    (h2 : P.Runs.secondRun i K = some l₂) {kf : Array Aff}
    (hk : P.keysOfK (P.seatCO (P.parCOf A)) (P.parCOf A) (behind s a h G) = some kf)
    (gf : GeoFits (P.parCOf A).geo x) (U : U3There own s a (P.parCOf A)) (rd : ℕ × ℕ → MsgQ)
    {gL : Forest.Heard} (hg : a.g = some gL)
    (hS : K5Law.SayAt Reading.gl (worldBehind St own s a h G rd) A.S gL i K) :
    ∀ name ∈ ["first", "keys", "second"], formsTQ Rd St own 2 name (behind s a h G) rd := by
  obtain ⟨eg, _, _, g, l, _, hg', _, hp, _⟩ := P.inOf_behind hin
  obtain rfl : gL = g := Option.some.inj (hg.symm.trans hg')
  have ezk : i.zk = gL.zk := by
    have e := (K5Law.inOf_some _ _ _ _ _ hin).2.2.1
    have e' : (a.g.map fun g => g.zk) = some i.zk := e
    rw [hg] at e'
    exact (Option.some.inj e').symm
  rw [← eg] at hp
  refine own_of_zero Rd St A own hRd hh hz hin h1 h2 hk gf U rd ?_
  -- The plan that the equivalence takes stands in one premise alone (its number of calls is the
  -- shape's) and nowhere in the conclusion: so the plan with that number laid in serves.
  exact (K5Law.say_at GQ Reading.gl _ { A with NC := A.S.calls.size } A.S gL i K l₁ l₂ j eg ezk rfl
    (K5Law.units_visited (K5Law.points_are hp)) h1 h2).2 hS

end

/-- **The frame of the sentence on the segment's own runs.** Conditional; each premise, and what
the library has for it, is listed in the file's head. `SayAt` is asked at whatever the claims'
reading at the state behind the lay returns. -/
theorem own_of_runs (Rd : Readers) (St : Stated) (A : Attention.Plan) (own : List (ℕ × ℕ))
    {s : First.S} {a : First.AttOwn} {x : Params.AttentionRounds} {rs : List Fmt.RoundView} {h : P.Heard}
    {G : Fork}
    (hRd : ∀ (name : String) (R : Read), (name == "K8.equations") = false →
      readerOf (fun _ => runsN A) 2 name (behind s a h G) = some R →
      Rd.forms 2 name (behind s a h G) = some R)
    (hh : hear x (a.F, rs, 0) = some (h, G, [], 0)) (hz : OnBytes.Model.Road.Sized a.F)
    (Rt : RunsReturn A s a h G) (gf : GeoFits (P.parCOf A).geo x)
    (U : U3There own s a (P.parCOf A)) (rd : ℕ × ℕ → MsgQ) {gL : Forest.Heard}
    (hg : a.g = some gL)
    (hS : ∀ i K, P.inOf (P.seatCO (P.parCOf A)) (P.parCOf A) (behind s a h G) = some (i, K) →
      K5Law.SayAt Reading.gl (worldBehind St own s a h G rd) A.S gL i K) :
    ∀ name ∈ ["first", "keys", "second"], formsTQ Rd St own 2 name (behind s a h G) rd := by
  obtain ⟨i, K, l₁, l₂, j, kf, _, _, hin, h1, h2, hk, _⟩ := Rt
  exact own_of_say Rd St A own hRd hh hz hin h1 h2 hk gf U rd hg (hS i K hin)

end H2K5.Honest

#print axioms H2K5.Honest.formsTQ_of
#print axioms H2K5.Honest.own_of_zero
#print axioms H2K5.Honest.own_of_say
#print axioms H2K5.Honest.own_of_runs
