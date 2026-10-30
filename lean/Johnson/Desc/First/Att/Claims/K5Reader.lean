-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/K5Reader.lean: kind K5: THE GENERIC READER ("the reader is the run itself": readerOf,
Johnson/Desc/First/Batch/ReaderOf.lean) AT THE KIND's RUNS "first", "keys", "second": what it gives is the run's own list
of forms and no late slot; AND THE READER's FORMS' WORTH ARE THE RUN's VALUES (valsStill, Johnson/Desc/First/Link/Law/StillRun.lean) at one
named choice of the letter ent; and the tool's premise hFu at that choice, under one named test.

The reader, the sentences, the tool and kind K9's law stand in other files. NOTHING COUNTED.



Main names:
  runsN_is: the kind's four runs typed at claims by Att/SeatN.lean ARE those typed by Batch/ClaimsAtS.lean's runOfForms (rfl).
  lateOf_self · reader_run: the generic reader at a run of forms that hands the record back.
  statesK5 · find_first | find_keys | find_second: which run the reader finds under each name.
  reader_first | reader_second | reader_keys: FORTH: at a record in an attention segment, from firstAt | secondAt's return
    (Claims/InAt.lean) and "every entry names row 0 of an array with one own row".
  reader_first_inv | reader_second_inv | reader_keys_inv: BACK: whatever the reader gives is that.
  reader_one_first | reader_one_second: ONE ANSWER at an earlier and a later record of the segment (over Claims/InAtOne.lean), where
    what was heard stays, the ledger is later, the width and "one own row" stay, and K5OkAt holds at the earlier ledger.
  entOwn: THE CHOICE OF ent: entry i of row r of array t is the cell (r, i) of the array that the snapshot's table of arrays names at t.
  refWorld_own: at it the tool's world at the snapshot is the sentences' world of own rows, field for field.
  vals_first | vals_second | vals_keys: **the reader's forms' worth are the run's values**: kind K9's hitems' last clause.
  hFu_first | hFu_second: the tool's hFu at entOwn, UNDER hW: at a full state every entry that a form names meets oneWeight
    (Johnson/Desc/First/Batch/OneWeight.lean), by entry_join (Johnson/Desc/Sound/FormsJoin.lean).
IS IT EMPTY HERE? Implications. That the reader gives anything at a real record is not shown. hW IS SHOWN OF NOTHING: of oneWeight's three
  clauses "one own row" and "row 0" are K5's files' to show (Claims/CoveredApart.lean's row0_of_cov has the second); "THAT VIRTUAL ROW's ONE
  WEIGHT IS 1" IS A PUBLIC TEST AT A FULL STATE: WHOSE IT IS TO PAY IS OPEN.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.K5Still
import Johnson.Desc.First.Att.Claims.InAtOne
import Johnson.Desc.First.Att.SeatN
import Johnson.Desc.First.Batch.ReaderOf
import Johnson.Desc.Sound.FormsJoin

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc (First.S First.AttOwn Claim named)
open VerifiableInference.Desc.K9 (atS runOfForms ofForm RunOf readerOf lateOf ownRow oneWeight Read)
open VerifiableInference.Desc.K9L (Pub9 Fx9 GoesOn pubOf fixed9 worldAt entryAt Bound)
open VerifiableInference.Desc.StillRun (valsStill)
open VerifiableInference.Desc.K4Values (refWorld)
open VerifiableInference.Desc.PhiAll (psiAtt psiAtt_at get_att)
open VerifiableInference.Desc.Sound (GQ worldOwn entry_join)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ParC Heard)

/-- Two wrappers, one text. -/
theorem runsN_is (A : Attention.Plan) : P.runsN A = (P.runsO A).map runOfForms := rfl

theorem lateOf_self (F : Fork) : lateOf F F = [] := by
  unfold lateOf
  refine List.filterMap_eq_nil_iff.2 fun j _ => ?_
  cases F.gotF.getD j false <;> rfl

/-- **The generic reader at a run of forms that hands the record back.** -/
theorem reader_run {states : ℕ → List (RunOf First.S)} {b : ℕ} {name : String}
    {r : String × (ℕ → First.S → Except String (List Aff × First.S))} {s : First.S} {l : List Aff} {G : Fork}
    (hf : ((states b).find? fun x => x.1 == name) = some (runOfForms r)) (hr : r.2 0 s = .ok (l, s))
    (hG : s.fork? = some G) (ho : ∀ f ∈ l, f.ents.all (ownRow G) = true) :
    readerOf states b name s = some { forms := l, late := [] } := by
  unfold readerOf
  rw [hf]
  have h1 : (runOfForms r).2 0 s = .ok (l.map ofForm, s) := by
    unfold runOfForms
    simp only [hr]
    rfl
  simp only [Option.bind_some, h1, hG]
  have h2 : ((l.map ofForm).all fun c => c.runs.isEmpty && c.eqFirst.isNone && c.form.ents.all (ownRow G)) = true := by
    refine List.all_eq_true.2 fun c hc => ?_
    obtain ⟨f, hfl, rfl⟩ := List.mem_map.1 hc
    show (true && true && f.ents.all (ownRow G)) = true
    rw [ho f hfl]
    rfl
  rw [if_pos h2, lateOf_self, List.map_map]
  congr 2
  exact List.map_id' l

/-! ### at the kind's three runs -/

section K5
variable {α : Type} (A : Attention.Plan) {states : ℕ → List (RunOf First.S)}
  (hst : states 2 = (P.runsO A).map runOfForms)

include hst in
theorem find_first : ((states 2).find? fun x => x.1 == "first") = some (runOfForms (rFirst (P.parCOf A))) := by
  rw [hst]; rfl

include hst in
theorem find_keys : ((states 2).find? fun x => x.1 == "keys") = some (runOfForms (rKeys (P.parCOf A))) := by
  rw [hst]; rfl

include hst in
theorem find_second : ((states 2).find? fun x => x.1 == "second") = some (runOfForms (rSecond (P.parCOf A))) := by
  rw [hst]; rfl

theorem fork_att {e : First.S} {a₀ : First.AttOwn} (he : e.here = .att a₀) : e.fork? = some a₀.F := by
  unfold First.S.fork?
  rw [he]

include hst in
/-- **FORTH, "first".** -/
theorem reader_first {e : First.S} {a₀ : First.AttOwn} {l : List Aff} (he : e.here = .att a₀)
    (hl : (a₀.g.bind fun g => a₀.heard5.bind fun h => firstAt (P.parCOf A) g h a₀.F) = some l)
    (ho : ∀ f ∈ l, f.ents.all (ownRow a₀.F) = true) :
    readerOf states 2 "first" e = some { forms := l, late := [] } :=
  reader_run (find_first A hst)
    (by show named "K5.first" (P.firstK (P.seatCO (P.parCOf A)) (P.parCOf A) e) = .ok (l, e)
        rw [firstK_isAt he, hl]; rfl) (fork_att he) ho

include hst in
/-- **FORTH, "second".** -/
theorem reader_second {e : First.S} {a₀ : First.AttOwn} {l : List Aff} (he : e.here = .att a₀)
    (hl : (a₀.g.bind fun g => a₀.heard5.bind fun h => secondAt (P.parCOf A) g h a₀.F) = some l)
    (ho : ∀ f ∈ l, f.ents.all (ownRow a₀.F) = true) :
    readerOf states 2 "second" e = some { forms := l, late := [] } :=
  reader_run (find_second A hst)
    (by show named "K5.second" (P.secondK (P.seatCO (P.parCOf A)) (P.parCOf A) e) = .ok (l, e)
        rw [secondK_isAt he, hl]; rfl) (fork_att he) ho

/-- What the generic reader gives at a run of the three: the run's own list, no late slot. -/
theorem reader_inv {b : ℕ} {name : String} {r : String × (ℕ → First.S → Except String (List Aff × First.S))}
    (hm : r ∈ P.runsK (P.seatCO (P.parCOf A)) (P.parCOf A))
    (hf : ((states b).find? fun x => x.1 == name) = some (runOfForms r)) {e : First.S} {R : Read}
    (h : readerOf states b name e = some R) : ∃ l F, r.2 0 e = .ok (l, e) ∧ R = { forms := l, late := [] } ∧
      e.fork? = some F ∧ ∀ f ∈ l, f.ents.all (ownRow F) = true := by
  unfold readerOf at h
  rw [hf] at h
  simp only [Option.bind_some] at h
  cases hz : (runOfForms r).2 0 e with
  | error m => simp only [hz] at h; cases h
  | ok z =>
    obtain ⟨e1, l, hl, ecl⟩ := runOfForms_hands (P.seatCO (P.parCOf A)) (P.parCOf A) r hm 0 e z.1 z.2 hz
    cases hF : e.fork? with
    | none => simp only [hz, hF] at h; cases h
    | some F =>
      simp only [hz, hF, e1, Option.bind_some] at h
      split at h
      · rename_i hc
        refine ⟨l, F, hl, ?_, rfl, fun f hf => ?_⟩
        · rw [← Option.some.inj h, lateOf_self, ecl, List.map_map]
          congr 1
          exact List.map_id' l
        · rw [ecl] at hc
          have := List.all_eq_true.1 hc _ (List.mem_map.2 ⟨f, hf, rfl⟩)
          simp only [Bool.and_eq_true] at this
          exact this.2
      · cases h

include hst in
/-- **BACK, "first".** -/
theorem reader_first_inv {e : First.S} {R : Read} (h : readerOf states 2 "first" e = some R) :
    ∃ a₀ l, e.here = .att a₀ ∧ (a₀.g.bind fun g => a₀.heard5.bind fun h => firstAt (P.parCOf A) g h a₀.F) = some l ∧
      R = { forms := l, late := [] } ∧ ∀ f ∈ l, f.ents.all (ownRow a₀.F) = true := by
  obtain ⟨l, F, hl, rfl, hF, ho⟩ := reader_inv A (rFirst_mem (P.parCOf A)) (find_first A hst) h
  have hk : P.firstK (P.seatCO (P.parCOf A)) (P.parCOf A) e = some (l, e) := named_ok hl
  obtain ⟨a₀, he⟩ : ∃ a, e.here = .att a := by
    unfold P.firstK at hk
    obtain ⟨x, hx, _⟩ := Option.bind_eq_some_iff.1 hk
    exact att_of_inOf hx
  rw [firstK_isAt he] at hk
  obtain ⟨l', hl', r⟩ := Option.map_eq_some_iff.1 hk
  obtain rfl : l' = l := (Prod.mk.inj r).1
  obtain rfl : a₀.F = F := Option.some.inj ((fork_att he).symm.trans hF)
  exact ⟨a₀, l', he, hl', rfl, ho⟩

include hst in
/-- **BACK, "second".** -/
theorem reader_second_inv {e : First.S} {R : Read} (h : readerOf states 2 "second" e = some R) :
    ∃ a₀ l, e.here = .att a₀ ∧ (a₀.g.bind fun g => a₀.heard5.bind fun h => secondAt (P.parCOf A) g h a₀.F) = some l ∧
      R = { forms := l, late := [] } ∧ ∀ f ∈ l, f.ents.all (ownRow a₀.F) = true := by
  obtain ⟨l, F, hl, rfl, hF, ho⟩ := reader_inv A (rSecond_mem (P.parCOf A)) (find_second A hst) h
  have hk : P.secondK (P.seatCO (P.parCOf A)) (P.parCOf A) e = some (l, e) := named_ok hl
  obtain ⟨a₀, he⟩ : ∃ a, e.here = .att a := by
    unfold P.secondK at hk
    obtain ⟨x, hx, _⟩ := Option.bind_eq_some_iff.1 hk
    exact att_of_inOf hx
  rw [secondK_isAt he] at hk
  obtain ⟨l', hl', r⟩ := Option.map_eq_some_iff.1 hk
  obtain rfl : l' = l := (Prod.mk.inj r).1
  obtain rfl : a₀.F = F := Option.some.inj ((fork_att he).symm.trans hF)
  exact ⟨a₀, l', he, hl', rfl, ho⟩

include hst in
/-- **BACK, "keys"**: no form. -/
theorem reader_keys_inv {e : First.S} {R : Read} (h : readerOf states 2 "keys" e = some R) :
    R = { forms := [], late := [] } := by
  obtain ⟨l, _, hl, rfl, _, _⟩ := reader_inv A (rKeys_mem (P.parCOf A)) (find_keys A hst) h
  have hk : P.keysK (P.seatCO (P.parCOf A)) (P.parCOf A) e = some (l, e) := named_ok hl
  obtain ⟨_, _, r⟩ := Option.map_eq_some_iff.1 hk
  rw [← (Prod.mk.inj r).1]

/-! ### one answer at every border -/

section One
variable {s s' : First.S} {a a' : First.AttOwn} (hs : s.here = .att a) (hs' : s'.here = .att a') (hg : a'.g = a.g)
  (h5 : a'.heard5 = a.heard5) (hL : PscRun.Later a.F a'.F)
  (hK : (a'.F.trees[(P.parCOf A).iU3]?).map (·.K) = (a.F.trees[(P.parCOf A).iU3]?).map (·.K))
  (hO : ∀ x, ownRow a'.F x = ownRow a.F x)
  (Q : ∀ g h, a.g = some g → a.heard5 = some h → K5OkAt (P.parCOf A) g.zk h a.F)

include hst hs hs' hg h5 hL hK hO Q in
/-- **The reader of "first" gives one answer at an earlier and a later record of the segment.** -/
theorem reader_one_first : readerOf states 2 "first" s' = readerOf states 2 "first" s := by
  have e : (a'.g.bind fun g => a'.heard5.bind fun h => firstAt (P.parCOf A) g h a'.F) =
      a.g.bind fun g => a.heard5.bind fun h => firstAt (P.parCOf A) g h a.F := by
    rw [hg, h5]
    cases eg : a.g with
    | none => rfl
    | some g =>
      cases eh : a.heard5 with
      | none => rfl
      | some h => exact firstAt_one (Q g h eg eh) hL hK
  cases r' : readerOf states 2 "first" s' with
  | some R =>
    obtain ⟨b, l, hb, hl, rfl, ho⟩ := reader_first_inv A hst r'
    have eb : b = a' := by
      rw [hs'] at hb
      cases hb
      rfl
    rw [eb] at hl ho
    have ho' : ∀ f ∈ l, f.ents.all (ownRow a.F) = true := fun f hf => by
      rw [← show ownRow a'.F = ownRow a.F from funext hO]
      exact ho f hf
    exact (reader_first A hst hs (e.symm.trans hl) ho').symm
  | none =>
    cases r : readerOf states 2 "first" s with
    | none => rfl
    | some R =>
      obtain ⟨b, l, hb, hl, rfl, ho⟩ := reader_first_inv A hst r
      have eb : b = a := by
        rw [hs] at hb
        cases hb
        rfl
      rw [eb] at hl ho
      have ho' : ∀ f ∈ l, f.ents.all (ownRow a'.F) = true := fun f hf => by
        rw [show ownRow a'.F = ownRow a.F from funext hO]
        exact ho f hf
      rw [reader_first A hst hs' (e.trans hl) ho'] at r'
      cases r'

include hst hs hs' hg h5 hL hK hO Q in
/-- **So does the reader of "second".** -/
theorem reader_one_second : readerOf states 2 "second" s' = readerOf states 2 "second" s := by
  have e : (a'.g.bind fun g => a'.heard5.bind fun h => secondAt (P.parCOf A) g h a'.F) =
      a.g.bind fun g => a.heard5.bind fun h => secondAt (P.parCOf A) g h a.F := by
    rw [hg, h5]
    cases eg : a.g with
    | none => rfl
    | some g =>
      cases eh : a.heard5 with
      | none => rfl
      | some h => exact secondAt_one (Q g h eg eh) hL hK
  cases r' : readerOf states 2 "second" s' with
  | some R =>
    obtain ⟨b, l, hb, hl, rfl, ho⟩ := reader_second_inv A hst r'
    have eb : b = a' := by
      rw [hs'] at hb
      cases hb
      rfl
    rw [eb] at hl ho
    have ho' : ∀ f ∈ l, f.ents.all (ownRow a.F) = true := fun f hf => by
      rw [← show ownRow a'.F = ownRow a.F from funext hO]
      exact ho f hf
    exact (reader_second A hst hs (e.symm.trans hl) ho').symm
  | none =>
    cases r : readerOf states 2 "second" s with
    | none => rfl
    | some R =>
      obtain ⟨b, l, hb, hl, rfl, ho⟩ := reader_second_inv A hst r
      have eb : b = a := by
        rw [hs] at hb
        cases hb
        rfl
      rw [eb] at hl ho
      have ho' : ∀ f ∈ l, f.ents.all (ownRow a'.F) = true := fun f hf => by
        rw [show ownRow a'.F = ownRow a.F from funext hO]
        exact ho f hf
      rw [reader_second A hst hs' (e.trans hl) ho'] at r'
      cases r'

end One

/-! ### the worlds -/

/-- **THE CHOICE OF ent**: the array's own cell, by the snapshot's table of arrays. -/
def entOwn {Kf : Type} [Zero Kf] (q : α × Option Pub9) (y : Bound Kf) (t r i : ℕ) : Kf :=
  match q.2.bind fun u => u.arrayOf[t]? with
  | some x => y.cell x.1 x.2 r i
  | none => 0

/-- At it the tool's world at the snapshot is the sentences' world of own rows. -/
theorem refWorld_own (x : α) (b : VerifiableInference.Desc.K9.Part) (y : Bound GQ) :
    refWorld Reading.gl (pubOf b).F [] (entOwn (x, some (pubOf b)) y) y = worldOwn b [] y := by
  unfold refWorld worldOwn
  congr 1

variable (φ : First.S → α) (rd : α → Option (Forest.Heard × Heard)) (hrd : ∀ e, rd (φ e) = psiAtt e)

include hrd in
/-- The forms read off what is fixed at e are the live record's. -/
theorem fs_at {at_ : ParC → Forest.Heard → Heard → Fork → Option (List Aff)} {e : First.S}
    {b : VerifiableInference.Desc.K9.Part} {a₀ : First.AttOwn} (hb : atS.get? e = some b) (he : e.here = .att a₀) :
    ((rd (φ e)).bind fun gh => (some (pubOf b)).bind fun u => at_ (P.parCOf A) gh.1 gh.2 u.F) =
      a₀.g.bind fun g => a₀.heard5.bind fun h => at_ (P.parCOf A) g h a₀.F := by
  have hF : (pubOf b).F = a₀.F := get_att e b a₀ hb he
  rw [hrd, psiAtt_at e a₀ he]
  cases a₀.g with
  | none => rfl
  | some g =>
    cases a₀.heard5 with
    | none => rfl
    | some h => show at_ (P.parCOf A) g h (pubOf b).F = _; rw [hF]; rfl

include hst hrd in
/-- **THE READER's FORMS' WORTH ARE THE RUN's VALUES, "first".** -/
theorem vals_first {e : First.S} {b : VerifiableInference.Desc.K9.Part} {R : Read} (hb : atS.get? e = some b)
    (hR : readerOf states 2 "first" e = some R) (y : Bound GQ) :
    valsStill Reading.gl (fsFirst rd (P.parCOf A)) entOwn (fixed9 φ e) y =
      R.forms.map fun f => f.value Reading.gl (worldOwn b R.late y) := by
  obtain ⟨a₀, l, he, hl, rfl, _⟩ := reader_first_inv A hst hR
  have hq : fixed9 φ e = (φ e, some (pubOf b)) := by unfold fixed9; rw [hb]; rfl
  have hfs : fsFirst rd (P.parCOf A) (φ e, some (pubOf b)) = some l := (fs_at A φ rd hrd (at_ := firstAt) hb he).trans hl
  rw [hq]
  unfold valsStill
  simp only [hfs, Option.getD_some, refWorld_own]

include hst hrd in
/-- **"second".** -/
theorem vals_second {e : First.S} {b : VerifiableInference.Desc.K9.Part} {R : Read} (hb : atS.get? e = some b)
    (hR : readerOf states 2 "second" e = some R) (y : Bound GQ) :
    valsStill Reading.gl (fsSecond rd (P.parCOf A)) entOwn (fixed9 φ e) y =
      R.forms.map fun f => f.value Reading.gl (worldOwn b R.late y) := by
  obtain ⟨a₀, l, he, hl, rfl, _⟩ := reader_second_inv A hst hR
  have hq : fixed9 φ e = (φ e, some (pubOf b)) := by unfold fixed9; rw [hb]; rfl
  have hfs : fsSecond rd (P.parCOf A) (φ e, some (pubOf b)) = some l := (fs_at A φ rd hrd (at_ := secondAt) hb he).trans hl
  rw [hq]
  unfold valsStill
  simp only [hfs, Option.getD_some, refWorld_own]

include hst in
/-- **"keys"**: both sides are empty. -/
theorem vals_keys {e : First.S} {b : VerifiableInference.Desc.K9.Part} {R : Read} (hb : atS.get? e = some b)
    (hR : readerOf states 2 "keys" e = some R) (y : Bound GQ) :
    valsStill Reading.gl (fsKeys (α := α)) entOwn (fixed9 φ e) y =
      R.forms.map fun f => f.value Reading.gl (worldOwn b R.late y) := by
  rw [reader_keys_inv A hst hR]
  unfold valsStill fixed9
  rw [hb]
  rfl

/-! ### hFu at entOwn -/

/-- **The tool's premise hFu at entOwn**, general in the forms' reader fs, under the named test hW. -/
theorem hFu_own (Ok : α × Option Pub9 → Prop) (Fu : First.S → Prop) (fs : α × Option Pub9 → Option (List Aff))
    (hW : ∀ q l t b, Fx9 φ Ok q t → Fu t → atS.get? t = some b → fs q = some l →
      ∀ f ∈ l, ∀ x ∈ f.ents.toList, oneWeight b.F x = true ∧ (b.L.arrayOf[x.tree]?).isSome = true) :
    ∀ q l t b (y : Bound GQ), Fx9 φ Ok q t → Fu t → atS.get? t = some b → fs q = some l →
      ∀ f ∈ l, ∀ x ∈ f.ents.toList,
        (worldAt Reading.gl b.L b.F y).entry x.tree x.row x.idx = entOwn q y x.tree x.row x.idx := by
  intro q l t b y hf hfu hb hl f hfl x hx
  obtain ⟨w1, w2⟩ := hW q l t b hf hfu hb hl f hfl x hx
  obtain ⟨_, _, u, b0, hu, hb0, go⟩ := hf
  obtain rfl : b0 = b := Option.some.inj (hb0.symm.trans hb)
  obtain ⟨cc, hc⟩ := Option.isSome_iff_exists.1 w2
  have hc' : u.arrayOf[x.tree]? = some cc := by rw [← go.2.2.2.1]; exact hc
  show entryAt Reading.gl b0.L.arrayOf (treesFrame b0.F.trees) y x.tree x.row x.idx = _
  rw [entry_join b0.L.arrayOf b0.F y x cc hc w1]
  unfold entOwn
  rw [hu]
  show _ = match u.arrayOf[x.tree]? with
    | some z => y.cell z.1 z.2 x.row x.idx
    | none => 0
  rw [hc']

end K5

end K5Law

#print axioms K5Law.runsN_is
#print axioms K5Law.reader_first
#print axioms K5Law.reader_first_inv
#print axioms K5Law.reader_one_first
#print axioms K5Law.reader_one_second
#print axioms K5Law.refWorld_own
#print axioms K5Law.vals_first
#print axioms K5Law.vals_second
#print axioms K5Law.vals_keys
#print axioms K5Law.hFu_own
