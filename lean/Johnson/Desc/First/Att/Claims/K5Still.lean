-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/K5Still.lean: kind K5: THE KIND's THREE RUNS OF CLAIMS ARE "Still"
(the tool of Johnson/Desc/First/Link/Law/StillRun.lean): a yes hands the record back, and at a
state that goes on from q the claims are the plain claims of forms READ OFF q; and the tool's premise
hOk (every slot that a form names is filled in the snapshot) for "first" and "second".

The tool and its imports are other files.
NOTHING COUNTED.

The letters. φ, Ok: the letters that all kinds share. rd: a reader on φ's values.
  hrd : ∀ e, rd (φ e) = psiAtt e: φ shows what the lookup heard and what the kind heard
    (psiAtt, Johnson/Desc/First/Link/Law/PhiAtt.lean).
  hQ : ∀ q u g h, Ok q → q.2 = some u → rd q.1 = some (g, h) → K5OkAt c g.zk h u.F: THE NAMED PREMISE ON
    Ok (K5OkAt, Claims/InAt.lean; its payer k5OkAt_of_hearing: the snapshot's ledger is sized and later
    than the one that the kind's hearing returned).
Main names:
  rFirst · rKeys · rSecond c: the kind's three named runs of forms at seatCO; runsK_is: they ARE the list
    runsK (seatCO c) c, by its text. runFirst · runKeys · runSecond c: the same as runs of claims.
  fsFirst · fsSecond rd c q: firstAt | secondAt (Claims/InAt.lean) at rd q.1 and the snapshot's ledger.
    fsKeys: no form.
  still_first · still_keys · still_second. hOk_first · hOk_keys · hOk_second: in still_plainOk's letters.
  first_runOk · second_runOk · keys_runOk: THE TOOL CALLED (still_runOk): RunOk of the three runs; of "first"
    and "second" under hrd, hQ and the tool's hFu; of "keys" under nothing.
IS IT EMPTY HERE?
  · Still's two fields speak of a yes: where a run refuses they say nothing.
  · still_keys needs neither hrd nor hQ.
  · hrd AND hQ ARE SHOWN OF NO φ AND NO Ok HERE. At an Ok that nothing meets all is idle.
Limits. The tool's other premise hFu (what the named entries are worth at a full state) is not spoken of.
  The fourth run of the kind's list, the lookup's "join", is no Still run and is not spoken of.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Link.Law.StillRun
import Johnson.Desc.First.Link.Law.PhiAtt
import Johnson.Desc.First.Att.Claims.InAt
import Johnson.Desc.First.Att.Claims.RunsHand
import Johnson.Desc.First.Att.Claims.ReadsNext

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open OnBytes.PscRun (Filled Later)
open VerifiableInference.Desc (First.S First.AttOwn Claim named)
open VerifiableInference.Desc.K9 (atS runOfForms)
open VerifiableInference.Desc.K9L (Pub9 Fx9 GoesOn)
open VerifiableInference.Desc.StillRun (Still)
open VerifiableInference.Desc.PhiAll (psiAtt psiAtt_at goesOn_K get_att)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ParC Heard)

variable {α : Type}

/-- The three named runs of forms, as runsK (Att/RunsK.lean) writes them, at seatCO. -/
def rFirst (c : ParC) : String × (ℕ → First.S → Except String (List Aff × First.S)) :=
  ("first", fun _ s => named "K5.first" (P.firstK (P.seatCO c) c s))
def rKeys (c : ParC) : String × (ℕ → First.S → Except String (List Aff × First.S)) :=
  ("keys", fun _ s => named "K5.keys" (P.keysK (P.seatCO c) c s))
def rSecond (c : ParC) : String × (ℕ → First.S → Except String (List Aff × First.S)) :=
  ("second", fun _ s => named "K5.second" (P.secondK (P.seatCO c) c s))

/-- They are the kind's own list. -/
theorem runsK_is (c : ParC) : P.runsK (P.seatCO c) c = [rFirst c, rKeys c, rSecond c] := rfl

/-- The three, as runs of claims. -/
def runFirst (c : ParC) : ℕ → First.S → Except String (List Claim × First.S) := (runOfForms (rFirst c)).2
def runKeys (c : ParC) : ℕ → First.S → Except String (List Claim × First.S) := (runOfForms (rKeys c)).2
def runSecond (c : ParC) : ℕ → First.S → Except String (List Claim × First.S) := (runOfForms (rSecond c)).2

theorem rFirst_mem (c : ParC) : rFirst c ∈ P.runsK (P.seatCO c) c := by rw [runsK_is]; simp
theorem rKeys_mem (c : ParC) : rKeys c ∈ P.runsK (P.seatCO c) c := by rw [runsK_is]; simp
theorem rSecond_mem (c : ParC) : rSecond c ∈ P.runsK (P.seatCO c) c := by rw [runsK_is]; simp

/-- A run that returns stands in an attention segment. -/
theorem att_of_inOf {c : ParC} {e : First.S} {x : P.Runs.In × ℕ} (h : P.inOf (P.seatCO c) c e = some x) :
    ∃ a, e.here = .att a := by
  unfold P.inOf at h
  obtain ⟨p, hp, _⟩ := Option.bind_eq_some_iff.1 h
  have hp' : (P.seatCO c).pts e = some p := hp
  unfold P.seatCO at hp'
  cases he : e.here with
  | att a => exact ⟨a, rfl⟩
  | _ => simp only [he] at hp'; cases hp'

/-- The forms, read off q. -/
def fsFirst (rd : α → Option (Forest.Heard × Heard)) (c : ParC) (q : α × Option Pub9) : Option (List Aff) :=
  (rd q.1).bind fun gh => q.2.bind fun u => firstAt c gh.1 gh.2 u.F
def fsSecond (rd : α → Option (Forest.Heard × Heard)) (c : ParC) (q : α × Option Pub9) : Option (List Aff) :=
  (rd q.1).bind fun gh => q.2.bind fun u => secondAt c gh.1 gh.2 u.F
def fsKeys (_ : α × Option Pub9) : Option (List Aff) := some []

variable (φ : First.S → α) (Ok : α × Option Pub9 → Prop) (rd : α → Option (Forest.Heard × Heard)) (c : ParC)

/-- **"keys".** -/
theorem still_keys : Still φ Ok (runKeys c) fsKeys where
  hands n e cl e₁ h := (runOfForms_hands (P.seatCO c) c _ (rKeys_mem c) n e cl e₁ h).1
  forms q n e cl e₁ _ h := by
    obtain ⟨_, l, hl, rfl⟩ := runOfForms_hands (P.seatCO c) c _ (rKeys_mem c) n e cl e₁ h
    have hk : P.keysK (P.seatCO c) c e = some (l, e) := named_ok hl
    obtain ⟨_, _, r⟩ := Option.map_eq_some_iff.1 hk
    refine ⟨[], rfl, ?_⟩
    rw [← (Prod.mk.inj r).1]

variable (hrd : ∀ e, rd (φ e) = psiAtt e)
  (hQ : ∀ q u g h, Ok q → q.2 = some u → rd q.1 = some (g, h) → K5OkAt c g.zk h u.F)
include hrd hQ

/-- The core: a return of the live record's function of (g, h, ledger) is read off q. -/
theorem read_off_q {at_ : ParC → Forest.Heard → Heard → Fork → Option (List Aff)}
    (back : ∀ (g : Forest.Heard) (h : Heard) (U G' : Fork) (l : List Aff), K5OkAt c g.zk h U → Later U G' →
      (G'.trees[c.iU3]?).map (·.K) = (U.trees[c.iU3]?).map (·.K) → at_ c g h G' = some l →
        at_ c g h U = some l)
    {q : α × Option Pub9} {e : First.S} (hf : Fx9 φ Ok q e) {a : First.AttOwn} (he : e.here = .att a)
    {l : List Aff} (hl : (a.g.bind fun g => a.heard5.bind fun h => at_ c g h a.F) = some l) :
    ((rd q.1).bind fun gh => q.2.bind fun u => at_ c gh.1 gh.2 u.F) = some l := by
  obtain ⟨hok, hφ, u, b, hu, hb, go⟩ := hf
  obtain ⟨g, hg, hl⟩ := Option.bind_eq_some_iff.1 hl
  obtain ⟨h, hh, hl⟩ := Option.bind_eq_some_iff.1 hl
  have hr : rd q.1 = some (g, h) := by
    rw [← hφ, hrd, psiAtt_at e a he, hg, hh]
    try rfl
  have hF : b.F = a.F := get_att e b a hb he
  rw [hr, hu]
  show at_ c g h u.F = some l
  exact back g h u.F a.F l (hQ q u g h hok hu hr) (hF ▸ go.1) (hF ▸ goesOn_K go c.iU3) hl

/-- **"first".** -/
theorem still_first : Still φ Ok (runFirst c) (fsFirst rd c) where
  hands n e cl e₁ h := (runOfForms_hands (P.seatCO c) c _ (rFirst_mem c) n e cl e₁ h).1
  forms q n e cl e₁ hf h := by
    obtain ⟨_, l, hl, rfl⟩ := runOfForms_hands (P.seatCO c) c _ (rFirst_mem c) n e cl e₁ h
    have hk : P.firstK (P.seatCO c) c e = some (l, e) := named_ok hl
    obtain ⟨a, he⟩ : ∃ a, e.here = .att a := by
      unfold P.firstK at hk
      obtain ⟨x, hx, _⟩ := Option.bind_eq_some_iff.1 hk
      exact att_of_inOf hx
    rw [firstK_isAt he] at hk
    obtain ⟨l', hl', r⟩ := Option.map_eq_some_iff.1 hk
    obtain rfl : l' = l := (Prod.mk.inj r).1
    exact ⟨l', read_off_q φ Ok rd c hrd hQ (at_ := firstAt) (fun _ _ _ _ _ Q L K e => firstAt_back Q L K e) hf he hl',
      rfl⟩

/-- **"second".** -/
theorem still_second : Still φ Ok (runSecond c) (fsSecond rd c) where
  hands n e cl e₁ h := (runOfForms_hands (P.seatCO c) c _ (rSecond_mem c) n e cl e₁ h).1
  forms q n e cl e₁ hf h := by
    obtain ⟨_, l, hl, rfl⟩ := runOfForms_hands (P.seatCO c) c _ (rSecond_mem c) n e cl e₁ h
    have hk : P.secondK (P.seatCO c) c e = some (l, e) := named_ok hl
    obtain ⟨a, he⟩ : ∃ a, e.here = .att a := by
      unfold P.secondK at hk
      obtain ⟨x, hx, _⟩ := Option.bind_eq_some_iff.1 hk
      exact att_of_inOf hx
    rw [secondK_isAt he] at hk
    obtain ⟨l', hl', r⟩ := Option.map_eq_some_iff.1 hk
    obtain rfl : l' = l := (Prod.mk.inj r).1
    exact ⟨l', read_off_q φ Ok rd c hrd hQ (at_ := secondAt) (fun _ _ _ _ _ Q L K e => secondAt_back Q L K e) hf he hl',
      rfl⟩

omit hrd in
/-- **The tool's premise hOk, of "first"**, in still_plainOk's own letters. -/
theorem hOk_first : ∀ q l u, Ok q → fsFirst rd c q = some l → q.2 = some u →
    ∀ f ∈ l, ∀ x ∈ f.slots.toList, Filled u.F x.1 := by
  intro q l u hok hl hu
  unfold fsFirst at hl
  obtain ⟨gh, hr, hl⟩ := Option.bind_eq_some_iff.1 hl
  rw [hu] at hl
  exact firstAt_slots (hQ q u gh.1 gh.2 hok hu hr) hl

omit hrd in
/-- **Of "second".** -/
theorem hOk_second : ∀ q l u, Ok q → fsSecond rd c q = some l → q.2 = some u →
    ∀ f ∈ l, ∀ x ∈ f.slots.toList, Filled u.F x.1 := by
  intro q l u hok hl hu
  unfold fsSecond at hl
  obtain ⟨gh, hr, hl⟩ := Option.bind_eq_some_iff.1 hl
  rw [hu] at hl
  exact secondAt_slots (hQ q u gh.1 gh.2 hok hu hr) hl

omit hrd hQ in
/-- **Of "keys"**: no form. -/
theorem hOk_keys : ∀ (q : α × Option Pub9) l (u : Pub9), Ok q → fsKeys q = some l → q.2 = some u →
    ∀ f ∈ l, ∀ x ∈ f.slots.toList, Filled u.F x.1 := by
  intro q l u _ hl _ f hf
  obtain rfl : [] = l := Option.some.inj hl
  cases hf

/-! ### the tool, called: that the letters fit is Lean's own check -/

section Called
open VerifiableInference.Desc.K9L VerifiableInference.Desc.StillRun
variable {Kf : Type} [Field Kf] (ρ : Reading Kf) (Fu : First.S → Prop)
  (ent : α × Option Pub9 → Bound Kf → ℕ → ℕ → ℕ → Kf)

/-- **RunOk of "first"**, under the tool's premise hFu alone beside hrd and hQ. -/
theorem first_runOk
    (hFu : ∀ q l t b y, Fx9 φ Ok q t → Fu t → atS.get? t = some b → fsFirst rd c q = some l →
      ∀ f ∈ l, ∀ x ∈ f.ents.toList,
        (worldAt ρ b.L b.F y).entry x.tree x.row x.idx = ent q y x.tree x.row x.idx) :
    RunOk ρ atS (O9 φ Ok Fu) (Fx9 φ Ok) (runFirst c) (plainTm (valsStill ρ (fsFirst rd c) ent))
      (lenStill (fsFirst rd c)) :=
  still_runOk ρ φ Ok Fu _ _ (still_first φ Ok rd c hrd hQ) (hOk_first Ok rd c hQ) ent hFu

/-- **RunOk of "second".** -/
theorem second_runOk
    (hFu : ∀ q l t b y, Fx9 φ Ok q t → Fu t → atS.get? t = some b → fsSecond rd c q = some l →
      ∀ f ∈ l, ∀ x ∈ f.ents.toList,
        (worldAt ρ b.L b.F y).entry x.tree x.row x.idx = ent q y x.tree x.row x.idx) :
    RunOk ρ atS (O9 φ Ok Fu) (Fx9 φ Ok) (runSecond c) (plainTm (valsStill ρ (fsSecond rd c) ent))
      (lenStill (fsSecond rd c)) :=
  still_runOk ρ φ Ok Fu _ _ (still_second φ Ok rd c hrd hQ) (hOk_second Ok rd c hQ) ent hFu

omit hrd hQ in
/-- **RunOk of "keys"**: no premise: it has no form. -/
theorem keys_runOk :
    RunOk ρ atS (O9 φ Ok Fu) (Fx9 φ Ok) (runKeys c) (plainTm (valsStill ρ fsKeys ent)) (lenStill fsKeys) :=
  still_runOk ρ φ Ok Fu _ _ (still_keys φ Ok c) (hOk_keys Ok) ent (by
    intro q l t b y _ _ _ hl f hf
    obtain rfl : [] = l := Option.some.inj hl
    cases hf)

end Called

end K5Law

#print axioms K5Law.runsK_is
#print axioms K5Law.still_keys
#print axioms K5Law.still_first
#print axioms K5Law.still_second
#print axioms K5Law.hOk_first
#print axioms K5Law.hOk_second
#print axioms K5Law.hOk_keys
#print axioms K5Law.first_runOk
#print axioms K5Law.second_runOk
#print axioms K5Law.keys_runOk
