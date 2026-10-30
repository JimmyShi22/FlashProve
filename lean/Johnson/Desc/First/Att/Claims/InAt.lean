-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/InAt.lean: kind K5: what the kind's runs of claims read, AS A PLAIN FUNCTION
of what the lookup heard (g), what the kind heard (h) and A LEDGER (U); one named premise on a ledger
under which (a) the runs return at it what they return at any later ledger and (b) every slot that
their forms name is filled in it; and that premise's payer.

Why. A law on one run of claims fixes the run's forms at a snapshot taken before a draw, and hands in a
return at the live record. The kind's seat at the first chain's record (seatCO, Att/SeatO.lean) reads the
live ledger. Here the seat's five readers are written out, so that the ledger is a letter.

Main names:
  inAt c g h U · firstAt · secondAt: inOf's, firstK's and secondK's texts (Att/RunsK.lean) at seatCO.
  inOf_isAt · firstK_isAt · secondK_isAt: at a record in an attention segment they ARE those.
  K5OkAt c zk h U: THE NAMED PREMISE: U is sized; h.om and h.om'' have NP members; at whatever ledger
    ptsFrom returns, the two records of Claims/SlotsIn.lean hold of what it returns at "filled in U".
  k5OkAt_of_hearing: ITS PAYER: the hearing's return (h, G), a sized ledger in front, GeoFits, U later
    than G and sized.
  inAt_back · firstAt_back · secondAt_back: (a). firstAt_slots · secondAt_slots: (b).
IS IT EMPTY HERE?
  · Where a run refuses at the later ledger (a) says nothing; where it refuses at U, (b) says nothing.
  · K5OkAt's clause slots is idle where ptsFrom returns at no ledger.
  · K5OkAt IS SHOWN OF NO LEDGER HERE but through its payer, whose premises are shown together of nothing:
    no member, at no size.
Limits. Nothing of "keys" (it gathers no form) and of "join". Nothing on entries.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.SeatO
import Johnson.Desc.First.Att.Claims.EndsOfPts
import Johnson.Desc.First.Att.Claims.SlotsApart
import Johnson.Desc.First.Att.Claims.SlotsMono

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open OnBytes.PscRun (Filled Later)
open VerifiableInference.Desc (First.S First.AttOwn)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ParC Heard)

/-- What the runs read, and K: inOf's text at seatCO, the ledger a letter. -/
def inAt (c : ParC) (g : Forest.Heard) (h : Heard) (U : Fork) : Option (P.Runs.In × ℕ) := do
  let p ← P.ptsFrom c.geo g.zk h U
  let t ← P.tablesP c.geo c.mats c.nW (P.lookOfO c.geo.lmb g) p
  pure ({ g := c.geo, p := p, t := t, zk := g.zk, iU3 := c.iU3 }, ← (U.trees[c.iU3]?).map (·.K))

def firstAt (c : ParC) (g : Forest.Heard) (h : Heard) (U : Fork) : Option (List Aff) :=
  (inAt c g h U).bind fun x => (P.Runs.firstRun x.1 x.2).map (·.1)

def secondAt (c : ParC) (g : Forest.Heard) (h : Heard) (U : Fork) : Option (List Aff) :=
  (inAt c g h U).bind fun x => P.Runs.secondRun x.1 x.2

variable {c : ParC}

/-- **At a record in an attention segment inOf is inAt at that segment's own ledger.** -/
theorem inOf_isAt {e : First.S} {a : First.AttOwn} (he : e.here = .att a) :
    P.inOf (P.seatCO c) c e = a.g.bind fun g => a.heard5.bind fun h => inAt c g h a.F := by
  have h5 : e.heard5? = a.heard5 := by
    unfold First.S.heard5?
    rw [he]
  unfold P.inOf P.seatCO inAt
  simp only [he, h5]
  cases a.g with
  | none => rfl
  | some g =>
    cases a.heard5 with
    | none => rfl
    | some h => rfl

theorem firstK_isAt {e : First.S} {a : First.AttOwn} (he : e.here = .att a) :
    P.firstK (P.seatCO c) c e =
      (a.g.bind fun g => a.heard5.bind fun h => firstAt c g h a.F).map fun l => (l, e) := by
  unfold P.firstK firstAt
  rw [inOf_isAt he]
  cases a.g with
  | none => rfl
  | some g =>
    cases a.heard5 with
    | none => rfl
    | some h =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases inAt c g h a.F with
      | none => rfl
      | some x =>
        obtain ⟨i, K⟩ := x
        simp only [Option.bind_some]
        cases P.Runs.firstRun i K <;> rfl

theorem secondK_isAt {e : First.S} {a : First.AttOwn} (he : e.here = .att a) :
    P.secondK (P.seatCO c) c e =
      (a.g.bind fun g => a.heard5.bind fun h => secondAt c g h a.F).map fun l => (l, e) := by
  unfold P.secondK secondAt
  rw [inOf_isAt he]
  cases a.g with
  | none => rfl
  | some g =>
    cases a.heard5 with
    | none => rfl
    | some h =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases inAt c g h a.F with
      | none => rfl
      | some x =>
        obtain ⟨i, K⟩ := x
        simp only [Option.bind_some]
        cases P.Runs.secondRun i K <;> rfl

/-- **THE NAMED PREMISE, on a ledger.** -/
structure K5OkAt (c : ParC) (zk : Array (Array E)) (h : Heard) (U : Fork) : Prop where
  sized : PscRun.Sized U
  om : h.om.size = c.geo.NP
  om'' : h.om''.size = c.geo.NP
  slots : ∀ F' p, P.ptsFrom c.geo zk h F' = some p →
    PtsSlots (Filled U) c.geo p ∧ RowsSlots (Filled U) p

/-- A record of tables without a table: rows_slots (Att/K05RowsSlots.lean) takes a whole record of what the
runs read and looks at its shape and its points alone. -/
def noTables : P.TablesP := P.TablesP.mk #[] #[] 0 0 0 #[] 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 [] #[]

/-- **Its payer**: the ledger is later than the one that the kind's hearing returned. -/
theorem k5OkAt_of_hearing {x : Params.AttentionRounds} {F G U : Fork} {rs rest : List Fmt.RoundView} {lead : ℕ}
    {h : Heard} {zk : Array (Array E)} (hh : P.hear x (F, rs, 0) = some (h, G, rest, lead))
    (hz : Road.Sized F) (gf : P.GeoFits c.geo x) (hL : Later G U) (hU : PscRun.Sized U) :
    K5OkAt c zk h U := by
  obtain ⟨L, _, _, _, hs, _, _⟩ := P.hear_said hh hz
  obtain ⟨o1, o2⟩ := om_sizes hs gf
  refine ⟨hU, o1, o2, fun F' p hp => ?_⟩
  unfold P.ptsFrom at hp
  obtain ⟨l, hl, hq⟩ := Option.bind_eq_some_iff.1 hp
  have m : ∀ j, Filled G j → Filled U j := fun j hj => (hL.keep j hj).1
  exact ⟨ptsSlots_mono m (P.pts_slots hs hq gf),
    rowsSlots_mono m (P.rows_slots (i := { g := c.geo, p := p, t := noTables, zk := zk, iU3 := 0 })
      (P.leftP_spec hl) hs (points_are hq))⟩

variable {g : Forest.Heard} {h : Heard} {U G' : Fork}

/-- **(a) What inAt returns at a later ledger it returns at U.** -/
theorem inAt_back (Q : K5OkAt c g.zk h U) (hL : Later U G')
    (hK : (G'.trees[c.iU3]?).map (·.K) = (U.trees[c.iU3]?).map (·.K)) {x : P.Runs.In × ℕ}
    (e : inAt c g h G' = some x) : inAt c g h U = some x := by
  unfold inAt at e ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at e ⊢
  obtain ⟨p, hp, t, ht, K, hk, r⟩ := e
  exact ⟨p, ptsFrom_back' (shownBack_of_later hL Q.sized) hp (Q.slots G' p hp).1 Q.om Q.om'', t, ht, K,
    hK ▸ hk, r⟩

theorem firstAt_back (Q : K5OkAt c g.zk h U) (hL : Later U G')
    (hK : (G'.trees[c.iU3]?).map (·.K) = (U.trees[c.iU3]?).map (·.K)) {l : List Aff}
    (e : firstAt c g h G' = some l) : firstAt c g h U = some l := by
  unfold firstAt at e ⊢
  obtain ⟨x, hx, r⟩ := Option.bind_eq_some_iff.1 e
  exact Option.bind_eq_some_iff.2 ⟨x, inAt_back Q hL hK hx, r⟩

theorem secondAt_back (Q : K5OkAt c g.zk h U) (hL : Later U G')
    (hK : (G'.trees[c.iU3]?).map (·.K) = (U.trees[c.iU3]?).map (·.K)) {l : List Aff}
    (e : secondAt c g h G' = some l) : secondAt c g h U = some l := by
  unfold secondAt at e ⊢
  obtain ⟨x, hx, r⟩ := Option.bind_eq_some_iff.1 e
  exact Option.bind_eq_some_iff.2 ⟨x, inAt_back Q hL hK hx, r⟩

/-- What inAt returns holds the place's shape and what ptsFrom returned. -/
theorem inAt_pts {x : P.Runs.In × ℕ} (e : inAt c g h U = some x) :
    x.1.g = c.geo ∧ P.ptsFrom c.geo g.zk h U = some x.1.p := by
  unfold inAt at e
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at e
  obtain ⟨p, hp, t, _, K, _, r⟩ := e
  rw [← Option.some.inj r]
  exact ⟨rfl, hp⟩

/-- **(b) Every slot that a form of "first" at U names is filled in U.** -/
theorem firstAt_slots (Q : K5OkAt c g.zk h U) {l : List Aff} (e : firstAt c g h U = some l) :
    ∀ f ∈ l, ∀ x ∈ f.slots.toList, Filled U x.1 := by
  unfold firstAt at e
  obtain ⟨x, hx, r⟩ := Option.bind_eq_some_iff.1 e
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 r
  obtain ⟨eg, hp⟩ := inAt_pts hx
  obtain ⟨q1, q2⟩ := Q.slots U _ hp
  exact first_slots_K05 (j := y.2) (eg ▸ q1) q2 hy

theorem secondAt_slots (Q : K5OkAt c g.zk h U) {l : List Aff} (e : secondAt c g h U = some l) :
    ∀ f ∈ l, ∀ x ∈ f.slots.toList, Filled U x.1 := by
  unfold secondAt at e
  obtain ⟨x, hx, r⟩ := Option.bind_eq_some_iff.1 e
  obtain ⟨eg, hp⟩ := inAt_pts hx
  obtain ⟨q1, q2⟩ := Q.slots U _ hp
  exact second_slots_K05 (eg ▸ q1) q2 r

end K5Law

#print axioms K5Law.inOf_isAt
#print axioms K5Law.firstK_isAt
#print axioms K5Law.secondK_isAt
#print axioms K5Law.k5OkAt_of_hearing
#print axioms K5Law.firstAt_back
#print axioms K5Law.secondAt_back
#print axioms K5Law.firstAt_slots
#print axioms K5Law.secondAt_slots
