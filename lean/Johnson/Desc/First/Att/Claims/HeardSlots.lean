-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/HeardSlots.lean: kind K5: WHICH SLOTS THE KIND's RUNS OF CLAIMS NAME OR LOOK UNDER HANGS ON THE
PLACE's SHAPE AND ON WHAT WAS HEARD ALONE: not on the lookup's key points, not on the ledger, not on what the kind's road
returns. One record on (Ps, g, h) says "all of them meet Ps"; it is made by the hearing, it is monotone in Ps, and it pays the
named premise K5OkAt (Claims/InAt.lean) as that stands.

Why. A promise that rides from block to block is a test on the carried record alone. K5OkAt's clause slots speaks of every
ledger at which ptsFrom returns: no test can run over all ledgers; and that ptsFrom returns at all is not given by the hearing's
yes (its other refusals are public tests that a later step asks first).

Main names:
  SumSlots Ps hh n: of one masked sumcheck's record: the slots that its start form names; its coefficients' stretch; its first n
    end values' slots.
  HeardSlots Ps g h: of the record Heard (Att/Hear.lean), a clause a field; and that h.om and h.om'' have g.NP members.
  heardSlots_mono.
  heard_pts: HeardSlots Ps g h and pointsOf g zk h l = some p give PtsSlots Ps g p. heard_rows: with LeftIs and PointsAre:
    RowsSlots Ps p. (The two records: Claims/SlotsIn.lean.)
  MADE: heardSlots_of_said: Said x h G L (Att/K5SaidAll.lean) and GeoFits g x (Att/K05PtsSlots.lean) give
    HeardSlots (PscRun.Filled G) g h. heardSlots_of_hear: from the hearing's return.
  SPENT: k5OkAt_of_heardSlots: PscRun.Sized U and HeardSlots (PscRun.Filled U) c.geo h give K5OkAt c zk h U, at every zk.
IS IT EMPTY HERE?
  · At Ps := fun _ => True HeardSlots is the two sizes. At Ps := fun _ => False it fails (five asks Ps (h.five + 0)).
  · heard_pts and heard_rows say nothing where pointsOf or leftP returns nothing.
  · HeardSlots IS SHOWN OF NO REAL RECORD HERE: heardSlots_of_hear's premises are shown together of nothing. NO MEMBER, AT NO SIZE.
Limits. The proofs of MADE are the first halves of Att/K05PtsSlots.lean's pts_slots and Att/K05RowsSlots.lean's rows_slots, over
  their own lemmas. pts_slots' statement follows from this file's (the first example at the foot); rows_slots' follows UNDER
  GeoFits BESIDE, which it does not ask (the second): so it stays the better theorem. Neither is turned.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.InAt

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open OnBytes.PscRun (Filled Later)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ParC Geo Heard Left Pts)

/-- Of one masked sumcheck's record. -/
structure SumSlots (Ps : ℕ → Prop) (hh : MaskedSum.Heard) (n : ℕ) : Prop where
  start : SlotsIn Ps hh.start
  coefs : ∀ i, i < (MaskedSum.hidingAt (hh.vars.zip hh.r)).1.length → Ps (hh.first + i)
  ends : ∀ i, i < n → Ps (hh.sEnd + i)

/-- **Every slot of which the kind's claims speak, off the place's shape and what was heard.** -/
structure HeardSlots (Ps : ℕ → Prop) (g : Geo) (h : Heard) : Prop where
  rem : ∀ j ∈ h.remainders.toList, ∀ i, i < 3 → Ps (j + i)
  seven : ∀ o ∈ h.scores.toList, ∀ i, i < 7 → Ps (o.1 + i)
  units : ∀ x ∈ (g.scores.toArray.zip h.scores).toList, SumSlots Ps x.2.2 (2 * x.1.pcs.length)
  five : ∀ i, i < 5 → Ps (h.five + i)
  bits : ∀ i, i < g.lt → Ps (h.bits + i)
  two : ∀ i, i < 2 → Ps (h.two + i)
  values : ∀ i, i < 2 → Ps (h.values + i)
  maxima : ∀ i, i < g.NP → Ps (h.maxima + i)
  division : SumSlots Ps h.division (2 * g.NP)
  below : SumSlots Ps h.below (2 * g.NP)
  on : SumSlots Ps h.on (2 * g.NP)
  atIndex : SumSlots Ps h.atIndex (2 * g.NP)
  key : SumSlots Ps h.key (g.Lam + g.NP * g.lt)
  cells : SumSlots Ps h.cells (2 * g.NP)
  om : h.om.size = g.NP
  om'' : h.om''.size = g.NP

variable {Ps Qs : ℕ → Prop} {g : Geo} {h : Heard}

theorem sumSlots_mono (m : ∀ j, Ps j → Qs j) {hh : MaskedSum.Heard} {n : ℕ} (a : SumSlots Ps hh n) :
    SumSlots Qs hh n :=
  ⟨slotsIn_mono m a.start, fun i hi => m _ (a.coefs i hi), fun i hi => m _ (a.ends i hi)⟩

theorem heardSlots_mono (m : ∀ j, Ps j → Qs j) (a : HeardSlots Ps g h) : HeardSlots Qs g h where
  rem j hj i hi := m _ (a.rem j hj i hi)
  seven o ho i hi := m _ (a.seven o ho i hi)
  units x hx := sumSlots_mono m (a.units x hx)
  five i hi := m _ (a.five i hi)
  bits i hi := m _ (a.bits i hi)
  two i hi := m _ (a.two i hi)
  values i hi := m _ (a.values i hi)
  maxima i hi := m _ (a.maxima i hi)
  division := sumSlots_mono m a.division
  below := sumSlots_mono m a.below
  on := sumSlots_mono m a.on
  atIndex := sumSlots_mono m a.atIndex
  key := sumSlots_mono m a.key
  cells := sumSlots_mono m a.cells
  om := a.om
  om'' := a.om''

/-- A sumcheck's row names such slots alone, whatever its summand. -/
theorem SumSlots.row {hh : MaskedSum.Heard} {n : ℕ} (a : SumSlots Ps hh n) (S0 : E) :
    SlotsIn Ps (P.formOf hh S0 {}) := P.slotsIn_formOf hh S0 a.start a.coefs

variable {zk : Array (Array E)} {l : Left} {p : Pts}

/-- **What the claims read of what was heard.** -/
theorem heard_pts (a : HeardSlots Ps g h) (hp : P.pointsOf g zk h l = some p) : PtsSlots Ps g p := by
  have H := points_are hp
  refine ⟨fun pc hpc => ?_, fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases planes_members hp pc hpc with ⟨e3, hm⟩ | ⟨e5, o, ho, e0⟩
    · rw [e3]
      exact ⟨Nat.le_refl _, a.rem _ hm⟩
    · rw [e5, e0]
      exact ⟨by omega, fun i hi => a.seven o ho i (by omega)⟩
  · obtain ⟨⟨⟨u, o⟩, f⟩, hx, ⟨hsc, _, h0, hpw⟩, _⟩ := P.forall2_left H.units k hk
    rw [Array.toList_zip] at hx
    have h1 := (List.of_mem_zip hx).1
    have h1' := h1
    rw [Array.toList_zip] at h1'
    have ho : o ∈ h.scores.toList := (List.of_mem_zip h1').2
    rw [h0, hsc, hpw, P.pieces_size]
    exact ⟨a.seven o ho, (a.units (u, o) h1).ends⟩
  · rw [H.s5]; exact a.five
  · rw [H.sIB]; exact a.bits
  · rw [H.s5h]; exact a.two
  · rw [H.sCl]; exact a.values
  · rw [H.sM6]; exact a.maxima
  · rw [H.scE]; exact a.division.ends
  · rw [H.vpm]; exact a.below.ends
  · rw [H.vpd]; exact a.on.ends
  · rw [H.scF]; exact a.atIndex.ends
  · rw [H.scd]; exact a.key.ends
  · rw [H.scH]; exact a.cells.ends

/-- **The rows that the sumchecks leave.** -/
theorem heard_rows {F : Fork} (a : HeardSlots Ps g h) (li : P.LeftIs g zk h F l) (H : PointsAre g zk h l p) :
    RowsSlots Ps p := by
  obtain ⟨fu, ⟨_, e1⟩, ⟨_, e2⟩, ⟨_, e3⟩, ⟨_, e4⟩, ⟨_, e5⟩, ⟨_, e6⟩⟩ := li.forms
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨⟨⟨u, o⟩, f⟩, hx, ⟨hsc, _⟩, _⟩ := P.forall2_left H.units k hk
    rw [hsc]
    show SlotsIn _ f
    rw [Array.toList_zip] at hx
    obtain ⟨S0, e0⟩ := (List.forall₂_iff_zip.1 fu).2 hx
    rw [e0]
    exact (a.units (u, o) (List.of_mem_zip hx).1).row _
  · rw [H.scE]; show SlotsIn _ l.division; rw [e1]; exact a.division.row _
  · rw [H.vpm]; show SlotsIn _ l.below; rw [e2]; exact a.below.row _
  · rw [H.vpd]; show SlotsIn _ l.on; rw [e3]; exact a.on.row _
  · rw [H.scF]; show SlotsIn _ l.atIndex; rw [e4]; exact a.atIndex.row _
  · rw [H.scd]; show SlotsIn _ l.key; rw [e5]; exact a.key.row _
  · rw [H.scH]; show SlotsIn _ l.cells; rw [e6]; exact a.cells.row _

/-! ### spent -/

/-- **SPENT: the record at "filled in U" pays the named premise, at every key point.** -/
theorem k5OkAt_of_heardSlots {c : ParC} {U : Fork} (hU : PscRun.Sized U) (a : HeardSlots (Filled U) c.geo h)
    (zk : Array (Array E)) : K5OkAt c zk h U := by
  refine ⟨hU, a.om, a.om'', fun F' p hp => ?_⟩
  unfold P.ptsFrom at hp
  obtain ⟨l, hl, hq⟩ := Option.bind_eq_some_iff.1 hp
  exact ⟨heard_pts a hq, heard_rows a (P.leftP_spec hl) (points_are hq)⟩

/-! ### made -/

/-- A sumcheck as the hearing's law describes it, its start form's slots filled. -/
theorem sumSlots_of_sumAt {C : Aff} {st : P.Stage} {pre : List E} {H : OnBytes.Tie.Pv.Att.PscH}
    {hh : MaskedSum.Heard} {G : Fork} {n : ℕ} (s : P.SumAt C st pre H hh G) (hC : SlotsIn (Filled G) C)
    (he : ∀ i, i < n → Filled G (hh.sEnd + i)) : SumSlots (Filled G) hh n :=
  ⟨by rw [P.sumAt_start s]; exact hC, P.sumAt_coefs s, he⟩

theorem units_sum {G : Fork} : ∀ (ps : List (ℕ × ℕ)) (os : List (ℕ × MaskedSum.Heard)) (pre : List E)
    (l : List (List E × OnBytes.Tie.Pv.Att.PscH)), P.UnitsAt ps os pre l G → ∀ o ∈ os,
      ∃ t ∈ ps, SumSlots (Filled G) o.2 (2 * t.2)
  | [], [], _, [], _ => fun _ ho => by cases ho
  | u :: ps, o :: os, _, (_, _) :: l, ⟨a1, a2, a3, _, a5⟩ => fun o' ho => by
    rcases List.mem_cons.1 ho with rfl | ho
    · exact ⟨u, List.mem_cons_self ..,
        sumSlots_of_sumAt a3 (slotsIn_slot (P.putRun_fl a2 6 (by rw [a1]; omega))) (P.sumAt_ends a3)⟩
    · obtain ⟨t, ht, b⟩ := units_sum ps os [] l a5 o' ho
      exact ⟨t, List.mem_cons_of_mem _ ht, b⟩
  | [], [], _, _ :: _, h => h.elim
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim
  | _ :: _, _ :: _, _, [], h => h.elim

/-- **MADE: what the hearing's law says gives the record at "filled in the ledger behind the hearing".** -/
theorem heardSlots_of_said {x : Params.AttentionRounds} {G : Fork} {L : P.Lists} (hs : P.Said x h G L)
    (gf : P.GeoFits g x) : HeardSlots (Filled G) g h := by
  obtain ⟨o1, o2⟩ := om_sizes hs gf
  refine ⟨P.planesAt_fl _ _ hs.planes, fun o ho => (P.units_fl _ _ _ _ hs.units o ho).1, fun y hy => ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, o1, o2⟩
  · rw [Array.toList_zip] at hy
    have ho : y.2 ∈ h.scores.toList := (List.of_mem_zip hy).2
    have hu : y.1 ∈ g.scores := by simpa using (List.of_mem_zip hy).1
    obtain ⟨t, ht, b⟩ := units_sum _ _ _ _ hs.units y.2 ho
    refine ⟨b.start, b.coefs, fun i hi => b.ends i ?_⟩
    have := gf.pieces y.1 hu
    rw [gf.score t ht]
    omega
  · exact fun i hi => P.putRun_fl hs.p5 i (by rw [hs.l5]; exact hi)
  · rw [gf.lt]; exact fun i hi => P.putRun_fl hs.pI i (by rw [hs.lI]; exact hi)
  · exact fun i hi => P.putRun_fl hs.p2 i (by rw [hs.l2]; exact hi)
  · exact fun i hi => P.putRun_fl hs.pC i (by rw [hs.lC]; exact hi)
  · rw [gf.NP]; exact fun i hi => P.putRun_fl hs.pM i (by rw [hs.lM]; exact hi)
  · rw [gf.NP]
    exact sumSlots_of_sumAt hs.sE (slotsIn_slot (P.putRun_fl hs.p5 1 (by rw [hs.l5]; omega))) (P.sumAt_ends hs.sE)
  · rw [gf.NP]
    exact sumSlots_of_sumAt hs.sM (slotsIn_slot (P.putRun_fl hs.pC 0 (by rw [hs.lC]; omega))) (P.sumAt_ends hs.sM)
  · rw [gf.NP]
    exact sumSlots_of_sumAt hs.sVD (slotsIn_slot (P.putRun_fl hs.pC 1 (by rw [hs.lC]; omega))) (P.sumAt_ends hs.sVD)
  · rw [gf.NP]
    refine sumSlots_of_sumAt hs.sF (P.slotsIn_batched _ _ _ _ _ fun b hb => ?_) (P.sumAt_ends hs.sF)
    have := P.putRun_fl hs.pM b (by rw [hs.lM]; exact hb)
    rwa [show h.maxima + b = h.maxima + (1 * b + 0) by omega] at this
  · rw [gf.NP, gf.Lam, gf.lt]
    exact sumSlots_of_sumAt hs.sD (P.slotsIn_batched _ _ _ _ _ fun b hb => P.sumAt_ends hs.sF _ (by omega))
      (P.sumAt_endsKey hs.sD)
  · rw [gf.NP]
    exact sumSlots_of_sumAt hs.sH (slotsIn_ofConst _) (P.sumAt_ends hs.sH)

/-- The same from the hearing's return. -/
theorem heardSlots_of_hear {x : Params.AttentionRounds} {F G : Fork} {rs rest : List Fmt.RoundView} {lead : ℕ}
    (hh : P.hear x (F, rs, 0) = some (h, G, rest, lead)) (hz : Road.Sized F) (gf : P.GeoFits g x) :
    HeardSlots (Filled G) g h ∧ Road.Sized G := by
  obtain ⟨L, _, _, _, hs, zG, _⟩ := P.hear_said hh hz
  exact ⟨heardSlots_of_said hs gf, zG⟩

/-- A control: the record bites: at a predicate that fails at the first of the five it fails. -/
theorem heardSlots_bites (hn : ¬ Ps (h.five + 0)) : ¬ HeardSlots Ps g h := fun a => hn (a.five 0 (by omega))

/-- pts_slots' statement, by this file's road. -/
example {x : Params.AttentionRounds} {G : Fork} {L : P.Lists} (hs : P.Said x h G L)
    (hp : P.pointsOf g zk h l = some p) (gf : P.GeoFits g x) : PtsSlots (Filled G) g p :=
  heard_pts (heardSlots_of_said hs gf) hp

/-- rows_slots' statement, with GeoFits beside. -/
example {x : Params.AttentionRounds} {F G : Fork} {L : P.Lists} (li : P.LeftIs g zk h F l) (hs : P.Said x h G L)
    (H : PointsAre g zk h l p) (gf : P.GeoFits g x) : RowsSlots (Filled G) p :=
  heard_rows (heardSlots_of_said hs gf) li H

end K5Law

#print axioms K5Law.heard_pts
#print axioms K5Law.heard_rows
#print axioms K5Law.k5OkAt_of_heardSlots
#print axioms K5Law.heardSlots_of_said
#print axioms K5Law.heardSlots_of_hear
#print axioms K5Law.heardSlots_bites
