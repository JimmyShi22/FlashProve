-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/HeardPlain.lean: kind K5: WHICH ENTRIES THE FORMS OF "first" AND "second" NAME, FROM WHAT IS HELD AS HEARD AND A LEDGER ALONE, with no word of the hearing's law: every entry is
an entry of ROW 0 OF THE ARRAY OF THE READS, below the tables' planned length.

Why. Claims/Covered.lean's law (a run at a time: Claims/CoveredApart.lean) takes RowsCov: the rows that the runs read name entries of the tables' part alone. Johnson/Desc/First/Att/K05RowsCov.lean pays it from the
hearing's law Said. A law that speaks at what is fixed before a later draw holds what was heard, not the hearing. Of Said that proof spends one thing: of each heard sumcheck the form "start". These name
no entry at all.

Main names:
  NoEnts f: the form names no entry. HeardPlain h: so of the "start" of every sumcheck that h holds: a record on h alone.
  MADE: heardPlain_of_said: from the hearing's law, by K05RowsCov.lean's own lemmas at the length 0.
  SPENT: cov_of_noEnts · rowsCov_of_plain (rows_cov's proof, the record in Said's place) · inAt_parts · first_named | second_named: **the entries that the runs' forms name.**
  heardPlain_bites: a control: a record whose "division" starts at a form with an entry fails it.
IS IT EMPTY HERE? first_named | second_named speak where firstAt | secondAt (Claims/InAt.lean) return. HeardPlain is shown of what a hearing with Said returns.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05RowsCov
import Johnson.Desc.First.Att.Claims.CoveredApart
import Johnson.Desc.First.Att.Claims.InAt

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ParC Heard Left Geo)

/-- The form names no entry. -/
def NoEnts (f : Aff) : Prop := f.ents.toList = []

/-- **No "start" of a heard sumcheck names an entry.** -/
structure HeardPlain (h : Heard) : Prop where
  units : ∀ o ∈ h.scores.toList, NoEnts o.2.start
  division : NoEnts h.division.start
  below : NoEnts h.below.start
  on : NoEnts h.on.start
  atIndex : NoEnts h.atIndex.start
  key : NoEnts h.key.start
  cells : NoEnts h.cells.start

theorem cov_of_noEnts {iU3 K nW : ℕ} {f : Aff} (h : NoEnts f) : Cov iU3 K nW f := by
  intro e he
  rw [h] at he
  cases he

/-- Covered at the length 0 is "no entry". -/
theorem noEnts_of_cov0 {iU3 K : ℕ} {f : Aff} (h : Cov iU3 K 0 f) : NoEnts f := by
  unfold NoEnts
  refine List.eq_nil_iff_forall_not_mem.2 fun e he => ?_
  obtain ⟨x, hx, _⟩ := h e he
  exact Nat.not_lt_zero x hx

/-- **MADE.** -/
theorem heardPlain_of_said {x : Params.AttentionRounds} {h : Heard} {G : Fork} {L : P.Lists} (hs : P.Said x h G L) :
    HeardPlain h :=
  ⟨fun o ho => noEnts_of_cov0 (iU3 := 0) (K := 0) (P.units_cov _ _ _ _ hs.units o ho),
    noEnts_of_cov0 (iU3 := 0) (K := 0) (by rw [P.sumAt_start hs.sE]; exact cov_slot _),
    noEnts_of_cov0 (iU3 := 0) (K := 0) (by rw [P.sumAt_start hs.sM]; exact cov_slot _),
    noEnts_of_cov0 (iU3 := 0) (K := 0) (by rw [P.sumAt_start hs.sVD]; exact cov_slot _),
    noEnts_of_cov0 (iU3 := 0) (K := 0) (by rw [P.sumAt_start hs.sF]; exact P.cov_batched _ _ _ _ _),
    noEnts_of_cov0 (iU3 := 0) (K := 0) (by rw [P.sumAt_start hs.sD]; exact P.cov_batched _ _ _ _ _),
    noEnts_of_cov0 (iU3 := 0) (K := 0) (by rw [P.sumAt_start hs.sH]; exact cov_ofConst _)⟩

variable {K nW : ℕ}

/-- **SPENT: RowsCov, the record in the hearing's law's place.** -/
theorem rowsCov_of_plain {i : P.Runs.In} {zk : Array (Array E)} {h : Heard} {l : Left} {F : Fork}
    (li : P.LeftIs i.g zk h F l) (hc : HeardPlain h) (H : PointsAre i.g zk h l i.p) : RowsCov i K nW := by
  obtain ⟨fu, ⟨_, e1⟩, ⟨_, e2⟩, ⟨_, e3⟩, ⟨_, e4⟩, ⟨_, e5⟩, ⟨_, e6⟩⟩ := li.forms
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨⟨⟨u, o⟩, f⟩, hx, ⟨hsc, _⟩, _⟩ := P.forall2_left H.units k hk
    rw [hsc]
    show Cov _ _ _ f
    rw [Array.toList_zip] at hx
    obtain ⟨S0, e0⟩ := (List.forall₂_iff_zip.1 fu).2 hx
    rw [e0]
    refine P.cov_formOf _ _ (cov_of_noEnts (hc.units o ?_))
    have h1 := (List.of_mem_zip hx).1
    rw [Array.toList_zip] at h1
    exact (List.of_mem_zip h1).2
  · rw [H.scE]
    show Cov _ _ _ l.division
    rw [e1]
    exact P.cov_formOf _ _ (cov_of_noEnts hc.division)
  · rw [H.vpm]
    show Cov _ _ _ l.below
    rw [e2]
    exact P.cov_formOf _ _ (cov_of_noEnts hc.below)
  · rw [H.vpd]
    show Cov _ _ _ l.on
    rw [e3]
    exact P.cov_formOf _ _ (cov_of_noEnts hc.on)
  · rw [H.scF]
    show Cov _ _ _ l.atIndex
    rw [e4]
    exact P.cov_formOf _ _ (cov_of_noEnts hc.atIndex)
  · rw [H.scd]
    show Cov _ _ _ l.key
    rw [e5]
    exact P.cov_formOf _ _ (cov_of_noEnts hc.key)
  · rw [H.scH]
    show Cov _ _ _ l.cells
    rw [e6]
    exact P.cov_formOf _ _ (cov_of_noEnts hc.cells)

variable {c : ParC} {g : Forest.Heard} {h : Heard} {U : Fork}

/-- What inAt's return holds. -/
theorem inAt_parts {x : P.Runs.In × ℕ} (e : inAt c g h U = some x) :
    x.1.g = c.geo ∧ x.1.iU3 = c.iU3 ∧ (U.trees[c.iU3]?).map (·.K) = some x.2 ∧
      (∃ l, P.LeftIs c.geo g.zk h U l ∧ P.pointsOf c.geo g.zk h l = some x.1.p) ∧
      P.tablesP c.geo c.mats c.nW (P.lookOfO c.geo.lmb g) x.1.p = some x.1.t := by
  unfold inAt at e
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at e
  obtain ⟨p, hp, t, ht, K', hk, r⟩ := e
  obtain rfl := Option.some.inj r
  unfold P.ptsFrom at hp
  obtain ⟨l, hl, hq⟩ := Option.bind_eq_some_iff.1 hp
  exact ⟨rfl, rfl, hk, ⟨l, P.leftP_spec hl, hq⟩, ht⟩

/-- The two premises of Claims/CoveredApart.lean's laws, at what inAt returns. -/
theorem cov_parts {x : P.Runs.In × ℕ} (e : inAt c g h U = some x) (hc : HeardPlain h) :
    LenIn x.1 c.nW ∧ RowsCov x.1 x.2 c.nW := by
  obtain ⟨eg, _, _, ⟨l, li, hp⟩, ht⟩ := inAt_parts e
  rw [← eg] at li hp ht
  exact ⟨len_in ht, rowsCov_of_plain li hc (points_are hp)⟩

/-- **The entries that the forms of "first" name.** -/
theorem first_named {l : List Aff} (e : firstAt c g h U = some l) (hc : HeardPlain h) {T : HTree}
    (hT : U.trees[c.iU3]? = some T) (hW : c.nW ≤ T.K) :
    ∀ f ∈ l, ∀ x ∈ f.ents.toList, x.tree = c.iU3 ∧ x.row = 0 ∧ x.idx < c.nW := by
  unfold firstAt at e
  obtain ⟨y, hy, e1⟩ := Option.bind_eq_some_iff.1 e
  obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 e1
  obtain ⟨_, eu, hk, _, _⟩ := inAt_parts hy
  obtain ⟨hL, hR⟩ := cov_parts hy hc
  have eK : T.K = y.2 := by rw [hT] at hk; exact Option.some.inj hk
  intro f hf x hx
  have := row0_of_cov (eK ▸ hW) (first_cov_K05 hL hR (j := z.2) hz f hf x hx)
  rwa [eu] at this

/-- **The entries that the forms of "second" name.** -/
theorem second_named {l : List Aff} (e : secondAt c g h U = some l) (hc : HeardPlain h) {T : HTree}
    (hT : U.trees[c.iU3]? = some T) (hW : c.nW ≤ T.K) :
    ∀ f ∈ l, ∀ x ∈ f.ents.toList, x.tree = c.iU3 ∧ x.row = 0 ∧ x.idx < c.nW := by
  unfold secondAt at e
  obtain ⟨y, hy, hz⟩ := Option.bind_eq_some_iff.1 e
  obtain ⟨_, eu, hk, _, _⟩ := inAt_parts hy
  obtain ⟨hL, hR⟩ := cov_parts hy hc
  have eK : T.K = y.2 := by rw [hT] at hk; exact Option.some.inj hk
  intro f hf x hx
  have := row0_of_cov (eK ▸ hW) (second_cov_K05 hL hR hz f hf x hx)
  rwa [eu] at this

/-- A control: a "division" that starts at a form with an entry fails the record. -/
theorem heardPlain_bites (h : Heard) (e : h.division.start = Aff.ent 0 0 0) : ¬ HeardPlain h := by
  intro a
  have := a.division
  unfold NoEnts at this
  rw [e] at this
  simp [Aff.ent] at this

end K5Law

#print axioms K5Law.heardPlain_of_said
#print axioms K5Law.rowsCov_of_plain
#print axioms K5Law.first_named
#print axioms K5Law.second_named
#print axioms K5Law.heardPlain_bites
