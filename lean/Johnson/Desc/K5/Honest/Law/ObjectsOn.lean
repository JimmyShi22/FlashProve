-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/ObjectsOn.lean: CONDITIONAL: the lookup's forms "objects" of an attention
segment (the item `formsT m 2 "objects"` of the library's table, which stands for the two runs (1,
"objects") and (1, "guests") of the statements below) RIDE FORWARD over the block of the segment's
own rounds (kind K5): where the sentence holds at the state in front, it holds at EVERY state that
`K5Keeps` (Johnson/Desc/K5/Honest/Law/Returns.lean) ties to it, not at the step's own result alone.
Rules over letters: the readers and the stated function are letters.

Why. Of the six sorts of items that ride past that block this is the one that reads what the block
turns: the open ledger. The five others: Johnson/Desc/K5/Honest/Law/RidesK5.lean.

How. The library has the sentence riding BACK, at the step's result
(Johnson/Desc/First/Att/K05ObjectsBack.lean). Its ground is an equality: by the lookup's promise in
front, the worth of each of these rows at EVERY LATER LEDGER is one term of the mask row alone
(`Fo.RowIs`, OnBytes/Tie/Pv/Lookup/Forest/FoForm.lean). `K5Keeps` says that the ledger behind is a
later one and leaves the link, the statement, the book and the roots. So the worth is one at the
two states. The public test beside the worth goes up with the ledger by the library's `affInT_up`
(Johnson/Desc/First/Att/K05FormsKept.lean).

Main names:
  `keeps_att`: what `K5Keeps` leaves of the open segment: all but its ledger and what its own rounds
    heard.
  `part_behind`: the open segment's part at the state behind is the part in front with the ledger
    behind.
  `ledgerUp_keeps`: the library's `LedgerUp` between the two parts.
  `rowWorth_on`: one row: worth 0 at the earlier ledger gives worth 0 at the later one.
  `formsTQ_objects_on`: **the sentence rides forward.**
  `formsTQ_guests_on`: the item's second run: the reader answers with no form.

Who is meant to show the premises. hz, hrows: the lookup's promise in front. hS, hB: the readers'
law at the two states. mS, mB: the stated function leaves the mask row.

Limits. That any state meets the premises is not shown here. Nothing on any other item.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.Returns
import Johnson.Desc.First.Att.K05ObjectsBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att.P (restO attRest partAt segAt_front LedgerUp affInT_up Below
  Stays value_nil dataQ_part)
open VerifiableInference.Desc.K9 (Readers segAt? mergeOf)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated formsTQ worldOwn dataQ)
open VerifiableInference.Desc.K9L (Bound)

/-- What the kind's step leaves of the open segment: all but its ledger and what its own rounds
heard. Conditional: K; e, e': the open segment at the two states. -/
theorem keeps_att {s s' : S} (K : K5Keeps s s') {a a' : AttOwn} (e : s.here = .att a)
    (e' : s'.here = .att a') : attRest a' = attRest a := by
  have h := VerifiableInference.Desc.First.Att.P.rest_att s' s K.1
  simp only [e, e'] at h
  exact Option.some.inj h

/-- **The open segment's part at the state behind is the part in front with the ledger behind.**
Conditional: K; e, e'. -/
theorem part_behind {s s' : S} (K : K5Keeps s s') {a a' : AttOwn} (e : s.here = .att a)
    (e' : s'.here = .att a') (o : Option ℕ) : partAt s' a' a'.F o = partAt s a a'.F o := by
  have hr := keeps_att K e e'
  have h1 : a'.L = a.L := congrArg (·.L) hr
  have h2 : a'.tl = a.tl := congrArg (·.tl) hr
  have h3 : s'.st = s.st := VerifiableInference.Desc.First.Att.P.rest_st s' s K.1
  have h4 : s'.book = s.book := VerifiableInference.Desc.First.Att.P.rest_book s' s K.1
  have h5 : s'.roots = s.roots := VerifiableInference.Desc.First.Att.P.rest_roots s' s K.1
  unfold partAt
  rw [h1, h2, h3, h4, h5]

/-- The two ledgers of `K5Keeps`, at the open segments named. Conditional: K; e, e'. -/
theorem keeps_ledgers {s s' : S} (K : K5Keeps s s') {a a' : AttOwn} (e : s.here = .att a)
    (e' : s'.here = .att a') : PscRun.Later a.F a'.F ∧ Below a.F a'.F := by
  obtain ⟨_, b, b', f, f', lt, bl⟩ := K
  obtain rfl : b = a := Here.att.inj (f.symm.trans e)
  obtain rfl : b' = a' := Here.att.inj (f'.symm.trans e')
  exact ⟨lt, bl⟩

/-- **The library's "the ledger has grown" between the two parts.** Conditional: K; e, e'; hz: the
ledger in front has its arrays' lengths. -/
theorem ledgerUp_keeps {s s' : S} (K : K5Keeps s s') {a a' : AttOwn} (e : s.here = .att a)
    (e' : s'.here = .att a') (hz : Sized a.F) (o o' : Option ℕ) :
    LedgerUp (partAt s a a.F o) (partAt s a a'.F o') := by
  obtain ⟨lt, bl⟩ := keeps_ledgers K e e'
  obtain ⟨z1, z2, z3⟩ := lt.sized ⟨hz.vp, hz.mf, hz.got⟩
  refine ⟨rfl, rfl, ⟨z1, z2, z3⟩, fun j y f h => ?_, bl⟩
  obtain ⟨k1, k2, k3⟩ := lt.keep j h.1
  exact ⟨k1, k2.trans h.2.1, k3.trans h.2.2⟩

/-- One row: worth 0 at the earlier ledger gives worth 0 at the later one, at one mask row.
Conditional: lt; hr: the row's worth at every later ledger is one term of the mask row. -/
theorem rowWorth_on {F G : Fork} (lt : Fo.Later F G) {row : Aff} {r : TwV.SRow Fo.Pl GQ}
    (hr : Fo.RowIs Reading.gl F row r) (a a' : K9.Part) (haF : a.F = F) (haG : a'.F = G)
    (Dt Dt' : Bound GQ) (hm : Dt.mask = Dt'.mask)
    (v0 : row.value Reading.gl (worldOwn a [] Dt) = 0) :
    row.value Reading.gl (worldOwn a' [] Dt') = 0 := by
  rw [value_nil, haF, hr F (Fo.Later.refl _), hm] at v0
  rw [value_nil, haG, hr G lt]
  exact v0

/-- **The sentence rides forward**, to every state that `K5Keeps` ties to the state in front.
Conditional: K; e; hz, hrows: the lookup's promise in front; hS, hB: the reader's answer at the two
states; mS, mB: the stated function leaves the mask row there; h: the sentence in front. -/
theorem formsTQ_objects_on (Rd : Readers) (St : Stated) (own : List (ℕ × ℕ)) {s s' : S}
    (K : K5Keeps s s') {att : AttOwn} (e : s.here = .att att) (hz : Sized att.F)
    {g : Forest.Heard}
    (hrows : ∀ i, i < g.rows.size → ∃ r, Fo.RowIs Reading.gl att.F (g.rows.getD i {}) r)
    (hS : Rd.forms 1 "objects" s = some { forms := g.rows.toList, late := [] })
    (hB : Rd.forms 1 "objects" s' = some { forms := g.rows.toList, late := [] })
    (mS : ∀ Dt, (St.at1 s Dt).mask = Dt.mask) (mB : ∀ Dt, (St.at1 s' Dt).mask = Dt.mask)
    (rd : ℕ × ℕ → MsgQ) (h : formsTQ Rd St own 1 "objects" s rd) :
    formsTQ Rd St own 1 "objects" s' rd := by
  obtain ⟨_, b, att', f, e', _, _⟩ := id K
  obtain rfl : b = att := Here.att.inj (f.symm.trans e)
  obtain ⟨a0, R0, ha0, hR0, _, hf0⟩ := h
  obtain rfl : partAt s b b.F (K9.owedOf s) = a0 := Option.some.inj ((segAt_front e).symm.trans ha0)
  obtain rfl := Option.some.inj (hS.symm.trans hR0)
  obtain ⟨lt, _⟩ := keeps_ledgers K e e'
  have lt' : Fo.Later b.F att'.F := ⟨lt.next, lt.ns, lt.keep⟩
  have hmg : mergeOf s' = mergeOf s := by
    unfold mergeOf
    rw [e, e']
  have hp := part_behind K e e' (K9.owedOf s')
  refine ⟨_, _, segAt_front e', hB, rfl, fun f hf => ?_⟩
  rw [hp, hmg]
  refine ⟨affInT_up own _ _ (ledgerUp_keeps K e e' hz _ _) f (hf0 f hf).1, ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hf
  have hi' : i < g.rows.size := by simpa using hi
  have ef : g.rows.toList[i] = g.rows.getD i {} := by
    simp [Array.getD, hi']
  obtain ⟨r, hr⟩ := hrows i hi'
  rw [ef]
  refine rowWorth_on lt' hr (partAt s b b.F (K9.owedOf s)) (partAt s b att'.F (K9.owedOf s')) rfl
    rfl (St.at1 s (dataQ own (partAt s b b.F (K9.owedOf s)) rd))
    (St.at1 s' (dataQ own (partAt s b att'.F (K9.owedOf s')) rd))
    ((mS _).trans ((congrArg (·.mask)
      (dataQ_part own s b rd b.F att'.F (K9.owedOf s) (K9.owedOf s'))).trans (mB _).symm)) ?_
  rw [← ef]
  exact (hf0 _ hf).2

/-- The item's second run: where the reader answers with no form the sentence holds outright (the
library's `formsTQ_guests`), at the state behind. Conditional: e'; hG: the reader's answer. -/
theorem formsTQ_guests_on (Rd : Readers) (St : Stated) (own : List (ℕ × ℕ)) {s' : S}
    {att' : AttOwn} (e' : s'.here = .att att')
    (hG : Rd.forms 1 "guests" s' = some { forms := [], late := [] }) (rd : ℕ × ℕ → MsgQ) :
    formsTQ Rd St own 1 "guests" s' rd :=
  VerifiableInference.Desc.First.Att.P.formsTQ_guests Rd St own e' hG rd

end H2K5.Honest

#print axioms H2K5.Honest.keeps_att
#print axioms H2K5.Honest.part_behind
#print axioms H2K5.Honest.keeps_ledgers
#print axioms H2K5.Honest.ledgerUp_keeps
#print axioms H2K5.Honest.rowWorth_on
#print axioms H2K5.Honest.formsTQ_objects_on
#print axioms H2K5.Honest.formsTQ_guests_on
