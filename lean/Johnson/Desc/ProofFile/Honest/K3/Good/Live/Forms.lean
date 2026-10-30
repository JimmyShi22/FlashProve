-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/Live/Forms.lean: the kind "lookup" (K3): for a calling kind
that lays the lookup's own forms into claims of its own: at what a lookup heard, under the condition
of Honest/K3/Good/Live/Clause.lean: with which coefficients the key side's last form, the row form
of the leaves' sumcheck (with any form kept) and the form on the bits' end slot name the slots of
the windows of "join" and "planes"; and where the leaves' own slots end. Theorems.

Terms. Honest/K3/GLOSSARY.md ("form", "slot", "window", "run (of claims): objects, guests, planes,
join", "caller"). In this file: `sc a j` is the coefficient with which the form a names slot j: the
sum over all its pairs on j, read in the library's field (Honest/K3/Good/Coef.lean). g is what the
lookup heard (`Forest.Heard`), p the place's public parameters, h its shape; a window counts from
p.first.

What is shown.
  `worth_kept`, `sc_rowForm`: the verifier program's row form of a heard sumcheck with the form
    `kept` kept is worth, and has the coefficients of, the row with nothing kept plus eps times
    `kept`. At any `kept` (`sc_leaves`, Honest/K3/Good/Live/Pure.lean, has it at a scaled one).
  `cEnd_sc`: on each slot of the window of "join" the coefficient of g.cEnd is not 0.
  `planes_sc`: on each slot of the window of "planes": either the coefficient of g.leaves.rowForm
    oneE kept is not 0, for every kept whose own coefficient there is 0; or the slot is g.sBit.
  `sBit_sc`: a form `Aff.slot s - a1` has the coefficient 1 on s, if a1 has the coefficient 0 there.
  `live_of_form`: a list with a claim that takes its own number and whose form has a coefficient
    other than 0 on slot j is live there (`liveAt`, Johnson/Desc/K9/Honest/SlotsLive.lean).
  `leaves_below`: the own slots of the leaves' sumcheck end at or below p.first + `Forest.elems h`.
  `unnamed_of_forms`: a list none of whose claims' forms names slot j does not name it
    (`unnamedAt`).
  `outside_clear`: outside the lookup's own stretch of slots (`Outside`,
    Honest/K3/Good/Live/Unnamed.lean): no heard row names the slot; g.cEnd does not; the row form of
    the leaves' sumcheck does not, whatever is kept that does not; and it is not g.sBit.

Hypotheses that remain. `hp`: the place's parameters make the shape h. `J`: g meets the condition
(in `leaves_below` and `outside_clear` at any test T: the samples' values are not used). `hj`: j is
in the window; in `outside_clear`: `Outside p h j`. In `planes_sc` and `sBit_sc`: the kept form, or
a1, has the coefficient 0 on the slot: `sc_clear` (Pure.lean) gives that of a form that does not
name it. In `live_of_form`: `hm`, `he`, `h`: the claim is in the list; it takes its own number; its
form's coefficient on j is not 0. In `unnamed_of_forms`: `h`: no claim's form names j. `worth_kept`
and `sc_rowForm` have no hypothesis.

Related. The library's `slotCo` (Johnson/Desc/K5/Honest/Law/Live.lean) is the like of `sc`, at every
reading, with its own lemmas on sums, differences and the description's row with nothing kept
(`slotCo_formOf`, `row_own_live`, in the same file). A second like of `sc` in the library:
`OnBytes.Road.K4.slotCo` (Johnson/Road/K4/LookLeft.lean), at every reading too. Its `slot_sub_live`
(Johnson/Desc/K5/Honest/Law/LiveForms.lean) is the like of `sBit_sc`: it assumes that the form taken
off has the coefficient 0 on every slot, and concludes that the coefficient on s is not 0. Neither
file stands among this file's import lines. The library's `rowForm_split`
(OnBytes/Desc/First/P1/PscSoundK.lean) splits S0 and the kept form off the verifier program's row
form, at every reading and every world; `worth_kept` says the like of the kept form alone, against
the description's own row (`rowAff`). `live_of_form` is one direction of the library's `liveAt_iff`
(SlotsLive.lean), with `sc` for `slotCoef`; its `unnamed_of_bool` (the same file) reads `unnamedAt`
as the premise `unnamed` has it, where `unnamed_of_forms` here concludes `unnamedAt`; the like for
other lists of claims: `liveAt_forms` (Johnson/Desc/K5/Honest/Law/LiveClaims.lean) and
`live_of_delta` (Johnson/Desc/ProofFile/Honest/K6/GoodLaw/Coef.lean). The sentence of `leaves_below`
the library has under `K3Left`, with the next slot of the ledger in front for p.first: `left_within`
with `left_len` (Johnson/Top/H/Keep/K3LeftWindow.lean).

Limits. Forms alone. That a calling kind's list of claims holds one of these forms, scaled or not,
and that what that kind holds as heard by the lookup is g, is not said here. No ledger is read. No
instance of the hypotheses together is exhibited in this file; Honest/K3/Good/Live/LiveGuards.lean
[not in this library] evaluates the condition to true at one synthetic place.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.Unnamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good.Live
open OnBytes (E zeroE oneE)
open OnBytes.Model (Fork Aff Reading World)
open OnBytes.Model.Forest (Shape Heard)
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (rowAff)
open VerifiableInference.Desc.First.Look (P)
open VerifiableInference.Desc.K3 (faceOf toPsc)
open VerifiableInference.Desc.K9H (slotCoef liveAt liveAt_iff unnamedAt unnamedIn)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Law.Exchange (toHeard_parts)
open ProofFile.Honest.K3.Parts (heard_names)

/-! ## The row form, with any form kept -/

/-- The verifier program's row form of a heard sumcheck with the form kept kept is worth the row
with nothing kept plus eps times kept. No hypothesis. -/
theorem worth_kept (hd : MaskedSum.Heard) (S0 : E) (kept : Aff) (Wd : World GE) :
    ((toPsc hd).rowForm S0 kept).value Reading.gl Wd =
      (rowAff hd S0 {}).value Reading.gl Wd + vl hd.eps * kept.value Reading.gl Wd := by
  rw [rowForm_value, MaskedSum.rowAff_value, MaskedSum.rowAff_value, Aff.value_empty]
  unfold vl
  ring

/-- The same of the coefficients, slot by slot. No hypothesis. -/
theorem sc_rowForm (hd : MaskedSum.Heard) (S0 : E) (kept : Aff) (j : Nat) :
    sc ((toPsc hd).rowForm S0 kept) j = sc (rowAff hd S0 {}) j + vl hd.eps * sc kept j := by
  rw [sc_eq, sc_eq, sc_eq, worth_kept, worth_kept]
  ring

/-! ## The three forms -/

/-- **On each slot of the window of "join" the coefficient of the key side's last form is not 0.**
Conditional on the hypotheses that the head of this file lists. -/
theorem cEnd_sc {p : P} {h : Shape} (hp : p.shape = some h) {g : Heard} (J : Clause p (some g))
    {j : ℕ} (hj : j ∈ windowOf (faceOf h) .join) : sc g.cEnd (p.first + j) ≠ 0 := by
  obtain ⟨H, F, G, rs, gv, eH, hd, hn, hh, hto, hcd, hgd⟩ := clause_open hp J
  obtain rfl : g = H := Option.some.inj eH
  obtain ⟨point, form, hkeys, _, _, _, _, hce, _⟩ := toHeard_parts hto
  obtain ⟨a, ha, hne⟩ := gives_pure hd hcd hh .join (goodRun_of _ _ hgd .join) hj
  have ha' : a ∈ gv.keys.map (·.2) := ha
  rw [hkeys] at ha'
  obtain rfl : a = form := List.mem_singleton.1 ha'
  rw [hce, ← hn]
  exact hne

/-- **On each slot of the window of "planes"**: the row form of the leaves' sumcheck has a
coefficient other than 0, whatever is kept that has none there; or the slot is the bits' end slot.
Conditional on the hypotheses that the head of this file lists. -/
theorem planes_sc {p : P} {h : Shape} (hp : p.shape = some h) {g : Heard} (J : Clause p (some g))
    {j : ℕ} (hj : j ∈ windowOf (faceOf h) .planes) :
    (∀ kept, sc kept (p.first + j) = 0 → sc (g.leaves.rowForm oneE kept) (p.first + j) ≠ 0) ∨
      p.first + j = g.sBit := by
  obtain ⟨H, F, G, rs, gv, eH, hd, hn, hh, hto, hcd, hgd⟩ := clause_open hp J
  obtain rfl : g = H := Option.some.inj eH
  obtain ⟨_, eL, eB, _⟩ := toHeard_fields hto
  obtain ⟨a, ha, hne⟩ := gives_pure hd hcd hh .planes (goodRun_of _ _ hgd .planes) hj
  rw [hn] at hne
  have ha' : a ∈ [rowAff gv.leaves oneE {}, Aff.slot gv.sBit] := ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
  rcases ha' with rfl | rfl
  · refine .inl fun kept hk => ?_
    rw [eL, sc_rowForm, hk, mul_zero, add_zero]
    exact hne
  · refine .inr ?_
    rw [sc_slot] at hne
    by_cases e : gv.sBit = p.first + j
    · rw [eB, e]
    · rw [if_neg e] at hne
      exact absurd rfl hne

/-- A form on one slot, less a form that has no coefficient there, has the coefficient 1 there. h:
a1 has the coefficient 0 on s. -/
theorem sBit_sc (s : Nat) {a1 : Aff} (h : sc a1 s = 0) : sc (Aff.slot s - a1) s = 1 := by
  rw [sc_sub, sc_slot, if_pos rfl, h, sub_zero]

/-- From a form's coefficient to the test on a list of claims. -/
theorem live_of_form {l : List Claim} {cl : Claim} (hm : cl ∈ l) (he : cl.eqFirst = none) {j : Nat}
    (h : sc cl.form j ≠ 0) : liveAt l j = true := by
  refine (liveAt_iff _ _).2 ⟨cl, hm, he, ?_⟩
  have e : slotCoef Reading.gl cl j = sc cl.form j := by
    unfold sc slotCoef
    rfl
  rw [e]
  exact h

/-! ## Where the leaves' own slots end -/

/-- **The own slots of the leaves' sumcheck end at or below the end of the lookup's stretch.**
Conditional on the hypotheses that the head of this file lists. -/
theorem leaves_below {T : LFace → List Fmt.Drawn → Bool} {p : P} {h : Shape}
    (hp : p.shape = some h) {g : Heard} (J : ClauseBy T p (some g)) :
    g.leaves.first + g.leaves.walk.1.length ≤ p.first + OnBytes.Model.Forest.elems h := by
  obtain ⟨H, F, G, rs, gv, eH, _, hn, hh, hto, _, _⟩ := clause_open hp J
  obtain rfl : g = H := Option.some.inj eH
  obtain ⟨_, eL, _, _⟩ := toHeard_fields hto
  obtain ⟨hokf, hm⟩ := hearV_messages hh
  obtain ⟨_, _, _, _, n5, _, _⟩ := heard_names (two_le_planes_of_ok _ hokf) hm
  rw [eL, walk_length, ← Spec.slots_elems, ← hn]
  exact n5

/-! ## Outside the lookup's own stretch -/

/-- From forms to the test on a list of claims. -/
theorem unnamed_of_forms {l : List Claim} {j : Nat} (h : ∀ cl ∈ l, Clear cl.form j) :
    unnamedAt l j = true := by
  unfold unnamedAt
  rw [List.all_eq_true]
  intro cl hcl
  unfold unnamedIn
  rw [List.all_eq_true]
  intro x hx
  simpa using h cl hcl x hx

/-- **Outside the lookup's own stretch none of its forms names the slot.** Conditional on the
hypotheses that the head of this file lists. -/
theorem outside_clear {T : LFace → List Fmt.Drawn → Bool} {p : P} {h : Shape}
    (hp : p.shape = some h) {g : Heard} (J : ClauseBy T p (some g)) {j : ℕ}
    (hj : Outside p h j) :
    (∀ a ∈ g.rows.toList, Clear a j) ∧ Clear g.cEnd j ∧
      (∀ S0 kept, Clear kept j → Clear (g.leaves.rowForm S0 kept) j) ∧ g.sBit ≠ j := by
  obtain ⟨H, F, G, rs, gv, eH, _, hn, hh, hto, _, _⟩ := clause_open hp J
  obtain rfl : g = H := Option.some.inj eH
  obtain ⟨_, eL, eB, _⟩ := toHeard_fields hto
  obtain ⟨point, form, hkeys, _, hrows, _, _, hce, _⟩ := toHeard_parts hto
  obtain ⟨hokf, hm⟩ := hearV_messages hh
  obtain ⟨n1, n2, n3, n4, n5, n6, n7⟩ := heard_names (two_le_planes_of_ok _ hokf) hm
  unfold Outside at hj
  rw [← Spec.slots_elems, ← hn] at hj
  refine ⟨fun a ha => ?_, ?_, fun S0 kept hk => ?_, ?_⟩
  · rw [hrows] at ha
    exact clear_of_in (n1 a ha) hj
  · rw [hce]
    exact clear_of_in (n2 (point, form) (by rw [hkeys]; exact List.mem_singleton.2 rfl)) hj
  · rw [eL]
    refine clear_rowForm _ _ (clear_of_in n3 hj) hk ?_
    rw [walk_length]
    show j < gv.leaves.first ∨ gv.leaves.first + _ ≤ j
    omega
  · rw [eB]
    omega

end ProofFile.Honest.K3.Good.Live

#print axioms ProofFile.Honest.K3.Good.Live.worth_kept
#print axioms ProofFile.Honest.K3.Good.Live.sc_rowForm
#print axioms ProofFile.Honest.K3.Good.Live.cEnd_sc
#print axioms ProofFile.Honest.K3.Good.Live.planes_sc
#print axioms ProofFile.Honest.K3.Good.Live.sBit_sc
#print axioms ProofFile.Honest.K3.Good.Live.live_of_form
#print axioms ProofFile.Honest.K3.Good.Live.leaves_below
#print axioms ProofFile.Honest.K3.Good.Live.unnamed_of_forms
#print axioms ProofFile.Honest.K3.Good.Live.outside_clear
