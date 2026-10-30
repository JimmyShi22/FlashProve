-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/PlanesG.lean: the three claims on the planes in the flat text
`planesG` (Johnson/Desc/First/Look/K3LookupGeneral.lean), against the text `planesV`
(Johnson/Desc/First/Look/Via/Rounds.lean). For every face: any number of parts, with or without a
shift. Theorems, with one definition.

Terms. Honest/K3/GLOSSARY.md ("claim", "count, bits, planes", "ledger", "world, worth").

What is shown.
  `SamePlane`: two claims on the planes have one scalar and one list of pairs, to the letter, and
    leads that are worth the same in every reading and world.
  `toPsc_ready`: the program's structure of a sumcheck that was heard without ends passes the four
    tests of the flat text of the late claim.
  `pscRow_of_row`, `row_of_pscRow`: the flat text of the late claim returns just where the part's
    own `row` returns, with the same ledger behind and the tape untouched.
  `planesG_of_planesV`, `planesV_of_planesG`: so the one text makes its three claims just where the
    other does; ledger and tape as said; the claims are the same, one by one.
  `planesG_returns`, `planesG_behind`: `planesG` returns, with three claims, where `hearV` has
    returned and the leaves' own slots are still owed; and at the hearing's own ledger.

Hypotheses that remain.
  In `planesG_returns`: `hh`: `hearV` returns; `hS`, `hroom`: the first ledger's arrays have their
    size, and it has room for the lookup's slots; `hS'`, `hL`, `ho`: the later ledger's arrays have
    their size; it is `Later` than the hearing's; the leaves' own slots are owed at it.
  In `planesG_behind`: `hh`, `hS`, `hroom`, and `hfree`: the first ledger is free from its count of
    slots on as far as the lookup reaches.
  In the others: `h0`: the sumcheck was heard without ends; `hr`, `h`, `hv`: the text in question
    returns.

How the proof goes. Why the leads are compared as worth: the first claim's lead is made by two
texts: the part's own makes the hiding polynomial's linear form by `hidingAt`, the program's by its
walk; the library shows them equal as read (Johnson/Desc/Part/MaskedSumTie.lean), not element by
element.

Users. This file is imported by Honest/K3/Law/PlanesGGuards.lean [not in this library],
Honest/K3/Law/PlanesGLetter.lean, Honest/K3/Law/Thread/Group11.lean [not in this library] and
Honest/K3/Law/Thread/LeavesOpen.lean [not in this library].

Limits. It speaks of `planesG` at the structure `toHeardG g` of what `hearV` heard. A sub-protocol
that hears by the flat text of K3LookupGeneral.lean makes a structure of its own: that this structure is
`toHeardG` of that of `hearV`, where `hearV` returns, is the library's `hearV_flRun`
(Johnson/Top/H/K3Via/Bridge.lean), called in Honest/K3/Law/PlanesGLetter.lean, which also has the
way from `planesV` to `planesG` to the letter. What this file has beyond that one: the way back, and
no hypothesis on the variables. Nothing is said on what the claims are worth.
Instances: Honest/K3/Law/PlanesGGuards.lean [not in this library] (by evaluation).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.SeatedPlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E zeroE oneE subE)
open OnBytes.Model (Fork Aff Reading World)
open OnBytes.K.Kc (Fl Tape)
open OnBytes.PscRun (Sized Filled Later)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Call ownSlots hidingAt)
open VerifiableInference.Desc.K3 (HeardV PlaneClaim hearV planesV planesG toHeardG toPsc leafVars)

/-- **Two claims on the planes are the same**: scalar and pairs to the letter; the
leads as worth. -/
def SamePlane (x y : PlaneClaim) : Prop :=
  x.scalar = y.scalar ∧ x.pairs = y.pairs ∧
    ∀ (K : Type) [CommRing K] (ρ : Reading K) (W : World K), x.lead.value ρ W = y.lead.value ρ W

/-- A claim is the same as itself. -/
theorem SamePlane.refl (x : PlaneClaim) : SamePlane x x := ⟨rfl, rfl, fun _ _ _ _ => rfl⟩

/-! ## The late claim -/

/-- The program's structure of a sumcheck that was heard without ends passes the flat text's four
tests. Conditional on the return of the part's hearing. -/
theorem toPsc_ready {C : Aff} {vs : List Var} {F₀ G₀ : Fork} {rs₀ : List Fmt.RoundView}
    {hd : MaskedSum.Heard}
    (h0 : MaskedSum.hear C { lead := 0, vs := vs, ends := none } F₀ rs₀ = some (hd, G₀)) :
    (!(toPsc hd).rowMade && (toPsc hd).started && !(toPsc hd).vars.isEmpty &&
      (toPsc hd).r.size == (toPsc hd).vars.size) = true := by
  obtain ⟨hs, T, R, _, hR, he, _⟩ := MaskedSum.hear_spec h0
  have hlen : R.rounds.length = vs.length := MaskedSum.readAll_none_len hR
  have hne : vs.isEmpty = false := by
    simp only [MaskedSum.shapeOk, Bool.and_eq_true, Bool.not_eq_true'] at hs
    exact hs.2
  have hv : hd.vars = vs := by rw [he]; rfl
  have hrl : hd.r.length = vs.length := by rw [he]; simp [hlen]
  cases vs with
  | nil => simp at hne
  | cons v vs' => simp [toPsc, hv, hrl]

/-- **Where the part's own row returns, the flat text of the late claim returns**, with the same
ledger behind and the tape untouched. Conditional on the return of the part's `hear` and `row`. -/
theorem pscRow_of_row {C : Aff} {vs : List Var} {F₀ G₀ F' G' : Fork} {rs₀ : List Fmt.RoundView}
    {hd : MaskedSum.Heard} {S0 S1 : E} {kept kept1 y : Aff} (t : Tape)
    (h0 : MaskedSum.hear C { lead := 0, vs := vs, ends := none } F₀ rs₀ = some (hd, G₀))
    (hr : MaskedSum.row hd S0 kept F' = some (y, G')) :
    Fl.pscRow (toPsc hd) S1 kept1 F' t =
      some (((toPsc hd).rowForm S1 kept1, { toPsc hd with rowMade := true }), G', t) := by
  have hcond := toPsc_ready h0
  have hw := MaskedSum.row_write hr
  rw [← walk_length] at hw
  have hw' : F'.hideRun (toPsc hd).first (Array.replicate (toPsc hd).walk.1.length zeroE)
      (subE zeroE oneE) = some G' := hw
  simp only [Fl.pscRow, bind, Fl.andThen, Fl.must, Fl.change, pure, Fl.ret, hcond, if_true, hw',
    Option.map_some]

/-- **The way back**: where the flat text of the late claim returns, so does the part's own row,
with the same ledger behind; and the tape is untouched. Conditional on that return. -/
theorem row_of_pscRow {hd : MaskedSum.Heard} {S0 S1 : E} {kept kept1 : Aff} {F' G' : Fork}
    {t u : Tape}
    {x : Aff × OnBytes.Model.Psc} (h : Fl.pscRow (toPsc hd) S1 kept1 F' t = some (x, G', u)) :
    MaskedSum.row hd S0 kept F' = some (MaskedSum.rowAff hd S0 kept, G') ∧ u = t ∧
      x.1 = (toPsc hd).rowForm S1 kept1 := by
  simp only [Fl.pscRow, bind, Fl.andThen, Fl.must, Fl.change, pure, Fl.ret] at h
  split at h
  · rename_i a G1 u1 hm
    split at hm
    · simp only [Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨_, rfl, rfl⟩ := hm
      split at h
      · rename_i a2 G2 u2 hc
        obtain ⟨G3, hG3, e⟩ := Option.map_eq_some_iff.1 hc
        simp only [Prod.mk.injEq] at e
        obtain ⟨_, rfl, rfl⟩ := e
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have hw : F'.hideRun hd.first
            (Array.replicate (hidingAt (hd.vars.zip hd.r)).1.length zeroE) (subE zeroE oneE) =
              some G3 := by
          rw [← walk_length]
          exact hG3
        refine ⟨?_, rfl, rfl⟩
        unfold MaskedSum.row
        simp only [hw, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        rfl
      · exact nomatch h
    · exact nomatch hm
  · exact nomatch h

/-! ## The three claims -/

/-- **Where `planesV` makes its three claims, `planesG` makes the same**, with the same ledger
behind and the tape untouched. Conditional on the leaves' structure being one that the part's
hearing made at a call without ends, and on the return of `planesV`. Instances:
Honest/K3/Law/PlanesGGuards.lean [not in this library] (by evaluation). -/
theorem planesG_of_planesV (f : LFace) (g : HeardV) {C : Aff} {vs : List Var} {F₀ G₀ F' G' : Fork}
    {rs₀ : List Fmt.RoundView} {cl : List PlaneClaim} (t : Tape)
    (h0 : MaskedSum.hear C { lead := 0, vs := vs, ends := none } F₀ rs₀ = some (g.leaves, G₀))
    (hv : planesV f g F' = some (cl, G')) :
    ∃ cl', planesG f (toHeardG g) F' t = some (cl', G', t) ∧ List.Forall₂ SamePlane cl cl' := by
  unfold planesV at hv
  obtain ⟨x, hx, e⟩ := Option.map_eq_some_iff.1 hv
  obtain ⟨y, G1⟩ := x
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have hp := pscRow_of_row (S1 := oneE) (kept1 := {}) t h0 hx
  refine ⟨_, by
    unfold planesG
    dsimp only
    rw [fl_bind_some (show Fl.pscRow (toHeardG g).leaves oneE {} F' t = _ from hp)]
    rfl, ?_⟩
  refine .cons ⟨rfl, rfl, fun K _ ρ W => ?_⟩ (.cons (SamePlane.refl _)
    (.cons (SamePlane.refl _) .nil))
  show y.value ρ W = ((toPsc g.leaves).rowForm oneE {}).value ρ W
  rw [MaskedSum.row_spec hx, rowForm_value]

/-- **The way back.** Conditional on the return of `planesG` at the structure `toHeardG g`. -/
theorem planesV_of_planesG (f : LFace) (g : HeardV) {F' G' : Fork} {t u : Tape}
    {cl' : List PlaneClaim} (h : planesG f (toHeardG g) F' t = some (cl', G', u)) :
    ∃ cl, planesV f g F' = some (cl, G') ∧ u = t ∧ List.Forall₂ SamePlane cl cl' := by
  unfold planesG at h
  dsimp only at h
  have h' : Fl.andThen (Fl.pscRow (toHeardG g).leaves oneE {}) _ F' t = some (cl', G', u) := h
  unfold Fl.andThen at h'
  split at h'
  · rename_i x G1 u1 hx
    obtain ⟨hr, rfl, hx1⟩ := row_of_pscRow (S0 := oneE) (kept := {})
      (show Fl.pscRow (toPsc g.leaves) oneE {} F' t = some (x, G1, u1) from hx)
    obtain ⟨x1, x2⟩ := x
    have e : some (_, G1, u1) = some (cl', G', u) := h'
    simp only [Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    refine ⟨_, by unfold planesV; rw [hr]; rfl, rfl, ?_⟩
    refine .cons ⟨rfl, rfl, fun K _ ρ W => ?_⟩
      (.cons (SamePlane.refl _) (.cons (SamePlane.refl _) .nil))
    show (MaskedSum.rowAff g.leaves oneE {}).value ρ W = x1.value ρ W
    have hx1' : x1 = (toPsc g.leaves).rowForm oneE {} := hx1
    rw [hx1', rowForm_value]
  · exact nomatch h'

/-- **`planesG` returns, with three claims.** Conditional on the return of `hearV`, on `Sized` and
room in front, on `Sized` at F', on F' being `Later` than the hearing's own ledger, and on the
leaves' own slots being owed at F'. Instances: Honest/K3/Law/PlanesGGuards.lean
[not in this library] (by evaluation). -/
theorem planesG_returns (f : LFace) {F G F' : Fork} {x : List Fmt.RoundView} {g : HeardV} (hS : Sized F)
    (hroom : F.next + f.slots ≤ F.ns) (hh : hearV f F x = some (g, G)) (hS' : Sized F')
    (hL : Later G F')
    (ho : OnBytes.PscRun.SlotsOwed F' (F.next + firstSlot f .leaves) (Stage.own f .leaves))
    (t : Tape) :
    ∃ cl' G', planesG f (toHeardG g) F' t = some (cl', G', t) ∧ cl'.length = 3 := by
  obtain ⟨cl, G', hv, h3⟩ := planesV_of_owed f hS hroom hh hS' hL ho
  obtain ⟨C, z, F₀, G₀, rs₀, h0, _, _⟩ := leaves_heard f hS (hearV_messages hh).2
  obtain ⟨cl', hg, hf⟩ := planesG_of_planesV f g t h0 hv
  exact ⟨cl', G', hg, by rw [← hf.length_eq]; exact h3⟩

/-- **At the hearing's own ledger.** Conditional on the return of `hearV`, on `Sized` and room in
front, and on the first ledger being free from its count of slots on as far as the lookup reaches.
Instances: Honest/K3/Law/PlanesGGuards.lean [not in this library] (by evaluation). -/
theorem planesG_behind (f : LFace) {F G : Fork} {x : List Fmt.RoundView} {g : HeardV} (hS : Sized F)
    (hroom : F.next + f.slots ≤ F.ns)
    (hfree : ∀ j, F.next ≤ j → j < F.next + f.slots → ¬ Filled F j)
    (hh : hearV f F x = some (g, G)) (t : Tape) :
    ∃ cl' G', planesG f (toHeardG g) G t = some (cl', G', t) ∧ cl'.length = 3 :=
  planesG_returns f hS hroom hh ((hearV_later hh).sized hS) (Later.refl G)
    (leaves_owed f hS hfree hh) t

#print axioms ProofFile.Honest.K3.Law.SamePlane.refl
#print axioms ProofFile.Honest.K3.Law.toPsc_ready
#print axioms ProofFile.Honest.K3.Law.pscRow_of_row
#print axioms ProofFile.Honest.K3.Law.row_of_pscRow
#print axioms ProofFile.Honest.K3.Law.planesG_of_planesV
#print axioms ProofFile.Honest.K3.Law.planesV_of_planesG
#print axioms ProofFile.Honest.K3.Law.planesG_returns
#print axioms ProofFile.Honest.K3.Law.planesG_behind

end ProofFile.Honest.K3.Law
