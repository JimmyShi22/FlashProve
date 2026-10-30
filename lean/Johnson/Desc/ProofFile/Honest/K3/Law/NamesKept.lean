-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/NamesKept.lean: which arrays the claims of the lookup's four
runs name. A claim of these runs has no run of entries; the entries of its form are those of what
was heard (rows; the form in which the key side ends; the form that the leaves' sumcheck was given)
and of the calling kind's forms (the keys; the two readers), and no other. Theorems.

Terms. Honest/K3/GLOSSARY.md ("claim", "form", "heard structure", "run (of claims)", "seat"). In
this file: `RowsIn Q f` (OnBytes/Tie/Pv/Led/LedRowsOf.lean) says that all entries of the form f lie
in the predicate Q on (array, virtual row). "The claim cl names no entry and no run of the array t"
is written out each time: (∀ x ∈ cl.form.ents, x.tree ≠ t) ∧ ∀ u ∈ cl.runs, u.tree ≠ t.

What is shown.
  `rowsIn_of_bare`, `kept_rowsIn`: small facts: a form without an entry; the forms' arithmetic.
  `names_objects`, `names_guests`, `names_join`, `names_planes`: for every seat (at the first
    chain's state) and every predicate Q: where the named forms have all their entries in Q, so has
    each claim's form; and each claim's list of runs is empty. `names_guests` stands at no seat: it
    speaks of `guestsRun` at the empty list of guests, where there is no claim at all.
  `namesNot_of`: from these two to: the claim names no entry and no run of the array t.
  `namesNot_objects`: where the heard rows name no entry: at every array t.
  `namesNot_join`, `namesNot_planes`: at an array t that the caller's forms do not name.
  `measure_objectsCalls`, `measure_objectsDigits`, `measure_guests`: at the batching's own texts
    `K9.objectsCalls`, `K9.objectsDigits` and `guestsRun` at the empty list of guests: no claim
    names the array of the smallness test's digits (tl.ix.ZZ) or a matrix's array of symbols
    (tl.gtTree.getD mu 0, mu < tl.NM).
  `namesNot_joinCalls`, `namesNot_planesCalls`: at `K9.joinCalls keys` and
    `K9.planesCalls lm readers`.

Hypotheses that remain.
  `h`: the run returns. (In `rowsIn_of_bare`: the form has no entry. In `namesNot_of`, with `hr`:
    the claim's form has all its entries off the array t; its list of runs is empty.)
  `hA`: the seat reads and writes the state's own ledger (`AtS2`, Johnson/Top/H/Keep/RunsAtS.lean).
  Three hypotheses on the state s at which the run is called: what was heard at the seat has rows
    without an entry (`hb`); its cEnd has none (`hc`); its leaves.start has none (`hs`).
  The hypotheses on the caller's forms (`hK`; `hb` and `hp` at "planes"): these are for the calling
    kind's files to show.
  The runs are called at the link's batching. Each of the three hypotheses on the state is shown
  right behind the lookup's own acceptance: in the library's `decide_rowsBare`
  (Johnson/Top/H/Keep/RowsBare.lean), `rowsBare_reached` (Johnson/Desc/First/Look/K03RowsBare.lean:
  the 24 links in front of the head's), the field cEndEnts of `K3Left`
  (Johnson/Top/H/K3LeftStatement.lean) and `k3_calls_leavesBare`, which concludes `LeavesBare` (both
  Johnson/Desc/First/Look/K3LeftItem.lean); and in this folder's `hearV_ne`
  (Honest/K3/Parts/NoEntries.lean), `cEnd_below` (Honest/K3/Law/Thread/CEndBelow.lean) and
  `hearVia_leaves` (Honest/K3/Law/Thread/DigitsHeardLink.lean). That what was heard stays from there
  to the batching is not shown here; nor is anything at the digits of the head's link.

How the proof goes. The proofs call the library's `named_bind`, `joinRun_cut`, `planesRun_cut`
(Johnson/Top/H/K3RunsLaw.lean), `join_heard`, `planes_heard` (Johnson/Top/H/Keep/K3Inv.lean),
`planes_rowsIn` (Johnson/Top/H/Keep/PlanesRowsIn.lean), `joinForm_has`
(Johnson/Desc/Kinds/Law/KeysHave.lean), `guestsRun_nil` (Johnson/Top/H/Keep/RunsGuests.lean) and
`rowsIn_addMul` (LedRowsOf.lean).

Limits. Whether a run returns is not spoken of. "planes" does name an array: through the caller's
readers. Nothing is said on slots or on values. That the sub-protocols which are seated have no
guests is not shown here. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Top.H.Keep.PlanesRowsIn
import Johnson.Top.H.Keep.RunsGuests
import Johnson.Desc.Kinds.Law.KeysHave
import Johnson.Desc.First.Look.K03States
import Johnson.Desc.First.Batch.BlindPlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E zeroE)
open OnBytes.Model (Fork Aff)
open OnBytes.Road.Rows (RowsIn rowsIn_addMul)
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.K3 (Seat Readers planesRun joinRun seatCalls seatDigits)
open VerifiableInference.Desc.Kinds.Head.Law (Kept joinForm_has)
open VerifiableInference.OnPublicFiles (AtS2 objectsRun guestsRun guestsRun_nil named_bind join_heard
        joinRun_cut planes_heard planesRun_cut planes_rowsIn k03_atS2_calls k03_atS2_digits)

local notation "FS" => VerifiableInference.Desc.First.S

/-! ## 1 Small -/

/-- A form without an entry has all its entries in Q. -/
theorem rowsIn_of_bare {Q : Nat → Nat → Prop} {f : Aff} (h : f.ents = #[]) : RowsIn Q f :=
  fun y hy => by
    rw [h] at hy
    simp at hy

/-- "All entries in Q" is kept by the forms' arithmetic. -/
theorem kept_rowsIn (Q : Nat → Nat → Prop) : Kept (RowsIn Q) :=
  ⟨fun k ha hb => rowsIn_addMul k ha hb, fun _ he _ => rowsIn_of_bare he⟩

/-! ## 2 For every seat and every Q -/

section
variable (seat : Seat FS Claim) (hA : AtS2 seat) {Q : Nat → Nat → Prop}
include hA

/-- **"objects".** Conditional on the run's return and on the heard rows. -/
theorem names_objects (n : Nat) (s : FS) (cls : List Claim) (s' : FS)
    (h : objectsRun seat n s = .ok (cls, s'))
    (hb : ∀ g, seat.heard s = some g → ∀ f ∈ g.rows.toList, RowsIn Q f) :
    ∀ cl ∈ cls, RowsIn Q cl.form ∧ cl.runs = #[] := by
  unfold objectsRun at h
  rw [named_bind] at h
  obtain ⟨F, _, h⟩ := h
  rw [named_bind] at h
  obtain ⟨g, e2, h⟩ := h
  have ec : g.rows.toList.map seat.claim = cls := congrArg Prod.fst (Except.ok.inj h)
  intro cl hcl
  rw [← ec] at hcl
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hcl
  rw [hA.form, hA.runs]
  exact ⟨hb g e2 f hf, rfl⟩

/-- **"join".** Conditional on the run's return, on the form in which the key side ends, and on the
caller's keys. -/
theorem names_join (keys : FS → Option (Array Aff)) (n : Nat) (s : FS) (cls : List Claim)
    (s' : FS) (h : joinRun seat keys n s = .ok (cls, s'))
    (hc : ∀ g, seat.heard s = some g → RowsIn Q g.cEnd)
    (hK : ∀ KF, keys s = some KF → ∀ c, c < KF.size →
      RowsIn Q (KF.getD c (Aff.ofConst zeroE))) :
    ∀ cl ∈ cls, RowsIn Q cl.form ∧ cl.runs = #[] := by
  obtain ⟨F, g, e1, e2⟩ := join_heard seat keys h
  obtain ⟨KF, hKF, _, rfl, _⟩ := joinRun_cut seat keys e1 e2 h
  intro cl hcl
  rw [List.mem_singleton] at hcl
  subst hcl
  rw [hA.form, hA.runs]
  exact ⟨joinForm_has (kept_rowsIn Q) g KF (hK KF hKF) (hc g e2), rfl⟩

/-- **"planes".** Conditional on the run's return, on the form that the leaves' sumcheck was given,
and on the caller's two readers. -/
theorem names_planes (lm : Nat) (readers : Readers FS) (n : Nat) (s : FS) (cls : List Claim)
    (s' : FS) (h : planesRun seat lm readers n s = .ok (cls, s'))
    (hs : ∀ g, seat.heard s = some g → RowsIn Q g.leaves.start)
    (hb : ∀ r, readers s = some r → ∀ e col f, r.1 e col = some f → RowsIn Q f)
    (hp : ∀ r, readers s = some r → ∀ col f, r.2 col = some f → RowsIn Q f) :
    ∀ cl ∈ cls, RowsIn Q cl.form ∧ cl.runs = #[] := by
  obtain ⟨F, g, e1, e2⟩ := planes_heard seat lm readers h
  have h1 := planes_rowsIn (Q := Q) seat (fun c => c.form) hA.form lm readers e2 h (hs g e2) hb hp
  obtain ⟨_, rows, _, _, _, _, ec, _⟩ := planesRun_cut seat lm readers e1 e2 h
  intro cl hcl
  refine ⟨h1 cl hcl, ?_⟩
  rw [ec] at hcl
  obtain ⟨f, _, rfl⟩ := List.mem_map.1 hcl
  exact hA.runs f

end

/-- **"guests", at the empty list of guests: no claim.** Conditional on the run's return. -/
theorem names_guests (n : Nat) (s : FS) (cls : List Claim) (s' : FS)
    (h : guestsRun ([] : List (VerifiableInference.Desc.First.Look.Guest FS Claim)) n s =
      .ok (cls, s')) : cls = [] := by
  rw [guestsRun_nil] at h
  exact (congrArg Prod.fst (Except.ok.inj h)).symm

/-! ## 3 "Names no entry and no run of the array t" -/

/-- From the two conclusions above. -/
theorem namesNot_of {t : Nat} {cl : Claim} (h : RowsIn (fun a _ => a ≠ t) cl.form)
    (hr : cl.runs = #[]) : (∀ x ∈ cl.form.ents, x.tree ≠ t) ∧ ∀ u ∈ cl.runs, u.tree ≠ t :=
  ⟨fun x hx => h x (by simpa using hx), fun u hu => by
    rw [hr] at hu
    simp at hu⟩

section
variable (seat : Seat FS Claim) (hA : AtS2 seat)
include hA

/-- **"objects", at every array.** Conditional on the run's return and on: the heard rows name no
entry. -/
theorem namesNot_objects (n : Nat) (s : FS) (cls : List Claim) (s' : FS)
    (h : objectsRun seat n s = .ok (cls, s'))
    (hb : ∀ g, seat.heard s = some g → ∀ f ∈ g.rows.toList, f.ents = #[]) (t : Nat) :
    ∀ cl ∈ cls, (∀ x ∈ cl.form.ents, x.tree ≠ t) ∧ ∀ u ∈ cl.runs, u.tree ≠ t := by
  intro cl hcl
  obtain ⟨a, b⟩ := names_objects seat hA (Q := fun a _ => a ≠ t) n s cls s' h
    (fun g hg f hf => rowsIn_of_bare (hb g hg f hf)) cl hcl
  exact namesNot_of a b

/-- **"join", at an array that the caller's keys do not name.** -/
theorem namesNot_join (keys : FS → Option (Array Aff)) (n : Nat) (s : FS) (cls : List Claim)
    (s' : FS) (h : joinRun seat keys n s = .ok (cls, s'))
    (hc : ∀ g, seat.heard s = some g → g.cEnd.ents = #[]) (t : Nat)
    (hK : ∀ KF, keys s = some KF → ∀ c, c < KF.size →
      ∀ x ∈ (KF.getD c (Aff.ofConst zeroE)).ents, x.tree ≠ t) :
    ∀ cl ∈ cls, (∀ x ∈ cl.form.ents, x.tree ≠ t) ∧ ∀ u ∈ cl.runs, u.tree ≠ t := by
  intro cl hcl
  obtain ⟨a, b⟩ := names_join seat hA (Q := fun a _ => a ≠ t) keys n s cls s' h
    (fun g hg => rowsIn_of_bare (hc g hg))
    (fun KF hKF c hlt y hy => hK KF hKF c hlt y (by simpa using hy)) cl hcl
  exact namesNot_of a b

/-- **"planes", at an array that the caller's readers' forms do not name.** -/
theorem namesNot_planes (lm : Nat) (readers : Readers FS) (n : Nat) (s : FS) (cls : List Claim)
    (s' : FS) (h : planesRun seat lm readers n s = .ok (cls, s'))
    (hs : ∀ g, seat.heard s = some g → g.leaves.start.ents = #[]) (t : Nat)
    (hb : ∀ r, readers s = some r → ∀ e col f, r.1 e col = some f → ∀ x ∈ f.ents, x.tree ≠ t)
    (hp : ∀ r, readers s = some r → ∀ col f, r.2 col = some f → ∀ x ∈ f.ents, x.tree ≠ t) :
    ∀ cl ∈ cls, (∀ x ∈ cl.form.ents, x.tree ≠ t) ∧ ∀ u ∈ cl.runs, u.tree ≠ t := by
  intro cl hcl
  obtain ⟨a, b⟩ := names_planes seat hA (Q := fun a _ => a ≠ t) lm readers n s cls s' h
    (fun g hg => rowsIn_of_bare (hs g hg))
    (fun r hr e col f hf y hy => hb r hr e col f hf y (by simpa using hy))
    (fun r hr col f hf y hy => hp r hr col f hf y (by simpa using hy)) cl hcl
  exact namesNot_of a b

end

/-! ## 4 At the batching's own texts -/

/-- **`K9.objectsCalls`.** Conditional on the run's return and on: the rows heard at the calls name
no entry. -/
theorem measure_objectsCalls (m : Nat) (s : FS) (cls : List Claim) (s' : FS)
    (h : VerifiableInference.Desc.K9.objectsCalls m s = .ok (cls, s'))
    (hb : ∀ g, s.lookHeard? = some g → ∀ f ∈ g.rows.toList, f.ents = #[]) :
    ∀ tl, s.tl? = some tl → ∀ cl ∈ cls,
      ((∀ x ∈ cl.form.ents, x.tree ≠ tl.ix.ZZ) ∧ ∀ u ∈ cl.runs, u.tree ≠ tl.ix.ZZ) ∧
        ∀ mu < tl.NM, (∀ x ∈ cl.form.ents, x.tree ≠ tl.gtTree.getD mu 0) ∧
          ∀ u ∈ cl.runs, u.tree ≠ tl.gtTree.getD mu 0 :=
  fun _ _ cl hcl =>
    ⟨namesNot_objects (seatCalls K3Lot.ofForm) k03_atS2_calls m s cls s' h hb _ cl hcl,
      fun _ _ => namesNot_objects (seatCalls K3Lot.ofForm) k03_atS2_calls m s cls s' h hb _ cl hcl⟩

/-- **`K9.objectsDigits`.** Conditional on the run's return and on: the rows heard at the digits
name no entry. -/
theorem measure_objectsDigits (m : Nat) (s : FS) (cls : List Claim) (s' : FS)
    (h : VerifiableInference.Desc.K9.objectsDigits m s = .ok (cls, s'))
    (hb : ∀ g, s.tl?.bind (·.heard) = some g → ∀ f ∈ g.rows.toList, f.ents = #[]) :
    ∀ tl, s.tl? = some tl → ∀ cl ∈ cls,
      ((∀ x ∈ cl.form.ents, x.tree ≠ tl.ix.ZZ) ∧ ∀ u ∈ cl.runs, u.tree ≠ tl.ix.ZZ) ∧
        ∀ mu < tl.NM, (∀ x ∈ cl.form.ents, x.tree ≠ tl.gtTree.getD mu 0) ∧
          ∀ u ∈ cl.runs, u.tree ≠ tl.gtTree.getD mu 0 :=
  fun _ _ cl hcl =>
    ⟨namesNot_objects (seatDigits K3Lot.ofForm) k03_atS2_digits m s cls s' h hb _ cl hcl,
      fun _ _ =>
        namesNot_objects (seatDigits K3Lot.ofForm) k03_atS2_digits m s cls s' h hb _ cl hcl⟩

/-- **"guests", at the empty list of guests.** Conditional on the run's return alone: there is no
claim, so the sentence holds of no claim. -/
theorem measure_guests (m : Nat) (s : FS) (cls : List Claim) (s' : FS)
    (h : guestsRun ([] : List (VerifiableInference.Desc.First.Look.Guest FS Claim)) m s =
      .ok (cls, s')) :
    ∀ tl, s.tl? = some tl → ∀ cl ∈ cls,
      ((∀ x ∈ cl.form.ents, x.tree ≠ tl.ix.ZZ) ∧ ∀ u ∈ cl.runs, u.tree ≠ tl.ix.ZZ) ∧
        ∀ mu < tl.NM, (∀ x ∈ cl.form.ents, x.tree ≠ tl.gtTree.getD mu 0) ∧
          ∀ u ∈ cl.runs, u.tree ≠ tl.gtTree.getD mu 0 := by
  intro tl _ cl hcl
  rw [names_guests m s cls s' h] at hcl
  exact nomatch hcl

/-- **`K9.joinCalls keys`**, at an array that the keys do not name. -/
theorem namesNot_joinCalls (keys : FS → Option (Array Aff)) (m : Nat) (s : FS) (cls : List Claim)
    (s' : FS) (h : VerifiableInference.Desc.K9.joinCalls keys m s = .ok (cls, s'))
    (hc : ∀ g, s.lookHeard? = some g → g.cEnd.ents = #[]) (t : Nat)
    (hK : ∀ KF, keys s = some KF → ∀ c, c < KF.size →
      ∀ x ∈ (KF.getD c (Aff.ofConst zeroE)).ents, x.tree ≠ t) :
    ∀ cl ∈ cls, (∀ x ∈ cl.form.ents, x.tree ≠ t) ∧ ∀ u ∈ cl.runs, u.tree ≠ t :=
  namesNot_join (seatCalls K3Lot.ofForm) k03_atS2_calls keys m s cls s' h hc t hK

/-- **`K9.planesCalls lm readers`**, at an array that the readers' forms do not name. -/
theorem namesNot_planesCalls (lm : Nat) (readers : Readers FS) (m : Nat) (s : FS)
    (cls : List Claim) (s' : FS)
    (h : VerifiableInference.Desc.K9.planesCalls lm readers m s = .ok (cls, s'))
    (hs : ∀ g, s.lookHeard? = some g → g.leaves.start.ents = #[]) (t : Nat)
    (hb : ∀ r, readers s = some r → ∀ e col f, r.1 e col = some f → ∀ x ∈ f.ents, x.tree ≠ t)
    (hp : ∀ r, readers s = some r → ∀ col f, r.2 col = some f → ∀ x ∈ f.ents, x.tree ≠ t) :
    ∀ cl ∈ cls, (∀ x ∈ cl.form.ents, x.tree ≠ t) ∧ ∀ u ∈ cl.runs, u.tree ≠ t :=
  namesNot_planes (seatCalls K3Lot.ofForm) k03_atS2_calls lm readers m s cls s' h hs t hb hp

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.rowsIn_of_bare
#print axioms ProofFile.Honest.K3.Law.kept_rowsIn
#print axioms ProofFile.Honest.K3.Law.names_objects
#print axioms ProofFile.Honest.K3.Law.names_join
#print axioms ProofFile.Honest.K3.Law.names_planes
#print axioms ProofFile.Honest.K3.Law.names_guests
#print axioms ProofFile.Honest.K3.Law.namesNot_of
#print axioms ProofFile.Honest.K3.Law.namesNot_objects
#print axioms ProofFile.Honest.K3.Law.namesNot_join
#print axioms ProofFile.Honest.K3.Law.namesNot_planes
#print axioms ProofFile.Honest.K3.Law.measure_objectsCalls
#print axioms ProofFile.Honest.K3.Law.measure_objectsDigits
#print axioms ProofFile.Honest.K3.Law.measure_guests
#print axioms ProofFile.Honest.K3.Law.namesNot_joinCalls
#print axioms ProofFile.Honest.K3.Law.namesNot_planesCalls
