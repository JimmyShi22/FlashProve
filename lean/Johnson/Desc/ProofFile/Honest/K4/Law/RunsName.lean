-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/RunsName.lean: CONDITIONAL.

What is here. The sub-protocol of the feed-forward layers' own rounds (kind K4) states two runs of
claims, "front" and "back", which a segment's batching runs. Here, UNDER `RunsPre`: wherever such a
run returns, EACH OF ITS CLAIMS BEARS NO RUN OF ENTRIES, AND EVERY SINGLE ENTRY THAT ITS FORM NAMES
LIES IN ONE ARRAY: the third array of reads of the smallness test's record,
`(tl.ix.U.getD 2 none).getD 0` (0 where the record names none). First at the runs of the kind's own
sub-protocol (`blockAtC p`, Johnson/Desc/First/K4/AtC.lean); then at the runs that are looked up in
that sub-protocol as the description's maker seats it (`IM.LaidAlone`, Johnson/IMR/SeatForm.lean, at
K4's lot's `ProofFile.k4Block x`). Statements and proofs: calls of the library's `front_row0_named`,
`back_row0_named` (Johnson/Road/K4/Reads/RowZeroNamed.lean: every entry of a form of either listing
is (o.v.iU3, 0, i)), `frontAtC`, `backAtC` (Johnson/Desc/First/K4/RunsAtC.lean: from the run to the
listing), `frontOf_eq` (Johnson/Road/K4/Total/AtKept.lean) and `run_pub`
(Johnson/Road/K4/Total/PubOnly.lean): the listing in front, at the public record with other tokens
laid in; and `IM.claim_yes` (from the seated run to the kind's).

Not shown here. `RunsPre p s`, THE HYPOTHESIS ON THE STATE IN FRONT OF THE RUN, IS PAID NOWHERE
HERE. Of the smallness test's record tl and K4's return o that the state shows, it asks four things:
(heard) o is what K4's hearing returned at the plan, at some tokens, lookup's return, ledger and
tape; (cols) the plan's third number of reads is at most o.v.K3; (pad) the lookup's record on the
names of its pad at o.H.fo, at some ledger; (array) o.v.iU3 is that array's number. That this array
is another than the smallness test's digits' array or a matrix's array of symbols is not said here.
That a description's member is so seated is a hypothesis (hb). Nothing on what a form is worth. No
example of the hypotheses together has been through Lean.
No property is claimed.
The honest prover is not in this file: it is a law on what the verifier's runs return.
Imports. Followed to the end, this file's imports reach no module under Johnson/Goal/, Johnson/D/ or
ThirdParty/ and none of Johnson/RecCompile/Honest…, Both… or PassH…; through
Johnson/IMR/SeatForm.lean they reach seven other modules of Johnson/RecCompile/.
By a program's count.

  `RunAsks`, `RunsPre`   the hypothesis, at what was heard; at a state.
  `forms_name`          forms as claims: no run of entries; the forms' own entries.
  `own_of_lay`          the state's reader of K4's return, inside a layers' segment.
  `front_names`, `back_names`   at one return of a run of the kind's own sub-protocol.
  `front_names_tl`, `back_names_tl`   **the same, with the array's number read off the state's
      record tl.**
  `front_names_laid`, `back_names_laid`   **at the seated sub-protocol's runs.**
-/
import Johnson.Road.K4.Reads.RowZeroNamed
import Johnson.Road.K4.Total.AtKept
import Johnson.Desc.First.K4.RunsAtC
import Johnson.Desc.ProofFile.Lot.K4
import Johnson.IMR.SeatForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par blockAtC claimOf hearFl formsFrontWith frontAtC backAtC)
open OnBytes.Desc.First.K4.Reads (front_row0_named back_row0_named)
open OnBytes.Desc.First.K4.Total (frontOf_eq run_pub)
open VerifiableInference.Desc (Block Claim Place)
open VerifiableInference.Desc.First (S)

/-- What is asked of what K4 heard. n3: the number of an array. This defines a hypothesis; the
definition claims nothing. -/
structure RunAsks (p : Par) (o : Own) (n3 : Nat) : Prop where
  heard : ∃ (tk : Array Nat) (fo : Forest.Heard) (F0 G0 : Fork) (t u : OnBytes.K.Kc.Tape),
    hearFl { p.P with tokv := tk } p.hp p.g fo F0 t = some (o, G0, u)
  cols : p.hp.nU.getD 2 0 ≤ o.v.K3
  pad : ∃ F' : Fork, _root_.Fo.Tp.PadNames o.H.fo F'
  array : o.v.iU3 = n3

/-- The hypothesis on the state in front of a run. -/
def RunsPre (p : Par) (s : S) : Prop :=
  ∀ tl o, s.tl? = some tl → s.own? = some o → RunAsks p o ((tl.ix.U.getD 2 none).getD 0)

/-- Forms as claims: no run of entries; the forms' own entries. -/
theorem forms_name (fs : Array Aff) (n3 : Nat)
    (h : ∀ f ∈ fs.toList, ∀ y ∈ f.ents.toList, y.tree = n3) :
    ∀ cl ∈ fs.toList.map claimOf, cl.runs = #[] ∧ ∀ x ∈ cl.form.ents, x.tree = n3 := by
  intro cl hcl
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hcl
  exact ⟨rfl, fun x hx => h f hf x (Array.mem_toList_iff.mpr hx)⟩

/-- The state's own reader at a state that stands in a layers' segment. -/
theorem own_of_lay {s : S} {a : VerifiableInference.Desc.First.LayOwn} (h : s.here = .lay a) :
    s.own? = a.own := by
  simp only [VerifiableInference.Desc.First.S.own?, h]

/-- CONDITIONAL on hA. At one return of the run "front" of the kind's own sub-protocol. -/
theorem front_names {p : Par} {R : Nat → S → Except String (List Claim × S)}
    (hr : (blockAtC p).claims.lookup "front" = some R) {m : Nat} {s s' : S} {cls : List Claim}
    (h : R m s = .ok (cls, s')) {n3 : Nat} (hA : ∀ o, s.own? = some o → RunAsks p o n3) :
    ∀ cl ∈ cls, cl.runs = #[] ∧ ∀ x ∈ cl.form.ents, x.tree = n3 := by
  obtain ⟨a, o, fs, G, ho, hf, rfl, hw⟩ := frontAtC hr h
  obtain ⟨⟨tk, fo, F0, G0, t, u, hh⟩, hK, ⟨F', N⟩, e3⟩ := hA o ((own_of_lay hw.1).trans ho)
  rw [frontOf_eq] at hf
  have hf0 : formsFrontWith (!p.k3Runs) { p.P with tokv := tk } p.g o a.F = some (fs, G) := by
    rw [run_pub (!p.k3Runs) p.P { p.P with tokv := tk } p.g o a.F rfl rfl]
    exact hf
  exact forms_name fs n3 fun f hf' y hy => (front_row0_named hh hK N hf0 f hf' y hy).1.trans e3

/-- CONDITIONAL on hA. At one return of the run "back" of the kind's own sub-protocol. -/
theorem back_names {p : Par} {R : Nat → S → Except String (List Claim × S)}
    (hr : (blockAtC p).claims.lookup "back" = some R) {m : Nat} {s s' : S} {cls : List Claim}
    (h : R m s = .ok (cls, s')) {n3 : Nat} (hA : ∀ o, s.own? = some o → RunAsks p o n3) :
    ∀ cl ∈ cls, cl.runs = #[] ∧ ∀ x ∈ cl.form.ents, x.tree = n3 := by
  obtain ⟨a, o, fs, G, ho, hf, rfl, hw⟩ := backAtC hr h
  obtain ⟨⟨tk, fo, F0, G0, t, u, hh⟩, hK, ⟨F', N⟩, e3⟩ := hA o ((own_of_lay hw.1).trans ho)
  exact forms_name fs n3 fun f hf' y hy => (back_row0_named hh hK N hf f hf' y hy).1.trans e3

/-- CONDITIONAL on `RunsPre`. **THE RUN "front", WITH THE ARRAY's NUMBER READ OFF THE STATE's RECORD
tl**: its claims bear no run of entries, and every entry that a form names lies in the third array
of reads. -/
theorem front_names_tl {p : Par} {R : Nat → S → Except String (List Claim × S)}
    (hr : (blockAtC p).claims.lookup "front" = some R) :
    ∀ m s cls s', RunsPre p s → R m s = .ok (cls, s') → ∀ tl, s.tl? = some tl →
      ∀ cl ∈ cls, cl.runs = #[] ∧ ∀ x ∈ cl.form.ents, x.tree = (tl.ix.U.getD 2 none).getD 0 :=
  fun _ _ _ _ hP h tl ht => front_names hr h fun o ho => hP tl o ht ho

/-- CONDITIONAL on `RunsPre`. **THE RUN "back", WITH THE ARRAY's NUMBER READ OFF THE STATE's RECORD
tl.** -/
theorem back_names_tl {p : Par} {R : Nat → S → Except String (List Claim × S)}
    (hr : (blockAtC p).claims.lookup "back" = some R) :
    ∀ m s cls s', RunsPre p s → R m s = .ok (cls, s') → ∀ tl, s.tl? = some tl →
      ∀ cl ∈ cls, cl.runs = #[] ∧ ∀ x ∈ cl.form.ents, x.tree = (tl.ix.U.getD 2 none).getD 0 :=
  fun _ _ _ _ hP h tl ht => back_names hr h fun o ho => hP tl o ht ho

section
variable {same : S → S → Bool} {b : Block S ProofFile.Cl} {x : Bool × Par} {name : String} {a : Place}
  (hb : IM.LaidAlone same b (ProofFile.k4Block x) name a)
include hb

/-- CONDITIONAL on hb and `RunsPre`. **THE SEATED RUN "front".** -/
theorem front_names_laid {R : Nat → S → Except String (List ProofFile.Cl × S)}
    (hr : b.claims.lookup "front" = some R) :
    ∀ m s cls s', RunsPre { x.2 with k3Runs := true } s → R m s = .ok (cls, s') →
      ∀ tl, s.tl? = some tl →
      ∀ cl ∈ cls, cl.runs = #[] ∧ ∀ y ∈ cl.form.ents, y.tree = (tl.ix.U.getD 2 none).getD 0 := by
  obtain ⟨r', h', -, hy⟩ := IM.claim_yes hb hr
  intro m s cls s' hP h
  exact front_names_tl (p := { x.2 with k3Runs := true }) h' m s cls s' hP
    ((hy m s (cls, s')).1 h).1

/-- CONDITIONAL on hb and `RunsPre`. **THE SEATED RUN "back".** -/
theorem back_names_laid {R : Nat → S → Except String (List ProofFile.Cl × S)}
    (hr : b.claims.lookup "back" = some R) :
    ∀ m s cls s', RunsPre { x.2 with k3Runs := true } s → R m s = .ok (cls, s') →
      ∀ tl, s.tl? = some tl →
      ∀ cl ∈ cls, cl.runs = #[] ∧ ∀ y ∈ cl.form.ents, y.tree = (tl.ix.U.getD 2 none).getD 0 := by
  obtain ⟨r', h', -, hy⟩ := IM.claim_yes hb hr
  intro m s cls s' hP h
  exact back_names_tl (p := { x.2 with k3Runs := true }) h' m s cls s' hP
    ((hy m s (cls, s')).1 h).1

end

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.forms_name
#print axioms ProofFile.Honest.K4.own_of_lay
#print axioms ProofFile.Honest.K4.front_names
#print axioms ProofFile.Honest.K4.back_names
#print axioms ProofFile.Honest.K4.front_names_tl
#print axioms ProofFile.Honest.K4.back_names_tl
#print axioms ProofFile.Honest.K4.front_names_laid
#print axioms ProofFile.Honest.K4.back_names_laid
