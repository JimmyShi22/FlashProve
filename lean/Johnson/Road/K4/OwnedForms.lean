-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/OwnedForms.lean: NO FORM OF K4's TWO RUNS OF CLAIMS NAMES A PLACE THAT NO TABLE
OWNS, under four premises on the plan and one premise on the lookup's record for each run: at a
hearing's return every entry that a form of formsFrontWith or of formsBack names lies in the array
of reads, at a place that the smallness test's numbering has for a column and a run of a table of
o.funs. So, if no place belongs to two tables (Apart), the entries entryTrue
(Johnson/Road/K4/EntryTrue.lean) are a table's sum at every entry that the runs name, not the
filling 0.

  `ownedAt tl o a r i`: the array is that of the reads, and a table of o.funs owns the place.
  `owned_form`: a form whose entries lie in the plan's families (InTab) names owned places alone.
  `back_owned`: all forms of the run "back".
  `front_owned`: all forms of the run "front", with the lookup's own claims listed or not;
    `front_owned_seated`: at the form that the seat runs (not listed); `front_owned_bare`: there, if
    the start form of the lookup's leaves' sumcheck names no entry.
  `entryTrue_at`: at an owned place entryTrue is saysOf of an owner.
No new argument: back_covered_left (Johnson/Road/K4/Reads/StackEnts.lean), front_coveredWith_heard
(Johnson/Road/K4/Reads/CoveredWith.lean) and owned_of_inTab (Johnson/Road/K4/OwnedOfInTab.lean).
Limits. Premises: the hearing's return; the run's return; ON THE PLAN, in the letters of PubLines'
fields (Johnson/Road/K4/PubAt.lean): hm = its hmats (the plan's list of matrices has the rows and
columns of tailsOf's), hg (g is a group of the layout), htm (so has the smallness test's record tl),
hNM (tl's number of matrices is its list's length); ON THE LOOKUP's RECORD: behind: the form in
which its key side ends names no entry (he: a field of the lookups' promise K3Left); in front: the
start form of its leaves' sumcheck names entries inside the families (hlv), or none (hs: by report,
PadNames.start with bare_ents gives it, in one of the lookup's files,
Johnson/Top/H/Keep/PadNamed.lean:
not called here), and, where the lookup's own claims are listed, so do they (hK3);
in entryTrue_at also Apart. Nothing on what a prover has committed, on a draw, on soundness or on
hiding.


-/
import Johnson.Road.K4.OwnedOfInTab
import Johnson.Road.K4.Reads.StackEnts
import Johnson.Road.K4.Reads.CoveredWith

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub Own HPlan2)
open OnBytes.Desc.First.K4 (engFl hear hearFl formsBack formsFrontWith)
open OnBytes.Desc.First.K4.Reads (inTab InTab EntsIn entsIn_mono entsIn_noEnts back_covered_left
  front_coveredWith_heard)
open OnBytes.Desc.First.P1 (gl)

/-- The array is that of the reads, and a table of the hearing's list owns the place. -/
def ownedAt (tl : HTailF2) (o : Own) (a r i : ℕ) : Prop :=
  a = o.v.iU3 ∧ ∃ z : HFun × ℕ × ℕ, z.1 ∈ o.funs ∧
    tl.tabAt z.1 z.2.1 z.2.2 = some (r * o.v.K3 + i)

/-- A form whose entries lie in the plan's families names owned places alone. -/
theorem owned_form {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (h : hear engFl P hp g fo F t = some (o, G, u)) (tl : HTailF2)
    (hm : ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) = matsR P.y g) (hg : g < P.y.NGr)
    (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR P.y g) (hNM : tl.NM = tl.mats.size)
    {f : Aff} (hf : InTab o.v f) : EntsIn (ownedAt tl o) f :=
  entsIn_mono (fun _ _ _ hi => owned_of_inTab h tl hm hg htm hNM hi) hf

/-- **No form of the run "back" names a place that no table owns**, under he and the four premises
on the plan. -/
theorem back_owned {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F0 G0 : Fork}
    {t u : Tape} {o : Own} {F G : Fork} {fs : Array Aff}
    (hh : hearFl P hp g fo F0 t = some (o, G0, u)) (he : fo.cEnd.ents = #[])
    (h : formsBack o F = some (fs, G)) (tl : HTailF2)
    (hm : ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) = matsR P.y g) (hg : g < P.y.NGr)
    (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR P.y g) (hNM : tl.NM = tl.mats.size) :
    ∀ f ∈ fs.toList, EntsIn (ownedAt tl o) f := fun f hf =>
  owned_form (show hear engFl P hp g fo F0 t = some (o, G0, u) from hh) tl hm hg htm hNM
    (back_covered_left hh he h f hf)

/-- **No form of the run "front" names a place that no table owns**, under hK3, hlv and the four
premises on the plan. -/
theorem front_owned {rows : Bool} {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard}
    {F0 G0 : Fork} {t u : Tape} {o : Own} {F G : Fork} {fs : Array Aff}
    (hh : hearFl P hp g fo F0 t = some (o, G0, u))
    (h : formsFrontWith rows P g o F = some (fs, G))
    (hK3 : rows = true → ∀ f ∈ o.H.fo.rows.toList, InTab o.v f)
    (hlv : InTab o.v o.H.fo.leaves.start) (tl : HTailF2)
    (hm : ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) = matsR P.y g) (hg : g < P.y.NGr)
    (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR P.y g) (hNM : tl.NM = tl.mats.size) :
    ∀ f ∈ fs.toList, EntsIn (ownedAt tl o) f := fun f hf =>
  owned_form (show hear engFl P hp g fo F0 t = some (o, G0, u) from hh) tl hm hg htm hNM
    (front_coveredWith_heard hh h hK3 hlv f hf)

/-- At the form that the seat runs. -/
theorem front_owned_seated {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard}
    {F0 G0 : Fork} {t u : Tape} {o : Own} {F G : Fork} {fs : Array Aff}
    (hh : hearFl P hp g fo F0 t = some (o, G0, u))
    (h : formsFrontWith false P g o F = some (fs, G))
    (hlv : InTab o.v o.H.fo.leaves.start) (tl : HTailF2)
    (hm : ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) = matsR P.y g) (hg : g < P.y.NGr)
    (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR P.y g) (hNM : tl.NM = tl.mats.size) :
    ∀ f ∈ fs.toList, EntsIn (ownedAt tl o) f :=
  front_owned hh h (fun e => by cases e) hlv tl hm hg htm hNM

/-- At the form that the seat runs, if the leaves' start form names no entry. -/
theorem front_owned_bare {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard}
    {F0 G0 : Fork} {t u : Tape} {o : Own} {F G : Fork} {fs : Array Aff}
    (hh : hearFl P hp g fo F0 t = some (o, G0, u))
    (h : formsFrontWith false P g o F = some (fs, G))
    (hs : o.H.fo.leaves.start.ents = #[]) (tl : HTailF2)
    (hm : ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) = matsR P.y g) (hg : g < P.y.NGr)
    (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR P.y g) (hNM : tl.NM = tl.mats.size) :
    ∀ f ∈ fs.toList, EntsIn (ownedAt tl o) f :=
  front_owned_seated hh h (entsIn_noEnts hs) tl hm hg htm hNM

/-- At an owned place the entry is a table's sum, if no place belongs to two tables. -/
theorem entryTrue_at {tl : HTailF2} {o : Own} (hA : Apart tl o.funs) (M : Mats Cb.Gl.E)
    {a r i : ℕ} (hi : ownedAt tl o a r i) :
    ∃ z : HFun × ℕ × ℕ, z.1 ∈ o.funs ∧ tl.tabAt z.1 z.2.1 z.2.2 = some (r * o.v.K3 + i) ∧
      entryTrue tl o M a r i = saysOf gl M z.1 z.2.1 z.2.2 := by
  classical
  obtain ⟨rfl, z, hz, hp⟩ := hi
  refine ⟨z, hz, hp, ?_⟩
  show (if o.v.iU3 = o.v.iU3 then
    (if h : ∃ x : HFun × ℕ × ℕ, x.1 ∈ o.funs ∧
        tl.tabAt x.1 x.2.1 x.2.2 = some (r * o.v.K3 + i)
     then saysOf gl M h.choose.1 h.choose.2.1 h.choose.2.2 else 0) else 0) =
    saysOf gl M z.1 z.2.1 z.2.2
  rw [if_pos rfl]
  have hex : ∃ x : HFun × ℕ × ℕ, x.1 ∈ o.funs ∧
      tl.tabAt x.1 x.2.1 x.2.2 = some (r * o.v.K3 + i) := ⟨z, hz, hp⟩
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  obtain ⟨e1, e2, e3⟩ := hA _ h1 _ hz _ _ _ _ _ h2 hp
  rw [e1, e2, e3]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.owned_form
#print axioms OnBytes.Road.K4.back_owned
#print axioms OnBytes.Road.K4.front_owned
#print axioms OnBytes.Road.K4.front_owned_seated
#print axioms OnBytes.Road.K4.front_owned_bare
#print axioms OnBytes.Road.K4.entryTrue_at
