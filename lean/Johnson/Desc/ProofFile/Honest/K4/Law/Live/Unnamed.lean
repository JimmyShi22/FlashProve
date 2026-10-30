-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Live/Unnamed.lean: CONDITIONAL. NO CLAIM OF THE LAYERS' OWN TWO
LISTS (sub-protocol K4) NAMES THE SLOT OF THE MERGE's END VALUE.

What is here. A LAW ON THE VERIFIER's TEXT: the honest prover is not in it. NO CLAIM OF THE LAYERS'
OWN TWO LISTS ("front", "back"; sub-protocol K4) NAMES THE SLOT OF THE MERGE's END VALUE, o.wo.sFv.
o: what a hearing of K4's own rounds returned. In Lean's words: the test `unnamedAt`
(Johnson/Desc/K9/Honest/SlotsLive.lean) says true at that slot of `plainOf lf ++ layersBack o`
(Johnson/Desc/K8/Honest/FallLayers.lean), lf the forms of `K4Values.frontForms`
(Johnson/Desc/First/Link/Law/K4Values.lean). Statements and proofs: joinings of the library's
`front_slots`, `back_slots` (Johnson/Road/K4/Slots/FrontBack.lean: which slots the two lists name,
at any shown values), `sFv_at` (Johnson/Road/K4/Total/NotFree.lean: sFv is the merge's first slot +
2 lk + 2) and the laws of Johnson/Road/K4/Total/BelowOk.lean.

  `lookFilled_of_pad`    `PadNames` gives the three premises `LookFilled`.
  `frontForms_some`      a return of `frontForms`, opened.
  `unnamedAt_plainOf`    forms none of which names slot j, as plain claims.
  `k4_front_unnamed`, `k4_back_unnamed`   list by list.
  `k4_unnamed_sFv`       **both lists together.**

Kin. THE LIBRARY HAS THE SAME END AT A RUN's RETURN: `front_not_sFv`, `back_not_sFv`
(Johnson/Road/K4/Total/NotFree.lean): no form that `formsFrontWith` | `formsBack` returns names
o.wo.sFv, under hF, hfree, h and, for "front", `LookFilled` and hlv. Here the lists are held without
a run's return (`frontForms` at any ledger's shown values and at public data with P's layout;
`backForms`), and the end is the test `unnamedAt`. For a lookup's own runs of claims the authors of
the kind "lookup" have the like: `objects_unnamed`, `planes_unnamed`, with `clear_rowForm` on a
sumcheck's own claim (Honest/K3/Good/Live/Unnamed.lean). Their `unnamed_of_forms`
(Honest/K3/Good/Live/Forms.lean) stands beside `unnamedAt_plainOf`: a list none of whose forms names
slot j passes `unnamedAt` at j: theirs at any list of claims, under their own `Clear`; this one at
forms laid as plain claims, under the library's `SlotsIn`.

Not shown here. THE HYPOTHESES ARE PAID NOWHERE HERE: h: o is a return of the hearing, at public
data P, a lookup's state fo and a ledger F; hF: F has arrays of the right sizes; hfree: nothing is
filled in F from its next free number on (the library's `FreeAbove`,
OnBytes/Tie/Pv/Psc/PscRoom.lean, written out); N: what the lookup's kept forms name (`PadNames`,
Johnson/Top/H/Keep/PadNamed.lean); hlv: the lookup's leaves' sumcheck's window lies below F's next
free number; hy: the lists are written at public data Q with P's layout (the hearing's data have the
request's tokens laid in; the lists' have not); hlf: `frontForms` returns. THE OTHER LETTERS: g, the
group's number, IS ONE LETTER IN THE HEARING AND IN THE LIST: a caller brings the list at the
hearing's own group · rows, whether the lookup's own claims head the list: either · U, the ledger
whose shown values the forms read: any. That the merge's slot of a state (`mergeOf`,
Johnson/Desc/First/Batch/AtS.lean) is o.wo.sFv is that definition's text where the state is at a
layers' segment whose state holds o; it is not used here. Nothing on the other slots: whether a
claim names them with a coefficient that is not 0 is Law/Live/Whole.lean's. Nothing on what a form
is worth. This file gives no example of the hypotheses together; its writers know of none that has
been through Lean.
No property is claimed.
-/
import Johnson.Road.K4.Total.BelowOk
import Johnson.Desc.First.Link.Law.K4Values
import Johnson.Desc.K8.Honest.FallLayers
import Johnson.Desc.K9.Honest.SlotsJoin
import Johnson.Top.H.Keep.PadNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The default instance `Inst.Model.Scl.ref` (a table of scales) is switched off in this file, so
that no statement picks a table of scales silently. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.Live
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (HPlan2 Own)
open OnBytes.PscRun (Sized Filled)
open OnBytes.Desc.First.K4 (hear engFl front planesParts rowsSummand)
open OnBytes.Desc.First.K4.Slots (SlotsIn slotsIn_mono front_slots back_slots LookFilled)
open OnBytes.Desc.First.K4.Total (frontOk_below backOk_below frontOk_at_y sFv_at)
open VerifiableInference.Desc.K4Values (frontForms backForms)
open VerifiableInference.Desc.K9H (unnamedAt unnamedIn unnamedAt_append)
open VerifiableInference.Desc.First

variable {P Q : Layer.Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G U : Fork}
  {t u : Tape} {rows : Bool} {lf : List Aff}

/-- What the lookup's kept forms name gives the three premises on the lookup's state. After
Johnson/Road/K4/InT/FormsInTOwn.lean, which does the same inside a proof. -/
theorem lookFilled_of_pad (N : _root_.Fo.Tp.PadNames fo F) : LookFilled rows fo F :=
  ⟨fun _ f hf => (N.rows f hf).filledA, N.sBit.filledA, N.start.filledA⟩

/-- A return of `frontForms`, opened: some shown values, the planes' parts, and the one call of
`front`. -/
theorem frontForms_some (h : frontForms rows Q g o U = some lf) :
    ∃ (sh : Array E) (pp : Aff × List Aff), planesParts o.v o.H.fo = some pp ∧
      front rows Q g o (o.H.tV.p.rowForm (rowsSummand Q.y o.H sh) {})
        (o.H.fo.leaves.rowForm oneE pp.1) = some lf := by
  unfold frontForms at h
  obtain ⟨sh, _, h1⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨pp, a2, h2⟩ := Option.bind_eq_some_iff.mp h1
  exact ⟨sh, pp, a2, h2⟩

/-- Forms none of which names slot j, as plain claims: the test says that j is unnamed. -/
theorem unnamedAt_plainOf (l : List Aff) (j : ℕ) (h : ∀ f ∈ l, SlotsIn (fun i => i ≠ j) f) :
    unnamedAt (K8.Honest.plainOf l) j = true := by
  unfold unnamedAt K8.Honest.plainOf
  rw [List.all_eq_true]
  intro cl hcl
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hcl
  unfold unnamedIn
  rw [List.all_eq_true]
  intro x hx
  exact bne_iff_ne.2 (h f hf x hx)

/-- CONDITIONAL. **No claim of "front" names the slot of the merge's end value.** -/
theorem k4_front_unnamed (hF : Sized F) (hfree : ∀ j, F.next ≤ j → ¬ Filled F j)
    (N : _root_.Fo.Tp.PadNames fo F)
    (hlv : fo.leaves.first + fo.leaves.walk.1.length ≤ F.next)
    (h : hear engFl P hp g fo F t = some (o, G, u)) (hy : Q.y = P.y)
    (hlf : frontForms rows Q g o U = some lf) :
    unnamedAt (K8.Honest.plainOf lf) o.wo.sFv = true := by
  obtain ⟨sh, pp, hpp, hfr⟩ := frontForms_some hlf
  have K := frontOk_at_y (frontOk_below hF hfree (lookFilled_of_pad (rows := rows) N) hlv h) hy
  have e := sFv_at h
  refine unnamedAt_plainOf lf _ fun f hf => ?_
  exact slotsIn_mono (fun j (hj : j < o.wo.toWsMerged.p.first) => by omega)
    (front_slots K sh hpp hfr f hf)

/-- CONDITIONAL. **No claim of "back" names the slot of the merge's end value.** -/
theorem k4_back_unnamed (hF : Sized F) (hfree : ∀ j, F.next ≤ j → ¬ Filled F j)
    (h : hear engFl P hp g fo F t = some (o, G, u)) :
    unnamedAt (K8.Honest.layersBack o) o.wo.sFv = true :=
  unnamedAt_plainOf (backForms o) _ fun f hf =>
    slotsIn_mono (fun j (hj : j < o.wo.sFv) => Nat.ne_of_lt hj)
      (back_slots (backOk_below hF hfree h) f hf)

/-- CONDITIONAL on all seven hypotheses. **NO CLAIM OF K4's TWO LISTS NAMES THE SLOT OF THE MERGE's
END VALUE.** -/
theorem k4_unnamed_sFv (hF : Sized F) (hfree : ∀ j, F.next ≤ j → ¬ Filled F j)
    (N : _root_.Fo.Tp.PadNames fo F)
    (hlv : fo.leaves.first + fo.leaves.walk.1.length ≤ F.next)
    (h : hear engFl P hp g fo F t = some (o, G, u)) (hy : Q.y = P.y)
    (hlf : frontForms rows Q g o U = some lf) :
    unnamedAt (K8.Honest.plainOf lf ++ K8.Honest.layersBack o) o.wo.sFv = true := by
  rw [unnamedAt_append, k4_front_unnamed hF hfree N hlv h hy hlf, k4_back_unnamed hF hfree h]
  rfl

end ProofFile.Honest.K4.Live

#print axioms ProofFile.Honest.K4.Live.lookFilled_of_pad
#print axioms ProofFile.Honest.K4.Live.frontForms_some
#print axioms ProofFile.Honest.K4.Live.unnamedAt_plainOf
#print axioms ProofFile.Honest.K4.Live.k4_front_unnamed
#print axioms ProofFile.Honest.K4.Live.k4_back_unnamed
#print axioms ProofFile.Honest.K4.Live.k4_unnamed_sFv
