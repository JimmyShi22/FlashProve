-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Live/AtYes.lean: CONDITIONAL. TWO LAWS OF Law/Live/ AT A YES OF
THE BLOCK OF THE LAYERS' OWN ROUNDS (sub-protocol K4); AND WHICH SLOT A STATE NAMES AS THE MERGE's.

What is here. A LAW ON THE VERIFIER's TEXT: the honest prover is not in it, and nothing is asked of
a drawn element. Statements and proofs: calls of the library's `blockAtS_hears`
(Johnson/Desc/First/K4/AtSHears.lean: what a yes of K4's block at the carried state gives: the
return of the function that reads K4's rounds, from the ledger of the state in front, and the state
behind) and of two laws of this folder.

  `mergeOf_lay_eq`: if a state at a layers' segment, where the segment's state holds o, names j as
      the slot of the merge's end value (`mergeOf`, Johnson/Desc/First/Batch/AtS.lean), then j is
      o.wo.sFv. From
      the library's `InT.mergeOf_lay` (Johnson/Road/K4/InT/ReaderAtK4.lean): such a state names
      o.wo.sFv.
  `k4_unnamed_of_yes`: **behind a yes: no claim of K4's two lists names that slot**
      (`k4_unnamed_sFv`, Law/Live/Unnamed.lean), at the o that the state behind holds.
  `k4_planes_of_yes`: **behind a yes: the lookup's slots that "front" names through the planes'
      claims are live** (`k4_live_planes`, Law/Live/Whole.lean), at that o.

Not shown here. THE HYPOTHESES ARE PAID NOWHERE HERE: h: the yes · ha · hfo: the state in front is
at a layers' segment, where the segment's state holds the lookup's state fo in its field fo · hF ·
hfree · N · hlv, as in Unnamed.lean, at that segment's ledger · behind the "for all" of both laws:
hy (the lists are written at public data with the block's layout; `k4_unnamed_of_yes` alone) and hlf
(`frontForms` returns) · hJ, as in Whole.lean: the lookup's law is to pay it. The library asks hF,
hfree and hlv of the same state in `KeptAsks` (Johnson/Road/K4/Total/AtKept.lean), and gives N and
hfo behind the lookup's yes (`padNames_behind_calls`, Johnson/Desc/First/Link/Law/K4AtFront.lean):
neither is called here. THAT fo IS WHAT A LATER STATE HOLDS AS HEARD OF THE LOOKUP (another field of
the segment's state, lookHeard). That a later state still holds that o. The third of this folder's
laws at a yes (`k4_live`) wants a tape that meets `TapeLive`: it is Law/Live/LiveOfYes.lean's. This
file gives no example of the hypotheses together; its writers know of none that has been through
Lean.
Kin. `mergeOf_lay_eq`: the library has `InT.mergeOf_lay`'s end once more, from the reader `own?`:
`mergeOf_own` (Johnson/Road/K4/MergeBelow.lean).
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Live.Whole
import Johnson.Desc.First.K4.AtSHears
import Johnson.Road.K4.InT.ReaderAtK4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The default instance `Inst.Model.Scl.ref` (a table of scales) is switched off in this file, so
that no statement picks a table of scales silently. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.Live
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized Filled)
open OnBytes.Desc.First.K4 (blockAtS blockAtS_hears)
open VerifiableInference.Desc.K4Values (frontForms)
open VerifiableInference.Desc.K9H (liveAt unnamedAt)
open VerifiableInference.Desc.First

/-- If a state at a layers' segment, where the segment's state holds o, names j as the merge's
slot, j is o.wo.sFv. -/
theorem mergeOf_lay_eq {s : S} {a : LayOwn} {o : Layer.Own} (hs : s.here = .lay a)
    (ho : a.own = some o) {j : ℕ} (hj : VerifiableInference.Desc.K9.mergeOf s = some j) :
    j = o.wo.sFv :=
  Option.some.inj (hj.symm.trans (OnBytes.Desc.First.K4.InT.mergeOf_lay hs ho))

variable {p : OnBytes.Desc.First.K4.Par} {s s' : S} {rs : List Fmt.RoundView}
  {cols : List (List (Nat × List UInt64))} {a : LayOwn} {fo : Forest.Heard}

/-- CONDITIONAL on all seven hypotheses and, behind the "for all", on hy and hlf. **BEHIND A YES OF
K4's BLOCK: NO CLAIM OF K4's TWO LISTS NAMES THE SLOT OF THE MERGE's END VALUE.** -/
theorem k4_unnamed_of_yes (h : (blockAtS p).decide s rs cols = .ok s') (ha : s.here = .lay a)
    (hfo : a.fo = some fo) (hF : Sized a.F) (hfree : ∀ j, a.F.next ≤ j → ¬ Filled a.F j)
    (N : _root_.Fo.Tp.PadNames fo a.F)
    (hlv : fo.leaves.first + fo.leaves.walk.1.length ≤ a.F.next) :
    ∃ (o : Layer.Own) (G : Fork),
      s' = { s with here := .lay { a with F := G, own := some o }, rowsOwed := none } ∧
      ∀ (rows : Bool) (Q : Layer.Pub) (U : Fork) (lf : List Aff), Q.y = p.P.y →
        frontForms rows Q p.g o U = some lf →
        unnamedAt (K8.Honest.plainOf lf ++ K8.Honest.layersBack o) o.wo.sFv = true := by
  obtain ⟨a', fo', o, G, h1, -, h3, -, -, h6, h7⟩ := blockAtS_hears h
  obtain rfl : a = a' := by
    have e := ha.symm.trans h1
    injection e
  obtain rfl : fo = fo' := Option.some.inj (hfo.symm.trans h3)
  exact ⟨o, G, h7, fun rows Q U lf hy hlf =>
    k4_unnamed_sFv (P := { p.P with tokv := s.tokv }) hF hfree N hlv h6 hy hlf⟩

/-- CONDITIONAL on h, ha, hfo and, behind the "for all", on hlf and, slot by slot, hJ. **BEHIND A
YES OF K4's BLOCK: THE LOOKUP's SLOTS THAT "front" NAMES THROUGH THE PLANES' CLAIMS ARE LIVE.** -/
theorem k4_planes_of_yes (h : (blockAtS p).decide s rs cols = .ok s') (ha : s.here = .lay a)
    (hfo : a.fo = some fo) :
    ∃ (o : Layer.Own) (G : Fork),
      s' = { s with here := .lay { a with F := G, own := some o }, rowsOwed := none } ∧
      ∀ (rows : Bool) (Q : Layer.Pub) (U : Fork) (lf : List Aff),
        frontForms rows Q p.g o U = some lf → ∀ J : ℕ,
        ((∀ kept, cf Reading.gl kept J = 0 →
          cf Reading.gl (fo.leaves.rowForm oneE kept) J ≠ 0) ∨ J = fo.sBit) →
        liveAt (K8.Honest.plainOf lf ++ K8.Honest.layersBack o) J = true := by
  obtain ⟨a', fo', o, G, h1, -, h3, -, -, h6, h7⟩ := blockAtS_hears h
  obtain rfl : a = a' := by
    have e := ha.symm.trans h1
    injection e
  obtain rfl : fo = fo' := Option.some.inj (hfo.symm.trans h3)
  exact ⟨o, G, h7, fun rows Q U lf hlf J hJ =>
    k4_live_planes (OnBytes.Desc.First.K4.Slots.own_fo h6) hlf hJ⟩

end ProofFile.Honest.K4.Live

#print axioms ProofFile.Honest.K4.Live.mergeOf_lay_eq
#print axioms ProofFile.Honest.K4.Live.k4_unnamed_of_yes
#print axioms ProofFile.Honest.K4.Live.k4_planes_of_yes
