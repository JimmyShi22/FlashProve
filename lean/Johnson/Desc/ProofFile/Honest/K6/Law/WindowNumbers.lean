-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/WindowNumbers.lean: THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6):
UNDER THE HYPOTHESIS h (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean): THE DESCRIPTION PASSES THE LIBRARY's
TEST ON PLACES; THE LOOKUP ON THE HEAD's CALLS SENDS 1,995 SCALARS; `takesOf`, THE LIBRARY's CEILING
ON THE LEDGER NUMBERS THAT K6 TAKES, IS 173; THE TWO NUMBERS ADD UP TO 2168. No definition; four
theorems. Corollaries of the library's own lemmas, as numerals. No file of the library calls them.

  `k6_placesOk_at_head`  (F0T …).placesOk = true: the library's `placesOk_of_planOk`
                         (Johnson/RunOne/Sound/KeyListsAtFK.lean) at the field planOk of h's laid
                         value
  `k6_elems_at_head`     Forest.elems (At.X Zp).HLy.fs = 1995: the field elems of the library's
                         `FsWritten` at `fs_in_scope` (Johnson/Desc/Kinds/Law/HeadFsWritten.lean)
  `k6_takes_at_head`     takesOf … = 173: the lines that stand inside the proof of the library's
                         `k6Pub_in_scope` (Johnson/Desc/Kinds/Law/K6PubInScope.lean), again
  `k6_window_at_head`    the sum of the two numbers: 2168

Limits.
  * h: the full size and the format's second hash function alone.
  * Public numbers alone: nothing on a coin, an entry, a value or a run.
  * `takesOf` IS A CEILING (Johnson/Desc/Kinds/Law/TakesAt.lean): that K6 takes or sends just 173 is
    not said here.
  * NO STATEMENT HERE SPEAKS OF A SLOT: at which ledger slot K6 begins or ends is not said here, the
    last theorem's name notwithstanding.
  * IT STANDS OVER THE LIBRARY ALONE. IT CALLS `numbers_in_scope`, WHICH IS DECLARED UNDER
    lean/Johnson/Goal/Meaning/ (HeadCondScope.lean); it imports no module of that folder by name.
  * Nothing on any property.
-/
import Johnson.RunOne.Sound.KeyListsAtFK
import Johnson.Desc.Kinds.Law.K6PubInScope
import Johnson.Desc.Kinds.Law.TakesAt
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Kinds (Norm.lPd)
open VerifiableInference.Desc.Kinds.Head (parOf)
open VerifiableInference.Desc.Kinds.Head.Law (workOf takesOf)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (fs_in_scope numbers_in_scope)
open OnBytes.Maker (WholeD)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: the hypothesis h. The description passes the library's test on places. -/
theorem k6_placesOk_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (P5J.F0T OnBytes.secondHashFunction Zp Np cF).placesOk = true :=
  Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk

/-- CONDITIONAL: the hypothesis h. The lookup on the head's calls sends 1,995 scalars. -/
theorem k6_elems_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    OnBytes.Model.Forest.elems (P5J.At.X Zp).HLy.fs = 1995 :=
  (fs_in_scope h.scope h.reads h.pubOne).elems

/-- CONDITIONAL: the hypothesis h. The library's ceiling on the ledger numbers that K6 takes is 173.
-/
theorem k6_takes_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    takesOf (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) = 173 := by
  have N := numbers_in_scope h.scope h.reads h.pubOne
  unfold takesOf Norm.lPd
  show 41 + 8 * (P5J.At.X Zp).hS.lt + 4 * OnBytes.Model.clog2 (P5J.At.X Zp).hS.d = 173
  rw [N.lt, N.d]
  decide

/-- CONDITIONAL: the hypothesis h. **The lookup's scalars and that ceiling add up to 2168.** -/
theorem k6_window_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    OnBytes.Model.Forest.elems (P5J.At.X Zp).HLy.fs +
      takesOf (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) = 2168 := by
  rw [k6_elems_at_head h, k6_takes_at_head h]

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.k6_placesOk_at_head
#print axioms ProofFile.Honest.K6.k6_elems_at_head
#print axioms ProofFile.Honest.K6.k6_takes_at_head
#print axioms ProofFile.Honest.K6.k6_window_at_head
