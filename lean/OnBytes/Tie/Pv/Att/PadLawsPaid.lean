-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Att/PadLawsPaid.lean: the three laws that OnBytes/Tie/Pv/Att/AttBordersRun.lean takes
as premises (PadLaws) hold.

They are the lookup's: Fo.pad_sized' and Fo.pad_clean (OnBytes/Tie/Pv/Lookup/Forest/FoPadKeeps.lean)
and Fo.KeepsL.rootInH (OnBytes/Tie/Pv/Lookup/Ends/FoKeepsLink.lean). These speak of PscRun.Sized
(OnBytes/Tie/Pv/Psc/PscFork.lean), the premises of Road.Sized (OnBytes/Tie/Pv/Psc/Run/PscHide.lean):
the same three equations, once as a conjunction and once as a record.

Main names:
  sized_iff: the two are equivalent.
  padSized: PadSized (OnBytes/Tie/Pv/Att/HearCut.lean).
  padLaws: PadLaws.

Limits: nothing but these.
-/
import OnBytes.Tie.Pv.Att.AttBordersRun
import OnBytes.Tie.Pv.Lookup.Forest.FoPadKeeps
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open OnBytes OnBytes.Model

theorem sized_iff (F : Fork) : Road.Sized F ↔ PscRun.Sized F :=
  ⟨fun h => ⟨h.vp, h.mf, h.got⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

theorem padSized : PadSized := fun _ _ _ F _ _ _ _ h hF =>
  (sized_iff _).2 (Fo.pad_sized' h ((sized_iff F).1 hF))

theorem padLaws : PadLaws where
  sized := padSized
  clean := fun _ _ _ F _ _ _ _ h hF hc => Fo.pad_clean h ((sized_iff F).1 hF) hc
  root := fun trees L _ F _ c _ h hF =>
    (sized_iff _).2 (Fo.KeepsL.rootInH trees L F c _ _ _ h ((sized_iff F).1 hF)).2

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.padLaws
