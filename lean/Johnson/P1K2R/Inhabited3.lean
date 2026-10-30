-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/Inhabited3.lean: the code switch: THREE TYPES THAT THE KIND's LAW NAMES HAVE A
MEMBER: the premises «the type has a member» of the last join of the kind's named condition. Most
parts of each member are written out: zeros, the empty list, the one point, an oracle message's
own symbols (`Cb.OMsg.sy0`). Two kinds of part are CHOSEN, not written out (`Classical.choice`),
out of the structures' own proofs that a type has a member: a sample's point (`Cb.Ood.Sample.ne`)
and a code's position (`neP`). General in the typed structure r, in the proof H that it passes its
test, and in the two selections iJ, iQ.

Main names:
  `frame_str_ne`: the strings of the first chain's frame at any laid data.
  `stage_ne`: the typed stage's statements and strings, at the plain letters.
  `tb_ne`: the type `TB` (BehindAt.lean) at the plain letters.
  `hI_plain`: the last two together, in the form in which the last join asks them.
Limits. A member of a type says nothing on any relation: no statement is shown true or false of
it. Nothing on soundness. On hiding nothing.

-/
import Johnson.P1K2R.CarryAtConst
import Johnson.Top.H0.K2Caller.PlaceLaw2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc.Sound

/-- The first chain's frame's strings have a member. -/
theorem frame_str_ne (D : OnBytes.Maker.WholeD) : Nonempty (frD D).E.Str :=
  ⟨(fun _ => default, fun _ => [])⟩

section
variable {r : SwRow} {H : r.OK}
  (iJ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.J → (Johnson.Pack.sigOf r.cs r.l).Ent)
  (iQ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
    r.kp).Sh.Cf.Q → (Johnson.Pack.sigOf r.cs r.l).Ent)

set_option maxHeartbeats 1000000 in
/-- The typed stage's statements and strings have a member. -/
theorem stage_ne :
    Nonempty ((Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).X ×
      (Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).Ex.Str) :=
  ⟨⟨⟨⟨⟨(0, fun _ => 0),
      fun k => (Classical.choice ((selZ (Letters.plain r H) iJ iQ).sw.hd.o k).Z.ne, fun _ => 0)⟩,
      PUnit.unit⟩,
    fun a => (Classical.choice
      ((Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).S.om a).Z.ne, fun _ => 0)⟩,
    ⟨⟨fun _ _ => 0, PUnit.unit⟩,
      fun a p => ((Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).S.om a).sy0 p⟩⟩⟩

set_option maxHeartbeats 1000000 in
/-- The type TB has a member. -/
theorem tb_ne : Nonempty (TB (Letters.plain r H) iJ iQ) :=
  ⟨⟨⟨⟨⟨⟨(0, fun _ => 0),
      fun k => (Classical.choice
        ((Cb.Pv.SendLoc.loc (selZ (Letters.plain r H) iJ iQ).sw).hd.o k).Z.ne, fun _ => 0)⟩,
      ⟨fun _ => Classical.choice (Cb.Pv.SendLoc.loc (selZ (Letters.plain r H) iJ iQ).sw).neP,
        fun _ _ => 0⟩⟩, PUnit.unit⟩,
    fun a => (Classical.choice
      ((Cb.Pv.SendLoc.loc (selZ (Letters.plain r H) iJ iQ).sw).tgt.S.om a).Z.ne, fun _ => 0)⟩,
    ⟨⟨PUnit.unit,
      fun a p => ((Cb.Pv.SendLoc.loc (selZ (Letters.plain r H) iJ iQ).sw).tgt.S.om a).sy0 p⟩,
      fun _ _ => 0⟩⟩⟩

/-- The two together, as the last join asks them. -/
theorem hI_plain :
    Nonempty (TB (Letters.plain r H) iJ iQ) ∧
      Nonempty ((Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).X ×
        (Cb.Pv.SendLoc.stage (selZ (Letters.plain r H) iJ iQ).sw).Ex.Str) :=
  ⟨tb_ne iJ iQ, stage_ne iJ iQ⟩

end

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.frame_str_ne
#print axioms VerifiableInference.Desc.First.K2Caller.stage_ne
#print axioms VerifiableInference.Desc.First.K2Caller.tb_ne
#print axioms VerifiableInference.Desc.First.K2Caller.hI_plain
