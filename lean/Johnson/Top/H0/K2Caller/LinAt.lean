-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/LinAt.lean: the premise `LdLocD.Lin` of the code switch's tie (AfterAt.lean:
`lawAfter_of`) paid at the caller of a place's record, under four inequalities on the stage's sizes.

`sel_lin` (Johnson/Top/H/SwitchSel.lean) has `Lin` from the laws of the folded complex's code,
`Sg.cKept` (OnBytes/Slice/CsRowKept.lean): one main row beside the kept rows, and two mask rows.
Here these laws are shown from the library's laws of one row (`ldOf_laws`, `ldRep_laws`:
OnBytes/Slice/LdOfFacts.lean) and of interleaving and pairing (`ld_laws_il`, `ld_laws_pair`).

  cKept_laws: `(s.cKept K).Laws` at every stage s with `Sg.Sized` (OnBytes/Slice/Numbers.lean)
  lin_at: `Lin` at the caller, for all letters, where the test `SwRow.sizedB` (SizedLit.lean) says
      yes
Limits: the test of Row.lean (`SwRow.ok`) does not ask the four inequalities: `sizedB` is a test
more. Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.AfterAt
import Johnson.Top.H0.K2Caller.SizedLit
import OnBytes.Slice.MembFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch

/-- **The laws of the folded complex's code.** -/
theorem cKept_laws (s : Sg) (K : Type) [Fintype K] [DecidableEq K] (hs : s.Sized) :
    (s.cKept K).Laws :=
  have hZ : s.cZ.Laws := ldRep_laws s.Z s.C.a hs.short (hs.short.trans hs.small) hs.roomZ
  ld_laws_pair GE s.Ps _ _
    (ld_laws_il GE s.Ps s.cM (Option K) (ldOf_laws s.C s.C.a hs.small hs.roomC))
    (ld_laws_pair GE s.Ps _ _ hZ hZ)

/-- **`Lin` at the caller of a place's record.** -/
theorem lin_at {r : SwRow} {H : r.OK} (hs : r.sizedB = true) (X : Letters r H)
    (iJ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r H X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent) :
    (selLoc X iJ iQ).Lin
      (fun j : (selR X).Sh.Cf.J => (⟨Sum.inr (iJ j).1, (iJ j).2⟩ : (selLoc X iJ iQ).S.Ent))
      (fun q : (selR X).Sh.Cf.Q => (⟨Sum.inr (iQ q).1, (iQ q).2⟩ : (selLoc X iJ iQ).S.Ent))
      Slf.idf id :=
  sel_lin _ _ _ _ _ _ _ _ _ _ _ (cKept_laws _ _ (sized_of hs X.t₀))

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.cKept_laws
#print axioms VerifiableInference.Desc.First.K2Caller.lin_at
