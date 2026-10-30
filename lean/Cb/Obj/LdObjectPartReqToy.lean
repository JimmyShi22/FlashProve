-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPartReqToy.lean: at the toy: the new messages of a segment, under the code that
hides 3 long positions (`LdGToy.V74`), and small facts on `R5` and `T`.



A request's preamble is an interactive oracle reduction from a request to claims on the encoded
index and on the oracles that it leaves. The object is one record with a configuration and, over it,
the sub-protocols of the proof system, as five terms. A request's preamble is the fourth.

Definitions and proofs. No parameter of a real protocol.















Main names:
  `LdGToy.V74`: standard oracle messages under the code of seven points and dimension 4
    (Cb/Ld/LdRelToy7d4.lean: distance 4, radius 2, lists of at most 3, hides 3 long positions).
  `V74_all`, `V74_ok`: `OK 3 3`, distance 4, transparent. `first_ok`: `(R5.M a).OK 2 1`.



Limits: on security: this file evaluates no error and says no level of security; the records that
its statements conclude, at the toy, have among their fields `list`, `zk` (`StdM.OK`,
Cb/Obj/LdObjectToyKit.lean).







Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectPartReq
import Cb.Req1.LdSegToy
import Cb.Obj.LdObjectOnBToy
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood LdToy LdToy7 LdToy74

namespace LdGToy

open Classical in
/-- The new messages, under the code that hides 3 long positions. -/
def V74 : StdNew Hh.hd P74 where
  ag := fun _ => True
  pj := fun k => pjAll k.1.1.1
  Mn := fun k =>
    toyStd74 {j : (D.code k.1.1.1).J // j ≠ pjAll k.1.1.1}
      {j : (D.code k.1.1.1).J // j ≠ pjAll k.1.1.1} ind
  cl := fun _ => Equiv.refl _
  Mc := @toyStd74 _ _ (Fintype.ofFinite _) (Classical.decEq _)
    (Fintype.ofFinite _) (Classical.decEq _) ind
  cc := Equiv.refl _
  inj := sJ_inj

open Classical in
theorem V74_all :
    (V74.Mc.OK 3 3 ∧ V74.Mc.Cm.Dist 4 ∧ V74.Mc.Cm.Transparent) ∧
    ∀ k, (V74.Mn k).OK 3 3 ∧ (V74.Mn k).Cm.Dist 4 ∧ (V74.Mn k).Cm.Transparent :=
  ⟨@toyStd74_ok _ _ (Fintype.ofFinite _) (Classical.decEq _) (Fintype.ofFinite _)
      (Classical.decEq _) ind ind_inj,
    fun _ => toyStd74_ok _ _ ind ind_inj⟩

theorem V74_ok : V74.OK 3 3 := ⟨V74_all.1.1, fun k => (V74_all.2 k).1⟩

theorem first_ok (a : Mem) : (R5.M a).OK 2 1 := by
  obtain ⟨hC, hCD, -, -, -, -, zC, -, -⟩ := ld_toy Bool
  obtain ⟨hZ, hZD, -, -, -, -, zZ, -, -⟩ := ld_toy (PCol 1 1 1)
  exact stdGM_ok R5 2 1 4 hC hZ hCD hZD zC zZ (fun C hL hD => list5 C hL hD)
    (fun _ _ h => Subtype.ext h) (fun β => β.2) a

theorem cf_laws : T.sh.Cf.Laws :=
  ld_laws_pair K P5 _ _ hyp.codes.1.1 (ld_laws_pair K P5 _ _ hyp.codes.1.2.1 hyp.codes.1.2.2)

instance (C : ConfigurationWithOutOfDomainSample) : IsEmpty (rqFold C R5 T kp Hh).S₂.O := ⟨fun a => a.2 trivial⟩

instance finAa : Finite T.sh.Cf.Aa :=
  inferInstanceAs
    (Finite ((Option Unit × (toyLd Bool).Aa) ⊕ ((toyLd (PCol 1 1 1)).Aa ⊕ (toyLd (PCol 1 1 1)).Aa)))

end LdGToy

open LdGToy

end Cb
