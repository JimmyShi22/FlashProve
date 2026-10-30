-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/SkelSides.lean: CONDITIONAL: on `LookSkel`.

What is here. A CONGRUENCE: WHAT THE SECOND TOKEN SUMCHECK's JOB AND THE BATCHED SUMCHECK's JOB
SHARE (`Sides.of`, Johnson/Desc/K4/Honest/Sides.lean), AT ANY TWO INPUTS and at two lists of what
the lookup has sampled, of one skeleton (`LookSkel`, Law/LookSkel.lean). A definition, and a
statement with its proof.

  `SidesSkel`   what of the shared data the two jobs' returns and shapes read AT MOST: that it is
      enough is shown in Law/SkelTerms.lean and Law/SkelStack.lean, not here.
  **`sidesOf_rel`**   both calls return or neither does, and what they return is in `SidesSkel`.

Debts and ends. `SidesSkel` IS AN END: NO DEBT: WHEREVER A LAW THAT TAKES IT IS CALLED BY A LAW THAT
DOES NOT TAKE IT ITSELF, IT IS PAID ON THE SPOT BY ONE OF TWO LAWS. It is concluded by
`sidesOf_rel`, here, FROM `LookSkel` ALONE, THE TWO INPUTS w AND w₀ BEING FREE LETTERS; and of a
thing and itself by `sidesSkel_refl` (Law/AtEnds.lean). It is a hypothesis of seven laws of
Law/SkelTerms.lean and one of Law/SkelStack.lean, and, as the field S of `DataSkel`, of four more
there. Outside these two files such a law is called in Law/FitTerms.lean, Law/TermsAll.lean and
Law/AtEnds.lean alone, each time at one shared data, with `sidesSkel_refl` or `dataSkel_refl`. The
laws at two inputs that other files call, `jobTerms_skel` and `jobStack_skel`, do not name it: they
ask `LookSkel`, or `PtsSkel` and a length. WHAT IT COMPARES BETWEEN TWO INPUTS: public data, names
and lengths: its own docstring lists them, and what is NOT in it: the input, any table of weights,
the gated products, what the rotation factor reads, any element outside the public data. `LookSkel`
IS A DEBT: see Law/LookSkel.lean.

Not shown here. `Sides.of` IS SHOWN TO RETURN NOWHERE: two calls are compared. That each field of
`SidesSkel` is read. Nothing on what a table, a form or a weight is worth.

Kin. No twin is known to its writers. What `Sides.of` lays, field by field, from one return:
`sides_fields` (Johnson/Road/K4/C/TermsAtOf.lean). The proof calls the library's `weightClaims_rel`
and `headWeights_rel` (Johnson/Desc/First/K4/Returns/Pub/Claims.lean). No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SkelEnv
import Johnson.Desc.ProofFile.Honest.K4.Law.SkelOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Flat (All2 OptRel optRel_bind optRel_bind_same)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.RtPub

/-- **What of the shared data the two jobs' returns and shapes read AT MOST** (that it is enough:
SkelTerms.lean and SkelStack.lean; that each field is read: nowhere): the place's public data; the
lookup's public numbers and lengths; the environment but for the calls' points, of which each one's
length is held; the calls' numbers; the lengths of the token point and of the long tables' first
coordinates; the number of the panels' weight claims; the entries that the claims on the shown
values name. NOT in it: the input, any table of weights, the gated products, what the rotation
factor reads, any element but what the public data Q themselves hold (the plan's state Q.hp.Fp has
fields of elements; in `sidesOf_rel` Q is one letter). -/
structure SidesSkel (S S₀ : Sides) : Prop where
  Q : S.Q = S₀.Q
  fo : LookSkel S.fo S₀.fo
  v : EnvLook S.v S₀.v
  TS : S.TS = S₀.TS
  zt : S.zt.size = S₀.zt.size
  zlow : S.zlow.size = S₀.zlow.size
  opens : S.opens.size = S₀.opens.size
  ends : All2 FormKeys S.ends S₀.ends

/-- **What the two jobs share, at two inputs and two lists of one skeleton.** -/
theorem sidesOf_rel (Q : K4Pub) (w w₀ : K4In) {p p₀ : Pts} (S : LookSkel p.fo p₀.fo) :
    OptRel SidesSkel (Sides.of Q w p) (Sides.of Q w₀ p₀) := by
  unfold Sides.of
  dsimp only
  refine optRel_bind (envOf_rel Q S) fun v v₀ hv => ?_
  refine optRel_bind_same fun TS => ?_
  refine optRel_bind (lastOf_rel S.zx _) fun Z Z₀ hZ => ?_
  have C : ClaimSkel
      { v := v, wsLay := Q.P.wsLay, rope := Q.P.rope, rs := Array.replicate Q.hp.lamS zeroE,
        rt := #[] }
      { v := v₀, wsLay := Q.P.wsLay, rope := Q.P.rope, rs := Array.replicate Q.hp.lamS zeroE,
        rt := #[] } := ⟨hv.1.keys.y, hv.1.g, rfl, rfl, hv.1.zk⟩
  refine optRel_bind (weightClaims_rel C TS) fun cls cls₀ hc => ?_
  refine optRel_bind (headWeights_rel C) fun a a₀ _ => ?_
  refine optRel_bind (amapM_all2_rel (l := cls.toArray) (l' := cls₀.toArray)
    (fun _ _ h => openOf_rel Q.P.wsLay w.w w₀.w _ h) hc) fun o o₀ ho => ?_
  refine optRel_bind (S := fun _ _ => True) ?_ fun t t₀ _ => ?_
  · unfold gatedTabs
    exact optRel_bind_same fun _ => optRel_bind_same fun _ => trivial
  -- `termsForms` reads of its second argument the field tT alone: so the two calls are one term
  rw [termsForms_eq hv.1.keys]
  refine optRel_bind_same fun ends => ?_
  refine ⟨rfl, S, hv.1, rfl, ztOf_skel Q S, ?_, ?_, All2.refl (R := FormKeys) (fun _ => rfl) ends⟩
  · show (Z.extract 0 Q.P.y.ls).size = (Z₀.extract 0 Q.P.y.ls).size
    rw [Array.size_extract, Array.size_extract, hZ]
  · show o.size = o₀.size
    rw [← Array.length_toList, ← Array.length_toList]
    exact ho.length

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.SidesSkel
#print axioms ProofFile.Honest.K4.sidesOf_rel
