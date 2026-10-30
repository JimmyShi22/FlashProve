-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRelJohnsonProofs.lean: the proofs of the statements of Cb/Ld/LdRelJohnson.lean.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Main names (statements and hypotheses: Cb/Ld/LdRelJohnson.lean):
  `ld_dist_ne`: the distance between the transforms of two different pairs (message, randomness).
  `ld_list_johnson`: the Johnson bound for a code read under a transformation (`LdCode`,
    Cb/Ld/LdRel.lean).
  `ld_list_unique`: unique decoding (the guard).
  `ld_msgs_list`: the list of messages (`LdCode.Msgs`) of a native word.
  `ld_coll`: the lemma on collisions at a code read under a transformation.
  `ld_coll_johnson`: the same from the distance alone.
-/
import Cb.Ld.LdRelJohnson
import Cb.Gen.JohnsonListProofs
import Cb.Gen.OodDecProofs

set_option autoImplicit false

namespace Cb
open Prob Cb.Ood

theorem ld_dist_ne : Spec.ld_dist_ne := by
  intro E P _ _ C d hL hd w w' hne
  have h0 : ¬ ((w - w').1 = 0 ∧ (w - w').2 = 0) := fun h => hne (sub_eq_zero.mp (Prod.ext h.1 h.2))
  refine (hd (w - w').1 (w - w').2 h0).trans (cnt_mono fun x hx heq => hx ?_)
  have h1 : C.enc (w - w').1 (w - w').2 = C.enc w.1 w.2 - C.enc w'.1 w'.2 := hL.encLin.map_sub w w'
  rw [h1, hL.tLin.map_sub, Pi.sub_apply, heq, sub_self]

theorem ld_list_johnson : Spec.ld_list_johnson := by
  intro E P _ _ _ C d e hL hd hJ f
  refine cnt_le_of_forall_finset fun Y hY => ?_
  refine JohnsonList.family_aux (fun (w : (C.J → E) × (C.Q → E)) x => C.T (C.enc w.1 w.2) x) d e hJ
    (C.T f) Y (fun w _ w' _ hne => ld_dist_ne E P C d hL hd w w' hne) fun w hw => ?_
  exact (le_of_eq (cnt_congr fun x => ne_comm)).trans (hY w hw)

theorem ld_list_unique : Spec.ld_list_unique := by
  intro E P _ _ _ C d e hL hd h2 f
  refine cnt_le_of_forall_finset fun Y hY =>
    Finset.card_le_one.mpr fun w hw w' hw' => by_contra fun hne => ?_
  have h1 := ld_dist_ne E P C d hL hd w w' hne
  have h3 : cnt (fun x => C.T (C.enc w.1 w.2) x ≠ C.T (C.enc w'.1 w'.2) x) ≤
      cnt (fun x => C.T f x ≠ C.T (C.enc w.1 w.2) x) +
        cnt (fun x => C.T f x ≠ C.T (C.enc w'.1 w'.2) x) :=
    cnt_le_add fun x hx => by
      by_cases hc : C.T f x = C.T (C.enc w.1 w.2) x
      · exact Or.inr fun hc' => hx (hc.symm.trans hc')
      · exact Or.inl hc
  have h4 : cnt (fun x => C.T f x ≠ C.T (C.enc w.1 w.2) x) ≤ e := hY w hw
  have h5 : cnt (fun x => C.T f x ≠ C.T (C.enc w'.1 w'.2) x) ≤ e := hY w' hw'
  omega

theorem ld_msgs_list : Spec.ld_msgs_list := by
  intro E P _ _ _ C e L hL f
  refine ood_list_mono _ _ _ L (fun m hm => ?_)
    (ood_list_image _ _ (fun w : (C.J → E) × (C.Q → E) => C.Near e f (C.enc w.1 w.2))
      Prod.fst L (ood_list_of_cnt _ _ L (hL f)))
  obtain ⟨r, hr⟩ := hm
  exact ⟨(m, r), hr, rfl⟩

theorem ld_coll : Spec.ld_coll := by
  intro E P _ _ _ C Z e L hL hZ f
  exact ⟨ood_cnt_clash_sample E C.J Z _ L (ld_msgs_list E P C e L hL f) hZ,
    ood_cnt_clash_sq E C.J Z _ L (ld_msgs_list E P C e L hL f) hZ⟩

theorem ld_coll_johnson : Spec.ld_coll_johnson := by
  intro E P _ _ _ C Z d e hL hd hJ hZ f
  exact ld_coll E P C Z e _ (ld_list_johnson E P C d e hL hd hJ) hZ f

end Cb
