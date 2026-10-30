-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupPlaceProofs.lean: the proofs of the statements of Cb/Ld/LdGroupPlace.lean. Nothing is
assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.

Main names (statements and hypotheses: Cb/Ld/LdGroupPlace.lean):
  `ldGroup_place_cells`: for all new messages m, the slot of the cut (`N.cut m`) that holds a kept
    message encoded anew has, at every cell (a place j with ¬ `N.pad k j`), the entry of its new
    message at the same place.
  `ldGroup_place_cell`, `ldGroup_place_fresh`, `ldGroup_place_rest`: where place sends a cell; a
    fresh pad entry; everything else.
  `ldGroup_place_old`: what goes into the carried message.
  `ldGroup_place_pads`: the slot of the cut at a pad place.
  `ldGroup_place_ride`: the entries of a held message that rides.

Limits: what the head of Cb/Ld/LdGroupPlace.lean lists as not said is not said here either.
-/
import Cb.Ld.LdGroupPlace

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.Ood

namespace GNew
variable {E : Type} [Field E] {S : Sig E} {G : Grp S} {Sh : GShape G} {kp : S.O → Prop}
  [DecidablePred kp] {Hd : GHeld Sh kp} (N : GNew Hd)

open Classical in
/-- what is at a place of a kept message encoded anew (`Hd.toNew .. n`, Cb/Ld/LdGroupPlace.lean)
goes to the same place of the new message (`⟨some n.1, N.same n.1 n.2⟩`) -/
theorem place_toNew (n : Hd.EntA N.ag) :
    N.place (Hd.toNew N.ag N.pad N.Qc n) = ⟨some n.1, N.same n.1 n.2⟩ := by
  have h1 : (Equiv.sumCompl (Hd.InNew N.ag N.pad N.Qc)).symm (Hd.toNew N.ag N.pad N.Qc n) =
      Sum.inl ⟨Hd.toNew N.ag N.pad N.Qc n, n, rfl⟩ :=
    Equiv.sumCompl_symm_apply_of_pos ⟨n, rfl⟩
  have h2 : N.eNew.symm ⟨Hd.toNew N.ag N.pad N.Qc n, n, rfl⟩ = n := by
    rw [Equiv.symm_apply_eq]
    rfl
  show N.toEnt
      (Equiv.sumCongr N.eNew.symm N.eC
        ((Equiv.sumCompl (Hd.InNew N.ag N.pad N.Qc)).symm (Hd.toNew N.ag N.pad N.Qc n))) = _
  rw [h1]
  show N.toEnt (Sum.inl (N.eNew.symm ⟨Hd.toNew N.ag N.pad N.Qc n, n, rfl⟩)) = _
  rw [h2]
  rfl

open Classical in
theorem place_not (u : N.U) (h : ¬ Hd.InNew N.ag N.pad N.Qc u) :
    N.place u = ⟨none, N.eC ⟨u, h⟩⟩ := by
  have h1 : (Equiv.sumCompl (Hd.InNew N.ag N.pad N.Qc)).symm u = Sum.inr ⟨u, h⟩ :=
    Equiv.sumCompl_symm_apply_of_neg h
  show N.toEnt
      (Equiv.sumCongr N.eNew.symm N.eC ((Equiv.sumCompl (Hd.InNew N.ag N.pad N.Qc)).symm u)) = _
  rw [h1]
  rfl

omit [DecidablePred kp] in
/-- an entry of the message of the folded complex goes to a kept message encoded anew only if it is
a cell -/
theorem inNew_msg {c : Sh.Cf.J} (h : Hd.InNew N.ag N.pad N.Qc (.inl (.inl c))) :
    ∃ n : Hd.EntA N.ag, ¬ N.pad n.1 n.2 ∧ Hd.sJ n.1.1 n.2 = c := by
  obtain ⟨n, hn⟩ := h
  unfold GHeld.toNew at hn
  by_cases hp : N.pad n.1 n.2
  · rw [dif_pos hp] at hn
    cases hn
  · rw [dif_neg hp] at hn
    exact ⟨n, hp, Sum.inl.inj (Sum.inl.inj hn)⟩

omit [DecidablePred kp] in
theorem not_inNew_pad {k : {k // N.ag k}} {j : (S.om k.1.1.1).C.J} (h : N.pad k j) :
    ¬ Hd.InNew N.ag N.pad N.Qc (.inl (.inl (Hd.sJ k.1 j))) := fun hc => by
  obtain ⟨⟨⟨k', hk'⟩, j'⟩, hn, he⟩ := N.inNew_msg hc
  obtain ⟨k, hk⟩ := k
  have h3 := N.inj ⟨k', j'⟩ ⟨k, j⟩ he
  obtain rfl : k' = k := congrArg Sigma.fst h3
  obtain rfl : j' = j := eq_of_heq (Sigma.mk.inj h3).2
  exact hn h

omit [DecidablePred kp] in
theorem not_inNew_ride {k : {a // Hd.cl a}} {j : (S.om k.1.1).C.J} (h : ¬ N.ag k) :
    ¬ Hd.InNew N.ag N.pad N.Qc (.inl (.inl (Hd.sJ k j))) := fun hc => by
  obtain ⟨⟨⟨k', hk'⟩, j'⟩, -, he⟩ := N.inNew_msg hc
  have h3 := N.inj ⟨k', j'⟩ ⟨k, j⟩ he
  obtain rfl : k' = k := congrArg Sigma.fst h3
  exact h hk'

end GNew

theorem ldGroup_place_cell : Spec.ldGroup_place_cell := by
  intro E _ S G Sh kp _ Hd N k j h
  have h1 := N.place_toNew ⟨k, j⟩
  unfold GHeld.toNew at h1
  rwa [dif_neg h] at h1

theorem ldGroup_place_fresh : Spec.ldGroup_place_fresh := by
  intro E _ S G Sh kp _ Hd N k j h
  have h1 := N.place_toNew ⟨k, j⟩
  unfold GHeld.toNew at h1
  rwa [dif_pos h] at h1

theorem ldGroup_place_rest : Spec.ldGroup_place_rest := fun _ _ _ _ _ _ _ _ N u h => N.place_not u h

theorem ldGroup_place_old : Spec.ldGroup_place_old := by
  intro E _ S G Sh kp _ Hd N
  refine ⟨fun k j h => ?_, fun q => ?_, fun c => ?_, fun c => ?_, fun q => ?_⟩
  · rw [N.place_not _ (N.not_inNew_pad h)]
  · rw [N.place_not _ fun ⟨n, hn⟩ => by
      unfold GHeld.toNew at hn
      split_ifs at hn
      cases hn]
  · rw [N.place_not _ fun hc => by
      obtain ⟨n, -, he⟩ := N.inNew_msg hc
      cases he]
  · rw [N.place_not _ fun hc => by
      obtain ⟨n, -, he⟩ := N.inNew_msg hc
      cases he]
  · rw [N.place_not _ fun ⟨n, hn⟩ => by
      unfold GHeld.toNew at hn
      split_ifs at hn
      cases hn]

theorem ldGroup_place_cells : Spec.ldGroup_place_cells := by
  intro E _ S G Sh kp _ Hd N m k j h
  show N.N₀.ents m (N.place (.inl (.inl (Hd.sJ k.1 j)))) = _
  rw [ldGroup_place_cell E S G Sh kp Hd N k j h]
  rfl

theorem ldGroup_place_pads : Spec.ldGroup_place_pads := by
  intro E _ S G Sh kp _ Hd N k j h
  refine ⟨N.eC ⟨_, N.not_inNew_pad h⟩, fun m => ?_⟩
  show N.N₀.ents m (N.place (.inl (.inl (Hd.sJ k.1 j)))) = _
  rw [N.place_not _ (N.not_inNew_pad h)]
  rfl

theorem ldGroup_place_ride : Spec.ldGroup_place_ride := by
  intro E _ S G Sh kp _ Hd N k j h
  refine ⟨N.eC ⟨_, N.not_inNew_ride (j := j) h⟩, fun m => ?_⟩
  show N.N₀.ents m (N.place (.inl (.inl (Hd.sJ k j)))) = _
  rw [N.place_not _ (N.not_inNew_ride (j := j) h)]
  rfl

end Cb
