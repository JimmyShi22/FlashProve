-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoLevelAlg.lean.
Small laws for reading one level of a product tree: the calls as rounds, the coordinates read,
forms by their values.

* `flEv_level`, `closed_level`: the channel's calls of a level, read as rounds, are one sumcheck
  as plain data (PscTie's flH) followed by the line's round; no message stays open.
* `sizes_level`: the numbers of scalars sent and of elements drawn, round by round. Premises: each
  round of the level sends 2 scalars, and 2 values are shown.
* `zs_level`: the coordinates that the rounds read, then 0 for the further variable. Premises: the
  order names variables below mu; the point has mu coordinates and is rho read, reversed.
* `byVar_snoc`: the point by coordinate does not see the further variable's challenge. Premise:
  the order is a permutation of the coordinates' numbers.
* `formIs_of_val`: a form is compared by its values alone (its public part reads as its value
  in the world in which each slot holds what was shown).
* `FormIs.lin2`: a combination of two forms.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoLevel

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie

section
variable {K : Type} [CommRing K] (ρ : Reading K)

theorem flGo_lvEv : ∀ (rs : List (Array OnBytes.E × OnBytes.E)) (l : List Ev),
    flGo ρ [] (lvEv rs ++ l) = flR ρ (lvRs rs) ++ flGo ρ [] l
  | [], _ => rfl
  | q :: rs, l => by
    show ([] ++ q.1.toList.map ρ.val, [ρ.val q.2]) :: flGo ρ [] (lvEv rs ++ l) = _
    rw [flGo_lvEv rs l]
    rfl

theorem openAfter_lvEv : ∀ (rs : List (Array OnBytes.E × OnBytes.E)) (l : List Ev),
    openAfter ρ [] (lvEv rs ++ l) = openAfter ρ [] l
  | [], _ => rfl
  | _ :: rs, l => openAfter_lvEv rs l

theorem flEv_level (m0 eps : OnBytes.E) (rs : List (Array OnBytes.E × OnBytes.E))
    (sentY : Array OnBytes.E) (beta : OnBytes.E) (vals : Array OnBytes.E) (tau : OnBytes.E) :
    flEv ρ (levelEv m0 eps rs sentY beta vals tau) =
      flH ρ m0 eps (lvRs rs ++ [(sentY.toList, beta)]) (some vals.toList) ++
        [([], [ρ.val tau])] := by
  show ([] ++ [ρ.val m0], [ρ.val eps]) :: flGo ρ [] (lvEv rs ++ _) = _
  rw [flGo_lvEv]
  unfold flH flR
  simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append, List.append_assoc,
    List.nil_append]
  rfl

/-- How many scalars each round of a level sends, and how many elements it draws. -/
theorem sizes_level (m0 eps : OnBytes.E) (rs : List (Array OnBytes.E × OnBytes.E))
    (sentY : Array OnBytes.E) (beta : OnBytes.E) (vals : Array OnBytes.E) (tau : OnBytes.E)
    (hq : ∀ q ∈ rs, q.1.size = 2) (hY : sentY.size = 2) (hv : vals.size = 2) :
    (flEv ρ (levelEv m0 eps rs sentY beta vals tau)).map (fun r => (r.1.length, r.2.length)) =
      [(1, 1)] ++ List.replicate rs.length (2, 1) ++ [(2, 1), (2, 0), (0, 1)] := by
  have e : ((flR ρ (lvRs rs)).map fun r => (r.1.length, r.2.length)) =
      List.replicate rs.length (2, 1) := by
    refine List.eq_replicate_iff.mpr ⟨by simp [flR, lvRs], fun b hb => ?_⟩
    simp only [flR, lvRs, List.map_map, List.mem_map] at hb
    obtain ⟨q, hq', rfl⟩ := hb
    simp [hq q hq']
  rw [flEv_level]
  unfold flH
  have e2 : flR ρ (lvRs rs ++ [(sentY.toList, beta)]) =
      flR ρ (lvRs rs) ++ [(sentY.toList.map ρ.val, [ρ.val beta])] := by
    simp [flR]
  rw [e2]
  simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append, e]
  simp [hY, hv]

theorem closed_level (m0 eps : OnBytes.E) (rs : List (Array OnBytes.E × OnBytes.E))
    (sentY : Array OnBytes.E) (beta : OnBytes.E) (vals : Array OnBytes.E) (tau : OnBytes.E) :
    Closed ρ (levelEv m0 eps rs sentY beta vals tau) := by
  show openAfter ρ [] (lvEv rs ++ _) = []
  rw [openAfter_lvEv]
  rfl

theorem zs_level (mu : ℕ) (rho : Array OnBytes.E) (order : List ℕ) (hv : ∀ v ∈ order, v < mu)
    (pt : List K) (hl : pt.length = mu) (hr : rdA ρ rho = pt.reverse) :
    ((lvZd mu rho order ++ [(zeroE, 3)]).map fun x : OnBytes.E × ℕ => ρ.val x.1) =
      inRounds order pt ++ [0] := by
  have h0 : rho.size = mu := by
    have := congrArg List.length hr
    simpa [rdA, hl] using this
  have e : (rho.toList.map ρ.val).reverse = pt := by
    have := congrArg List.reverse hr
    simpa [rdA] using this
  rw [List.map_append, ← e, ← readAt_inRounds ρ.val zeroE mu order hv rho h0]
  simp only [lvZd, List.map_map, List.map_cons, List.map_nil, ρ.zero]
  rfl

theorem byVar_snoc (order : List ℕ) (xs : List K) (b : K)
    (hp : order.Perm (List.range xs.length)) : byVar order (xs ++ [b]) = byVar order xs := by
  unfold byVar
  refine List.map_congr_left fun c hc => ?_
  have hlen : order.length = xs.length := by rw [hp.length_eq, List.length_range]
  have hm : c ∈ order := hp.symm.subset (by rw [← hlen]; exact hc)
  have hi : order.idxOf c < xs.length := by rw [← hlen]; exact List.idxOf_lt_length_of_mem hm
  rw [List.getD_append _ _ _ _ hi]

/-- The world in which each slot holds what was shown, and every entry is 0. -/
private def shownWorld (F : Fork) : World K := ⟨fun j => ρ.val (F.vp.getD j zeroE), fun _ _ _ => 0⟩

private theorem publicPart_value (F : Fork) (a : Aff) (x : OnBytes.E)
    (h : F.publicPart a = some x) :
    ρ.val x = a.value ρ (shownWorld ρ F) := by
  unfold Fork.publicPart at h
  rw [← Array.foldlM_toList] at h
  have H := foldlM_adds
    (fun (v : OnBytes.E) (y : ℕ × OnBytes.E) => (F.shown y.1).map fun z => addE v (mulE y.2 z))
    (fun _ => True) ρ.val (slotValue ρ (shownWorld ρ F)) (by
      intro s y s' _ hs
      refine ⟨trivial, ?_⟩
      have hs' : (F.shown y.1).map (fun z => addE s (mulE y.2 z)) = some s' := hs
      unfold Fork.shown at hs'
      split at hs'
      · obtain rfl := Option.some.inj hs'
        rw [ρ.add, ρ.mul]
        rfl
      · exact absurd hs' (by simp)) a.slots.toList a.const x trivial h
  have he : (a.ents.toList.map (Ent.value ρ (shownWorld ρ F))).sum = 0 := by
    refine List.sum_eq_zero fun y hy => ?_
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy
    show ρ.val z.coef * 0 = 0
    rw [mul_zero]
  unfold Aff.value
  rw [H.2, he]
  ring

private theorem evalL_zero (inc : List (Pl × K)) : evalL (muOf (fun _ => (0 : K))) inc = 0 := by
  unfold evalL
  refine List.sum_eq_zero fun y hy => ?_
  obtain ⟨z, _, rfl⟩ := List.mem_map.mp hy
  have : muOf (fun _ => (0 : K)) z.1 = 0 := by cases z.1 <;> rfl
  rw [this, mul_zero]

private theorem worldOf_zero (F : Fork) :
    F.worldOf ρ (fun _ => 0) (fun _ _ _ => 0) = shownWorld ρ F := by
  unfold Fork.worldOf shownWorld
  simp only [mul_zero, sub_zero]

/-- A form is compared by its values alone. -/
theorem formIs_of_val {F : Fork} {C : Aff} {tg : K} {inc : List (Pl × K)}
    (h : ∀ G, Later F G → ∀ (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K),
      C.value ρ (G.worldOf ρ mask entry) = tg - evalL (muOf mask) inc) : FormIs ρ F C tg inc :=
  fun G hG => ⟨fun x hx => by
    rw [publicPart_value ρ G C x hx, ← worldOf_zero, h G hG, evalL_zero, sub_zero], h G hG⟩

/-- A combination of two forms. -/
theorem FormIs.lin2 {F : Fork} {C1 C2 : Aff} {t1 t2 : K} {i1 i2 : List (Pl × K)}
    (h1 : FormIs ρ F C1 t1 i1) (h2 : FormIs ρ F C2 t2 i2) (a b : OnBytes.E) :
    FormIs ρ F (Aff.scale C1 a + Aff.scale C2 b) (ρ.val a * t1 + ρ.val b * t2)
      (scale (ρ.val a) i1 ++ scale (ρ.val b) i2) :=
  formIs_of_val ρ fun G hG mask entry => by
    rw [Aff.value_add, Aff.value_scale, Aff.value_scale, (h1 G hG).2, (h2 G hG).2]
    unfold evalL
    rw [List.map_append, List.sum_append]
    have e : ∀ (u : K) (i : List (Pl × K)),
        ((scale u i).map fun pc => pc.2 * muOf mask pc.1).sum =
          u * (i.map fun pc => pc.2 * muOf mask pc.1).sum := by
      intro u i
      unfold scale
      rw [List.map_map, ← List.sum_map_mul_left]
      refine congrArg List.sum (List.map_congr_left fun pc _ => ?_)
      simp only [Function.comp]
      ring
    rw [e, e]
    ring

end
end Fo
