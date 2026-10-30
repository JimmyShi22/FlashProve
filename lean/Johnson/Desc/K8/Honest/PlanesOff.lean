-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/PlanesOff.lean: THE SMALLNESS TEST: THE KIND's OWN SHARE OF "NO OTHER PLAIN
CLAIM BEARS ON THE ROW": of the first four claims of the kind's own list each lays nothing on a
virtual row of the bits' array but the one claim whose row it is; and none of the four lays anything
on the reads' row of the digits' array. So the two named premises `PlaneOff`
(Johnson/Desc/K8/Honest/PlanesWeight.lean) and `PlainOff` at the reads' row
(Johnson/Desc/K8/Honest/Added8.lean) come down to the claims of the OTHER runs of the segment: those
gathered in front of the kind's list and those behind it. None of the library's goals.

  `bzRun_off`   a run over a virtual row of the bits' array is no run of another row
  **`four8_plane_off`**   j ≠ 1 + e ⊢ claim number j of the library's `four8` names no entry and no
                   run of virtual row e of the bits' array: a sibling, by the row, of `four8_off`
                   (Johnson/Desc/K8/Honest/NamesOff.lean), which asks an array other than the bits'
  `OthersOff fr bk t r i`   each claim gathered in front of the kind's list, and each behind it,
                   lays 0 on the entry
  **`planeOff_of`**   Added8 · tl.heard = some g · the four premises below · OthersOff at (BZ, e,
                   x) ⊢ PlaneOff fr k8 bk tl e x
  **`plainOff_reads`**   the same premises · OthersOff at (ZZ, the reads' row, x) ⊢ PlainOff fr k8
                   bk tl.ix.ZZ tl.zzRowReads x
The four premises: the two forms that the digits' lookup has heard (its last claim; the start of its
last sumcheck) name no entry · the two calls' pieces lie as the plan lays them (`piecesLaid`) · the
array of the bits is not the array of the digits.
Limits. IMPLICATIONS: `OthersOff` HANGS ON OTHER KINDS' CLAIMS AND IS PAID BY NOBODY HERE; so are
the four premises and `Added8`.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.PlanesWeight
import Johnson.Desc.K8.Honest.NamesOff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc

/-- A run over a virtual row of the bits' array is no run of another row. -/
theorem bzRun_off (tl : HTailF2) (row e : Nat) (c : E) (w : Array E) (h : row ≠ e) :
    ∀ u ∈ (#[Fo.bzRun tl row c w] : Array Run2).toList, ¬ (u.tree = tl.ix.BZ ∧ u.row = e) := by
  intro u hu hcu
  obtain rfl : u = Fo.bzRun tl row c w := List.mem_singleton.1 hu
  exact h hcu.2

/-- **Of the kind's own four claims each but number 1 + e names nothing of row e of the bits'
array.** -/
theorem four8_plane_off (tl : HTailF2) (g : Forest.Heard) (hc : g.cEnd.ents.isEmpty = true)
    (hl : g.leaves.start.ents.isEmpty = true) (hL : piecesLaid tl = true)
    (hB : tl.ix.BZ ≠ tl.ix.ZZ) (e : Nat) :
    ∀ (j : Nat) (cl : Claim), (K9L.four8 tl g)[j]? = some cl → j ≠ 1 + e →
      NamesNotAt tl.ix.BZ e cl := by
  intro j cl hj hne
  rcases j with _ | _ | _ | _ | j
  · obtain rfl := Option.some.inj ((show (K9L.four8 tl g)[0]? = some
      { form := Aff.ofConst (Fo.joinConst tl g) - g.cEnd, runs := (Fo.joinRuns tl g).toArray }
      from rfl).symm.trans hj)
    refine ⟨fun x hx _ => ?_, fun u hu hcu => ?_⟩
    · rcases addMul_ents _ _ _ x hx with h1 | ⟨y, hy, -, -, -⟩
      · simp [Aff.ofConst] at h1
      · exact absurd hy (no_ent _ hc y)
    · have hu' : u ∈ Fo.joinRuns tl g := by simpa using hu
      rw [joinRuns_eq] at hu'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hu'
      obtain ⟨e1, -⟩ := pair_row tl hL x hx
      have c1 : x.2.tree = tl.ix.BZ := hcu.1
      exact hB (c1.symm.trans e1)
  · obtain rfl := Option.some.inj ((four8_one tl g).symm.trans hj)
    refine ⟨fun x hx _ => ?_, bzRun_off tl 0 e _ _ (by omega)⟩
    obtain ⟨y, hy, -, -, -⟩ := rowForm_ents _ _ x hx
    exact absurd hy (no_ent _ hl y)
  · obtain rfl := Option.some.inj ((four8_two tl g).symm.trans hj)
    exact ⟨fun x hx _ => by simp [Aff.slot] at hx, bzRun_off tl 1 e _ _ (by omega)⟩
  · obtain rfl := Option.some.inj ((four8_three tl g).symm.trans hj)
    exact ⟨fun x hx _ => by simp [Aff.ofConst] at hx, bzRun_off tl 2 e _ _ (by omega)⟩
  · exact absurd hj (by simp [K9L.four8])

/-- Each claim gathered in front of the kind's list, and each behind it, lays 0 on the entry. -/
def OthersOff (fr bk : List Claim) (t r i : Nat) : Prop :=
  (∀ cl ∈ fr, coefOn cl t r i = 0) ∧ ∀ cl ∈ bk, coefOn cl t r i = 0

section
variable {tl tl' : HTailF2} {funs : Array HFun} {Y G F₁ F₂ : Fork} {fr k8 bk : List Claim}
  {n₀ : Nat}

/-- **`PlaneOff` comes down to the other runs' claims.** -/
theorem planeOff_of (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) {g : Forest.Heard}
    (hg : tl.heard = some g) (hc : g.cEnd.ents.isEmpty = true)
    (hl : g.leaves.start.ents.isEmpty = true) (hL : piecesLaid tl = true)
    (hB : tl.ix.BZ ≠ tl.ix.ZZ) (e x : Nat) (hO : OthersOff fr bk tl.ix.BZ e x) :
    PlaneOff fr k8 bk tl e x := by
  obtain ⟨g', -, hg', h4, -⟩ := K9L.take_four A.eq
  obtain rfl : g' = g := Option.some.inj (hg'.symm.trans hg)
  refine ⟨fun j cl hj hne => ?_, fun j cl hj => hO.2 cl (List.mem_of_getElem? hj)⟩
  by_cases hlt : j < fr.length
  · rw [List.getElem?_append_left hlt] at hj
    exact hO.1 cl (List.mem_of_getElem? hj)
  · rw [List.getElem?_append_right (by omega), h4] at hj
    exact coefOn_off (four8_plane_off tl g' hc hl hL hB e (j - fr.length) cl hj (by omega)) x

/-- **`PlainOff` at the reads' row comes down to the other runs' claims.** -/
theorem plainOff_reads (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) {g : Forest.Heard}
    (hg : tl.heard = some g) (hc : g.cEnd.ents.isEmpty = true)
    (hl : g.leaves.start.ents.isEmpty = true) (hL : piecesLaid tl = true)
    (hB : tl.ix.BZ ≠ tl.ix.ZZ) (x : Nat) (hO : OthersOff fr bk tl.ix.ZZ tl.zzRowReads x) :
    PlainOff fr k8 bk tl.ix.ZZ tl.zzRowReads x := by
  obtain ⟨g', -, hg', h4, -⟩ := K9L.take_four A.eq
  obtain rfl : g' = g := Option.some.inj (hg'.symm.trans hg)
  refine ⟨fun j cl hj => ?_, fun j cl hj => hO.2 cl (List.mem_of_getElem? hj)⟩
  by_cases hlt : j < fr.length
  · rw [List.getElem?_append_left hlt] at hj
    exact hO.1 cl (List.mem_of_getElem? hj)
  · rw [List.getElem?_append_right (by omega), h4] at hj
    exact coefOn_off (four8_off tl g' hc hl hL tl.ix.ZZ tl.zzRowReads hB (fun h => by
      have h2 := h.2
      unfold HTailF2.zzRowReads at h2
      omega) cl (List.mem_of_getElem? hj)) x

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.bzRun_off
#print axioms VerifiableInference.Desc.First.K8.Honest.four8_plane_off
#print axioms VerifiableInference.Desc.First.K8.Honest.planeOff_of
#print axioms VerifiableInference.Desc.First.K8.Honest.plainOff_reads
