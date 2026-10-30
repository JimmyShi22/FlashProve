-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoPeelMeets.lean.
The maps from a file's written rounds to the typed rounds of the sub-proofs' lookup: the image in
the words of the byte-level verifier's view, and when a description's rounds meet the spec.

Main names:
  `lookCarry_view`: if each written round meets its spec and sends no answer to a sample, and a
    written transcript τ has the image τ', then forFl h L Ex τ' is the view's rounds
    PQ.rvSL (ckP .two) ds τ, read by Reading.gl.
  `isNZ_all`: where all elements of a round are drawn other than 0, each of them is.
  `Plain d`: the written round d sends elements of the extension field alone, as many as its
    entry's bytes say; it draws no position and no matrix entry, is neither a sealing nor a round
    of seeds, and draws at most as many elements other than 0 as elements.
  `meets_entry`: such a round meets the spec Fo.spEnt d.entry. `Plain.noAns`: it sends no answer to
    a sample.
  `meets_plan`: so written rounds ds with Plain, whose entries are those of a plan that the planner
    finishes at Params.planForest for the shape h, meet Fo.specF h round for round.
Under (meets_plan): 1 ≤ h.v; the planner has finished.
Does not say: that a file's description has these rounds at the lookup's place, or that they are
Plain.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPeelForB
import OnBytes.Tie.Pv.Lookup.Forest.FoPeelView
import OnBytes.Tie.Pv.Lookup.Forest.FoMeetPlan

set_option autoImplicit false

namespace Fo.Peel
open Iop Prob Cb TWhole TwV Tw OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model Run

section
open Cb.Fo
variable {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀] (h : FoNums.Sh) (L : Lay GE St₀ J₀)
  (Ex : ExtSpec) (ds : List PQ.RD)

/-- The image, read as plain data, is the view's rounds read in the field. -/
theorem lookCarry_view (hM : List.Forall₂ Meets ds (specF h)) (hA : ∀ d ∈ ds, NoAns d.items)
    (τ : Tr (PQ.uL (ckP .two) ds)) (τ' : Tr (forB GE h L V₀ V₀C (Ex := Ex)).R.shape)
    (e : (lookCarry h L Ex ds hM.length_eq).tr τ = some τ') :
    forFl h L Ex τ' = (PQ.rvSL (ckP .two) ds τ).map (rdRV Reading.gl) :=
  (lookCarry_read h L Ex ds hM τ τ' e).1.trans (flWs_view ds τ hA).symm

end

/-! ### when a written round meets the spec of its entry -/

theorem isNZ_rep : ∀ (n : ℕ) (l : List Fmt.Draw) (i : ℕ), i < n →
    IsNZ (List.replicate n Fmt.Draw.elemNZ ++ l) i
  | _ + 1, _, 0, _ => trivial
  | n + 1, l, i + 1, h => isNZ_rep n l i (Nat.lt_of_succ_lt_succ h)

/-- Where all elements of a round are drawn other than 0, each of them is. -/
theorem isNZ_all (e : Fmt.Entry) (k : Fmt.Kind) (hp : e.poss = 0) (hk : k ≠ .seeds)
    (hz : e.drawNZ = e.drawE) (i : ℕ) (hi : i < e.drawE) : IsNZ (Fmt.dsOf e k) i := by
  unfold Fmt.dsOf Fmt.dsElems
  rw [hp, if_neg hk, hz, Nat.sub_self]
  exact isNZ_rep e.drawE _ i hi

/-- A written round that sends elements and draws elements, and nothing else. -/
structure Plain (d : PQ.RD) : Prop where
  allE : ∀ it ∈ d.items, it = Fmt.Item.e
  count : d.items.length = d.entry.msg / 24
  poss : d.entry.poss = 0
  logN : d.entry.logN = 0
  trits : d.entry.trits = 0
  notSealed : d.kind ≠ .sealed
  notSeeds : d.kind ≠ .seeds
  nz : d.entry.drawNZ ≤ d.entry.drawE

theorem nS_allE : ∀ l : List Fmt.Item, (∀ it ∈ l, it = Fmt.Item.e) → nS l = l.length
  | [], _ => rfl
  | a :: l, h => by
    obtain rfl := h a List.mem_cons_self
    exact congrArg (· + 1) (nS_allE l fun it hi => h it (List.mem_cons_of_mem _ hi))

theorem Plain.items {d : PQ.RD} (hd : Plain d) : nS d.items = d.entry.msg / 24 :=
  (nS_allE d.items hd.allE).trans hd.count

/-- Such a round sends no answer to a sample. -/
theorem Plain.noAns {d : PQ.RD} (hd : Plain d) : NoAns d.items := fun it hi e => by
  rw [hd.allE it hi] at e
  cases e

theorem meets_entry {d : PQ.RD} (hd : Plain d) : Meets d (spEnt d.entry) where
  sd := by
    have h := sendsDraws_of (d := d) (r := ⟨d.entry, d.kind, d.items, []⟩) ⟨rfl, rfl, rfl⟩ hd.trits
      hd.notSealed hd.notSeeds hd.nz (by rw [hd.logN]; exact Nat.zero_le _)
    simp only [hd.items, hd.poss, hd.logN] at h
    exact h
  nz := fun hz i hi => by
    have hz' : d.entry.drawNZ = d.entry.drawE := by
      simpa [spEnt] using (Bool.and_eq_true_iff.mp hz).2
    exact isNZ_all d.entry d.kind hd.poss hd.notSeeds hz' i hi

theorem meets_map : ∀ ds : List PQ.RD, (∀ d ∈ ds, Plain d) →
    List.Forall₂ Meets ds ((ds.map (·.entry)).map spEnt)
  | [], _ => .nil
  | d :: ds, h => .cons (meets_entry (h d List.mem_cons_self))
      (meets_map ds fun d' hd => h d' (List.mem_cons_of_mem _ hd))

/-- Written rounds whose entries are the plan's meet the lookup's spec. -/
theorem meets_plan {s : Params.Setting} {sc : Params.Scope} (h : FoNums.Sh) (hv : 1 ≤ h.v)
    {P : Params.Planned}
    (hf : Params.finish s sc (Params.planForest ⟨h.v, h.d, FoNums.several h⟩) = .ok P)
    (ds : List PQ.RD) (hd : ∀ d ∈ ds, Plain d) (he : ds.map (·.entry) = P.rounds.map (·.entry)) :
    List.Forall₂ Meets ds (specF h) := by
  have := meets_map ds hd
  rwa [he, plan_spec h hv hf] at this

end Fo.Peel
