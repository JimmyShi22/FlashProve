-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/PadsView.lean: the light test padsDoor (Johnson/Desc/Kinds/PadsDoor.lean) is
a function of a small plain structure: it equals padsV (Johnson/Desc/Kinds/PadsTest.lean) at the
view of its arguments. Definitions and theorems. No Mathlib.

What is proved.
  pairsOf iXI nas NHf   the 24 pairs (reading segment, owning segment, the matrix's number in the
          reading segment's list), as a list.
  pmemP, padsViewOf     what the test reads of an oracle message; the view of padsDoor's arguments.
          A segment's number counts up to 24.
  padsDoor_pairs        padsDoor is padFreeP at every one of the 24 pairs.
  **padsDoor_eq**       padsDoor cs layout labs num arr group mems iXI nas NHf = padsV (padsViewOf
          cs layout labs num arr group mems iXI nas NHf), for all arguments.

No existential quantifier in these statements.
Not proved here. The view of any particular public files. Nothing on soundness.

-/
import Johnson.Desc.Kinds.PadsDoor
import Johnson.Desc.Kinds.PadsTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

open OnBytes.Params (ReqArray ReqLayout)

/-- The 24 pairs. -/
def pairsOf (iXI : Nat) (nas : Nat → Nat) (NHf : Nat) : List (Nat × Nat × Nat) :=
  ((List.range 12).flatMap fun g =>
    (if g == 0 then [] else [(2 * g, 2 * (g - 1), iXI)]) ++ [(2 * g + 1, 2 * g, nas g + 3)]) ++
    [(24, 22, NHf + 3)]

section
variable (cs : OnBytes.Codes) (layout : ReqLayout) (labs : Nat → Nat → Nat)
  (num arr : Nat → Nat → Nat) (group : Nat → List (Nat × Nat))
  (mems : List (OnBytes.OracleShape × (Nat × Nat)))

/-- What the test reads of a sampled oracle message. -/
def pmemP (y : OnBytes.OracleShape × (Nat × Nat)) : PMemV :=
  { segs := (List.range 25).filter fun k => (group k).contains y.2
    num := arr y.2.1 y.2.2
    mainRows := y.1.mainRows
    maskRows := y.1.maskRows
    mainDeg := y.1.mainDeg
    ell := (cs.base.getD y.1.code default).ell }

/-- The view. -/
def padsViewOf (iXI : Nat) (nas : Nat → Nat) (NHf : Nat) : PadsView :=
  { pairs := (pairsOf iXI nas NHf).map fun x =>
      (x.1, x.2.1,
        (VerifiableInference.Desc.arrayOf layout (ownerP (labs x.1 x.2.2)).1
          (ownerP (labs x.1 x.2.2)).2).map (arrV num (ownerP (labs x.1 x.2.2)).1))
    mems := mems.map (pmemP cs arr group) }

/-- padsDoor is padFreeP at every one of the 24 pairs. -/
theorem padsDoor_pairs (iXI : Nat) (nas : Nat → Nat) (NHf : Nat) :
    padsDoor cs layout labs num arr group mems iXI nas NHf =
      (pairsOf iXI nas NHf).all fun x =>
        padFreeP cs layout labs num arr group mems x.1 x.2.1 x.2.2 := by
  unfold padsDoor pairsOf
  rw [List.all_append, List.all_flatMap]
  congr 1
  · refine congrArg (fun f => (List.range 12).all f) (funext fun g => ?_)
    rw [List.all_append]
    cases hg : (g == 0)
    · simp
    · simp
  · simp

theorem segs_mem {k : Nat} (hk : k < 25) (y : OnBytes.OracleShape × (Nat × Nat)) :
    (pmemP cs arr group y).segs.contains k = (group k).contains y.2 := by
  unfold pmemP
  dsimp only
  cases h : (group k).contains y.2
  · rw [List.contains_eq_mem, decide_eq_false_iff_not, List.mem_filter]
    exact fun x => by rw [h] at x; exact Bool.noConfusion x.2
  · rw [List.contains_eq_mem, decide_eq_true_eq, List.mem_filter]
    exact ⟨List.mem_range.2 hk, h⟩

theorem there_eq (iXI : Nat) (nas : Nat → Nat) (NHf : Nat) {k : Nat} (hk : k < 25) (n : Nat) :
    copyThereP arr group mems k n =
      thereV (padsViewOf cs layout labs num arr group mems iXI nas NHf) k n := by
  unfold copyThereP thereV padsViewOf
  dsimp only
  rw [List.any_map]
  refine congrArg (fun f => mems.any f) (funext fun y => ?_)
  show _ = ((pmemP cs arr group y).segs.contains k && _)
  rw [segs_mem cs arr group hk y]
  rfl

theorem missAt_eq (k : Nat) (A : ReqArray) (y : OnBytes.OracleShape × (Nat × Nat)) :
    missB cs y.1 A = missAtV (arrV num k A) (pmemP cs arr group y) := by
  unfold missB missAtV arrV blockMiss
  dsimp only
  rw [List.all_map]
  rfl

theorem miss_eq (iXI : Nat) (nas : Nat → Nat) (NHf : Nat) {k : Nat} (hk : k < 25) (ko : Nat)
    (A : ReqArray) :
    copiesMissP cs arr group mems k (num ko A.message) A =
      missV (padsViewOf cs layout labs num arr group mems iXI nas NHf) k (arrV num ko A) := by
  unfold copiesMissP missV padsViewOf
  dsimp only
  rw [List.all_map]
  refine congrArg (fun f => mems.all f) (funext fun y => ?_)
  show _ = (!((pmemP cs arr group y).segs.contains k && _) || _)
  rw [segs_mem cs arr group hk y, ← missAt_eq cs num arr group ko A y]
  rfl

theorem pairs_lt {iXI : Nat} {nas : Nat → Nat} {NHf : Nat} {x : Nat × Nat × Nat}
    (hx : x ∈ pairsOf iXI nas NHf) : x.1 < 25 ∧ x.2.1 < 25 := by
  unfold pairsOf at hx
  rcases List.mem_append.1 hx with h | h
  · obtain ⟨g, hg, h⟩ := List.mem_flatMap.1 h
    have hg' := List.mem_range.1 hg
    rcases List.mem_append.1 h with h | h
    · cases e : (g == 0)
      · rw [e] at h
        obtain rfl := List.mem_singleton.1 h
        exact ⟨by show 2 * g < 25; omega, by show 2 * (g - 1) < 25; omega⟩
      · rw [e] at h
        cases h
    · obtain rfl := List.mem_singleton.1 h
      exact ⟨by show 2 * g + 1 < 25; omega, by show 2 * g < 25; omega⟩
  · obtain rfl := List.mem_singleton.1 h
    exact ⟨by show 24 < 25; decide, by show 22 < 25; decide⟩

/-- **The light test is a function of the view.** -/
theorem padsDoor_eq (iXI : Nat) (nas : Nat → Nat) (NHf : Nat) :
    padsDoor cs layout labs num arr group mems iXI nas NHf =
      padsV (padsViewOf cs layout labs num arr group mems iXI nas NHf) := by
  rw [padsDoor_pairs]
  unfold padsV
  have hp : (padsViewOf cs layout labs num arr group mems iXI nas NHf).pairs =
      (pairsOf iXI nas NHf).map fun x =>
        (x.1, x.2.1,
          (VerifiableInference.Desc.arrayOf layout (ownerP (labs x.1 x.2.2)).1
            (ownerP (labs x.1 x.2.2)).2).map (arrV num (ownerP (labs x.1 x.2.2)).1)) := rfl
  rw [hp, List.all_map]
  have E : ∀ x ∈ pairsOf iXI nas NHf,
      padFreeP cs layout labs num arr group mems x.1 x.2.1 x.2.2 =
        pairV (padsViewOf cs layout labs num arr group mems iXI nas NHf)
          (x.1, x.2.1,
            (VerifiableInference.Desc.arrayOf layout (ownerP (labs x.1 x.2.2)).1
              (ownerP (labs x.1 x.2.2)).2).map (arrV num (ownerP (labs x.1 x.2.2)).1)) := by
    intro x hx
    obtain ⟨h1, h2⟩ := pairs_lt hx
    unfold padFreeP pairV
    dsimp only
    cases VerifiableInference.Desc.arrayOf layout (ownerP (labs x.1 x.2.2)).1
        (ownerP (labs x.1 x.2.2)).2 with
    | none => rfl
    | some A =>
      show (copyThereP _ _ _ _ _ && copyThereP _ _ _ _ _ && copiesMissP _ _ _ _ _ _ _ &&
        copiesMissP _ _ _ _ _ _ _) = _
      rw [there_eq cs layout labs num arr group mems iXI nas NHf h1,
        there_eq cs layout labs num arr group mems iXI nas NHf h2,
        miss_eq cs layout labs num arr group mems iXI nas NHf h1,
        miss_eq cs layout labs num arr group mems iXI nas NHf h2]
      rfl
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun k x hx => (E x hx).symm.trans (k x hx), fun k x hx => (E x hx).trans (k x hx)⟩

end

end VerifiableInference.Desc.Kinds.Head.Law.OffPad

#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.padsDoor_eq
