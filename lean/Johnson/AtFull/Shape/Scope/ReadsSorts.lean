-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/ReadsSorts.lean: THE READS' CELLS OF THE TABLE GO ALIKE AT TWO PUBLIC RECORDS THAT MEET SameRead
(Scope/Rel.lean): at the head's link the first half is one function; at the attention links it goes alike under RelX. (The even links: LayerSorts.lean.)

Limits. Laws on terms; nothing is evaluated; nothing says that a step returns. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.PlainCells
import Johnson.AtFull.Shape.Scope.Join
import Johnson.AtFull.Shape.ReadsHeadAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model OnBytes.Model.Head
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.K8.ReadsQuiet (PH)

variable {X X₀ : Verify.Public}

/-- The quiet step at the head's link reads none of the six numbers. -/
theorem headReadsG_flat (p : VerifiableInference.Desc.Place) (h : Head.Shape) (L : HL) (hp : HPlanH2)
    (a : ChainSh) :
    VerifiableInference.Desc.K8.ReadsQuiet.headReadsG ⟨p, h, L, hp⟩ a =
      VerifiableInference.Desc.K8.ReadsQuiet.headReadsG ⟨p, flatH h, L, hp⟩ a := rfl

/-- **At the head's link the reads' first half is one function at the two records.** -/
theorem reads_head_first (S : SameRead X X₀) :
    (TabL.readsHead (LW X)).1 = (TabL.readsHead (LW X₀)).1 := by
  unfold TabL.readsHead
  rw [nums_same S 24]
  cases (LW X₀).nums 24 with
  | none => rfl
  | some q =>
    obtain ⟨_, _, rd, _⟩ := q
    have e : ∀ a : ChainSh, readsHeadGS ((LW X).k1 24 5 1) rd
          ⟨⟨1, some 24, 5, .K1⟩, (LW X).XG.hS, (LW X).XG.HLy, (LW X).XG.H⟩ a =
        readsHeadGS ((LW X₀).k1 24 5 1) rd
          ⟨⟨1, some 24, 5, .K1⟩, (LW X₀).XG.hS, (LW X₀).XG.HLy, (LW X₀).XG.H⟩ a := by
      intro a
      have eH : (LW X).XG.H = (LW X₀).XG.H := S.H
      have eL : (LW X).XG.HLy = (LW X₀).XG.HLy := S.HLy
      have eS : flatH (LW X).XG.hS = flatH (LW X₀).XG.hS := S.hS
      unfold readsHeadGS
      rw [eH, eL]
      have e2 : ∀ m, VerifiableInference.Desc.K8.ReadsQuiet.headReadsG
            ⟨⟨1, some 24, 5, .K1⟩, (LW X).XG.hS, (LW X₀).XG.HLy, (LW X₀).XG.H⟩ m =
          VerifiableInference.Desc.K8.ReadsQuiet.headReadsG
            ⟨⟨1, some 24, 5, .K1⟩, (LW X₀).XG.hS, (LW X₀).XG.HLy, (LW X₀).XG.H⟩ m := by
        intro m
        refine (headReadsG_flat _ _ _ _ m).trans ?_
        refine Eq.trans ?_ (headReadsG_flat _ _ _ _ m).symm
        rw [eS]
      simp only [e2]
      rfl
    show readsA _ _ = readsA _ _
    funext y
    unfold readsA
    rw [e y.1]
    rfl

/-- **The reads at the head's link.** -/
theorem reads_head_rel (S : SameRead X X₀) :
    CellRel X X₀ (337 + 5) ((TabL.headRow (LW X)).at 5) ((TabL.headRow (LW X₀)).at 5) :=
  cellRel_of_eq (by decide) (reads_head_first S)

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.reads_head_first
#print axioms Johnson.AtFull.Shape.Scope.reads_head_rel
