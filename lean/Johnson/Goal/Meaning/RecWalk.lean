-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/RecWalk.lean: RecAll (Johnson/Goal/Meaning/RecAll.lean) at every record that
the fold over a chain's blocks passes through, from the first chain's first record: the general
half.

No kind and no description is named: the blocks are a letter.
  recAll_fold: a fold over blocks that are all Decides (RecRel cs sh), from a record with RecAll,
    returns a record with RecAll (the library's foldBlocks_keeps, Johnson/Desc/FoldKeeps.lean).
  recAll_from_start, recAll_from_startReq: so from what S.startP | S.startReqP returns
    (Johnson/Desc/First/StartPlain.lean), with the codes and the shape that it was handed.
  recAll_border: where a fold over l₁ ++ l₂ returns: the record at the border has RecAll, IF THE
    BLOCKS OF l₁ ARE Decides (RecRel cs sh): nothing is asked of l₂.
Not claimed: that any block is Decides (RecRel cs sh).
-/
import Johnson.Goal.Meaning.RecRel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Decides)

variable {cs : Codes} {sh : ReqShape} {Cl : Type}

/-- The columns that a fold is handed (two types bear the name Col where this file stands). -/
abbrev Cols : Type := List VerifiableInference.Desc.OpenedColumn

theorem recAll_fold {ft : Nat} {bs : List (Block S Cl)}
    (hb : ∀ b ∈ bs, Decides (RecRel cs sh) b) {s : S} {rs : List Fmt.RoundView} {cols : Cols}
    {r : S × List Fmt.RoundView × Cols} (h : foldBlocks ft bs s rs cols = .ok r)
    (R : RecAll cs sh s) : RecAll cs sh r.1 :=
  Keeps.foldBlocks_keeps (RecRel cs sh) (recRel_refl cs sh) (recRel_trans cs sh) ft bs hb s rs cols
    r h R

theorem recAll_from_start {P : First.Par} {layout : ReqLayout} {s₀ : S}
    (h0 : S.startP P cs sh layout = some s₀) {ft : Nat} {bs : List (Block S Cl)}
    (hb : ∀ b ∈ bs, Decides (RecRel cs sh) b) {rs : List Fmt.RoundView} {cols : Cols}
    {r : S × List Fmt.RoundView × Cols} (h : foldBlocks ft bs s₀ rs cols = .ok r) :
    RecAll cs sh r.1 :=
  recAll_fold hb h (recAll_first h0)

theorem recAll_firstReq {P : First.Par} {layout : ReqLayout} {T V : Nat} {req : Array UInt32}
    {s₀ : S} (h0 : S.startReqP P cs sh layout T V req = some s₀) : RecAll cs sh s₀ := by
  unfold S.startReqP at h0
  obtain ⟨s, hs, h1⟩ := Option.bind_eq_some_iff.1 h0
  split at h1
  · cases h1
    exact recAll_withReq (recAll_first hs) req
  · cases h1

theorem recAll_from_startReq {P : First.Par} {layout : ReqLayout} {T V : Nat}
    {req : Array UInt32} {s₀ : S} (h0 : S.startReqP P cs sh layout T V req = some s₀) {ft : Nat}
    {bs : List (Block S Cl)} (hb : ∀ b ∈ bs, Decides (RecRel cs sh) b) {rs : List Fmt.RoundView}
    {cols : Cols} {r : S × List Fmt.RoundView × Cols}
    (h : foldBlocks ft bs s₀ rs cols = .ok r) : RecAll cs sh r.1 :=
  recAll_fold hb h (recAll_firstReq h0)

/-- **At a border: nothing is asked of the blocks behind it.** -/
theorem recAll_border {ft : Nat} {l₁ l₂ : List (Block S Cl)}
    (hb : ∀ b ∈ l₁, Decides (RecRel cs sh) b) {s : S} {rs : List Fmt.RoundView} {cols : Cols}
    {r : S × List Fmt.RoundView × Cols} (h : foldBlocks ft (l₁ ++ l₂) s rs cols = .ok r)
    (R : RecAll cs sh s) :
    ∃ t rs' cols', foldBlocks ft l₁ s rs cols = .ok (t, rs', cols') ∧
      foldBlocks ft l₂ t rs' cols' = .ok r ∧ RecAll cs sh t := by
  obtain ⟨t, rs', cols', h1, h2⟩ := Keeps.foldBlocks_split ft l₂ l₁ s rs cols r h
  exact ⟨t, rs', cols', h1, h2, recAll_fold hb h1 R⟩

#print axioms recAll_from_startReq
#print axioms recAll_border

end Meaning.K2
