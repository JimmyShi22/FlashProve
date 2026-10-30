-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/OpenedStart.lean: `TieAt` (Honest/Law/Rule/OpenedStep.lean)
at a chain's start: in a chain that is handed no earlier chain's columns (`TieAt.start`), and in the
second chain, which is handed those of the first and the shared chain (`TieAt.start₃`). General in
the `Before`. With the challenges that three chains' rounds as shown hold (`drawnOf_laid`).

  1  `HeldAt.nil`, `TieAt.start`   nothing read so far
  2  `TieAt.start₃`   the two earlier chains' reads
  3  `drawnOf_laid`   the challenges in `laidOf` (Honest/Law/Rule/Words.lean), in the cut for the
     second chain, chain by chain

Limits.
  * `TieAt.start₃` takes as hypotheses that the `Before` holds the two earlier chains' columns for
    their declared rounds' reads. They are paid in Honest/Law/Rule/OpenedFile.lean (`held_two`,
    `tie_second`), not here.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.OpenedStep
import Johnson.Desc.ProofFile.Honest.Law.Rule.Words

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription OpenedColumn)

variable {Xi W Y : Type}

/-! ## 1 Nothing read so far -/

theorem HeldAt.nil (ch ft : Nat) (f : Before) : HeldAt ([] ++ [(ch, ft, [])]) f [] := by
  have e : readsBefore ([] ++ [(ch, ft, [])]) f = [] := by
    unfold readsBefore
    simp [readsOf]
  unfold HeldAt
  rw [e, Before.opened_eq]
  rfl

/-- **At the start of a chain that is handed no earlier chain's columns.** `hm`: the state's field
is `some []`, as `ChainProgress.start` (Honest/Walk.lean) lays it. `hf`: nothing of the chain has been
produced. -/
theorem TieAt.start {ch ft : Nat} {mid : Option (Mid W Y)} {f : Before}
    (hm : ∀ m, mid = some m → m.opened = some []) (hf : f.drawnOf ch = []) :
    TieAt [] ch ft [] mid f where
  held := fun m e => ⟨[], hm m e, HeldAt.nil ch ft f⟩
  early := fun x hx => by cases hx
  level := by simp [hf]

/-! ## 2 The second chain -/

/-- **At the start of the second chain.** `d₁`, `d₂`: the declared rounds of the first and the
shared chain. `c₁`, `c₂`: the columns that they have read. -/
theorem TieAt.start₃ {ft : Nat} {d₁ d₂ : List Fmt.DeclaredRound} {mid : Option (Mid W Y)} {f : Before}
    {c₁ c₂ : List OpenedColumn} (hm : ∀ m, mid = some m → m.opened = some (c₁ ++ c₂))
    (h₁ : colsOff f (readsOf 0 0 (fun _ _ => none) (fun _ => none) d₁ (f.drawnOf 0)) = some c₁)
    (h₂ : colsOff f (readsOf 1 0 (fun _ _ => none) (fun _ => none) d₂ (f.drawnOf 1)) = some c₂)
    (l₁ : d₁.length ≤ (f.drawnOf 0).length) (l₂ : d₂.length ≤ (f.drawnOf 1).length)
    (l₃ : f.drawnOf 2 = []) :
    TieAt [(0, 0, d₁), (1, 0, d₂)] 2 ft [] mid f where
  held := by
    intro m e
    refine ⟨c₁ ++ c₂, hm m e, ?_⟩
    have er : readsBefore ([(0, 0, d₁), (1, 0, d₂)] ++ [(2, ft, [])]) f =
        readsOf 0 0 (fun _ _ => none) (fun _ => none) d₁ (f.drawnOf 0) ++
          readsOf 1 0 (fun _ _ => none) (fun _ => none) d₂ (f.drawnOf 1) := by
      unfold readsBefore
      simp [readsOf]
    unfold HeldAt
    rw [er, Before.opened_eq, colsOff_append, h₁, h₂]
    rfl
  early := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact l₁
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact l₂
      · cases hx
  level := by simp [l₃]

/-! ## 3 The challenges in what three chains' rounds show -/

theorem drawnOf_laid (F : FileDescription Xi) (ρ : Draws) (l₀ l₁ l₂ : List Played)
    (st : List (Nat × Nat × List UInt64)) (c : Nat) (hc : c ≤ 2) :
    ((laidOf F ρ l₀ l₁ l₂).front 2 st).drawnOf c = (pick3 l₀ l₁ l₂ c).map (·.drawn) := by
  have h0 : ∀ (t : Nat → List Nat) (l : List Played),
      (shownBy c t l 0).map (·.2.2) = l.map (·.drawn) := by
    intro t l
    rw [shownBy_pairs, List.map_map]
    exact pairs_drawn t l 0
  show (((shownBy 0 (treeAsks F ρ 0) l₀ 0 ++ shownBy 1 (treeAsks F ρ 1) l₁ 0 ++
    shownBy 2 (treeAsks F ρ 2) l₂ 0).filter fun r => r.1 == c).map (·.2.2)) = _
  rw [List.filter_append, List.filter_append]
  have hc3 : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  rcases hc3 with rfl | rfl | rfl
  · rw [filter_same, filter_other (ch := 1) (c := 0) (by decide),
      filter_other (ch := 2) (c := 0) (by decide), List.append_nil, List.append_nil]
    exact h0 _ _
  · rw [filter_other (ch := 0) (c := 1) (by decide), filter_same,
      filter_other (ch := 2) (c := 1) (by decide), List.nil_append, List.append_nil]
    exact h0 _ _
  · rw [filter_other (ch := 0) (c := 2) (by decide), filter_other (ch := 1) (c := 2) (by decide),
      filter_same, List.nil_append, List.nil_append]
    exact h0 _ _

end ProofFile.Honest

#print axioms ProofFile.Honest.HeldAt.nil
#print axioms ProofFile.Honest.TieAt.start
#print axioms ProofFile.Honest.TieAt.start₃
#print axioms ProofFile.Honest.drawnOf_laid
