-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Tile.lean: the piece of the batching's joined block is owed just its stretch,
and its trees are listed: what a rule of composition asks of a piece beside its law (`Piece.Owed`,
`Piece.Listed`). Statements with their proofs.
Main names:
  `atM3_rounds`, `atM3_rounds_length`: the joined block's declared rounds are the batching's.
  `Bare d`: a written round opens no stored part and no tree, and sends no tree.
  `groupsOf_bare`, `wantsOf_bare`: such rounds read nothing.
  `pieceM3_owed`, `pieceM3_listed`.
Used of `verify-on-bytes`: nothing.

What is not claimed. That the written rounds of a real plan's stretch are `Bare`: a test on data: an
evaluation at two stored sets' public files, a small and a full-size one, said yes, and a control
said no; no theorem says it of a plan.

-/
import Johnson.Desc.K13.Law.Tries

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes Iop Run
open OnBytes.Maker
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame Piece)

variable {Cl W : Type}

/-- The joined block's declared rounds are the batching's. -/
theorem atM3_rounds (P : Where) : (atM3 (Cl := Cl) P).rounds = battRounds P := by
  simp [atM3, Block.andThen, frontB, quietB, still, claimCombinationBlock]

/-- They are 2 and one for each column variable. -/
theorem atM3_rounds_length (P : Where) : (atM3 (Cl := Cl) P).rounds.length = 2 + P.lin.kCol := by
  rw [atM3_rounds]
  simp [battRounds]
  omega

/-- A written round opens no stored part and no tree, and sends no tree. -/
def Bare (d : RDT) : Prop := d.stored = [] ∧ d.opens = [] ∧ d.trees = []

/-- Declared rounds that open nothing read no group. -/
theorem groupsOf_bare (ft : ℕ) : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    (∀ d ∈ ds, d.stored = [] ∧ d.opens = []) → groupsOf ft ds Rs = []
  | [], _, _ => by simp [groupsOf]
  | _ :: _, [], _ => by simp [groupsOf]
  | d :: ds, R :: Rs, h => by
    unfold groupsOf
    rw [(h d List.mem_cons_self).1, (h d List.mem_cons_self).2,
      groupsOf_bare ft ds Rs fun d' hd' => h d' (List.mem_cons_of_mem _ hd')]
    rfl

/-- Written rounds that open nothing ask for no leaf. -/
theorem wantsOf_bare (a : ℕ) (dep : ℕ → Option ℕ) : ∀ (ds : List RDT) (Rs : List Fmt.Drawn),
    (∀ d ∈ ds, Bare d) → wantsOf a dep ds Rs = []
  | [], _, _ => by simp [wantsOf]
  | _ :: _, [], _ => by simp [wantsOf]
  | d :: ds, R :: Rs, h => by
    unfold wantsOf
    rw [(h d List.mem_cons_self).1, (h d List.mem_cons_self).2.1,
      wantsOf_bare a dep ds Rs fun d' hd' => h d' (List.mem_cons_of_mem _ hd')]
    rfl

/-- **The block is owed just its stretch.** -/
theorem pieceM3_owed (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (hk : P.lin.kCol = ds.length) (hB : ∀ d ∈ dZ :: d0 :: ds, Bare d) :
    (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).Owed := by
  refine ⟨?_, fun y τ => ?_⟩
  · show (dZ :: d0 :: ds).length + ([] : List Fmt.RoundView).length = (atM3 (Cl := Cl) P).rounds.length
    rw [atM3_rounds_length, hk]
    simp
    omega
  · have h1 : ∀ Rs : List Fmt.Drawn, (atM3 (Cl := Cl) P).reads F.ft Rs = [] := by
      intro Rs
      unfold Block.reads
      rw [atM3_rounds]
      refine groupsOf_bare _ _ _ fun d hd => ?_
      simp only [battRounds, List.mem_cons, List.mem_replicate] at hd
      rcases hd with rfl | rfl | ⟨_, rfl⟩ <;> exact ⟨rfl, rfl⟩
    have h2 : (sView (ckP .two) (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).stage y τ).opened =
        [] := by
      show (List.filterMap _ (wantsOf _ _ (dZ :: d0 :: ds) _)) = []
      rw [wantsOf_bare _ _ _ _ hB]
      rfl
    show (List.flatMap id ((atM3 (Cl := Cl) P).reads F.ft _)).length = _
    rw [h1, h2]
    rfl

/-- **Its trees are listed**: it sends none and opens none. -/
theorem pieceM3_listed (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (hB : ∀ d ∈ dZ :: d0 :: ds, Bare d) :
    (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).Listed := by
  have hno : ∀ (l : List RDT), (∀ d ∈ l, Bare d) → ∀ n, treeShT l n = none := by
    intro l
    induction l with
    | nil => intro _ n; rfl
    | cons d l ih =>
      intro h n
      rw [treeShT_cons, (h d List.mem_cons_self).2.2]
      simpa using ih (fun d' hd' => h d' (List.mem_cons_of_mem _ hd')) n
  refine ⟨fun n sh h => ?_, fun d hd j hj => ?_⟩
  · have h' : treeShT (dZ :: d0 :: ds) n = some sh := h
    rw [hno _ hB n] at h'
    cases h'
  · have hd' : d ∈ dZ :: d0 :: ds := hd
    rw [(hB d hd').2.1] at hj
    cases hj

end VerifiableInference.Desc.K13.Law
