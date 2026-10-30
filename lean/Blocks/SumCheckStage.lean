-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/SumCheckStage.lean: the masked sumcheck as a stage, and a form of its start claim.

Blocks/SumCheckBlock.lean proves, each under its hypotheses, soundness, completeness and masked form
of the masked sumcheck.
Here they are combined in one stage (Blocks/Stage.lean), for a sumcheck with `nzv` false everywhere
(no later block divides by a challenge), so that the withheld set (`Hon.withheld`,
Blocks/BlockHon.lean) is empty: `SC.Prover.stage`; `SC.Prover.props_stage`, under its hypotheses.
The stage sends no vector. `sumOutL_plainW_lkVars` writes the start claim of a sumcheck with plain
weights for a function of the first g coordinates of a point indexed by ℕ: the sum of its values on
the hypercube.
-/
import Blocks.StageLib
import Blocks.ProductBlock
import Blocks.LookupRel
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks

open Iop Prob Alg

/-- The start claim of a plain sumcheck, for a function Φ of the first g coordinates: summing Φ out
over the g variables gives the sum of the values of Φ on the hypercube. -/
theorem sumOutL_plainW_lkVars {E : Type} [Field E] (g : ℕ) (z : ℕ → E) (Φ : (ℕ → E) → E)
    (hΦ : ∀ w w' : ℕ → E, (∀ t < g, w t = w' t) → Φ w = Φ w') :
    sumOutL plainW (lkVars g) Φ z = ∑ X ∈ Finset.range (2 ^ g), Φ (cubePt g X) := by
  have hfun : Φ = fun y : ℕ → E => (fun v : Fin g → E => Φ (nat v)) fun t : Fin g => y t := by
    funext y
    exact hΦ _ _ fun t ht => by simp [nat, ht]
  have h1 := sumOutL_comp (fun t : Fin g => (t : ℕ)) Fin.val_injective (plainW (K := E))
    (fun v : Fin g → E => Φ (nat v)) (List.finRange g) z
  have h2 := sumOutL_plain (List.finRange g) (List.nodup_finRange g) (List.mem_finRange)
    (fun v : Fin g → E => Φ (nat v)) (fun t : Fin g => z t)
  have e : sumOutL plainW (lkVars g) Φ z = ∑ b : Fin g → Bool, Φ (nat (corner b : Fin g → E)) := by
    unfold lkVars
    conv_lhs => rw [hfun]
    exact h1.trans h2
  rw [e, ← sum_num fun c => Φ (cubePt g c)]
  simp only [cubePt, bits_num]

theorem nodup_lkVars (g : ℕ) : (lkVars g).Nodup := (List.nodup_finRange g).map Fin.val_injective

namespace SC

variable {E Y P Ξ ι A : Type}
  [Field E] [Fintype E] [DecidableEq E] [DecidableEq ι] {S : SC E Y P Ξ ι} (H : S.Prover A)

namespace Prover

/-- The first part of the honest state does not change. -/
theorem next_fst :
    ∀ (l l' : List ι) (s : A × (ι → E)) (ρ : Rho (S.sc l).shape), ((H.sc l l').next s ρ).1 = s.1
  | [], _, _, _ => rfl
  | _ :: l, l', _, _ => next_fst l l' _ _

/-- Under `hnz`, the public part of the withheld set is empty. -/
theorem bad_sc (hnz : ∀ i, S.nzv i = false) : ∀ l l' : List ι, (H.sc l l').Bad = ∅
  | [], _ => rfl
  | i :: l, l' => by
      refine Set.eq_empty_of_forall_notMem fun ρ hρ => ?_
      rcases hρ with h | h
      · have h1 : S.nzv i = true ∧ (Rho.fst (s := (S.round i).shape) ρ).1 = 0 := h
        rw [hnz i] at h1
        exact absurd h1.1 (by simp)
      · have h1 : Rho.snd (s := (S.round i).shape) ρ ∈ (H.sc l l').Bad := h
        rw [bad_sc hnz l l'] at h1
        exact h1

/-- Its `Win` is empty: nothing else is withheld. -/
theorem win_sc : ∀ (l l' : List ι) (s : A × (ι → E)), (H.sc l l').Win s = ∅
  | [], _, _ => rfl
  | i :: l, l', s => by
      refine Set.eq_empty_of_forall_notMem fun ρ hρ => ?_
      rcases hρ with h | h
      · exact h
      · have h1 : Rho.snd (s := (S.round i).shape) ρ ∈
            (H.sc l l').Win ((H.round i (l ++ l')).next s (Rho.fst ρ)) := h
        rw [win_sc l l'] at h1
        exact h1

/-- The protocol of the masked sumcheck that binds the variables of l. -/
def core (l : List ι) : Core P E ⟨S.X, Y, A × (ι → E)⟩ ⟨S.X, Y, A × (ι → E)⟩ where
  B := S.sc l
  H := H.sc l []

variable [Fintype P] [DecidableEq P]

/-- The masked sumcheck that binds the variables of l, as a stage. -/
def stage (l : List ι) : Stage P E ⟨S.X, Y, A × (ι → E)⟩ ⟨S.X, Y, A × (ι → E)⟩ where
  toCore := H.core l
  ε := S.scErr l
  U := S.padsOf l
  D := S.padsOf l
  Sim := S.simSc l
  pBad := 0
  pWin := 0

/-- `Stage.Props` of `stage`, from the start claim to the end claim, under the hypotheses below.
hnode is used for completeness only: the honest prover finds a round's scalars from the round
polynomial's values at 0, 1, .., e i + 1, which have to be different in E. -/
theorem props_stage {Φ : Ξ → Y → (ι → E) → E} (h : S.OK Φ)
    (hnode : ∀ i, Function.Injective (node (S.e i) : Fin (S.e i + 2) → E))
    (hnz : ∀ i, S.nzv i = false) {l : List ι} (hp : S.PlacesOnceOn l)
    (hl : l.Nodup) {Link : A → (P → E) → Ξ → Y → Prop}
    (hLink : ∀ a π ξ y,
      Link a π ξ y → S.wt ξ = H.wt a ∧ ∀ p ∈ S.padsOf l, S.forms.val y (S.forms.pad p) = π p)
    (V : A → Prop) :
    (H.stage l).Props ⟨S.Rsum Φ l, H.Hsum Link l, fun s => V s.1⟩
      ⟨S.Reval Φ, H.Hsum Link [], fun s => V s.1⟩ := by
  have hacc := H.accOn_sc h.forms hnode l [] hLink
  rw [List.append_nil] at hacc
  exact Stage.Props.of_empty
    (S := H.stage l) (S.clean_sc_eval h l) hacc (H.masked_sc_on V l [] hp hl)
    (fun s ρ hs => by
      show V ((H.sc l []).next s ρ).1
      rw [next_fst]
      exact hs)
    (H.bad_sc hnz l []) (H.win_sc l [])

end Prover

variable {F : Type} [Field F] [Algebra F E]

/-- The encoding data of the rounds: they have no vectors. -/
def encSc (S : SC E Y P Ξ ι) (F : Type) [Field F] [Algebra F E] :
    (l : List ι) → EncData F E (S.sc l).shape
  | [] => PUnit.unit
  | i :: l => (REnc.none E F (Fin (S.e i + 1)) E, encSc S F l)

variable [Fintype P] [DecidableEq P]

/-- The stage exposes the same entries as its input. -/
def Prover.track (l : List ι) (ra : Reads F E ⟨S.X, Y, A × (ι → E)⟩) : (H.core l).Track ra ra where
  d := encSc S F l
  src := fun n => .inl n

theorem Prover.track_ok (l : List ι) (ra : Reads F E ⟨S.X, Y, A × (ι → E)⟩) : (H.track l ra).OK :=
  ⟨fun y τ n => by
      show ra.rd ((S.sc l).imp y τ) n = ra.rd y n
      rw [S.imp_sc],
    fun y τ => by
      show ra.mat ((S.sc l).imp y τ) = ra.mat y
      rw [S.imp_sc]⟩

end SC

end Blocks
