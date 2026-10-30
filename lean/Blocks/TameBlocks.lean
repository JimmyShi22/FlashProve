-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/TameBlocks.lean: whether the verifiers of the masked sumcheck, the product layer, the batched
sumcheck and the closing block reject depends on their own randomness only, for the explicit parts
named below.

The notion: `Core.Tame` (Blocks/Tame.lean).
 * `Ledger.len`: the numbers of LIN, opened forms and REL in the list of deferred claims (`Ledger`,
   Blocks/Form.lean). `Ledger.Ord n x`: the list x is well-formed (`Ledger.wf`: every term of a REL
   names an opened form in the list) and has the lengths n. It is preserved, at the new lengths, by
   these operations on a list: `Ord.addLin`, `addLins`, `addProd`, `addProds`, `addRel` (under hts),
   `append` (of two lists with `Ord`), `push`; the empty list has it (`ord_empty`).
 * `SC.Prover.tame_core`: a masked sumcheck preserves every property of its public data. It rejects
   exactly if the challenge of a flagged variable (`SC.nzv`) is 0.
 * `PL.Prover.tame_core`: a product layer: a well-formed list stays well-formed and gains two opened
   forms and one REL. So its check of the list never rejects such a list.
 * `SCB.Prover.tame_core`: a batched sumcheck: the same, with 2 nb opened forms and one REL.
 * `Closing.tame_core`: the closing block accepts every list of the lengths for which it is made. So
   its check of the lengths never rejects such a list.
-/
import Blocks.Tame
import Blocks.SumCheckStage
import Blocks.StageBatched
import Blocks.ProductStage
import Blocks.ClosingStage
import Blocks.HLedProds
import Blocks.SemClaims

set_option autoImplicit false

namespace Blocks

open Iop Prob Alg

namespace Ledger

variable {N E : Type}

/-- the numbers of LIN, opened forms and REL -/
def len (x : Ledger N E) : ℕ × ℕ × ℕ := (x.lin.length, x.opn.length, x.rel.length)

/-- The list is well-formed and has the lengths n. -/
def Ord (n : ℕ × ℕ × ℕ) (x : Ledger N E) : Prop := x.wf = true ∧ x.len = n

theorem ord_empty : (empty : Ledger N E).Ord (0, 0, 0) := ⟨rfl, rfl⟩

variable {n : ℕ × ℕ × ℕ} {x : Ledger N E}

theorem Ord.addLin (h : x.Ord n) (f : Form N E) : (x.addLin f).Ord (n.1 + 1, n.2.1, n.2.2) := by
  obtain ⟨hw, rfl⟩ := h
  exact ⟨hw, by simp [len, Ledger.addLin]⟩

theorem Ord.addLins (h : x.Ord n) (fs : List (Form N E)) :
    (x.addLins fs).Ord (n.1 + fs.length, n.2.1, n.2.2) := by
  obtain ⟨hw, rfl⟩ := h
  exact ⟨hw, by simp [len, Ledger.addLins]⟩

theorem Ord.addProd [One E] (h : x.Ord n) (f a b : Form N E) :
    (x.addProd f a b).Ord (n.1, n.2.1 + 2, n.2.2 + 1) := by
  obtain ⟨hw, rfl⟩ := h
  exact ⟨wf_addProd hw f a b, by simp [len, Ledger.addProd]⟩

theorem Ord.addProds [One E] :
    ∀ (ps : List (Form N E × Form N E × Form N E)) {n : ℕ × ℕ × ℕ} {x : Ledger N E},
      x.Ord n → (x.addProds ps).Ord (n.1, n.2.1 + 2 * ps.length, n.2.2 + ps.length)
  | [], _, _, h => h
  | p :: ps, n, x, h => by
      have h1 := Ord.addProds ps (h.addProd p.1 p.2.1 p.2.2)
      have e : ((n.1, n.2.1 + 2 + 2 * ps.length, n.2.2 + 1 + ps.length) : ℕ × ℕ × ℕ) =
          (n.1, n.2.1 + 2 * (p :: ps).length, n.2.2 + (p :: ps).length) := by
        rw [List.length_cons]
        refine Prod.ext rfl (Prod.ext ?_ ?_)
        · show n.2.1 + 2 + 2 * ps.length = n.2.1 + 2 * (ps.length + 1)
          omega
        · show n.2.2 + 1 + ps.length = n.2.2 + (ps.length + 1)
          omega
      rw [← e]
      exact h1

theorem Ord.addRel (h : x.Ord n) (f : Form N E) {os : List (Form N E)} {ts : List (E × ℕ × ℕ)}
    (hts : ∀ t ∈ ts, t.2.1 < os.length ∧ t.2.2 < os.length) :
    (x.addRel f os ts).Ord (n.1, n.2.1 + os.length, n.2.2 + 1) := by
  obtain ⟨hw, rfl⟩ := h
  exact ⟨wf_addRel hw f hts, by simp [len, Ledger.addRel]⟩

theorem Ord.append {n' : ℕ × ℕ × ℕ} {x' : Ledger N E} (h : x.Ord n) (h' : x'.Ord n') :
    (x.append x').Ord (n.1 + n'.1, n.2.1 + n'.2.1, n.2.2 + n'.2.2) := by
  obtain ⟨hw, rfl⟩ := h
  obtain ⟨hw', rfl⟩ := h'
  exact ⟨wf_append hw hw', by simp [len, Ledger.append]⟩

theorem Ord.push [Fintype N] [CommRing E] {N' : Type} [DecidableEq N'] (h : x.Ord n) (σ : N → N') :
    (x.push σ).Ord n := by
  obtain ⟨hw, rfl⟩ := h
  exact ⟨(wf_push σ x).trans hw, by simp [len, Ledger.push]⟩

end Ledger

namespace SC

variable {E Y P Ξ ι : Type} [Field E] [Fintype E] [DecidableEq E] [DecidableEq ι] (S : SC E Y P Ξ ι)

/-- One round preserves every property of the public data. -/
theorem tame_round (i : ι) (J : Ξ → Prop) :
    (S.round i).Tame {ρ | ρ.1 ∈ {r : E | S.nzv i = true ∧ r = 0}}
      (fun x => J x.2.2) fun x => J x.2.2 :=
  Block.Tame.one _ (fun _ _ _ hx hc => ⟨_, if_neg hc, hx⟩) fun _ _ _ hc => if_pos hc

end SC

namespace SC.Prover

variable {E Y P Ξ ι A : Type}
  [Field E] [Fintype E] [DecidableEq E] [DecidableEq ι] {S : SC E Y P Ξ ι} (H : S.Prover A)

theorem tame_sc (J : Ξ → Prop) :
    ∀ l l' : List ι, (S.sc l).Tame (H.sc l l').Bad (fun x => J x.2.2) fun x => J x.2.2
  | [], _ => Block.Tame.pure _ fun x hx => ⟨x, rfl, hx⟩
  | i :: l, l' => Block.Tame.seq (S.tame_round i J) (tame_sc J l l')

/-- The masked sumcheck preserves every property of its public data, and rejects exactly on its
public set `Bad`. -/
theorem tame_core (J : Ξ → Prop) (l : List ι) :
    (H.core l).Tame (fun x => J x.2.2) fun x => J x.2.2 := H.tame_sc J l []

end SC.Prover

namespace PL.Prover

variable {E Y P N Ξ A : Type} [Field E] [NeZero (2 : E)] [Fintype E] [DecidableEq E] [Fintype N]
  [DecidableEq N] {L : PL E Y P N Ξ} (H : L.Prover A)

omit [NeZero (2 : E)] in
theorem tame_fin (n : ℕ × ℕ × ℕ) :
    L.fin.Tame {ρ | ρ.1 ∈ {ζ : E | L.okE ζ = false}} (fun x => x.2.2.2.1.Ord n)
      fun xo => xo.1.led.Ord (n.1, n.2.1 + 2, n.2.2 + 1) :=
  Block.Tame.one _
    (fun x ζ s hx hζ => ⟨L.out x ζ s, if_pos (by
        have h1 : L.okE ζ = true := by
          cases hc : L.okE ζ
          · exact absurd hc hζ
          · rfl
        rw [h1, hx.1]
        rfl), hx.addProd _ _ _⟩)
    fun x ζ s hζ => if_neg (by
      rw [show L.okE ζ = false from hζ]
      exact Bool.false_ne_true)

omit [NeZero (2 : E)] in
/-- The product layer: a well-formed list stays well-formed, and gains two opened forms and one REL;
for a well-formed list the verifier rejects exactly on the public set `Bad`. -/
theorem tame_core (n : ℕ × ℕ × ℕ) :
    H.core.Tame (fun x => x.led.Ord n) fun xo => xo.1.led.Ord (n.1, n.2.1 + 2, n.2.2 + 1) :=
  Block.Tame.seq (Block.Tame.pure _
      (Ib := fun x : L.sc.X => x.2.2.2.1.Ord n) fun _ hx => ⟨_, rfl, hx⟩)
    (Block.Tame.seq (H.scP.tame_sc (fun ξ => ξ.2.1.Ord n) _ _) (tame_fin n))

end PL.Prover

namespace SCB.Prover

variable {E Y P N Ξ ι A : Type} [Field E] [Fintype E] [DecidableEq E] [DecidableEq ι] [Fintype N]
  [DecidableEq N] {B : SCB E Y P N Ξ ι} (H : B.Prover A)

/-- The batched sumcheck: a well-formed list stays well-formed, and gains 2 nb opened forms and one
REL; the caller's explicit part is passed on unchanged. For a well-formed list (with J) the verifier
rejects exactly on its public set `Bad`. -/
theorem tame_core (n : ℕ × ℕ × ℕ) (J : Ξ → Prop) (l : List ι) :
    (H.core l).Tame (fun x => (B.led x.2.2).Ord n ∧ J x.2.2) fun xo =>
      xo.1.2.Ord (n.1, n.2.1 + 2 * B.nb, n.2.2 + 1) ∧ J xo.1.1 :=
  Core.Tame.seq (H.pr.tame_core (fun ξ => (B.led ξ).Ord n ∧ J ξ) l)
    (Core.Tame.seq
      (Core.tame_nameScalars H.t0 B.idxE H.endVal
        (Ib := fun x : B.sc.X × (Fin B.nb × Bool → E) => (B.led x.1.2.2).Ord n ∧ J x.1.2.2)
        fun _ _ hx => hx)
      (Core.tame_pure _ _ fun x hx => ⟨_, if_pos hx.1.1, by
        have h1 := hx.1.addRel x.1.1 (B.ts_lt (fun b => B.W x.1.2.2 b x.1.2.1) x.2)
        rw [B.length_os] at h1
        exact h1, hx.2⟩))

end SCB.Prover

namespace Closing

variable {N E P : Type} [Fintype N] [DecidableEq N] [Field E] [Fintype E] [DecidableEq E]
  {nO nR : ℕ} (nL : ℕ) (pl : Places N (Fin nR) nO) (pp : Places P (Fin nR) nO)

omit [Fintype N] [DecidableEq E] in
/-- The closing block accepts every list of the lengths for which it is made, whatever the prover
sends and whatever its own randomness is. -/
theorem tame_core : (core (E := E) nL pl pp).Tame (fun x => x.len = (nL, nO, nR)) fun _ => True :=
  Block.Tame.seq (Block.Tame.pure _ (Ib := fun _ => True) fun _ hx =>
      ⟨_, if_pos ⟨congrArg Prod.fst hx, congrArg (fun t => t.2.1) hx, congrArg (fun t => t.2.2) hx⟩,
        trivial⟩)
    (Block.Tame.seq
      (Block.Tame.one _ (Bd := ∅) (Ib := fun _ => True)
        (fun _ _ _ _ _ => ⟨_, rfl, trivial⟩) fun _ _ _ h => h.elim)
      (Block.Tame.one _ (Bd := ∅) (fun _ _ _ _ _ => ⟨_, rfl, trivial⟩) fun _ _ _ h => h.elim))

end Closing

end Blocks
