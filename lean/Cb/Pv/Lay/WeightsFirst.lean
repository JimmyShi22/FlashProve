-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/WeightsFirst.lean: the last stretch of the first layers' sub-proof's own rounds: as
Cb/Pv/Lay/Weights.lean, with one more value, which is sent in the round of the batching draw.

In the first group of layers one more claim on the committed weights is needed: the embedding's. It
comes from an identity between two forms in the entries,
    (sum over the corners x of the cube of fe (x)) = rhs:
on the left a sum over the weights, on the right a form in the cells of the stream that comes in.
The prover sends one scalar: the left side plus a mask entry of its own. That splits the identity
into
    (A) (the sum of fe) + m mkE = sent,      (B) sent - m mkE = rhs.
The row (B) rides on. In the same round the verifier draws one element; under its powers the n older
claims and (A), as the last, become one claim. Then comes the merge.

Main names:
  `WFirstL`: the parameters: those of Cb/Pv/Lay/Weights.lean, and fe, rhs, mkE.
  `WFirstL.Phi`: the n older claims and the identity. `WFirstL.B`: the row that rides on.
  `WFirstL.L`: the merge's parameters behind the round. `WFirstL.sg_iff`: what its input claim says.
  `WFirstL.cnt_bad`: if a claim or the identity fails, at most n draws make (B) and the combined
    claim true.
  `WFirstL.blk V`, `WFirstL.knowAt`, `WFirstL.know`, `WFirstL.errs`: the reduction; its knowledge
    soundness for each fixed tuple of messages, from "what rides, the n claims and the identity" to
    "what rides, the row (B), one row on names, the row on the end value"; its errors: n; 1; 2 for
    each column bit; 1; 0.

Limits: the fields `deg` and `dege` (each summand has degree at most 2 in each variable) are to be
paid by whoever fills the record. For the rest as in Cb/Pv/Lay/Weights.lean.

-/
import Cb.Pv.Lay.Weights

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Iop Prob Cb IOR Finset TWhole

noncomputable section

/-- The parameters of the stretch. -/
structure WFirstL (E : Type) [Field E] [Fintype E] extends WeightsL E where
  /-- the new claim's summand -/
  fe : St → (J → E) → (Fin k → E) → E
  dege : ∀ st m, Alg.DegLE (fun _ : Fin k => 2) (fe st m)
  /-- the other side of the identity -/
  rhs : St → (J → E) → E
  /-- the name of the sent scalar's mask entry -/
  mkE : J

variable {E : Type} [Field E] [Fintype E]

namespace WFirstL
variable (G : WFirstL E)

/-- the left side of the identity -/
def lhs (st : G.St) (m : G.J → E) : E := ∑ b : Fin G.k → Bool, G.fe st m (Alg.corner b)

/-- the older claims, and the identity -/
def Phi (st : G.St) (m : G.J → E) : Prop :=
  (∀ a, G.toWeightsL.val st m a = G.sh a st) ∧ G.lhs st m = G.rhs st m

/-- the states behind the round -/
abbrev St1 : Type := (G.St × (Unit → E)) × E

/-- the row that rides on -/
def B (x : G.St1) (m : G.J → E) : Prop := x.1.2 () - m G.mkE = G.rhs x.1.1 m

open Classical in
/-- the merge's parameters behind the round -/
@[reducible] def L : MergeL E where
  J := G.J
  k := G.k
  St := G.St1
  f := fun x m z => ∑ a : Fin G.n, x.2 ^ (a : ℕ) * G.fa a x.1.1 m z + x.2 ^ G.n * G.fe x.1.1 m z
  deg := fun x m => (Alg.DegLE.sum Finset.univ fun a _ => (G.deg a x.1.1 m).const_mul
      (x.2 ^ (a : ℕ))).add
    ((G.dege x.1.1 m).const_mul (x.2 ^ G.n))
  inc := fun x j => (∑ a : Fin G.n, if j = G.nm a then x.2 ^ (a : ℕ) * G.be a x.1.1 else 0) +
    if j = G.mkE then x.2 ^ G.n else 0
  tg := fun x => ∑ a : Fin G.n, x.2 ^ (a : ℕ) * G.sh a x.1.1 + x.2 ^ G.n * x.1.2 ()
  wAt := G.wAt
  cAt := G.cAt
  Rd := fun x m => G.Rd x.1.1 m ∧ G.B x m

theorem inc_sum (x : G.St1) (m : G.J → E) :
    ∑ j, G.L.inc x j * m j =
      ∑ a : Fin G.n, x.2 ^ (a : ℕ) * (m (G.nm a) * G.be a x.1.1) + x.2 ^ G.n * m G.mkE := by
  classical
  show ∑ j, ((∑ a : Fin G.n, if j = G.nm a then x.2 ^ (a : ℕ) * G.be a x.1.1 else 0) +
    if j = G.mkE then x.2 ^ G.n else 0) * m j = _
  simp only [add_mul, sum_add_distrib, sum_mul]
  congr 1
  · rw [sum_comm]
    refine sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single (G.nm a)]
    · rw [if_pos rfl]
      ring
    · intro j _ hj
      rw [if_neg hj, zero_mul]
    · intro h0
      exact absurd (Finset.mem_univ _) h0
  · rw [Finset.sum_eq_single G.mkE]
    · rw [if_pos rfl]
    · intro j _ hj
      rw [if_neg hj, zero_mul]
    · intro h0
      exact absurd (Finset.mem_univ _) h0

/-- What the merge's input claim says. -/
theorem sg_iff (x : G.St1) (m : G.J → E) :
    G.L.Sg x m ↔
      ∑ a : Fin G.n, x.2 ^ (a : ℕ) * (G.toWeightsL.val x.1.1 m a - G.sh a x.1.1) +
        x.2 ^ G.n * (G.lhs x.1.1 m + m G.mkE - x.1.2 ()) = 0 := by
  unfold MergeL.Sg
  rw [G.inc_sum]
  have h : ∑ b : Fin G.k → Bool, G.L.f x m (Alg.corner b) =
      ∑ a : Fin G.n, x.2 ^ (a : ℕ) * ∑ b : Fin G.k → Bool, G.fa a x.1.1 m (Alg.corner b) +
        x.2 ^ G.n * G.lhs x.1.1 m := by
    show ∑ b : Fin G.k → Bool, (∑ a : Fin G.n, x.2 ^ (a : ℕ) * G.fa a x.1.1 m (Alg.corner b) +
      x.2 ^ G.n * G.fe x.1.1 m (Alg.corner b)) = _
    rw [sum_add_distrib, sum_comm]
    congr 1
    · exact sum_congr rfl fun a _ => (mul_sum _ _ _).symm
    · exact (mul_sum _ _ _).symm
  rw [h]
  show _ = ∑ a : Fin G.n, x.2 ^ (a : ℕ) * G.sh a x.1.1 + x.2 ^ G.n * x.1.2 () ↔ _
  have e : ∑ a : Fin G.n, x.2 ^ (a : ℕ) * (G.toWeightsL.val x.1.1 m a - G.sh a x.1.1) =
      ∑ a : Fin G.n, x.2 ^ (a : ℕ) * ∑ b : Fin G.k → Bool, G.fa a x.1.1 m (Alg.corner b) +
        ∑ a : Fin G.n, x.2 ^ (a : ℕ) * (m (G.nm a) * G.be a x.1.1) -
        ∑ a : Fin G.n, x.2 ^ (a : ℕ) * G.sh a x.1.1 := by
    rw [← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun a _ => by
      unfold WeightsL.val
      ring
  rw [e]
  constructor <;> intro h1 <;> linear_combination h1

/-- what stands behind the round -/
def Th (x : G.St1) (m : G.J → E) : Prop := G.B x m ∧ G.L.Sg x m

theorem cnt_bad (st : G.St) (m : G.J → E) (h : ¬ G.Phi st m) (s : Unit → E) :
    cnt (fun c => G.Th ((st, s), c) m) ≤ G.n := by
  classical
  let v : Fin (G.n + 1) → E := Fin.snoc (fun a : Fin G.n => G.toWeightsL.val st m a - G.sh a st)
    (G.lhs st m - G.rhs st m)
  have hv : v ≠ 0 := fun h0 => h
    ⟨fun a => sub_eq_zero.1 (by
        have := congrFun h0 a.castSucc
        simpa [v, Fin.snoc_castSucc] using this),
      sub_eq_zero.1 (by
        have := congrFun h0 (Fin.last G.n)
        simpa [v, Fin.snoc_last] using this)⟩
  refine le_trans (cnt_mono fun c hc => ?_) (ok_powers E (G.n + 1) v hv)
  obtain ⟨hB, hS⟩ := hc
  have h2 := (G.sg_iff ((st, s), c) m).1 hS
  have h3 : s () - m G.mkE = G.rhs st m := hB
  show ∑ t : Fin (G.n + 1), c ^ (t : ℕ) * v t = 0
  rw [Fin.sum_univ_castSucc]
  simp only [v, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  rw [← h2, ← h3]
  show _ = ∑ a : Fin G.n, c ^ (a : ℕ) * (G.toWeightsL.val st m a - G.sh a st) +
    c ^ G.n * (G.lhs st m + m G.mkE - s ())
  ring

section Block
variable {Ex : ExtSpec} {M Wp Kc : Type} (R0 : Rels Kc G.St Ex (M × Wp)) (msg : M → G.J → E)

/-- what rides before the round -/
@[reducible] def A0 : Rels Kc G.St Ex (M × Wp) :=
  ⟨fun st y w => R0.rel st y w ∧ G.Rd st (msg w.1), fun a w => R0.relR a w ∧ G.Rd a.1 (msg w.1),
    R0.on, R0.core⟩

@[reducible] def R1 : Rels Kc G.St1 Ex (M × Wp) :=
  ⟨fun x y w => R0.rel x.1.1 y w, fun a w => R0.relR (a.1.1.1, a.2) w, fun a => R0.on
      (a.1.1.1, a.2), R0.core⟩

/-- the joint before the stretch -/
@[reducible] def relIn : Rels Kc G.St Ex (M × Wp) := sendIn (G.A0 R0 msg) msg G.Phi

variable (V : ShortK G.L.T.par Ex)

/-- The reduction. -/
def blk : IOR G.St Ex G.L.T.par.Out Ex := (send E Unit E G.St Ex).seq (G.L.blk V)

/-- its errors -/
def eps : Err (G.blk V).shape :=
  Err.app (s := (send E Unit E G.St Ex).shape) ((G.n, ()) : ℕ × Unit) V.ε

theorem knowAt :
    KnowAt (G.blk V) (G.relIn R0 msg) (G.L.relOut (G.R1 R0) msg)
        (fun _ _ _ wp => wp) (G.eps V) := by
  have h1 := send_knowAt (D := E) (G.A0 R0 msg) msg G.Phi G.Th G.n
      fun st m h s => G.cnt_bad st m h s
  have h2 := G.L.knowAt (G.R1 R0) msg V
  refine knowAt_seq h1 (knowAt_mono h2 (fun _ h => h) (fun a w _ h => ?_)
      (fun _ _ _ h => h) fun _ h => h)
  exact ⟨⟨h.1.1, h.1.2.1⟩, h.1.2.2, h.2⟩

theorem know (m : M) :
    (G.blk V).red.Know (G.relIn R0 msg).on (fun a wp => (G.relIn R0 msg).relR a (m, wp))
      (fun b wp => (G.L.relOut (G.R1 R0) msg).relR b (m, wp)) (fun _ _ wp => wp) (G.eps V) :=
  (G.knowAt R0 msg V).know m

theorem errs : TWhole.errList (G.eps V) = G.n :: 1 :: (List.replicate G.k 2 ++ [1, 0]) := by
  unfold eps
  refine (errList_app _ _).trans ?_
  exact congrArg (List.cons G.n) (G.L.errs V)

end Block

end WFirstL
end
end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.WFirstL.sg_iff
#print axioms Cb.Pv.Lay.WFirstL.cnt_bad
#print axioms Cb.Pv.Lay.WFirstL.knowAt
#print axioms Cb.Pv.Lay.WFirstL.errs
