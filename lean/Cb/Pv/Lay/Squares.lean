-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/Squares.lean: the stretch of the norms' sums of squares in a layers' sub-proof: hidden
scalars are sent and batched, the norms are joined, and one product layer follows.

For each of n norms and each of ns places the sub-proof needs an identity between two forms in the
entries,
    conv i s = rhs i s:
on the left the s-th convolution sum of the limbs of norm i's input, which is quadratic in cells; on
the right a form in the norm's digit row. The prover sends a scalar for each (i, s): conv i s plus a
mask entry of its own. That splits the identity into two claims under one new name:
    (A) conv i s + m (mkS i s) = sent (i, s),      (B) sent (i, s) - m (mkS i s) = rhs i s.
The rows (B) ride on. In the same round the verifier draws one element c. Under its powers, from the
power 0 on, the claims (A) of a norm become one claim: the left sides add up to the sum of the
squares of one vector, the limbs under the powers of c (`law`). So behind the round n claims are
open, all under one draw. They are joined under the equality weights of a fresh point, and a product
layer follows whose two maps are that vector, the left one cut off behind the last norm
(Cb/Pv/Lay/Routed.lean).

Main names:
  `SquaresL`: the parameters. `law` is a condition on conv and the vector, held in the record;
    `scale` is the factor by which the programs multiply the start form (a plain sum over some
    variables is written as an equality-weighted sum at 1/2).
  `SquaresL.Phi`: the identities. `SquaresL.B`: the rows (B).
  `SquaresL.R`: the parameters of the join and the layer behind the round.
  `SquaresL.cnt_bad`: if an identity fails, at most ns - 1 draws make all rows (B) and all batched
    claims true.
  `SquaresL.blk V`, `SquaresL.knowAt`, `SquaresL.know`: the reduction; its knowledge soundness for
    each fixed tuple of messages, from "what rides, and the identities" to "what rides, the rows
    (B), one row on names, two rows on end values".
  `SquaresL.errs`: its errors, round by round: ns - 1; the join's; the layer's.

Limits: nothing is said on what conv, rhs and the vector are in the model. The fields `law`, `hs`
(scale is not 0) and `hn` (n is at most 2^g) are to be paid by whoever fills the record: that the
programs' convolution sums and vector meet `law` is not shown here. The layer's left map is the
vector cut to 0 from the index n * 2^k' on (Cb/Pv/Lay/Routed.lean): the two maps are the same vector
only at n = 2^g. For the rest as in Cb/Pv/Lay/Routed.lean.

-/
import Cb.Pv.Lay.Routed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Iop Prob Cb IOR Finset TWhole

noncomputable section

/-- The parameters of the stretch. -/
structure SquaresL (E : Type) [Field E] [Fintype E] where
  J : Type
  [finJ : Fintype J]
  g : ℕ
  k' : ℕ
  /-- the number of norms; of places -/
  n : ℕ
  hn : n ≤ 2 ^ g
  ns : ℕ
  e : Fin (g + k') ≃ Fin (g + k')
  St : Type
  /-- the vector under the drawn element, on the index i * 2^k' + x -/
  vx : St → E → (J → E) → ℕ → E
  pnt : St → Fin k' → E
  scale : E
  hs : scale ≠ 0
  conv : St → (J → E) → Fin n → Fin ns → E
  rhs : St → (J → E) → Fin n → Fin ns → E
  law : ∀ st c m i, scale * ∑ s : Fin ns, c ^ (s : ℕ) * conv st m i s =
    Blocks.ext k' (fun x => vx st c m (i.val * 2 ^ k' + x) * vx st c m (i.val * 2 ^ k' + x))
        (Blocks.nat (pnt st))
  /-- the names of the sent scalars' mask entries -/
  mkS : Fin n → Fin ns → J
  wAt : PIdx (ldPartFmt E (g + k') (fun _ => 2) ++ [pDummy E 2]) → J
  cAt : Bool → J
  Rd : St → (J → E) → Prop

attribute [instance] SquaresL.finJ

variable {E : Type} [Field E] [Fintype E]

namespace SquaresL
variable (G : SquaresL E)

/-- the identities -/
def Phi (st : G.St) (m : G.J → E) : Prop := ∀ i s, G.conv st m i s = G.rhs st m i s

/-- the states behind the round: ((the old state, the sent scalars), the drawn element) -/
abbrev St1 : Type := (G.St × (Fin G.n × Fin G.ns → E)) × E

/-- the rows that ride on -/
def B (x : G.St1) (m : G.J → E) : Prop := ∀ i s, x.1.2 (i, s) - m (G.mkS i s) = G.rhs x.1.1 m i s

open Classical in
/-- the join and the layer behind the round -/
@[reducible] def R : RoutedL E where
  J := G.J
  g := G.g
  k' := G.k'
  n := G.n
  hn := G.hn
  e := G.e
  St := G.St1
  vm := fun x m _ X => G.vx x.1.1 x.2 m X
  pnt := fun x => G.pnt x.1.1
  inci := fun i x j => ∑ s : Fin G.ns, if j = G.mkS i s then G.scale * x.2 ^ (s : ℕ) else 0
  sh := fun i x => G.scale * ∑ s : Fin G.ns, x.2 ^ (s : ℕ) * x.1.2 (i, s)
  wAt := G.wAt
  cAt := G.cAt
  Rd := fun x m => G.Rd x.1.1 m ∧ G.B x m

theorem inci_sum (i : Fin G.n) (x : G.St1) (m : G.J → E) :
    ∑ j, G.R.inci i x j * m j = G.scale * ∑ s : Fin G.ns, x.2 ^ (s : ℕ) * m (G.mkS i s) := by
  classical
  show ∑ j, (∑ s : Fin G.ns, if j = G.mkS i s then G.scale * x.2 ^ (s : ℕ) else 0) * m j = _
  simp only [sum_mul]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun s _ => ?_
  rw [Finset.sum_eq_single (G.mkS i s)]
  · rw [if_pos rfl]
    ring
  · intro j _ hj
    rw [if_neg hj, zero_mul]
  · intro h0
    exact absurd (Finset.mem_univ _) h0

/-- what a batched claim says -/
theorem val_iff (i : Fin G.n) (x : G.St1) (m : G.J → E) :
    G.R.val x m i = G.R.sh i x ↔
      ∑ s : Fin G.ns, x.2 ^ (s : ℕ) * (G.conv x.1.1 m i s + m (G.mkS i s) - x.1.2 (i, s)) = 0 := by
  unfold RoutedL.val
  rw [G.inci_sum]
  show Blocks.ext G.k' (fun y => G.vx x.1.1 x.2 m (i.val * 2 ^ G.k' + y) * G.vx x.1.1 x.2 m (i.val
      * 2 ^ G.k' + y))
    (Blocks.nat (G.pnt x.1.1)) + _ = G.scale * ∑ s : Fin G.ns, x.2 ^ (s : ℕ) * x.1.2 (i, s) ↔ _
  rw [← G.law x.1.1 x.2 m i, ← mul_add, ← sub_eq_zero, ← mul_sub, mul_eq_zero, or_iff_right G.hs,
    ← sum_add_distrib, ← sum_sub_distrib]
  have e : ∀ s : Fin G.ns, x.2 ^ (s : ℕ) * G.conv x.1.1 m i s + x.2 ^ (s : ℕ) * m (G.mkS i s) -
      x.2 ^ (s : ℕ) * x.1.2 (i, s) = x.2 ^ (s : ℕ) * (G.conv x.1.1 m i s + m (G.mkS i s)
          - x.1.2 (i, s)) :=
    fun s => by ring
  simp only [e]

/-- what stands behind the round -/
def Th (x : G.St1) (m : G.J → E) : Prop := G.B x m ∧ ∀ i, G.R.val x m i = G.R.sh i x

theorem cnt_bad (st : G.St) (m : G.J → E) (h : ¬ G.Phi st m) (s : Fin G.n × Fin G.ns → E) :
    cnt (fun c => G.Th ((st, s), c) m) ≤ G.ns - 1 := by
  classical
  have h1 : ∃ i, (fun t => G.conv st m i t - G.rhs st m i t) ≠ 0 := by
    by_contra hc
    refine h fun i t => ?_
    have h2 : (fun t => G.conv st m i t - G.rhs st m i t) = 0 := by
      by_contra h3
      exact hc ⟨i, h3⟩
    exact sub_eq_zero.1 (congrFun h2 t)
  obtain ⟨i, hi⟩ := h1
  refine le_trans (cnt_mono fun c hc => ?_) (ok_powers E G.ns _ hi)
  obtain ⟨hB, hA⟩ := hc
  have h2 := (G.val_iff i ((st, s), c) m).1 (hA i)
  show ∑ t : Fin G.ns, c ^ (t : ℕ) * (G.conv st m i t - G.rhs st m i t) = 0
  rw [← h2]
  refine sum_congr rfl fun t _ => ?_
  have h3 : s (i, t) - m (G.mkS i t) = G.rhs st m i t := hB i t
  show _ = c ^ (t : ℕ) * (G.conv st m i t + m (G.mkS i t) - s (i, t))
  rw [← h3]
  ring

section Block
variable {Ex : ExtSpec} {M Wp Kc : Type} (R0 : Rels Kc G.St Ex (M × Wp)) (msg : M → G.J → E)

/-- what rides before the round -/
@[reducible] def A0 : Rels Kc G.St Ex (M × Wp) :=
  ⟨fun st y w => R0.rel st y w ∧ G.Rd st (msg w.1), fun a w => R0.relR a w ∧ G.Rd a.1 (msg w.1),
    R0.on, R0.core⟩

/-- the base, read at the old state -/
@[reducible] def R1 : Rels Kc G.St1 Ex (M × Wp) :=
  ⟨fun x y w => R0.rel x.1.1 y w, fun a w => R0.relR (a.1.1.1, a.2) w, fun a => R0.on
      (a.1.1.1, a.2), R0.core⟩

/-- the joint before the stretch: what rides, and the identities -/
@[reducible] def relIn : Rels Kc G.St Ex (M × Wp) := sendIn (G.A0 R0 msg) msg G.Phi

variable (V : ShortK G.R.L.T.par Ex)

/-- The reduction. -/
def blk : IOR G.St Ex G.R.L.T.par.Out Ex := (send E (Fin G.n × Fin G.ns) E G.St Ex).seq (G.R.blk V)

/-- its errors -/
def eps : Err (G.blk V).shape :=
  Err.app (s := (send E (Fin G.n × Fin G.ns) E G.St Ex).shape) ((G.ns - 1, ()) : ℕ × Unit)
      (G.R.eps (Kc := Kc) V)

theorem knowAt :
    KnowAt (G.blk V) (G.relIn R0 msg) (G.R.L.relOut (G.R.R1 (G.R1 R0)) msg) (fun _ _ _ wp => wp)
      (G.eps (Kc := Kc) V) := by
  have h1 := send_knowAt (D := E) (G.A0 R0 msg) msg G.Phi G.Th (G.ns - 1)
      fun st m h s => G.cnt_bad st m h s
  have h2 := G.R.knowAt (G.R1 R0) msg V
  refine knowAt_seq h1 (knowAt_mono h2 (fun _ h => h) (fun a w _ h => ?_)
      (fun _ _ _ h => h) fun _ h => h)
  exact ⟨⟨h.1.1, h.1.2.1⟩, h.1.2.2, h.2⟩

theorem know (m : M) :
    (G.blk V).red.Know (G.relIn R0 msg).on (fun a wp => (G.relIn R0 msg).relR a (m, wp))
      (fun b wp => (G.R.L.relOut (G.R.R1 (G.R1 R0)) msg).relR b (m, wp)) (fun _ _ wp => wp)
      (G.eps (Kc := Kc) V) :=
  (G.knowAt R0 msg V).know m

theorem errs : TWhole.errList (G.eps (Kc := Kc) V) =
    (G.ns - 1) :: (G.g * Fintype.card E ^ (G.g - 1)) :: 1 :: (List.replicate (G.g
        + G.k') 2 ++ [2, 0, 1]) := by
  unfold eps
  refine (errList_app _ _).trans ?_
  rw [G.R.errs V]
  rfl

end Block

end SquaresL
end
end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.SquaresL.cnt_bad
#print axioms Cb.Pv.Lay.SquaresL.knowAt
#print axioms Cb.Pv.Lay.SquaresL.errs
