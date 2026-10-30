-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/Routed.lean: several claims on products of two maps are joined under the equality weights
of a fresh point, and one product layer follows.

Before the stretch n claims are open, all at one point z of k' coordinates. Claim i says
    (sum over x of eq(z, x) * vL(i, x) * vR(i, x)) + < inci i, m > = sh i:
the value of a vector that is never sent, under a linear form in mask entries, is a public number.
(Where the value was shown masked, the form is the mask's factor at the name of its mask entry, and
sh i is the scalar that was sent.) The verifier draws a point p of g coordinates, with n at most
2^g. Under the weights eq(p, i) the claims become one claim of the same form on g + k' variables, at
the point (p, z). Then comes the product layer (Cb/Pv/Lay/Prod.lean). In a layers' sub-proof this is
the stretch of the routed experts' gated products; with the message of the squares' scalars before
it, also that of the norms.

Main names:
  `ext_join`: the extension on g + k' variables at (p, z) of a vector that vanishes from index n *
    2^k' on is the sum over i below n of eq(p, i) times the extension of block i at z.
  `RoutedL`: the parameters. `RoutedL.val`: a claim's value, with its mask.
  `RoutedL.L`: the product layer's parameters behind the draw. `RoutedL.link`: the joined claim is
    its input claim.
  `RoutedL.blk V`, `RoutedL.knowAt`, `RoutedL.know`: the reduction; its knowledge soundness for each
    fixed tuple of messages, from "what rides, and all n claims" to "what rides, one row on names,
    two rows on end values".
  `RoutedL.errs`: its errors, round by round: the join's g * |E|^(g - 1) (of |E|^g points); then the
    layer's.

Limits: the field `hn` (n is at most 2^g) is to be paid by whoever fills the record. Behind the draw
the layer's left map is the given one cut to 0 from the index n * 2^k' on, so the row on its end
value speaks of the cut map; at n = 2^g nothing is cut. At g = 0 the stretch still has the round of
the join, with a draw from a set of one point and the error 0; the programs have no such round
there. The join's error is a count of points, out of the |E|^g points. For the rest as in
Cb/Pv/Lay/Prod.lean and Cb/Pv/Lay/Draws.lean.

-/
import Cb.Pv.Lay.Prod
import Cb.Pv.Lay.Draws
import Cb.Gen.BatEvaderNumProofs
import Blocks.LookupCalls

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Iop Prob Cb IOR Finset TWhole

noncomputable section

section Ext
variable {E : Type} [Field E]

theorem eqN_congr' {g off off' : ℕ} {a a' : ℕ → E} (h : ∀ t < g, a (off + t) = a'
    (off' + t)) (X : ℕ) :
    Blocks.eqN g off a X = Blocks.eqN g off' a' X := by
  unfold Blocks.eqN
  exact prod_congr rfl fun t ht => by rw [h t (mem_range.mp ht)]

theorem nat_append_left (g k' : ℕ) (p : Fin g → E) (z : Fin k' → E) (t : ℕ) (ht : t < g) :
    Blocks.nat (Fin.append p z) t = Blocks.nat p t := by
  unfold Blocks.nat
  rw [dif_pos (by omega), dif_pos ht]
  exact Fin.append_left p z ⟨t, ht⟩

theorem nat_append_right (g k' : ℕ) (p : Fin g → E) (z : Fin k' → E) (t : ℕ) (ht : t < k') :
    Blocks.nat (Fin.append p z) (g + t) = Blocks.nat z t := by
  unfold Blocks.nat
  rw [dif_pos (by omega), dif_pos ht]
  exact Fin.append_right p z ⟨t, ht⟩

/-- The join of n blocks. -/
theorem ext_join (g k' n : ℕ) (hn : n ≤ 2 ^ g) (P : ℕ → E) (hP : ∀ X, n * 2 ^ k' ≤ X → P X = 0)
    (p : Fin g → E) (z : Fin k' → E) :
    Blocks.ext (g + k') P (Blocks.nat (Fin.append p z)) =
      ∑ i : Fin n, Blocks.eqN g 0 (Blocks.nat p) i.val *
        Blocks.ext k' (fun x => P (i.val * 2 ^ k' + x)) (Blocks.nat z) := by
  rw [Blocks.ext_two, Fin.sum_univ_eq_sum_range
    (fun i => Blocks.eqN g 0 (Blocks.nat p) i * Blocks.ext k' (fun x => P (i * 2 ^ k' + x))
        (Blocks.nat z)) n]
  have hsub : range n ⊆ range (2 ^ g) := range_subset_range.2 hn
  rw [← sum_subset hsub]
  · refine sum_congr rfl fun i _ => ?_
    unfold Blocks.ext
    rw [mul_sum]
    refine sum_congr rfl fun y _ => ?_
    rw [eqN_congr' (off' := 0) (a' := Blocks.nat p) (fun t ht => by
        rw [Nat.zero_add]; exact nat_append_left g k' p z t ht) i,
      eqN_congr' (off := g) (off' := 0) (a' := Blocks.nat z) (fun t ht => by
        rw [Nat.zero_add]; exact nat_append_right g k' p z t ht) y]
    ring
  · intro i _ hi
    refine sum_eq_zero fun y _ => ?_
    rw [hP (i * 2 ^ k' + y) (by
      have : n ≤ i := Nat.le_of_not_lt fun h => hi (mem_range.2 h)
      exact le_trans (Nat.mul_le_mul_right _ this) (Nat.le_add_right _ _)), mul_zero]

end Ext

/-- The parameters of the stretch. -/
structure RoutedL (E : Type) [Field E] [Fintype E] where
  J : Type
  [finJ : Fintype J]
  /-- the coordinates of the fresh point; of the claims' point; the number of claims -/
  g : ℕ
  k' : ℕ
  n : ℕ
  hn : n ≤ 2 ^ g
  /-- the order in which the g + k' variables are bound -/
  e : Fin (g + k') ≃ Fin (g + k')
  St : Type
  /-- the two maps, on the index i * 2^k' + x -/
  vm : St → (J → E) → Bool → ℕ → E
  /-- the claims' point -/
  pnt : St → Fin k' → E
  /-- a claim's incoming form and target -/
  inci : Fin n → Slf E St J
  sh : Fin n → St → E
  wAt : PIdx (ldPartFmt E (g + k') (fun _ => 2) ++ [pDummy E 2]) → J
  cAt : Bool → J
  Rd : St → (J → E) → Prop

attribute [instance] RoutedL.finJ

variable {E : Type} [Field E] [Fintype E]

namespace RoutedL
variable (G : RoutedL E)

/-- the value of claim i, with its mask -/
def val (st : G.St) (m : G.J → E) (i : Fin G.n) : E :=
  Blocks.ext G.k' (fun x => G.vm st m false (i.val * 2 ^ G.k' + x) * G.vm st m true
      (i.val * 2 ^ G.k' + x))
    (Blocks.nat (G.pnt st)) + ∑ j, G.inci i st j * m j

/-- the evader: the equality weights of a point -/
abbrev ev : Evader E (Fin G.n) := Evader.eqNum E G.g G.n

/-- the product layer's parameters behind the draw; the left map is cut off behind the last claim -/
@[reducible] def L : ProdL E where
  J := G.J
  k := G.g + G.k'
  e := G.e
  St := G.St × (Fin G.g → E)
  vm := fun x m b X =>
    bif b then G.vm x.1 m true X else (if G.n * 2 ^ G.k' ≤ X then 0 else G.vm x.1 m false X)
  pnt := fun x => Fin.append x.2 (G.pnt x.1)
  inc := fun x j => ∑ i : Fin G.n, G.ev.ze x.2 i * G.inci i x.1 j
  tg := fun x => ∑ i : Fin G.n, G.ev.ze x.2 i * G.sh i x.1
  wAt := G.wAt
  cAt := G.cAt
  Rd := fun x m => G.Rd x.1 m

theorem inc_sum (x : G.St × (Fin G.g → E)) (m : G.J → E) :
    ∑ j, G.L.inc x j * m j = ∑ i : Fin G.n, G.ev.ze x.2 i * ∑ j, G.inci i x.1 j * m j := by
  show ∑ j, (∑ i : Fin G.n, G.ev.ze x.2 i * G.inci i x.1 j) * m j = _
  simp only [sum_mul, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => mul_assoc _ _ _

/-- The joined claim is the product layer's input claim. -/
theorem link (x : G.St × (Fin G.g → E)) (m : G.J → E) :
    G.L.Sg x m ↔ ∑ i, G.ev.ze x.2 i * G.val x.1 m i = ∑ i, G.ev.ze x.2 i * G.sh i x.1 := by
  have h := ext_join G.g G.k' G.n G.hn
    (fun X => G.L.vm x m false X * G.L.vm x m true X)
    (fun X hX => by
      show (if G.n * 2 ^ G.k' ≤ X then (0 : E) else G.vm x.1 m false X) * _ = 0
      rw [if_pos hX, zero_mul]) x.2 (G.pnt x.1)
  have hb : ∀ i : Fin G.n,
      Blocks.ext G.k'
        (fun y => G.L.vm x m false (i.val * 2 ^ G.k' + y) * G.L.vm x m true (i.val * 2 ^ G.k' + y))
        (Blocks.nat (G.pnt x.1)) =
      Blocks.ext G.k'
        (fun y => G.vm x.1 m false (i.val * 2 ^ G.k' + y) * G.vm x.1 m true (i.val * 2 ^ G.k' + y))
        (Blocks.nat (G.pnt x.1)) := fun i =>
    Blocks.ext_congr (fun y hy => by
      have hlt : ¬ G.n * 2 ^ G.k' ≤ i.val * 2 ^ G.k' + y := by
        have h1 : (i.val + 1) * 2 ^ G.k' ≤ G.n * 2 ^ G.k' := Nat.mul_le_mul_right _ i.2
        rw [Nat.add_mul, Nat.one_mul] at h1
        omega
      show (if G.n * 2 ^ G.k' ≤ i.val * 2 ^ G.k' + y then (0 : E)
        else G.vm x.1 m false (i.val * 2 ^ G.k' + y)) * G.vm x.1 m true (i.val * 2 ^ G.k' + y) = _
      rw [if_neg hlt]) _
  have key : Blocks.ext G.L.k (fun X => G.L.vm x m false X * G.L.vm x m true X)
      (Blocks.nat (G.L.pnt x)) +
      ∑ j, G.L.inc x j * m j = ∑ i, G.ev.ze x.2 i * G.val x.1 m i := by
    rw [G.inc_sum]
    refine (congrArg (· + ∑ i : Fin G.n, G.ev.ze x.2 i * ∑ j, G.inci i x.1 j * m j) h).trans ?_
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [hb i]
    exact (mul_add _ _ _).symm
  unfold ProdL.Sg
  rw [key]

section Block
variable {Ex : ExtSpec} {M Wp Kc : Type} (R0 : Rels Kc G.St Ex (M × Wp)) (msg : M → G.J → E)

/-- what rides before the draw -/
@[reducible] def A0 : Rels Kc G.St Ex (M × Wp) :=
  ⟨fun st y w => R0.rel st y w ∧ G.Rd st (msg w.1), fun a w => R0.relR a w ∧ G.Rd a.1 (msg w.1),
    R0.on, R0.core⟩

@[reducible] def R1 : Rels Kc (G.St × (Fin G.g → E)) Ex (M × Wp) :=
  ⟨fun x y w => R0.rel x.1 y w, fun a w => R0.relR (a.1.1, a.2) w, fun a => R0.on
      (a.1.1, a.2), R0.core⟩

/-- the joint before the stretch: what rides, and all claims -/
@[reducible] def relIn : Rels Kc G.St Ex (M × Wp) := combIn (G.A0 R0 msg) msg G.val
    fun st i => G.sh i st

variable (V : ShortK G.L.T.par Ex)

/-- The reduction. -/
def blk : IOR G.St Ex G.L.T.par.Out Ex := (comb G.ev G.St Ex).seq (G.L.blk V)

/-- its errors -/
def eps : Err (G.blk V).shape :=
  Err.app (s := (comb G.ev G.St Ex).shape)
    (Nums.draw Kc (Fin G.g → E) (fun (st : G.St) (β : Fin G.g → E) => (st, β)) Ex G.ev.err).err
    (G.L.eps (Kc := Kc) V)

theorem knowAt :
    KnowAt (G.blk V) (G.relIn R0 msg) (G.L.relOut (G.R1 R0) msg) (fun _ _ _ wp => wp) (G.eps
        (Kc := Kc) V) := by
  have h1 := comb_knowAt G.ev (G.A0 R0 msg) msg G.val (fun st i => G.sh i st)
      (ok_eqNum E G.g G.n G.hn)
  have h2 := G.L.knowAt (G.R1 R0) msg V
  refine knowAt_seq h1 (knowAt_mono h2 (fun _ h => h) (fun a w _ h => ?_)
      (fun _ _ _ h => h) fun _ h => h)
  exact ⟨h.1, (G.link a.1 _).1 h.2⟩

theorem know (m : M) :
    (G.blk V).red.Know (G.relIn R0 msg).on (fun a wp => (G.relIn R0 msg).relR a (m, wp))
      (fun b wp => (G.L.relOut (G.R1 R0) msg).relR b (m, wp)) (fun _ _ wp => wp)
          (G.eps (Kc := Kc) V) :=
  (G.knowAt R0 msg V).know m

theorem errs : TWhole.errList (G.eps (Kc := Kc) V) =
    (G.g * Fintype.card E ^ (G.g - 1)) :: 1 :: (List.replicate (G.g + G.k') 2 ++ [2, 0, 1]) := by
  unfold eps
  refine (errList_app _ _).trans ?_
  rw [G.L.errs V]
  rfl

end Block

end RoutedL
end
end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.ext_join
#print axioms Cb.Pv.Lay.RoutedL.link
#print axioms Cb.Pv.Lay.RoutedL.knowAt
#print axioms Cb.Pv.Lay.RoutedL.errs
