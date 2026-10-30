-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/Sc3.lean: the sumcheck of products of an attention sub-proof, and its knowledge
soundness.

Its statement is: start = the sum over b and x of W_b(x) A_b(x) B_b(x), for nb pairs of maps (A_b,
B_b) in nv variables and public weights W_b (OnBytes/Model/AttentionSums.lean, sc3In and sc3Row;
C++: vf_sumcheck_attention.h [not in this library]). A round's polynomial has degree at most 3, the
round in the further variable at most 2, and all 2 nb end values are shown; the programs send them
in the order A_0, B_0, A_1, B_1, and so on. Among an attention sub-proof's own rounds there is one
sumcheck of this kind for each score segment that is present, and five more; one further sumcheck
is of another kind (OnBytes/Params/SubRounds.lean, planAttentionOwn; Cb/Pv/Att/Scd.lean).

Main names:
  Sc3: the parameters: nv, nb; the public states; the weights W; the maps, as functions of the
    entries (they need not be linear in them), where (b, false) names A_b and (b, true) names B_b;
    the incoming form; the entries that serve as masks; and two conditions: each weight and each
    map has degree at most 1 in every variable.
  Sc3.plain: the parameters as a plain sumcheck (Cb/Pv/Att/Plain.lean).
  sc3_ok: the conditions of a plain sumcheck hold.
  sc3_knowAt: the block, with n further scalars in its first message, has knowledge soundness
    (KnowAt), for every choice of the coefficients left out. At a choice that is not lawful the
    verifier may reject; at the choice of Cb/Pv/Att/Fix.lean it rejects nothing (sc3_out). That this
    choice is the programs' is by reading (that file's Limits): no statement says it.
  sc3_know: the same as the one item «know».
  sc3_nums: its errors are 1, then 3 for each variable, then 2, then 0: counts of challenge
    values, as said at plain_nums.
  sc3_sum: what the sum claim says.
  sc3_fix: the choice of Cb/Pv/Att/Fix.lean is lawful.

Limits. The limits of Cb/Pv/Att/Ride.lean hold here too: above all, the entries are fixed before
the block's first message. No parameters of an attention sub-proof are built here: that its
weights and maps meet the two conditions is not stated. Nothing is said on an honest prover or on
hiding; nothing on which committed arrays the maps read, on the order in which the rounds bind the
variables of an index, or on the port's routines.

-/
import Cb.Pv.Att.Fix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Cb TWhole Johnson.L5.Layers

/-- The parameters of a sumcheck of products. -/
structure Sc3 (E : Type) [Field E] [Fintype E] where
  nv : ℕ
  nb : ℕ
  St : Type
  J : Type
  [finJ : Fintype J]
  W : St → Fin nb → (Fin nv → E) → E
  map : St → (J → E) → Fin nb × Bool → (Fin nv → E) → E
  inc : St → J → E
  wAt : PIdx (ldPartFmt E nv (fun _ => 3) ++ [pDummy E 2]) → J
  cAt : Fin nb × Bool → J
  degW : ∀ st b, Alg.DegLE (fun _ => 1) (W st b)
  degM : ∀ st m a, Alg.DegLE (fun _ => 1) (map st m a)

attribute [instance] Sc3.finJ

variable {E : Type} [Field E] [Fintype E] (T : Sc3 E)

/-- As a plain sumcheck. -/
def Sc3.plain : PlainSc E where
  nv := T.nv
  deg := fun _ => 3
  A := Fin T.nb × Bool
  DY := 2
  St := T.St
  J := T.J
  map := T.map
  S := fun st x v => ∑ b, T.W st b x * v (b, false) * v (b, true)
  inc := T.inc
  wAt := T.wAt
  cAt := T.cAt

theorem sc3_lin (st : T.St) (m : T.J → E) (u : Fin T.nb × Bool → E) (a : Fin T.nb × Bool) :
    Alg.DegLE (fun _ => 1) fun x => T.plain.map st m a x + u a :=
  (T.degM st m a).add (Alg.DegLE.const _ _)

theorem sc3_ok : T.plain.OK where
  one := fun _ => show 1 ≤ 3 by norm_num
  degX := fun st m u =>
    Alg.DegLE.sum Finset.univ fun b _ =>
      (((T.degW st b).mul (sc3_lin T st m u (b, false))).mul (sc3_lin T st m u (b, true))).mono
        fun _ => le_refl 3
  degY := fun st x v u =>
    ⟨![∑ b, T.W st b x * v (b, false) * v (b, true),
        ∑ b, T.W st b x * (v (b, false) * u (b, true) + u (b, false) * v (b, true)),
        ∑ b, T.W st b x * u (b, false) * u (b, true)], fun y => by
      have e : ∀ c0 c1 c2 : E, hev ![c0, c1, c2] y = c0 + y * c1 + y ^ 2 * c2 := fun c0 c1 c2 => by
        simp [hev, Fin.sum_univ_three]
      refine Eq.trans ?_ (e _ _ _).symm
      show ∑ b, T.W st b x * (v (b, false) + u (b, false) * y) * (v (b, true) + u (b, true) * y) = _
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring⟩

section Block
variable (F : ∀ st, HFixs (T.plain.our.par.vars st)) (n : ℕ) {X : Type}
  (cl : X → (Fin n → E) → E × T.St) (Ex : ExtSpec) {M Wp Kc : Type}
  (A0 : IOR.Rels Kc X Ex (M × Wp)) (msg : M → T.J → E) (Θ : X → (Fin n → E) → (T.J → E) → Prop)

theorem sc3_knowAt :
    KnowAt (rideNR T.plain.our.par n F cl Ex) (rideNIn T.plain.our.par n cl Ex A0 msg Θ)
      (rideNOut T.plain.our.par n Ex A0 msg Θ) (fun _ _ _ wp => wp)
      (rideNE T.plain.our.par n Ex) :=
  plain_knowAt T.plain F n cl Ex A0 msg Θ (sc3_ok T)

/-- The one item «know». -/
theorem sc3_know (m : M) :
    (rideNR T.plain.our.par n F cl Ex).red.Know (rideNIn T.plain.our.par n cl Ex A0 msg Θ).on
      (fun a wp => (rideNIn T.plain.our.par n cl Ex A0 msg Θ).relR a (m, wp))
      (fun b wp => (rideNOut T.plain.our.par n Ex A0 msg Θ).relR b (m, wp)) (fun _ _ wp => wp)
      (rideNE T.plain.our.par n Ex) :=
  (sc3_knowAt T F n cl Ex A0 msg Θ).know m

theorem sc3_nums :
    errList (rideNE T.plain.our.par n Ex) = 1 :: (List.replicate T.nv 3 ++ [2] ++ [0]) := by
  rw [plain_nums]
  show 1 :: (List.ofFn (fun _ : Fin T.nv => 3) ++ [2] ++ [0]) = _
  rw [List.ofFn_const]

end Block

theorem sc3_sum (x : E × T.St) (m : T.J → E) :
    T.plain.our.par.SumHolds x m ↔
      ∑ c : Fin T.nv → Bool, ∑ b, T.W x.2 b (Alg.corner c) *
          T.map x.2 m (b, false) (Alg.corner c) * T.map x.2 m (b, true) (Alg.corner c) +
        ∑ j, T.inc x.2 j * m j = x.1 :=
  plain_sum T.plain x m

theorem sc3_fix : ∀ st, HFixs.OK (T.plain.our.par.vars st) (T.plain.fix st) :=
  plain_fix T.plain (sc3_ok T)

/-- At the choice of Cb/Pv/Att/Fix.lean the block rejects nothing. -/
theorem sc3_out (n : ℕ) {X : Type} (cl : X → (Fin n → E) → E × T.St) (Ex : ExtSpec) (x : X)
    (y : Ex.Str) (τ : Tr (shapeRN T.plain.our.par n)) :
    (rideNR T.plain.our.par n T.plain.fix cl Ex).out x y τ =
      some ((x, riders T.plain.our.par n τ),
        shortV T.plain.our.par T.plain.fix (cl x (riders T.plain.our.par n τ))
          (unrideN T.plain.our.par n τ)) :=
  plain_out T.plain (sc3_ok T) n cl Ex x y τ

end Cb.Pv.Att
