-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/Plain.lean: the masked sumcheck over plain cube variables with a degree each, all of
whose end values are shown: its parameters, and its knowledge soundness.

All sumchecks among an attention sub-proof's own rounds have this form
(OnBytes/Model/AttentionSums.lean: sc3In and scdIn; both kinds of round are plain:
OnBytes/Model/Psc.lean, RoundForm.weight). They differ in the number of variables, the degrees,
the maps and the summand. The library has a builder for summands that are sums of products of maps
(Cb/Part/LdPartPsc.lean); here the summand is any function of the shown values.

Main names:
  PlainSc: the parameters: nv variables with the degrees deg; the maps' names A; the degree DY of
    the summand in the shown values; the public states St; map st m a x: map a at the point x, as
    a function of the entries m : J → E (any function: it need not be linear in m); S st x v: the
    summand at the point x on the values v of the maps; inc st: the coefficients of the incoming
    form; wAt, cAt: the entries that serve as the sumcheck's own masks.
  PlainSc.our: the parameters as an instance of the library's PscOur, over the library's own cube
    variables (Cb/Part/LdPartVars.lean) in the plain form.
  PlainSc.OK: three conditions: every degree is at least 1; the summand on the maps, whatever
    constants are added to their values, has at most the degrees deg in x; along every line in the
    values it is a polynomial of degree at most DY.
  plain_vars, plain_deg, plain_inj: under OK the three conditions of the general sumcheck.
  plain_degs: the degrees of the nv + 1 variables.
  plain_knowAt: the block of Cb/Pv/Att/Ride.lean at these parameters has knowledge soundness
    (KnowAt).
  plain_nums: its errors are 1, the degrees, DY, 0. The numbers are counts of challenge values: of
    |E| in the first round and in each variable's round, of |E| - 1 in the further variable's
    (psc_our_card, Cb/Ld/LdPsc.lean); in the last round nothing is drawn.
  plain_sum: what the sum claim says: the sum over the corners of the cube of the summand on the
    maps, plus the incoming form, is the target.
  plain_val: what the output claim on an end value says.

Limits. The limits of Cb/Pv/Att/Ride.lean hold here too. Nothing is said on an honest prover or on
hiding, nor on the port's routines. No probability and no sum of errors is stated.

-/
import Cb.Pv.Att.Ride
import Cb.Part.LdPartVarsProofs
import Cb.Ld.LdPscProofsOur

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Cb TWhole Johnson.L5.Layers

/-- The parameters. -/
structure PlainSc (E : Type) [Field E] [Fintype E] where
  nv : ℕ
  deg : Fin nv → ℕ
  A : Type
  [finA : Fintype A]
  DY : ℕ
  St : Type
  J : Type
  [finJ : Fintype J]
  map : St → (J → E) → A → (Fin nv → E) → E
  S : St → (Fin nv → E) → (A → E) → E
  inc : St → J → E
  wAt : PIdx (ldPartFmt E nv deg ++ [pDummy E DY]) → J
  cAt : A → J

attribute [instance] PlainSc.finA PlainSc.finJ

namespace PlainSc
variable {E : Type} [Field E] [Fintype E] (T : PlainSc E)

/-- the data of the variables: all plain -/
abbrev dat : PDats (ldPartFmt E T.nv T.deg) := ldPartDat E T.nv T.deg fun _ => none

/-- The instance of the library's sumcheck. -/
def our : PscOur E where
  St := T.St
  J := T.J
  fmt := ldPartFmt E T.nv T.deg
  dat := fun _ => T.dat
  A := T.A
  B := Empty
  F := fun st m a X => T.map st m a (ldPartFn T.nv T.deg T.dat X)
  Fb := fun _ _ b _ => b.elim
  S0 := fun st X v => T.S st (ldPartFn T.nv T.deg T.dat X) v
  S1 := fun _ _ _ b => b.elim
  DY := T.DY
  slS := T.inc
  wAt := T.wAt
  cAt := T.cAt

/-- The conditions. -/
structure OK : Prop where
  one : ∀ i, 1 ≤ T.deg i
  degX : ∀ st m (u : T.A → E), Alg.DegLE T.deg fun x => T.S st x fun a => T.map st m a x + u a
  degY : ∀ st x (v u : T.A → E), ∃ c : Fin (T.DY + 1) → E, ∀ y : E,
    T.S st x (fun a => v a + u a * y) = hev c y

end PlainSc

variable {E : Type} [Field E] [Fintype E] (T : PlainSc E)

theorem plain_vars (h : T.OK) : T.our.par.VarsOK :=
  (psc_our_ok E T.our).1 fun _ => ldPartVars_ok E T.nv T.deg (fun _ => none) fun i _ => h.one i

theorem plain_inj : T.our.par.ValInj :=
  (psc_our_ok E T.our).2 (ldPartVars_inj E T.nv T.deg)

theorem plain_deg (h : T.OK) : T.our.par.DegOK :=
  psc_our_deg E T.our
    (fun st m u => by
      have h1 := ldPartVars_deg E T.nv T.deg T.dat _ (h.degX st m u)
      refine (congrArg (HDeg _) (funext fun X => ?_)).mp h1
      show _ = T.S st _ _ + ∑ b : Empty, _
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      rfl)
    (fun st X v u _ => by
      obtain ⟨c, hc⟩ := h.degY st (ldPartFn T.nv T.deg T.dat X) v u
      refine ⟨c, fun y => ?_⟩
      show T.S st _ _ + ∑ b : Empty, _ = _
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      exact hc y)

theorem plain_degs : T.our.par.fmt.map PFmt.n = List.ofFn T.deg ++ [T.DY] := by
  rw [psc_our_degs E T.our]
  show (ldPartFmt E T.nv T.deg).map PFmt.n ++ [T.DY] = _
  rw [ldPartVars_degs E T.nv T.deg]

section Block
variable (F : ∀ st, HFixs (T.our.par.vars st)) (n : ℕ) {X : Type}
  (cl : X → (Fin n → E) → E × T.St) (Ex : ExtSpec) {M Wp Kc : Type}
  (A0 : IOR.Rels Kc X Ex (M × Wp)) (msg : M → T.J → E) (Θ : X → (Fin n → E) → (T.J → E) → Prop)

/-- The block has knowledge soundness. This is said under the hypotheses that stand in the statement
itself, which this comment does not list; it is no claim that they hold. -/
theorem plain_knowAt (h : T.OK) :
    KnowAt (rideNR T.our.par n F cl Ex) (rideNIn T.our.par n cl Ex A0 msg Θ)
      (rideNOut T.our.par n Ex A0 msg Θ) (fun _ _ _ wp => wp) (rideNE T.our.par n Ex) :=
  rideN_knowAt T.our.par n F cl Ex A0 msg Θ (plain_vars T h) (plain_deg T h) (plain_inj T)

/-- Its errors. -/
theorem plain_nums :
    errList (rideNE T.our.par n Ex) = 1 :: (List.ofFn T.deg ++ [T.DY] ++ [0]) := by
  rw [rideN_nums, plain_degs]

end Block

/-- What the sum claim says. -/
theorem plain_sum (x : E × T.St) (m : T.J → E) :
    T.our.par.SumHolds x m ↔
      ∑ b : Fin T.nv → Bool, T.S x.2 (Alg.corner b) (fun a => T.map x.2 m a (Alg.corner b)) +
        ∑ j, T.inc x.2 j * m j = x.1 := by
  rw [psc_our_sum E T.our x m]
  have hs := ldPartVars_sum E T.nv T.deg (fun _ => none) (T.our.sum x.2 m)
  rw [show T.our.SumHolds x m ↔ hSumAll (pVars (ldPartFmt E T.nv T.deg) T.dat) (T.our.sum x.2 m) +
    ∑ j, T.inc x.2 j * m j = x.1 from Iff.rfl, hs]
  have e : ∀ b : Fin T.nv → Bool,
      (∏ i, ldPartWt (none : Option E) (b i)) *
        T.our.sum x.2 m (pH _ T.dat (ldPartPP T.nv T.deg (Alg.corner b))) =
      T.S x.2 (Alg.corner b) fun a => T.map x.2 m a (Alg.corner b) := fun b => by
    have h1 : (∏ i : Fin T.nv, ldPartWt (none : Option E) (b i)) = 1 :=
      Finset.prod_eq_one fun _ _ => rfl
    rw [h1, one_mul]
    show T.S x.2 (ldPartFn T.nv T.deg T.dat _) _ + ∑ b : Empty, _ = _
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    show T.S x.2 (ldPartFn T.nv T.deg T.dat _)
      (fun a => T.map x.2 m a (ldPartFn T.nv T.deg T.dat _)) = _
    rw [ldPartVars_fn E T.nv T.deg T.dat]
  rw [Finset.sum_congr rfl fun b _ => e b]

/-- What the output claim on an end value says. -/
theorem plain_val (o : T.our.par.Out) (m : T.J → E) (a : T.A) :
    T.our.par.EHolds o m a ↔
      T.map o.st m a (ldPartFn T.nv T.deg T.dat (T.our.ini o.st (T.our.par.hp o.st o.pt))) +
        m (T.cAt a) * T.our.lst o.st (T.our.par.hp o.st o.pt) = o.vals a :=
  psc_our_val E T.our o m a

end Cb.Pv.Att
