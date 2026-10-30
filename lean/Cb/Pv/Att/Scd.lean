-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/Scd.lean: the sumcheck of an attention sub-proof for the key at the index of the maximum:
its parameters, its block and the statement of its knowledge soundness.

Of the sumchecks of an attention sub-proof this is the one whose rounds have a degree of their own
each (OnBytes/Model/AttentionSums.lean, scdIn and scdRow, called by keyAtIndexIn of
OnBytes/Model/AttentionDivide.lean; C++: vf_sumcheck_attention.h and vf_attention_check.h). This
file holds definitions and one statement; the proofs are in Cb/Pv/Att/ScdProofs.lean.

The sizes (ScdSize): lt bits of a token's position; lgk bits of a head of keys and values; Lam
layers; HA query heads that read one head of keys and values. There are pairs = Lam * HA pairs
(layer, query head), and pair b belongs to layer b / HA.

The claim. The variables are, in the order of the rounds, j (lt bits: the key's position), g (lgk
bits), i (lt bits: the query's position): k = lt + lgk + lt variables, each summed plainly over 0
and 1. With public points ri, rg and public factors om, the claim on the entries m is
    sum over (j, g, i) of
      eq(ri, i) eq(rg, g) * sum over the pairs b of
        om b * KC_(b / HA) * prod over t < lt of ( IB_(b,t) (2 y_t - 1) + (1 - y_t) ),
      + < inc, m >  =  the target,        where y_t = j_(lt - 1 - t).
KC_l (one map for each layer) and IB_(b,t) (one for each pair and bit) are functions of the state,
the entries and the point (j, g, i). Two conditions stand in the parameters: KC_l has degree at most
1 in each coordinate of j and g and does not depend on i (degK); IB_(b,t) has degree at most 1 in
each coordinate of g and i and does not depend on j (degI). So the summand has the degree 2 in a
coordinate of j, lt + 2 in one of g, lt + 1 in one of i (ScdSize.deg), and the degree lt + 1 in the
values of the maps.
A factor v (2 y - 1) + (1 - y) equals v y + (1 - v) (1 - y).

Main names:
  `ScdSize`: the sizes. `scdS`: the summand at a point, on the values of the maps.
  `Scd`: the parameters. `Scd.plain`: the parameters as a plain sumcheck (Cb/Pv/Att/Plain.lean).
    The end values are named by `ScdSize.A`; in the programs' message KC_l stand first, by l, then
    IB_(b,t) by b and then t.
  `scdR`: the block: the short sumcheck with n further scalars in its first message
    (Cb/Pv/Att/Ride.lean) at the programs' choice of the coefficients that are left out
    (Cb/Pv/Att/Fix.lean: the linear one in the k rounds of the variables, the constant one in the
    round of the further variable). `scdE`: its errors. `scdIn`, `scdOut`: its joints.
  `H_scd`: the statement: at each of the listed sizes, for all parameters, every joint that is
    carried along and each fixed tuple of messages: round-by-round knowledge soundness between the
    two joints, the extractor the identity, with the errors `scdE`.

Limits: which committed arrays the maps read, where the mask entries lie and what the incoming form
is are parameters: that they are the programs' is a matter of the chain that uses the block. That
the port's routines compute this block's verifier is not said here. Nothing is said on an honest
prover or on hiding.

-/
import Cb.Pv.Att.Fix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Cb TWhole

/-- The sizes of the sumcheck. -/
structure ScdSize where
  /-- bits of a token's position -/
  lt : ℕ
  /-- bits of a head of keys and values -/
  lgk : ℕ
  /-- layers -/
  Lam : ℕ
  /-- query heads that read one head of keys and values -/
  HA : ℕ
  deriving DecidableEq, Repr

namespace ScdSize
variable (s : ScdSize)

/-- the pairs (layer, query head) -/
def pairs : ℕ := s.Lam * s.HA
/-- the variables -/
def k : ℕ := s.lt + s.lgk + s.lt

/-- the degree of each round -/
def deg (i : Fin s.k) : ℕ :=
  if i.1 < s.lt then 2 else if i.1 < s.lt + s.lgk then s.lt + 2 else s.lt + 1
/-- the degree that is allowed to a map KC_l in each variable -/
def degKC (i : Fin s.k) : ℕ := if i.1 < s.lt + s.lgk then 1 else 0
/-- the degree that is allowed to a map IB_(b,t) in each variable -/
def degIB (i : Fin s.k) : ℕ := if i.1 < s.lt then 0 else 1

/-- where the coordinates of j stand among the variables -/
def jAt (a : Fin s.lt) : Fin s.k := ⟨a.1, by have := a.2; unfold k; omega⟩
/-- where the coordinates of g stand -/
def gAt (a : Fin s.lgk) : Fin s.k := ⟨s.lt + a.1, by have := a.2; unfold k; omega⟩
/-- where the coordinates of i stand -/
def iAt (a : Fin s.lt) : Fin s.k := ⟨s.lt + s.lgk + a.1, by have := a.2; unfold k; omega⟩

/-- the layer of a pair -/
def lay (b : Fin s.pairs) : Fin s.Lam :=
  ⟨b.1 / s.HA, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact b.2)⟩

/-- the maps: KC_l, then IB_(b,t) -/
abbrev A : Type := Fin s.Lam ⊕ (Fin s.pairs × Fin s.lt)

end ScdSize

/-- The summand at the point z, on the values v of the maps. -/
def scdS {E : Type} [Field E] (s : ScdSize) (ri : Fin s.lt → E) (rg : Fin s.lgk → E)
    (om : Fin s.pairs → E) (z : Fin s.k → E) (v : s.A → E) : E :=
  Alg.eqPt ri (fun a => z (s.iAt a)) * Alg.eqPt rg (fun a => z (s.gAt a)) *
    ∑ b : Fin s.pairs, om b * v (.inl (s.lay b)) *
      ∏ t : Fin s.lt, (v (.inr (b, t)) * (z (s.jAt t.rev) + z (s.jAt t.rev) - 1) +
        (1 - z (s.jAt t.rev)))

/-- The parameters. -/
structure Scd (E : Type) [Field E] [Fintype E] (s : ScdSize) where
  St : Type
  J : Type
  [finJ : Fintype J]
  /-- the public points and factors, read off a state -/
  ri : St → Fin s.lt → E
  rg : St → Fin s.lgk → E
  om : St → Fin s.pairs → E
  /-- the maps -/
  mapKC : St → (J → E) → Fin s.Lam → (Fin s.k → E) → E
  mapIB : St → (J → E) → Fin s.pairs → Fin s.lt → (Fin s.k → E) → E
  inc : St → J → E
  wAt : PIdx (ldPartFmt E s.k s.deg ++ [pDummy E (s.lt + 1)]) → J
  cAt : s.A → J
  degK : ∀ st m l, Alg.DegLE s.degKC (mapKC st m l)
  degI : ∀ st m b t, Alg.DegLE s.degIB (mapIB st m b t)

attribute [instance] Scd.finJ

variable {E : Type} [Field E] [Fintype E] {s : ScdSize} (T : Scd E s)

/-- the maps under one name -/
def Scd.map (st : T.St) (m : T.J → E) : s.A → (Fin s.k → E) → E
  | .inl l => T.mapKC st m l
  | .inr p => T.mapIB st m p.1 p.2

/-- As a plain sumcheck. -/
def Scd.plain : PlainSc E where
  nv := s.k
  deg := s.deg
  A := s.A
  DY := s.lt + 1
  St := T.St
  J := T.J
  map := T.map
  S := fun st x v => scdS s (T.ri st) (T.rg st) (T.om st) x v
  inc := T.inc
  wAt := T.wAt
  cAt := T.cAt

section Block
variable (n : ℕ) {X : Type} (cl : X → (Fin n → E) → E × T.St) (Ex : ExtSpec) {M Wp Kc : Type}
  (A0 : IOR.Rels Kc X Ex (M × Wp)) (msg : M → T.J → E) (Θ : X → (Fin n → E) → (T.J → E) → Prop)

/-- The block. -/
noncomputable def scdR : IOR X Ex ((X × (Fin n → E)) × T.plain.our.par.Out) Ex :=
  rideNR T.plain.our.par n T.plain.fix cl Ex

/-- Its errors, as counts, round by round. -/
noncomputable def scdE : Err (scdR T n cl Ex).shape := rideNE T.plain.our.par n Ex

/-- The joint before the block: there are scalars of which Θ holds and at which the sum claim holds.
-/
noncomputable def scdIn : IOR.Rels Kc X Ex (M × Wp) := rideNIn T.plain.our.par n cl Ex A0 msg Θ

/-- The joint behind the block: Θ of the scalars that were sent; the row on the hiding polynomial's
coefficients; the claims on the end values. -/
noncomputable def scdOut : IOR.Rels Kc ((X × (Fin n → E)) × T.plain.our.par.Out) Ex (M × Wp) :=
  rideNOut T.plain.our.par n Ex A0 msg Θ

end Block

variable (E) in
/-- THE STATEMENT. -/
def H_scd (sizes : List ScdSize) : Prop :=
  ∀ s ∈ sizes, ∀ (T : Scd E s) (n : ℕ) (X : Type) (cl : X → (Fin n → E) → E × T.St) (Ex : ExtSpec)
    (M Wp Kc : Type) (A0 : IOR.Rels Kc X Ex (M × Wp)) (msg : M → T.J → E)
    (Θ : X → (Fin n → E) → (T.J → E) → Prop) (m : M),
    (scdR T n cl Ex).red.Know (scdIn T n cl Ex A0 msg Θ).on
      (fun a wp => (scdIn T n cl Ex A0 msg Θ).relR a (m, wp))
      (fun b wp => (scdOut T n Ex A0 msg Θ).relR b (m, wp))
      (fun _ _ wp => wp) (scdE T n cl Ex)

end Cb.Pv.Att
