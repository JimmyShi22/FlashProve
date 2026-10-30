-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpTie.lean: the lookup: the two sides of the identity are tied by a chain of sumchecks
without variable, on values that are never sent.
This file is about one part of the lookup argument with multiplicities in bits: how the product over
the keys is compared with a product of powers of the products over the table.

Definitions, and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLkpTieProofs.lean.
It is built from the sumcheck for a polynomial summand (Cb/Ld/LdPsc.lean: `PscOur`, with an empty
list of variables) and a step without rounds (Cb/Ld/LdSigStep.lean). Nothing about them is assumed.
No oracle is sent.

Where it is used. After its first challenge a lookup with multiplicities in bits claims PK = the
product over the bit positions j of PT_j ^ (2 ^ j): PK the product over the keys, PT_j the product
over the table at the bit position j. Neither is ever sent: they are functions of the public state
and of the messages ("virtual scalars").
With Q_j := the product over i ≥ j of PT_i ^ (2 ^ (i - j)) the claim reads PK = Q_0, and Q_j =
Q_(j+1)² · PT_j for j < n (`D.StepTo n`: the one condition; n + 1 is the number of steps). It is not
asked at j ≥ n: with n = W - 1 (W: the number of bit positions that write a multiplicity,
Cb/Gen/LkpAlg.lean) and Q_(W-1) = PT_(W-1) it would fail there in general, and a condition that the
lookup's values do not meet would make the theorem empty.

The chain. Every step is the sumcheck with no variable but the dummy one: three rounds (a scalar |
ε; a round polynomial in the dummy variable | β ≠ 0; two masked values | nothing). Its input is one
claim S(values) + (a linear form on mask entries) = (public target); its output: a row on its own
hiding coefficients (and on the entries that the incoming form reads), and for each of the two
values value + β · (own mask entry) = (the scalar sent).
  step 0: S = Y₁ - Y₂ at (PK, Q_0), target 0 in the lookup's use (here: any target), no form →
  masked claims on PK and on Q_0.
  step j + 1: S = Y₁² · Y₂ at (Q_(j+1), PT_j): the masked claim on Q_j → masked claims on Q_(j+1)
  and on PT_j.
Between two steps nothing is sent: the verifier takes the scalar sent for Q_j as the next target and
β at that mask entry as the next form (a step without rounds).
After the steps 0, .., n: one masked claim on Q_n is open (the joint's own claim); the masked claims
on PK and on PT_0, .., PT_(n-1), and the n + 1 rows on hiding coefficients, ride along. With n = W -
1 and Q_(W-1) = PT_(W-1) these are masked claims with public targets on the roots of the keys' tree
and of the table's forest: nobody else has to state them.

The data. `D : TieP E` (St0, J; PK, PT, Q as functions of state and entries; where the own masks of
each step lie). `D.tieA`: the steps 0, .., n as one block at the base (`Cb.BkA` of
Cb/Ld/LdLkpTreeP.lean).

Main names:
  `Spec.ldLkpTie_ok`: the conditions of the sumcheck hold at every step (no variable; degrees 1 and
    3 in the dummy variable).
  `Spec.ldLkpTie_step`: under `D.StepTo l`: one step, with the step without rounds after it: good
    for each fixed tuple of messages (`GoodAt`), the identity extracts.
  `Spec.ldLkpTie_chain`: under `D.StepTo n`: the steps 0, .., n.
  `Spec.ldLkpTie_rounds`: 3 (n + 1) rounds.
  Errors of a step, counts: 1 of |E|; the degree (1, then 3) of |E| - 1; 0.

Limits: this file says nothing on zero knowledge: under the conditions of `Spec.psc_our_mm`
(Cb/Ld/LdPscZk.lean), every step is a masked block, in this sense: its sumcheck has `Honest.MM` (its
item is "masked messages": Cb/Ld/LdPscZk*.lean); the item for the chain is not here.
That PK, PT_j are the products of a lookup, and `D.StepTo` for them, is the caller's matter
(`Cb.honest_rows`, Cb/Gen/LkpAlgProofs.lean, gives it for `Cb.Lkp.hU` at n = W - 1, for W ≥ 1).
The bit positions at or above W get no claim here.
The following is declared as a reading of ours. A write-up of ours (lean/CREDITS.md) has
one sentence on this chain (sumchecks without variable on values that are never sent; a summand of
the kind "a square
times a factor"). Which values, in which order, with which masks is not written there: the chain
above is our reading.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdLkpTreeP
import Cb.Ld.LdLineAt
import Cb.Ld.LdSigStep

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob

noncomputable section

/-- The data of a tie. -/
structure TieP (E : Type) [Field E] [Fintype E] where
  St0 : Type
  J : Type
  [finJ : Fintype J]
  /-- The virtual scalars. -/
  PK : St0 → (J → E) → E
  PT : St0 → (J → E) → ℕ → E
  Q  : St0 → (J → E) → ℕ → E
  /-- Own masks of step 0, and of step j + 1: the coefficients of the hiding polynomial; one entry
  for each of the two values. -/
  wS  : PIdx (([] : List (PFmt E)) ++ [pDummy E 1]) → J
  cS  : Bool → J
  wAt : ℕ → PIdx (([] : List (PFmt E)) ++ [pDummy E 3]) → J
  cAt : ℕ → Bool → J

attribute [instance] TieP.finJ

variable {E : Type} [Field E] [Fintype E]

namespace TieP
variable (D : TieP E)

/-- The one condition, below n. -/
def StepTo (n : ℕ) : Prop := ∀ st m j, j < n → D.Q st m j = D.Q st m (j + 1) ^ 2 * D.PT st m j

/-- A step with its readers. -/
structure Lv where
  T : PscOur E
  toJ : T.J → D.J
  base : T.St → D.St0
  /-- The value that the next step takes up; the value whose claim rides along. -/
  nx : T.A
  pt : T.A

/-- Step 0: PK - Q_0. -/
def TS : PscOur E where
  St := D.St0
  J := D.J
  fmt := []
  dat := fun _ => ()
  A := Bool
  B := Empty
  F := fun st m b _ => if b then D.Q st m 0 else D.PK st m
  Fb := fun _ _ b _ => b.elim
  S0 := fun _ _ v => v false - v true
  S1 := fun _ _ _ b => b.elim
  DY := 1
  slS := fun _ _ => 0
  wAt := D.wS
  cAt := D.cS

def lv0 : D.Lv := ⟨D.TS, id, id, true, false⟩

open Classical in
/-- Step j + 1, after the step L: Q_(j+1)² · PT_j, with the form β of L at the mask entry of the
value taken up. -/
def TN (j : ℕ) (L : D.Lv) : PscOur E where
  St := L.T.par.Out
  J := D.J
  fmt := []
  dat := fun _ => ()
  A := Bool
  B := Empty
  F := fun o m b _ => if b then D.PT (L.base o.st) m j else D.Q (L.base o.st) m (j + 1)
  Fb := fun _ _ b _ => b.elim
  S0 := fun _ _ v => v false ^ 2 * v true
  S1 := fun _ _ _ b => b.elim
  DY := 3
  slS := fun o i => if i = L.toJ (L.T.cAt L.nx) then L.T.lst o.st (L.T.par.hp o.st o.pt) else 0
  wAt := D.wAt j
  cAt := D.cAt j

def lvS (j : ℕ) (L : D.Lv) : D.Lv := ⟨D.TN j L, id, fun o => L.base o.st, false, true⟩

/-- The steps. -/
def lv : ℕ → D.Lv
  | 0 => D.lv0
  | j + 1 => D.lvS j (lv j)

/-- The joint's own claim before step l. -/
def claim : (l : ℕ) → E × (D.lv l).T.St → (D.J → E) → Prop
  | 0 => fun x m => D.PK x.2 m - D.Q x.2 m 0 = x.1
  | l + 1 =>
    fun x m =>
      D.Q ((D.lv (l + 1)).base x.2) m l +
          ∑ j, (D.lv (l + 1)).T.slS x.2 j * m ((D.lv (l + 1)).toJ j) = x.1

section Base
variable (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E)

/-- The entries in the naming of step l. -/
def msgAt (l : ℕ) : M → (D.lv l).T.J → E := fun ms j => msg ms ((D.lv l).toJ j)

variable {Ex M Wp Kc}

/-- What rides along after step l: what rode before, the row on the hiding coefficients, the masked
claim on the value that is not taken up. -/
def after (l : ℕ) (A : Rels Kc (D.lv l).T.St Ex (M × Wp)) :
    Rels Kc (D.lv l).T.par.Out Ex (M × Wp) :=
  ⟨fun o y w =>
      A.rel o.st y w ∧
      (D.lv l).T.par.UHolds o (D.msgAt M msg l w.1) ∧
      (D.lv l).T.par.EHolds o (D.msgAt M msg l w.1) (D.lv l).pt,
    fun a w =>
      A.relR (a.1.st, a.2) w ∧
      (D.lv l).T.par.UHolds a.1 (D.msgAt M msg l w.1) ∧
      (D.lv l).T.par.EHolds a.1 (D.msgAt M msg l w.1) (D.lv l).pt,
    fun a => A.on (a.1.st, a.2),
    A.core⟩

/-- What rides along before step l. -/
def ride (A0 : Rels Kc D.St0 Ex (M × Wp)) : (l : ℕ) → Rels Kc (D.lv l).T.St Ex (M × Wp)
  | 0 => A0
  | l + 1 => D.after msg l (ride A0 l)

/-- The joint before step l: the step's own claim, and what rides along. -/
def jtAt (A0 : Rels Kc D.St0 Ex (M × Wp)) (l : ℕ) : Rels Kc (E × (D.lv l).T.St) Ex (M × Wp) :=
  ⟨fun x y w => (D.ride msg A0 l).rel x.2 y w ∧ D.claim l x (msg w.1),
    fun a w => (D.ride msg A0 l).relR (a.1.2, a.2) w ∧ D.claim l a.1 (msg w.1),
    fun a => (D.ride msg A0 l).on (a.1.2, a.2),
    (D.ride msg A0 l).core⟩

/-- The step without rounds after step l: the scalar sent for the value taken up is the next target.
-/
def nxt (l : ℕ) : (D.lv l).T.par.Out → E × (D.lv (l + 1)).T.St := fun o => (o.vals (D.lv l).nx, o)

variable (Ex Wp Kc) in
/-- Step l, with the step without rounds after it. -/
def stepA (l : ℕ) : BkA Kc M (E × (D.lv l).T.St) (E × (D.lv (l + 1)).T.St) Ex Wp :=
  ⟨((D.lv l).T.par.psc Ex).post (fun o => some (D.nxt l o)) (ExtMap.id Ex),
    ((D.lv l).T.par.hon Ex fun w => D.msgAt M msg l w.1).post (fun o => some (D.nxt l o))
      (ExtMap.id Ex) fun o => (D.nxt l o.1, o.2),
    ((D.lv l).T.par.nums Ex Kc).post (fun o => some (D.nxt l o)) (ExtMap.id Ex)⟩

variable (Ex Wp Kc) in
/-- The tie: the steps 0, .., n. -/
def tieA (n : ℕ) : BkA Kc M (E × (D.lv 0).T.St) (E × (D.lv (n + 1)).T.St) Ex Wp :=
  BkA.chain (fun l => E × (D.lv l).T.St) (D.stepA Ex Wp Kc msg) n

end Base
end TieP
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp

section
variable (E : Type) [Field E] [Fintype E]

/-- The first joint's own claim is the sum claim of step 0. -/
def ldLkpTie_sum0 : Prop :=
  ∀ (D : TieP E) (x : E × (D.lv 0).T.St) (m : D.J → E),
    (D.lv 0).T.SumHolds x (fun j => m ((D.lv 0).toJ j)) ↔ D.claim 0 x m

/-- The masked claim on Q_l is the sum claim of step l + 1, where Q_l = Q_(l+1)² · PT_l. -/
def ldLkpTie_sum : Prop :=
  ∀ (D : TieP E) (l : ℕ) (x : E × (D.lv (l + 1)).T.St) (m : D.J → E),
    D.Q ((D.lv (l + 1)).base x.2) m l =
      D.Q ((D.lv (l + 1)).base x.2) m (l + 1) ^ 2 * D.PT ((D.lv (l + 1)).base x.2) m l →
    ((D.lv (l + 1)).T.SumHolds x (fun j => m ((D.lv (l + 1)).toJ j)) ↔ D.claim (l + 1) x m)

/-- The form of the claim before step l + 1: β of step l at the mask entry of the value taken up, 0
elsewhere. -/
def ldLkpTie_form : Prop :=
  ∀ (D : TieP E) (l : ℕ) (o : (D.lv l).T.par.Out) (m : D.J → E), ∑ j,
      (D.lv (l + 1)).T.slS o j * m ((D.lv (l + 1)).toJ j) =
    (D.lv l).T.lst o.st ((D.lv l).T.par.hp o.st o.pt) *
      m ((D.lv l).toJ ((D.lv l).T.cAt (D.lv l).nx))

def ldLkpTie_ok : Prop :=
  ∀ (D : TieP E) (l : ℕ), (D.lv l).T.VarsOK ∧ (D.lv l).T.ValInj ∧ (D.lv l).T.DegX ∧ (D.lv l).T.DegY

/-- One step. -/
def ldLkpTie_step : Prop :=
  ∀ (D : TieP E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E)
      (A0 : Rels Kc D.St0 Ex (M × Wp)) (l : ℕ),
    D.StepTo l → (D.stepA Ex Wp Kc msg l).Good (D.jtAt msg A0 l) (D.jtAt msg A0 (l + 1))

/-- The tie, at the base. -/
def ldLkpTie_chain : Prop :=
  ∀ (D : TieP E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E)
      (A0 : Rels Kc D.St0 Ex (M × Wp)) (n : ℕ),
    D.StepTo n → (D.tieA Ex Wp Kc msg n).Good (D.jtAt msg A0 0) (D.jtAt msg A0 (n + 1))

/-- The tie over a signature (`GoodB`, Ior/Masked.lean; `Sig`, Cb/Ld/LdSig.lean), under
`D.StepTo n`. -/
def ldLkpTie_sig : Prop :=
  ∀ (D : TieP E) (S : Sig E) (E₀ : ExtSpec) (Wp Kc : Type) (msg : S.Msg → D.J → E)
      (A0 : Rels Kc D.St0 E₀ (S.Msg × Wp)) (n : ℕ),
    D.StepTo n →
    GoodB ((D.tieA E₀ Wp Kc msg n).R.keep S.Smp S.ext) (S.liftH (D.tieA E₀ Wp Kc msg n).H)
      (S.over (D.jtAt msg A0 0)) (S.over (D.jtAt msg A0 (n + 1))) (fun _ _ w => w)
      ((D.tieA E₀ Wp Kc msg n).P.keep S.Smp S.ext)

def ldLkpTie_rounds : Prop :=
  ∀ (D : TieP E) (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E) (n : ℕ),
    (D.tieA Ex Wp Kc msg n).R.shape.length = 3 * (n + 1)

/-- What rides along after a step, written out: the masked claim on PK (after step 0), on PT_j
(after step j + 1). -/
def ldLkpTie_ride : Prop :=
  ∀ (D : TieP E) (m : D.J → E),
    (∀ o : (D.lv 0).T.par.Out,
      (D.lv 0).T.par.EHolds o (fun j => m ((D.lv 0).toJ j)) (D.lv 0).pt ↔
      D.PK o.st m + m (D.cS false) * (D.lv 0).T.lst o.st ((D.lv 0).T.par.hp o.st o.pt) =
        o.vals (D.lv 0).pt) ∧
    ∀ (j : ℕ) (o : (D.lv (j + 1)).T.par.Out),
      (D.lv (j + 1)).T.par.EHolds o (fun i => m ((D.lv (j + 1)).toJ i)) (D.lv (j + 1)).pt ↔
      D.PT ((D.lv (j + 1)).base o.st) m j +
          m (D.cAt j true) * (D.lv (j + 1)).T.lst o.st ((D.lv (j + 1)).T.par.hp o.st o.pt) =
        o.vals (D.lv (j + 1)).pt

end
end Cb.Spec
