-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Caller.lean: kind K5: a caller of the proved chain's own type, made of the
public
record at a place, over the committed messages; and what the joint in front then says at that
caller. General
in the message type and in the first statement.

Main names:
  `baseOf S pl C npl zOf`: the sizes are L5.dimOf S (S: the plan's shape); four variables number a
    bit; its
    message is the committed symbols; the entries are the cells behind them; the cell named c is
      read at
    pl (L5.addrA S c), as Johnson/Road/Rows/AttStartBase.lean reads it.
  `callerOf S pl C npl zOf maskOf symsOf LM LD LE ns N`: closedOf of that base: over any type of
    messages, read
    by maskOf and symsOf; every mask entry's place is a slot's number.
  `caller_t`: the cells are t c = cellValS (symsOf m) (pl (addrA S c) …): att_ord_base's premise ht,
    by
    definition.
  `caller_front`: what the chain's first joint says there gives att_ord_base's own1 and own2 in its
    own
    letters, where a position has at most 16 bits.
  `caller_know`: the chain's knowledge soundness at that caller.
  `caller_atPlan_full`, `caller_atPlan_small`: AtPlan at the caller, at the two stored
    configurations'
    records, where the shape's six sizes are those named.
  `callerProd`: the instance whose message is a mask beside the symbols.

Limits: it is not a closed caller. Still parameters: maskOf, symsOf, zOf · pl (PlaceOK is
AttStartBase.lean's
premise) · C (the lookup's calls) · LM, LD, LE · the size of the committed matrices. That L5.dimOf
of the
planner's shape is the tuple named, that the neighbouring kinds' statements are made at this caller,
and that
the first statement's lookup point is what the lookup's kind hands on (LookPts), are not shown in
this file or in what it imports.
Sources: Johnson/Road/Lane5AttDef.lean (L5.dimOf, L5.addrA); Cb/Pv/Tail/InLink.lean (Syms,
cellValS); Agree.lean
(JCell); Cb/Pv/Att/OwnAt.lean; and what Att/K05Front.lean and Att/K05Closed.lean name.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Road.Rows.AttStartBase
import Johnson.Desc.First.Att.K05Front
import Johnson.Desc.First.Att.K05Numbers
import Johnson.Desc.First.Att.K05Condition

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole IOR OnBytes OnBytes.Model Cb.Pv.Att Inst.Model Inst.Model.AttSeg
open Cb.Pv.Tail (Size Syms JCell cellValS)

variable {K : Type} [Field K] [Fintype K] {s : Size} {X Mg : Type}

/-- The parameters over the committed symbols. The places of mask entries and the three free linear
claims are idle here:
closedOf lays them. -/
noncomputable def baseOf (S : Attention.Shape) (pl : ℕ → ℕ → ℕ → JCell s) (C : AttSeg.Calls) (npl : ℕ)
    (zOf : X → ℕ → K) : OwnPar K (Syms K s) X where
  D := OnBytes.Road.L5.dimOf S
  C := C
  J := Option (JCell s)
  msg := fun y j => j.elim 0 (cellValS y)
  rd := fun e c => e (some (pl (OnBytes.Road.L5.addrA S c).1 (OnBytes.Road.L5.addrA S c).2.1
    (OnBytes.Road.L5.addrA S c).2.2))
  zOf := zOf
  npl := npl
  kap := 4
  wAt := fun _ _ => none
  cAt := fun _ _ => none
  w18 := fun _ => none
  c18 := fun _ => none
  wH := fun _ => none
  cH := fun _ => none
  kM := fun _ => none
  kD := fun _ => none
  kE := fun _ => none
  kV := fun _ => none
  kF := fun _ => none
  LM := fun _ _ _ => True
  LD := fun _ _ _ => True
  LE := fun _ _ _ => True

section Caller
variable (S : Attention.Shape) (pl : ℕ → ℕ → ℕ → JCell s) (C : AttSeg.Calls) (npl : ℕ) (zOf : X → ℕ → K)
  (maskOf : Mg → ℕ → K) (symsOf : Mg → Syms K s)
  (LM : Seen K X → (Fin (3 * npl + 7) → K) → Mg → Prop)
  (LD : Seen K X → (Fin 7 → K) → Mg → Prop)
  (LE : Seen K X → (Fin (5 + (OnBytes.Road.L5.dimOf S).lT + 2) → K) → Mg → Prop) (ns : ℕ) (N : Nums)

/-- **The caller**: over any messages, read by maskOf and symsOf; every mask entry's place is a
slot's number. -/
noncomputable def callerOf : OwnPar K Mg X :=
  closedOf (baseOf S pl C npl zOf) ⟨maskOf, symsOf, LM, LD, LE⟩ ns N

/-- At the caller the cells are read off the committed symbols at the meaning row's own places: its
premise ht. -/
theorem caller_t (m : Mg) (c : AttSeg.Raw) :
    (callerOf S pl C npl zOf maskOf symsOf LM LD LE ns N).tOf m c =
      cellValS (symsOf m)
        (pl (OnBytes.Road.L5.addrA S c).1 (OnBytes.Road.L5.addrA S c).2.1 (OnBytes.Road.L5.addrA S c).2.2) :=
  rfl

/-- **What the joint in front says at the caller**: the meaning row's own1 and own2, in just its
letters. -/
theorem caller_front (hT : (OnBytes.Road.L5.dimOf S).lT ≤ 16) (x : X) (m : Mg)
    (h : ((callerOf S pl C npl zOf maskOf symsOf LM LD LE ns N).own
      (theMeans K (callerOf S pl C npl zOf maskOf symsOf LM LD LE ns N).D
        (callerOf S pl C npl zOf maskOf symsOf LM LD LE ns N).C
        (callerOf S pl C npl zOf maskOf symsOf LM LD LE ns N).kap)).ch.Todo x m) :
    (∀ k b g i, (Idn.at1 k b g i).Valid (OnBytes.Road.L5.dimOf S) →
      idnVal (OnBytes.Road.L5.dimOf S) ((callerOf S pl C npl zOf maskOf symsOf LM LD LE ns N).tOf m)
        (.at1 k b g i) = 0) ∧
    ∀ b g i, (Idn.at2 b g i).Valid (OnBytes.Road.L5.dimOf S) →
      idnVal (OnBytes.Road.L5.dimOf S) ((callerOf S pl C npl zOf maskOf symsOf LM LD LE ns N).tOf m)
        (.at2 b g i) = 0 :=
  ⟨fun k b g i hv => own1_of_todo (callerOf S pl C npl zOf maskOf symsOf LM LD LE ns N) (by
      show (OnBytes.Road.L5.dimOf S).lT ≤ 2 ^ 4
      omega) x m h k b g i hv,
    fun b g i hv => own2_of_todo (callerOf S pl C npl zOf maskOf symsOf LM LD LE ns N) x m h b g i hv⟩

/-- The proved chain's knowledge soundness at the caller: no further condition. -/
theorem caller_know (Kc X0 Wp : Type) (Ex : ExtSpec) (A0 : Rels Kc X0 Ex (Mg × Wp)) (pr : X → X0)
    (Dn : X → Mg → Prop) :
    KnowAt (((callerOf S pl C npl zOf maskOf symsOf LM LD LE ns N).own (theMeans K _ _ _)).ch.R Ex)
      (jt A0 pr fun x m => Dn x m ∧
        ((callerOf S pl C npl zOf maskOf symsOf LM LD LE ns N).own (theMeans K _ _ _)).ch.Todo x m)
      (jt A0 (fun e => pr (((callerOf S pl C npl zOf maskOf symsOf LM LD LE ns N).own (theMeans K _ _ _)).ch.back e))
        (((callerOf S pl C npl zOf maskOf symsOf LM LD LE ns N).own (theMeans K _ _ _)).ch.Last Dn))
      (fun _ _ _ wp => wp) (((callerOf S pl C npl zOf maskOf symsOf LM LD LE ns N).own (theMeans K _ _ _)).ch.eps Ex) :=
  ownAt_knowAt (callerOf S pl C npl zOf maskOf symsOf LM LD LE ns N) Ex A0 pr Dn

end Caller

/-- **The numeric condition at the caller, at the full-size stored set's record**: where the plan's
shape has the sizes
lgk · lnT - 1 · lB · ldh · HA · Lam = 3 3 6 7 5 4 and there are two plane messages. -/
theorem caller_atPlan_full (S : Attention.Shape) (pl : ℕ → ℕ → ℕ → JCell s) (C : AttSeg.Calls) (zOf : X → ℕ → K)
    (maskOf : Mg → ℕ → K) (symsOf : Mg → Syms K s) (LM : Seen K X → (Fin (3 * 2 + 7) → K) → Mg → Prop)
    (LD : Seen K X → (Fin 7 → K) → Mg → Prop)
    (LE : Seen K X → (Fin (5 + (OnBytes.Road.L5.dimOf S).lT + 2) → K) → Mg → Prop) (ns : ℕ) (N : Nums)
    (u0 : ℕ) (hS : OnBytes.Road.L5.dimOf S = ⟨3, 3, 6, 7, 5, 4, u0⟩) (p : Par) (hp : p.own = fullRecord) :
    AtPlan (callerOf S pl C 2 zOf maskOf symsOf LM LD LE ns N) p :=
  atPlan_full (callerOf S pl C 2 zOf maskOf symsOf LM LD LE ns N) u0 hS rfl rfl p hp

/-- The same at the small plan's record. -/
theorem caller_atPlan_small (S : Attention.Shape) (pl : ℕ → ℕ → ℕ → JCell s) (C : AttSeg.Calls) (zOf : X → ℕ → K)
    (maskOf : Mg → ℕ → K) (symsOf : Mg → Syms K s) (LM : Seen K X → (Fin (3 * 2 + 7) → K) → Mg → Prop)
    (LD : Seen K X → (Fin 7 → K) → Mg → Prop)
    (LE : Seen K X → (Fin (5 + (OnBytes.Road.L5.dimOf S).lT + 2) → K) → Mg → Prop) (ns : ℕ) (N : Nums)
    (u0 : ℕ) (hS : OnBytes.Road.L5.dimOf S = ⟨1, 1, 4, 7, 2, 4, u0⟩) (p : Par) (hp : p.own = smallRecord) :
    AtPlan (callerOf S pl C 2 zOf maskOf symsOf LM LD LE ns N) p :=
  atPlan_small (callerOf S pl C 2 zOf maskOf symsOf LM LD LE ns N) u0 hS rfl rfl p hp

/-- The instance whose message is a mask beside the symbols and whose first statement is the
lookup's point. -/
noncomputable def callerProd (S : Attention.Shape) (pl : ℕ → ℕ → ℕ → JCell s) (C : AttSeg.Calls) (npl : ℕ)
    (LM : Seen K (ℕ → K) → (Fin (3 * npl + 7) → K) → (ℕ → K) × Syms K s → Prop)
    (LD : Seen K (ℕ → K) → (Fin 7 → K) → (ℕ → K) × Syms K s → Prop)
    (LE : Seen K (ℕ → K) → (Fin (5 + (OnBytes.Road.L5.dimOf S).lT + 2) → K) → (ℕ → K) × Syms K s → Prop) (ns : ℕ)
    (N : Nums) : OwnPar K ((ℕ → K) × Syms K s) (ℕ → K) :=
  callerOf S pl C npl id Prod.fst Prod.snd LM LD LE ns N

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.caller_atPlan_full
#print axioms VerifiableInference.Desc.First.Att.P.caller_t
#print axioms VerifiableInference.Desc.First.Att.P.caller_front
#print axioms VerifiableInference.Desc.First.Att.P.caller_know
