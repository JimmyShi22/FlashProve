-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/ValueMasks.lean: AT THE VALUE OF Johnson/Road/K4/Value.lean, WHAT THE MESSAGES HOLD
AT EACH TYPED NAME OF A MASK ENTRY IS THE OWN MASK ROW's ENTRY AT A SLOT's NUMBER. Two theorems on
the two kinds of names, and one for each of the value's eighteen letters that name a mask entry;
each of these by unfolding and the first two.

  `msg_sl`: for n ≤ ns: the messages at `sl n` are the mask row's entry n. `msg_ix`: for n ≤ nx: at
    `ix n` the index-mask message's entry n.
  `msg_mkS`, `msg_wS`, `msg_cS` (the squares: the sums' scalars, the sumcheck's own coefficients,
    its end values) · `msg_mkP`, `msg_rP`, `msg_wP`, `msg_cP` (the products: the scalars, the
    claimed sum, own, end values) · `msg_rT`, `msg_wT`, `msg_cT` (the terms) · `msg_wI`, `msg_cI`
    (the batched sumcheck) · `msg_w5`, `msg_c5`, `msg_w6`, `msg_c6` (the two product layers) ·
    `msg_w7`, `msg_c7` (the merge: own; its shown value's mask is an entry of the index-mask
    message).

Limits. Each asks that the slot's number is at most ns (nx): beyond it `sl` names the last entry.
That the numbers are a hearing's slots is another file's (Johnson/Road/K4/SlotsTie.lean).

-/
import Johnson.Road.K4.Value

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open OnBytes.Tie.Pv (slotP)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type}

namespace Plan4
variable (Q : Plan4 E M X) (m : M)

/-- The messages at a slot's name. -/
theorem msg_sl {n : ℕ} (h : n ≤ Q.ns) : Q.msg m (Q.sl n) = Q.maskAt m n := by
  show Q.maskAt m (min n Q.ns) = Q.maskAt m n
  rw [Nat.min_eq_left h]

/-- The messages at the name of an entry of the index-mask message. -/
theorem msg_ix {n : ℕ} (h : n ≤ Q.nx) : Q.msg m (Q.ix n) = Q.idxAt m n := by
  show Q.idxAt m (min n Q.nx) = Q.idxAt m n
  rw [Nat.min_eq_left h]

theorem msg_mkS (i : Fin Q.D.nNu) (s : Fin 9) (h : Q.sW + 9 * i + s ≤ Q.ns) :
    Q.full.msg m (Q.full.mkS i s) = Q.maskAt m (Q.sW + 9 * i + s) := Q.msg_sl m h

theorem msg_wS (q) (h : slotP _ Q.fS q ≤ Q.ns) :
    Q.full.msg m (Q.full.wS q) = Q.maskAt m (slotP _ Q.fS q) := Q.msg_sl m h

theorem msg_cS (b : Bool) (h : Q.vS + (if b then 1 else 0) ≤ Q.ns) :
    Q.full.msg m (Q.full.cS b) = Q.maskAt m (Q.vS + (if b then 1 else 0)) := Q.msg_sl m h

theorem msg_mkP (i : Fin (Q.D.nNu * 7)) (h : Q.sP + i ≤ Q.ns) :
    Q.full.msg m (Q.full.mkP i) = Q.maskAt m (Q.sP + i) := Q.msg_sl m h

theorem msg_rP (h : Q.cP0 ≤ Q.ns) : Q.full.msg m Q.full.rP = Q.maskAt m Q.cP0 := Q.msg_sl m h

theorem msg_wP (q) (h : slotP _ Q.fP q ≤ Q.ns) :
    Q.full.msg m (Q.full.wP q) = Q.maskAt m (slotP _ Q.fP q) := Q.msg_sl m h

theorem msg_cP (x : Fin Q.D.nNu × Fin 4) (h : Q.vP + 4 * x.1 + x.2 ≤ Q.ns) :
    Q.full.msg m (Q.full.cP x) = Q.maskAt m (Q.vP + 4 * x.1 + x.2) := Q.msg_sl m h

theorem msg_rT (h : Q.cT0 ≤ Q.ns) : Q.full.msg m Q.full.rT = Q.maskAt m Q.cT0 := Q.msg_sl m h

theorem msg_wT (q) (h : slotP _ Q.fT q ≤ Q.ns) :
    Q.full.msg m (Q.full.wT q) = Q.maskAt m (slotP _ Q.fT q) := Q.msg_sl m h

theorem msg_cT (a : ShA Q.D) (h : Q.vT + Q.numT a ≤ Q.ns) :
    Q.full.msg m (Q.full.cT a) = Q.maskAt m (Q.vT + Q.numT a) := Q.msg_sl m h

theorem msg_wI (q) (h : slotP _ Q.fI q ≤ Q.ns) :
    Q.full.msg m (Q.full.wI q) = Q.maskAt m (slotP _ Q.fI q) := Q.msg_sl m h

theorem msg_cI (a : IA Q.D ⊕ IB Q.D) (h : Q.vI + Q.numI a ≤ Q.ns) :
    Q.full.msg m (Q.full.cI a) = Q.maskAt m (Q.vI + Q.numI a) := Q.msg_sl m h

theorem msg_w5 (q) (h : slotP _ Q.f5 q ≤ Q.ns) :
    Q.full.msg m (Q.full.w5 q) = Q.maskAt m (slotP _ Q.f5 q) := Q.msg_sl m h

theorem msg_c5 (b : Bool) (h : Q.v5 + (if b then 1 else 0) ≤ Q.ns) :
    Q.full.msg m (Q.full.c5 b) = Q.maskAt m (Q.v5 + (if b then 1 else 0)) := Q.msg_sl m h

theorem msg_w6 (q) (h : slotP _ Q.f6 q ≤ Q.ns) :
    Q.full.msg m (Q.full.w6 q) = Q.maskAt m (slotP _ Q.f6 q) := Q.msg_sl m h

theorem msg_c6 (b : Bool) (h : Q.v6 + (if b then 1 else 0) ≤ Q.ns) :
    Q.full.msg m (Q.full.c6 b) = Q.maskAt m (Q.v6 + (if b then 1 else 0)) := Q.msg_sl m h

theorem msg_w7 (q) (h : slotP _ Q.f7 q ≤ Q.ns) :
    Q.full.msg m (Q.full.w7 q) = Q.maskAt m (slotP _ Q.f7 q) := Q.msg_sl m h

theorem msg_c7 (h : Q.v7 ≤ Q.nx) : Q.full.msg m Q.full.c7 = Q.idxAt m Q.v7 := Q.msg_ix m h

end Plan4
end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4.msg_sl
#print axioms OnBytes.Road.K4.Plan4.msg_cP
#print axioms OnBytes.Road.K4.Plan4.msg_c7
