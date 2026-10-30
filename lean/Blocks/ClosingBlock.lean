-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/ClosingBlock.lean: the closing of a segment, as a block, with soundness, completeness and
masked form. (`Block.Clean`: Blocks/Block.lean; `Hon.AccOn`, `Hon.Masked`: Blocks/BlockHon.lean.
Words of this library: lean/GLOSSARY.md.)

What the closing does. A segment has recorded claims LIN(f) and REL(f; ∑ c o_i o_j) on opened forms
(Blocks/Form.lean: the deferred claims). The closing turns them into one linear claim.
 (1) For each REL the prover sends two auxiliary masked scalars, with values ϑ1 and ϑ0.
 (2) The verifier sends the product challenge ς.
 (3) For each opened form f_i the prover sends ô_i, honestly ς val(f_i) + η_i with a pad η_i of its
     own.
 (4) The verifier sends one coefficient for each claim.
The affine expression of LIN(f) is f, that of the opened form f_i is ς f_i + η_i - ô_i, that of a
REL is ς² f + ς ϑ1 + ϑ0 - ∑ c ô_i ô_j. The linear claim says that their sum under the coefficients
has the value 0.

The two blocks and the relation between them. `closeA` is (1), (2) and `closeB` is (3), (4). After ς
the relation `Mid` says: every LIN is true, and for every REL the polynomials T² val(f) + T ϑ1 + ϑ0
and ∑ c (T val(f_i) + η_i)(T val(f_j) + η_j) agree at T = ς. It speaks of true objects only, not of
the ô, which are not yet sent.
 * `closeA` is sound from "all recorded claims are true" to `Mid`, with at most 2 bad values of ς:
   those at which the two polynomials of one REL whose relation is false agree.
   (One such REL is chosen; which one does not matter.)
 * `closeB` is sound from `Mid` to "the linear claim is true", with at most |E|^(n - 1) bad tuples
   of n coefficients, a fraction 1/|E|: those under which the sum vanishes although some affine
   expression has a value other than 0. (If nothing at all is on record, n = 0, there is one empty
   tuple, the bound is 1 and says nothing.) The equation ô_i = ς val(f_i) + η_i is a step of this
   proof.

Honest side. ϑ1 = ∑ c (o_i η_j + o_j η_i) and ϑ0 = ∑ c η_i η_j read the pads of the ô, which are
sent later. So in the fixed order of the pads the pads of the ô come first, and masked form is
composed against the order of the blocks (`Hon.Masked.comp'`). Masked form: `masked_honClose`,
`masked_honClosing`: see their statements.

All names of this file are in the namespace `Blocks.Closing`.

One round more. The record is an input of the closing, so it is complete before the prover message
with the auxiliary scalars: further masked scalars that are opened and are the first argument of a
REL need a round of their own before the closing. That is one round more than if they were sent in
the same prover message as the auxiliary scalars.

The record as lists. `closing` takes the record as lists (`Blocks.Ledger`). The numbers of claims
are parameters, because the shape depends on them, and the verifier rejects if the lengths differ.

The counting cores are `Alg.count_roots_le` and `Alg.count_affine_form_le_pow` (Alg/Poly.lean).
-/
import Alg.Poly
import Prob.Count
import Blocks.Form
import Blocks.BlockLib

set_option autoImplicit false

namespace Blocks

open Iop Prob

namespace Closing

/-! ## 1. Two small facts -/

/-- A polynomial of degree exactly 2 has at most two zeros. -/
theorem cnt_quadratic_le {E : Type} [Field E] [Finite E] {a : E} (ha : a ≠ 0) (b c : E) :
    cnt (fun T : E => a * T ^ 2 + b * T + c = 0) ≤ 2 := by
  have hq : (Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c) ≠
      0 := by
    intro h0
    have h1 := Polynomial.natDegree_quadratic (b := b) (c := c) ha
    rw [h0, Polynomial.natDegree_zero] at h1
    exact absurd h1 (by norm_num)
  refine le_trans (le_of_eq (cnt_congr fun T => ?_))
    (Alg.count_roots_le hq Polynomial.natDegree_quadratic_le)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]

/-- The relation w = T u + v between three vectors, entry by entry, holds for the vectors read on ℕ.
-/
theorem nat_affine {E : Type} [Field E] {n : ℕ} (T : E) {u v w : Fin n → E}
    (h : ∀ i, w i = T * u i + v i) (i : ℕ) :
    nat w i = T * nat u i + nat v i := by
  unfold nat
  by_cases hi : i < n
  · simp only [dif_pos hi, h]
  · simp only [dif_neg hi, mul_zero, add_zero]

/-! ## 2. The record, with index types -/

/-- The recorded claims: LIN indexed by L, nO opened forms, REL indexed by R; the terms of a REL
name opened forms by their numbers. -/
structure Recorded (N E L R : Type) (nO : ℕ) where
  lin : L → Form N E
  opn : Fin nO → Form N E
  rel : R → Form N E
  terms : R → List (E × ℕ × ℕ)

/-- The places of the pads of the closing among the entries (fixed by the public parameters): two
for each REL (true: ϑ1, false: ϑ0), one for each opened form. -/
structure Places (N R : Type) (nO : ℕ) where
  aux : R × Bool → N
  opn : Fin nO → N

section Core

variable {N E L R : Type} {nO : ℕ} [Fintype N] [DecidableEq N] [Field E] [Fintype E] [DecidableEq E]
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

namespace Recorded

/-- The values of the opened forms. -/
def ov (x : Recorded N E L R nO) (y : N → E) : ℕ → E := nat fun i => Form.val y (x.opn i)

/-- All recorded claims are true. -/
def True (x : Recorded N E L R nO) (y : N → E) : Prop :=
  (∀ l, Form.val y (x.lin l) = 0) ∧ ∀ r, Form.val y (x.rel r) = termSum (x.ov y) (x.terms r)

end Recorded

variable (pl : Places N R nO)

/-- The pads of the opened forms. -/
def Places.padv (y : N → E) : ℕ → E := nat fun i => y (pl.opn i)

/-- The value of an auxiliary masked scalar. -/
def Places.theta (s : R × Bool → E) (y : N → E) (k : R × Bool) : E := s k - y (pl.aux k)

/-! ## 3. The auxiliary scalars and the product challenge -/

variable (E R) in
/-- (1), (2): two scalars for each REL; then ς. -/
abbrev rAux : Round := vRound E Empty (fun a => Empty.elim a) (fun a => Empty.elim a) (R × Bool) E

variable (N E L R nO) in
/-- The explicit part after ς: the record, the auxiliary scalars, ς. -/
abbrev XMid : Type := Recorded N E L R nO × (R × Bool → E) × E

variable (N E L R nO) in
/-- The first block of the closing. -/
@[reducible] def closeA : Block (Recorded N E L R nO) (N → E) (XMid N E L R nO) (N → E) :=
  Block.one (rAux E R) (fun x ς s => some (x, s, ς)) (fun y _ _ => y)

/-- The relation after ς: every LIN is true, and the two polynomials of every REL agree at ς. -/
def Mid (x : XMid N E L R nO) (y : N → E) : Prop :=
  (∀ l, Form.val y (x.1.lin l) = 0) ∧
  ∀ r, x.2.2 ^ 2 * Form.val y (x.1.rel r) +
      x.2.2 * pl.theta x.2.1 y (r, true) + pl.theta x.2.1 y (r, false) =
    termSum (fun i => x.2.2 * x.1.ov y i + pl.padv y i) (x.1.terms r)

omit [DecidableEq N] [Fintype L] [DecidableEq L] [DecidableEq R] in
/-- The product challenge: at most two values of ς are bad. -/
theorem clean_closeA : (closeA N E L R nO).Clean Recorded.True (Mid pl) (2, ()) := by
  refine Block.clean_one
    (fun x y m =>
      {ς | ∃ h : ∃ r, ¬ Form.val y (x.rel r) = termSum (x.ov y) (x.terms r),
        ς ^ 2 * Form.val y (x.rel h.choose) + ς * pl.theta m.2 y (h.choose, true) +
            pl.theta m.2 y (h.choose, false) =
          termSum (fun i => ς * x.ov y i + pl.padv y i) (x.terms h.choose)})
    2 (fun x y m => ?_) fun x y m c xo hc hxo hRo => ?_
  · by_cases h : ∃ r, ¬ Form.val y (x.rel r) = termSum (x.ov y) (x.terms r)
    · refine le_trans (cnt_mono fun ς hς => ?_) (cnt_quadratic_le (sub_ne_zero.mpr h.choose_spec)
        (pl.theta m.2 y (h.choose, true) - termCross (x.ov y) (pl.padv y) (x.terms h.choose))
        (pl.theta m.2 y (h.choose, false) - termSum (pl.padv y) (x.terms h.choose)))
      obtain ⟨_, hς⟩ := hς
      rw [termSum_line] at hς
      linear_combination hς
    · rw [cnt_false fun ς hς => h hς.1]
      exact Nat.zero_le _
  · obtain rfl := Option.some.inj hxo
    have hM : Mid pl (x, m.2, c) y := hRo
    exact ⟨hM.1, fun r => by_contra fun hr => hc ⟨⟨r, hr⟩, hM.2 _⟩⟩

/-! ## 4. The opened elements and the coefficients -/

variable (E L R nO) in
/-- (3), (4): one element for each opened form; then one coefficient for each claim. -/
abbrev rOpen : Round :=
  vRound E Empty (fun a => Empty.elim a) (fun a => Empty.elim a) (Fin nO) (L ⊕ Fin nO ⊕ R → E)

/-- The affine expressions of the claims. -/
def exprs (x : XMid N E L R nO) (oh : Fin nO → E) : L ⊕ Fin nO ⊕ R → Form N E
  | .inl l => x.1.lin l
  | .inr (.inl o) => x.2.2 • x.1.opn o + Form.ent (pl.opn o) - Form.const (oh o)
  | .inr (.inr r) =>
    x.2.2 ^ 2 • x.1.rel r + x.2.2 • Form.masked (x.2.1 (r, true)) (pl.aux (r, true)) +
      Form.masked (x.2.1 (r, false)) (pl.aux (r, false)) -
      Form.const (termSum (nat oh) (x.1.terms r))

/-- The linear claim of the segment, as a form that is claimed to have the value 0. -/
def linClaim (x : XMid N E L R nO) (oh : Fin nO → E) (a : L ⊕ Fin nO ⊕ R → E) : Form N E :=
  ∑ k, a k • exprs pl x oh k

omit [Fintype E] [DecidableEq E] [DecidableEq L] [DecidableEq R] in
/-- The value of the linear claim is the sum of the values of the affine expressions under the
coefficients. -/
theorem val_linClaim (x : XMid N E L R nO) (oh : Fin nO → E) (a : L ⊕ Fin nO ⊕ R → E) (y : N → E) :
    Form.val y (linClaim pl x oh a) = ∑ k, a k * Form.val y (exprs pl x oh k) := by
  unfold linClaim
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [map_smul, smul_eq_mul]

omit [Fintype E] [DecidableEq E] [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R] in
/-- The value of the affine expression of an opened form: ς val(f) + η - ô. -/
theorem val_exprs_opn (x : XMid N E L R nO) (oh : Fin nO → E) (y : N → E) (o : Fin nO) :
    Form.val y (exprs pl x oh (.inr (.inl o))) =
      x.2.2 * Form.val y (x.1.opn o) + y (pl.opn o) - oh o := by
  show Form.val y (x.2.2 • x.1.opn o + Form.ent (pl.opn o) - Form.const (oh o)) = _
  rw [map_sub, map_add, map_smul, smul_eq_mul, Form.val_ent, Form.val_const]

omit [Fintype E] [DecidableEq E] [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R] in
/-- The value of the affine expression of a REL: ς² val(f) + ς ϑ1 + ϑ0 - ∑ c ô_i ô_j. -/
theorem val_exprs_rel (x : XMid N E L R nO) (oh : Fin nO → E) (y : N → E) (r : R) :
    Form.val y (exprs pl x oh (.inr (.inr r))) =
      x.2.2 ^ 2 * Form.val y (x.1.rel r) + x.2.2 * pl.theta x.2.1 y (r, true) +
        pl.theta x.2.1 y (r, false) - termSum (nat oh) (x.1.terms r) := by
  show Form.val y
      (x.2.2 ^ 2 • x.1.rel r + x.2.2 • Form.masked (x.2.1 (r, true)) (pl.aux (r, true)) +
        Form.masked (x.2.1 (r, false)) (pl.aux (r, false)) -
        Form.const (termSum (nat oh) (x.1.terms r))) = _
  rw [map_sub, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, Form.val_masked,
    Form.val_masked, Form.val_const]
  rfl

variable (E L) in
/-- The second block of the closing. -/
@[reducible] def closeB : Block (XMid N E L R nO) (N → E) (Form N E) (N → E) :=
  Block.one (rOpen E L R nO) (fun x a oh => some (linClaim pl x oh a)) (fun y _ _ => y)

omit [Fintype E] [DecidableEq E] [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R] in
/-- If all affine expressions have the value 0, the relation after ς holds. -/
theorem mid_of_exprs {x : XMid N E L R nO} {oh : Fin nO → E} {y : N → E}
    (h : ∀ k, Form.val y (exprs pl x oh k) = 0) : Mid pl x y := by
  have hO : ∀ i, nat oh i = x.2.2 * x.1.ov y i + pl.padv y i := nat_affine x.2.2 fun o => by
    have h1 := h (.inr (.inl o))
    rw [val_exprs_opn] at h1
    exact (sub_eq_zero.mp h1).symm
  refine ⟨fun l => h (.inl l), fun r => ?_⟩
  have h1 := h (.inr (.inr r))
  rw [val_exprs_rel, termSum_congr hO] at h1
  exact sub_eq_zero.mp h1

/-- The coefficients: a fraction of at most 1/|E| of the tuples is bad (if nothing is on record, the
one empty tuple of coefficients counts as bad, and the bound says nothing). -/
theorem clean_closeB : (closeB E L pl).Clean (Mid pl) (fun g y => Form.val y g = 0)
    (Fintype.card E ^ (Fintype.card (L ⊕ Fin nO ⊕ R) - 1), ()) := by
  refine Block.clean_one
    (fun x y m =>
      {a : L ⊕ Fin nO ⊕ R →
        E | (fun k => Form.val y (exprs pl x m.2 k)) ≠ 0 ∧
        0 + ∑ k, a k * Form.val y (exprs pl x m.2 k) = 0})
    _ (fun x y m => ?_) fun x y m c xo hc hxo hRo => ?_
  · by_cases h : (fun k => Form.val y (exprs pl x m.2 k)) = 0
    · rw [cnt_false fun a ha => ha.1 h]
      exact Nat.zero_le _
    · exact (cnt_mono fun a ha => ha.2).trans (Alg.count_affine_form_le_pow 0 _ (Or.inr h))
  · obtain rfl := Option.some.inj hxo
    have hg : Form.val y (linClaim pl x m.2 c) = 0 := hRo
    refine mid_of_exprs pl (oh := m.2) fun k => ?_
    have h0 : (fun k => Form.val y (exprs pl x m.2 k)) = 0 := by
      by_contra hne
      exact hc ⟨hne, by rw [zero_add, ← val_linClaim]; exact hg⟩
    exact congrFun h0 k

/-! ## 5. The closing, on a record with index types -/

variable (E L) in
/-- The closing. -/
@[reducible] def closeCore : Block (Recorded N E L R nO) (N → E) (Form N E) (N → E) :=
  (closeA N E L R nO).seq (closeB E L pl)

variable (E L R nO) in
/-- The errors of the closing: 2 at ς; |E|^(n - 1) at the n coefficients. -/
def closeErr : Err ([rAux E R] ++ [rOpen E L R nO]) :=
  Err.app (s := [rAux E R]) (t := [rOpen E L R nO]) (2, ())
    (Fintype.card E ^ (Fintype.card (L ⊕ Fin nO ⊕ R) - 1), ())

/-- Closing. If neither ς nor the coefficients are bad and the linear claim of the segment is true,
then every recorded LIN is true, and so is the relation of every REL. -/
theorem clean_closeCore :
    (closeCore E L pl).Clean Recorded.True (fun g y => Form.val y g = 0) (closeErr E L R nO) :=
  (clean_closeA pl).comp (clean_closeB pl)

/-! ## 6. The honest side -/

variable {P : Type}

/-- The honest prover's state at the closing: the values of the opened forms and the terms of the
REL. It holds no pad. -/
abbrev HClose (E R : Type) (nO : ℕ) : Type := (Fin nO → E) × (R → List (E × ℕ × ℕ))

variable (pp : Places P R nO)

/-- The honest values of the auxiliary scalars: ϑ1 = ∑ c (o_i η_j + o_j η_i), ϑ0 = ∑ c η_i η_j. -/
def auxVal (a : HClose E R nO) (π : P → E) (k : R × Bool) : E :=
  if k.2 then termCross (nat a.1) (nat fun i => π (pp.opn i)) (a.2 k.1)
  else termSum (nat fun i => π (pp.opn i)) (a.2 k.1)

variable (N E L) in
/-- The honest side of the first block. -/
@[reducible] def honA : Hon (closeA N E L R nO) P E (HClose E R nO) (HClose E R nO × E) :=
  Hon.one (fun a π => (fun e => Empty.elim e, fun k => auxVal pp a π k + π (pp.aux k)))
    (fun a ς => (a, ς)) ∅ fun _ => ∅

variable (E L) in
/-- The honest side of the second block. -/
@[reducible] def honB : Hon (closeB E L pl) P E (HClose E R nO × E) (HClose E R nO) :=
  Hon.one (fun a π => (fun e => Empty.elim e, fun o => a.2 * a.1.1 o + π (pp.opn o)))
    (fun a _ => a.1) ∅ fun _ => ∅

variable (E L) in
/-- The honest side of the closing. -/
@[reducible] def honClose : Hon (closeCore E L pl) P E (HClose E R nO) (HClose E R nO) :=
  (honA N E L pp).seq (honB E L pl pp)

/-- The statement belongs to the honest state: the pads stand at their places, the state holds the
values of the opened forms and the terms, and all recorded claims are true. -/
def HonIn (a : HClose E R nO) (π : P → E) (x : Recorded N E L R nO) (y : N → E) : Prop :=
  (∀ k, y (pl.aux k) = π (pp.aux k)) ∧ (∀ o, y (pl.opn o) = π (pp.opn o)) ∧
  (∀ o, a.1 o = Form.val y (x.opn o)) ∧ a.2 = x.terms ∧ x.True y

/-- The same after ς: the auxiliary scalars on record are the honest ones. -/
def HonMid (a : HClose E R nO × E) (π : P → E) (x : XMid N E L R nO) (y : N → E) : Prop :=
  HonIn pl pp a.1 π x.1 y ∧ x.2.2 = a.2 ∧ ∀ k, x.2.1 k = auxVal pp a.1 π k + π (pp.aux k)

omit [DecidableEq N] [DecidableEq E] [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R] in
/-- Completeness of the first block: the honest auxiliary scalars are on record. -/
theorem accOn_honA : (honA N E L pp).AccOn (HonIn pl pp) (HonMid pl pp) :=
  Hon.accOn_one fun _ _ x _ c hi _ _ => ⟨(x, _, c), rfl, hi, rfl, fun _ => rfl⟩

omit [Fintype E] [DecidableEq E] [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R] in
/-- Under `h` (`HonMid`): for the honest prover every affine expression has the value 0. -/
theorem val_exprs_honest {a : HClose E R nO × E} {π : P → E} {x : XMid N E L R nO} {y : N → E}
    (h : HonMid pl pp a π x y) (k : L ⊕ Fin nO ⊕ R) :
    Form.val y (exprs pl x (fun o => a.2 * a.1.1 o + π (pp.opn o)) k) = 0 := by
  obtain ⟨⟨hpa, hpo, ho, hts, htrue⟩, hς, hs⟩ := h
  have hov : ∀ i, x.1.ov y i = nat a.1.1 i := fun i => by
    unfold Recorded.ov
    rw [show (fun i => Form.val y (x.1.opn i)) = a.1.1 from funext fun o => (ho o).symm]
  rcases k with l | o | r
  · exact htrue.1 l
  · rw [val_exprs_opn, hς, ← ho o, hpo o]
    ring
  · have hO : ∀ i, nat (fun o => a.2 * a.1.1 o + π (pp.opn o)) i =
        a.2 * nat a.1.1 i + nat (fun i => π (pp.opn i)) i :=
      nat_affine a.2 fun _ => rfl
    rw [val_exprs_rel, termSum_congr hO, termSum_line, htrue.2 r, termSum_congr hov, hς]
    unfold Places.theta
    rw [hs (r, true), hs (r, false), hpa (r, true), hpa (r, false)]
    unfold auxVal
    simp only [if_true, Bool.false_eq_true, if_false, hts]
    ring

omit [DecidableEq E] in
/-- Completeness of the second block: the linear claim is true. -/
theorem accOn_honB : (honB E L pl pp).AccOn (HonMid pl pp) (fun _ _ g y => Form.val y g = 0) :=
  Hon.accOn_one fun a π x y c hi _ _ => ⟨_, rfl, by
    show Form.val y (linClaim pl x (fun o => a.2 * a.1.1 o + π (pp.opn o)) c) = 0
    rw [val_linClaim]
    exact Finset.sum_eq_zero fun k _ => by rw [val_exprs_honest pl pp hi k, mul_zero]⟩

omit [DecidableEq E] in
/-- Completeness of the closing, at every ρ and for all pads: the linear claim of the segment is
true. -/
theorem accOn_honClose :
    (honClose E L pl pp).AccOn (HonIn pl pp) (fun _ _ g y => Form.val y g = 0) :=
  (accOn_honA pl pp).comp (accOn_honB pl pp)

variable [Fintype P] [DecidableEq P]

omit [Fintype N] [DecidableEq N] [DecidableEq E] [Fintype L] [DecidableEq L] in
/-- Under the hypotheses below, the first block is in masked form: the auxiliary scalars have pads
of their own, and their values read the pads of the opened elements only. -/
theorem masked_honA (haux : Function.Injective pp.aux)
    (hd : Disjoint (Set.range pp.opn) (Set.range pp.aux)) :
    (honA N E L pp).Masked (fun _ => _root_.True) (Set.range pp.aux)
      (Set.range pp.opn ∪ Set.range pp.aux) (Hon.simOne (r := rAux E R) (K := R × Bool) E id) :=
  Hon.masked_one (r := rAux E R) (K := R × Bool) id (fun _ => _root_.True) pp.aux haux
    (auxVal (E := E) pp) (Set.range pp.opn) (fun _ _ _ => rfl)
    (fun a π π' _ h => by
      funext k
      unfold auxVal
      rw [show (fun i => π (pp.opn i)) = fun i => π' (pp.opn i) from funext fun i => h _ ⟨i, rfl⟩]) hd

omit [Fintype N] [DecidableEq E] in
/-- Under the hypotheses below, the second block is in masked form: each opened element has a pad of
its own, and its value reads no pad. -/
theorem masked_honB (hopn : Function.Injective pp.opn) :
    (honB E L pl pp).Masked (fun _ => _root_.True) (Set.range pp.opn) (∅ ∪ Set.range pp.opn)
      (Hon.simOne (r := rOpen E L R nO) (K := Fin nO) E id) :=
  Hon.masked_one (r := rOpen E L R nO) (K := Fin nO) id (fun _ => _root_.True) pp.opn hopn
    (fun (a : HClose E R nO × E) _ o => a.2 * a.1.1 o) ∅ (fun _ _ _ => rfl)
    (fun _ _ _ _ _ => rfl) (Set.empty_disjoint _)

omit [Fintype N] [DecidableEq E] in
/-- Under the hypotheses below:
The closing is in masked form. Every scalar has a pad of its own. The auxiliary scalars read the
pads of the opened elements, which are sent later; so the order of the pads is not the order in
time. What the verifier sees is uniform. -/
theorem masked_honClose (haux : Function.Injective pp.aux) (hopn : Function.Injective pp.opn)
    (hd : Disjoint (Set.range pp.opn) (Set.range pp.aux)) :
    (honClose E L pl pp).Masked (fun _ => _root_.True)
      (Set.range pp.aux ∪ Set.range pp.opn) (Set.range pp.aux ∪ Set.range pp.opn)
      (Hon.simSeq (Hon.simOne (r := rAux E R) (K := R × Bool) E id)
        (Hon.simOne (r := rOpen E L R nO) (K := Fin nO) E id)) :=
  ((masked_honA pp haux hd).comp' (masked_honB pl pp hopn) (fun _ _ _ _ => trivial) hd.symm
    (by rw [Set.empty_union]; exact hd)).mono
    (by
      rintro p ((h | h) | (h | h))
      · exact Or.inr h
      · exact Or.inl h
      · exact absurd h (Set.notMem_empty p)
      · exact Or.inr h)

end Core

/-! ## 7. The closing, on a record that is kept as lists -/

section Lists

variable {N E : Type} [Fintype N] [DecidableEq N] [Field E] [Fintype E]
  [DecidableEq E] (nL nO nR : ℕ)

omit [Fintype N] [DecidableEq N] [Fintype E] [DecidableEq E] in
/-- The record with index types, if the lists have the lengths nL, nO, nR; otherwise nothing. -/
def toRecorded (x : Ledger N E) : Option (Recorded N E (Fin nL) (Fin nR) nO) :=
  if x.lin.length = nL ∧ x.opn.length = nO ∧ x.rel.length = nR then
    some ⟨fun l => x.lin.getD l 0,
      fun o => x.opn.getD o 0,
      fun r => (x.rel.getD r (0, [])).1,
      fun r => (x.rel.getD r (0, [])).2⟩
  else none

variable {nL nO nR}

omit [DecidableEq N] [Fintype E] [DecidableEq E] in
/-- The two forms of the record say the same. -/
theorem toRecorded_true_iff {x : Ledger N E} {xo : Recorded N E (Fin nL) (Fin nR) nO}
    (h : toRecorded nL nO nR x = some xo) (y : N → E) : xo.True y ↔ x.True y := by
  unfold toRecorded at h
  split_ifs at h with hl
  obtain rfl := Option.some.inj h
  obtain ⟨h1, h2, h3⟩ := hl
  have hov : ∀ i, nat (fun o : Fin nO => Form.val y (x.opn.getD o 0)) i = x.opv y i := fun i => by
    unfold nat Ledger.opv
    by_cases hi : i < nO
    · rw [dif_pos hi]
    · rw [dif_neg hi, List.getD_eq_default _ _ (by omega), map_zero]
  constructor
  · rintro ⟨ha, hb⟩
    refine ⟨fun f hf => ?_, fun r hr => ?_⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hf
      have h4 : Form.val y (x.lin.getD i 0) = 0 := ha ⟨i, h1 ▸ hi⟩
      rwa [List.getD_eq_getElem _ _ hi] at h4
    · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
      have h4 : Form.val y (x.rel.getD i (0, [])).1 =
          termSum (nat fun o : Fin nO => Form.val y (x.opn.getD o 0)) (x.rel.getD i (0, [])).2 :=
        hb ⟨i, h3 ▸ hi⟩
      rwa [termSum_congr hov, List.getD_eq_getElem _ _ hi] at h4
  · rintro ⟨ha, hb⟩
    refine ⟨fun l => ?_, fun r => ?_⟩
    · have hl : (l : ℕ) < x.lin.length := h1 ▸ l.2
      show Form.val y (x.lin.getD l 0) = 0
      rw [List.getD_eq_getElem _ _ hl]
      exact ha _ (List.getElem_mem hl)
    · have hr : (r : ℕ) < x.rel.length := h3 ▸ r.2
      show Form.val y (x.rel.getD r (0, [])).1 =
        termSum (nat fun o : Fin nO => Form.val y (x.opn.getD o 0)) (x.rel.getD r (0, [])).2
      rw [termSum_congr hov, List.getD_eq_getElem _ _ hr]
      exact hb _ (List.getElem_mem hr)

variable (E nL) (pl : Places N (Fin nR) nO)

/-- The closing of a segment. The numbers of recorded LIN, opened forms and REL are parameters; the
verifier rejects a record of other lengths. -/
@[reducible] def closing : Block (Ledger N E) (N → E) (Form N E) (N → E) :=
  (Block.pure (toRecorded nL nO nR) id).seq (closeCore E (Fin nL) pl)

/-- Closing, for the record as lists. At most 2 values of ς and a fraction 1/|E| of the coefficients
are bad (if nothing is on record, the one empty tuple of coefficients counts as bad, and the bound
says nothing). If none is bad and the linear claim of the segment is true, then all recorded claims
are true. -/
theorem clean_closing :
    (closing E nL pl).Clean Ledger.True (fun g y => Form.val y g = 0)
      (closeErr E (Fin nL) (Fin nR) nO) :=
  Block.Clean.comp (B₁ := Block.pure (toRecorded nL nO nR) id) (R₂ := Recorded.True)
    (Block.clean_pure_iff.2 fun _ y _ hxo hR => (toRecorded_true_iff hxo y).mp hR)
    (clean_closeCore pl)

variable {P : Type} (pp : Places P (Fin nR) nO)

/-- The honest side of the closing. -/
@[reducible] def honClosing :
    Hon (closing E nL pl) P E (HClose E (Fin nR) nO) (HClose E (Fin nR) nO) :=
  (Hon.pure (toRecorded nL nO nR) id id).seq (honClose E (Fin nL) pl pp)

variable {E}

/-- The record belongs to the honest state: the lists have the right lengths, the pads stand at
their places, the state holds the values of the opened forms and the terms, and all recorded claims
are true. -/
def HonLedger (a : HClose E (Fin nR) nO) (π : P → E) (x : Ledger N E) (y : N → E) : Prop :=
  (x.lin.length = nL ∧ x.opn.length = nO ∧ x.rel.length = nR) ∧
  (∀ k, y (pl.aux k) = π (pp.aux k)) ∧
  (∀ o, y (pl.opn o) = π (pp.opn o)) ∧
  (∀ o : Fin nO, a.1 o = Form.val y (x.opn.getD o 0)) ∧
  (∀ r : Fin nR, a.2 r = (x.rel.getD r (0, [])).2) ∧
  x.True y

omit [DecidableEq E] in
/-- Completeness of the closing, at every ρ and for all pads. -/
theorem accOn_honClosing :
    (honClosing E nL pl pp).AccOn (HonLedger nL pl pp) (fun _ _ g y => Form.val y g = 0) := by
  refine Hon.AccOn.comp (R₂ := HonIn pl pp)
    (Hon.accOn_pure fun a π x y hi => ?_) (accOn_honClose pl pp)
  obtain ⟨hl, hpa, hpo, ho, hts, htrue⟩ := hi
  have hx : toRecorded nL nO nR x =
      some ⟨fun l => x.lin.getD l 0,
        fun o => x.opn.getD o 0,
        fun r => (x.rel.getD r (0, [])).1,
        fun r => (x.rel.getD r (0, [])).2⟩ := if_pos hl
  exact ⟨_, hx, hpa, hpo, ho, funext hts, (toRecorded_true_iff hx y).mpr htrue⟩

variable [Fintype P] [DecidableEq P]

omit [Fintype N] [DecidableEq E] in
/-- Under the hypotheses below, the closing is in masked form. -/
theorem masked_honClosing (haux : Function.Injective pp.aux) (hopn : Function.Injective pp.opn)
    (hd : Disjoint (Set.range pp.opn) (Set.range pp.aux)) :
    (honClosing E nL pl pp).Masked (fun _ => _root_.True)
      (Set.range pp.aux ∪ Set.range pp.opn) (Set.range pp.aux ∪ Set.range pp.opn)
      (Hon.simSeq (s := []) (fun _ => PMF.pure ())
        (Hon.simSeq (Hon.simOne (r := rAux E (Fin nR)) (K := Fin nR × Bool) E id)
          (Hon.simOne (r := rOpen E (Fin nL) (Fin nR) nO) (K := Fin nO) E id))) := by
  have h := (Hon.masked_pure (P := P) (E := E) (toRecorded (N := N) (E := E) nL nO nR) id
      (id : HClose E (Fin nR) nO → _) fun _ => _root_.True).comp
    (masked_honClose (L := Fin nL) pl pp haux hopn hd) (fun _ _ _ _ => trivial)
    (Set.empty_disjoint _) (Set.empty_disjoint _)
  rw [Set.empty_union] at h
  exact h

end Lists

end Closing

end Blocks
