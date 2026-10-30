-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/Parts.lean: from one masked claim on the product of the roots of m = n + 1 parts to
one masked claim on each part's root, by a chain of n sumchecks without variable.

Where it is used. In a lookup whose keys come in parts, the tie of the two sides of the identity
leaves a claim on the product of the roots of all parts' product trees, and each tree needs a claim
on its own root. The lookup of Cb/Ld/LdLkpAsm2.lean has one key tree and no such step.

Definitions, statements and proofs. The chain is built from the sumcheck for a polynomial summand
(Cb/Ld/LdPsc.lean: PscOur, with an empty list of variables), after the pattern of the tie
(Cb/Ld/LdLkpTie.lean, Cb/Ld/LdLkpTieProofs.lean). Only files of Cb/ are imported.

The data. D : PartsP E holds the state before the steps (any type St0), the entries J, the number n
of steps (the parts are 0, .., n), the roots as functions of state and entries (they are never
sent), the form D.inc that comes in with the claim on the product of all roots, and where each
step's own mask entries stand: D.wAt l (three names) and D.cAt l (two), as TieP.wAt and TieP.cAt
do. That these places are pairwise different and used by nothing else is not asked here.
D.rest st m j is the product of the roots j, .., n: a definition; no hypothesis stands for it.

Step l, for l < n. The summand is Y₁ · Y₂ at the two values (false: root l; true: rest (l + 1)).
Three rounds: a scalar | ε; a round polynomial in the further variable | β ≠ 0; two values |
nothing.
    In:  rest l + (form on the entries) = target.
    Out: the row on the step's hiding coefficients; root l + β · (own entry cAt l false) = the first
      value sent
         (it rides along); rest (l + 1) + β · (own entry cAt l true) = the second value sent: the
         next step's claim, by a step without rounds (D.nxt).
The types of the states are a family by recursion (D.lv): St0, then the sumcheck's Out over the
state before.

Main names:
  D.afterA b k: the block b, then the steps 0, .., k - 1, by recursion from b. At k = 0 no round is
    added (one part: nothing to split).
  mapA φ: a step without rounds as a block of its own (IOR.pure). D.aloneA k := D.afterA (mapA id)
    k.
  parts_ok: the four conditions VarsOK, ValInj, DegX, DegY of the sumcheck hold at every step.
    (There
    is no variable but the further one: the first three hold of an empty list; the weight is in
      DegY.)
  rest_step, rest_last: rest j = root j * rest (j + 1) for j ≤ n; rest n = root n.
  parts_sum: for l ≤ n the sum claim of step l is the joint's own claim.
  parts_step: for l ≤ n, step l is Good (BkA.Good: GoodAt, the identity extracts) from D.jtAt l to
    D.jtAt (l + 1).
  parts_after: if b is Good from A to D.jtAt 0 and k ≤ n + 1, then D.afterA b k is Good from A to
    D.jtAt k. The lookup uses k = n. The lemma holds one step further because rest (n + 1) is the
    empty product 1.
  parts_alone: D.aloneA k is Good from D.jtAt 0 to D.jtAt k.
  parts_know: the field know of parts_alone, written out: knowledge soundness of D.aloneA k's
    verifier for each fixed tuple of messages. (The term D.aloneA carries the sumcheck's honest
      side;
    blocks without an honest side: Cb/Pv/KeyLookup/PartsK.lean.)
  parts_rounds: D.afterA b k has b's rounds and 3 k more.

Limits: the only premises are k ≤ n + 1 (a condition on public numbers) and, in parts_after, the
block before. This file does not say who states the incoming claim, nor that the roots are products
of trees. The read-out as forms, targets and rows is in Cb/Pv/KeyLookup/PartsRows.lean, the lists of
errors in Cb/Pv/KeyLookup/PartsErr.lean. The round in the further variable sends all three
coefficients of its polynomial here; the format in which the constant is not sent:
Cb/Pv/KeyLookup/PartsShort.lean.


-/
import Cb.Ld.LdLkpTieRows
import Cb.Ld.LdLkpTieProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp

noncomputable section

/-- The data of the parts' chain. -/
structure PartsP (E : Type) [Field E] [Fintype E] where
  St0 : Type
  J : Type
  [finJ : Fintype J]
  /-- the number of steps: the parts are 0, .., n -/
  n : ℕ
  /-- the parts' roots: virtual scalars -/
  root : St0 → (J → E) → ℕ → E
  /-- the form that comes in with the claim on the product of all roots -/
  inc : St0 → J → E
  /-- own masks of step l: the coefficients of the hiding polynomial; one entry for each of the two
  values -/
  wAt : ℕ → PIdx (([] : List (PFmt E)) ++ [pDummy E 2]) → J
  cAt : ℕ → Bool → J

attribute [instance] PartsP.finJ

variable {E : Type} [Field E] [Fintype E]

namespace PartsP
variable (D : PartsP E)

/-- The product of the roots j, .., n. -/
def rest (st : D.St0) (m : D.J → E) (j : ℕ) : E := ∏ i ∈ Finset.Ico j (D.n + 1), D.root st m i

/-- A step, with the maps from its entries and states to those of the data. -/
structure Lv where
  T : PscOur E
  toJ : T.J → D.J
  base : T.St → D.St0
  /-- the value that the next step takes up (the rest); the value whose claim rides along (the root)
  -/
  nx : T.A
  pt : T.A

/-- Step 0: root 0 · rest 1, with the incoming form. -/
def T0 : PscOur E where
  St := D.St0
  J := D.J
  fmt := []
  dat := fun _ => ()
  A := Bool
  B := Empty
  F := fun st m b _ => if b then D.rest st m 1 else D.root st m 0
  Fb := fun _ _ b _ => b.elim
  S0 := fun _ _ v => v false * v true
  S1 := fun _ _ _ b => b.elim
  DY := 2
  slS := fun st j => D.inc st j
  wAt := D.wAt 0
  cAt := D.cAt 0

def lv0 : D.Lv := ⟨D.T0, id, id, true, false⟩

open Classical in
/-- Step j + 1, after the step L: root (j + 1) · rest (j + 2), with the form β of L at the mask
entry of the
value taken up. -/
def TN (j : ℕ) (L : D.Lv) : PscOur E where
  St := L.T.par.Out
  J := D.J
  fmt := []
  dat := fun _ => ()
  A := Bool
  B := Empty
  F := fun o m b _ => if b then D.rest (L.base o.st) m (j + 2) else D.root (L.base o.st) m (j + 1)
  Fb := fun _ _ b _ => b.elim
  S0 := fun _ _ v => v false * v true
  S1 := fun _ _ _ b => b.elim
  DY := 2
  slS := fun o i => if i = L.toJ (L.T.cAt L.nx) then L.T.lst o.st (L.T.par.hp o.st o.pt) else 0
  wAt := D.wAt (j + 1)
  cAt := D.cAt (j + 1)

def lvS (j : ℕ) (L : D.Lv) : D.Lv := ⟨D.TN j L, id, fun o => L.base o.st, true, false⟩

/-- The steps: the states' types are a family by recursion. -/
def lv : ℕ → D.Lv
  | 0 => D.lv0
  | j + 1 => D.lvS j (lv j)

/-- The joint's own claim before step l: the masked claim on the product of the roots l, .., n. -/
def claim (l : ℕ) (x : E × (D.lv l).T.St) (m : D.J → E) : Prop :=
  D.rest ((D.lv l).base x.2) m l + ∑ j, (D.lv l).T.slS x.2 j * m ((D.lv l).toJ j) = x.1

section Base
variable (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E)

/-- The entries in the naming of step l. -/
def msgAt (l : ℕ) : M → (D.lv l).T.J → E := fun ms j => msg ms ((D.lv l).toJ j)

variable {Ex M Wp Kc}

/-- What rides along after step l: what rode before, the row on the hiding coefficients, the masked
claim on
the root l. -/
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

/-- The step without rounds after step l: the scalar sent for the rest is the next target. -/
def nxt (l : ℕ) : (D.lv l).T.par.Out → E × (D.lv (l + 1)).T.St := fun o => (o.vals (D.lv l).nx, o)

variable (Ex Wp Kc) in
/-- Step l, with the step without rounds after it. -/
def stepA (l : ℕ) : BkA Kc M (E × (D.lv l).T.St) (E × (D.lv (l + 1)).T.St) Ex Wp :=
  ⟨((D.lv l).T.par.psc Ex).post (fun o => some (D.nxt l o)) (ExtMap.id Ex),
    ((D.lv l).T.par.hon Ex fun w => D.msgAt M msg l w.1).post (fun o => some (D.nxt l o))
      (ExtMap.id Ex) fun o => (D.nxt l o.1, o.2),
    ((D.lv l).T.par.nums Ex Kc).post (fun o => some (D.nxt l o)) (ExtMap.id Ex)⟩

/-- The block b, then the steps 0, .., k - 1. At k = 0: b, and no round more. -/
def afterA {X : Type} (b : BkA Kc M X (E × (D.lv 0).T.St) Ex Wp) :
    (k : ℕ) → BkA Kc M X (E × (D.lv k).T.St) Ex Wp
  | 0 => b
  | k + 1 => (afterA b k).seq (D.stepA Ex Wp Kc msg k)

end Base
end PartsP

/-- A step without rounds as a block of its own: a map on the explicit part. -/
def mapA (Kc M : Type) {X X' : Type} (Ex : ExtSpec) (Wp : Type) (φ : X → X') :
    BkA Kc M X X' Ex Wp :=
  ⟨IOR.pure (fun x => some (φ x)) (ExtMap.id Ex),
    Honest.pure (fun x => some (φ x)) (ExtMap.id Ex) (fun o => (φ o.1, o.2)),
    Nums.pure Kc (fun x => some (φ x)) (ExtMap.id Ex)⟩

/-- The steps 0, .., k - 1 alone. -/
def PartsP.aloneA (D : PartsP E) (Ex : ExtSpec) {M : Type} (Wp Kc : Type) (msg : M → D.J → E)
    (k : ℕ) :
    BkA Kc M (E × (D.lv 0).T.St) (E × (D.lv k).T.St) Ex Wp :=
  D.afterA msg (mapA Kc M Ex Wp id) k

end

/-! ## Proofs -/

section
variable {E : Type} [Field E] [Fintype E] (D : PartsP E)

theorem PartsP.rest_step (st : D.St0) (m : D.J → E) (j : ℕ) (h : j ≤ D.n) :
    D.rest st m j = D.root st m j * D.rest st m (j + 1) :=
  Finset.prod_eq_prod_Ico_succ_bot (Nat.lt_succ_of_le h) _

theorem PartsP.rest_last (st : D.St0) (m : D.J → E) : D.rest st m D.n = D.root st m D.n := by
  unfold PartsP.rest
  rw [Nat.Ico_succ_singleton, Finset.prod_singleton]

theorem PartsP.cover : ∀ (l : ℕ) (a : (D.lv l).T.A), a = (D.lv l).nx ∨ a = (D.lv l).pt
  | 0, true => Or.inl rfl
  | 0, false => Or.inr rfl
  | _ + 1, true => Or.inl rfl
  | _ + 1, false => Or.inr rfl

/-- The value that the next step takes up is the rest; the value whose claim rides is the root. -/
theorem PartsP.F_nx :
    ∀ (l : ℕ) (st : (D.lv l).T.St) (m : D.J → E) (X : HPt ((D.lv l).T.vars st)),
      (D.lv l).T.F st (fun j => m ((D.lv l).toJ j)) (D.lv l).nx X =
        D.rest ((D.lv l).base st) m (l + 1)
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl

theorem PartsP.F_pt :
    ∀ (l : ℕ) (st : (D.lv l).T.St) (m : D.J → E) (X : HPt ((D.lv l).T.vars st)),
      (D.lv l).T.F st (fun j => m ((D.lv l).toJ j)) (D.lv l).pt X = D.root ((D.lv l).base st) m l
  | 0, _, _, _ => rfl
  | _ + 1, _, _, _ => rfl

theorem PartsP.fmt_nil : ∀ l, (D.lv l).T.fmt = []
  | 0 => rfl
  | _ + 1 => rfl

theorem PartsP.dy : ∀ l, (D.lv l).T.DY = 2
  | 0 => rfl
  | _ + 1 => rfl

/-- The four conditions of the library's sumcheck, at every step. -/
theorem parts_ok (l : ℕ) :
    (D.lv l).T.VarsOK ∧ (D.lv l).T.ValInj ∧ (D.lv l).T.DegX ∧ (D.lv l).T.DegY := by
  cases l with
  | zero =>
    exact ⟨fun _ _ hv => absurd hv (List.not_mem_nil), fun _ hf => absurd hf (List.not_mem_nil),
      fun _ _ _ => trivial, fun _ _ v u r => degY_aux v u r⟩
  | succ l =>
    exact ⟨fun _ _ hv => absurd hv (List.not_mem_nil), fun _ hf => absurd hf (List.not_mem_nil),
      fun _ _ _ => trivial, fun _ _ v u r => degY_aux v u r⟩

/-- For l ≤ n the sum claim of step l is the joint's own claim. -/
theorem parts_sum (l : ℕ) (hl : l ≤ D.n) (x : E × (D.lv l).T.St) (m : D.J → E) :
    (D.lv l).T.SumHolds x (fun j => m ((D.lv l).toJ j)) ↔ D.claim l x m := by
  have h := D.rest_step ((D.lv l).base x.2) m l hl
  cases l with
  | zero =>
    show (D.root x.2 m 0 * D.rest x.2 m 1 + ∑ b : Empty, (b.elim : E) * (b.elim : E)) +
          ∑ j, (D.lv 0).T.slS x.2 j * m ((D.lv 0).toJ j) = x.1 ↔
      D.rest ((D.lv 0).base x.2) m 0 + ∑ j, (D.lv 0).T.slS x.2 j * m ((D.lv 0).toJ j) = x.1
    rw [h, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    exact Iff.rfl
  | succ l =>
    show (D.root ((D.lv (l + 1)).base x.2) m (l + 1) * D.rest ((D.lv (l + 1)).base x.2) m (l + 2) +
            ∑ b : Empty, (b.elim : E) * (b.elim : E)) +
          ∑ j, (D.lv (l + 1)).T.slS x.2 j * m ((D.lv (l + 1)).toJ j) = x.1 ↔
      D.rest ((D.lv (l + 1)).base x.2) m (l + 1) +
          ∑ j, (D.lv (l + 1)).T.slS x.2 j * m ((D.lv (l + 1)).toJ j) = x.1
    rw [h, Finset.univ_eq_empty, Finset.sum_empty, add_zero]

/-- The form of the claim before step l + 1: β of step l at the mask entry of the value taken up, 0
elsewhere. -/
theorem parts_form (l : ℕ) (o : (D.lv l).T.par.Out) (m : D.J → E) :
    ∑ j, (D.lv (l + 1)).T.slS o j * m ((D.lv (l + 1)).toJ j) =
      (D.lv l).T.lst o.st ((D.lv l).T.par.hp o.st o.pt) *
        m ((D.lv l).toJ ((D.lv l).T.cAt (D.lv l).nx)) := by
  classical
  show ∑ j : D.J,
      (if j = (D.lv l).toJ ((D.lv l).T.cAt (D.lv l).nx) then
            (D.lv l).T.lst o.st ((D.lv l).T.par.hp o.st o.pt)
          else 0) * m j = _
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The row on the value taken up is the next joint's own claim. -/
theorem parts_next (l : ℕ) (o : (D.lv l).T.par.Out) (m : D.J → E) :
    (D.lv l).T.par.EHolds o (fun j => m ((D.lv l).toJ j)) (D.lv l).nx ↔
    D.claim (l + 1) (D.nxt l o) m := by
  refine (psc_our_val E (D.lv l).T o _ (D.lv l).nx).trans ?_
  have hF : (D.lv l).T.F o.st (fun j => m ((D.lv l).toJ j)) (D.lv l).nx
        ((D.lv l).T.ini o.st ((D.lv l).T.par.hp o.st o.pt)) =
      D.rest ((D.lv l).base o.st) m (l + 1) :=
    D.F_nx l o.st m _
  show _ ↔ D.rest ((D.lv l).base o.st) m (l + 1) +
      ∑ j, (D.lv (l + 1)).T.slS o j * m ((D.lv (l + 1)).toJ j) = o.vals (D.lv l).nx
  have h2 := (parts_form D l o m).trans (mul_comm _ _)
  exact ⟨fun h => (congrArg₂ (· + ·) hF.symm h2).trans h,
    fun h => (congrArg₂ (· + ·) hF h2.symm).trans h⟩

/-- What rides along after step l, written out: the masked claim on the root l. -/
theorem parts_ride (l : ℕ) (o : (D.lv l).T.par.Out) (m : D.J → E) :
    (D.lv l).T.par.EHolds o (fun j => m ((D.lv l).toJ j)) (D.lv l).pt ↔
    D.root ((D.lv l).base o.st) m l +
        m ((D.lv l).toJ ((D.lv l).T.cAt (D.lv l).pt)) *
          (D.lv l).T.lst o.st ((D.lv l).T.par.hp o.st o.pt) = o.vals (D.lv l).pt := by
  refine (psc_our_val E (D.lv l).T o _ (D.lv l).pt).trans ?_
  have hF : (D.lv l).T.F o.st (fun j => m ((D.lv l).toJ j)) (D.lv l).pt
        ((D.lv l).T.ini o.st ((D.lv l).T.par.hp o.st o.pt)) = D.root ((D.lv l).base o.st) m l :=
    D.F_pt l o.st m _
  exact ⟨fun h => (congrArg (· + _) hF.symm).trans h, fun h => (congrArg (· + _) hF).trans h⟩

section
variable (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E) (A0 : Rels Kc D.St0 Ex (M × Wp))

theorem parts_jt (l : ℕ) (hl : l ≤ D.n) :
    (D.lv l).T.baseIn (D.ride msg A0 l) (fun w => D.msgAt M msg l w.1) = D.jtAt msg A0 l :=
  rels_ext
    (funext fun x =>
      funext fun _ => funext fun w =>
        propext (and_congr_right fun _ => parts_sum D l hl x (msg w.1)))
    (funext fun a => funext fun w =>
      propext (and_congr_right fun _ => parts_sum D l hl a.1 (msg w.1)))
    rfl rfl

/-- One step. -/
theorem parts_step (l : ℕ) (hl : l ≤ D.n) :
    (D.stepA Ex Wp Kc msg l).Good (D.jtAt msg A0 l) (D.jtAt msg A0 (l + 1)) := by
  have ok := parts_ok D l
  have g1 := psc_our_goodAt E (D.lv l).T Ex M Wp Kc (D.ride msg A0 l) (D.msgAt M msg l)
    ok.1 ok.2.2.1 ok.2.2.2 ok.2.1
  rw [parts_jt D Ex M Wp Kc msg A0 l hl] at g1
  refine goodAt_postMap Kc M _ _ _ Ex Ex Wp Wp _ _ _ _ (D.jtAt msg A0 (l + 1)) _ _ (D.nxt l) g1 ?_
    (fun _ _ h => h) (fun _ => rfl) ?_
  · intro o y w h
    exact ⟨⟨h.1, h.2.1, h.2.2 _⟩, (parts_next D l o (msg w.1)).1 (h.2.2 _)⟩
  · intro o y w _ h
    refine ⟨h.1.1, h.1.2.1, fun a => ?_⟩
    rcases D.cover l a with rfl | rfl
    · exact (parts_next D l o (msg w.1)).2 h.2
    · exact h.1.2.2

/-- A block, then the steps 0, .., k - 1. -/
theorem parts_after {X : Type} (b : BkA Kc M X (E × (D.lv 0).T.St) Ex Wp)
    (A : Rels Kc X Ex (M × Wp)) (hb : b.Good A (D.jtAt msg A0 0)) :
    ∀ k, k ≤ D.n + 1 → (D.afterA msg b k).Good A (D.jtAt msg A0 k)
  | 0, _ => hb
  | k + 1, hk =>
    goodAt_seq_ext Kc M _ _ _ Ex Ex Ex Wp Wp Wp _ _ _ _ A (D.jtAt msg A0 k)
      (D.jtAt msg A0 (k + 1)) (fun _ _ _ wp => wp) (fun _ _ _ wp => wp)
      (fun _ _ _ wp => wp) _ _ (parts_after b A hb k (Nat.le_of_succ_le hk))
      (parts_step D Ex M Wp Kc msg A0 k (Nat.le_of_succ_le_succ hk)) fun _ _ _ _ _ _ _ => rfl

end
end

/-- A step without rounds, alone, is good: under the four conditions of the library's stepAt_map. -/
theorem mapA_good (Kc M X X' : Type) (Ex : ExtSpec) (Wp : Type) (φ : X → X')
    (A : Rels Kc X Ex (M × Wp)) (B : Rels Kc X' Ex (M × Wp))
    (h1 : ∀ x y w, A.rel x y w → B.rel (φ x) y w) (h2 : ∀ x y, A.on (x, y) → B.on (φ x, y))
    (h3 : ∀ w, B.core w = A.core w)
    (h4 : ∀ x y w, A.on (x, y) → B.relR (φ x, y) w → A.relR (x, y) w) :
    (mapA Kc M Ex Wp φ).Good A B := by
  have hS := stepAt_map Kc M X X' Ex Wp φ A B h1 h2 h3 h4
  refine ⟨⟨()⟩,
    ⟨fun x y y' τ τ' _ _ _ _ => rfl, fun y y' τ τ' q _ _ hE _ => hS.isLocal y y' q hE⟩,
    ?_, ?_, fun w x _ _ => hS.keeps x w, ?_, fun _ _ => le_refl _, ?_,
    fun w x _ _ => hS.same x w, ?_⟩
  · intro x y w c ρ hR _
    exact hS.acc x y w hR
  · intro a τ b ha hb
    obtain ⟨e1, e2⟩ := red_out_eq_some.1 hb
    rw [show b = (b.1, (ExtMap.id Ex).map a.2) from Prod.ext rfl e2]
    exact hS.onOut a.1 a.2 b.1 ha e1
  · exact prRho_empty _ fun _ h => h
  · intro k
    exact prRho_empty _ fun _ h => h
  · intro u a ha b w hb hw
    obtain ⟨e1, e2⟩ := red_out_eq_some.1 hb
    rw [show b = (b.1, (ExtMap.id Ex).map a.2) from Prod.ext rfl e2] at hw
    exact hS.know u a.1 a.2 b.1 w ha e1 hw

section
variable {E : Type} [Field E] [Fintype E] (D : PartsP E)
variable (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → D.J → E) (A0 : Rels Kc D.St0 Ex (M × Wp))

/-- The steps 0, .., k - 1 alone. -/
theorem parts_alone (k : ℕ) (hk : k ≤ D.n + 1) :
    (D.aloneA Ex Wp Kc msg k).Good (D.jtAt msg A0 0) (D.jtAt msg A0 k) :=
  parts_after D Ex M Wp Kc msg A0 _ _
    (mapA_good Kc M _ _ Ex Wp id _ _ (fun _ _ _ h => h) (fun _ _ h => h) (fun _ => rfl)
      fun _ _ _ _ h => h) k hk

/-- The field know of parts_alone: knowledge soundness for each fixed tuple of messages; the
identity extracts.
Road (k) proper: PartsK.lean. -/
theorem parts_know (k : ℕ) (hk : k ≤ D.n + 1) (m : M) :
    (D.aloneA Ex Wp Kc msg k).R.red.Know (D.jtAt msg A0 0).on
      (fun a wp => (D.jtAt msg A0 0).relR a (m, wp)) (fun b wp => (D.jtAt msg A0 k).relR b (m, wp))
      (fun _ _ wp => wp) (D.aloneA Ex Wp Kc msg k).P.err :=
  (parts_alone D Ex M Wp Kc msg A0 k hk).know m

/-- Three rounds a step. -/
theorem parts_rounds {X : Type} (b : BkA Kc M X (E × (D.lv 0).T.St) Ex Wp) (k : ℕ) :
    (D.afterA msg b k).R.shape.length = b.R.shape.length + 3 * k := by
  have hl : ∀ l, (D.stepA Ex Wp Kc msg l).R.shape.length = 3 := fun l => by
    have e : (D.stepA Ex Wp Kc msg l).R.shape = ((D.lv l).T.par.psc Ex).shape := rfl
    rw [e, psc_our_len E (D.lv l).T Ex, D.fmt_nil l]
    rfl
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : (D.afterA msg b (k + 1)).R.shape =
        (D.afterA msg b k).R.shape ++ (D.stepA Ex Wp Kc msg k).R.shape := rfl
    rw [e, List.length_append, ih, hl k]
    ring

end
end Lk6
