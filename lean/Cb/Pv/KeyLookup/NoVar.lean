-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/KeyLookup/NoVar.lean: the short sumcheck without variable: what its verifier puts out at a
transcript, and the row that it leaves, coefficient by coefficient.

Definitions, statements and proofs. A sumcheck of Cb/Ld/LdPsc.lean (PscOur) with an empty list of
variables has three rounds: a scalar | ε; a polynomial in the further variable | β ≠ 0; the shown
values | nothing. In the short format (Cb/Pv/KeyLookup/Short0.lean) the constant of that polynomial
is not sent. This file is general in the degree D of the summand and in the type A of the shown
values. The steps of a chain whose records are written out with fmt := [] and B := Empty take these
lemmas as they stand, since such a record unfolds to NoVar.mk0.

Main names:
  NoVar.one i c: the form "c at the entry i, 0 elsewhere", by a decidable equality on the entries.
  NoVar.ite_one, ite_one': an "if" by any instance of Decidable is that form.
  NoVar.mk0 St J A F S0 D sl w c: the record: states St, entries J, shown maps F, summand S0 of
    degree D in the shown values, incoming form sl, places w (D + 1 names) and c (one for each
    a : A).
  NoVar.fill0: the polynomial completed at its constant, at the draw: σ + Σ_t q t * β ^ (t + 1).
  NoVar.value0: the short verifier's value (TWhole.shortV at the pick F₀), written out: state, ε, β,
    (μ + ε * target) + Σ_t q t * β ^ (t + 1), the values.
  NoVar.row0: the row rowUof (Cb/Ld/LdLkpTreeRows.lean) of that record: the coefficient at j is
    Σ_t one (w (inl t)) (β ^ (t + 1)) j + one (w (inr ())) 1 j + ε * sl st j; the target is
    fin - ε * S0 st () v.
  NoVar.eq0: the weights of its one variable sum to 1 (TWhole.Eq0).
  NoVar.rd0V e: how its three rounds are read flat (Cb/Pv/KeyLookup/Flat.lean), for a numbering
    e : A ≃ Fin n of the shown values; rd0V_fms: their formats (1 | 1), (D | 1, not 0), (n | 0);
    rd0V_view: the flat view of a transcript, written out.
  NoVar.snt f i t, chl f i: scalar number t sent, and the first element drawn, in round i of a flat
    list. NoVar.finF D tg f, rowF D w mf f: the last value of the running claim and the row's
    coefficients as functions of the three flat rounds (code).
  NoVar.facts: for every typed transcript τ with flat view f: the state is handed on; β = chl f 1;
    the value shown for a is snt f 2 (e a); the row is ⟨rowF D w (sl y.2) f,
    finF D y.1 f - chl f 0 * S0 y.2 (the values)⟩.

Limits: no premise. Nothing on soundness, nothing on an honest side.

-/
import Cb.Pv.KeyLookup.Flat
import Cb.Ld.LdLkpTreeRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
namespace NoVar
open Iop IOR Hiop Prob Cb Cb.LdLkp Johnson.L5.Layers Flat

/-- c at the entry i, 0 elsewhere. -/
def one {E J : Type} [Zero E] [DecidableEq J] (i : J) (c : E) : J → E :=
  fun j => if j = i then c else 0

theorem ite_one {E J : Type} [Zero E] [DecidableEq J] (i j : J) (c : E) (inst : Decidable (i = j)) :
    @ite E (i = j) inst c 0 = one i c j := by
  unfold one
  by_cases h : i = j
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg fun e => h e.symm]

theorem ite_one' {E J : Type} [Zero E] [DecidableEq J] (i j : J) (c : E)
    (inst : Decidable (j = i)) : @ite E (j = i) inst c 0 = one i c j := by
  unfold one
  by_cases h : j = i
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

section
variable {E : Type} [Field E] [Fintype E]

/-- The sumcheck without variable. -/
noncomputable def mk0 (St J A : Type) [Fintype J] [Fintype A] (F : St → (J → E) → A → E)
    (S0 : St → (A → E) → E) (D : ℕ) (sl : St → J → E)
    (w : PIdx (([] : List (PFmt E)) ++ [pDummy E D]) → J) (c : A → J) : PscOur E where
  St := St
  J := J
  fmt := []
  dat := fun _ => ()
  A := A
  B := Empty
  F := fun st m a _ => F st m a
  Fb := fun _ _ b _ => b.elim
  S0 := fun st _ v => S0 st v
  S1 := fun _ _ _ b => b.elim
  DY := D
  slS := sl
  wAt := w
  cAt := c

/-- The polynomial completed at its constant, at the draw. -/
theorem fill0 (D : ℕ) (σ β : E) (q : Fin D → E) :
    hev (hFill ((pDummy E D).var (pDummyD E D)) ((0 : Fin (D + 1)), (1 : E)) σ q) β =
      σ + ∑ t : Fin D, q t * β ^ ((t : ℕ) + 1) := by
  have h0 : ((pDummy E D).var (pDummyD E D)).phi
      ((0 : Fin (D + 1)).insertNth (α := fun _ => E) 0 q) = 0 := by
    show ∑ _s : Unit, (1 : E) • ∑ t : Fin (D + 1), (0 : E) ^ (t : ℕ) •
      ((0 : Fin (D + 1)).insertNth (α := fun _ => E) 0 q) t = 0
    simp [Fin.sum_univ_succ]
  show hev ((0 : Fin (D + 1)).insertNth (α := fun _ => E) ((1 : E) • (σ -
    ((pDummy E D).var (pDummyD E D)).phi ((0 : Fin (D + 1)).insertNth (α := fun _ => E) 0 q))) q)
      β = _
  rw [h0]
  show ∑ t : Fin (D + 1), β ^ (t : ℕ) •
    ((0 : Fin (D + 1)).insertNth (α := fun _ => E) ((1 : E) • (σ - 0)) q) t = _
  rw [Fin.sum_univ_succ]
  simp [mul_comm]

theorem psi0 (D : ℕ) (β : E) : hPsi [(pDummy E D).var (pDummyD E D)] (β, ()) = 1 := by
  show (∑ t : Fin (D + 1), β ^ (t : ℕ) • (if t = 0 then (1 : E) else 0)) * 1 = 1
  simp

omit [Fintype E] in
theorem sum_hidx (v : HVar E) (g : HIdx [v] → E) :
    ∑ i, g i = ∑ t : Fin v.n, g (.inl t) + g (.inr ()) := by
  show ∑ i : Fin v.n ⊕ Unit, g i = _
  rw [Fintype.sum_sum_type]
  exact congrArg (fun z => (∑ t : Fin v.n, g (.inl t)) + z)
    (Fintype.sum_unique fun a : Unit => g (.inr a))

omit [Fintype E] in
theorem pushJ_id {J : Type} [Fintype J] (c : J → E) : pushJ (id : J → J) c = c := by
  funext j
  exact (Finset.sum_eq_single j (fun b _ hb => if_neg hb)
    (fun h => absurd (Finset.mem_univ j) h)).trans (if_pos rfl)

variable (St J A : Type) [Fintype J] [Fintype A] (F : St → (J → E) → A → E)
  (S0 : St → (A → E) → E) (D : ℕ) (sl : St → J → E)
  (w : PIdx (([] : List (PFmt E)) ++ [pDummy E D]) → J) (c : A → J)

/-- The weights of the one variable sum to 1. -/
theorem eq0 : TWhole.Eq0 (mk0 St J A F S0 D sl w c).par :=
  TWhole.our_eq0 (mk0 St J A F S0 D sl w c) fun _ _ hv => absurd hv List.not_mem_nil

/-- The short verifier's value at a transcript, written out. -/
theorem value0 (x : E × St) (mu eps : E) (q : Fin D → E) (be : {x : E // x ≠ 0}) (v : A → E) :
    TWhole.shortV (mk0 St J A F S0 D sl w c).par (TWhole.F₀ (mk0 St J A F S0 D sl w c).par) x
        (((), mu), eps, (((), q), be, (((), v), (), ()))) =
      ⟨x.2, eps, (be.1, ()), mu + eps * x.1 + ∑ t : Fin D, q t * be.1 ^ ((t : ℕ) + 1), v⟩ := by
  have h := fill0 D (mu + eps * x.1) be.1 q
  show (⟨x.2, eps, (be.1, ()),
    hev (hFill ((pDummy E D).var (pDummyD E D)) ((0 : Fin (D + 1)), (1 : E)) (mu + eps * x.1) q)
      be.1, v⟩ : (mk0 St J A F S0 D sl w c).par.Out) = _
  rw [h]

/-- The row that the sumcheck leaves, coefficient by coefficient. -/
theorem row0 [DecidableEq J] (h : IsEmpty (mk0 St J A F S0 D sl w c).par.B) (st : St)
    (eps be fin : E) (v : A → E) :
    rowUof (mk0 St J A F S0 D sl w c) h (id : J → J) ⟨st, eps, (be, ()), fin, v⟩ =
      ⟨fun j => (∑ t : Fin D, one (w (Sum.inl t : Fin D ⊕ Unit)) (be ^ ((t : ℕ) + 1)) j) +
          one (w (Sum.inr () : Fin D ⊕ Unit)) 1 j + eps * sl st j,
        fin - eps * S0 st v⟩ := by
  unfold rowUof
  refine congrArg₂ Row.mk ((pushJ_id _).trans (funext fun (j : J) => ?_)) rfl
  unfold PscPar.slU
  show (∑ i : HIdx [(pDummy E D).var (pDummyD E D)], _) + _ + _ = _
  rw [sum_hidx]
  show ((∑ t : Fin D, @ite E (w (Sum.inl t : Fin D ⊕ Unit) = j) (Classical.propDecidable _)
        (1 * be ^ ((t : ℕ) + 1)) 0) +
      @ite E (w (Sum.inr () : Fin D ⊕ Unit) = j) (Classical.propDecidable _) 1 0) +
    eps * hPsi [(pDummy E D).var (pDummyD E D)] (be, ()) * sl st j + eps * ∑ b : Empty, _ = _
  rw [psi0, Finset.univ_eq_empty (α := Empty), Finset.sum_empty]
  simp only [ite_one, one_mul, mul_one, mul_zero, add_zero]

end

section
variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
variable (St J A : Type) [Fintype J] [Fintype A] (F : St → (J → E) → A → E)
  (S0 : St → (A → E) → E) (D : ℕ) (sl : St → J → E)
  (w : PIdx (([] : List (PFmt E)) ++ [pDummy E D]) → J) (c : A → J)

/-- How the three rounds are read flat. -/
noncomputable def rd0V {n : ℕ} (e : A ≃ Fin n) : RdS E (shapeS (mk0 St J A F S0 D sl w c).par) :=
  rdFull (mk0 St J A F S0 D sl w c).par ((fuDummy D, ()) : FU (pDummy E D) × Unit) e

theorem rd0V_fms {n : ℕ} (e : A ≃ Fin n) :
    (rd0V St J A F S0 D sl w c e).fms = [⟨1, 1, false⟩, ⟨D, 1, true⟩, ⟨n, 0, false⟩] := rfl

theorem rd0V_view {n : ℕ} (e : A ≃ Fin n) (mu eps : E) (q : Fin D → E) (be : {x : E // x ≠ 0})
    (v : A → E) :
    (rd0V St J A F S0 D sl w c e).view (((), mu), eps, (((), q), be, (((), v), (), ()))) =
      [([mu], [eps]), (List.ofFn q, [be.1]), (List.ofFn fun i => v (e.symm i), [])] := rfl


/-! ### the same, read off the flat view -/

/-- Scalar number t sent in round i of a flat list; the first element drawn in round i. -/
def snt (f : List (RV E)) (i t : ℕ) : E := (f.getD i ([], [])).1.getD t 0
def chl (f : List (RV E)) (i : ℕ) : E := (f.getD i ([], [])).2.headD 0

/-- The last value of the running claim, from the target tg and the three flat rounds. -/
def finF (D : ℕ) (tg : E) (f : List (RV E)) : E :=
  snt f 0 0 + chl f 0 * tg + ∑ t : Fin D, snt f 1 t.val * chl f 1 ^ ((t : ℕ) + 1)

/-- The row's coefficients, from the incoming form mf and the three flat rounds. -/
def rowF {J : Type} [DecidableEq J] (D : ℕ)
    (w : PIdx (([] : List (PFmt E)) ++ [pDummy E D]) → J) (mf : J → E) (f : List (RV E)) : J → E :=
  fun j => (∑ t : Fin D, one (w (Sum.inl t : Fin D ⊕ Unit)) (chl f 1 ^ ((t : ℕ) + 1)) j) +
    one (w (Sum.inr () : Fin D ⊕ Unit)) 1 j + chl f 0 * mf j

/-- What the short verifier puts out, and the row, as functions of the flat view. -/
theorem facts [DecidableEq J] (h : IsEmpty (mk0 St J A F S0 D sl w c).par.B) {n : ℕ}
    (e : A ≃ Fin n) (y : E × St) (τ : Tr (shapeS (mk0 St J A F S0 D sl w c).par))
    (o : (mk0 St J A F S0 D sl w c).par.Out)
    (ho : o = TWhole.shortV (mk0 St J A F S0 D sl w c).par
      (TWhole.F₀ (mk0 St J A F S0 D sl w c).par) y τ)
    (f : List (RV E)) (hf : f = (rd0V St J A F S0 D sl w c e).view τ) :
    o.st = y.2 ∧
      (mk0 St J A F S0 D sl w c).lst o.st ((mk0 St J A F S0 D sl w c).par.hp o.st o.pt) = chl f 1 ∧
      (∀ a, o.vals a = snt f 2 (e a).val) ∧
      rowUof (mk0 St J A F S0 D sl w c) h (id : J → J) o =
        ⟨rowF D w (sl y.2) f, finF D y.1 f - chl f 0 * S0 y.2 fun a => snt f 2 (e a).val⟩ := by
  obtain ⟨⟨_, (mu : E)⟩, (eps : E), ⟨_, (q : Fin D → E)⟩, (be : {x : E // x ≠ 0}),
    ⟨_, (v : A → E)⟩, _, _⟩ := τ
  have ho' := ho.trans (value0 St J A F S0 D sl w c y mu eps q be v)
  have hf' := hf.trans (rd0V_view St J A F S0 D sl w c e mu eps q be v)
  clear ho hf
  subst ho'
  subst hf'
  have hq : ∀ t : Fin D, snt [([mu], [eps]), (List.ofFn q, [be.1]),
      (List.ofFn fun i => v (e.symm i), [])] 1 t.val = q t := fun t => getD_ofFn q t
  have hv : ∀ a, snt [([mu], [eps]), (List.ofFn q, [be.1]),
      (List.ofFn fun i => v (e.symm i), [])] 2 (e a).val = v a := fun a =>
    (getD_ofFn (fun i => v (e.symm i)) (e a)).trans (congrArg v (e.symm_apply_apply a))
  refine ⟨rfl, rfl, fun a => (hv a).symm, ?_⟩
  rw [row0]
  refine congrArg₂ Row.mk rfl ?_
  have e1 : (fun a => snt [([mu], [eps]), (List.ofFn q, [be.1]),
      (List.ofFn fun i => v (e.symm i), [])] 2 (e a).val) = v := funext hv
  rw [e1]
  unfold finF
  simp only [hq]
  rfl

end
end NoVar
end Lk6

#print axioms Lk6.NoVar.fill0
#print axioms Lk6.NoVar.value0
#print axioms Lk6.NoVar.row0
#print axioms Lk6.NoVar.eq0
#print axioms Lk6.NoVar.rd0V_view
#print axioms Lk6.NoVar.facts
