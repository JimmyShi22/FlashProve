-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/RuleKitProofs.lean: the proof of `KitMeasure` of
Johnson/Desc/Sound/RuleKit.lean. Theorems and the lemmas that they need.

Limits: those of that file.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.RuleKit
import Prob.Count
import Prob.Bias
import Iop.GrindProofs
import Run.DrawTieProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes (E)
open TypedOracleCompiler.Run.PQ (RD)
open _root_.Run.PQ (CK)
open _root_.Prob (cnt cnt_mono cnt_false cnt_congr cnt_prod_le cnt_fst cnt_comp_le cnt_eq_const
  cnt_equiv)
open _root_.Run (Vals DVal outAll toU3 toU3_inj bsRound)
open VerifiableInference.Desc.First.Prod (cnt_mem_le)

/-- The elements that the values of a list of draws give. -/
def elsOf (f : Fmt.Fld) (ds : List Fmt.Draw) (v : Vals f ds) : List Fmt.Ext :=
  (Fmt.collect (outAll f ds v)).elems

/-- At place j the list holds an element of the rule's list at the elements before it. -/
def BadAt (L : List Fmt.Ext → List E) (j : ℕ) (l : List Fmt.Ext) : Prop :=
  ∃ x, l[j]? = some x ∧ E.ofTriple x ∈ L (l.take j)

theorem badAt_nil (L : List Fmt.Ext → List E) (j : ℕ) : ¬ BadAt L j [] := by
  rintro ⟨x, hx, _⟩
  simp at hx

theorem badAt_cons_zero (L : List Fmt.Ext → List E) (y : Fmt.Ext) (l : List Fmt.Ext) :
    BadAt L 0 (y :: l) ↔ E.ofTriple y ∈ L [] := by
  constructor
  · rintro ⟨x, hx, hb⟩
    have e : y = x := by simpa using hx
    subst e
    simpa using hb
  · intro h
    exact ⟨y, by simp, by simpa using h⟩

theorem badAt_cons_succ (L : List Fmt.Ext → List E) (j : ℕ) (y : Fmt.Ext) (l : List Fmt.Ext) :
    BadAt L (j + 1) (y :: l) ↔ BadAt (fun pre => L (y :: pre)) j l := by
  unfold BadAt
  simp only [List.getElem?_cons_succ, List.take_succ_cons]

theorem cnt_first_le {A : Type} [Fintype A] (emb : A → Fmt.Ext) (hinj : Function.Injective emb)
    (l : List E) : cnt (fun a : A => E.ofTriple (emb a) ∈ l) ≤ l.length := by
  classical
  have h := cnt_mem_le (fun a : A => E.ofTriple (emb a))
    (fun a b hab => hinj (congrArg OnBytes.E.triple hab)) l.toFinset
  refine le_trans (le_of_eq (cnt_congr fun a => ?_)) (le_trans h (List.toFinset_card_le l))
  exact List.mem_toFinset.symm

theorem step_skip (f : Fmt.Fld) (n : ℕ) (d : Fmt.Draw) (ds : List Fmt.Draw) (hd : isElem d = false)
    (hel : ∀ (a : DVal f d) (v : Vals f ds), elsOf f (d :: ds) (a, v) = elsOf f ds v)
    (ih : ∀ (j : ℕ) (L : List Fmt.Ext → List E), (∀ pre, (L pre).length ≤ n) →
      cnt (fun v : Vals f ds => BadAt L j (elsOf f ds v)) ≤ n * others f ds)
    (j : ℕ) (L : List Fmt.Ext → List E) (hL : ∀ pre, (L pre).length ≤ n) :
    cnt (fun v : Vals f (d :: ds) => BadAt L j (elsOf f (d :: ds) v)) ≤ n * others f (d :: ds) := by
  have h1 : cnt (fun v : DVal f d × Vals f ds => BadAt L j (elsOf f (d :: ds) v)) ≤
      Fintype.card (DVal f d) * (n * others f ds) :=
    cnt_prod_le _ _ fun a => by
      show cnt (fun v : Vals f ds => BadAt L j (elsOf f (d :: ds) (a, v))) ≤ n * others f ds
      simp only [hel a]
      exact ih j L hL
  have h2 : others f (d :: ds) = Fintype.card (DVal f d) * others f ds := by
    simp [others, hd, Nat.card_eq_fintype_card]
  rw [h2]
  refine le_trans h1 (le_of_eq ?_)
  ring

theorem step_elem (f : Fmt.Fld) (n : ℕ) (d : Fmt.Draw) (ds : List Fmt.Draw) (hd : isElem d = true)
    (emb : DVal f d → Fmt.Ext) (hinj : Function.Injective emb)
    (hel : ∀ (a : DVal f d) (v : Vals f ds), elsOf f (d :: ds) (a, v) = emb a :: elsOf f ds v)
    (ih : ∀ (j : ℕ) (L : List Fmt.Ext → List E), (∀ pre, (L pre).length ≤ n) →
      cnt (fun v : Vals f ds => BadAt L j (elsOf f ds v)) ≤ n * others f ds)
    (j : ℕ) (L : List Fmt.Ext → List E) (hL : ∀ pre, (L pre).length ≤ n) :
    cnt (fun v : Vals f (d :: ds) => BadAt L j (elsOf f (d :: ds) v)) ≤ n * others f (d :: ds) := by
  have h2 : others f (d :: ds) =
      max (Fintype.card (Vals f ds)) (Fintype.card (DVal f d) * others f ds) := by
    simp [others, hd, Nat.card_eq_fintype_card]
  rw [h2]
  cases j with
  | zero =>
    have h1 : cnt (fun v : DVal f d × Vals f ds => BadAt L 0 (elsOf f (d :: ds) v)) =
        cnt (fun a : DVal f d => E.ofTriple (emb a) ∈ L []) * Fintype.card (Vals f ds) := by
      rw [← cnt_fst (D := Vals f ds) (fun a : DVal f d => E.ofTriple (emb a) ∈ L [])]
      refine cnt_congr fun v => ?_
      obtain ⟨a, v⟩ := v
      rw [hel a v]
      exact badAt_cons_zero L _ _
    refine le_trans (le_of_eq h1) ?_
    exact Nat.mul_le_mul (le_trans (cnt_first_le emb hinj _) (hL [])) (le_max_left _ _)
  | succ j =>
    have h1 : cnt (fun v : DVal f d × Vals f ds => BadAt L (j + 1) (elsOf f (d :: ds) v)) ≤
        Fintype.card (DVal f d) * (n * others f ds) :=
      cnt_prod_le _ _ fun a => by
        show cnt (fun v : Vals f ds => BadAt L (j + 1) (elsOf f (d :: ds) (a, v))) ≤
          n * others f ds
        simp only [hel a, badAt_cons_succ]
        exact ih j (fun pre => L (emb a :: pre)) (fun pre => hL _)
    refine le_trans h1 ?_
    calc Fintype.card (DVal f d) * (n * others f ds)
        = n * (Fintype.card (DVal f d) * others f ds) := by ring
      _ ≤ n * max (Fintype.card (Vals f ds)) (Fintype.card (DVal f d) * others f ds) :=
          Nat.mul_le_mul_left n (le_max_right _ _)

/-- **The count over the values of the draws.** -/
theorem cnt_vals_le (f : Fmt.Fld) (n : ℕ) (ds : List Fmt.Draw) :
    ∀ (j : ℕ) (L : List Fmt.Ext → List E), (∀ pre, (L pre).length ≤ n) →
      cnt (fun v : Vals f ds => BadAt L j (elsOf f ds v)) ≤ n * others f ds := by
  induction ds with
  | nil =>
    intro j L _
    exact le_trans (le_of_eq (cnt_false (P := fun v : Vals f [] => BadAt L j (elsOf f [] v))
      fun _ => badAt_nil L j)) (Nat.zero_le _)
  | cons d ds ih =>
    intro j L hL
    cases d with
    | elem =>
      exact step_elem f n .elem ds rfl (fun a : DVal f .elem => toU3 (f := f) a) toU3_inj
        (fun _ _ => rfl) ih j L hL
    | elemNZ =>
      exact step_elem f n .elemNZ ds rfl (fun a : DVal f .elemNZ => toU3 (f := f) a.1)
        (fun a b h => Subtype.ext (toU3_inj h)) (fun _ _ => rfl) ih j L hL
    | pos k => exact step_skip f n (.pos k) ds rfl (fun _ _ => rfl) ih j L hL
    | trits m => exact step_skip f n (.trits m) ds rfl (fun _ _ => rfl) ih j L hL
    | sealed => exact step_skip f n .sealed ds rfl (fun _ _ => rfl) ih j L hL

theorem elsOf_length (f : Fmt.Fld) (ds : List Fmt.Draw) :
    ∀ v : Vals f ds, (elsOf f ds v).length = nElems ds := by
  induction ds with
  | nil => intro _; rfl
  | cons d ds ih =>
    intro v
    cases d with
    | elem =>
      show (toU3 (f := f) v.1 :: elsOf f ds v.2).length = _
      simp [nElems, isElem, ih, Nat.add_comm]
    | elemNZ =>
      show (toU3 (f := f) v.1.1 :: elsOf f ds v.2).length = _
      simp [nElems, isElem, ih, Nat.add_comm]
    | pos k =>
      show (elsOf f ds v.2).length = _
      simp [nElems, isElem, ih]
    | trits m =>
      show (elsOf f ds v.2).length = _
      simp [nElems, isElem, ih]
    | sealed =>
      show (elsOf f ds v.2).length = _
      simp [nElems, isElem, ih]

/-- Over each old challenge stand 2 ^ b written ones. -/
theorem cnt_old_le {C : Type} [Fintype C] (b : ℕ) (P : C → Prop) :
    cnt (fun c : _root_.Iop.GChal b C => P (_root_.Iop.GChal.old c)) ≤ cnt P * 2 ^ b := by
  refine cnt_comp_le (_root_.Iop.GChal.old (b := b) (C := C)) (w := 2 ^ b) (fun u => ?_) P
  have h := cnt_equiv (_root_.Iop.GChal.equiv b C) (fun p : C × (Fin b → Bool) => p.1 = u)
  have h' : cnt (fun c : _root_.Iop.GChal b C => _root_.Iop.GChal.old c = u) =
      cnt (fun p : C × (Fin b → Bool) => p.1 = u) := h
  rw [h', cnt_fst (D := Fin b → Bool) (fun c : C => c = u), cnt_eq_const]
  simp

theorem kitMeasure : KitMeasure := by
  intro f d h
  have G := (_root_.Run.planDraws_law f d.entry d.kind h).1
  refine ⟨fun c => le_of_eq (elsOf_length f (Fmt.dsOf d.entry d.kind)
    ((bsRound f d.entry d.kind).φ (_root_.Iop.GChal.old (b := d.entry.work) c))),
    fun j n L hL => ?_⟩
  have s1 := cnt_old_le (C := Fin (bsRound f d.entry d.kind).b → _root_.Iop.Dig 256) d.entry.work
    (fun u => BadAt L j (elsOf f (Fmt.dsOf d.entry d.kind) ((bsRound f d.entry d.kind).φ u)))
  have s2 := cnt_comp_le (bsRound f d.entry d.kind).φ G.fib
    (fun v => BadAt L j (elsOf f (Fmt.dsOf d.entry d.kind) v))
  have s3 := cnt_vals_le f n (Fmt.dsOf d.entry d.kind) j L hL
  have s : cnt (fun c : _root_.Iop.GChal d.entry.work
        (Fin (bsRound f d.entry d.kind).b → _root_.Iop.Dig 256) =>
      BadAt L j (elsOf f (Fmt.dsOf d.entry d.kind)
        ((bsRound f d.entry d.kind).φ (_root_.Iop.GChal.old c)))) ≤ n * kitF f d := by
    refine le_trans s1 (le_trans (Nat.mul_le_mul_right _ (le_trans s2
      (Nat.mul_le_mul_right _ s3))) (le_of_eq ?_))
    unfold kitF
    ring
  exact s

end VerifiableInference.Desc.Sound
