-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/EraseKit.lean: general lemmas on `erase`, the map from programs with tokens to ordinary
oracle algorithms.

Compile/Star.lean defines `erase`; Compile/Batch/Star.lean makes the scheme's committer and prover
from `erase` of programs (`Step`, Rom/Defer.lean): a token is an index into a list of strings (the
store), `fresh` and `marked` append to the store, `reveal` reads it.
  Part 1  erase of each constructor, erase of bind
  Part 2  the outputs of an oracle algorithm under fixed oracle functions
  Part 3  a small calculus of postconditions for erased programs under fixed oracle functions; the
          store only grows
-/
import Compile.Star
import Rom.EagerLazy

noncomputable section

namespace Compile
open Iop Rom

/-! ## Part 1. erase -/

section Erase

variable {S : OSpec} {sp : Split S} {α β : Type}

theorem step_bind_eq (c : Step S sp α) (g : α → Step S sp β) : (c >>= g) = c.bind g := rfl

theorem step_pure_eq (a : α) : (pure a : Step S sp α) = Step.pure a := rfl

@[simp] theorem erase_pure (a : α) (vs : List Bits) :
    erase (Step.pure a : Step S sp α) vs = OComp.pure (a, vs) := rfl

@[simp] theorem erase_sample (n : ℕ) (k : Fin (n + 1) → Step S sp α) (vs : List Bits) :
    erase (Step.sample n k) vs = OComp.sample n fun r => erase (k r) vs := rfl

@[simp] theorem erase_plain (o : S.ι) (q : S.Dom o) (k : S.Rng o → Step S sp α) (vs : List Bits) :
    erase (Step.plain o q k) vs = OComp.query o q fun r => erase (k r) vs := rfl

@[simp] theorem erase_fresh (l : ℕ) (k : Tok → Step S sp α) (vs : List Bits) :
    erase (Step.fresh l k) vs =
      OComp.sample (2 ^ l - 1) fun r =>
        erase (k vs.length) (vs ++ [List.ofFn fun i : Fin l => r.val.testBit i]) := rfl

@[simp] theorem erase_marked (o : S.ι) (t : Tok) (us : List Tok)
    (pt : Bits → List Bits → S.Dom o) (inj : ∀ vs, Function.Injective fun v => pt v vs)
    (k : sp.Vis o → Tok → Step S sp α) (vs : List Bits) :
    erase (Step.marked o t us pt inj k) vs =
      OComp.query o (pt (vs.getD t []) (us.map fun u => vs.getD u [])) fun r =>
        erase (k (sp.split o r).1 vs.length) (vs ++ [List.ofFn (sp.split o r).2]) := rfl

@[simp] theorem erase_reveal (ts : List Tok) (k : List Bits → Step S sp α) (vs : List Bits) :
    erase (Step.reveal ts k) vs = erase (k (ts.map fun u => vs.getD u [])) vs := rfl

/-- erase of a sequence: the second program starts from the store that the first one leaves. -/
theorem erase_bind (c : Step S sp α) (g : α → Step S sp β) (vs : List Bits) :
    erase (c.bind g) vs = (erase c vs).bind fun o => erase (g o.1) o.2 := by
  induction c generalizing vs with
  | pure a => rfl
  | sample n k ih => simp only [Step.bind, erase, OComp.bind, ih]
  | plain o q k ih => simp only [Step.bind, erase, OComp.bind, ih]
  | fresh l k ih => simp only [Step.bind, erase, OComp.bind, ih]
  | marked o t us pt inj k ih => simp only [Step.bind, erase, OComp.bind, ih]
  | reveal ts k ih => simp only [Step.bind, erase, ih]

end Erase

/-! ## Part 2. Outputs under fixed oracle functions -/

section Outs

variable {S : OSpec} {α β : Type}

/-- The values that the algorithm can return under the oracle functions f, over its coins. -/
def Outs (f : Fam S) (c : OComp S α) : Set α := (c.runEager f).support

variable {f : Fam S}

@[simp] theorem mem_outs_pure {a b : α} : b ∈ Outs f (OComp.pure a : OComp S α) ↔ b = a := by
  simp [Outs, OComp.runEager]

@[simp] theorem mem_outs_query {o : S.ι} {q : S.Dom o} {k : S.Rng o → OComp S α} {b : α} :
    b ∈ Outs f (OComp.query o q k) ↔ b ∈ Outs f (k (f o q)) := Iff.rfl

@[simp] theorem mem_outs_sample {n : ℕ} {k : Fin (n + 1) → OComp S α} {b : α} :
    b ∈ Outs f (OComp.sample n k) ↔ ∃ r, b ∈ Outs f (k r) := by
  simp [Outs, OComp.runEager]

theorem mem_outs_bind {c : OComp S α} {g : α → OComp S β} {b : β} :
    b ∈ Outs f (c.bind g) ↔ ∃ a ∈ Outs f c, b ∈ Outs f (g a) := by
  simp only [Outs, OComp.runEager_bind, PMF.mem_support_bind_iff]

end Outs

/-! ## Part 3. Postconditions -/

section Tri

variable {S : OSpec} {sp : Split S} {α β : Type} {f : Fam S}

/-- Postcondition. Under the oracle functions f, whatever the coins, the erased program c, started
with the store vs, returns a value a and a store vs' with Q a vs'. -/
def Tri (f : Fam S) (c : Step S sp α) (vs : List Bits) (Q : α → List Bits → Prop) : Prop :=
  ∀ o ∈ Outs f (erase c vs), Q o.1 o.2

theorem Tri.mono {c : Step S sp α} {vs : List Bits} {Q R : α → List Bits → Prop} (h : Tri f c vs Q)
    (hQR : ∀ a vs', Q a vs' → R a vs') : Tri f c vs R := fun o ho => hQR _ _ (h o ho)

theorem Tri.and {c : Step S sp α} {vs : List Bits} {Q R : α → List Bits → Prop}
    (h : Tri f c vs Q) (h' : Tri f c vs R) :
    Tri f c vs fun a vs' => Q a vs' ∧ R a vs' :=
  fun o ho => ⟨h o ho, h' o ho⟩

theorem tri_pure_iff {a : α} {vs : List Bits} {Q : α → List Bits → Prop} :
    Tri f (Step.pure a : Step S sp α) vs Q ↔ Q a vs := by
  simp [Tri]

theorem Tri.bind {c : Step S sp α} {g : α → Step S sp β} {vs : List Bits} {Q : α → List Bits → Prop}
    {R : β → List Bits → Prop} (h : Tri f c vs Q) (hg : ∀ a vs', Q a vs' → Tri f (g a) vs' R) :
    Tri f (c.bind g) vs R := by
  intro o ho
  rw [erase_bind] at ho
  obtain ⟨x, hx, hox⟩ := mem_outs_bind.1 ho
  exact hg x.1 x.2 (h x hx) o hox

theorem tri_sample_iff {n : ℕ} {k : Fin (n + 1) → Step S sp α}
    {vs : List Bits} {Q : α → List Bits → Prop} :
    Tri f (Step.sample n k) vs Q ↔ ∀ r, Tri f (k r) vs Q := by
  simp only [Tri, erase_sample, mem_outs_sample]
  constructor
  · intro h r o ho; exact h o ⟨r, ho⟩
  · rintro h o ⟨r, ho⟩; exact h r o ho

theorem tri_plain_iff {o : S.ι} {q : S.Dom o} {k : S.Rng o → Step S sp α}
    {vs : List Bits} {Q : α → List Bits → Prop} :
    Tri f (Step.plain o q k) vs Q ↔ Tri f (k (f o q)) vs Q := Iff.rfl

theorem tri_fresh_iff {l : ℕ} {k : Tok → Step S sp α} {vs : List Bits} {Q : α → List Bits → Prop} :
    Tri f (Step.fresh l k) vs Q ↔
    ∀ r : Fin (2 ^ l - 1 + 1),
      Tri f (k vs.length) (vs ++ [List.ofFn fun i : Fin l => r.val.testBit i]) Q := by
  simp only [Tri, erase_fresh, mem_outs_sample]
  constructor
  · intro h r o ho; exact h o ⟨r, ho⟩
  · rintro h o ⟨r, ho⟩; exact h r o ho

theorem tri_marked_iff {o : S.ι} {t : Tok} {us : List Tok} {pt : Bits → List Bits → S.Dom o}
    {inj : ∀ vs, Function.Injective fun v => pt v vs} {k : sp.Vis o → Tok → Step S sp α}
    {vs : List Bits} {Q : α → List Bits → Prop} :
    Tri f (Step.marked o t us pt inj k) vs Q ↔
    Tri f (k (sp.split o (f o (pt (vs.getD t []) (us.map fun u => vs.getD u [])))).1 vs.length)
      (vs ++ [List.ofFn (sp.split o (f o (pt (vs.getD t []) (us.map fun u => vs.getD u [])))).2])
      Q := Iff.rfl

theorem tri_reveal_iff {ts : List Tok} {k : List Bits → Step S sp α}
    {vs : List Bits} {Q : α → List Bits → Prop} :
    Tri f (Step.reveal ts k) vs Q ↔ Tri f (k (ts.map fun u => vs.getD u [])) vs Q := Iff.rfl

/-- The store only grows. -/
theorem tri_prefix (c : Step S sp α) (vs : List Bits) : Tri f c vs fun _ vs' => vs <+: vs' := by
  induction c generalizing vs with
  | pure a => exact tri_pure_iff.2 (List.prefix_refl vs)
  | sample n k ih => exact tri_sample_iff.2 fun r => ih r vs
  | plain o q k ih => exact tri_plain_iff.2 (ih _ vs)
  | fresh l k ih =>
    exact tri_fresh_iff.2 fun r => (ih _ _).mono fun _ _ h => (List.prefix_append vs _).trans h
  | marked o t us pt inj k ih =>
    exact tri_marked_iff.2 ((ih _ _ _).mono fun _ _ h => (List.prefix_append vs _).trans h)
  | reveal ts k ih => exact tri_reveal_iff.2 (ih _ vs)

/-- Every postcondition may assume that the store has grown. -/
theorem Tri.with_prefix {c : Step S sp α} {vs : List Bits}
    {Q : α → List Bits → Prop} (h : Tri f c vs Q) :
    Tri f c vs fun a vs' => Q a vs' ∧ vs <+: vs' :=
  h.and (tri_prefix c vs)

end Tri

/-- A token into a store keeps its string when the store grows. -/
theorem getD_of_prefix {vs vs' : List Bits} (h : vs <+: vs') {t : ℕ} (ht : t < vs.length) :
    vs'.getD t [] = vs.getD t [] := by
  obtain ⟨e, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left ht]

/-- The token that was added last has the string that was added. -/
theorem getD_concat_length (vs : List Bits) (v : Bits) : (vs ++ [v]).getD vs.length [] = v := by
  simp [List.getD_eq_getElem?_getD]

end Compile
