-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/G9/Split.lean: splitting a joined transcript without building its shape.

Why. Tr.fst and Tr.snd (Iop/Shape.lean) match on the shape, so code that runs them builds the shape,
and a shape that mentions a definition without code cannot be built by code. (The list of all
challenges of a round is no obstacle: a Round holds it behind a function of Unit, which compiled
code calls only where the list is read.)

Main names:
  Cut α β γ: how a type α of joined transcripts falls into a first part β and a second part γ: one
    constructor for each round of the first part. It holds types alone, which compiled code erases.
  Cut.fst, Cut.snd: the two parts.
  cutOf s t: the cut of two shapes. It matches on s and is meant for statements. For a list s that
    is written out it equals .cons _ _ (.. (.nil _)) by rfl.
  cut_fst, cut_snd: (cutOf s t).fst = Tr.fst and (cutOf s t).snd = Tr.snd.
  seqVC, Tot.seqC, Tot.ior_seqC: the function seqV and the rules Tot.seq and Tot.ior_seq of
    Cb/G9/Tot.lean, with a cut.
  fstN, sndN: the same split by recursion on the number of rounds of s, with casts along equations
    of types; fstN_eq, sndN_eq, seqVN, Tot.seqN.

Which to take. fstN and sndN have the shapes among their arguments. They do not match on them, but a
definition that calls them must be able to name the shapes in code: a shape that mentions a
definition without code, such as the library's pDummy, is refused there. A Cut has no shape among
its arguments, so it also serves blocks that are written with pDummy.

Limits: a Cut with code is given for lists that are written out. Nothing is said on soundness,
knowledge soundness or hiding.

Sources. seqVN, Tot.seqN, seqVC, Tot.seqC and the statement of Tot.ior_seqC resemble two
files of the Lean library ArkLib (https://github.com/Verified-zkEVM/ArkLib; Apache-2.0):
ArkLib/OracleReduction/Composition/Sequential/IsPure.lean, lines 34 to 50 (Copyright (c) 2024-2026
ArkLib Contributors), and ArkLib/OracleReduction/Basic.lean, lines 994 to 996 and 1011 to 1015
(Copyright (c) 2024-2025 ArkLib Contributors). lean/CREDITS.md has ArkLib's entry.



-/
import Cb.G9.Tot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TWhole.G9
open Iop

theorem tr_drop_succ (s t : Shape) (k : ℕ) (h : k < s.length) :
    Tr (s.drop k ++ t) = ((s[k]).Msg × (s[k]).Chal × Tr (s.drop (k + 1) ++ t)) := by
  rw [List.drop_eq_getElem_cons h]; rfl

theorem tr_drop_all (s t : Shape) (k : ℕ) (h : s.length ≤ k) : Tr (s.drop k ++ t) = Tr t := by
  rw [List.drop_of_length_le h]; rfl

theorem tr_drop_succ0 (s : Shape) (k : ℕ) (h : k < s.length) :
    Tr (s.drop k) = ((s[k]).Msg × (s[k]).Chal × Tr (s.drop (k + 1))) := by
  rw [List.drop_eq_getElem_cons h]; rfl

theorem tr_drop_all0 (s : Shape) (k : ℕ) (h : s.length ≤ k) : Tr (s.drop k) = Unit := by
  rw [List.drop_of_length_le h]; rfl

/-- The second part, from round k on; n rounds of s are still to be passed over. -/
def sndFrom (s t : Shape) : (n k : ℕ) → k + n = s.length → Tr (s.drop k ++ t) → Tr t
  | 0, k, h, τ => cast (tr_drop_all s t k (by omega)) τ
  | n + 1, k, h, τ => sndFrom s t n (k + 1) (by omega) (cast (tr_drop_succ s t k (by omega)) τ).2.2

/-- The first part, from round k on. -/
def fstFrom (s t : Shape) : (n k : ℕ) → k + n = s.length → Tr (s.drop k ++ t) → Tr (s.drop k)
  | 0, k, h, _ => cast (tr_drop_all0 s k (by omega)).symm ()
  | n + 1, k, h, τ =>
    cast (tr_drop_succ0 s k (by omega)).symm
      ((cast (tr_drop_succ s t k (by omega)) τ).1, (cast (tr_drop_succ s t k (by omega)) τ).2.1,
        fstFrom s t n (k + 1) (by omega) (cast (tr_drop_succ s t k (by omega)) τ).2.2)

/-- Tr.snd, by the number of rounds of s. -/
def sndN (s t : Shape) (n : ℕ) (h : n = s.length) (τ : Tr (s ++ t)) : Tr t :=
  sndFrom s t n 0 (by omega) τ

/-- Tr.fst, by the number of rounds of s. -/
def fstN (s t : Shape) (n : ℕ) (h : n = s.length) (τ : Tr (s ++ t)) : Tr s :=
  fstFrom s t n 0 (by omega) τ

theorem snd_of_nil {u t : Shape} (e : u = []) (e' : Tr (u ++ t) = Tr t) (τ : Tr (u ++ t)) :
    Tr.snd (s := u) τ = cast e' τ := by
  subst e; rfl

theorem snd_of_cons {u u' t : Shape} {r : Round} (e : u = r :: u')
    (e' : Tr (u ++ t) = (r.Msg × r.Chal × Tr (u' ++ t))) (τ : Tr (u ++ t)) :
    Tr.snd (s := u) τ = Tr.snd (s := u') (cast e' τ).2.2 := by
  subst e; rfl

theorem fst_of_nil {u t : Shape} (e : u = []) (e'' : Tr u = Unit) (τ : Tr (u ++ t)) :
    Tr.fst (s := u) τ = cast e''.symm () := by
  subst e; rfl

theorem fst_of_cons {u u' t : Shape} {r : Round} (e : u = r :: u')
    (e' : Tr (u ++ t) = (r.Msg × r.Chal × Tr (u' ++ t))) (e'' : Tr u = (r.Msg × r.Chal × Tr u'))
    (τ : Tr (u ++ t)) :
    Tr.fst (s := u) τ =
      cast e''.symm ((cast e' τ).1, (cast e' τ).2.1, Tr.fst (s := u') (cast e' τ).2.2) := by
  subst e; rfl

theorem sndFrom_eq (s t : Shape) : ∀ (n k : ℕ) (h : k + n = s.length) (τ : Tr (s.drop k ++ t)),
    sndFrom s t n k h τ = Tr.snd (s := s.drop k) τ
  | 0, k, h, τ => (snd_of_nil (List.drop_of_length_le (by omega)) _ τ).symm
  | n + 1, k, h, τ => by
    show sndFrom s t n (k + 1) _ (cast (tr_drop_succ s t k (by omega)) τ).2.2 = _
    rw [sndFrom_eq s t n (k + 1)]
    exact (snd_of_cons (List.drop_eq_getElem_cons (by omega)) _ τ).symm

theorem fstFrom_eq (s t : Shape) : ∀ (n k : ℕ) (h : k + n = s.length) (τ : Tr (s.drop k ++ t)),
    fstFrom s t n k h τ = Tr.fst (s := s.drop k) τ
  | 0, k, h, τ =>
    (fst_of_nil (List.drop_of_length_le (by omega)) (tr_drop_all0 s k (by omega)) τ).symm
  | n + 1, k, h, τ => by
    show cast (tr_drop_succ0 s k (by omega)).symm
      ((cast (tr_drop_succ s t k (by omega)) τ).1, (cast (tr_drop_succ s t k (by omega)) τ).2.1,
        fstFrom s t n (k + 1) _ (cast (tr_drop_succ s t k (by omega)) τ).2.2) = _
    rw [fstFrom_eq s t n (k + 1)]
    exact (fst_of_cons (List.drop_eq_getElem_cons (by omega)) (tr_drop_succ s t k (by omega))
      (tr_drop_succ0 s k (by omega)) τ).symm

theorem sndN_eq (s t : Shape) (n : ℕ) (h : n = s.length) (τ : Tr (s ++ t)) :
    sndN s t n h τ = Tr.snd (s := s) τ := sndFrom_eq s t n 0 (by omega) τ

theorem fstN_eq (s t : Shape) (n : ℕ) (h : n = s.length) (τ : Tr (s ++ t)) :
    fstN s t n h τ = Tr.fst τ := fstFrom_eq s t n 0 (by omega) τ

variable {A B C : Type}

/-- Two total verifiers in turn, on a joined transcript, split by the number of the first one's
rounds. -/
def seqVN (s₁ s₂ : Shape) (n : ℕ) (h : n = s₁.length) (v₁ : A → Tr s₁ → B) (v₂ : B → Tr s₂ → C)
    (a : A) (τ : Tr (s₁ ++ s₂)) : C :=
  v₂ (v₁ a (fstN s₁ s₂ n h τ)) (sndN s₁ s₂ n h τ)

theorem seqVN_eq (s₁ s₂ : Shape) (n : ℕ) (h : n = s₁.length) (v₁ : A → Tr s₁ → B)
    (v₂ : B → Tr s₂ → C) : seqVN s₁ s₂ n h v₁ v₂ = seqV s₁ s₂ v₁ v₂ := by
  funext a τ
  unfold seqVN seqV
  rw [fstN_eq, sndN_eq]

theorem Tot.seqN {K₁ : Reduction A B} {K₂ : Reduction B C} {v₁ : A → Tr K₁.shape → B}
    {v₂ : B → Tr K₂.shape → C} (h₁ : Tot K₁ v₁) (h₂ : Tot K₂ v₂) (n : ℕ) (h : n = K₁.shape.length) :
    Tot (K₁.seq K₂) (seqVN K₁.shape K₂.shape n h v₁ v₂) := by
  rw [seqVN_eq]
  exact Tot.seq h₁ h₂

/-! ## The split as a small piece of data over types: no shape among the arguments -/

/-- How a type of joined transcripts falls into a first and a second part: one «cons» a round of the
first part. -/
inductive Cut : Type → Type → Type → Type 1 where
  | nil (T : Type) : Cut T Unit T
  | cons (M Ch : Type) {α β γ : Type} (c : Cut α β γ) : Cut (M × Ch × α) (M × Ch × β) γ

def Cut.fst : {α β γ : Type} → Cut α β γ → α → β
  | _, _, _, .nil _, _ => ()
  | _, _, _, .cons _ _ c, (m, ch, a) => (m, ch, c.fst a)

def Cut.snd : {α β γ : Type} → Cut α β γ → α → γ
  | _, _, _, .nil _, a => a
  | _, _, _, .cons _ _ c, (_, _, a) => c.snd a

/-- The cut of two shapes. It recurses on the shape and is meant for statements; for a list that is
written out it is .cons _ _ (.. (.nil _)) by rfl. -/
def cutOf : (s t : Shape) → Cut (Tr (s ++ t)) (Tr s) (Tr t)
  | [], t => .nil (Tr t)
  | r :: s, t => .cons r.Msg r.Chal (cutOf s t)

theorem cut_fst : ∀ (s t : Shape) (τ : Tr (s ++ t)), (cutOf s t).fst τ = Tr.fst τ
  | [], _, _ => rfl
  | _ :: s, t, (m, c, a) => congrArg (fun x => (m, c, x)) (cut_fst s t a)

theorem cut_snd : ∀ (s t : Shape) (τ : Tr (s ++ t)), (cutOf s t).snd τ = Tr.snd (s := s) τ
  | [], _, _ => rfl
  | _ :: s, t, (_, _, a) => cut_snd s t a

/-- Two total verifiers in turn on a joined transcript, split by a cut: its arguments are types and
functions alone. -/
def seqVC {T T₁ T₂ : Type} (c : Cut T T₁ T₂) (v₁ : A → T₁ → B) (v₂ : B → T₂ → C) (a : A) (τ : T) :
    C :=
  v₂ (v₁ a (c.fst τ)) (c.snd τ)

theorem Tot.seqC {K₁ : Reduction A B} {K₂ : Reduction B C} {v₁ : A → Tr K₁.shape → B}
    {v₂ : B → Tr K₂.shape → C} (h₁ : Tot K₁ v₁) (h₂ : Tot K₂ v₂)
    (c : Cut (Tr (K₁.shape ++ K₂.shape)) (Tr K₁.shape) (Tr K₂.shape))
    (hc : c = cutOf K₁.shape K₂.shape) :
    Tot (K₁.seq K₂) (seqVC c v₁ v₂) := by
  subst hc
  intro a τ
  rw [Tot.seq h₁ h₂ a τ]
  unfold seqVC seqV
  rw [cut_fst, cut_snd]

/-- The same for two IORs joined by the library's IOR.seq. -/
theorem Tot.ior_seqC {X₁ X₂ X₃ : Type} {E₁ E₂ E₃ : ExtSpec} {R₁ : IOR X₁ E₁ X₂ E₂}
    {R₂ : IOR X₂ E₂ X₃ E₃} {v₁ : X₁ × E₁.Str → Tr R₁.shape → X₂ × E₂.Str}
    {v₂ : X₂ × E₂.Str → Tr R₂.shape → X₃ × E₃.Str} (h₁ : Tot R₁.red v₁) (h₂ : Tot R₂.red v₂)
    (c : Cut (Tr (R₁.shape ++ R₂.shape)) (Tr R₁.shape) (Tr R₂.shape))
    (hc : c = cutOf R₁.shape R₂.shape) : Tot (R₁.seq R₂).red (seqVC c v₁ v₂) := fun a τ =>
  (IOR.red_seq_out R₁ R₂ a τ).trans (Tot.seqC h₁ h₂ c hc a τ)

end TWhole.G9

#print axioms TWhole.G9.sndN_eq
#print axioms TWhole.G9.fstN_eq
#print axioms TWhole.G9.seqVN_eq
#print axioms TWhole.G9.Tot.seqN
#print axioms TWhole.G9.cut_fst
#print axioms TWhole.G9.cut_snd
#print axioms TWhole.G9.Tot.seqC
#print axioms TWhole.G9.Tot.ior_seqC
