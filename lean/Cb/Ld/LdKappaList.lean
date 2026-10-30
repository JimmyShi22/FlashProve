-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdKappaList.lean: "every round's error, as a probability, is at most κ" (`Err.Below`,
Iop/InteractiveOracleProof.lean), read off two lists of numbers; the assembled lookup (`LkAsm2`,
Cb/Ld/LdLkpAsm2.lean), the zero-knowledge sumcheck (`PscPar`, Cb/Ld/LdPsc.lean) and the batching of
tensor rows in numbers. The quoted words say e ≤ κ · v, with e the round's error, a count of values
of its verifier message (`Err`, Iop/Rbr.lean), and v the number of all values of that message. These
errors are numbers that are listed for a sub-protocol (`(A.baseN ..).P.err`, `(A.subIN ..).P.err`,
`Y.errC`, `Y.err`, `(B.nums ..).err`): that a sub-protocol is sound at the numbers that are listed
for it is no statement of this file.

Definitions (on numbers) and theorems: glue; nothing is evaluated.

Why: what κ is for is told in the head of Cb/Ld/LdKappaKit.lean.


Main names:
  `BelowNV κ es vs` (es: counts of exceptional values; vs: numbers of values of the verifier
    messages).
  `Err.below_iff_lists`: `Err.Below ε κ` ↔ `BelowNV κ` (the list of ε's errors) (the list of the
    shape's numbers of values) (`Err.toList`, `Shape.chalList`: Ior/KnowCollRulesChainErr.lean).
  `LkAsm2.Kap`: `A.Kap κ`, with q = |E|: five numbers:
    2^(`A.v'` + 1) - 1 ≤ κ q (the first challenge);
    2 ≤ κ q (a variable of a sumcheck; it covers the coefficient's and the line steps' 1);
    3 ≤ κ (q - 1) (the further variable, which is not 0: degrees 1, 2, 3);
    w q^(w-1) ≤ κ q^w, (w + d) q^(w+d-1) ≤ κ q^(w+d) (the two points).
  `ldKappa_lkp`, `ldKappa_lkpI`: `A.Kap κ` → every round's error of `A.baseN` (of `A.subIN`), as a
    probability, is at most κ.
  `ldKappa_pscC`, `ldKappa_psc`: `Y.Kap κ` (`PscPar.Kap`) → every error of its lists `Y.errC` (where
    no map is revealed: `PscPar.core`, Cb/Ld/LdPsc.lean) and `Y.err` (values revealed in a last
    round without a verifier message), as a probability, is at most κ.
  `ldKappa_batt`: `B.Kap κ` (B a batching of tensor rows, `BattPar`, Cb/Ld/LdBatt.lean) → every
    round's error of `B.nums`, as a probability, is at most κ.

Limits: this file says nothing on the size of any number. `A.Kap`'s second and third clause are
asked whether or not a sumcheck with a variable, or a tie's further step, occurs: slightly more
than the lists ask at degenerate parameters.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdKappaKit
import Cb.Ld.LdLkpAsm2ErrProofs
import Cb.Ld.LdBatt

set_option autoImplicit false

namespace Iop
open scoped ENNReal

/-- the two lists have the same length, and entry by entry e ≤ κ · v -/
def BelowNV (κ : ℝ≥0∞) : List ℕ → List ℕ → Prop :=
  List.Forall₂ fun e v => (e : ℝ≥0∞) ≤ κ * (v : ℝ≥0∞)

theorem Err.below_iff_lists :
    ∀ {s : Shape} (ε : Err s) (κ : ℝ≥0∞), Err.Below ε κ ↔ BelowNV κ ε.toList s.chalList
  | [], _, _ => ⟨fun _ => List.Forall₂.nil, fun _ => trivial⟩
  | _ :: _, (_, ε), κ => ⟨fun h => List.Forall₂.cons h.1 ((Err.below_iff_lists ε κ).1 h.2), fun h => by
      cases h with
      | cons h1 h2 => exact ⟨h1, (Err.below_iff_lists ε κ).2 h2⟩⟩

theorem belowNV_app {κ : ℝ≥0∞} {a b a' b' : List ℕ} (h : BelowNV κ a b) (h' : BelowNV κ a' b') :
    BelowNV κ (a ++ a') (b ++ b') :=
  List.rel_append h h'

theorem belowNV_one {κ : ℝ≥0∞} {e v : ℕ} (h : (e : ℝ≥0∞) ≤ κ * (v : ℝ≥0∞)) : BelowNV κ [e] [v] :=
  List.Forall₂.cons h List.Forall₂.nil

theorem belowNV_flatMap {α : Type} {κ : ℝ≥0∞} (f g : α → List ℕ) :
    ∀ l : List α, (∀ a, BelowNV κ (f a) (g a)) → BelowNV κ (l.flatMap f) (l.flatMap g)
  | [], _ => List.Forall₂.nil
  | a :: l, h => by
      rw [List.flatMap_cons, List.flatMap_cons]
      exact belowNV_app (h a) (belowNV_flatMap f g l h)

theorem belowNV_rep {κ : ℝ≥0∞} {e v : ℕ} (h : (e : ℝ≥0∞) ≤ κ * (v : ℝ≥0∞)) :
    ∀ k : ℕ, BelowNV κ (List.replicate k e) (List.replicate k v)
  | 0 => List.Forall₂.nil
  | k + 1 => List.Forall₂.cons h (belowNV_rep h k)

end Iop

namespace Cb
open Iop Prob Hiop IOR Cb.LdLkp
open scoped ENNReal

theorem belowNV_psc {κ : ℝ≥0∞} {q n D : ℕ} (h1 : ((1 : ℕ) : ℝ≥0∞) ≤ κ * (q : ℝ≥0∞))
    (hn : (n : ℝ≥0∞) ≤ κ * (q : ℝ≥0∞)) (hD : (D : ℝ≥0∞) ≤ κ * ((q - 1 : ℕ) : ℝ≥0∞)) (k : ℕ) :
    BelowNV κ (pscErrs k n D) (pscVals q k) :=
  List.Forall₂.cons h1
    (belowNV_app (belowNV_rep hn k) (List.Forall₂.cons hD (belowNV_one (by simp))))

theorem belowNV_core {κ : ℝ≥0∞} {q n : ℕ} (h1 : ((1 : ℕ) : ℝ≥0∞) ≤ κ * (q : ℝ≥0∞))
    (hn : (n : ℝ≥0∞) ≤ κ * (q : ℝ≥0∞)) (k : ℕ) :
    BelowNV κ (coreErrs k n) (coreVals q k) :=
  List.Forall₂.cons h1 (belowNV_rep hn k)

section
variable {E : Type} [Field E] [Fintype E]

/-- The assembled lookup: its five numbers (each told in the head). -/
structure LdLkp.LkAsm2.Kap (A : LkAsm2 E) (κ : ℝ≥0∞) : Prop where
  lam   : ((2 ^ (A.v' + 1) - 1 : ℕ) : ℝ≥0∞) ≤ κ * (Fintype.card E : ℝ≥0∞)
  two   : ((2 : ℕ) : ℝ≥0∞) ≤ κ * (Fintype.card E : ℝ≥0∞)
  three : ((3 : ℕ) : ℝ≥0∞) ≤ κ * ((Fintype.card E - 1 : ℕ) : ℝ≥0∞)
  ptW   : ((A.w * Fintype.card E ^ (A.w - 1) : ℕ) : ℝ≥0∞) ≤ κ * ((Fintype.card E ^ A.w : ℕ) : ℝ≥0∞)
  ptK   : (((A.w + A.d) * Fintype.card E ^ (A.w + A.d - 1) : ℕ) : ℝ≥0∞) ≤
    κ * ((Fintype.card E ^ (A.w + A.d) : ℕ) : ℝ≥0∞)

theorem ldKappa_lkpL (A : LkAsm2 E) (κ : ℝ≥0∞) (h : A.Kap κ) :
    BelowNV κ (A.errs (Fintype.card E)) (A.vals (Fintype.card E)) := by
  have h1 : ((1 : ℕ) : ℝ≥0∞) ≤ κ * (Fintype.card E : ℝ≥0∞) :=
    le_trans (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2)) h.two
  have d1 : ((1 : ℕ) : ℝ≥0∞) ≤ κ * ((Fintype.card E - 1 : ℕ) : ℝ≥0∞) :=
    le_trans (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 3)) h.three
  have d2 : ((2 : ℕ) : ℝ≥0∞) ≤ κ * ((Fintype.card E - 1 : ℕ) : ℝ≥0∞) :=
    le_trans (by exact_mod_cast (by norm_num : (2 : ℕ) ≤ 3)) h.three
  unfold LkAsm2.errs LkAsm2.vals
  exact belowNV_app
    (belowNV_app
      (belowNV_app
        (belowNV_app
          (belowNV_app (belowNV_one h.lam)
            (belowNV_app (belowNV_psc h1 h.two d1 0)
              (belowNV_flatMap _ _ _ fun _ => belowNV_psc h1 h.two h.three 0)))
          (belowNV_one h.ptW))
        (belowNV_app
          (belowNV_flatMap _ _ _ fun l =>
            belowNV_app (belowNV_psc h1 h.two d2 (0 + l)) (belowNV_one h1))
          (belowNV_flatMap _ _ _ fun l =>
            belowNV_app (belowNV_psc h1 h.two d2 (A.w + l)) (belowNV_one h1))))
      (belowNV_core h1 h.two (A.w + A.d)))
    (belowNV_app (belowNV_one h.ptK) (belowNV_psc h1 h.two d2 (A.w + A.d)))

theorem ldKappa_lkp (A : LkAsm2 E) (N : Type) (ι : N → A.J) (Ex : ExtSpec) (M Wp Kc : Type)
    (msg : M → A.J → E) (κ : ℝ≥0∞) (h : A.Kap κ) :
    Err.Below (A.baseN ι Ex M Wp Kc msg).P.err κ := by
  rw [Err.below_iff_lists, ldLkpAsm2E_errs E A N ι Ex M Wp Kc msg,
    ldLkpAsm2E_vals E A N ι Ex M Wp Kc msg]
  exact ldKappa_lkpL A κ h

theorem ldKappa_lkpI (A : LkAsm2 E) (N : Type) (ι : N → A.J) (C : ConfigurationWithOutOfDomainSample) (S : Sig E)
    (msg : C.Msg × S.Msg → A.J → E) (κ : ℝ≥0∞) (h : A.Kap κ) :
    Err.Below (A.subIN ι C S msg).P.err κ := by
  rw [Err.below_iff_lists, ((ldLkpAsm2E_sub E).2 A N ι C S msg).1,
    ((ldLkpAsm2E_sub E).2 A N ι C S msg).2]
  exact ldKappa_lkpL A κ h

/-- The sumcheck for a polynomial summand: its numbers: 1 ≤ κ |E| (the coefficient); for each
variable f of its format: f.n ≤ κ |f.Ch|. -/
structure PscPar.Kap (Y : PscPar E) (κ : ℝ≥0∞) : Prop where
  coef : ((1 : ℕ) : ℝ≥0∞) ≤ κ * (Fintype.card E : ℝ≥0∞)
  vars : ∀ f ∈ Y.fmt, (f.n : ℝ≥0∞) ≤ κ * (Fintype.card f.Ch : ℝ≥0∞)

omit [Fintype E] in
theorem pErr_below (κ : ℝ≥0∞) :
    ∀ l : List (PFmt E),
      (∀ f ∈ l, (f.n : ℝ≥0∞) ≤ κ * (Fintype.card f.Ch : ℝ≥0∞)) → Err.Below (pErr l) κ
  | [], _ => trivial
  | f :: l, h =>
    ⟨h f (List.mem_cons_self), pErr_below κ l fun g hg => h g (List.mem_cons_of_mem f hg)⟩

theorem ldKappa_pscC (Y : PscPar E) (Ex : ExtSpec) (κ : ℝ≥0∞) (h : Y.Kap κ) :
    Err.Below (Y.errC Ex) κ :=
  ⟨h.coef, pErr_below κ Y.fmt h.vars⟩

theorem ldKappa_psc (Y : PscPar E) (Ex : ExtSpec) (κ : ℝ≥0∞) (h : Y.Kap κ) :
    Err.Below (Y.err Ex) κ :=
  Err.Below.app (ldKappa_pscC Y Ex κ h) ⟨by simp, trivial⟩

/-- The batching of tensor rows: its numbers: the zero-evader's; the coefficient's; the degree n of
each of the k column variables, a challenge from all of E. -/
structure BattPar.Kap (B : BattPar E) (κ : ℝ≥0∞) : Prop where
  ev  : (B.Z.err : ℝ≥0∞) ≤ κ * (Fintype.card B.Z.D : ℝ≥0∞)
  psc : B.par.Kap κ

theorem ldKappa_batt (B : BattPar E) (Ex : ExtSpec) (Kc : Type) (κ : ℝ≥0∞) (h : B.Kap κ) :
    Err.Below (B.nums Ex Kc).err κ :=
  Err.Below.app (⟨h.ev, trivial⟩ : Err.Below (IOR.Nums.draw Kc B.Z.D B.nx Ex B.Z.err).err κ)
    (ldKappa_pscC B.par Ex κ h.psc)

end
end Cb
