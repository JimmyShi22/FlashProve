-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpInst2.lean: for the assembled lookup `LkAsm2` (Cb/Ld/LdLkpAsm2.lean): the table's forest
with the public factor at the bit positions, and its top claim closed without revealing (exactly: no
map is revealed: `PscPar.core`, Cb/Ld/LdPsc.lean).
This file is about the table's side of a lookup argument with multiplicities in bits: the product
trees over the table.

Definitions, statements (in `Cb.Spec`) and proofs.

Why: `I.DT` (Cb/Ld/LdLkpInst.lean) has the leaf 1 + bit (u, j) · (λ - 1 - entry u) at all 2^w bit
positions j, of which only the first n + 1 count; that the product at an idle position is 1 is a
claim of its own in `LkAsm` (Cb/Ld/LdLkpAsm.lean) (`LkHead.Idle`, Cb/Ld/LdLkpHead.lean), true
because honest bits are 0 there.
Here the leaf carries a public factor, 1 at the counting positions and 0 at the others:
1 + On j · bit (u, j) · (λ - 1 - entry u). So the product at an idle position is 1 for all messages.
The factor is absorbed into the bits: `I.bitOn n m u j` is the entry at bAt u j if j < n + 1, else
0; the leaf is `facT` of Cb/Gen/LkpAlg.lean at these bits, and all of Cb/Ld/LdLkpNum.lean applies as
it stands.

Main names:
  `I.DT2 n`: the forest (`TreeP`, Cb/Ld/LdLkpTreeP.lean): as `I.DT`, at the bits with the factor.
  `I.endU n wE`: the closing of its top claim without revealing (Cb/Ld/LdLkpEndU.lean) (exactly: no
    map is revealed: `PscPar.core`, Cb/Ld/LdPsc.lean): public vector On j · (λ - 1 - entry u). The
    closing's i-th variable is coordinate `I.oE` i, weighted at that coordinate of the forest's top
    point (by default coordinate i).
  `Spec.ldLkpInst2_step`: an entry of a level is the product of the two above it.
  `Spec.ldLkpInst2_root`: level 0 at the position θ is the product over the table at that position,
    at the bits with the factor.
  `Spec.ldLkpInst2_count`, `Spec.ldLkpInst2_idle`: at a counting position that product is the
    product at the bits without the factor (`I.bit`); it is 1 at an idle position, for all messages.
  `Spec.ldLkpInst2_top_iff`, `Spec.ldLkpInst2_top`: the sum claim at the top of the forest is the
    closing block's claim; the tree's joint at level d is the closing block's input joint.

Limits: this file says nothing on the bits at idle positions: no claim reads them but the bit test
and the closing block's end row (Y at the end point: `LkEndU.rowB`, Cb/Ld/LdLkpEndU.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpInstProofs
import Cb.Ld.LdLkpEndU

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob Cb.Lkp

noncomputable section

namespace LkInst
variable {E : Type} [Field E] [Fintype E] (I : LkInst E) (n : ℕ)

/-- the bits with the public factor -/
def bitOn (m : I.J → E) : ℕ → ℕ → E := fun u j => if j < n + 1 then m (I.bAt u j) else 0

/-- The table's forest. -/
def DT2 : TreeP E where
  St0 := I.X
  J := I.J
  g := I.w
  U := fun x m l => cubeLvl I.w I.d (facT I.w (I.tab (I.st x)) (I.bitOn n m) (I.lam x)) l
  inc0 := fun x ϱ j => ∑ θ, Alg.eqk ϱ θ * I.formT x θ j
  wAt := I.wT
  cAt := I.cT
  sg := I.oT

/-- The closing of the forest's top claim, where no map is revealed (`PscPar.core`,
Cb/Ld/LdPsc.lean). Its j-th variable (j from 0, in the order of their rounds) is coordinate oE j
and has the equality weight at coordinate oE j of the forest's top point; the places of the bits and
the public vector are read at the corner whose coordinate v is the variable number oE⁻¹ v.
`LkEndU` has no order of its own: this block's `tAt`, `cp` and points (`z`, `fn`, its end point) go
by variable, entry j being coordinate oE j; the bit test's point (`ZeroCube.fn`, Cb/Ld/LdZero.lean)
goes by coordinate. -/
def endU (wE : PIdx (List.replicate (I.w + I.d) (pfCube E 2)) → I.J) : LkEndU E where
  X := ((I.DT2 n).lv I.d).T.St
  J := I.J
  k := I.w + I.d
  tAt := fun b => I.tAt fun v => b (I.oE.symm v)
  z := fun s j => ((I.DT2 n).lv I.d).pnt s (I.oE j)
  cp := fun s b =>
    if numLE (fun v => b (I.oE.symm v)) % 2 ^ I.w < n + 1 then
      I.lam (((I.DT2 n).lv I.d).base s) - 1 -
        I.tab (I.st (((I.DT2 n).lv I.d).base s)) (numLE (fun v => b (I.oE.symm v)) / 2 ^ I.w)
    else 0
  inc := fun s => pushJ ((I.DT2 n).lv I.d).toJ (((I.DT2 n).lv I.d).T.slS s)
  wAt := wE

end LkInst
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp
variable (E : Type) [Field E] [Fintype E]

def ldLkpInst2_step : Prop := ∀ (I : LkInst E) (n : ℕ), (I.DT2 n).Step

def ldLkpInst2_root : Prop :=
  ∀ (I : LkInst E) (n : ℕ) x m (θ : Fin (I.w + 0) → Bool),
    (I.DT2 n).U x m 0 θ = tabProd I.d (I.tab (I.st x)) (I.bitOn n m) (I.lam x) (numLE θ)

def ldLkpInst2_count : Prop :=
  ∀ (I : LkInst E) (n : ℕ) (t : ℕ → E) (m : I.J → E) (al : E) (j : ℕ),
    j < n + 1 → tabProd I.d t (I.bitOn n m) al j = tabProd I.d t (I.bit m) al j

/-- At an idle position the product is 1, for all messages. -/
def ldLkpInst2_idle : Prop :=
  ∀ (I : LkInst E) (n : ℕ) (t : ℕ → E) (m : I.J → E) (al : E) (j : ℕ),
    n + 1 ≤ j → tabProd I.d t (I.bitOn n m) al j = 1

def ldLkpInst2_top_iff : Prop :=
  ∀ (I : LkInst E) (n : ℕ) wE (x : E × ((I.DT2 n).lv I.d).T.St) (m : I.J → E),
    ((I.DT2 n).lv I.d).T.SumHolds x (fun j => m (((I.DT2 n).lv I.d).toJ j)) ↔
    (I.endU n wE).Holds x m

/-- The tree's joint at level d is the closing block's input joint. -/
def ldLkpInst2_top : Prop :=
  ∀ (I : LkInst E) (n : ℕ) wE (Ex : ExtSpec) (M Wp Kc : Type) (msg : M → I.J → E)
      (A0 : Rels Kc ((I.DT2 n).lv 0).T.St Ex (M × Wp)),
    (I.DT2 n).jtAt msg A0 I.d = (I.endU n wE).relsIn ((I.DT2 n).ride msg A0 I.d) fun w => msg w.1

end Cb.Spec

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

theorem ldLkpInst2_step : Spec.ldLkpInst2_step E := fun I n x m l b =>
  ldLkpNum_step E I.w I.d (facT I.w (I.tab (I.st x)) (I.bitOn n m) (I.lam x)) l b

theorem ldLkpInst2_root : Spec.ldLkpInst2_root E := fun I n x m θ =>
  ldLkpNum_rootT E I.w I.d (I.tab (I.st x)) (I.bitOn n m) (I.lam x) θ

theorem ldLkpInst2_count : Spec.ldLkpInst2_count E := fun I n t m al j hj =>
  Finset.prod_congr rfl fun u _ => by
    show 1 + (if j < n + 1 then m (I.bAt u j) else 0) * (al - 1 - t u) =
      1 + m (I.bAt u j) * (al - 1 - t u)
    rw [if_pos hj]

theorem ldLkpInst2_idle : Spec.ldLkpInst2_idle E := fun I n t m al j hj =>
  Finset.prod_eq_one fun u _ => by
    show 1 + (if j < n + 1 then m (I.bAt u j) else 0) * (al - 1 - t u) = 1
    rw [if_neg (Nat.not_lt.mpr hj), zero_mul, add_zero]

theorem ldLkpInst2_top_iff : Spec.ldLkpInst2_top_iff E := by
  intro I n wE x m
  rw [ldLkpP_sum E (I.DT2 n) (ldLkpInst2_step E I n) I.d x m]
  have hU : (I.DT2 n).U (((I.DT2 n).lv I.d).base x.2) m I.d =
      fun b : Fin (I.w + I.d) → Bool => 1 + m (I.tAt b) *
        (if numLE b % 2 ^ I.w < n + 1 then
          I.lam (((I.DT2 n).lv I.d).base x.2) - 1 -
            I.tab (I.st (((I.DT2 n).lv I.d).base x.2)) (numLE b / 2 ^ I.w)
        else 0) := by
    funext b
    refine (ldLkpNum_topT E I.w I.d _ _ _ b).trans ?_
    show 1 + (if numLE b % 2 ^ I.w < n + 1 then m (I.bAt (numLE b / 2 ^ I.w) (numLE b % 2 ^ I.w))
            else 0) * _ =
      1 + m (I.tAt b) * (if numLE b % 2 ^ I.w < n + 1 then _ else 0)
    by_cases h : numLE b % 2 ^ I.w < n + 1
    · rw [if_pos h, if_pos h]
      rfl
    · rw [if_neg h, if_neg h, zero_mul, mul_zero]
  rw [hU, ← ldLkpP_push E _ _ ((I.DT2 n).lv I.d).toJ (((I.DT2 n).lv I.d).T.slS x.2) m]
  have h := Alg.mle_equiv I.oE
    (fun b : Fin (I.w + I.d) → Bool => 1 + m (I.tAt b) *
      (if numLE b % 2 ^ I.w < n + 1 then
        I.lam (((I.DT2 n).lv I.d).base x.2) - 1 -
          I.tab (I.st (((I.DT2 n).lv I.d).base x.2)) (numLE b / 2 ^ I.w)
      else 0)) (((I.DT2 n).lv I.d).pnt x.2)
  exact Iff.of_eq (congrArg (fun t =>
    t + ∑ j, pushJ ((I.DT2 n).lv I.d).toJ (((I.DT2 n).lv I.d).T.slS x.2) j * m j = x.1) h.symm)

theorem ldLkpInst2_top : Spec.ldLkpInst2_top E := fun I n wE _ _ _ _ msg _ =>
  LdLkp.rels_ext (funext fun x =>
      funext fun _ =>
        funext fun w => propext (and_congr_right fun _ => ldLkpInst2_top_iff E I n wE x (msg w.1)))
    (funext fun a =>
      funext fun w => propext (and_congr_right fun _ => ldLkpInst2_top_iff E I n wE a.1 (msg w.1)))
    rfl rfl

end
end Cb
