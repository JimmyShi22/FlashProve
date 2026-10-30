-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefAsm.lean: the digits' lookup of the reference segment is the assembled lookup: what
the list of moves asks reduces to conditions on numbers and places. (not all hypotheses are named
here: see `Spec.ldSegRef_asm_hyp`)

This file takes the library's lookup protocol (`LkAsm2`, Cb/Ld/LdLkpAsm2.lean) for the lookup
argument on the range check's digits.
Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Req1/LdSegRefAsmProofs.lean.
A lookup claims that every key is an entry of the table, and a further clause `more`, which is
`True` here (`Lk.inR`, Cb/Ld/LdLkp.lean); its exact form adds a clause on the multiplicities
(`Lk.inP`).

Why: Cb/Req1/LdSegRefDig.lean takes the lookup as a parameter (any chain between the two stages
`Q.lkS`, `Q.lkT`) and the clause on the multiplicities as a hypothesis (`Q.Mult`). Here, under the
hypotheses of the statements below, both are discharged from the theorems of:
  Cb/Ld/LdLkpAsm2.lean, Cb/Ld/LdLkpAsm2Pull.lean: the assembled lookup (multiplicities in bits,
    product trees, the tie by a chain of sumchecks): it sends no oracle; its rows and its mask form
    read the named entries only; every explicit part that its verifier puts out lists the same
    number of rows.
  Cb/Ld/LdLkpMult.lean: which vectors of multiplicities make a lookup complete: the honest bits of
    each function are valid (`Spec.ldLkpMult_honest`: 2^n < 2^W, every key in the table); valid
    function by function is valid for the joint lookup at every shift.

Main names:
  `LdDgA`: the data: Q (Cb/Req1/LdSegRefDig.lean); ι: the entries that rows and mask form read,
    among all entries; w, n: 2^w bit positions of which the first n + 1 count; the places of the
    bits (bAt) and of the own masks of all blocks of the lookup (eleven fields), among the entries
    of all messages.
  `X.A`: the data of the assembled lookup (`LkAsm2`): state (explicit part, shift); entries: all
    entries of all messages; 2^(v+1) keys: the shifted digits, as functions of the entries at the
    digits' places; the shifted joint table of 2^(1+d) entries.
  `X.mult`: "the bits at their places write a valid vector of multiplicities" (the wide form:
    `LkAsm2.ValidMu`).
  `X.lk`: the lookup as a chain of one link.
  `X.Bits`: the law of the bits' places: if the part sent with the digits is what the honest prover
    derives, then at the places bAt Y j, for the 2^(1+d) entries Y of the joint table and the 2^w
    bit positions j (nothing is asked of bAt beyond them), stand the honest bits of the low digits'
    lookup and of the high digits' lookup, side by side.
  `Spec.ldSegRef_asm_L`: the lookup claim of Cb/Req1/LdSegRefDig.lean is that of the assembled
    lookup, read on all entries: by definition.
  `Spec.ldLkpMult_congr`: if W ≤ 2^w, "the bits write a valid vector" reads the bits of the table's
    entries at the 2^w positions only.
  `Spec.ldSegRef_asm_mult`: `Q.Mult X.mult`, from `p.OK`, the sizes (q, H ≤ 2^d; K ≤ 2^v),
    2^v < 2^(n+1), n + 1 ≤ 2^w and `X.Bits`.
  `Spec.ldSegRef_asm_allB`: the link has all of the bundle but zero knowledge, from: ι injective
    and its range holds all named places; the lookup's conditions on numbers (Adm). Here `Adm pp`
    is taken at the characteristic pp of E.
  `Spec.ldSegRef_asm_hyp`: all that the four moves ask, from conditions on numbers and places
    alone: `p.OK`, `Q.Places`, the sizes, the two tags differ, the three conditions of
    `Spec.ldSegRef_asm_allB`, `X.Bits` (a law of places that reads mkV too).

Limits: this file says nothing on zero knowledge. Under the hypotheses of `Spec.mj_chain`
(Cb/Ld/LdLkpMaskChain.lean), a lookup that sends no oracle has masked messages as a whole: it is
one masked block whose own masks are those of all its sumchecks (a composition of masked blocks and
of blocks without prover message: Ior/Masked.lean, Cb/Ld/LdLkpMaskChain.lean), in this sense: the
whole chain `Fits` (`MJ.Fits`), so it has the item "masked messages" (`Honest.MM`, Ior/Masked.lean).
For the assembled lookup that is, under the hypotheses of its statement, the theorem
`ldLkpAsm2M_subN` (stated in Cb/Ld/LdLkpAsm2GoodM.lean); it is brought to X.link in
Cb/Req1/LdSegRefAsmZk.lean, not here. This file does not say that places with these laws exist.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefDig
import Cb.Ld.LdLkpAsm2Pull
import Cb.Ld.LdLkpMult
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp

/-- The assembled lookup on the digits: the data. -/
structure LdDgA (E Kc : Type) [Field E] [Fintype E] (E₀ : ExtSpec) (Wp : Type) : Type 1 where
  Q   : LdDgP E Kc E₀ Wp
  ι   : Q.Nn → Q.T.Ent
  w   : ℕ
  n   : ℕ
  bAt : ℕ → ℕ → Q.T.Ent
  wS  : PIdx (([] : List (PFmt E)) ++ [pDummy E 1]) → Q.T.Ent
  cS  : Bool → Q.T.Ent
  wAt : ℕ → PIdx (([] : List (PFmt E)) ++ [pDummy E 3]) → Q.T.Ent
  cAt : ℕ → Bool → Q.T.Ent
  wK  : (l : ℕ) → PIdx (List.replicate (0 + l) (pfCube E 2) ++ [pDummy E 2]) → Q.T.Ent
  cK  : ℕ → Bool → Q.T.Ent
  wT  : (l : ℕ) → PIdx (List.replicate (w + l) (pfCube E 2) ++ [pDummy E 2]) → Q.T.Ent
  cT  : ℕ → Bool → Q.T.Ent
  wE  : PIdx (List.replicate (w + (1 + Q.d)) (pfCube E 2)) → Q.T.Ent
  wB  : PIdx (List.replicate (w + (1 + Q.d)) (pfCube E 2) ++ [pDummy E 2]) → Q.T.Ent
  cB  : Q.T.Ent

namespace LdDgA
variable {E Kc : Type} [Field E] [Fintype E] {E₀ : ExtSpec} {Wp : Type} (X : LdDgA E Kc E₀ Wp)

/-- the keys of one kind, as functions of the entries -/
def keyF (μ : X.Q.T.Ent → E) (f : ℕ) : ℕ → E :=
  rngKeys X.Q.D.p X.Q.e (if f = 0 then fun r u => μ (X.Q.lo r u) else fun r u => μ (X.Q.hi r u))
/-- the table of one kind -/
def tabF (f : ℕ) : ℕ → E := tabMod (if f = 0 then X.Q.D.p.q else X.Q.D.p.H)

/-- The data of the assembled lookup. -/
def A : LkAsm2 E where
  St := X.Q.X₄ × E
  J := X.Q.T.Ent
  v' := X.Q.v
  d := 1 + X.Q.d
  w := X.w
  n := X.n
  key := fun x μ => shKey X.Q.v (X.keyF μ) X.Q.tag x.2
  tab := fun x => shTab X.Q.d X.tabF X.Q.tag x.2
  bAt := X.bAt
  wS := X.wS
  cS := X.cS
  wAt := X.wAt
  cAt := X.cAt
  wK := X.wK
  cK := X.cK
  wT := X.wT
  cT := X.cT
  wE := X.wE
  wB := X.wB
  cB := X.cB

/-- The lookup's exact clause: the bits write a valid vector of multiplicities. -/
def mult : X.Q.X₄ × E → Ms X.Q.T E₀ → Prop := fun x ym => X.A.ValidMu x (X.Q.T.ents ym.2)

/-- the entries that rows and mask form read -/
def ent : Ms X.Q.T E₀ → X.Q.Nn → E := fun ym => X.A.entN X.ι (X.Q.T.ents ym.2)

/-- The lookup, as a link and as a chain of one link. -/
def link : IOR.Link Kc (X.Q.lkS X.mult).J (X.Q.lkT X.ent X.A.nRows).J :=
  X.Q.ofSub X.mult X.ent X.A.nRows (X.A.subN X.ι X.Q.T E₀ Kc Wp X.Q.T.ents)
def lk : IOR.Chain Kc (X.Q.lkS X.mult).J (X.Q.lkT X.ent X.A.nRows).J := .one X.link

/-- The law of the bits' places. -/
def Bits : Prop :=
  ∀ m : X.Q.T.Msg, X.Q.vv m = X.Q.D.mkV (X.Q.dg m) →
    ∀ Y < 2 ^ (1 + X.Q.d), ∀ j < 2 ^ X.w, X.Q.T.ents m (X.bAt Y j) =
      shBit X.Q.d (fun f => hbit X.Q.v (X.n + 1) (X.keyF (X.Q.T.ents m) f) (X.tabF f)) Y j

end LdDgA

namespace Spec
open IOR

/-- States, if W ≤ 2 ^ w: "Valid" reads the bits in range only. -/
def ldLkpMult_congr : Prop :=
  ∀ (E : Type) [Field E] (n T w W : ℕ) (key t : ℕ → E) (M M' : ℕ → ℕ → E), W ≤ 2 ^ w →
    (∀ u < 2 ^ T, ∀ j < 2 ^ w, M' u j = M u j) → Valid n T w W key t M → Valid n T w W key t M'

/-- The lookup claim is that of the assembled lookup, read on all entries. -/
def ldSegRef_asm_L : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (X : LdDgA E Kc E₀ Wp),
    X.Q.L = ⟨X.A.v' + 1, X.A.d, fun st ym => X.A.key st (X.Q.T.ents ym.2), X.A.tab, fun _ _ => True⟩

/-- States, under the hypotheses below: for digits in their tables, what the honest prover derives
from the digits meets the lookup's exact clause at every shift. -/
def ldSegRef_asm_mult : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (X : LdDgA E Kc E₀ Wp),
    X.Q.D.p.OK → X.Q.D.p.q ≤ 2 ^ X.Q.d → X.Q.D.p.H ≤ 2 ^ X.Q.d → X.Q.K ≤ 2 ^ X.Q.v →
    2 ^ X.Q.v < 2 ^ (X.n + 1) → X.n + 1 ≤ 2 ^ X.w → X.Bits → X.Q.Mult X.mult

/-- States, under the hypotheses below: the link has all of the bundle but zero knowledge. -/
def ldSegRef_asm_allB : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (pp : ℕ)
      [CharP E pp] (X : LdDgA E Kc E₀ Wp),
    Function.Injective X.ι → X.A.PlacesIn (fun j => j ∈ Set.range X.ι) →
    X.A.H.lkb.Adm pp → X.lk.AllB

/-- All that the four moves ask, from numbers and places. (not all hypotheses are named here: see
the statement below) -/
def ldSegRef_asm_hyp : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (pp : ℕ)
      [CharP E pp] (X : LdDgA E Kc E₀ Wp),
    X.Q.D.p.OK → X.Q.Places → X.Q.D.p.q ≤ 2 ^ X.Q.d → X.Q.D.p.H ≤ 2 ^ X.Q.d → X.Q.K ≤ 2 ^ X.Q.v →
    X.Q.tag 0 ≠ X.Q.tag 1 → Function.Injective X.ι → X.A.PlacesIn (fun j => j ∈ Set.range X.ι) →
    X.A.H.lkb.Adm pp → X.Bits → (X.Q.prog X.mult X.ent X.A.nRows X.lk).Hyp

end Spec
end Cb
