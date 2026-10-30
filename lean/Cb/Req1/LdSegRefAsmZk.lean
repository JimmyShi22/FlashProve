-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefAsmZk.lean: under the hypotheses of its statements, the digits' lookup of the
reference segment is one masked block: what zero knowledge asks of its four moves, beside their
hypotheses, falls to places and to one fact on fresh masks.

Definitions, statements and proofs.

Why: Cb/Req1/LdSegRefAsm.lean takes the assembled lookup for the digits' lookup and states, under
its hypotheses, all of the bundle but zero knowledge (proved in Cb/Req1/LdSegRefAsmProofs.lean).
Under the hypotheses of `Spec.mj_chain` (Cb/Ld/LdLkpMaskChain.lean), a lookup that sends no oracle
has masked messages as a whole; for the assembled lookup that is, under the hypotheses of its
statement, the theorem `ldLkpAsm2M_subN` (stated in Cb/Ld/LdLkpAsm2GoodM.lean). Here it is brought
to the link `X.link` between the two stages of Cb/Req1/LdSegRefDig.lean.
The letters of the item: `MaskData` (Ior/Masked.lean). `MaskData R Wi` is a structure: a type `Kc`
with `kc : Wi → Kc`; a type `Xp` with `pub : Xi → Xp`; a finite, non-empty type `Mk` with
`put : Mk → Kc → Kc`; a predicate `Cl` on `Xp` and `Kc`; `msg`, from `Kc`, `Xp` and the verifier's
randomness ρ to plain parts; and `sim`, from `Xp` and ρ to distributions on plain parts. The item
"masked messages": `Honest.MM`; a masked block: `GoodM` (Ior/Masked.lean). `LdProg.Zk`,
`LdProg.After`: Cb/Req1/LdReq.lean.

Main names:
  `X.Dt`: "the data" of the lookup: the places of the digits and of the bits of the multiplicities.
  `X.dm Rd`: the letters of the item "masked messages": of a witness are read the entries in Rd of
    all messages, and nothing else; own masks: those of all sumchecks of the lookup.
  `Spec.ldSegRef_asm_reads`: the lookup's exact claim (keys in the table; the bits write a valid
    vector) reads the data only. No hypothesis beside whatever the arguments hold as proofs.
  `Spec.ldSegRef_asm_goodM`: X.link is a masked block with the letters X.dm Rd, from: ι injective,
    its range holds all named places; the conditions on numbers; the own masks of all sumchecks lie
    at pairwise different places outside the data (A.MaskOK X.Dt; not all hypotheses are named here:
    see `LkAsm2.MaskOK`, Cb/Ld/LdLkpMaskAsm2.lean); Rd holds data and own masks; the further oracles
    have a value; and whatever the arguments hold as proofs. The conditions on numbers are `Adm pp`,
    pp the characteristic of E.
  `Spec.ldSegRef_asm_zk`: (step; shift; step; lookup).Zk base from these, two different tags, and:
    the fact (X.dm Rd).fact is fresh before the lookup.

Limits: this file does not say that the fact is fresh: it is carried there from the sending of the
masks (Cb/Req1/LdSegRefCarry.lean carries the wide fact through the moves before the lookup;
Cb/Req1/LdSegCarry.lean: the fact at a masked link follows from the wide one), each under the
hypotheses of its statements.
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegRefAsmProofs
import Cb.Ld.LdLkpAsm2GoodMProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp IOR IOR.Chain

namespace LdDgA
variable {E Kc : Type} [Field E] [Fintype E] {E₀ : ExtSpec} {Wp : Type} (X : LdDgA E Kc E₀ Wp)

/-- The data of the lookup: the places of the digits and of the bits. -/
def Dt (j : X.Q.T.Ent) : Prop :=
  (∃ r u, X.Q.lo r u = j) ∨ (∃ r u, X.Q.hi r u = j) ∨ ∃ Y i, X.bAt Y i = j

/-- The letters of the item "masked messages". -/
def dm (Rd : X.Q.T.Ent → Prop) : MaskData X.link.R (X.Q.lkS X.mult).J.W :=
  X.A.dmN X.ι X.Q.T (X.A.mjChain E₀ X.Q.T.Msg Wp Kc X.Q.T.ents Rd)
    (X.A.lk.inP X.A.ValidMu) fun w => mjCut Rd (X.Q.T.ents w.1)

end LdDgA

namespace Spec

/-- The lookup's exact claim reads the data only. -/
def ldSegRef_asm_reads : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (X : LdDgA E Kc E₀ Wp),
    X.A.ClaimReads X.Dt X.A.ValidMu

/-- States, under the hypotheses below: the digits' lookup is one masked block. -/
def ldSegRef_asm_goodM : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp]
      (X : LdDgA E Kc E₀ Wp) [Nonempty E₀.Str] (Rd : X.Q.T.Ent → Prop),
    Function.Injective X.ι → X.A.PlacesIn (fun j => j ∈ Set.range X.ι) → X.A.H.lkb.Adm pp →
    X.A.MaskOK X.Dt → (∀ j, X.A.srAll X.Dt j → Rd j) → X.link.GoodM (X.dm Rd)

/-- What zero knowledge asks of the four moves, beside their hypotheses. -/
def ldSegRef_asm_zk : Prop :=
  ∀ (E Kc : Type) (E₀ : ExtSpec) (Wp : Type) [Field E] [Fintype E] (pp : ℕ)
      [CharP E pp] (X : LdDgA E Kc E₀ Wp) [Nonempty E₀.Str]
      (Rd : X.Q.T.Ent → Prop) (base : MaskFact X.Q.D.s4.J.W → Prop),
    X.Q.tag 0 ≠ X.Q.tag 1 → Function.Injective X.ι → X.A.PlacesIn (fun j => j ∈ Set.range X.ι) →
    X.A.H.lkb.Adm pp → X.A.MaskOK X.Dt → (∀ j, X.A.srAll X.Dt j → Rd j) →
    (X.Q.pre X.mult).After base (X.dm Rd).fact → (X.Q.prog X.mult X.ent X.A.nRows X.lk).Zk base

end Spec

theorem ldSegRef_asm_reads : Spec.ldSegRef_asm_reads := by
  intro E Kc E₀ Wp _ _ X st k k' h hk
  have ek : X.keyF k = X.keyF k' := by
    funext f
    unfold LdDgA.keyF
    by_cases hf : f = 0
    · rw [if_pos hf, if_pos hf]
      congr 1
      funext r u
      exact h _ (Or.inl ⟨r, u, rfl⟩)
    · rw [if_neg hf, if_neg hf]
      congr 1
      funext r u
      exact h _ (Or.inr (Or.inl ⟨r, u, rfl⟩))
  have e1 : X.A.key st k = X.A.key st k' := by
    show shKey X.Q.v (X.keyF k) X.Q.tag st.2 = shKey X.Q.v (X.keyF k') X.Q.tag st.2
    rw [ek]
  have e2 : X.A.H.bit k = X.A.H.bit k' :=
    funext fun Y => funext fun i => h _ (Or.inr (Or.inr ⟨Y, i, rfl⟩))
  have hk' : (InTable (X.A.v' + 1) X.A.d (X.A.key st k) (X.A.tab st) ∧ True) ∧
      Valid (X.A.v' + 1) X.A.d X.A.w (X.A.n + 1) (X.A.key st k) (X.A.tab st) (X.A.H.bit k) := hk
  rw [e1, e2] at hk'
  exact hk'

theorem ldSegRef_asm_goodM : Spec.ldSegRef_asm_goodM := by
  intro E Kc E₀ Wp _ _ pp _ X _ Rd hι hP hAdm hM hRd
  have gM := ldLkpAsm2M_subN E pp X.A X.Q.Nn X.ι X.A.ValidMu X.Q.T E₀ Kc Wp X.Q.R1 X.Q.T.ents X.Dt
    Rd hι hP hAdm (ldLkpAsm2_muValid E X.A hAdm.1) hM hRd (ldSegRef_asm_reads E Kc _ _ X)
  exact ⟨(allB_one X.link).1 (ldSegRef_asm_allB E Kc _ _ pp X hι hP hAdm),
    gM.mm,
    fun x y w hw => gM.claim x y w hw⟩

theorem ldSegRef_asm_zk : Spec.ldSegRef_asm_zk := by
  intro E Kc E₀ Wp _ _ pp _ X _ Rd base ht hι hP hAdm hM hRd hf
  exact ldSegRef_dg_zk E Kc _ _ X.Q X.mult X.ent X.A.nRows X.lk base ht
    ((okGiven_one X.link _).2
      (Or.inr ⟨X.dm Rd, ldSegRef_asm_goodM E Kc _ _ pp X Rd hι hP hAdm hM hRd, hf⟩))

end Cb
