-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectCtbPre.lean: bookkeeping for the compiler to a random-oracle argument, for which it
is asked that the types of positions, symbols and plain messages of every round are countable: here
for the reduction that tests that a word encodes an index.

Definitions, theorems. Bookkeeping for the passage to one random oracle, as Cb/Obj/LdObjectCtb.lean,
which says what `CtbSh` (CompileK/ImplCountable.lean) is.

Main names:
  `ctb_drawR`, `ctb_rounds`, `ctb_coreP`, `ctb_pscP`: the links of a chain at the base (`Cb.BkA`,
    Cb/Ld/LdLkpTreeP.lean): the verifier draws a value; the rounds of the variables; the sumcheck
    for a polynomial summand without and with its last round. Asked: the field is finite (it is, by
    type: the instance argument `[Fintype E]`; `ctb_drawR` has no field); of `ctb_rounds`, that the
    shape that follows is countable; of `ctb_drawR`, that the values to draw are finitely many and
    that there is one (`[Fintype D]` `[Nonempty D]`); beside these, the instance fields of the
    records among the arguments (`PscPar E`: `finJ`, `finA`, `finB`; `PFmt E`: `finS`, `finCh`,
    `neCh`; `Round`, of the shape that follows in `ctb_rounds`: `finChal`, `neChal`).
  `ctbA_chainA`: the assembled lookup (`LkAsm2`, Cb/Ld/LdLkpAsm2.lean): no hypothesis beside the
    instance arguments `[Field E]` `[Fintype E]` and the instance field `finJ : Fintype J` of
    `A : LkAsm2 E`.
  `ctb_subN`, `ctb_subIN`: lifted over oracle messages; with an encoded index.
  `ldWfCtb`: the term `B.wf` of weights-formedness, for any blocks. Asked: the symbols of the family
    sent are countable (`Sig.CtbSy`), and each lookup's shape is.
  `ldWfCtb_lks`: with the lookups as values (`K.sub`, Cb/Ld/LdWfBlocks.lean). Asked: `Sig.CtbSy`
    alone.

Limits: on a protocol this file has one kind of conclusion, countability (as in `ctbA_chainA`,
`ldWfCtb`, `ldWfCtb_lks`); beyond it no statement of the file concludes anything of a protocol.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectCtb
import Cb.Ld.LdWfBlocks
import Cb.Ld.LdLkpAsm2Pull

set_option autoImplicit false

namespace Iop.IOR

theorem Chain.ctb_fam {K : Type} (J : ℕ → Joint K)
    (b : ∀ l, Link K (J l) (J (l + 1))) (h : ∀ l, (b l).Ctb) : ∀ n, (Chain.fam J b n).Ctb
  | 0 => (Chain.ctb_one _).2 (h 0)
  | n + 1 => (Chain.ctb_snoc _ _).2 ⟨Chain.ctb_fam J b h n, h (n + 1)⟩

end Iop.IOR

namespace Cb
open Iop Prob Hiop IOR Cb.LdLkp

theorem ctb_drawR {X X' : Type} (D : Type) [Fintype D] [Nonempty D]
    (nx : X → D → X') (Ex : ExtSpec) :
    CtbSh (IOR.draw D nx Ex).shape :=
  ⟨⟨inferInstanceAs (Countable Empty), fun p => p.elim, inferInstanceAs (Countable Unit)⟩, trivial⟩

section Psc
variable {E : Type} [Field E] [Fintype E]

theorem ctb_rounds : ∀ (l : List (PFmt E)) {t : Shape}, CtbSh t → CtbSh (pRounds l ++ t)
  | [], _, h => h
  | f :: l, _, h =>
    ⟨⟨inferInstanceAs (Countable Empty),
        fun p => p.elim,
        inferInstanceAs (Countable (Fin (f.n + 1) → E))⟩,
      ctb_rounds l h⟩

theorem ctb_coreP (Y : PscPar E) (Ex : ExtSpec) : CtbSh (Y.core Ex).shape := by
  have h := ctb_rounds Y.fmt (t := []) trivial
  rw [List.append_nil] at h
  exact ⟨⟨inferInstanceAs (Countable Empty), fun p => p.elim, inferInstanceAs (Countable E)⟩, h⟩

theorem ctb_pscP (Y : PscPar E) (Ex : ExtSpec) : CtbSh (Y.psc Ex).shape :=
  ctbSh_append (ctb_coreP Y Ex)
    ⟨⟨inferInstanceAs (Countable Empty), fun p => p.elim, inferInstanceAs (Countable (Y.A → E))⟩,
      trivial⟩

end Psc

/-- positions, symbols and plain parts of a block at the base are countable -/
def BkA.Ctb {K M X₁ X₂ : Type} {Ex : ExtSpec} {Wp : Type} (b : BkA K M X₁ X₂ Ex Wp) : Prop :=
  CtbSh b.R.shape

section Rules
variable {K M X₁ X₂ X₃ : Type} {Ex : ExtSpec} {Wp : Type}

theorem ctbA_seq {a : BkA K M X₁ X₂ Ex Wp} {b : BkA K M X₂ X₃ Ex Wp} (ha : a.Ctb) (hb : b.Ctb) :
    (a.seq b).Ctb :=
  ctbSh_append ha hb

theorem ctbA_chain (X : ℕ → Type) (b : ∀ l, BkA K M (X l) (X (l + 1)) Ex Wp) (h : ∀ l, (b l).Ctb) :
    ∀ n, (BkA.chain X b n).Ctb
  | 0 => h 0
  | n + 1 => ctbA_seq (ctbA_chain X b h n) (h (n + 1))

theorem ctbA_preM {b : BkA K M X₂ X₃ Ex Wp} (h : b.Ctb) (φ : X₁ → X₂) : (b.preM φ).Ctb := h
theorem ctbA_postM {b : BkA K M X₁ X₂ Ex Wp} (h : b.Ctb) (φ : X₂ → X₃) : (b.postM φ).Ctb := h

end Rules

section Lkp
variable {E : Type} [Field E] [Fintype E] (Ex : ExtSpec) (M Wp Kc : Type)

theorem ctbA_tie (D : TieP E) (msg : M → D.J → E) (n : ℕ) : (D.tieA Ex Wp Kc msg n).Ctb :=
  ctbA_chain (fun l => E × (D.lv l).T.St)
    (D.stepA Ex Wp Kc msg) (fun l => ctb_pscP (D.lv l).T.par Ex) n

theorem ctbA_lev (D : TreeP E) (msg : M → D.J → E) (l : ℕ) : (D.levA Ex Wp Kc msg l).Ctb :=
  ctbSh_append (ctb_pscP (D.lv l).T.par Ex) (ctb_drawR _ _ Ex)

theorem ctbA_tree (D : TreeP E) (msg : M → D.J → E) (n : ℕ) : (D.treeA Ex Wp Kc msg n).Ctb :=
  ctbA_chain (fun l => E × (D.lv l).T.St) (D.levA Ex Wp Kc msg) (ctbA_lev Ex M Wp Kc D msg) n

theorem ctbA_head (H : LkHead E) (msg : M → H.J → E) : (H.headA Ex M Wp Kc msg).Ctb :=
  ctbSh_append (ctb_drawR _ _ Ex) (ctbA_tie Ex M Wp Kc H.tie msg H.n)

theorem ctbA_segK (I : LkInst E) (v' : ℕ) (tK : I.X → E) (msg : M → I.J → E) :
    (segK I v' tK Ex M Wp Kc msg).Ctb :=
  ctbA_tree Ex M Wp Kc (I.setV (v' + 1)).DK msg v'

theorem ctbA_forest (Q : SegTab E) (msg : M → Q.I.J → E) : ∀ l, (Q.forest Ex Wp Kc msg l).Ctb
  | 0 => ctb_drawR _ _ Ex
  | l + 1 => ctbA_seq (ctbA_forest Q msg l) (ctbA_lev Ex M Wp Kc Q.D msg l)

theorem ctbA_segT (Q : SegTab E) (msg : M → Q.I.J → E) : (Q.segT Ex Wp Kc msg).Ctb :=
  ctbA_seq (ctbA_seq (ctbA_forest Ex M Wp Kc Q msg Q.I.d) (ctb_pscP Q.En.psc.par Ex))
    (ctbSh_append (ctb_drawR _ _ Ex) (ctb_pscP Q.Bt.zc.next.par Ex))

theorem ctbA_forest2 (A : LkAsm2 E) (msg : M → A.J → E) : ∀ l, (A.forest Ex M Wp Kc msg l).Ctb
  | 0 => ctbA_segK Ex M Wp Kc A.IK A.v' (fun x => A.tK (A.oR x)) msg
  | l + 1 => ctbA_seq (ctbA_forest2 A msg l) (ctbA_lev Ex M Wp Kc A.D msg l)

/-- The assembled lookup. -/
theorem ctbA_chainA (A : LkAsm2 E) (msg : M → A.J → E) : (A.chainA Ex M Wp Kc msg).Ctb :=
  ctbA_seq (ctbA_seq
      (ctbA_seq (ctbA_seq (ctbA_head Ex M Wp Kc A.H msg) (ctb_drawR _ _ Ex))
        (ctbA_forest2 Ex M Wp Kc A msg A.d))
      (ctb_coreP A.En.par Ex))
    (ctbSh_append (ctb_drawR _ _ Ex) (ctb_pscP A.Bt.zc.next.par Ex))

theorem ctbA_baseA (A : LkAsm2 E) (msg : M → A.J → E) : (A.baseA Ex M Wp Kc msg).Ctb :=
  ctbA_chainA Ex M Wp Kc A msg
theorem ctbA_baseN (A : LkAsm2 E) {N : Type} (ι : N → A.J) (msg : M → A.J → E) :
    (A.baseN ι Ex M Wp Kc msg).Ctb :=
  ctbA_chainA Ex M Wp Kc A msg

end Lkp

section Lift
variable {E : Type} [Field E] [Fintype E]

theorem ctb_subN (A : LkAsm2 E) {N : Type} (ι : N → A.J) (S : Sig E) (E₀ : ExtSpec)
    (Kc Wp : Type) (msg : S.Msg → A.J → E) :
    CtbSh (A.subN ι S E₀ Kc Wp msg).R.shape :=
  ctbA_chainA E₀ S.Msg Wp Kc A msg

theorem ctb_subIN (A : LkAsm2 E) {N : Type} (ι : N → A.J) (C : ConfigurationWithOutOfDomainSample)
    (S : Sig E) (msg : C.Msg × S.Msg → A.J → E) :
    CtbSh (A.subIN ι C S msg).R.shape :=
  ctbA_chainA C.E0 (C.Msg × S.Msg) Unit Unit A msg

theorem ctb_batt (B : BattPar E) (Ex : ExtSpec) : CtbSh (B.batt Ex).shape :=
  ctbSh_append (ctb_drawR _ _ Ex) (ctb_coreP B.par Ex)

variable {C : ConfigurationWithOutOfDomainSample} {P : LdWfP E C}

/-- Weights-formedness' term, for any blocks. -/
theorem ldWfCtb (B : P.Blk) (hS : P.S.CtbSy) (hL : ∀ l, CtbSh (B.sub l).R.shape) :
    CtbSh B.wf.shape := by
  show (B.chain.link B.p0).Ctb
  refine chainCtb_link _ _ ?_
  unfold LdWfP.Blk.chain LdWfP.Blk.cLkp
  exact (Chain.ctb_snoc _ _).2
    ⟨chainCtb_append _ _ ((Chain.ctb_one _).2 (ctb_sendFam P.S P.Sd P.WSt C.E0 hS))
        (Chain.ctb_fam P.J B.lLkp hL P.n),
      ctb_batt P.bt C.E0⟩

/-- the lookups as values -/
theorem ldWfCtb_sub (K : P.Lks) (l : ℕ) : CtbSh (K.sub l).R.shape :=
  ctb_subIN (K.asm l) Sum.inr C P.S P.msg

/-- Weights-formedness' term, the lookups being the assembled ones. -/
theorem ldWfCtb_lks (B : P.Blk) (K : P.Lks) (hB : B.sub = K.sub) (hS : P.S.CtbSy) :
    CtbSh B.wf.shape :=
  ldWfCtb B hS fun l => by rw [hB]; exact ldWfCtb_sub K l

end Lift
end Cb
