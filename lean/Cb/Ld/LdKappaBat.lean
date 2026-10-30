-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdKappaBat.lean: bounds on the errors of round-by-round soundness: "every round's error, as a
probability, is at most κ": the test for linear constraints at N instances, with its closing; the
preamble of weights-formedness.

Definitions and theorems: glue along the rules of composition; nothing is evaluated.
A round's error e is a number (`Err`, Iop/Rbr.lean). It is, as a probability, at most κ if e ≤ κ ·
v, with v the number of values of the round's verifier message (`Err.Below`, Iop/InteractiveOracleProof.lean). A
list, a chain, a plan, a closing or a link is at most κ if every round's error in it is. These
errors are numbers that a link lists (the data fields `LinkA.err`, `Link.P.err`): that a link is
sound at the numbers that it lists is no statement of this file; for the test at N instances with a
closing cZ, under `P.FoldErr on0 εf`, `P.D.py` injective, `S.OK` and `cZ.KB N P.key6 kT`, that tie
is `Spec.ldLinCB_know` (Cb/Ld/LdLinChainB.lean) (that condition itself asks soundness of some of the
parts one level down: for these the tie carries soundness, it does not found it): `IOR.KnowB`
(Ior/BatchSeq.lean) for the vectors of
statements that share the encoded index and its record (`SameKey P.k0`), on the statements with the
condition `(P.j0 on0).on`; for the preamble of weights-formedness, under `LdWfP.Laws` and `B.Hyp`,
`Spec.ldWf` (Cb/Ld/LdWf.lean) (that condition itself asks soundness of some of the parts one level
down: for these the tie carries soundness, it does not found it).

Main names:
  `IOR.ChainA.ErrBelowA`: "at most κ" for a chain of a batch. `LdLinP.KapCB`: the core at N
    instances.
  `ldKappa_nilA`, `ldKappa_consLo`, `ldKappa_consSh`: plans for a batch are at most κ: "nothing is
    left"; and, under `D.Kap κ` (Cb/Ld/LdKappaRun.lean), a test D in every slot, or once by the
    shared part, then a plan that is at most κ. The error for one fixed instance stands, no factor
    N (as in this protocol's technical report (lean/CREDITS.md)).
  `ldKappa_linCA`: `P.KapCB S εf N κ`, a closing at most κ → the test at N instances with that
    closing, as one link, is at most κ.
  `LdWfP.Blk.Kap`: weights-formedness: the sending's number; for each forest l ≤ n: every round of
    the lookup `B.sub l` is at most κ; every round of the batching of tensor rows is at most κ. The
    last two are clauses on the blocks' lists, not on numbers (as in the request's record:
    Cb/Req1/LdSegRefBelow.lean).
  `ldKappa_wf`: `B.Kap κ` → every round of `B.link` is at most κ.
  The statements with `P : LdLinP` take the type ι of positions nonempty.

Limits: this file says nothing on the size of any number.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdKappaRun
import Cb.Ld.LdBatchPlanLin
import Cb.Ld.LdWf

set_option autoImplicit false

namespace Iop
open scoped ENNReal
namespace IOR.ChainA
variable {K : Type}

/-- Every link's list of errors for a batch, as a probability, is at most κ, round by round. A link
of a batch (`LinkA`, Cb/Ld/LdLinChainB.lean) carries a list of its own; for most links it is the
list for one instance. -/
def ErrBelowA : {A B : Joint K} → ChainA K A B → ℝ≥0∞ → Prop
  | _, _, .one a, κ => Err.Below a.err κ
  | _, _, .snoc c a, κ => c.ErrBelowA κ ∧ Err.Below a.err κ

variable {A B C : Joint K}
theorem errBelowA_one (a : LinkA K A B) (κ : ℝ≥0∞) :
    (ChainA.one a).ErrBelowA κ ↔ Err.Below a.err κ := by rw [ErrBelowA]
theorem errBelowA_snoc (c : ChainA K A B) (a : LinkA K B C) (κ : ℝ≥0∞) :
    (c.snoc a).ErrBelowA κ ↔ c.ErrBelowA κ ∧ Err.Below a.err κ := by rw [ErrBelowA]

end IOR.ChainA

open IOR IOR.ChainA

theorem chainA_errBelow {K : Type} {A B : Joint K} (c : ChainA K A B) (d : A.W) (κ : ℝ≥0∞) :
    c.ErrBelowA κ → Err.Below (c.linkA d).err κ := by
  induction c with
  | one a => intro h; rw [linkA_one]; exact (errBelowA_one a κ).1 h
  | snoc c a ih =>
      intro h
      rw [linkA_snoc]
      exact Err.Below.app (ih ((errBelowA_snoc c a κ).1 h).1) ((errBelowA_snoc c a κ).1 h).2

theorem errBelowA_append {K : Type} {A B C : Joint K} (c : ChainA K A B)
    (c' : ChainA K B C) (κ : ℝ≥0∞) :
    (c.append c').ErrBelowA κ ↔ c.ErrBelowA κ ∧ c'.ErrBelowA κ := by
  induction c' with
  | one a => rw [append_one, errBelowA_snoc, errBelowA_one]
  | snoc c' a ih => rw [append_snoc, errBelowA_snoc, errBelowA_snoc, ih, and_assoc]

end Iop

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain IOR.ChainA
open scoped ENNReal

section
variable {E ι κ' J Y : Type}
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ'] [Fintype J] [Fintype Y]

/-- The core of the test for linear constraints at N instances: its numbers. They are the numbers of
`LdLinP.KapC` (Cb/Ld/LdKappaKit.lean) but at the point: `P.errPtB εf N`, in which the term of the
point's polynomial identity occurs N times. -/
structure LdLinP.KapCB (P : LdLinP E ι κ' J Y) (S : P.Snd) (εf N : ℕ) (κ : ℝ≥0∞) : Prop where
  sW   : (ldSendFamErr P.NW P.SdW S.LW : ℝ≥0∞) ≤ κ * (Fintype.card P.SdW.D : ℝ≥0∞)
  pt   : (P.errPtB εf N : ℝ≥0∞) ≤ κ * (Fintype.card P.vPt.D : ℝ≥0∞)
  sU   : (ldSendFamErr P.NU P.SdU S.LU : ℝ≥0∞) ≤ κ * (Fintype.card P.SdU.D : ℝ≥0∞)
  loc  : (P.errLoc : ℝ≥0∞) ≤ κ * (Fintype.card P.vLoc.D : ℝ≥0∞)
  sO   : (ldSendFamErr P.NO P.SdO S.LO : ℝ≥0∞) ≤ κ * (Fintype.card P.SdO.D : ℝ≥0∞)
  zeta : (P.errZeta : ℝ≥0∞) ≤ κ * (Fintype.card P.vZeta.D : ℝ≥0∞)

theorem ldKappa_linA (P : LdLinP E ι κ' J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
    (S : P.Snd) (εf N : ℕ) (κ : ℝ≥0∞) (h : P.KapCB S εf N κ) :
    (P.chainA on0 S εf N).ErrBelowA κ := by
  unfold LdLinP.chainA
  simp only [errBelowA_snoc, errBelowA_one]
  exact ⟨⟨⟨⟨⟨⟨trivial, kap_send _ _ _ _ _ _ _ κ h.sW⟩, ⟨h.pt, trivial⟩⟩,
          kap_send _ _ _ _ _ _ _ κ h.sU⟩,
        ⟨h.loc, trivial⟩⟩,
      kap_send _ _ _ _ _ _ _ κ h.sO⟩,
    ⟨h.zeta, trivial⟩⟩

theorem ldKappa_linCA (P : LdLinP E ι κ' J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
    (S : P.Snd) (εf N : ℕ) (cZ : ChainA Unit P.J6 LdLinP.JT) (d : P.W0) (κ : ℝ≥0∞)
    (h : P.KapCB S εf N κ) (hZ : cZ.ErrBelowA κ) :
    Err.Below (P.linCA on0 S εf N cZ d).err κ := by
  unfold LdLinP.linCA
  exact chainA_errBelow _ _ κ ((errBelowA_append _ _ κ).2 ⟨ldKappa_linA P on0 S εf N κ h, hZ⟩)

omit [Fintype E] [Nonempty ι] in
theorem ldKappa_linZA (C : LdLinC E ι κ' J Y) (QA : LdTcA C.S C.E₀ C.Wpa) (fq : C.St6 → QA.Q.St)
    (κ : ℝ≥0∞) (h : QA.cA.ErrBelowA κ) : (C.cZA QA fq).ErrBelowA κ :=
  (errBelowA_append _ _ κ).2 ⟨(errBelowA_one _ κ).2 trivial, h⟩

end

section
variable {E : Type} [Field E] {S : Sig E} {E₀ : ExtSpec} {Wp : Type}

theorem ldKappa_nilA (w₀ : S.Wit × Wp) (κ : ℝ≥0∞) : (LdTcA.nil S E₀ Wp w₀).cA.ErrBelowA κ :=
  (errBelowA_one _ κ).2 trivial

variable [Fintype E]

theorem ldKappa_consLo (D : LdRunD S) (QA : LdTcA (S.sub D.kp) E₀ Wp) (d : S.Wit × Wp)
    (d' : LdBrW D.G D.kp Wp) (κ : ℝ≥0∞) (h : D.Kap κ) (hQ : QA.cA.ErrBelowA κ) :
    (LdTcA.consLo D QA d d').cA.ErrBelowA κ :=
  (errBelowA_append _ _ κ).2 ⟨(errBelowA_one _ κ).2 (ldKappa_run D QA.Q.base d d' κ h), hQ⟩

theorem ldKappa_consSh (D : LdRunD S) (QA : LdTcA (S.sub D.kp) E₀ Wp) (d : S.Wit × Wp)
    (d' : LdBrW D.G D.kp Wp) (κ : ℝ≥0∞) (h : D.Kap κ) (hQ : QA.cA.ErrBelowA κ) :
    (LdTcA.consSh D QA d d').cA.ErrBelowA κ :=
  (errBelowA_append _ _ κ).2 ⟨(errBelowA_one _ κ).2 (ldKappa_run D QA.Q.base d d' κ h), hQ⟩

end

theorem ldKappa_fam {K : Type} (J : ℕ → Joint K) (b : ∀ l, Link K (J l) (J (l + 1))) (κ : ℝ≥0∞) :
    ∀ n, (∀ l, l ≤ n → Err.Below (b l).P.err κ) → (Chain.fam J b n).ErrBelow κ
  | 0, h => (errBelow_one _ κ).2 (h 0 le_rfl)
  | n + 1, h =>
    (errBelow_snoc _ _ κ).2
      ⟨ldKappa_fam J b κ n fun l hl => h l (Nat.le_succ_of_le hl), h (n + 1) le_rfl⟩

section
variable {E : Type} [Field E] [Fintype E] {C : ConfigurationWithOutOfDomainSample} {P : LdWfP E C}

/-- Weights-formedness: its numbers, and its blocks' lists. -/
structure LdWfP.Blk.Kap (B : P.Blk) (κ : ℝ≥0∞) : Prop where
  send : (ldSendFamErr P.S P.Sd B.L : ℝ≥0∞) ≤ κ * (Fintype.card P.Sd.D : ℝ≥0∞)
  lkp  : ∀ l, l ≤ P.n → Err.Below (B.sub l).P.err κ
  batt : Err.Below (P.bt.nums C.E0 Unit).err κ

theorem ldKappa_wf (B : P.Blk) (κ : ℝ≥0∞) (h : B.Kap κ) : Err.Below B.link.P.err κ := by
  unfold LdWfP.Blk.link
  refine chain_errBelow Unit _ _ _ _ κ ?_
  unfold LdWfP.Blk.chain LdWfP.Blk.cLkp
  refine (errBelow_snoc _ _ κ).2
    ⟨(errBelow_append Unit _ _ _ _ _ κ).2
        ⟨(errBelow_one _ κ).2 ?_, ldKappa_fam P.J B.lLkp κ P.n fun l hl => h.lkp l hl⟩,
      h.batt⟩
  exact kap_send P.S P.Sd P.WSt C.E0 Unit B.L B.t κ h.send

end
end Cb
