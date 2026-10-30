-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdAltB.lean: how the last part of a proximity test on a batch of instances, its closing, is
composed when fronts and whole tests alternate in it: rules for knowledge soundness, and for the
honest prover's side.

Definitions and statements; the proofs are in Cb/Ld/LdAltBProofs.lean. Generic: no protocol. The
analogue for batches of Cb/Ld/LdLinCloseAlt.lean.
A closing (`LdTc`, Cb/Ld/LdLinCloseChain.lean) is a chain of links (`IOR.Link`,
Ior/KnowCollRulesChain.lean) from a statement over a signature down to the trivial statement. A
front (`Front`, Cb/Ld/LdFront.lean) is a list of steps without rounds, batchings and splittings over
one signature. A whole test (`LdRunD`, Cb/Ld/LdLinCloseRuns.lean) is one test on a group of oracle
messages, as one link.
The honest side: the honest prover of a protocol or reduction, as data: its coins, its strategy, and
the sets of verifier randomness that its analysis names.
The file uses:
  Cb/Ld/LdLinCloseAlt.lean (`LdTc.front x Q p`: a front in front of a closing; its `Q.OkBehind c₀`
    is the predicate for one instance of which `OkBehindV` here is the analogue);
  Cb/Ld/LdBatchBlocksPlan.lean (`LdTcA`: a plan for a batch: a closing, a chain of annotated links,
    the proof that its links are the closing's; `consLo`, `consSh`; `KB`);
  Cb/Ld/LdLinCloseVPlan.lean (`LdTcV`: its honest side; `QV.OK`: every link is a piece; the
    annotations are coherent; the last demand holds of the empty family);
  Cb/Ld/LdLinBHonTop.lean (`c.OkFromV c₀`: a chain that stands behind another, for sets of slots).

In standard terms: a batch has N slots, each with a statement or empty. A key (`JKey`,
Cb/Ld/LdLinChainB.lean) is a function of the statement at a joint. A link is `KB` from one key to
the next (same file) if it is knowledge sound (`KnowB`, Ior/BatchSeq.lean) for the vectors whose
statements all have one value of the key, and on every transcript of the batch takes such a vector
to one whose statements all have one value of the next key. A chain is `KB N kx ky` if its links are
so, along some keys between.

Why: the two files on plans for a batch (Cb/Ld/LdBatchBlocksPlan.lean, Cb/Ld/LdLinCloseVPlan.lean)
know whole tests only, each a piece by itself. A splitting is a masked link: no piece. So a plan
with a front needs (1) a place for the front's annotated links and their honest side, (2) "in order
behind a chain" in place of "every link is a piece".
The front's links for a batch are parameters here: any chain cF of annotated links whose links are
the front's (`cF.forget = LdTc.frontC p`), any chain cV with honest sides over cF. (Which link is
run in every slot and which by the shared part: Cb/Ld/LdSplitV.lean has the splitting both ways.)

Main names:
  `LdTcA.front x QA p cF hF`: the plan for a batch "the front, then QA". `LdTcV.front .. cV hV QV`:
    the honest side of "the front, then QA".
  `Spec.ldAltB_front`: the links of cF are the front's (`hF`); cF is knowledge sound for the vectors
    with one key, from kx to ky, and QA from ky ⇒ the plan from kx.
  `QV.OkBehindV c₀`: the honest side of a plan is in order behind c₀: each link is a piece, or a
    masked link whose masks are fresh, for sets of slots, after c₀ and the plan's earlier links; the
    annotations are coherent; the last demand holds of the empty family.
  `Spec.chainV_append_assoc`: `append` of chains is associative. `Spec.chainV_okFrom_append`: see
    its doc comment.
  `Spec.ldAltV_of_ok`: `QV.OK` gives `QV.OkBehindV c₀` for every c₀.
  `Spec.ldAltV_consLo`, `Spec.ldAltV_consSh`: a whole test in front (in every slot; once, by the
    shared part): the test's link (`D.loV ..`; `D.shV ..`) is a piece (`LinkV.PV`,
    Cb/Ld/LdLinChainV.lean), QV in order behind (c₀, then the test) ⇒ in order behind c₀.
  `Spec.ldAltV_front`: a front in front: the links of cF are the front's (`hF`), cV is a chain with
    honest sides over cF (`hV`); cV stands behind c₀; cF's annotations are coherent; QV in order
    behind (c₀, then cV) ⇒ in order behind c₀.
  `Spec.ldAltV_cZ`: the closing of the test for linear constraints (the step without rounds in every
    slot, then the plan): the step is a piece, QV in order behind (c₀, then the step) ⇒ the three
    conditions that the test for linear constraints asks of its closing on the honest side of a
    batch (`ldLinT_all`, Cb/Ld/LdLinBHonTop.lean).

Limits: no front's links are given. This file does not say that a mask is fresh for sets of slots.
The order of a closing in a batch is our reading (the head of Cb/Ld/LdLinCloseAlt.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinCloseAlt
import Cb.Ld.LdLinCloseVPlan
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
namespace Spec
open IOR

def chainV_append_assoc : Prop :=
  ∀ (K : Type) (N : ℕ) (A B C D : Joint K) (VA : JV N A) (VB : JV N B) (VC : JV N C) (VD : JV N D)
      (c₁ : ChainV K N VA VB) (c₂ : ChainV K N VB VC) (c₃ : ChainV K N VC VD),
    (c₁.append c₂).append c₃ = c₁.append (c₂.append c₃)

/-- States: (c, then c') stands behind c₀ if and only if c does and c' stands behind
(c₀, then c). -/
def chainV_okFrom_append : Prop :=
  ∀ (K : Type) (N : ℕ) (Z A B C : Joint K) (VZ : JV N Z) (VA : JV N A) (VB : JV N B) (VC : JV N C)
      (c₀ : ChainV K N VZ VA) (c : ChainV K N VA VB) (c' : ChainV K N VB VC),
    (c.append c').OkFromV c₀ ↔ c.OkFromV c₀ ∧ c'.OkFromV (c₀.append c)

end Spec
end Iop

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {E : Type} [Field E] [Fintype E] {S : Sig E} {E₀ : ExtSpec} {Wp : Type}

/-- A front in front of a plan for a batch. -/
def LdTcA.front (x : FSt S E₀ Wp Unit) (QA : LdTcA S E₀ Wp)
    (p : Front x ⟨QA.Q.St, QA.Q.base⟩) (cF : ChainA Unit x.stage.J (S.jointCf QA.Q.base))
    (hF : cF.forget = LdTc.frontC p) : LdTcA S E₀ Wp where
  Q := LdTc.front x QA.Q p
  cA := cF.append QA.cA
  same := (chainA_forget_append Unit _ _ _ cF QA.cA).trans
    (congrArg₂ (fun c c' => Chain.append c c') hF QA.same)

variable {N : ℕ}

omit [Fintype E] in
/-- The honest side of a plan is in order behind c₀. -/
def LdTcV.OkBehindV {QA : LdTcA S E₀ Wp} {V : JV N (S.jointCf QA.Q.base)} (QV : LdTcV N QA V)
    {Z : Joint Unit} {VZ : JV N Z} (c₀ : ChainV Unit N VZ V) : Prop :=
  QV.cV.OkFromV c₀ ∧ QA.cA.Coh ∧ ∀ J, QV.VT.q J fun _ => ∅

/-- The honest side of "the front, then QA". -/
def LdTcV.front (x : FSt S E₀ Wp Unit) (QA : LdTcA S E₀ Wp)
    (p : Front x ⟨QA.Q.St, QA.Q.base⟩) (cF : ChainA Unit x.stage.J (S.jointCf QA.Q.base))
    (hF : cF.forget = LdTc.frontC p) (Vx : JV N x.stage.J) (Vy : JV N (S.jointCf QA.Q.base))
    (cV : ChainV Unit N Vx Vy) (hV : cV.forget = cF) (QV : LdTcV N QA Vy) :
    LdTcV N (LdTcA.front x QA p cF hF) Vx where
  VT := QV.VT
  cV := cV.append QV.cV
  same := (chainV_forget_append Unit N _ _ _ _ _ _ cV QV.cV).trans
    (congrArg₂ (fun c c' => ChainA.append c c') hV QV.same)

end

namespace Spec

/-- A front, then a plan. States that it is `KB` from kx, if the links of cF are the front's (`hF`),
`cF.KB N kx ky` and `QA.KB N ky`. -/
def ldAltB_front : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (x : FSt S E₀ Wp Unit)
      (QA : LdTcA S E₀ Wp) (p : Front x ⟨QA.Q.St, QA.Q.base⟩)
      (cF : ChainA Unit x.stage.J (S.jointCf QA.Q.base)) (hF : cF.forget = LdTc.frontC p) (N : ℕ)
      (kx : JKey x.stage.J) (ky : JKey (S.jointCf QA.Q.base)),
    cF.KB N kx ky → QA.KB N ky → (LdTcA.front x QA p cF hF).KB N kx

def ldAltV_of_ok : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (N : ℕ)
      (QA : LdTcA S E₀ Wp) (V : JV N (S.jointCf QA.Q.base)) (QV : LdTcV N QA V)
      (Z : Joint Unit) (VZ : JV N Z) (c₀ : ChainV Unit N VZ V),
    QV.OK → QV.OkBehindV c₀

/-- A whole test in every slot, in front. -/
def ldAltV_consLo : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (N : ℕ) (D : LdRunD S)
      (QA : LdTcA (S.sub D.kp) E₀ Wp) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp)
      (VA : JV N (S.jointCf (D.pre QA.Q.base)))
      (tieB : VA.W0 → QA.Q.St × (S.sub D.kp).Smp → (E₀.prod (S.sub D.kp).ext).Str →
        (S.sub D.kp).Wit × Wp → Prop)
      (qB : QFam (E₀.prod (S.sub D.kp).ext) N) (QV : LdTcV N QA ⟨VA.W0, tieB, qB⟩) (Z : Joint Unit)
      (VZ : JV N Z) (c₀ : ChainV Unit N VZ VA),
    (D.loV QA.Q.base d d' N VA tieB qB).PV →
    QV.OkBehindV (c₀.snoc (D.loV QA.Q.base d d' N VA tieB qB)) →
    (LdTcV.consLo D QA d d' VA tieB qB QV).OkBehindV c₀

/-- A whole test once, by the shared part, in front. -/
def ldAltV_consSh : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (N : ℕ) (D : LdRunD S)
      (QA : LdTcA (S.sub D.kp) E₀ Wp) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp)
      (VA : JV N (S.jointCf (D.pre QA.Q.base))) (W0' : Type)
      (tieB : W0' → QA.Q.St × (S.sub D.kp).Smp → (E₀.prod (S.sub D.kp).ext).Str →
        (S.sub D.kp).Wit × Wp → Prop)
      (qB : QFam (E₀.prod (S.sub D.kp).ext) N)
      (rep : VA.W0 → ((((D.B → E) × (∀ b, D.Sb b)) × QA.Q.St) × S.Smp) × (S.Wit × Wp))
      (nx : VA.W0 → W0') (QV : LdTcV N QA ⟨W0', tieB, qB⟩) (Z : Joint Unit)
      (VZ : JV N Z) (c₀ : ChainV Unit N VZ VA),
    (D.shV QA.Q.base d d' N VA W0' tieB qB rep nx).PV →
    QV.OkBehindV (c₀.snoc (D.shV QA.Q.base d d' N VA W0' tieB qB rep nx)) →
    (LdTcV.consSh D QA d d' VA W0' tieB qB rep nx QV).OkBehindV c₀

/-- A front in front. -/
def ldAltV_front : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (N : ℕ)
      (x : FSt S E₀ Wp Unit) (QA : LdTcA S E₀ Wp) (p : Front x ⟨QA.Q.St, QA.Q.base⟩)
      (cF : ChainA Unit x.stage.J (S.jointCf QA.Q.base))
      (hF : cF.forget = LdTc.frontC p) (Vx : JV N x.stage.J)
      (Vy : JV N (S.jointCf QA.Q.base)) (cV : ChainV Unit N Vx Vy) (hV : cV.forget = cF)
      (QV : LdTcV N QA Vy) (Z : Joint Unit) (VZ : JV N Z) (c₀ : ChainV Unit N VZ Vx),
    cV.OkFromV c₀ → cF.Coh → QV.OkBehindV (c₀.append cV) →
    (LdTcV.front x QA p cF hF Vx Vy cV hV QV).OkBehindV c₀

/-- The closing of the test for linear constraints. States, under the hypotheses below, the three
conditions on the honest side of a batch. -/
def ldAltV_cZ : Prop :=
  ∀ (E ι κ J Y : Type) [Field E] [Fintype ι] [Fintype κ] [Fintype J] [Fintype Y]
      (C : LdLinC E ι κ J Y) (N : ℕ) (QA : LdTcA C.S C.E₀ C.Wpa) (fq : C.St6 → QA.Q.St)
      (VA : JV N C.j6J)
      (tieB : VA.W0 → QA.Q.St × C.S.Smp → (C.E₀.prod C.S.ext).Str → C.S.Wit × C.Wpa → Prop)
      (qB : QFam (C.E₀.prod C.S.ext) N) (QV : LdTcV N QA ⟨VA.W0, tieB, qB⟩) (Z : Joint Unit)
      (VZ : JV N Z) (c₀ : ChainV Unit N VZ VA),
    ((C.link fq QA.Q.base).loV N VA tieB qB).PV →
    QV.OkBehindV (c₀.snoc ((C.link fq QA.Q.base).loV N VA tieB qB)) →
    (C.cZV QA fq VA tieB qB QV).OkFromV c₀ ∧
    (C.cZV QA fq VA tieB qB QV).forget.Coh ∧
    ∀ Jn, QV.VT.q Jn fun _ => ∅

end Spec
end Cb
