-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBatchBlocksPlan.lean: round-by-round knowledge soundness of the last part of a proximity
test with linear claims, when at most N instances are proved together (a batch): rules that compose
it test by test.

Definitions, statements (`Iop.Spec.link_lo_kb`; the others in `Cb.Spec`) and proofs (an assembly).

The test is the test for linear constraints on the encoded index (Cb/Ld/LdLin.lean). The core
(`LdLinP.core`, Cb/Ld/LdLin.lean) is the test without its closing: the chain up to the rows that are
left. The closing is Cb/Ld/LdLinCloseLin.lean's (`C.cZ Q fq`: a step without rounds, then whole
tests on groups in a row), unchanged: the links and extractors are those of one instance. This file
is on any plan of groups without a splitting. Each test is run either in every slot or once by the
shared part (slot, shared part: `RAnn`, Iop/Batch.lean).

A plan for a batch (`LdTcA`) is a plan Q (`LdTc`, Cb/Ld/LdLinCloseChain.lean), a chain of annotated
links, and the proof that its links are Q's. Here each link gets its annotation (who speaks, which
verifier messages are shared), and the chain its keys (what the statements of one batch have in
common at each joint: `JKey`, Cb/Ld/LdLinChainB.lean). The errors are fields of the plan's annotated
links; `l.lo`, `LdTcA.nil`, `consLo` and `consSh` put the one-instance errors there.
`KB` (`LinkA.KB`, Cb/Ld/LdLinChainB.lean) asks that the link is knowledge sound for the vectors with
one key, and takes them to vectors with one key. `KnowB` (Ior/BatchSeq.lean) asks, for each
statement, for sets of bad verifier messages that are within the errors, jointly for every
admissible vector, such that for a statement that meets `on`, on a transcript that avoids them, the
extractor leads a witness of the output statement back to one of the input.

Main names:
  `l.lo`: any link, run in every slot in local rounds. `Spec.link_lo_kb`: it is `KB` from knowledge
    soundness for one instance, if the first joint's condition holds of every statement, between any
    two keys such that the new key is a function of the old one.
  `LdTcA.nil`, `consLo D QA`, `consSh D QA`: nothing is left; the test D in every slot, then QA; the
    test D once, by the shared part, then QA.
  `QA.KB N k`: knowledge sound for the vectors with one key k, link by link along some keys.
  `Spec.ldPlanB_nil`, `Spec.ldPlanB_cons_local`, `Spec.ldPlanB_cons_shared`: the three rules. `nil`
    has `KB` from every key, if S has no oracle message. If `D.OK` and `QA.KB N kB`, then
    `consLo D QA` has `KB` from kA, if kB is a function of kA; and `consSh D QA`, if kB is a
    function of kA and the transcript and the test's acting part (`ldRunAct`,
    Cb/Ld/LdBatchBlocks.lean) is a function of the key kA.
  `Spec.ldLinB_cZ_kb`: the closing for a batch (`C.cZA QA fq`) is knowledge sound from the key that
    the core leaves (`C.P.k6`), if the plan says the rows that are left and `C.Ab`
    (`C.Says QA.Q.base fq`, Cb/Ld/LdLinClosePre.lean), `QA.KB N kS`, and the plan's first key kS is
    a function of k6.
  `Spec.ldLinB_close`: the whole test for at most N instances, core and closing, from "the closing
    is knowledge sound from k6" and the core's hypotheses (`C.P.FoldErr on0 εf`,
    `Function.Injective C.P.D.py`, `S.OK`; ι is not empty): `KnowB` for the vectors that share the
    encoded index and its record, on the statements with the condition of `C.P.j0 on0`; and the term
    is the one-instance test's (so `ldLinCl_tail` of Cb/Ld/LdLinCloseLin.lean speaks of the same
    links).

Limits: for a plan built by `LdTcA.nil`, `consLo`, `consSh` the errors are the core's for N
instances (`errCoreB`, Cb/Ld/LdLinB.lean), then each test's one-instance errors. How to read them
(Ior/BatchSeq.lean: the notion is "for its instances"): in a shared round the number bounds the
values that are bad for some slot that has had no bad value so far (so a shared test is paid once,
not N times); in a local round it bounds the bad values of each such slot, whose verifier message is
its own. Whoever asks "is some slot of the batch fooled" adds the local rounds' errors over the
slots: N times.
This file gives no plan but the empty one (`LdTcA.nil`; `consLo`, `consSh` build on a given test and
plan): that the rows on the shared groups are functions of k6, and which groups there are, are
hypotheses (on keys). This file says nothing on a splitting, and nothing on the honest side of a
batch. All of `KnowB`'s content hangs on which vectors are admissible (the head of
Ior/BatchSeq.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBatchBlocks
import Cb.Ld.LdLinCloseLinProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob

/-- Any link, in every slot, in local rounds. -/
def IOR.Link.lo {K : Type} {A B : IOR.Joint K} (l : IOR.Link K A B) : IOR.LinkA K A B :=
  ⟨l, RoundSplits.allLocal _, l.P.err⟩

namespace Spec
open IOR

def link_lo_kb : Prop :=
  ∀ (K : Type) (A B : Joint K) (l : Link K A B) (N : ℕ) (kA : JKey A)
      (kB : JKey B) (F : kA.κ → kB.κ),
    l.R.red.Know A.rels.on A.rels.relR B.rels.relR l.ext l.P.err → (∀ a, A.rels.on a) →
    (∀ a τ b, l.R.red.out a τ = some b → kB.key b = F (kA.key a)) → l.lo.KB N kA kB

end Spec

open IOR

theorem link_lo_kb : Spec.link_lo_kb := fun _ _ _ l N kA kB F h hon hF =>
  ⟨knowB_conseq _ _ _ _ _ _ _ _ N _ _ _ _ _ _ _ _ _ _
      (knowB_local _ _ _ _ _ _ l.R RAnn.allLocal (fun _ => rfl) N _ _ _ _ _ h) (fun _ _ => trivial)
      (fun a _ => hon a) (fun _ _ _ w => w) (fun _ _ w => w),
    sameKey_any _ _ _ _ _ _ l.R _ N kA.key kB.key F hF⟩

end Iop

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- the key at the trivial statement -/
def ldKeyT : JKey ldTrivJ := ⟨Unit, fun _ => ()⟩

/-- A plan for a batch: a plan Q (`LdTc`, Cb/Ld/LdLinCloseChain.lean), a chain of annotated links,
and the proof that its links are Q's. -/
structure LdTcA {E : Type} [Field E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) where
  Q    : LdTc S E₀ Wp
  cA   : ChainA Unit (S.jointCf Q.base) ldTrivJ
  same : cA.forget = Q.c

namespace LdTcA
variable {E : Type} [Field E] {S : Sig E} {E₀ : ExtSpec} {Wp : Type}

/-- knowledge sound for the vectors with one key k, link by link along some keys -/
def KB (QA : LdTcA S E₀ Wp) (N : ℕ) (k : JKey (S.jointCf QA.Q.base)) : Prop := QA.cA.KB N k ldKeyT

/-- Nothing is left. -/
def nil (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (w₀ : S.Wit × Wp) : LdTcA S E₀ Wp where
  Q := LdTc.nil S E₀ Wp w₀
  cA := .one
    (Link.lo ⟨(LdTl.nil S E₀ Wp w₀).R, (LdTl.nil S E₀ Wp w₀).H,
        (LdTl.nil S E₀ Wp w₀).ext, (LdTl.nil S E₀ Wp w₀).N⟩)
  same := ChainA.forget_one _

variable [Fintype E]

/-- The test D in every slot, then QA. -/
def consLo (D : LdRunD S) (QA : LdTcA (S.sub D.kp) E₀ Wp)
    (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp) : LdTcA S E₀ Wp where
  Q := LdTc.cons D QA.Q d d'
  cA := (ChainA.one (D.linkLo QA.Q.base d d')).append QA.cA
  same := (chainA_forget_append Unit _ _ _ (ChainA.one (D.linkLo QA.Q.base d d')) QA.cA).trans
    (congrArg₂ (fun c c' => Chain.append c c') (ChainA.forget_one _) QA.same)

/-- The test D once, by the shared part, then QA. -/
def consSh (D : LdRunD S) (QA : LdTcA (S.sub D.kp) E₀ Wp)
    (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp) : LdTcA S E₀ Wp where
  Q := LdTc.cons D QA.Q d d'
  cA := (ChainA.one (D.linkSh QA.Q.base d d')).append QA.cA
  same := (chainA_forget_append Unit _ _ _ (ChainA.one (D.linkSh QA.Q.base d d')) QA.cA).trans
    (congrArg₂ (fun c c' => Chain.append c c') (ChainA.forget_one _) QA.same)

end LdTcA

/-- The closing of the test, for a batch. -/
def LdLinC.cZA {E ι κ J Y : Type} [Field E] [Fintype Y] [Fintype ι] [Fintype κ]
    [Fintype J] (C : LdLinC E ι κ J Y) (QA : LdTcA C.S C.E₀ C.Wpa) (fq : C.St6 → QA.Q.St) :
    ChainA Unit C.j6J ldTrivJ :=
  (ChainA.one (C.link fq QA.Q.base).lo).append QA.cA

namespace Spec

def ldPlanB_nil : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) [IsEmpty S.O] (E₀ : ExtSpec) (Wp : Type) (w₀ : S.Wit × Wp)
      (N : ℕ) (k : JKey (S.jointCf (LdTcA.nil S E₀ Wp w₀).Q.base)),
    (LdTcA.nil S E₀ Wp w₀).KB N k

/-- A test in every slot, then a plan. -/
def ldPlanB_cons_local : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (D : LdRunD S)
      (QA : LdTcA (S.sub D.kp) E₀ Wp) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp) (N : ℕ)
      (kA : JKey (S.jointCf (D.pre QA.Q.base)))
      (kB : JKey ((S.sub D.kp).jointCf QA.Q.base)) (F : kA.κ → kB.κ),
    D.OK → QA.KB N kB →
    (∀ a τ b, (D.link QA.Q.base d d').R.red.out a τ = some b → kB.key b = F (kA.key a)) →
    (LdTcA.consLo D QA d d').KB N kA

/-- A test once, by the shared part, then a plan. -/
def ldPlanB_cons_shared : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (D : LdRunD S)
      (QA : LdTcA (S.sub D.kp) E₀ Wp) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp) (N : ℕ)
      (kA : JKey (S.jointCf (D.pre QA.Q.base))) (kB : JKey ((S.sub D.kp).jointCf QA.Q.base))
      (act : kA.κ → ((D.G.Row D.B → E) × (∀ ν, D.G.RowSt D.Sb ν)) × D.G.C.ext.Str)
      (F : kA.κ → Tr (D.link QA.Q.base d d').R.shape → kB.κ),
    D.OK → QA.KB N kB → (∀ a, ldRunAct D.G D.Sb QA.Q.St E₀ a = act (kA.key a)) →
    (∀ a τ b, (D.link QA.Q.base d d').R.red.out a τ = some b → kB.key b = F (kA.key a) τ) →
    (LdTcA.consSh D QA d d').KB N kA

section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- States that the links of the closing for a batch are those of the closing. -/
def ldLinB_cZ_same : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (QA : LdTcA C.S C.E₀ C.Wpa) (fq : C.St6 → QA.Q.St),
    (C.cZA QA fq).forget = C.cZ QA.Q fq

/-- The closing, from the key that the core leaves. -/
def ldLinB_cZ_kb : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (QA : LdTcA C.S C.E₀ C.Wpa) (fq : C.St6 → QA.Q.St) (N : ℕ)
      (kS : JKey (C.S.jointCf QA.Q.base)) (F : C.P.key6.κ → kS.κ),
    C.Says QA.Q.base fq → QA.KB N kS →
    (∀ x y, kS.key ((fq (C.toSt x), C.toSmp x), C.toE.map y) = F (C.P.k6 (x, y))) →
    (C.cZA QA fq).KB N C.P.key6 ldKeyT

/-- The whole test for at most N instances. -/
def ldLinB_close : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf N : ℕ)
      (S : C.P.Snd) (d : C.P.W0) (QA : LdTcA C.S C.E₀ C.Wpa) (fq : C.St6 → QA.Q.St),
    C.P.FoldErr on0 εf → Function.Injective C.P.D.py → S.OK → (C.cZA QA fq).KB N C.P.key6 ldKeyT →
    (C.P.linCA on0 S εf N (C.cZA QA fq) d).l.R.KnowB (C.P.linCA on0 S εf N (C.cZA QA fq) d).ann N
      (SameKey C.P.k0) (C.P.j0 on0).on (C.P.j0 on0).relR (fun _ (_ : Unit) => True)
      (C.P.linCA on0 S εf N (C.cZA QA fq) d).l.ext (C.P.linCA on0 S εf N (C.cZA QA fq) d).err ∧
    (C.P.linCA on0 S εf N (C.cZA QA fq) d).l = C.P.linC on0 S εf (C.cZ QA.Q fq) d

end
end Spec

theorem ldPlanB_nil : Spec.ldPlanB_nil := by
  intro E _ S _ E₀ Wp w₀ N k
  have h := (Chain.allT_one _).1 (ldChain_nil E S E₀ Wp w₀).1
  exact (ChainA.kb_one _ N k ldKeyT).2
    (link_lo_kb Unit _ _ _ N k ldKeyT (fun _ => ()) h.know (fun _ => trivial) fun _ _ _ _ => rfl)

theorem ldPlanB_cons_local : Spec.ldPlanB_cons_local := by
  intro E _ _ S E₀ Wp D QA d d' N kA kB F hD hQ hF
  exact chainA_kb_append Unit _ _ _ (ChainA.one (D.linkLo QA.Q.base d d')) QA.cA N kA kB ldKeyT
    ((ChainA.kb_one _ N kA kB).2
      (ldRunB_link_local E S D QA.Q.St Wp E₀ QA.Q.base d d' N kA kB F hD hF)) hQ

theorem ldPlanB_cons_shared : Spec.ldPlanB_cons_shared := by
  intro E _ _ S E₀ Wp D QA d d' N kA kB act F hD hQ hact hF
  exact chainA_kb_append Unit _ _ _ (ChainA.one (D.linkSh QA.Q.base d d')) QA.cA N kA kB ldKeyT
    ((ChainA.kb_one _ N kA kB).2
      (ldRunB_link_shared E S D QA.Q.St Wp E₀ QA.Q.base d d' N kA kB act F hD hact hF)) hQ

section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

omit [Fintype E] [Nonempty ι] in
theorem ldLinB_cZ_same : Spec.ldLinB_cZ_same E ι κ J Y := by
  intro C QA fq
  unfold LdLinC.cZA LdLinC.cZ
  rw [chainA_forget_append, ChainA.forget_one, QA.same]
  rfl

omit [Fintype E] [Nonempty ι] in
theorem ldLinB_cZ_kb : Spec.ldLinB_cZ_kb E ι κ J Y := by
  intro C QA fq N kS F hS hQ hF
  have hT := ldLinPre_step_cf E ι κ J Y C QA.Q.St QA.Q.base fq hS
  refine chainA_kb_append Unit _ _ _ (ChainA.one (C.link fq QA.Q.base).lo)
    QA.cA N C.P.key6 kS ldKeyT ((ChainA.kb_one _ N _ kS).2 ?_) hQ
  refine link_lo_kb Unit _ _ (C.link fq QA.Q.base) N C.P.key6 kS F ?_ (fun _ => trivial) ?_
  · rintro ⟨x, y⟩ _ b w hb hw
    obtain rfl := Option.some.inj hb
    exact hT.know x y _ w trivial rfl hw
  · rintro ⟨x, y⟩ τ b hb
    obtain rfl := Option.some.inj hb
    exact hF x y

theorem ldLinB_close : Spec.ldLinB_close E ι κ J Y := by
  intro C on0 εf N S d QA fq hF hpy hS hKB
  refine ⟨ldLinCB_know C.P on0 εf N S (C.cZA QA fq) ldKeyT d hF hpy hS hKB, ?_⟩
  rw [ldLinCB_same]
  exact congrArg (fun c => C.P.linC on0 S εf c d) (ldLinB_cZ_same E ι κ J Y C QA fq)

end
end Cb
