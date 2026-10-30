-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinClosePlanPB.lean: the test for linear constraints for at most N instances, with the
technical report's plan (one splitting, the shared one): the plan for a batch, and round-by-round
knowledge soundness with no hypothesis on keys left but `cA'.KB N (ldKeyU _) ldKeyT`.

In standard terms: under the hypotheses below, round-by-round knowledge soundness of an interactive
oracle proof that proves at most N instances at once, for the vectors of statements that share the
encoded index and its record (on the statements with the input joint's condition; what is extracted
is a witness of its relaxed relation: see the row of `Spec.ldLinPpB_know`), where a part of the
prover's messages and of the verifier's challenges is shared by all instances.
Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLinClosePlanPBProofs.lean.
A key (`JKey`, Cb/Ld/LdLinChainB.lean) is a function of the statement at a joint; `KB N k k'` says
that each annotated link is round-by-round knowledge sound (`IOR.KnowB`, Ior/BatchSeq.lean) for the
vectors of statements that have one key, and takes them to such vectors: from the key k at the first
joint to k' at the last, along some keys at the joints between. The acting part of a test
(`ldRunAct`, Cb/Ld/LdBatchBlocks.lean) is all rows that it takes in, with targets and states, and
its members' words.
The plan is that of Cb/Ld/LdLinClosePlanP.lean, its tests those of Cb/Ld/LdLinCloseDemandP.lean (T :
LdLinPpT p), unchanged. For a batch:
  The front (the fold's row is split by one entry of the shared mask-only message; each row goes to
    its test): by the shared part: the scalar is one for all slots. (That the message is mask-only
    is not asked: Cb/Ld/LdLinClosePlanP.lean, Limits, (1).)
  The first test (G_u's group: the record's rows, the columns, the u-half) and the second (Ω's
    group: the ω-half): each once, by the shared part, under shared verifier messages.
  The third test (the instance's group: evaluation, inner product): in every slot, in the slot's
    local rounds.
  What closes the rest (`T.Q'`): a chain of annotated links cA' whose links are those of `T.Q'.c`: a
    parameter; asked: knowledge sound for every vector of statements.

Main names:
  `Spec.ldRun_out`: what a whole test's reduction hands on does not depend on the transcript: if it
    accepts, the new statement is (`D.outX`, `D.outY`) of the old one: what is claimed beside the
    test's rows, the further oracles, and samples and words of the oracle messages that are kept.
  `Spec.ldLinPpB_same`: the links of the closing for a batch are those of C.cZ (LdTc.front (p.x₁ ..)
    T.Q T.front) (C.fqP T.fa). That chain has one link more than the C.cZf .. of
    Cb/Ld/LdLinCloseDemandP.lean: the link that does nothing, at the head of the front (no round, no
    message). The theorems for one instance on this very chain: Cb/Ld/LdLinCloseDemandPA.lean
    (`T.QF`; `ldLinPpT_tailA`, `ldLinPpT_topA`). No theorem of this library states that the
    hypotheses of `ldLinPpT_tailA` or `ldLinPpT_topA` can be met together.
  `Spec.ldLinPpB_act`: the acting parts of both shared tests.
  `Spec.ldLinPpB_kb`: the closing is knowledge sound from the key `C.P.key6`. Asked: `p.Shared`;
    `restG` is "rest"; `T.Q'.base` says Ab (`p.SaysA`); `p.Plain`; `p.Kept`; the three tests' own
    hypotheses (`T.D₁.OK`, `T.D₂.OK`, `T.D₃.OK`); cA', whose links are those of `T.Q'.c` (`same'`),
    is knowledge sound for every vector of statements.
  `Spec.ldLinPpB_know`: the whole test for linear constraints (core and closing): `KnowB` for the
    vectors that share the encoded index and its record (on the statements with the condition
    `(C.P.j0 on0).on`, Cb/Ld/LdLin.lean; what is extracted is a witness of the relaxed relation
    `(C.P.j0 on0).relR`); and its link is that of the test for one instance with the chain of
    `Spec.ldLinPpB_same`. Asked: what `Spec.ldLinPpB_kb` asks, and `C.P.FoldErr on0 εf`, `C.P.D.py`
    injective, `Sn.OK`, ι not empty.

The errors: the core's for N instances; 0 for the splitting; the two shared tests', each paid once;
the third test's, in local rounds; then the rest's (cA' is a parameter, with annotations of its
own).

Notation: `on0`: a predicate on `C.P.D.X.Row → ι → E` and `C.P.D.X.Rec`; `εf`, `N`: natural numbers;
`Sn`: the honest senders, and the numbers of the three sendings (`C.P.Snd`, Cb/Ld/LdLin.lean); `d`
(in `Spec.ldLinPpB_know`): a value of `C.P.W0`; `ldKeyU`: the key that says nothing: every vector of
statements has one key (Cb/Ld/LdBatchPlanLin.lean); `ldKeyT`: the key at the trivial statement
(Cb/Ld/LdBatchBlocksPlan.lean); `C.P.key6`: the key `⟨_, C.P.k6⟩` (Cb/Ld/LdLinChainB.lean; `k0`,
`k6`: Cb/Ld/LdLinB.lean); `C.P.FoldErr on0 εf`:
`∀ f rec, on0 f rec → cnt (C.P.D.X.Bad f rec C.P.e') ≤ εf` (Cb/Ld/LdLin.lean).

Limits: this file says nothing on the honest side of a batch (Cb/Ld/LdLinClosePlanPV.lean). This
file does not say that the hypotheses can be met together (`ldLinPpB_kb` is used in the proof of
`ldObjPp_parts`, Cb/Obj/LdObjectPlanPaper.lean). No theorem of this library states that the
hypotheses of `ldLinPpB_know` can be met together.

Terms: lean/GLOSSARY.md.
"The technical report": this protocol's technical report (lean/CREDITS.md).
-/
import Cb.Ld.LdLinCloseDemandP
import Cb.Ld.LdBatchPlanLin
import Cb.Ld.LdFrontOn
import Cb.Ld.LdFrontBProofs
import Cb.Ld.LdLinCloseV
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace LdLinPpT
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype Y] [Fintype κ] [Fintype J]
  {C : LdLinC E ι κ J Y} {p : LdLinPp C} (T : LdLinPpT p)

/-- the three tests and the rest, for a batch: two by the shared part, one in every slot -/
def QAt (cA' : ChainA Unit (p.S₃.jointCf T.Q'.base) ldTrivJ)
    (same' : cA'.forget = T.Q'.c) : LdTcA C.S C.E₀ C.Wpa :=
  LdTcA.consSh T.D₁
    (LdTcA.consSh T.D₂ (LdTcA.consLo T.D₃ ⟨T.Q', cA', same'⟩ T.d₃ T.d₃') T.d₂ T.d₂') T.d₁ T.d₁'

/-- The plan for a batch: the front by the shared part, then these. -/
def QA (cA' : ChainA Unit (p.S₃.jointCf T.Q'.base) ldTrivJ)
    (same' : cA'.forget = T.Q'.c) : LdTcA C.S C.E₀ C.Wpa :=
  LdTcA.front (p.x₁ T.Q'.base)
    (T.QAt cA' same') T.front (T.front.cA true) (frontB_forget E C.S C.E₀ C.Wpa _ _ T.front true)

/-- the key in front of the second shared test: its acting part -/
def kA₂ : JKey (p.S₁.jointCf (T.D₂.pre (LdTc.cons T.D₃ T.Q' T.d₃ T.d₃').base)) :=
  ⟨_, ldRunAct p.G₂ (fun _ : Unit => C.Sh6) _ C.E₀⟩

/-- the key in front of the first shared test: its acting part, and that of the second at what the
first hands on -/
def kA₁ :
    JKey
      (C.S.jointCf (T.D₁.pre (LdTc.cons T.D₂ (LdTc.cons T.D₃ T.Q' T.d₃ T.d₃') T.d₂ T.d₂').base)) :=
  ⟨_, fun a =>
      (ldRunAct p.GU (fun _ : C.Brc ⊕ Unit => C.Sh6) _ C.E₀ a,
        T.kA₂.key (T.D₁.outX a.1, T.D₁.outY a.2))⟩

/-- the key at the head of the front: for each scalar, the key after the front -/
def kAx : JKey (p.x₁ T.Q'.base).stage.J :=
  ⟨E → T.kA₁.κ,
    fun a u =>
      T.kA₁.key ((((Sum.elim (splitNx C.S C.Sh6 C.Sh6 _ a.1 u).1.2.1.1 fun _ =>
                  (splitNx C.S C.Sh6 C.Sh6 _ a.1 u).1.1.2.1,
                Sum.elim (splitNx C.S C.Sh6 C.Sh6 _ a.1 u).1.2.1.2 fun _ =>
                  (splitNx C.S C.Sh6 C.Sh6 _ a.1 u).1.1.2.2),
              (oneClaim (splitNx C.S C.Sh6 C.Sh6 _ a.1 u).1.1.1,
                (splitNx C.S C.Sh6 C.Sh6 _ a.1 u).1.2.2)),
            (splitNx C.S C.Sh6 C.Sh6 _ a.1 u).2),
          (sideG C.S (ExtMap.id C.E₀)).map a.2)⟩

end LdLinPpT

namespace Spec

/-- States: what a whole test's reduction hands on does not depend on the transcript. -/
def ldRun_out : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (St₀ Wp : Type)
      (E₀ : ExtSpec) (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp))
      (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp) a τ b,
    (D.link A₀ d d').R.red.out a τ = some b → b = (D.outX a.1, D.outY a.2)

section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- The links of the closing for a batch. -/
def ldLinPpB_same : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPp C) (T : LdLinPpT p)
      (cA' : ChainA Unit (p.S₃.jointCf T.Q'.base) ldTrivJ) (same' : cA'.forget = T.Q'.c),
    (C.cZA (T.QA cA' same') (C.fqP T.fa)).forget =
      C.cZ (LdTc.front (p.x₁ T.Q'.base) T.Q T.front) (C.fqP T.fa)

/-- States: if `p.Shared`, for statements with one key k6, and one scalar, both shared tests' acting
parts are the same. -/
def ldLinPpB_act : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPp C) (T : LdLinPpT p) (x x' : C.P.X6) (y y' : C.P.E5.Str),
    p.Shared → C.P.k6 (x, y) = C.P.k6 (x', y') →
    T.kAx.key ((C.fqP T.fa (C.toSt x), C.toSmp x), C.toE.map y) =
      T.kAx.key ((C.fqP T.fa (C.toSt x'), C.toSmp x'), C.toE.map y')

/-- States, under the premises below: the closing is knowledge sound from the key `C.P.key6`. -/
def ldLinPpB_kb : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPp C) (T : LdLinPpT p)
      (cA' : ChainA Unit (p.S₃.jointCf T.Q'.base) ldTrivJ) (same' : cA'.forget = T.Q'.c) (N : ℕ),
    p.Shared → (∀ sa m, p.restG.val sa (p.Gc.msg (p.left₂ m)) = C.rest sa (C.aM m)) →
    p.SaysA T.Q'.base T.fa → p.Plain → p.Kept → T.D₁.OK → T.D₂.OK → T.D₃.OK →
    cA'.KB N (ldKeyU _) ldKeyT → (C.cZA (T.QA cA' same') (C.fqP T.fa)).KB N C.P.key6 ldKeyT

/-- States, for ι not empty and under the premises below: `KnowB` of the test for linear constraints
for at most N instances, for the vectors that share the encoded index and its record, on the
statements with the condition `(C.P.j0 on0).on`; what is extracted is a witness of
`(C.P.j0 on0).relR`. -/
def ldLinPpB_know : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPp C) (T : LdLinPpT p)
      (cA' : ChainA Unit (p.S₃.jointCf T.Q'.base) ldTrivJ) (same' : cA'.forget = T.Q'.c) (N : ℕ)
      (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (Sn : C.P.Snd) (d : C.P.W0),
    C.P.FoldErr on0 εf → Function.Injective C.P.D.py → Sn.OK → p.Shared →
    (∀ sa m, p.restG.val sa (p.Gc.msg (p.left₂ m)) = C.rest sa (C.aM m)) → p.SaysA T.Q'.base T.fa →
    p.Plain → p.Kept → T.D₁.OK → T.D₂.OK → T.D₃.OK → cA'.KB N (ldKeyU _) ldKeyT →
    (C.P.linCA on0 Sn εf N (C.cZA (T.QA cA' same') (C.fqP T.fa)) d).l.R.KnowB
      (C.P.linCA on0 Sn εf N (C.cZA (T.QA cA' same') (C.fqP T.fa)) d).ann N (SameKey C.P.k0)
      (C.P.j0 on0).on (C.P.j0 on0).relR (fun _ (_ : Unit) => True)
      (C.P.linCA on0 Sn εf N (C.cZA (T.QA cA' same') (C.fqP T.fa)) d).l.ext
      (C.P.linCA on0 Sn εf N (C.cZA (T.QA cA' same') (C.fqP T.fa)) d).err ∧
    (C.P.linCA on0 Sn εf N (C.cZA (T.QA cA' same') (C.fqP T.fa)) d).l =
      C.P.linC on0 Sn εf (C.cZ (LdTc.front (p.x₁ T.Q'.base) T.Q T.front) (C.fqP T.fa)) d

end
end Spec
end Cb
