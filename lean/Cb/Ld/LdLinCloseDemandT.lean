-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseDemandT.lean: the last part of a test for linear constraints on an encoded matrix
(the index), for a plan with four proximity tests on groups of oracles and two steps that split a
linear claim: what all instances of a batch share comes first, then what is an instance's own.

The core of the test for linear constraints (Cb/Ld/LdLin.lean) is an interactive oracle reduction
from one linear claim on the encoded index to linear claims ("rows") on the messages (`Sig.Msg`,
Cb/Ld/LdSig.lean) of oracle messages that it sends and on a function (`C.rest`) of those that the
preamble left. A front is a sequence of sub-reductions that sends, drops and tests no oracle
message.

Definitions and statements; the proofs are in Cb/Ld/LdLinCloseDemandTProofs.lean.
It uses Cb/Ld/LdLinClosePlanT.lean (the plan `p`: stages, fronts, base joints; κ° is the entry that
its field `k₀` names, κ_c the one that `k₁` names), Cb/Ld/LdLinCloseAlt.lean (fronts and whole tests
alternate: `Q.OkBehind c₀`), Cb/Ld/LdLinCloseDemand.lean (positions add up),
Cb/Ld/LdLinCloseLin.lean (`C.cZ`: the step without rounds, then a closing) and Cb/Ld/LdLinChain.lean
(the test's core as a chain).
A closing `Q : LdTc C.S C.E₀ C.Wpa` (Cb/Ld/LdLinCloseChain.lean) has a base joint `Q.base`, a chain
`Q.c` to the trivial statement and a demand on positions `Q.q`. "Fresh": `FreshFor`,
Ior/KnowCollRulesChain.lean.
`TailTr`, a tail of a chain, asks of a reduction from a joint to a joint whose statements have no
oracles the bundle `IOR.GoodT` and three further clauses, `noHid`, `tied` and `bears`, which
Cb/Ld/LdTowerKit.lean states (through `IOR.Tied`, Ior/Batch.lean, and `IOR.Bears`, Ior/Bears.lean).
`IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its
honest side, between two joints, at given numbers; among its clauses: completeness between the
honest relations, outside sets of verifier randomness whose probabilities further clauses bound by
the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input
joint's set of statements, with a given extractor, at the numbers' list of errors; and one on
honest-verifier zero knowledge.

Main names:
  `Spec.ldLinAlt_tail` (by way of `Spec.ldLinAlt_chain`, which concludes `(C.cZ Q fq).OkFrom` the
    core and `(C.cZ Q fq).SidesCT (C.P.q5 Sn qa)`): generic, for any closing Q of the test. Under
    the core's hypotheses (ι nonempty, `C.P.FoldErr on0 εf`, `C.P.D.py` injective, `Sn.OK`): if Q's
    base joint says the rows that are left (`C.Says Q.base fq`), Q is in order after the core and
    the step, and Q's demand is within what the three sendings bear (`C.P.q5 Sn qa`), then the test
    with the closing `C.cZ Q fq` is a tail. Cb/Ld/LdLinCloseLin.lean has this for closings that are
    in order by themselves.
  `T.Q` (`T : LdLinPtT p`): the whole closing: front₁ ; D₁ ; D₂ (the shared front and tests) ;
    front₂ ; D₃ ; D₄ (the instance's) ; Q' (the closing of what is left).
  `Spec.ldLinPtT_behind`: under the hypotheses of its statement, the two on masks among them, `T.Q`
    is in order after the core and the step (`T.c₀`).
  `Spec.ldLinPtT_demand`: under the hypotheses of its statement, the demand of `T.Q` is within what
    the three sendings bear, if T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) is at most ba on
    what the preamble left, and at most the senders' numbers: the same bound as with both splittings
    in front (Cb/Ld/LdLinCloseDemandS.lean): a front reads no position.
  `Spec.ldLinPtT_tail`: under the hypotheses of these two statements, the test with this closing is
    a tail, from the claim on the encoded index to the trivial statement.
  Hypotheses on masks, two, each at the chain at which it is used: κ° is fresh after `T.c₀` (and the
    link that does nothing); κ_c is fresh after `T.c₂` (and the link that does nothing): behind the
    core, the step, front₁ and the two shared tests.

Limits: this file does not say these two facts, the two hypotheses on masks above. It says nothing
on the batch's two sides. It does not say that the hypotheses can be met together.
The plan with two splittings is not the technical report's (head of Cb/Ld/LdLinClosePlanT.lean);
the report's: Cb/Ld/LdLinClosePlanP.lean, Cb/Ld/LdLinCloseDemandP.lean,
Cb/Ld/LdLinCloseDemandPA.lean. The generic part of this file (`ldLinAlt_chain`, `ldLinAlt_tail`)
serves the report's plan too.

Terms: lean/GLOSSARY.md.
"The technical report": this protocol's technical report (lean/CREDITS.md).
-/
import Cb.Ld.LdLinClosePlanTProofs
import Cb.Ld.LdLinCloseDemandS
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The data of the four tests: for each of the four groups the zero-evader, the whole test, the
bound on the list, the number of positions, and two proofs: the group has a common long position
(`ne₁` to `ne₄`), and every oracle message is a member or kept (`hc₁` to `hc₄`); the closing `Q'` of
what is left, with `fa` for its explicit part; `d₁` to `d₄'`: default values for the tests'
extractors. -/
structure LdLinPtT {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype Y] [Fintype κ] [Fintype J]
    {C : LdLinC E ι κ J Y} (p : LdLinPt C) where
  [ne₁ : Nonempty p.GU.P]
  hc₁ : ∀ o, p.GU.mem o ∨ p.kp₁ o
  Z₁  : Evader E (p.GU.Row (C.Brc ⊕ Unit))
  T₁  : LdEnd (p.GU.joint (fun _ => C.Sh6) p.r₁ Z₁)
  L₁  : ℕ
  t₁  : ℕ
  [ne₂ : Nonempty p.G₂.P]
  hc₂ : ∀ o, p.G₂.mem o ∨ p.kp₂ o
  Z₂  : Evader E (p.G₂.Row Unit)
  T₂  : LdEnd (p.G₂.joint (fun _ => C.Sh6) p.r₂ Z₂)
  L₂  : ℕ
  t₂  : ℕ
  [ne₃ : Nonempty p.GcO.P]
  hc₃ : ∀ o, p.GcO.mem o ∨ p.kp₃ o
  Z₃  : Evader E (p.GcO.Row Unit)
  T₃  : LdEnd (p.GcO.joint (fun _ => C.St6) p.r₃ Z₃)
  L₃  : ℕ
  t₃  : ℕ
  [ne₄ : Nonempty p.G₄.P]
  hc₄ : ∀ o, p.G₄.mem o ∨ p.kp₄ o
  Z₄  : Evader E (p.G₄.Row LinB₂)
  T₄  : LdEnd (p.G₄.joint (fun _ => C.St6) p.r₄ Z₄)
  L₄  : ℕ
  t₄  : ℕ
  Q'  : LdTc p.S₄ C.E₀ C.Wpa
  fa  : C.Sta → Q'.St
  d₁  : C.S.Wit × C.Wpa
  d₁' : LdBrW p.GU p.kp₁ C.Wpa
  d₂  : p.S₁.Wit × C.Wpa
  d₂' : LdBrW p.G₂ p.kp₂ C.Wpa
  d₃  : p.S₂.Wit × C.Wpa
  d₃' : LdBrW p.GcO p.kp₃ C.Wpa
  d₄  : p.S₃.Wit × C.Wpa
  d₄' : LdBrW p.G₄ p.kp₄ C.Wpa

namespace LdLinPtT
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype Y] [Fintype κ] [Fintype J]
  {C : LdLinC E ι κ J Y} {p : LdLinPt C} (T : LdLinPtT p)

@[reducible] def D₁ : LdRunD C.S :=
  { G := p.GU, neP := T.ne₁, kp := p.kp₁, hc := T.hc₁, B := C.Brc ⊕ Unit, Sb := fun _ => C.Sh6,
    sl := p.r₁, Z := T.Z₁, T := T.T₁, L := T.L₁, t := T.t₁ }
@[reducible] def D₂ : LdRunD p.S₁ :=
  { G := p.G₂, neP := T.ne₂, kp := p.kp₂, hc := T.hc₂, B := Unit, Sb := fun _ => C.Sh6, sl := p.r₂,
    Z := T.Z₂, T := T.T₂, L := T.L₂, t := T.t₂ }
@[reducible] def D₃ : LdRunD p.S₂ :=
  { G := p.GcO, neP := T.ne₃, kp := p.kp₃, hc := T.hc₃, B := Unit, Sb := fun _ => C.St6, sl := p.r₃,
    Z := T.Z₃, T := T.T₃, L := T.L₃, t := T.t₃ }
@[reducible] def D₄ : LdRunD p.S₃ :=
  { G := p.G₄, neP := T.ne₄, kp := p.kp₄, hc := T.hc₄, B := LinB₂, Sb := fun _ => C.St6, sl := p.r₄,
    Z := T.Z₄, T := T.T₄, L := T.L₄, t := T.t₄ }

/-- The instance's two tests, then the closing of what is left. -/
def Q₃ : LdTc p.S₂ C.E₀ C.Wpa :=
  LdTc.cons T.D₃ (LdTc.cons T.D₄ T.Q' T.d₄ T.d₄') T.d₃ T.d₃'
/-- The instance's front in front of `Q₃`. -/
def Q₂ : LdTc p.S₂ C.E₀ C.Wpa := LdTc.front (p.x₂ T.Q'.base) T.Q₃ (p.front₂ T.Q'.base)
/-- The two shared tests in front of `Q₂`. -/
def Q₁ : LdTc C.S C.E₀ C.Wpa :=
  LdTc.cons T.D₁ (LdTc.cons T.D₂ T.Q₂ T.d₂ T.d₂') T.d₁ T.d₁'
/-- The whole closing: the shared front in front of `Q₁`. -/
def Q : LdTc C.S C.E₀ C.Wpa := LdTc.front (p.x₁ T.Q'.base) T.Q₁ (p.front₁ T.Q'.base)

variable [Fintype ι] [Nonempty ι]
  (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (Sn : C.P.Snd)

/-- The core and the step without rounds. -/
def c₀ := (C.P.chain on0 Sn εf).append (C.chain (C.fqT T.fa) (p.x₁ T.Q'.base).A)
/-- `c₀`, then the shared front. -/
def c₁ := (T.c₀ on0 εf Sn).append (LdTc.frontC (p.front₁ T.Q'.base))
/-- `c₁`, then the two shared tests: all that comes before the instance's front. -/
def c₂ := ((T.c₁ on0 εf Sn).snoc
    (T.D₁.link (LdTc.cons T.D₂ T.Q₂ T.d₂ T.d₂').base T.d₁ T.d₁')).snoc
  (T.D₂.link T.Q₂.base T.d₂ T.d₂')

end LdLinPtT

namespace Spec
section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

open Classical in
/-- A closing that is in order after the core and the step. -/
def ldLinAlt_chain : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ)
      (Sn : C.P.Snd) (qa : Finset C.P.Ea.Pos → Prop) (Q : LdTc C.S C.E₀ C.Wpa) (fq : C.St6 → Q.St),
    C.P.FoldErr on0 εf → Function.Injective C.P.D.py → Sn.OK → C.Says Q.base fq →
    Q.OkBehind ((C.P.chain on0 Sn εf).append (C.chain fq Q.base)) →
    (∀ V, Q.q V → C.P.q5 Sn qa (V.biUnion C.toE.src)) →
    (C.cZ Q fq).OkFrom (C.P.chain on0 Sn εf) ∧ (C.cZ Q fq).SidesCT (C.P.q5 Sn qa)

open Classical in
def ldLinAlt_tail : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ)
      (Sn : C.P.Snd) (qa : Finset C.P.Ea.Pos → Prop) (d : C.P.W0)
      (Q : LdTc C.S C.E₀ C.Wpa) (fq : C.St6 → Q.St),
    C.P.FoldErr on0 εf → Function.Injective C.P.D.py → Sn.OK → C.Says Q.base fq →
    Q.OkBehind ((C.P.chain on0 Sn εf).append (C.chain fq Q.base)) →
    (∀ V, Q.q V → C.P.q5 Sn qa (V.biUnion C.toE.src)) →
    TailTr (C.P.linC on0 Sn εf (C.cZ Q fq) d).R (C.P.linC on0 Sn εf (C.cZ Q fq) d).H
      (C.P.j0 on0) trivRels (C.P.linC on0 Sn εf (C.cZ Q fq) d).ext
      (C.P.linC on0 Sn εf (C.cZ Q fq) d).P (C.P.q0 qa)

/-- States, for ι nonempty and under the hypotheses below: the whole closing is in order after the
core and the step. Limits: the head. -/
def ldLinPtT_behind : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPt C) (T : LdLinPtT p)
      (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (Sn : C.P.Snd)
      (Rd₁ : C.S.Ent → Prop) (Rr₁ : C.S.O → Prop) (Rd₂ : p.S₂.Ent → Prop) (Rr₂ : p.S₂.O → Prop),
    C.P.FoldErr on0 εf → Function.Injective C.P.D.py → Sn.OK →
    (∀ sa m, p.restG.val sa (p.GcW.msg (p.left₂ m)) = C.rest sa (C.aM m)) →
    p.SaysA T.Q'.base T.fa → p.Plain → p.Kept → T.D₁.OK → T.D₂.OK → T.D₃.OK → T.D₄.OK → T.Q'.OK →
    (∀ n, p.Rs₀ n → Rd₁ n) → (∀ n, p.Rs₁ n → Rd₂ n) →
    ((T.c₀ on0 εf Sn).append (.one (p.x₁ T.Q'.base).stage.idLink)).FreshFor
      ((p.x₁ T.Q'.base).stage.wideFact Rd₁ Rr₁ (fun n => n = ⟨p.k₀.o, p.k₀.j⟩) E fun u _ => u).kc E
      ((p.x₁ T.Q'.base).stage.wideFact Rd₁ Rr₁ (fun n => n = ⟨p.k₀.o, p.k₀.j⟩) E fun u _ => u).put →
    ((T.c₂ on0 εf Sn).append (.one (p.x₂ T.Q'.base).stage.idLink)).FreshFor
      ((p.x₂ T.Q'.base).stage.wideFact Rd₂ Rr₂ (fun n => n = ⟨p.k₁.o, p.k₁.j⟩) E fun u _ => u).kc E
      ((p.x₂ T.Q'.base).stage.wideFact Rd₂ Rr₂ (fun n => n = ⟨p.k₁.o, p.k₁.j⟩) E fun u _ => u).put →
    T.Q.OkBehind (T.c₀ on0 εf Sn)

open Classical in
def ldLinPtT_demand : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPt C) (T : LdLinPtT p) (Sn : C.P.Snd)
      (qa : Finset C.P.Ea.Pos → Prop) (q₀ : Finset C.E₀.Pos → Prop)
      (ba : C.Sa.O → ℕ) (b' : p.S₄.O → ℕ),
    (∀ V, T.Q'.q V → p.S₄.qFam q₀ b' V) → (∀ W, C.Sa.qFam q₀ ba W → qa W) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) (.inl (.inl (.inl a))) ≤ ba a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) (.inl (.inl (.inr a))) ≤ Sn.tW a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) (.inl (.inr a)) ≤ Sn.tU a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) (.inr a) ≤ Sn.tO a) →
    ∀ V, T.Q.q V → C.P.q5 Sn qa (V.biUnion C.toE.src)

/-- States, for ι nonempty and under the hypotheses below: the test with the closing in the order of
a batch is a tail. Limits: the head. -/
def ldLinPtT_tail : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPt C) (T : LdLinPtT p)
      (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (Sn : C.P.Snd)
      (qa : Finset C.P.Ea.Pos → Prop) (d : C.P.W0) (q₀ : Finset C.E₀.Pos → Prop)
      (ba : C.Sa.O → ℕ) (b' : p.S₄.O → ℕ) (Rd₁ : C.S.Ent → Prop) (Rr₁ : C.S.O → Prop)
      (Rd₂ : p.S₂.Ent → Prop) (Rr₂ : p.S₂.O → Prop),
    C.P.FoldErr on0 εf → Function.Injective C.P.D.py → Sn.OK →
    (∀ sa m, p.restG.val sa (p.GcW.msg (p.left₂ m)) = C.rest sa (C.aM m)) →
    p.SaysA T.Q'.base T.fa → p.Plain → p.Kept → T.D₁.OK → T.D₂.OK → T.D₃.OK → T.D₄.OK → T.Q'.OK →
    (∀ n, p.Rs₀ n → Rd₁ n) → (∀ n, p.Rs₁ n → Rd₂ n) →
    ((T.c₀ on0 εf Sn).append (.one (p.x₁ T.Q'.base).stage.idLink)).FreshFor
      ((p.x₁ T.Q'.base).stage.wideFact Rd₁ Rr₁ (fun n => n = ⟨p.k₀.o, p.k₀.j⟩) E fun u _ => u).kc E
      ((p.x₁ T.Q'.base).stage.wideFact Rd₁ Rr₁ (fun n => n = ⟨p.k₀.o, p.k₀.j⟩) E fun u _ => u).put →
    ((T.c₂ on0 εf Sn).append (.one (p.x₂ T.Q'.base).stage.idLink)).FreshFor
      ((p.x₂ T.Q'.base).stage.wideFact Rd₂ Rr₂ (fun n => n = ⟨p.k₁.o, p.k₁.j⟩) E fun u _ => u).kc E
      ((p.x₂ T.Q'.base).stage.wideFact Rd₂ Rr₂ (fun n => n = ⟨p.k₁.o, p.k₁.j⟩) E fun u _ => u).put →
    (∀ V, T.Q'.q V → p.S₄.qFam q₀ b' V) → (∀ W, C.Sa.qFam q₀ ba W → qa W) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) (.inl (.inl (.inl a))) ≤ ba a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) (.inl (.inl (.inr a))) ≤ Sn.tW a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) (.inl (.inr a)) ≤ Sn.tU a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need (T.D₄.need b'))) (.inr a) ≤ Sn.tO a) →
    TailTr (C.P.linC on0 Sn εf (C.cZ T.Q (C.fqT T.fa)) d).R
      (C.P.linC on0 Sn εf (C.cZ T.Q (C.fqT T.fa)) d).H (C.P.j0 on0) trivRels
      (C.P.linC on0 Sn εf (C.cZ T.Q (C.fqT T.fa)) d).ext
      (C.P.linC on0 Sn εf (C.cZ T.Q (C.fqT T.fa)) d).P (C.P.q0 qa)

end
end Spec
end Cb
