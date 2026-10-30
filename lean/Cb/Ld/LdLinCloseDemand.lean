-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseDemand.lean: what several tests in a row need of the oracle messages: an oracle
message that lies in two tests bears the sum of their positions.

Definitions, and statements (each statement a `Prop` in `Cb.Spec`); the proofs are in
Cb/Ld/LdLinCloseDemandProofs.lean.
It uses Cb/Ld/LdLinCloseChain.lean (a closing as a chain: `LdTc`, with its demand on positions
`Q.q`), Cb/Ld/LdSendPiece.lean (`S.qFam q₀ b`: of the further oracles what q₀ allows, of each oracle
message o at most b o long positions).
In standard terms: a demand ("what is needed of the oracles") is a predicate on finite sets of
oracle positions. "Q needs at most b and q₀" says that every set within the demand `Q.q` is within
`S.qFam q₀ b`.

Why: a sending is honest-verifier zero knowledge against a bounded number of long positions of each
word (`Spec.ldSendFam_exactWith`, Cb/Ld/LdSendFam.lean, under its hypotheses). The theorems on a
closing behind the test for linear constraints ask, as a hypothesis, that what the closing needs
lies within what the three sendings bear. Here that hypothesis is brought down to inequalities
between numbers.

Main names:
  `D.need b'`, the bound after one more test: of the oracle message o: (`D.t` if o is a member of
    the test's group) + (b' of it if it is kept).
  `Spec.ldDemand_nil`: the closing with nothing left needs nothing: it is within every `S.qFam q₀ b`
    with `q₀ ∅`.
  `Spec.ldDemand_cons`: the rule for one more test.
  `Spec.ldDemand_le`: D.need b' o ≤ D.t + (b' if kept).
  `Spec.ldDemand_lin`: through the re-bracketing of Cb/Ld/LdLinClosePre.lean: at most b of the
    oracle messages of `C.S` is within the demand q5 of Cb/Ld/LdLin.lean, if b is at most the three
    senders' numbers on the three families, and at most ba on what the preamble left, and qa allows
    what q₀ and ba allow.
  `LdLinPlT p`: the tests of the plan without a splitting: for each of the two groups the
    zero-evader, the whole test, the bound on the list, the number of positions; the closing Q' of
    what is left; further fields: `fa`, `d₁` to `d₂'`; `ne₁`, `ne₂`, `hc₁`, `hc₂` hold proofs.
  `Spec.ldDemand_plan`: the demand of `T.Q` is within q5, from: T.D₁.need (T.D₂.need b') is at most
    the senders' numbers, and at most ba on what the preamble left; Q' needs at most b' and q₀; qa
    allows what q₀ and ba allow.
  `Spec.ldDemand_plain`: in plain numbers. By it the inequalities of `Spec.ldDemand_plan` on the
    three families follow from t₁ + t₂ ≤ the sender's number of every member of the three families,
    if Q' needs nothing of them.
  `Spec.ldLinPlan_tail`: under the hypotheses that follow, the test for linear constraints with the
    closing of the plan is a tail of a chain, from its input joint (`C.P.j0 on0`) to the trivial
    statement: the core's hypotheses (ι nonempty, `C.P.FoldErr on0 εf`, `C.P.D.py` injective,
    `Sn.OK`); and on the closing no others, beside whatever the arguments hold as proofs, than the
    tests' own (`T.D₁.OK`, `T.D₂.OK`), `Q'.OK`, "restG is rest" (the equation on `p.restG.val`), "Q'
    says Ab" (`p.SaysA T.Q'.base T.fa`) and those of `Spec.ldDemand_plan`, the inequalities among
    them.
In `Spec.ldLinPlan_tail`, `TailTr` is the conclusion. `TailTr`, a tail of a chain, asks of a
reduction from a joint to a joint whose statements have no oracles the bundle `IOR.GoodT` and three
further clauses, `noHid`, `tied` and `bears`, which Cb/Ld/LdTowerKit.lean states (through
`IOR.Tied`, Ior/Batch.lean, and `IOR.Bears`, Ior/Bears.lean).
`IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its
honest side, between two joints, at given numbers; among its clauses: completeness between the
honest relations, outside sets of verifier randomness whose probabilities further clauses bound by
the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input
joint's set of statements, with a given extractor, at the numbers' list of errors; and one on
honest-verifier zero knowledge.

Limits: this file says nothing on the batch (Ω then bears one shared test and one for each slot),
and nothing on plans with a splitting.
The rule on sums of positions follows this protocol's technical report, which follows a proof of the
paper that this protocol builds on; the numbers asked of the senders follow that report's theorem on
linear constraints, which follows Brakedown (GLSTW23), TensorSwitch (BFRW25) and that paper
(lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinCloseLinProofs
import Cb.Ld.LdLinClosePlanProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The bound after one more test. -/
def LdRunD.need {E : Type} [Field E] [Fintype E] {S : Sig E}
    (D : LdRunD S) (b' : (S.sub D.kp).O → ℕ) : S.O → ℕ :=
  fun o => (if D.G.mem o then D.t else 0) + (if h : D.kp o then b' ⟨o, h⟩ else 0)

/-- The tests of the plan without a splitting: the data. -/
structure LdLinPlT {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype Y] [Fintype κ] [Fintype J]
    {C : LdLinC E ι κ J Y} (p : LdLinPl C) where
  [ne₁ : Nonempty p.G₁.P]
  hc₁ : ∀ o, p.G₁.mem o ∨ p.kp₁ o
  Z₁  : Evader E (p.G₁.Row C.B₁)
  T₁  : LdEnd (p.G₁.joint (fun _ => C.Sh6) p.sl₁ Z₁)
  L₁  : ℕ
  t₁  : ℕ
  [ne₂ : Nonempty p.G₂.P]
  hc₂ : ∀ o, p.G₂.mem o ∨ p.kp₂ o
  Z₂  : Evader E (p.G₂.Row LinB₂)
  T₂  : LdEnd (p.G₂.joint (fun _ => C.St6) p.sl₂ Z₂)
  L₂  : ℕ
  t₂  : ℕ
  /-- the closing of what is left, and how its explicit part is made -/
  Q'  : LdTc p.S₂ C.E₀ C.Wpa
  fa  : C.Sta → Q'.St
  /-- values of the extractors where nothing was output -/
  d₁  : C.S.Wit × C.Wpa
  d₁' : LdBrW p.G₁ p.kp₁ C.Wpa
  d₂  : p.S₁.Wit × C.Wpa
  d₂' : LdBrW p.G₂ p.kp₂ C.Wpa

namespace LdLinPlT
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype Y] [Fintype κ] [Fintype J]
  {C : LdLinC E ι κ J Y} {p : LdLinPl C} (T : LdLinPlT p)

@[reducible] def D₁ : LdRunD C.S :=
  { G := p.G₁, neP := T.ne₁, kp := p.kp₁, hc := T.hc₁, B := C.B₁, Sb := fun _ => C.Sh6, sl := p.sl₁,
    Z := T.Z₁, T := T.T₁, L := T.L₁, t := T.t₁ }
@[reducible] def D₂ : LdRunD p.S₁ :=
  { G := p.G₂, neP := T.ne₂, kp := p.kp₂, hc := T.hc₂, B := LinB₂, Sb := fun _ => C.St6,
    sl := p.sl₂, Z := T.Z₂, T := T.T₂, L := T.L₂, t := T.t₂ }

/-- The first test, then the second, then the closing of what is left. -/
def Q : LdTc C.S C.E₀ C.Wpa :=
  LdTc.cons T.D₁ (LdTc.cons T.D₂ T.Q' T.d₂ T.d₂') T.d₁ T.d₁'

/-- the explicit part -/
def fq : C.St6 → T.Q.St := C.fq T.fa

end LdLinPlT

namespace Spec

def ldDemand_nil : Prop :=
  ∀ (E : Type) [Field E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (w₀ : S.Wit × Wp)
      (q₀ : Finset E₀.Pos → Prop) (b : S.O → ℕ),
    q₀ ∅ → ∀ V, (LdTc.nil S E₀ Wp w₀).q V → S.qFam q₀ b V

/-- The rule. States: if Q needs at most b' and q₀, then `LdTc.cons D Q d d'` needs at most
`D.need b'` and q₀. -/
def ldDemand_cons : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (D : LdRunD S)
      (Q : LdTc (S.sub D.kp) E₀ Wp) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp)
      (q₀ : Finset E₀.Pos → Prop) (b' : (S.sub D.kp).O → ℕ),
    (∀ V, Q.q V → (S.sub D.kp).qFam q₀ b' V) →
    ∀ V, (LdTc.cons D Q d d').q V → S.qFam q₀ (D.need b') V

def ldDemand_le : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (D : LdRunD S) (b' : (S.sub D.kp).O → ℕ) (o : S.O),
    D.need b' o ≤ D.t + (if h : D.kp o then b' ⟨o, h⟩ else 0)

section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

open Classical in
/-- Through the re-bracketing. -/
def ldDemand_lin : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (Sn : C.P.Snd) (qa : Finset C.P.Ea.Pos → Prop)
      (q₀ : Finset C.E₀.Pos → Prop) (ba : C.Sa.O → ℕ) (b : C.S.O → ℕ),
    (∀ W, C.Sa.qFam q₀ ba W → qa W) → (∀ a, b (.inl (.inl (.inl a))) ≤ ba a) →
    (∀ a, b (.inl (.inl (.inr a))) ≤ Sn.tW a) → (∀ a, b (.inl (.inr a)) ≤ Sn.tU a) →
    (∀ a, b (.inr a) ≤ Sn.tO a) → ∀ V, C.S.qFam q₀ b V → C.P.q5 Sn qa (V.biUnion C.toE.src)

open Classical in
/-- The demand of the plan. -/
def ldDemand_plan : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPl C) (T : LdLinPlT p) (Sn : C.P.Snd)
      (qa : Finset C.P.Ea.Pos → Prop) (q₀ : Finset C.E₀.Pos → Prop)
      (ba : C.Sa.O → ℕ) (b' : p.S₂.O → ℕ),
    (∀ V, T.Q'.q V → p.S₂.qFam q₀ b' V) → (∀ W, C.Sa.qFam q₀ ba W → qa W) →
    (∀ a, T.D₁.need (T.D₂.need b') (.inl (.inl (.inl a))) ≤ ba a) →
    (∀ a, T.D₁.need (T.D₂.need b') (.inl (.inl (.inr a))) ≤ Sn.tW a) →
    (∀ a, T.D₁.need (T.D₂.need b') (.inl (.inr a)) ≤ Sn.tU a) →
    (∀ a, T.D₁.need (T.D₂.need b') (.inr a) ≤ Sn.tO a) →
    ∀ V, T.Q.q V → C.P.q5 Sn qa (V.biUnion C.toE.src)

/-- In plain numbers: an oracle message of which the closing of what is left needs at most c bears
at most t₁ + t₂ + c. -/
def ldDemand_plain : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPl C) (T : LdLinPlT p) (b' : p.S₂.O → ℕ) (o : C.S.O) (c : ℕ),
    (∀ h₁ h₂, b' ⟨⟨o, h₁⟩, h₂⟩ ≤ c) → T.D₁.need (T.D₂.need b') o ≤ T.t₁ + T.t₂ + c

/-- States, for ι nonempty and under the hypotheses below: the test with the closing of the plan is
a tail. -/
def ldLinPlan_tail : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPl C) (T : LdLinPlT p)
      (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (Sn : C.P.Snd)
      (qa : Finset C.P.Ea.Pos → Prop) (d : C.P.W0) (q₀ : Finset C.E₀.Pos → Prop)
      (ba : C.Sa.O → ℕ) (b' : p.S₂.O → ℕ),
    C.P.FoldErr on0 εf → Function.Injective C.P.D.py → Sn.OK →
    (∀ sa m, p.restG.val sa (p.G₂.msg (C.S.res (T := OMsg.Msg) p.kp₁ m)) = C.rest sa (C.aM m)) →
    p.SaysA T.Q'.base T.fa → T.D₁.OK → T.D₂.OK → T.Q'.OK → (∀ V, T.Q'.q V → p.S₂.qFam q₀ b' V) →
    (∀ W, C.Sa.qFam q₀ ba W → qa W) →
    (∀ a, T.D₁.need (T.D₂.need b') (.inl (.inl (.inl a))) ≤ ba a) →
    (∀ a, T.D₁.need (T.D₂.need b') (.inl (.inl (.inr a))) ≤ Sn.tW a) →
    (∀ a, T.D₁.need (T.D₂.need b') (.inl (.inr a)) ≤ Sn.tU a) →
    (∀ a, T.D₁.need (T.D₂.need b') (.inr a) ≤ Sn.tO a) →
    TailTr (C.P.linC on0 Sn εf (C.cZ T.Q T.fq) d).R (C.P.linC on0 Sn εf (C.cZ T.Q T.fq) d).H
      (C.P.j0 on0) trivRels (C.P.linC on0 Sn εf (C.cZ T.Q T.fq) d).ext
      (C.P.linC on0 Sn εf (C.cZ T.Q T.fq) d).P (C.P.q0 qa)

end
end Spec
end Cb
