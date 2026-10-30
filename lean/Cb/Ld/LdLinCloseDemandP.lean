-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseDemandP.lean: the plan of this protocol's technical report (lean/CREDITS.md): its
three tests, the whole closing as one term, and the test for linear constraints with this closing as
a tail.

Definitions, and statements (each statement a `Prop` in `Cb.Spec`); the proofs are in
Cb/Ld/LdLinCloseDemandPProofs.lean. One instance's chain.
It uses Cb/Ld/LdLinClosePlanP.lean (the plan `p`: one splitting, of the fold's row; two shared
tests; one test of the instance's own; κ is the entry that its field `k₀` names, not the type κ of
the binders), Cb/Ld/LdLinCloseSplit.lean (a front in front of a closing that is in order by itself:
`C.cZf`; the mask entry fresh after the core, from the sender's law), Cb/Ld/LdLinCloseChain.lean,
Cb/Ld/LdLinCloseDemand.lean. G_u, Ω are two of the three named oracle messages that the core sends
(Cb/Ld/LdLin.lean).
A closing `Q : LdTc C.S C.E₀ C.Wpa` (Cb/Ld/LdLinCloseChain.lean) has a first joint `Q.base`, a chain
`Q.c` to the trivial statement and a demand on positions `Q.q`. "Fresh": `FreshFor`,
Ior/KnowCollRulesChain.lean.
In `Spec.ldLinPpT_tail` and `Spec.ldLinPpT_top`, `TailTr` is the conclusion. `TailTr`, a tail of a
chain, asks of a reduction from a joint to a joint whose statements have no oracles the bundle
`IOR.GoodT` and three further clauses, `noHid`, `tied` and `bears`, which Cb/Ld/LdTowerKit.lean
states (through `IOR.Tied`, Ior/Batch.lean, and `IOR.Bears`, Ior/Bears.lean).
`IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its
honest side, between two joints, at given numbers; among its clauses: completeness between the
honest relations, outside sets of verifier randomness whose probabilities further clauses bound by
the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input
joint's set of statements, with a given extractor, at the numbers' list of errors; and one on
honest-verifier zero knowledge.

Main names:
  `LdLinPpT p`: the data; `T.D₁`, `T.D₂`, `T.D₃`: the three tests.
  The whole closing: `C.cZf (p.x₁ ..) T.Q (C.fqP T.fa) T.front`: the step without rounds ; the
    splitting ; a step ; D₁ ; D₂ ; D₃ ; Q'.
  `Spec.ldLinPpT_ok`: `T.Q` is in order, from the three tests' own hypotheses and `Q'.OK`.
  `Spec.ldLinPpT_demand`: under the hypotheses of its statement, its demand is within what the three
    sendings bear, if T.D₁.need (T.D₂.need (T.D₃.need b')) (`need`: Cb/Ld/LdLinCloseDemand.lean) is
    at most ba on what the preamble left, and at most the senders' numbers. A front reads no
    position.
  `Spec.ldLinPpT_tail`: under the hypotheses of its statement (ι nonempty among them), the test with
    this closing is a tail, from the claim on the encoded index to the trivial statement. One
    hypothesis on masks: κ is fresh after the core and the step. (Where κ stands: `p.Plain`.)
  `Spec.ldLinPpT_top`: the same with no hypothesis on a fresh mask, κ riding with Ω: in its place
    the law of Ω's sender for one own mask entry, at a reading Rd that holds what the splitting
    reads. (not all hypotheses are named here: see its statement; ι is nonempty.)
Rounds: the core has nine, the splitting one: the report's ten, at most six of them with a
non-empty verifier message; then the tests'. The steps have no round, no message and read nothing:
they re-bracket the statement.

Limits: this file says nothing on the batch's two sides (Cb/Ld/LdLinClosePlanPB.lean,
Cb/Ld/LdLinClosePlanPV.lean, Cb/Obj/LdObjectPaperBatch.lean). It does not say that the hypotheses
can be met together. No theorem of this library states that the hypotheses of `ldLinPpT_tail` or
`ldLinPpT_top` can be met together. (κ riding with G_u is not covered, and nothing is missing by
that: the report sends the mask holder with Ω, in one prover message.)

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinClosePlanP
import Cb.Ld.LdLinCloseSplitTop
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The data of the three tests: for each of the three groups the zero-evader, the whole test, the
bound on the list, the number of positions; the closing `Q'` of what the preamble left, with `fa`
for its explicit part; `d₁` to `d₃'`: default values for the tests' extractors; the fields `ne₁` to
`ne₃` and `hc₁` to `hc₃` hold proofs. -/
structure LdLinPpT {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype Y] [Fintype κ] [Fintype J]
    {C : LdLinC E ι κ J Y} (p : LdLinPp C) where
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
  [ne₃ : Nonempty p.Gc.P]
  hc₃ : ∀ o, p.Gc.mem o ∨ p.kp₃ o
  Z₃  : Evader E (p.Gc.Row LinB₂)
  T₃  : LdEnd (p.Gc.joint (fun _ => C.St6) p.r₃ Z₃)
  L₃  : ℕ
  t₃  : ℕ
  Q'  : LdTc p.S₃ C.E₀ C.Wpa
  fa  : C.Sta → Q'.St
  d₁  : C.S.Wit × C.Wpa
  d₁' : LdBrW p.GU p.kp₁ C.Wpa
  d₂  : p.S₁.Wit × C.Wpa
  d₂' : LdBrW p.G₂ p.kp₂ C.Wpa
  d₃  : p.S₂.Wit × C.Wpa
  d₃' : LdBrW p.Gc p.kp₃ C.Wpa

namespace LdLinPpT
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype Y] [Fintype κ] [Fintype J]
  {C : LdLinC E ι κ J Y} {p : LdLinPp C} (T : LdLinPpT p)

@[reducible] def D₁ : LdRunD C.S :=
  { G := p.GU, neP := T.ne₁, kp := p.kp₁, hc := T.hc₁, B := C.Brc ⊕ Unit, Sb := fun _ => C.Sh6,
    sl := p.r₁, Z := T.Z₁, T := T.T₁, L := T.L₁, t := T.t₁ }
@[reducible] def D₂ : LdRunD p.S₁ :=
  { G := p.G₂, neP := T.ne₂, kp := p.kp₂, hc := T.hc₂, B := Unit, Sb := fun _ => C.Sh6, sl := p.r₂,
    Z := T.Z₂, T := T.T₂, L := T.L₂, t := T.t₂ }
@[reducible] def D₃ : LdRunD p.S₂ :=
  { G := p.Gc, neP := T.ne₃, kp := p.kp₃, hc := T.hc₃, B := LinB₂, Sb := fun _ => C.St6, sl := p.r₃,
    Z := T.Z₃, T := T.T₃, L := T.L₃, t := T.t₃ }

/-- The three tests, then the closing of what the preamble left. -/
def Q : LdTc C.S C.E₀ C.Wpa :=
  LdTc.cons T.D₁ (LdTc.cons T.D₂ (LdTc.cons T.D₃ T.Q' T.d₃ T.d₃') T.d₂ T.d₂') T.d₁ T.d₁'

/-- the plan's front, down to the first joint of T.Q -/
def front : Front (p.x₁ T.Q'.base) ⟨T.Q.St, T.Q.base⟩ := p.front₁ T.Q'.base

end LdLinPpT

namespace Spec
section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

def ldLinPpT_ok : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPp C) (T : LdLinPpT p),
    T.D₁.OK → T.D₂.OK → T.D₃.OK → T.Q'.OK → T.Q.OK

open Classical in
def ldLinPpT_demand : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPp C) (T : LdLinPpT p) (Sn : C.P.Snd)
      (qa : Finset C.P.Ea.Pos → Prop) (q₀ : Finset C.E₀.Pos → Prop)
      (ba : C.Sa.O → ℕ) (b' : p.S₃.O → ℕ),
    (∀ V, T.Q'.q V → p.S₃.qFam q₀ b' V) → (∀ W, C.Sa.qFam q₀ ba W → qa W) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need b')) (.inl (.inl (.inl a))) ≤ ba a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need b')) (.inl (.inl (.inr a))) ≤ Sn.tW a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need b')) (.inl (.inr a)) ≤ Sn.tU a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need b')) (.inr a) ≤ Sn.tO a) →
    ∀ V, T.Q.q V → C.P.q5 Sn qa (V.biUnion C.toE.src)

/-- States, for ι nonempty and under the hypotheses below: the test with the report's closing
is a tail. Limits: the head. -/
def ldLinPpT_tail : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPp C) (T : LdLinPpT p)
      (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (Sn : C.P.Snd)
      (qa : Finset C.P.Ea.Pos → Prop) (d : C.P.W0) (q₀ : Finset C.E₀.Pos → Prop) (ba : C.Sa.O → ℕ)
      (b' : p.S₃.O → ℕ) (Rd : C.S.Ent → Prop) (Rr : C.S.O → Prop),
    C.P.FoldErr on0 εf → Function.Injective C.P.D.py → Sn.OK →
    (∀ sa m, p.restG.val sa (p.Gc.msg (p.left₂ m)) = C.rest sa (C.aM m)) → p.SaysA T.Q'.base T.fa →
    p.Plain → p.Kept → T.D₁.OK → T.D₂.OK → T.D₃.OK → T.Q'.OK → (∀ n, p.Rs₀ n → Rd n) →
    ((C.P.chain on0 Sn εf).append (C.chain (C.fqP T.fa) (p.x₁ T.Q'.base).A)).FreshFor
      ((p.x₁ T.Q'.base).stage.wideFact Rd Rr (fun n => n = ⟨p.k₀.o, p.k₀.j⟩) E fun u _ => u).kc E
      ((p.x₁ T.Q'.base).stage.wideFact Rd Rr (fun n => n = ⟨p.k₀.o, p.k₀.j⟩) E fun u _ => u).put →
    (∀ V, T.Q'.q V → p.S₃.qFam q₀ b' V) → (∀ W, C.Sa.qFam q₀ ba W → qa W) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need b')) (.inl (.inl (.inl a))) ≤ ba a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need b')) (.inl (.inl (.inr a))) ≤ Sn.tW a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need b')) (.inl (.inr a)) ≤ Sn.tU a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need b')) (.inr a) ≤ Sn.tO a) →
    TailTr (C.P.linC on0 Sn εf (C.cZf (p.x₁ T.Q'.base) T.Q (C.fqP T.fa) T.front) d).R
      (C.P.linC on0 Sn εf (C.cZf (p.x₁ T.Q'.base) T.Q (C.fqP T.fa) T.front) d).H (C.P.j0 on0)
      trivRels (C.P.linC on0 Sn εf (C.cZf (p.x₁ T.Q'.base) T.Q (C.fqP T.fa) T.front) d).ext
      (C.P.linC on0 Sn εf (C.cZf (p.x₁ T.Q'.base) T.Q (C.fqP T.fa) T.front) d).P (C.P.q0 qa)

open Classical in
/-- The same, with the sender's law in place of the fresh mask; κ rides with Ω.
(not all hypotheses are named here: see the statement below; ι is nonempty.) Limits: the head. -/
def ldLinPpT_top : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPp C) (T : LdLinPpT p)
      (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (Sn : C.P.Snd)
      (qa : Finset C.P.Ea.Pos → Prop) (d : C.P.W0) (q₀ : Finset C.E₀.Pos → Prop) (ba : C.Sa.O → ℕ)
      (b' : p.S₃.O → ℕ) (Rd : C.S.Ent → Prop) (n₀ : C.NO.Ent) (U₀ : Sn.dO.Own E),
    C.P.FoldErr on0 εf → Function.Injective C.P.D.py → Sn.OK →
    (∀ sa m, p.restG.val sa (p.Gc.msg (p.left₂ m)) = C.rest sa (C.aM m)) →
    p.SaysA T.Q'.base T.fa → p.Plain → p.Kept → T.D₁.OK → T.D₂.OK → T.D₃.OK → T.Q'.OK →
    (∀ n, p.Rs₀ n → Rd n) → (⟨p.k₀.o, p.k₀.j⟩ : C.S.Ent) = C.eO n₀ → Rd (C.eO n₀) →
    U₀.Laws C.SdO (fun m w' => (C.NO.cut (fun n => Rd (C.eO n)) m, w'))
      (fun u k => (C.NO.ow (fun n => n = n₀) (fun _ => u) k.1, k.2)) →
    (∀ V, T.Q'.q V → p.S₃.qFam q₀ b' V) → (∀ W, C.Sa.qFam q₀ ba W → qa W) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need b')) (.inl (.inl (.inl a))) ≤ ba a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need b')) (.inl (.inl (.inr a))) ≤ Sn.tW a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need b')) (.inl (.inr a)) ≤ Sn.tU a) →
    (∀ a, T.D₁.need (T.D₂.need (T.D₃.need b')) (.inr a) ≤ Sn.tO a) →
    TailTr (C.P.linC on0 Sn εf (C.cZf (p.x₁ T.Q'.base) T.Q (C.fqP T.fa) T.front) d).R
      (C.P.linC on0 Sn εf (C.cZf (p.x₁ T.Q'.base) T.Q (C.fqP T.fa) T.front) d).H (C.P.j0 on0)
      trivRels (C.P.linC on0 Sn εf (C.cZf (p.x₁ T.Q'.base) T.Q (C.fqP T.fa) T.front) d).ext
      (C.P.linC on0 Sn εf (C.cZf (p.x₁ T.Q'.base) T.Q (C.fqP T.fa) T.front) d).P (C.P.q0 qa)

end
end Spec
end Cb
