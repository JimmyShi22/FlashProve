-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/KnowCollRulesMask.lean: honest-verifier zero knowledge of a chain whose masks are sent in
advance.

The matter is sequential composition of interactive oracle reductions (IORs, Ior/Ior.lean).
Definitions and statements; the proofs are in Ior/KnowCollRulesMaskProofs.lean. No protocol, no
code occurs here.
A block is an IOR with its honest side H (`IOR.Honest`, Ior/Honest.lean), taken as a part of a
chain. A prefix is all of a chain that comes before a given block, as one IOR with its honest side.
A link is here an IOR with its honest side, as a step of a chain (as a record with extractor and
numbers: `IOR.Link`, Ior/KnowCollRulesChain.lean).
`GoodT`: Ior/KnowCollGood.lean. `GoodM`: Ior/Masked.lean.
`H.withheld w x` is the union of two sets of verifier randomness that the honest side names:
`H.Bad`, which takes no argument, and `H.Hid w x`, which takes the witness and the explicit
statement.

Why: a block may hide what it sends in the clear by mask entries that stand in an oracle sent
earlier (Ior/Masked.lean: the masks stand in the block's input witness; the block has the item
"masked messages", `H.MM D`, and not the field `exact`; that `exact` fails of it: under the
premises of `Spec.masked_not_exact`). Zero knowledge is then a property of a chain that also holds
the round in which the masks are sent. Between that round and the block the chain shows things that
depend on the masks: symbols of the oracle that holds them, and the answers to a sample of that
oracle. So the masks are not "fresh coins" of the block, and the rule for chains
(Ior/ExactSeq.lean) does not apply.
The answer, as a rule for prefixes: "a prefix of the chain; then the masked block".

Main names:
  `H.Fresh Ri bud kc Mk put`: a property of the honest side H of the prefix. kc: what the coming
    block reads of the witness that the prefix hands on; put M k: k with the block's own mask
    entries overwritten by M. It says: on every triple of Ri, at every ρ that is not withheld, for
    every set T of further positions within the budget, the triple (what the run shows at T, the
    explicit part handed on, kc of the witness handed on) has the same law, over the prefix's
    coins, as the triple in which the own mask entries are overwritten by fresh uniform ones. In
    words (the reading meant of `kc`, `put`; by type any maps `Wo → Kc`, `Mk → Kc → Kc`): given all
    that the prefix shows, the block's own masks are still uniform, and independent of the rest of
    what the block reads.
  `Spec.exact_seq_masked`, under the hypotheses of its statement: a prefix that is honest-verifier
    zero knowledge in the exact form (`Honest.ExactWith`, Ior/Honest.lean) and Fresh for the
    block's masks, then a block with the item "masked messages": the whole is honest-verifier
    zero knowledge in the exact form, with no new error. The simulator is named: the rule for
    chains' simulator (`IOR.simSeq`) on the prefix's simulator and the block's (`D.simOwn`). The
    budget: that of the rule for chains; the block has no oracle, so nothing is asked for it. Two
    hypotheses of the statement: `R₁.IsLocal` (Ior/Ior.lean: see its docstring), and "the relation
    implies the claim": `∀ x y w, Rb x y w → D.Cl (D.pub x) (D.kc w)`.
  `Spec.goodT_seq_masked`: the same for the bundles: `GoodT`, Fresh, then `GoodM`, is `GoodT`.
    Errors in a row, probabilities added, extractors composed.

How `Fresh` is had (Mk non-empty):
  `Spec.fresh_snd`, under `H₁.Acc Ra Rb`: the part that sends the masks comes last: if the second
    part is Fresh on all its inputs, so is the whole, whatever the first part is.
  `H.Blind kci kco Mk puti puto`: a link that does not look at these masks: if what is read of two
    input witnesses differs by an overwriting of the masks, then, with the same explicit part,
    coins and verifier messages, the link sends the same messages, ends with the same explicit
    part, and what is read of the two output witnesses differs by the same overwriting.
  `Spec.fresh_seq`: Fresh is carried through a link that is Blind. The link may be of any kind:
    with the field `exact`, or itself a masked block with other masks.
  `Spec.fresh_conseq`: a smaller relation, a smaller budget, a coarser reading. (not all hypotheses
    are named here: see its statement)
  `Spec.blind_carry`: a link whose honest prover only hands a part of the witness on
    (Ior/Frame.lean: `H.carry`) is Blind for masks that stand in that part.

Why this route: the written lemma warns that a forward replacement is wrong (an earlier block's
values simulated, its inner masks real: the next block's honest message fails its check), goes
backwards through the chain, and has a second route by reordering.
(Which text is meant: see the last sentences of this head.)
The rule here is neither, and the warning does not hit it: no honest block is ever run after a
simulated prefix.
The block's law is taken given the real prefix, and the prefix's law is replaced last.
This rule carries the theorem; Ior/Masked.lean's "the same block with the masks as its coins"
(`exact_own`) is a piece of the second route and is not used by it.

Under the hypotheses of `Spec.mm_seq`, `Spec.goodM_seq` (among them `MaskLink.OK`) and
`Spec.mm_silent`, a sub-protocol all of whose masks stand in its input (a chain of masked blocks
and of blocks without prover message) is itself a masked block (stated for two in a row, and for
one block without prover message): Ior/KnowCollRulesMaskSeq.lean. The flat statement for any number
of links: Ior/KnowCollRulesChain.lean (`chain_ok`).

How a chain is treated: it is bracketed to the left: ((first; second); third) .. Each masked block
B has its own Fresh, which starts at the part that sends B's masks (`fresh_snd`), goes through
every link up to B (`fresh_seq`), and is used up at B (`goodT_seq_masked`). Links with the field
`exact` are added by the rule for chains (`Spec.goodT_seq`).

What the conditions of the written lemma become (each condition in this file's own words):
"The masks of different blocks are disjoint, none is a pad; masks, pads and encoding randomness are
uniform": a matter of the part that sends them: it has to be Fresh for each block's (kc, put). For
that, kc must forget the pad and the encoding randomness of the oracle that holds the masks: with
the pad in view, the answers to the sample tell a functional of the masks.
"Before the block no prover message but that oracle and the answers to its sample depends on the
block's masks, that oracle's pad or its encoding randomness": every link in between is Blind. In
particular no proximity test on that oracle comes before the block: its prover reads the encoding
randomness, so it is not Blind for a kc that forgets it [no theorem here].
"Every oracle is read no more often than its encoding bears": the budget. The errors of the written
lemma are the probabilities `pHid` of the bundles, which add.

Limits: this file says nothing for chains that are bracketed otherwise: a masked block together
with a proximity test that follows it is no unit with a property of its own here.
That the simulator is "uniform-query" and runs its distinguisher once, which the written lemma
makes part of every such item, has no counterpart in the exact form.
No part that is Fresh is exhibited here (a small case: Ior/KnowCollRulesMaskTest.lean).
This file says nothing on classes of distinguishers: our exact form has sets of further
positions instead (Ior/Honest.lean says why).
It says nothing on running times. "uniform-query": a term of the paper that this protocol builds on.
The lemma follows this protocol's technical report (lean/CREDITS.md), which follows the paper that
this protocol builds on. "The written lemma" is its form in a write-up of ours; its proof there goes
backwards through the chain, the proof here goes forwards, prefix by prefix.
Terms: lean/GLOSSARY.md: budget, bundle, chain, extractor, fresh, honest side, mask,
numbers (of a reduction), pad, sample, withheld, zero knowledge.
-/
import Ior.Masked
import Ior.Frame
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR
variable {K Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type}

namespace Honest
variable {R : IOR Xi Ei Xo Eo}

/-- What a run shows at the further positions T, the explicit part with which the honest prover
ends, and what is read (kc) of the witness with which it ends. -/
def seen (H : R.Honest Wi Wo) {Kc : Type} (kc : Wo → Kc) (w : Wi) (x : Xi)
    (ρ : Rho R.shape) (T : Finset (OPos R.shape)) (c : H.Coin) : View R × Xo × Kc :=
  (R.view T ((H.strat w x c).run ρ).1, ((H.strat w x c).run ρ).2.1, kc ((H.strat w x c).run ρ).2.2)

/-- For a non-empty `Mk`: on every triple of Ri, at every ρ that is not withheld, for every set T
of further positions within the budget, the triple (what the run shows at T, the explicit part
handed on, kc of the witness handed on) has the same law, over the prefix's coins, as the triple in
which the own mask entries are overwritten by fresh uniform ones. (see Ior/MaskControls.lean,
"where `Fresh` alone says nothing") -/
def Fresh (H : R.Honest Wi Wo) (Ri : Xi → Ei.Str → Wi → Prop)
    (bud : Rho R.shape → Finset (OPos R.shape) → Prop) {Kc : Type} (kc : Wo → Kc) (Mk : Type)
    [Fintype Mk] [Nonempty Mk] (put : Mk → Kc → Kc) : Prop :=
  ∀ x y w, Ri x y w →
    ∀ ρ, ρ ∉ H.withheld w x →
      ∀ T, bud ρ T →
        (unif (H.Coin × Mk)).map (fun a =>
            ((H.seen kc w x ρ T a.1).1,
              (H.seen kc w x ρ T a.1).2.1,
              put a.2 (H.seen kc w x ρ T a.1).2.2)) =
          (unif H.Coin).map (H.seen kc w x ρ T)

/-- A link that does not look at the masks. -/
def Blind (H : R.Honest Wi Wo) {Ki Ko : Type} (kci : Wi → Ki) (kco : Wo → Ko) (Mk : Type)
    (puti : Mk → Ki → Ki) (puto : Mk → Ko → Ko) : Prop :=
  ∀ (w w' : Wi) (M : Mk) (x : Xi) (c : H.Coin) (ρ : Rho R.shape), kci w' = puti M (kci w) →
    ((H.strat w' x c).run ρ).1 = ((H.strat w x c).run ρ).1 ∧
    ((H.strat w' x c).run ρ).2.1 = ((H.strat w x c).run ρ).2.1 ∧
    kco ((H.strat w' x c).run ρ).2.2 = puto M (kco ((H.strat w x c).run ρ).2.2)

end Honest
end IOR

namespace Spec
open IOR

/-- A prefix that is honest-verifier zero knowledge and fresh, then a masked block: honest-verifier
zero knowledge, with the simulator named. (not all hypotheses are named here: see the statement
below) -/
def exact_seq_masked : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (Ra : X₁ → E₁.Str → W₁ → Prop)
      (Rb : X₂ → E₂.Str → W₂ → Prop) (b₁ : Rho R₁.shape → Finset (OPos R₁.shape) → Prop)
      (S₁ : Honest.Sim R₁) (D : MaskData R₂ W₂) (m : H₂.MM D),
    R₁.IsLocal → H₁.Acc Ra Rb → H₁.ExactWith Ra b₁ S₁ → H₁.Fresh Ra b₁ D.kc D.Mk D.put →
    (∀ x y w, Rb x y w → D.Cl (D.pub x) (D.kc w)) →
    (H₁.seq H₂).ExactWith Ra (budSeq R₁ R₂ b₁ fun _ _ => True) (simSeq S₁ (D.simOwn m.noOrc))

/-- The same for the bundles. -/
def goodT_seq_masked : Prop :=
  ∀ (K X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (A : Rels K X₁ E₁ W₁)
      (B : Rels K X₂ E₂ W₂) (C : Rels K X₃ E₃ W₃)
      (e₁ : X₁ × E₁.Str → Tr R₁.shape → W₂ → W₁) (e₂ : X₂ × E₂.Str → Tr R₂.shape → W₃ → W₂)
      (d : W₁) (P₁ : Nums K R₁) (P₂ : Nums K R₂) (D : MaskData R₂ W₂),
    GoodT R₁ H₁ A B e₁ P₁ → H₁.Fresh A.rel P₁.bud D.kc D.Mk D.put → GoodM R₂ H₂ B C e₂ P₂ D →
    GoodT (R₁.seq R₂) (H₁.seq H₂) A C (IOR.extSeq R₁ R₂ e₁ e₂ d) (P₁.seq P₂)

/-- The part that sends the masks comes last. -/
def fresh_snd : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (Ra : X₁ → E₁.Str → W₁ → Prop)
      (Rb : X₂ → E₂.Str → W₂ → Prop) (b₁ : Rho R₁.shape → Finset (OPos R₁.shape) → Prop)
      (b₂ : Rho R₂.shape → Finset (OPos R₂.shape) → Prop) (Kc : Type) (kc : W₃ → Kc) (Mk : Type)
      [Fintype Mk] [Nonempty Mk] (put : Mk → Kc → Kc),
    H₁.Acc Ra Rb → H₂.Fresh Rb b₂ kc Mk put → (H₁.seq H₂).Fresh Ra (budSeq R₁ R₂ b₁ b₂) kc Mk put

/-- States: Fresh is carried through a link that does not look at the masks. -/
def fresh_seq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (Ra : X₁ → E₁.Str → W₁ → Prop)
      (b₁ : Rho R₁.shape → Finset (OPos R₁.shape) → Prop)
      (b₂ : Rho R₂.shape → Finset (OPos R₂.shape) → Prop) (K₂ K₃ : Type) (kc₂ : W₂ → K₂)
      (kc₃ : W₃ → K₃) (Mk : Type) [Fintype Mk] [Nonempty Mk] (put₂ : Mk → K₂ → K₂)
      (put₃ : Mk → K₃ → K₃),
    H₁.Fresh Ra b₁ kc₂ Mk put₂ → H₂.Blind kc₂ kc₃ Mk put₂ put₃ →
    (H₁.seq H₂).Fresh Ra (budSeq R₁ R₂ b₁ b₂) kc₃ Mk put₃

/-- A smaller relation, a smaller budget, a coarser reading (g, which commutes with the
overwriting). (not all hypotheses are named here: see the statement below) -/
def fresh_conseq : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (Ri Ri' : Xi → Ei.Str → Wi → Prop) (bud bud' : Rho R.shape → Finset (OPos R.shape) → Prop)
      (Kc Kc' : Type) (kc : Wo → Kc) (g : Kc → Kc') (Mk : Type) [Fintype Mk] [Nonempty Mk]
      (put : Mk → Kc → Kc) (put' : Mk → Kc' → Kc'),
    (∀ x y w, Ri' x y w → Ri x y w) → (∀ ρ T, bud' ρ T → bud ρ T) →
    (∀ M k, g (put M k) = put' M (g k)) → H.Fresh Ri bud kc Mk put →
    H.Fresh Ri' bud' (fun w => g (kc w)) Mk put'

/-- States: a link whose honest prover only hands a part of the witness on is blind for masks in
that part. kz: what is read of that part; the rest of the witness may be read in full. -/
def blind_carry : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo Wz : Type) (H : R.Honest Wi Wo)
      (Kz : Type) (kz : Wz → Kz) (Mk : Type) (put : Mk → Kz → Kz),
    (H.carry Wz).Blind (fun w : Wi × Wz => (w.1, kz w.2)) (fun w : Wo × Wz => (w.1, kz w.2)) Mk
      (fun M k => (k.1, put M k.2)) (fun M k => (k.1, put M k.2))

end Spec
end Iop
