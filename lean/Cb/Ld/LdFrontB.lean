-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdFrontB.lean: several statements proved in one batch: the links of a front.

In standard terms: a batch protocol proves up to N statements in one run. This file takes the
reductions before the last proximity tests of a protocol, in which linear claims are combined or
split and no oracle is sent or tested. It marks their rounds as local (the verifier message is drawn
for each statement apart) or shared (once for all), and states, under the hypotheses of its
statement, round-by-round knowledge soundness for batches whose statements agree on a function of
statement and oracles, the key.

Definitions and statements; the proofs are in Cb/Ld/LdFrontBProofs.lean. Generic: no protocol.
A front `p : Front x y` (Cb/Ld/LdFront.lean; here of core type `Unit`) is a list of moves (steps
without rounds, batchings, splittings) over one signature. `LdTc.frontC p`
(Cb/Ld/LdLinCloseAlt.lean) is the chain of its links, after the link that does nothing. An annotated
link (`LinkA`, Cb/Ld/LdLinChainB.lean) is a link with an annotation of its rounds (`RoundSplits`,
Iop/Batch.lean) and a list of errors.

Why: a closing step of a batch is either the instances' own (each slot runs it in local rounds;
`l.lo`, Cb/Ld/LdBatchBlocksPlan.lean) or shared (run once, by the shared part, under shared verifier
messages; `l.sh`, Cb/Ld/LdSplitV.lean). So there is one switch, sh, for a whole front.

Main names:
  `p.cA sh`: the front's links with annotations and errors (a `ChainA`, Cb/Ld/LdLinChainB.lean).
  `Spec.frontB_forget`: its links are the front's (`LdTc.frontC p`). This is the hypothesis hF of
    `LdTcA.front` (Cb/Ld/LdAltB.lean).
  `Spec.frontB_coh`: its annotations are coherent (`ChainA.Coh`, Cb/Ld/LdLinBData.lean).
  `p.Keys sh N kx ky`: keys along the front (`JKey`, Cb/Ld/LdLinChainB.lean: what the statements of
    one batch have in common at each stage).
  `Spec.frontB_kb`: the front's knowledge soundness for the vectors with one key, under the
    hypotheses of its statement.

Limits: this file says nothing on the honest side. All of `KnowB`'s content hangs on which vectors
are admissible (the head of Ior/BatchSeq.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdAltB
import Cb.Ld.LdSplitV
import Cb.Ld.LdFrontProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace Front
variable {E : Type} [Field E] [Fintype E] {S : Sig E} {E₀ : ExtSpec} {Wp : Type}

/-- a link, in every slot or once by the shared part -/
def md {A B : Joint Unit} (sh : Bool) (l : Link Unit A B) : LinkA Unit A B :=
  if sh then l.sh else l.lo

/-- the link of a step without rounds -/
def stepL (y z : FSt S E₀ Wp Unit) (f : y.stage.X → Option z.stage.X)
    (g : ExtMap y.stage.Ex z.stage.Ex) (m : y.stage.X × y.stage.W → z.stage.X × z.stage.W)
    (back : y.stage.X × y.stage.Ex.Str → z.stage.W → y.stage.W) : Link Unit y.stage.J z.stage.J :=
  ⟨IOR.pure f g, IOR.Honest.pure f g m, fun a _ w => back a w, IOR.Nums.pure Unit f g⟩

/-- The front's links for a batch. The link that does nothing and the steps without rounds have no
round, so nothing to annotate. Errors: those for one instance. -/
def cA (sh : Bool) :
    {x y : FSt S E₀ Wp Unit} → Front x y → ChainA Unit x.stage.J y.stage.J
  | _, _, .nil x => .one x.stage.idLink.lo
  | _, _, .step (y := y) p z f g m back => (cA sh p).snoc (stepL y z f g m back).lo
  | _, _, .bat B iB Sb sl Z St₀ A₀ p => (cA sh p).snoc (md sh (batD B iB Sb sl Z St₀ A₀).link)
  | _, _, .split G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs p =>
    (cA sh p).snoc (md sh (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).link)

/-- Keys along the front. There is some key at every stage between, such that after the link that
does nothing, after a step and after a splitting in every slot the new key is a function of the old
one; after a splitting by the shared part it is a function of the old key and the transcript (the
scalar said is one for all slots); the annotated link of a batching is knowledge sound between the
two keys. This last is asked, not derived: its error need not be 0, so a shared run needs that what
acts is a function of the key. For a splitting it is derived: the splitting's link is then knowledge
sound both ways, under its own hypotheses (`Spec.ldSplV_lo_kb`, `Spec.ldSplV_sh_kb`,
Cb/Ld/LdSplitV.lean). -/
def Keys (sh : Bool) (N : ℕ) :
    {x y : FSt S E₀ Wp Unit} → Front x y → JKey x.stage.J → JKey y.stage.J → Prop
  | _, _, .nil _, kx, ky => ∃ F : kx.κ → ky.κ, ∀ a, ky.key a = F (kx.key a)
  | _, _, .step (y := y) p z f g m back, kx, kz =>
    ∃ ky : JKey y.stage.J,
      Keys sh N p kx ky ∧
      ∃ F : ky.κ → kz.κ,
        ∀ a τ b, (stepL y z f g m back).R.red.out a τ = some b → kz.key b = F (ky.key a)
  | _, _, .bat B iB Sb sl Z St₀ A₀ p, kx, kz =>
    ∃ ky, Keys sh N p kx ky ∧ (md sh (batD B iB Sb sl Z St₀ A₀).link).KB N ky kz
  | _, _, .split G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs p, kx, kz =>
    ∃ ky,
      Keys sh N p kx ky ∧
      ∃ F : ky.κ → Tr (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).link.R.shape → kz.κ,
        (sh = false → ∀ κ' τ τ', F κ' τ = F κ' τ') ∧
        ∀ a τ b, (splD G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs).link.R.red.out a τ = some b →
          kz.key b = F (ky.key a) τ

end Front

namespace Spec

def frontB_forget : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (x y : FSt S E₀ Wp Unit)
      (p : Front x y) (sh : Bool),
    (p.cA sh).forget = LdTc.frontC p

def frontB_coh : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (x y : FSt S E₀ Wp Unit)
      (p : Front x y) (sh : Bool),
    (p.cA sh).Coh

/-- States: the moves' own hypotheses (`p.prog.Hyp`) and `p.Keys sh N kx ky` ⇒
`(p.cA sh).KB N kx ky`: the front is knowledge sound for the vectors with one key. -/
def frontB_kb : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type) (x y : FSt S E₀ Wp Unit)
      (p : Front x y) (sh : Bool) (N : ℕ) (kx : JKey x.stage.J) (ky : JKey y.stage.J),
    p.prog.Hyp → p.Keys sh N kx ky → (p.cA sh).KB N kx ky

end Spec
end Cb
