-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinBHon.lean: the honest side of the test for linear constraints on the encoded index for
at most N instances: the core.

In standard terms: the honest prover's strategies in the batch form of the test, up to its closing:
which part of the prover, a slot or the part shared by all slots, sends each message, and from which
data it computes it.

Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLinBHonProofs.lean. The notions
are those of Ior/LinkV.lean (the honest side of a link of a batch, over any implicit instance),
Ior/LinkVBears.lean (budgets for families of slots) and Cb/Ld/LdLinChainV.lean (all this along a
chain). The links, annotations and errors are those of Cb/Ld/LdLinChainB.lean: `P.chainA`.

Who holds what. A slot holds its whole one-instance witness (Cb/Ld/LdLin.lean: `W0`, `WA`, `W1` ..
`W5`). The shared part of the prover holds (`Sh0` .. `Sh6`):
  at the start: the encoded index as sent, the full messages M of its rows, and the index's record
    (the prover encoded index is kept with its record: all slots of a batch have one record);
  after ψ*: also ψ*;
  after G_u's family: also that family's samples, words as sent, messages and encoding randomness;
  after the locations: also the locations and the folds read;
  after Ω's family: also that family's samples, words, messages and randomness; after ζ: also ζ.
The tie at a joint says that the slot's statement and witness hold the same; in particular, at
every joint, that the slot's record is the shared one. No strategy reads the record.

Who speaks. `step0`, `sW`: each slot for itself (`H.localV`). `pt`, `loc`, `zeta`: nobody. `sU`,
`sO`: the shared part alone (`H.sharedV s0`): its strategies `sU0`, `sO0` are functions of what it
holds, its own coins and the shared verifier messages, by type: it folds M at γ, resp. forms
ω = (index matrix)·eq(ψ*, ·), and runs the family's sender on that vector. That this is what the
one-instance prover of every slot sends is where `S.Apart` enters (Cb/Ld/LdLinChainFresh.lean: the
messages of G_u's family are made from u and coins alone, those of Ω's from ω and coins alone).

What may still be read, through all slots (`qv0` .. `qv5`: demands on families of sets of
positions). Of what a slot owns (the oracles left, the members of its family NW): each slot's set
within the one-instance demand. Of what is shared: the union over the slots: at most t positions of
the encoded index; at most tU a long positions of the member a of G_u's family, tO a of Ω's. So an
oracle message that lies in one shared test and in a test of each of N slots has to bear the
positions of all 1 + N tests.

Main names:
  In all statements but `Spec.ldLinV_her` ι, the set of positions of the encoded index, is nonempty.
  `Spec.ldLinV_her`: the demands are kept by subsets of the set of slots.
  `Spec.ldLinV_forget`: the chain's links with annotations are those of the batch's knowledge
    soundness (`P.chainA`).
  `Spec.ldLinV_pv`: under `P.FoldErr on0 εf`, an injective `P.D.py`, `S.OK`, `S.Apart` and a value
    of `P.Ea.Str` (ya under Limits): each of the seven links is a piece: local, complete for each
    slot, exactly honest-verifier zero knowledge for sets of slots at its budget (`PieceV.exact`:
    `HonestV.ExactV`, Ior/LinkV.lean), bears what follows.
  `Spec.ldLinV_core`: under the hypotheses of `Spec.ldLinV_pv`: all links of `P.chainV` are pieces.

Why: a slot holds its whole one-instance witness, so also the messages and the encoding randomness
of G_u's and Ω's families, tied to the shared part's. (A slot's own test on Ω needs them.) So an
instance's later messages may depend on the shared part's coins. This protocol's technical report
(lean/CREDITS.md) says the same: an instance's messages may depend on the shared messages and on the
randomness from which the prover encodes them.

Notation: `N`: the number of slots; `qa`: a predicate on finite sets of positions of the oracles
left (`P.Ea`); `on0`: a condition on the encoded index and its record; `εf`: the number in
`P.FoldErr on0 εf`; `γ`: the first part of the shared point ψ* = (γ, ψlo); `u`: the fold of M at γ.

Limits: this file says nothing on a closing. Masked links are no pieces (Ior/LinkVMasked.lean). It
says nothing on soundness. ya: a fixed value of the oracles left, and the formats' fixed symbols,
fill the places of which nothing is ever given to a simulator.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinChainV
import Cb.Ld.LdLinChainFresh
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
namespace IOR

/-- the budget of a run in every slot: each slot's further positions -/
def budEach {X X' : Type} {Ei Eo : ExtSpec} (R : IOR X Ei X' Eo) (N : ℕ)
    (bud : Rho R.shape → Finset (OPos R.shape) → Prop) : BudB R.shape N :=
  fun J ρs Ts => ∀ j : J, bud (ρs j) (Ts j)

open Classical in
/-- the budget of a run by the shared part alone: the union of the slots' further positions -/
def budUnion {X X' : Type} {Ei Eo : ExtSpec} (R : IOR X Ei X' Eo) (N : ℕ)
    (bud : Rho R.shape → Finset (OPos R.shape) → Prop) : BudB R.shape N :=
  fun J ρs Ts => ∀ j : J, bud (ρs j) (Finset.univ.biUnion Ts)

end IOR
end Iop

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace LdLinP
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
  [Fintype Y] (P : LdLinP E ι κ J Y)

/-! ### What the shared part holds -/

abbrev Sh0 : Type := ((ι → P.Sy) × P.IxW) × P.D.X.Rec
abbrev Sh2 : Type := P.Sh0 × P.D.Pt
abbrev Sh3 : Type := P.Sh2 × (P.NU.Smp × P.NU.ext.Str × P.NU.Wit)
abbrev Sh4 : Type := P.Sh3 × P.Loc
abbrev Sh5 : Type := P.Sh4 × (P.NO.Smp × P.NO.ext.Str × P.NO.Wit)
abbrev Sh6 : Type := P.Sh5 × (Fin P.D.l → E)

/-! ### What may still be read, through all slots -/

variable (S : P.Snd) (qa : Finset P.Ea.Pos → Prop) (N : ℕ)

def qv0 : QFam P.E0 N := fun _ Us =>
  (∀ T : Finset ι, (∀ i ∈ T, ∃ j, (Sum.inl i : P.E0.Pos) ∈ Us j) → T.card ≤ P.t) ∧
  ∀ j, qa (Us j).toRight
def qv1 : QFam P.E1 N := fun J Us =>
  P.qv0 qa N J (fun j => (Us j).toLeft) ∧
  ∀ j a, cnt (fun x : (P.NW.om a).P => (Sum.inr ⟨a, x⟩ : P.E1.Pos) ∈ Us j) ≤ S.tW a
def qv3 : QFam P.E3 N := fun J Us =>
  P.qv1 S qa N J (fun j => (Us j).toLeft) ∧
  ∀ a, cnt (fun x : (P.NU.om a).P => ∃ j, (Sum.inr ⟨a, x⟩ : P.E3.Pos) ∈ Us j) ≤ S.tU a
def qv4 : QFam P.E4 N := fun _ Us =>
  ((∀ j, qa (Us j).toLeft.toLeft) ∧
    ∀ j a, cnt
        (fun x : (P.NW.om a).P => (Sum.inr ⟨a, x⟩ : (P.Ea.prod P.NW.ext).Pos) ∈ (Us j).toLeft) ≤
      S.tW a) ∧
  ∀ a, cnt (fun x : (P.NU.om a).P => ∃ j, (Sum.inr ⟨a, x⟩ : P.E4.Pos) ∈ Us j) ≤ S.tU a
def qv5 : QFam P.E5 N := fun J Us =>
  P.qv4 S qa N J (fun j => (Us j).toLeft) ∧
  ∀ a, cnt (fun x : (P.NO.om a).P => ∃ j, (Sum.inr ⟨a, x⟩ : P.E5.Pos) ∈ Us j) ≤ S.tO a

/-! ### The joints for a batch

Each `V..` is a triple: what the shared part holds (`Sh..`), the tie, the demand (`qv..`). In a tie
s is what the shared part holds; x, y, w are a slot's explicit statement, oracles and witness. Its
equations stand in this order: the encoded index as sent (up to `V3`: the locations drop it), the
full messages M, the record; from `V2` on ψ*; from `V3` on the samples, the words as sent, and the
messages with the encoding randomness of G_u's family; from `V4` on the locations and the folds
read; from `V5` on the same three of Ω's family; in `V6` ζ. -/

variable (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)

def V0 : JV N (P.J0 on0) :=
  ⟨P.Sh0, fun s (x : P.X0) (y : P.E0.Str) (w : P.W0) => (y.1 = s.1.1 ∧ w.1 = s.1.2) ∧ x.2 = s.2,
    P.qv0 qa N⟩
def VA : JV N (P.JA on0) :=
  ⟨P.Sh0, fun s (x : P.X0) (y : P.E0.Str) (w : P.WA) => (y.1 = s.1.1 ∧ w.2.1 = s.1.2) ∧ x.2 = s.2,
    P.qv0 qa N⟩
def V1 : JV N (P.J1 on0) :=
  ⟨P.Sh0, fun s (x : P.X1) (y : P.E1.Str) (w : P.W1) =>
      (y.1.1 = s.1.1 ∧ w.2.1 = s.1.2) ∧ x.1.2 = s.2,
    P.qv1 S qa N⟩
def V2 : JV N (P.J2 on0) :=
  ⟨P.Sh2, fun s (x : P.X2) (y : P.E1.Str) (w : P.W2) =>
      ((y.1.1 = s.1.1.1 ∧ w.2.2.1 = s.1.1.2) ∧ x.1.1.2 = s.1.2) ∧ x.2 = s.2,
    P.qv1 S qa N⟩
def V3 : JV N (P.J3 on0) :=
  ⟨P.Sh3, fun s (x : P.X3) (y : P.E3.Str) (w : P.W3) =>
      (((y.1.1.1 = s.1.1.1.1 ∧ w.2.2.1 = s.1.1.1.2) ∧ x.1.1.1.2 = s.1.1.2) ∧ x.1.2 = s.1.2) ∧
      x.2 = s.2.1 ∧ y.2 = s.2.2.1 ∧ w.1 = s.2.2.2,
    P.qv3 S qa N⟩
def V4 : JV N P.J4 :=
  ⟨P.Sh4, fun s (x : P.X4) (y : P.E4.Str) (w : P.W4) =>
      (((w.2.2.2.1 = s.1.1.1.1.2 ∧ x.1.1.1.1.2 = s.1.1.1.2) ∧ x.1.1.2 = s.1.1.2) ∧
        x.1.2 = s.1.2.1 ∧ y.2 = s.1.2.2.1 ∧ w.2.1 = s.1.2.2.2) ∧
      x.2 = s.2,
    P.qv4 S qa N⟩
def V5 : JV N P.J5 :=
  ⟨P.Sh5, fun s (x : P.X5) (y : P.E5.Str) (w : P.W5) =>
      ((((w.2.2.2.1 = s.1.1.1.1.1.2 ∧ x.1.1.1.1.1.2 = s.1.1.1.1.2) ∧ x.1.1.1.2 = s.1.1.1.2) ∧
          x.1.1.2 = s.1.1.2.1 ∧
          y.1.2 = s.1.1.2.2.1 ∧
          w.2.1 = s.1.1.2.2.2) ∧
        x.1.2 = s.1.2) ∧
      x.2 = s.2.1 ∧ y.2 = s.2.2.1 ∧ w.1 = s.2.2.2,
    P.qv5 S qa N⟩
def V6 : JV N P.J6 :=
  ⟨P.Sh6, fun s (x : P.X6) (y : P.E5.Str) (w : P.W5) => (P.V5 S qa N).tie s.1 x.1 y w ∧ x.2 = s.2,
    P.qv5 S qa N⟩

/-! ### The shared part's strategies -/

def sPt0 (s : P.Sh0) (_ : Unit) : Strat P.pt.shape P.Sh2 :=
  ((((), ()), fun c => (s, c)) : Strat [drawRound P.D.Pt] P.Sh2)

/-- the witness on which the shared part runs the sender of G_u's family: the fold of M at γ; the
rest is a fixed value, which, under `S.Apart`, the sender's `put` does not read -/
def wU (s : P.Sh2) : P.W2 := (foldAll s.2.1 s.1.1.2, S.dU.w0.2)

def sU0 (s : P.Sh2) (c : S.dU.Mk × S.dU.Nn.Rnd) : Strat P.sU.shape P.Sh3 :=
  (((S.dU.Nn.enc (S.dU.put (P.wU S s) c.1) c.2, ()),
    fun sd =>
      (((), S.dU.ans P.SdU sd (P.wU S s) c.1),
        fun _ =>
          (s, ((fun a => (P.SdU.sd a sd, S.dU.ans P.SdU sd (P.wU S s) c.1 a)),
              S.dU.Nn.enc (S.dU.put (P.wU S s) c.1) c.2,
              fun a =>
                (S.dU.upM (S.dU.put (P.wU S s) c.1) a,
                  S.dU.upR c.2 a))))) : Strat (P.NU.sh P.SdU) P.Sh3)

def sLoc0 (s : P.Sh3) (_ : Unit) : Strat P.loc.shape P.Sh4 :=
  ((((), ()),
    fun Q =>
      (s, (Q, fun i =>
            P.D.X.G.mulVec (foldAll s.1.2.1 s.1.1.1.2)
              (Q i)))) : Strat [drawRound (Fin P.t → ι)] P.Sh4)

def wO (s : P.Sh4) : P.W4 := (P.D.omOf (P.D.X.view s.1.1.1.1.2) s.1.1.2, S.dO.w0.2)

def sO0 (s : P.Sh4) (c : S.dO.Mk × S.dO.Nn.Rnd) : Strat P.sO.shape P.Sh5 :=
  (((S.dO.Nn.enc (S.dO.put (P.wO S s) c.1) c.2, ()),
    fun sd =>
      (((), S.dO.ans P.SdO sd (P.wO S s) c.1),
        fun _ =>
          (s, ((fun a => (P.SdO.sd a sd, S.dO.ans P.SdO sd (P.wO S s) c.1 a)),
              S.dO.Nn.enc (S.dO.put (P.wO S s) c.1) c.2,
              fun a =>
                (S.dO.upM (S.dO.put (P.wO S s) c.1) a,
                  S.dO.upR c.2 a))))) : Strat (P.NO.sh P.SdO) P.Sh5)

def sZeta0 (s : P.Sh5) (_ : Unit) : Strat P.zeta.shape P.Sh6 :=
  ((((), ()), fun c => (s, c)) : Strat [drawRound (Fin P.D.l → E)] P.Sh6)

/-! ### The links, with the honest side of a batch -/

variable (εf : ℕ)

def lv0 : LinkV Unit N (P.V0 qa N on0) (P.VA qa N on0) :=
  ⟨⟨P.lk0 on0, RoundSplits.allLocal _, ()⟩, P.hStep0.localV P.Sh0, budEach P.step0 N (P.lk0 on0).P.bud⟩
def lvW : LinkV Unit N (P.VA qa N on0) (P.V1 S qa N on0) :=
  ⟨⟨P.lkW on0 S, RoundSplits.allLocal _, (ldSendFamNums P.NW P.SdW P.X0 P.E0 Unit S.LW S.tW).err⟩,
    (ldSendFamHon P.SdW P.X0 P.E0 S.dW).localV P.Sh0,
    budEach P.sW N (P.lkW on0 S).P.bud⟩
def lvPt : LinkV Unit N (P.V1 S qa N on0) (P.V2 S qa N on0) :=
  ⟨⟨P.lkPt on0 εf, shAnn _, ((P.errPtB εf N, ()) : ℕ × Unit)⟩,
    P.hPt.sharedV P.sPt0,
    budUnion P.pt N (P.lkPt on0 εf).P.bud⟩
def lvU : LinkV Unit N (P.V2 S qa N on0) (P.V3 S qa N on0) :=
  ⟨⟨P.lkU on0 S, shAnn _, (ldSendFamNums P.NU P.SdU P.X2 P.E1 Unit S.LU S.tU).err⟩,
    (ldSendFamHon P.SdU P.X2 P.E1 S.dU).sharedV (P.sU0 S),
    budUnion P.sU N (P.lkU on0 S).P.bud⟩
def lvLoc : LinkV Unit N (P.V3 S qa N on0) (P.V4 S qa N) :=
  ⟨⟨P.lkLoc on0, shAnn _, ((P.errLoc, ()) : ℕ × Unit)⟩,
    P.hLoc.sharedV P.sLoc0,
    budUnion P.loc N (P.lkLoc on0).P.bud⟩
def lvO : LinkV Unit N (P.V4 S qa N) (P.V5 S qa N) :=
  ⟨⟨P.lkO S, shAnn _, (ldSendFamNums P.NO P.SdO P.X4 P.E4 Unit S.LO S.tO).err⟩,
    (ldSendFamHon P.SdO P.X4 P.E4 S.dO).sharedV (P.sO0 S),
    budUnion P.sO N (P.lkO S).P.bud⟩
def lvZeta : LinkV Unit N (P.V5 S qa N) (P.V6 S qa N) :=
  ⟨⟨P.lkZeta, shAnn _, ((P.errZeta, ()) : ℕ × Unit)⟩,
    P.hZeta.sharedV P.sZeta0,
    budUnion P.zeta N P.lkZeta.P.bud⟩

/-- The core, with the honest side of a batch. -/
def chainV : ChainV Unit N (P.V0 qa N on0) (P.V6 S qa N) :=
  ((((((ChainV.one (P.lv0 qa N on0)).snoc (P.lvW S qa N on0)).snoc (P.lvPt S qa N on0 εf)).snoc
          (P.lvU S qa N on0)).snoc
        (P.lvLoc S qa N on0)).snoc
      (P.lvO S qa N)).snoc
    (P.lvZeta S qa N)

end LdLinP

namespace Spec
section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- The demands are kept by subsets of the set of slots. -/
def ldLinV_her : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (S : P.Snd) (qa : Finset P.Ea.Pos → Prop) (N : ℕ), (P.qv0 qa N).Her ∧
    (P.qv1 S qa N).Her ∧ (P.qv3 S qa N).Her ∧ (P.qv4 S qa N).Her ∧ (P.qv5 S qa N).Her

/-- The chain's links with annotations are those of the batch's knowledge soundness. -/
def ldLinV_forget : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf N : ℕ)
      (S : P.Snd) (qa : Finset P.Ea.Pos → Prop),
    (P.chainV S qa N on0 εf).forget = P.chainA on0 S εf N

/-- For a nonempty ι and under the hypotheses below: each of the seven links is a piece. -/
def ldLinV_pv : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf N : ℕ) (S : P.Snd)
      (qa : Finset P.Ea.Pos → Prop) (_ : P.Ea.Str),
    P.FoldErr on0 εf → Function.Injective P.D.py → S.OK → S.Apart →
    (P.lv0 qa N on0).PV ∧ (P.lvW S qa N on0).PV ∧ (P.lvPt S qa N on0 εf).PV ∧
    (P.lvU S qa N on0).PV ∧ (P.lvLoc S qa N on0).PV ∧ (P.lvO S qa N).PV ∧ (P.lvZeta S qa N).PV

/-- The core, for a nonempty ι and under the hypotheses below: all links are pieces. -/
def ldLinV_core : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf N : ℕ) (S : P.Snd)
      (qa : Finset P.Ea.Pos → Prop) (_ : P.Ea.Str),
    P.FoldErr on0 εf → Function.Injective P.D.py → S.OK → S.Apart → (P.chainV S qa N on0 εf).AllPV

end
end Spec
end Cb
