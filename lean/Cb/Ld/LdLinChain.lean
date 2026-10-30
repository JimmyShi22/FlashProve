-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinChain.lean: the interactive test that an encoded index meets linear constraints, written
as a sequence of interactive oracle reductions whose last part is a parameter, so that its closing
may use masks that the test has sent before.

Definitions, statements (`Cb.Spec.ldLinC_allT` to `Cb.Spec.ldLinC_err`, `Iop.Spec.blind_peek`) and
proofs. The blocks, joints and errors are those of Cb/Ld/LdLin.lean. What differs is only how the
whole is put together.
A joint (`IOR.Joint`, Ior/KnowCollRulesChain.lean) holds the types of explicit part, oracles and
witness, with their relations.
The core's seven blocks, in their order (Cb/Ld/LdLin.lean):
  `step0`: no round; the honest prover computes w = gᵀ·(index matrix) (`wOf`,
    Cb/Ld/LdLinWords.lean).
  `sW`: two rounds; the sending of the family `NW`, whose member `iW` is the oracle message W, which
    holds w.
  `pt`: one round; the verifier's message is the shared point ψ* = (γ, ψlo).
  `sU`: two rounds; the sending of the family `NU`, whose member `iU` is G_u, which holds the whole
    folded full message u.
  `loc`: one round; the verifier's message is t locations of the encoded index.
  `sO`: two rounds; the sending of the family `NO`, whose member `iO` is Ω, which holds
    ω = (index matrix)·eq(ψ*, ·) (`omOf`).
  `zeta`: one round; the verifier's message is ζ.
The parameters of the statements. `on0` is a condition on the encoded index and its record, a
parameter; all that the chain uses of it is `P.FoldErr on0 εf`: on the statements that meet `on0` at
most εf points γ are bad for the fold at the radius e'. `S` (`P.Snd`) holds the honest senders and
the numbers of the three sendings; `S.OK` is what the statement on a sending
(`Spec.ldSendFam_piece`, Cb/Ld/LdSendPiece.lean) asks, three times. `P.D.py` gives the rows of the
index matrix as vertices of a cube (Cb/Ld/LdLinWords.lean). `d` is any value of the first joint's
type of witnesses: the composed extractor's value where the first verifier rejects (`IOR.extSeq`,
through `Link.seq`).

Why: Cb/Ld/LdLin.lean's test takes as closing one reduction with the whole bundle, honest-verifier
zero knowledge included. A closing whose splittings take their masks from mask-only oracle messages
that ride with W, G_u or Ω (as this protocol's technical report (lean/CREDITS.md) has it) is not
zero knowledge by itself: its masks stand in its input witness (Ior/Masked.lean:
`masked_not_exact`). Zero knowledge is then a
property of the whole chain only (Ior/KnowCollRulesChain.lean: `Chain`, `c.Ok`;
Ior/KnowCollPiece.lean: `c.OkFrom c₀`; Cb/Ld/LdTowerKitChain.lean: `chain_tail_append`).

Main names (in the statements of `Cb.Spec` the type ι of positions is nonempty):
  `P.chain on0 S εf`: the core, as a chain. `P.linC on0 S εf cZ d`: the test, with a closing chain.
  `Spec.ldLinC_allT`, `Spec.ldLinC_sides`: under `P.FoldErr on0 εf`, injective `P.D.py` and `S.OK`:
    every link of the core has the whole bundle (`Chain.AllT`, Ior/KnowCollRulesChain.lean); every
    link has the budgets' half (`Chain.Sides`, Ior/KnowCollPiece.lean), from `P.q0 qa` to
    `P.q5 S qa`.
  `Spec.ldLinC_tail`: under `P.FoldErr on0 εf`, injective `P.D.py` and `S.OK`:
    for every closing chain that stands behind the core
      (cZ.OkFrom core: each of its links has the whole bundle, or is a masked block whose masks are
      fresh after all that comes before it, the core included)
    and has the budgets' half (`cZ.SidesCT`):
    the test is a tail of a chain (`TailTr`) from the claim on the encoded index to the trivial
    statement, on the statements with the condition (`(P.j0 on0).on`).
    So `Spec.tailTr_end` (Cb/Ld/LdTowerKit.lean) applies.
  `Spec.ldLinC_rounds`: the rounds of the core: sums over the links.
  `Spec.ldLinC_err`: the errors of the core: those of the seven blocks, in a row.
  `Iop.Spec.blind_peek`: a round without a prover message does not look at masks, if what the honest
    prover computes there does not: the form in which "fresh" is carried through pt, loc, zeta
    (Ior/KnowCollRulesMask.lean: `Blind`).

What the statements conclude. `Spec.ldLinC_tail` concludes `TailTr`; `Spec.ldLinC_allT` concludes
"the whole bundle", `IOR.GoodT`, of every link of the core. `TailTr`, a tail of a chain, asks of a
reduction from a joint to a joint whose statements have no oracles the bundle `IOR.GoodT` and three
further clauses, `noHid`, `tied` and `bears`, which Cb/Ld/LdTowerKit.lean states (through
`IOR.Tied`, Ior/Batch.lean, and `IOR.Bears`, Ior/Bears.lean). `IOR.GoodT` (likewise `IOR.Good`,
Ior/Chain.lean) bundles what is asked of one reduction, with its honest side, between two joints, at
given numbers; among its clauses: completeness between the honest relations, outside sets of
verifier randomness whose probabilities further clauses bound by the numbers; round-by-round
knowledge soundness (`Know`) between the relaxed relations, on the input joint's set of statements,
with a given extractor, at the numbers' list of errors; and one on honest-verifier zero knowledge.

What `cZ.OkFrom` asks of the order in a closing: a masked link's masks must be fresh after all that
comes before it: before it, no prover message but the oracle message that holds them and its answer
may depend on them, on that message's pad or on its encoding randomness; in particular no test on a
group that holds that message comes before the splitting; the masks of different blocks are
disjoint, and none is a pad: a matter of the sending that is Fresh for each of them.

Limits: no closing chain is given (none in this file; closing chains, each over a plan (`LdTc`) that
is a parameter: `LdLinC.cZ`, Cb/Ld/LdLinCloseLin.lean; `LdLinC.cZf`, Cb/Ld/LdLinCloseSplit.lean).
That masks sent in the core are fresh after it (`FreshFor`) is part of the hypothesis `cZ.OkFrom`.
It asks that the sending which holds them is Fresh and that the later links are Blind. For the
sendings this is a matter of their senders. One instance; the batch: Cb/Ld/LdLinChainB.lean,
Cb/Ld/LdLinChainBFmt.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinProofsChain
import Cb.Ld.LdTowerKitChain
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
namespace Spec
open IOR

/-- A round without a prover message does not look at masks, if what the honest prover computes
there does not. -/
def blind_peek : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (V : PeekV Xi Ei Xo Eo)
      (hx : Xi → Wi → V.D → Xo) (hw : Xi → Wi → V.D → Wo) (Ki Ko : Type) (kci : Wi → Ki)
      (kco : Wo → Ko) (Mk : Type) (puti : Mk → Ki → Ki) (puto : Mk → Ko → Ko),
    (∀ w w' M x c,
      kci w' = puti M (kci w) → hx x w' c = hx x w c ∧ kco (hw x w' c) = puto M (kco (hw x w c))) →
    (Honest.peek V hx hw).Blind kci kco Mk puti puto

end Spec

theorem blind_peek : Spec.blind_peek := fun _ _ _ _ _ _ V _ _ _ _ _ _ _ _ _ h w w' M x _ ρ hk =>
  ⟨rfl, (h w w' M x (show V.D × Unit from ρ).1 hk).1, (h w w' M x (show V.D × Unit from ρ).1 hk).2⟩

end Iop

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace LdLinP
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
  [Fintype Y] (P : LdLinP E ι κ J Y)
variable (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (S : P.Snd) (εf : ℕ)

/-! ### The joints of Cb/Ld/LdLin.lean with their types, at the form whose conditions may fail
(`Rels.cf`) -/

def J0 : Joint Unit := ⟨P.X0, P.E0, P.W0, (P.j0 on0).cf⟩
def JA : Joint Unit := ⟨P.X0, P.E0, P.WA, (P.jA on0).cf⟩
def J1 : Joint Unit := ⟨P.X1, P.E1, P.W1, (P.j1 on0).cf⟩
def J2 : Joint Unit := ⟨P.X2, P.E1, P.W2, (P.j2 on0).cf⟩
def J3 : Joint Unit := ⟨P.X3, P.E3, P.W3, (P.j3 on0).cf⟩
def J4 : Joint Unit := ⟨P.X4, P.E4, P.W4, P.j4.cf⟩
def J5 : Joint Unit := ⟨P.X5, P.E5, P.W5, P.j5.cf⟩
def J6 : Joint Unit := ⟨P.X6, P.E5, P.W5, P.j6.cf⟩
/-- the trivial statement -/
def JT : Joint Unit := ⟨Unit, extNone, Unit, trivRels⟩

/-! ### The seven blocks as links (reduction, honest side, extractor, numbers) -/

def lk0 : Link Unit (P.J0 on0) (P.JA on0) :=
  ⟨P.step0, P.hStep0, fun _ _ w => w.2, Nums.pure Unit some (ExtMap.id _)⟩
def lkW : Link Unit (P.JA on0) (P.J1 on0) :=
  ⟨P.sW, ldSendFamHon P.SdW P.X0 P.E0 S.dW,
    fun _ _ w => P.backW (P.NW.msgs w.1) w.2,
    ldSendFamNums P.NW P.SdW P.X0 P.E0 Unit S.LW S.tW⟩
def lkPt : Link Unit (P.J1 on0) (P.J2 on0) :=
  ⟨P.pt, P.hPt, fun _ _ w => w.2, Nums.peek Unit P.vPt (P.errPt εf)⟩
def lkU : Link Unit (P.J2 on0) (P.J3 on0) :=
  ⟨P.sU, ldSendFamHon P.SdU P.X2 P.E1 S.dU,
    fun _ _ w => P.backU (P.NU.msgs w.1) w.2,
    ldSendFamNums P.NU P.SdU P.X2 P.E1 Unit S.LU S.tU⟩
def lkLoc : Link Unit (P.J3 on0) P.J4 :=
  ⟨P.loc, P.hLoc, fun _ _ w => w.2, Nums.peek Unit P.vLoc P.errLoc⟩
def lkO : Link Unit P.J4 P.J5 :=
  ⟨P.sO, ldSendFamHon P.SdO P.X4 P.E4 S.dO,
    fun _ _ w => P.backO (P.NO.msgs w.1) w.2,
    ldSendFamNums P.NO P.SdO P.X4 P.E4 Unit S.LO S.tO⟩
def lkZeta : Link Unit P.J5 P.J6 :=
  ⟨P.zeta, P.hZeta, fun _ _ w => w, Nums.peek Unit P.vZeta P.errZeta⟩

/-- The core: the chain of these seven links, in this order, bracketed to the left. -/
def chain : Chain Unit (P.J0 on0) P.J6 :=
  ((((((Chain.one (P.lk0 on0)).snoc (P.lkW on0 S)).snoc (P.lkPt on0 εf)).snoc (P.lkU on0 S)).snoc
      (P.lkLoc on0)).snoc
    (P.lkO S)).snoc P.lkZeta

/-- the core as one link, written out -/
def coreL (d : P.W0) : Link Unit (P.J0 on0) P.J6 :=
  ((((((P.lk0 on0).seq (P.lkW on0 S) d).seq (P.lkPt on0 εf) d).seq (P.lkU on0 S) d).seq
        (P.lkLoc on0) d).seq
      (P.lkO S) d).seq
    P.lkZeta d

/-- The test, for any closing chain cZ from `P.J6` to the trivial statement. -/
def linC (cZ : Chain Unit P.J6 JT) (d : P.W0) : Link Unit (P.J0 on0) JT :=
  ((P.chain on0 S εf).append cZ).link d

end LdLinP

namespace Spec
section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- States: under the hypotheses below, every link of the core has the whole bundle. -/
def ldLinC_allT : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf : ℕ) (S : P.Snd),
    P.FoldErr on0 εf → Function.Injective P.D.py → S.OK → (P.chain on0 S εf).AllT

/-- States: under the hypotheses below, every link of the core has the budgets' half. -/
def ldLinC_sides : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf : ℕ)
      (S : P.Snd) (qa : Finset P.Ea.Pos → Prop),
    P.FoldErr on0 εf → Function.Injective P.D.py → S.OK →
    (P.chain on0 S εf).Sides (P.q0 qa) (P.q5 S qa)

/-- States, under the hypotheses below: the test, with any closing chain that stands behind the core
and has the budgets' half, is a tail of a chain (`TailTr`) from the claim on the encoded index to
the trivial statement, on the statements with the condition. -/
def ldLinC_tail : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf : ℕ) (S : P.Snd)
      (qa : Finset P.Ea.Pos → Prop) (d : P.W0) (cZ : Chain Unit P.J6 LdLinP.JT),
    P.FoldErr on0 εf → Function.Injective P.D.py → S.OK →
    cZ.OkFrom (P.chain on0 S εf) → cZ.SidesCT (P.q5 S qa) →
    TailTr (P.linC on0 S εf cZ d).R (P.linC on0 S εf cZ d).H (P.j0 on0) trivRels
      (P.linC on0 S εf cZ d).ext (P.linC on0 S εf cZ d).P (P.q0 qa)

/-- States: the core has 2+1+2+1+2+1 rounds, of which at most six have a verifier message that is
not empty: sums over the links. -/
def ldLinC_rounds : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf : ℕ) (S : P.Snd),
    (P.chain on0 S εf).nAll = 0 + 2 + 1 + 2 + 1 + 2 + 1 ∧
    (P.chain on0 S εf).nVer ≤ 0 + 1 + 1 + 1 + 1 + 1 + 1

/-- States: the core as one link is `P.coreL`, written out; its errors are those of the seven blocks
in a row, in the brackets of the chain. -/
def ldLinC_err : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
      (εf : ℕ) (S : P.Snd) (d : P.W0),
    (P.chain on0 S εf).link d = P.coreL on0 S εf d ∧
    (P.coreL on0 S εf d).P.err =
      Err.app (t := P.zeta.shape)
        (Err.app (t := P.sO.shape)
          (Err.app (t := P.loc.shape)
            (Err.app (t := P.sU.shape)
              (Err.app (t := P.pt.shape)
                (Err.app (s := P.step0.shape) (t := P.sW.shape) ()
                  (ldSendFamNums P.NW P.SdW P.X0 P.E0 Unit S.LW S.tW).err)
                ((P.errPt εf, ()) : ℕ × Unit))
              (ldSendFamNums P.NU P.SdU P.X2 P.E1 Unit S.LU S.tU).err)
            ((P.errLoc, ()) : ℕ × Unit))
          (ldSendFamNums P.NO P.SdO P.X4 P.E4 Unit S.LO S.tO).err)
        ((P.errZeta, ()) : ℕ × Unit)

end
end Spec

section
variable {E ι κ J Y : Type}
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- the seven pieces -/
theorem LdLinP.pieces (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf : ℕ)
    (S : P.Snd) (qa : Finset P.Ea.Pos → Prop) (hF : P.FoldErr on0 εf)
    (hpy : Function.Injective P.D.py) (hS : S.OK) :
    PieceTr (P.lk0 on0).R (P.lk0 on0).H (P.J0 on0).rels (P.JA on0).rels (P.lk0 on0).ext
      (P.lk0 on0).P (P.q0 qa) (P.q0 qa) ∧
    PieceTr (P.lkW on0 S).R (P.lkW on0 S).H (P.JA on0).rels (P.J1 on0).rels (P.lkW on0 S).ext
      (P.lkW on0 S).P (P.q0 qa) (P.q1 S qa) ∧
    PieceTr (P.lkPt on0 εf).R (P.lkPt on0 εf).H (P.J1 on0).rels (P.J2 on0).rels (P.lkPt on0 εf).ext
      (P.lkPt on0 εf).P (P.q1 S qa) (P.q1 S qa) ∧
    PieceTr (P.lkU on0 S).R (P.lkU on0 S).H (P.J2 on0).rels (P.J3 on0).rels (P.lkU on0 S).ext
      (P.lkU on0 S).P (P.q1 S qa) (P.q3 S qa) ∧
    PieceTr (P.lkLoc on0).R (P.lkLoc on0).H (P.J3 on0).rels P.J4.rels (P.lkLoc on0).ext
      (P.lkLoc on0).P (P.q3 S qa) (P.q4 S qa) ∧
    PieceTr (P.lkO S).R (P.lkO S).H P.J4.rels P.J5.rels (P.lkO S).ext (P.lkO S).P
      (P.q4 S qa) (P.q5 S qa) ∧
    PieceTr P.lkZeta.R P.lkZeta.H P.J5.rels P.J6.rels P.lkZeta.ext P.lkZeta.P
      (P.q5 S qa) (P.q5 S qa) :=
  ⟨ldk_pieceTr_cf (ldLin_step0 P on0 (P.q0 qa)),
    ldSendFam_piece E P.NW P.SdW Unit P.X0 P.WA P.W0 P.E0 (P.jA on0) P.backW S.dW S.LW S.tW
      (P.q0 qa) hS.lawsW hS.fairW hS.listW hS.evW hS.sndW hS.blW hS.hidW,
    ldk_pieceTr_cf (ldLin_pt P on0 εf (P.q1 S qa) hF),
    ldSendFam_piece E P.NU P.SdU Unit P.X2 P.W2 P.W1 P.E1 (P.j2 on0) P.backU S.dU S.LU S.tU
      (P.q1 S qa) hS.lawsU hS.fairU hS.listU hS.evU hS.sndU hS.blU hS.hidU,
    ldk_pieceTr_cf (ldLin_loc P on0 S qa),
    ldSendFam_piece E P.NO P.SdO Unit P.X4 P.W4 P.W3 P.E4 P.j4 P.backO S.dO S.LO S.tO (P.q4 S qa)
      hS.lawsO hS.fairO hS.listO hS.evO hS.sndO hS.blO hS.hidO,
    ldk_pieceTr_cf (ldLin_zeta P (P.q5 S qa) hpy)⟩

theorem ldLinC_allT : Spec.ldLinC_allT E ι κ J Y := by
  intro P on0 εf S hF hpy hS
  obtain ⟨h0, hW, hP, hU, hL, hO, hZ⟩ := P.pieces on0 εf S (fun _ => True) hF hpy hS
  unfold LdLinP.chain
  simp only [Chain.allT_snoc, Chain.allT_one]
  exact ⟨⟨⟨⟨⟨⟨h0.good, hW.good⟩, hP.good⟩, hU.good⟩, hL.good⟩, hO.good⟩, hZ.good⟩

theorem ldLinC_sides : Spec.ldLinC_sides E ι κ J Y := by
  intro P on0 εf S qa hF hpy hS
  obtain ⟨h0, hW, hP, hU, hL, hO, hZ⟩ := P.pieces on0 εf S qa hF hpy hS
  unfold LdLinP.chain
  simp only [Chain.sides_snoc, Chain.sides_one]
  exact ⟨P.q5 S qa,
    ⟨P.q4 S qa,
      ⟨P.q3 S qa,
        ⟨P.q1 S qa,
          ⟨P.q1 S qa,
            ⟨P.q0 qa, ⟨h0.noHid, h0.noTie, h0.bears⟩, ⟨hW.noHid, hW.noTie, hW.bears⟩⟩,
            ⟨hP.noHid, hP.noTie, hP.bears⟩⟩,
          ⟨hU.noHid, hU.noTie, hU.bears⟩⟩,
        ⟨hL.noHid, hL.noTie, hL.bears⟩⟩,
      ⟨hO.noHid, hO.noTie, hO.bears⟩⟩,
    ⟨hZ.noHid, hZ.noTie, hZ.bears⟩⟩

theorem ldLinC_tail : Spec.ldLinC_tail E ι κ J Y := by
  intro P on0 εf S qa d cZ hF hpy hS hOk hSd
  have h := chain_tail_append Unit (P.J0 on0) P.J6 Unit Unit trivRels (P.chain on0 S εf) cZ d
    (P.q0 qa) (P.q5 S qa) ((ok_of_allT Unit _ _ _).1 (ldLinC_allT P on0 εf S hF hpy hS)) hOk
    (sidesC_of_sides Unit _ _ _ _ _ (ldLinC_sides P on0 εf S qa hF hpy hS)) hSd
  exact ⟨goodT_cf_out _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ => trivial) h.good,
    h.noHid, h.tied, h.bears⟩

theorem ldLinC_rounds : Spec.ldLinC_rounds E ι κ J Y := by
  intro P on0 εf S
  unfold LdLinP.chain
  simp only [Chain.nAll_snoc, Chain.nAll_one, Chain.nVer_snoc, Chain.nVer_one]
  refine ⟨rfl, ?_⟩
  have hs : ∀ (N : Sig E) (Sd : N.Seeds), (N.sh Sd).nVer ≤ 1 := fun N Sd => by
    show (if Fintype.card Sd.D = 1 then 0 else 1) + ((if Fintype.card Unit = 1 then 0 else 1) + 0) ≤
      1
    rw [if_pos Fintype.card_unit]
    split <;> omega
  have hd : ∀ (D : Type) [Fintype D] [Nonempty D], Shape.nVer [drawRound D] ≤ 1 := fun D _ _ => by
    show (if Fintype.card D = 1 then 0 else 1) + 0 ≤ 1
    split <;> omega
  show 0 + (P.NW.sh P.SdW).nVer + Shape.nVer [drawRound P.D.Pt] + (P.NU.sh P.SdU).nVer +
      Shape.nVer [drawRound (Fin P.t → ι)] + (P.NO.sh P.SdO).nVer +
      Shape.nVer [drawRound (Fin P.D.l → E)] ≤ _
  have a1 := hs P.NW P.SdW
  have a2 := hd P.D.Pt
  have a3 := hs P.NU P.SdU
  have a4 := hd (Fin P.t → ι)
  have a5 := hs P.NO P.SdO
  have a6 := hd (Fin P.D.l → E)
  omega

theorem ldLinC_err : Spec.ldLinC_err E ι κ J Y := by
  intro P on0 εf S d
  refine ⟨?_, rfl⟩
  unfold LdLinP.chain LdLinP.coreL
  simp only [Chain.link_snoc, Chain.link_one]

end
end Cb
