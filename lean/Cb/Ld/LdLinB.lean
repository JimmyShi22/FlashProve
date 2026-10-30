-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinB.lean: the test for linear constraints on the encoded index for at most N instances
that share the encoded index and its record: round-by-round knowledge soundness.

Definitions and statements (in `Iop.Spec` and `Cb.Spec`); the proofs are in
Cb/Ld/LdLinBProofs.lean. The protocol of one slot is Cb/Ld/LdLin.lean's, unchanged.
In standard terms: at most N instances (slots) of the one-instance protocol run side by side; a
prover message has a slot's part and a shared part; a local round has a verifier message for each
slot, a shared round one for all (`RAnn`, `Kind`, Iop/Batch.lean). `KnowB` (Ior/BatchSeq.lean) asks,
for each statement, for sets of bad verifier messages that are within the errors, jointly for every
admissible vector, such that for a statement that meets `on`, on a transcript that avoids them, the
extractor leads a witness of the output statement back to one of the input.

The annotation (`annCore`):
  `step0`: no round.
  `sW`: the slot sends its own family NW (W, and its own mask-only messages); its seed is its own
    (a local verifier message); then its answers.
  `pt`: nobody sends; one shared point ψ* for all slots.
  `sU`, `loc`, `sO`, `zeta`: only the shared part of the prover sends (the families of G_u and of
    Ω, their answers); the seeds, the locations and ζ are shared: one G_u, one list of locations,
    one Ω for the whole batch.
The errors (`errCoreB`), counts of values of one verifier message. As for one instance, but for the
shared point:
εf·q^klo + N·(v + klo)·q^(v+klo-1): the fold's bad points are counted once (they are a function of
the encoded index and its record), the instances' by the union bound. G_u's and Ω's seeds, the
locations, ζ: once, not N times: their bad sets are functions of what the slots share. W's seed: the
one-instance error, in a local round (`JWithin`, Blocks/Batch/Kit.lean).
In the formula q is the number of elements of E; v = `P.D.X.v`, the number of row variables; klo =
`P.D.klo`, the number of column variables inside a code row; εf: see `Spec.ldLinB_core`.

Main names:
`k0` .. `k6`: the keys (a vector of statements is admissible if all its members have one key:
`SameKey`, Ior/BatchSeq.lean).
Generic (no protocol): a round without a prover message (`IOR.peek`, Cb/Ld/LdLinKit.lean) under a
shared verifier message:
  `Spec.knowB_peek`: `KnowB` from a joint count: for every admissible vector, the values that are
    bad for some slot number at most err.
  `Spec.knowB_peek_key`: the same if a slot's bad values lie in a set that is a function of a key,
    of at most err elements: counted once.
  Both at the joints whose conditions may fail (`Rels.cf`), if the round carries the condition.
The test (ι, the set of positions of the encoded index, is nonempty in the last two; their argument
d: the extractor's fixed values, where a verifier has rejected: `P.extCore`, Cb/Ld/LdLin.lean):
  `Spec.ldLinB_send_shared`: a sending by the shared part, under `Sd.Fair`, bounds on the lists and
    evading samples, has `KnowB` with every vector admissible and the sending's errors, counted
    once.
  `Spec.ldLinB_core`: under `P.FoldErr on0 εf` (on the statements that meet `on0` at most εf points
    γ are bad for the fold), an injective `P.D.py` and `S.OK` (all three are told in the head of
    Cb/Ld/LdLinChain.lean): the chain up to the rows that are left has `KnowB`, at the joints `.cf`,
    for the vectors with one key `k0`, with the errors `errCoreB`, and takes them to vectors with
    one key `k6`.
  `Spec.ldLinB_know`: under the three hypotheses of `Spec.ldLinB_core`, with a closing that has
    `KnowB` for the vectors with one key `k6`: the test has `KnowB` for the vectors with one key
    `k0`, on the statements with the condition `(P.j0 on0).on`, to the trivial statement.

Why, on the count: a list of joint errors has N times the sample's error in the round of the W's
seeds (a joint error); here each slot has its own seed in a
local round, with the error of one instance, as the errors "for one fixed instance" have it
(`KnowB`,
Ior/BatchSeq.lean). A write-up of ours (lean/CREDITS.md) prints both lists, the joint one
and the one for one fixed instance: the list here is the second.

Limits: this file says nothing on the honest side of a batch (who computes what from which witness;
zero knowledge for sets of slots). No closing is given (none of type `P.Closing`; a closing chain
with annotations, over a plan (`LdTcA`) that is a parameter, for the test on chains `P.linCA`,
Cb/Ld/LdLinChainB.lean: `LdLinC.cZA`, Cb/Ld/LdBatchBlocksPlan.lean). All of `KnowB`'s content hangs
on which vectors are admissible (the head of Ior/BatchSeq.lean): here, at the start, those that
share encoded index and record.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Ld.LdLin
import Ior.KnowWideB
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
namespace Spec
open IOR Prob

/-- A round without a prover message, under a shared verifier message: from a joint count.
(not all hypotheses are named here: see the statement below) -/
def knowB_peek : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (V : PeekV Xi Ei Xo Eo)
      (back : Xi × Ei.Str → V.D → Wo → Wi) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (N err : ℕ)
      (adm : (Fin N → Option (Xi × Ei.Str)) → Prop),
    (∀ x y c, A.on (x, y) → B.on (V.nx x y c, V.g.map y)) →
    (∀ a, adm a →
      cnt (fun c =>
          ∃ j aj,
            a j = some aj ∧ A.on aj ∧
            ∃ w', B.relR (V.nx aj.1 aj.2 c, V.g.map aj.2) w' ∧ ¬ A.relR aj (back aj c w')) ≤ err) →
    (IOR.peek V).KnowB (RoundSplits.const (RAnn.ofShared .sh) [drawRound V.D]) N adm (fun _ => True)
      A.cf.relR B.cf.relR (fun a τ w' => back a (drawn τ) w') ((err, ()) : ℕ × Unit)

/-- The same, counted once: a slot's bad values lie in a set that is a function of a key.
(not all hypotheses are named here: see the statement below) -/
def knowB_peek_key : Prop :=
  ∀ (K Xi Xo κ : Type) (Ei Eo : ExtSpec) (Wi Wo : Type) (V : PeekV Xi Ei Xo Eo)
      (back : Xi × Ei.Str → V.D → Wo → Wi) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo) (N err : ℕ)
      (key : Xi × Ei.Str → κ) (Bk : κ → V.D → Prop),
    (∀ x y c, A.on (x, y) → B.on (V.nx x y c, V.g.map y)) → (∀ k, cnt (Bk k) ≤ err) →
    (∀ a c w',
      A.on a → B.relR (V.nx a.1 a.2 c, V.g.map a.2) w' → ¬ A.relR a (back a c w') → Bk (key a) c) →
    (IOR.peek V).KnowB (RoundSplits.const (RAnn.ofShared .sh) [drawRound V.D]) N (SameKey key)
      (fun _ => True) A.cf.relR B.cf.relR (fun a τ w' => back a (drawn τ) w') ((err, ()) : ℕ × Unit)

end Spec
end Iop

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood

namespace LdLinP
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
  [Fintype Y] (P : LdLinP E ι κ J Y)

/-- only the shared part speaks, and the verifier's messages are shared -/
abbrev shAnn (s : Shape) : RoundSplits s := RoundSplits.const (RAnn.ofShared .sh) s

/-- Who speaks, and which verifier messages are shared. -/
def annCore : RoundSplits P.core.shape :=
  RoundSplits.app (s := P.step0.shape) (RoundSplits.allLocal _)
    (RoundSplits.app (s := P.sW.shape) (RoundSplits.allLocal _)
      (RoundSplits.app (s := P.pt.shape) (shAnn _)
        (RoundSplits.app (s := P.sU.shape) (shAnn _)
          (RoundSplits.app (s := P.loc.shape) (shAnn _)
            (RoundSplits.app (s := P.sO.shape) (t := P.zeta.shape) (shAnn _) (shAnn _))))))

def annLin (Z : P.Closing) (aT : RoundSplits Z.T.shape) : RoundSplits (P.lin Z).shape :=
  RoundSplits.app (s := P.core.shape) P.annCore aT

/-- What the statements of one batch have in common, joint by joint: at the start the encoded index
and its record; then also ψ*; G_u's family and its samples; the locations and the folds read (from
here on without the encoded index, which has left the statement); Ω's family and its samples; ζ. -/
def k0 (a : P.X0 × P.E0.Str) : (ι → P.Sy) × P.D.X.Rec := (a.2.1, a.1.2)
def k1 (a : P.X1 × P.E1.Str) : (ι → P.Sy) × P.D.X.Rec := (a.2.1.1, a.1.1.2)
def k2 (a : P.X2 × P.E1.Str) : ((ι → P.Sy) × P.D.X.Rec) × P.D.Pt := ((a.2.1.1, a.1.1.1.2), a.1.2)
def k3 (a : P.X3 × P.E3.Str) : (((ι → P.Sy) × P.D.X.Rec) × P.D.Pt) × (P.NU.Smp × P.NU.ext.Str) :=
  (((a.2.1.1.1, a.1.1.1.1.2), a.1.1.2), (a.1.2, a.2.2))
def k4 (a : P.X4 × P.E4.Str) : ((P.D.X.Rec × P.D.Pt) × (P.NU.Smp × P.NU.ext.Str)) × P.Loc :=
  (((a.1.1.1.1.1.2, a.1.1.1.2), (a.1.1.2, a.2.2)), a.1.2)
def k5 (a : P.X5 × P.E5.Str) :
    (((P.D.X.Rec × P.D.Pt) × (P.NU.Smp × P.NU.ext.Str)) × P.Loc) × (P.NO.Smp × P.NO.ext.Str) :=
  (P.k4 (a.1.1, a.2.1), (a.1.2, a.2.2))
def k6 (a : P.X6 × P.E5.Str) :
    ((((P.D.X.Rec × P.D.Pt) × (P.NU.Smp × P.NU.ext.Str)) × P.Loc) × (P.NO.Smp × P.NO.ext.Str)) ×
      (Fin P.D.l → E) :=
  (P.k5 (a.1.1, a.2), a.1.2)

/-- the error of the shared point for at most N instances -/
def errPtB (εf N : ℕ) : ℕ :=
  εf * Fintype.card E ^ P.D.klo +
    N * ((P.D.X.v + P.D.klo) * Fintype.card E ^ (P.D.X.v + P.D.klo - 1))

/-- The errors of the chain for at most N instances. -/
def errCoreB (S : P.Snd) (εf N : ℕ) : Err P.core.shape :=
  Err.app (s := P.step0.shape) ()
    (Err.app (s := P.sW.shape) (ldSendFamNums P.NW P.SdW P.X0 P.E0 Unit S.LW S.tW).err
      (Err.app (s := P.pt.shape) ((P.errPtB εf N, ()) : ℕ × Unit)
        (Err.app (s := P.sU.shape) (ldSendFamNums P.NU P.SdU P.X2 P.E1 Unit S.LU S.tU).err
          (Err.app (s := P.loc.shape) ((P.errLoc, ()) : ℕ × Unit)
            (Err.app (s := P.sO.shape) (t := P.zeta.shape)
              (ldSendFamNums P.NO P.SdO P.X4 P.E4 Unit S.LO S.tO).err
              ((P.errZeta, ()) : ℕ × Unit))))))

end LdLinP

namespace Spec
open IOR
section
variable (E : Type) [Field E]

/-- A sending by the shared part, under the three hypotheses below: every vector is admissible; the
error is counted once. In the proof the bad seeds are `ldSendFamBad` (Cb/Ld/LdSendFam.lean): those
with a collision of some member for its word; they do not depend on the statement. -/
def ldLinB_send_shared : Prop :=
  ∀ (M : Sig E) (Sd : M.Seeds) (X W W' : Type) (E₀ : ExtSpec) (A : Rels Unit X E₀ W)
      (back : M.Msg → W' → W) (L t : M.O → ℕ) (N : ℕ),
    Sd.Fair → (∀ a, (M.om a).ListLE (L a)) → (∀ a, (M.om a).Evades) →
    (ldSendFam M Sd X E₀).KnowB (RoundSplits.const (RAnn.ofShared .sh) (M.sh Sd)) N (fun _ => True)
      (fun _ => True) A.cf.relR (M.over (M.pull A back)).cf.relR
      (fun _ _ w => back (M.msgs w.1) w.2) (ldSendFamNums M Sd X E₀ Unit L t).err

variable (ι κ J Y : Type) [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- The chain up to the rows that are left, for at most N instances.
(not all hypotheses are named here: see the statement below) -/
def ldLinB_core : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf N : ℕ) (S : P.Snd)
      (d : P.W0 × P.WA × P.W1 × P.W2 × P.W3 × P.W4),
    P.FoldErr on0 εf → Function.Injective P.D.py → S.OK →
    P.core.KnowB P.annCore N (SameKey P.k0) (fun _ => True) (P.j0 on0).cf.relR P.j6.cf.relR
      (P.extCore d) (P.errCoreB S εf N) ∧
    ∀ a, SameKey P.k0 a →
      ∀ τ : BTr N P.core.shape P.annCore,
        SameKey P.k6 fun j => (a j).bind fun aj => P.core.red.out aj (τ.slot j)

/-- The test for at most N instances, with any closing that is knowledge sound for the vectors of
statements which share what the chain makes them share.
(not all hypotheses are named here: see the statement below) -/
def ldLinB_know : Prop :=
  ∀ (P : LdLinP E ι κ J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (εf N : ℕ)
      (S : P.Snd) (d : P.W0 × P.WA × P.W1 × P.W2 × P.W3 × P.W4) (Z : P.Closing)
      (aT : RoundSplits Z.T.shape) (εT : Err Z.T.shape),
    P.FoldErr on0 εf → Function.Injective P.D.py → S.OK →
    Z.T.KnowB aT N (SameKey P.k6) (fun _ => True) P.j6.cf.relR (fun _ (_ : Unit) => True) Z.ext εT →
    (P.lin Z).KnowB (P.annLin Z aT) N (SameKey P.k0) (P.j0 on0).on (P.j0 on0).relR
      (fun _ (_ : Unit) => True) (P.extLin Z d) (Err.app (s := P.core.shape) (P.errCoreB S εf N) εT)

end
end Spec
end Cb
