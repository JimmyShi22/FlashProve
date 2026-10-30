-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Compile/Batch/NeedP.lean: two facts on the scheme `argP` (Compile/Batch/StarS.lean: entries in the
  verification key, no query for an empty slot, proving key (i, seed)). (1) Under the two hypotheses
  below, its three algorithms C, P, V (committer, prover, verifier) go on in the same way after two
  answers that agree on the marked blocks (`facOK_argP`); the marked blocks are those that the table
  of Compile/Batch/NeedTable.lean names ("what is needed" in the docstring of `facOK_argP`). (2) For
  `Std m`: an upper bound on what the marked blocks of its verifier's queries add up to
  (`costBoundAt_V_argP`); Compile/Batch/NeedCost.lean has the same bound for V of
  Compile/Batch/Star.lean (words of this library: lean/GLOSSARY.md).

  Compile/Batch/StarS.lean: argP W WP p bk σ. Its three algorithms are made from programs of
  Compile/Batch/Star.lean and Compile/Batch/ProverU.lean by bind, pure, sample, `erase`, `realQ` and
  the two constructions of the derived mode (every sample made from small ones; these read out of
  answers of a derivation oracle σ.o), all of which preserve the condition (`OComp.FactorsBy`:
  Rom/OverOneN.lean, Rom/OverOneNDerive.lean; for `erase`: `SFac.erase`, Compile/NeedBlocks.lean;
  for `realQ`: `facBy_realQ`, Compile/Batch/NeedBlocks.lean).
  Hypotheses: `QueryLayout.NB W nb` (the challenge of round i of protocol t is a function of the blocks
  below nb t i), and hσ: of an answer of the derivation oracle nothing is left out. The second holds
  if σ.o is the oracle `other` (`whole_of_eq`, Top/ProgN.lean).
    `sf_batOf`        one batch on a given node, for any compiled prover pv that has the property
                      (`SFac`)
    `facOK_argP`      C, P, V read a typed answer only up to the relation `agree nb`. The step from
                      it to what the second exit asks of a scheme, and what that exit then carries
                      over, are not in this library.
    `costBoundAt_V_argP`
                      for every coding m that splits an answer as Compile/Batch/ImplOf.lean does
                      (`Std m`), and whatever key, request and proof V is given: on every path the
                      marked blocks of the queries of V, at the table `needOf nb m`, add up to at
                      most the bound cVBN W nb. The reason: V runs the verifier of
                      Compile/Batch/Star.lean on other inputs (`reK`, `liftK`,
                      Compile/Batch/StarK.lean). A bound on V's queries over the second exit is not
                      in this library.
  Notation:
    `W`: a `QueryLayout lam L` (Iop/BatchWire.lean): the wire record: parameters of the compiler, beside
      `Params`;
    `WP`: a `WireBP L` (Iop/BatchWireP.lean): the prover's data for the three protocols, and the
      enumeration of the encoding randomness;
    `p`: a `Params` (Compile/Star.lean): the numbers `sMT`, `sFS`, `M` (the number of copies is M
      + 1) and `s1`;
    `bk`: a `CoinPlan` (Rom/Blocks.lean): how a uniform sample is made from small ones;
    `σ`: a `SeedOracle` (Rom/SpecDerive.lean): an auxiliary oracle, used as a source of coins;
      `σ.o`: that oracle's name;
    `OComp.FactorsBy ag c` (Rom/OverOneN.lean): the program reads an answer only up to a relation
      ag on answers: at every query node, answers in the relation have the same continuation
      program; and so on in every continuation;
    `SFac` (Compile/NeedBlocks.lean): `FactorsBy` for a token program; `FacOK ag A`
      (Rom/OverOneNGen.lean): the three algorithms read an answer only up to a relation ag on
      answers;
    `agree nb` (Compile/Batch/NeedTable.lean): two typed answers agree on what is needed;
    the second exit (the title of Rom/OverOneN.lean): the step to one hash function in which only
      marked hash blocks of an answer are queried;
    `pv`: a `Seed.Run W` (Compile/Batch/SeedFace.lean): what is in the place of the compiled
      prover of a batch;
    `liftK π`, `reK ℓ π` (Compile/Batch/StarK.lean): a proof without entry in the format `Prf`;
      the proof π with the fields cm and piL overwritten by entry number π.leaf, or by (zeros, none)
      if the list has no such entry, and the field leaf by 0.
  Limits: nothing on C's and P's numbers of queries. No probability and no error bound is stated
  here.
-/
import Compile.Batch.StarS
import Compile.Batch.NeedCost
import Rom.OverOneNDerive
import Compile.Batch.NeedBlocksU
import Rom.OverOneNGen

open Rom Iop

namespace Compile.Batch
namespace Need
open Compile.Need (SFac)

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
  (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L)) {nb : Tag → ℕ → ℕ}

/-- one batch on a given node -/
theorem sf_batOf {pv : Seed.Run W}
    (hpv : ∀ trees w fl xs,
      SFac (S := spec lam W.K L) (sp := split lam W.K L) (agree nb) (pv trees w fl xs))
    (i : I) (j : ℕ) (nd : Option (Node lam L)) (b : List (X × Unit)) :
    SFac (S := spec lam W.K L) (sp := split lam W.K L) (agree nb) (Seed.batOf WP pv i j nd b) :=
  (sf_drawT nb WP.perm).bind fun _ => by
    cases nd with
    | none => exact .pure _
    | some nd => exact (hpv _ _ _ _).bind fun _ => .pure _

variable (hW : W.NB nb)
  (hσ : ∀ q r r', agree (lam := lam) (K := W.K) (L := L) nb σ.o q r r' → r = r')
include hW hσ

/-- Under `W.NB nb` and hσ: C, P and V of `argP` go on in the same way after two answers that agree
on what is needed. -/
theorem facOK_argP : FacOK (agree nb) (argP W WP p bk σ) where
  C := fun i => by
    rw [argP_C]
    exact fun s =>
      OComp.FactorsBy.bind
        ((((facBy_C W WP p hW i).map _).blocks bk).derive σ s hσ 0) fun _ => trivial
  P := fun k b => by
    rw [argP_P]
    exact fun j =>
        OComp.FactorsBy.bind
            ((((sf_nodeP' (nb := nb) W WP p k.1).erase []).blocks bk).derive σ k.2 hσ _) fun a =>
      OComp.FactorsBy.bind (facBy_realQ W _
          ((sf_batOf W WP (fun _ _ _ _ => sf_proveBU nb _ _ _ _ _ _ _ _ _ _ _ _ _ hW.B _ _)
            k.1 j.val (some a.1) b).erase a.2)) fun _ => trivial
  V := fun v x π => facBy_V W p hW _ _ _

omit hW hσ

/-- For `Std m`: on every path the marked blocks of the queries of V add up to at most cVBN W nb. -/
theorem costBoundAt_V_argP (nb : Tag → ℕ → ℕ) {m : OracleCoding (spec lam W.K L) lam} (hm : Std m)
    (v : IVKK lam L) (x : X) (π : PrfK lam L) :
    ((argP W WP p bk σ).V v x π).CostBoundAt (needOf nb m).num (cVBN W nb) :=
  costBoundAt_V W nb hm p v.1 x (reK v.2 (liftK π))

end Need
end Compile.Batch
