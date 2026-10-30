-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/RecMain.lean: this file states the composition theorems of the holographic interactive oracle
proof: what follows for the composed protocol from hypotheses on its building blocks and on the
configuration.

Statements (the proofs: Hiop/RecMainProof.lean; that of `rec_soundAt`: Hiop/RecSoundProof.lean).
The object is `S.lhr`, the parameter lists, with `fitOff`
and `fitOn`, are `S.Hyp P`; `S.HypH P` is `S.Hyp P` without the items on knowledge soundness
(Hiop/RecBuild.lean); `C.Props b eR` is on the configuration (Hiop/RecConf.lean).

Main names:
  `Spec.rec_offline`: under `S.Hyp P`: the offline IOP, on statements (record, word) without a
    collision, has round-by-round knowledge soundness with the relaxation "the index decoder
    answers" (no witness); errors: those of the preamble followed by those of the IOPP.
    Completeness, at every value of the verifier's randomness outside `withheld` (`Honest.Acc`,
    Ior/Honest.lean); honest-verifier exact zero knowledge at the composed budget, at every value of
    the verifier's randomness outside `Hid` (`Honest.Exact`, Ior/Honest.lean).
  `Spec.rec_online`: under `C.Props b eR`, `S.Hyp P`: round-by-round knowledge soundness of a
    session, instance by instance, for each record, the same record in all slots; relation: the
    index decoder says none, or the cells extracted are a witness in Rno for the decoded index;
    errors: those of the preamble followed by those of the IOPP. Honest-verifier exact zero
    knowledge for sets of slots at the composed budget, on honest records (`validB`: and where
    `Ryes` holds), at every value of the verifier's randomness at which no slot of the set is in
    `Hid` (`BIOP.ExactT`, Ior/Batch.lean).
  `Spec.rec_soundAt`: under `C.Props b eR`, `S.Hyp P`: index binding with its numbers. The record
    clause has a number of its own, the configuration's eR: it is no entry of the offline list.
  `Spec.rec_honest`: under `C.Props b eR`, `S.HypH P`: completeness, formats, numbers of positions
    read, honest-verifier zero knowledge of each run: from the lists without their items on
    knowledge soundness.
  `Spec.rec_main`: under `C.Props b eR`, `S.Hyp P`, `P.Below εs`, eR ≤ εs · |Seed|: the object built
    in Hiop/RecBuild.lean has all properties of Hiop/RecInterface.lean (`PropsR`).





Limits: THE FACTOR N. On paper the theorem on a session is for the JOINT notion (some instance of
the batch): N times the preamble's errors, then the IOPP's. Here the list has
ONE-INSTANCE errors in the rounds of an instance and joint errors in the shared rounds
(Ior/KnowWide.lean: SndBKT): the preamble's errors stand WITHOUT the factor N. That is the paper's
lemma on one instance, and the list that the compiler takes; the fully joint list, with the factor
N, is not stated of a session in this library. What the library has, each under its hypotheses: the
step from `JointLaw` to `JointLawAll` at `Err.jointAll` (`BatchK.jointLawAll_of_jointLaw`,
Ior/BatchKProofs.lean) and the fully joint list for `SndBK` (`Spec.jointAll_of_sndBK`,
Ior/Batch.lean).
No hypothesis beside: `ConfigurationWithOutOfDomainSample.Props` (on the configuration), `SubsR.Hyp` (the parameter lists,
`fitOff`, `fitOn`; in `Spec.rec_honest` `SubsR.HypH` in its place), `Nums.Below` and the line for eR
(εs bounds the errors); and whatever the arguments hold
as proofs.
This file says nothing on zero knowledge of the whole object (any number of further encoded indices,
links and sessions within the budget, one record each): Hiop/RecWhole.lean. It says nothing on the
compiled argument.

Terms: lean/GLOSSARY.md.
-/
/- Limits: no theorem of this library states `S.Hyp P` of a concrete object, or that the hypotheses
   of `rec_main`, `rec_offline`, `rec_online` or `rec_honest` can be met together.



-/
import Hiop.RecBuild

set_option autoImplicit false

namespace Hiop
open Iop Prob
open scoped ENNReal

namespace Spec

/-- The offline phase: on statements (record, word) without a collision. -/
def rec_offline : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums), S.Hyp P →
    S.offline.red.Know C.free C.RwfR (fun _ _ => True)
      (fun _ _ (_ : Unit) => ()) (Err.app P.wf.err P.linOff.err) ∧
    S.hOffline.Acc C.Rwf IOR.triv ∧
    S.hOffline.Exact C.Rwf (IOR.budSeq S.wf S.linOff P.wf.bud P.linOff.bud)

/-- The online phase: for each record, with that record in all slots. -/
def rec_online : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums) (b eR : ℕ), C.Props b eR → S.Hyp P →
    (∀ rec : C.Rec, (S.session.toBatch.comap fun x => (x, rec)).SndBKT S.N id none
      (fun x y w => C.D y rec = none ∨ ∃ i, C.D y rec = some i ∧ C.Rno i x w)
      (fun x y τ => S.wit (x, rec) y τ) (Err.app P.req.err P.linOn.err)) ∧
    S.session.ExactT S.lhr.honestOnlineBatchProver S.N (S.lhr.validB fun i x => ∃ c, C.Ryes i x c)
      (budOnline S.req S.linOn P.req.bud P.linOn.bud)

/-- States: under the hypotheses below, index binding of the object, with its numbers: the record
clause has the configuration's eR and is no entry of a list; offline: the preamble's errors, then
the IOPP's; the link: `P.link.err`; a session: the preamble's, then the IOPP's. -/
def rec_soundAt : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums) (b eR : ℕ), C.Props b eR → S.Hyp P →
    S.lhr.SoundAtR C.Rno S.wit eR
      (Err.app P.wf.err P.linOff.err : Err (S.wf.shape ++ S.linOff.shape)) P.link.err
      (Err.app P.req.err P.linOn.err : Err (S.req.shape ++ S.linOn.ior.shape))

/-- States: under the hypotheses below, the honest side and the formats of the object, from the
lists without their items on knowledge soundness. -/
def rec_honest : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums) (b eR : ℕ) (εs : ℝ≥0∞),
    C.Props b eR → S.HypH P → S.lhr.PropsH (fun i x => ∃ c, C.Ryes i x c) (P.lh b εs)

/-- The theorem on the holographic IOP with records. -/
def rec_main : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums) (b eR : ℕ) (εs : ℝ≥0∞), C.Props b eR → S.Hyp P →
    P.Below εs → (eR : ℝ≥0∞) ≤ εs * (Fintype.card C.Seed : ℝ≥0∞) →
    S.lhr.PropsR C.Ryes C.Rno S.wit (P.lh b εs)

end Spec
end Hiop
