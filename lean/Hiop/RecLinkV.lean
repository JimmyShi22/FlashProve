-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/RecLinkV.lean: this file has one bridging lemma on the honest prover of the batched test for
linear constraints: from the form in which such a prover is built, a chain of reductions, to the
list of hypotheses on that test, knowledge soundness apart, that the composition theorems take.

A statement and its proof. No protocol, no code: any configuration with a record, any "what a
preamble leaves" (`ConfigurationWithOutOfDomainSample`, `ConfigurationWithOutOfDomainSample.Left`, Hiop/RecConf.lean).

Why: Hiop/RecSubs.lean asks of the IOPP for the constraint relation at N instances a list without
knowledge soundness (`LinBListR`): formats, completeness for each slot, the probability of the
public withheld set, exact zero knowledge for sets of slots, `bud0`, and what is read of the encoded
index. Such a test is built as a chain of batch links (Ior/LinkV.lean: a run in every slot, a run by
the shared part alone, one link after the other), from a relation of the chain's own on (shared
witness, the slot's whole witness). This file joins the two.

Main names:
  `Spec.rec_linB_list`: a link H to the trivial statement on the batch IOP's own IOR and annotation,
    whose shared witness at the start is the prover encoded index with its record; complete (`AccV`,
    Ior/LinkV.lean) and exactly zero knowledge for sets of slots (`ExactV`, Ior/LinkV.lean) from
    RiV, at a budget that bears "no further reads"; one bridging fact: the constraint relation gives
    RiV at the slot witness `mk`; and the format items, which are properties of the IOR and its
    annotation alone (strings (`IsPoint`), local, coherent, tied, what is read of the encoded
    index); and `prRho H.withheld ≤ P.pBad`. Then `LinBListR` holds of the batch IOP with the honest
    side `H.toB mk`.

Limits: no chain is given. This file says nothing on knowledge soundness: Cb/Obj/LdObjectBatch.lean.

Terms: lean/GLOSSARY.md.
-/
import Hiop.RecBuild
import Ior.LinkVRules

set_option autoImplicit false

namespace Hiop
open Iop Prob IOR
open scoped ENNReal

namespace Spec

open Classical in
def rec_linB_list : Prop :=
  ∀ (C : ConfigurationWithOutOfDomainSample) (S : C.Left) (R : IOR (S.Xl × C.Rec) S.El Unit extNone) (A : RoundSplits R.shape)
      (Wi W0' Wo : Type) (H : R.HonestV A C.PIdx Wi W0' Wo) (mk : C.PIdx → S.WAux → Wi)
      (RiV : S.Xl × C.Rec → S.El.Str → C.PIdx × Wi → Prop)
      (RoV : Unit → extNone.Str → W0' × Wo → Prop) (N : ℕ) (P : LinBNums R.shape N),
    Nonempty R.shape.IsPoint → R.IsLocal → A.Coherent → R.Tied →
    (∀ ρ ρ', Rho.sh A ρ = Rho.sh A ρ' →
      (R.extReads ρ).filter (fun p => p.isLeft) = (R.extReads ρ').filter (fun p => p.isLeft)) →
    (∀ ρ, ((R.extReads ρ).filter fun p => p.isLeft).card ≤ P.q) → H.AccV RiV RoV →
    H.ExactV N RiV P.bud → (∀ J ρs, P.bud J ρs fun _ => ∅) → prRho H.withheld ≤ P.pBad →
    (∀ x y w, S.Rlin x y w → RiV x y (w.1, mk w.1 w.2)) → LinBListR S ⟨R, A⟩ (H.toB mk) N P

end Spec

theorem rec_linB_list : Spec.rec_linB_list := by
  classical
  intro C S R A Wi W0' Wo H mk RiV RoV N P hp hl hc ht hsh hq hacc hex hb0 hbad hR
  exact
    { point := hp
      isLocal := hl
      coherent := hc
      acc := fun x y w c ρ hw hρ =>
        acc_toB _ _ _ R A _ _ _ _ _ H mk RiV RoV hacc x y w c ρ (hR x y w hw) hρ
      prBad := hbad
      exact := by
        obtain ⟨Sm, hS⟩ := exact_toB _ _ _ R A _ _ _ _ _ H mk RiV N P.bud hex
        exact ⟨Sm, fun w0 y0 a ha => hS w0 y0 a fun j aj hj => hR _ _ _ (ha j aj hj)⟩
      bud0 := hb0
      tied := ht
      idxShared := hsh
      idxReads := hq }

end Hiop
