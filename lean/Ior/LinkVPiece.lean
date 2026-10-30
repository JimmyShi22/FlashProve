-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/LinkVPiece.lean: a block for one instance as a piece of a chain of batch links: run in every
slot, or run by the shared part alone.

In standard terms: an interactive oracle reduction for one instance, run in every instance of a
batch or once for all, as one step of a sequential composition.

Statements and proofs; they only put the rules of Ior/LinkVRules.lean together into the bundle of
Ior/LinkVBears.lean (`PieceV`). No protocol occurs here.

A block is an IOR R (Ior/Ior.lean) with its honest side H (`IOR.Honest`, Ior/Honest.lean), taken
as a part of a chain. A batch link is an IOR with an annotation of its shape (`RoundSplits`,
Iop/Batch.lean) and an honest side (`IOR.HonestV`, Ior/LinkV.lean). What a slot is: the head of
Ior/LinkVBears.lean.

Main names:
  `Spec.pieceV_local`: local, complete, honest-verifier exactly zero knowledge (`Honest.Exact`,
    Ior/Honest.lean), nothing hidden withheld (all for one instance); the link's relations RiV,
    RoV (the one-instance relations and the tie to the shared witness, which honest runs carry);
    the link bears what follows, at the budget "each slot's". Then `H.localV W0` is a piece.
  `Spec.pieceV_shared`: the same for `H.sharedV s0`; asked beside: on RiV the one-instance
    prover's transcript is that of the shared strategy s0; the symbols that the simulator is given
    are determined by the shared witness; the budget is "at the union".

No premise of its own is asked on ties (`PieceV` has no field `noTie`, as `IOR.Piece`,
Ior/Tail.lean, has, and no field `tied`, as `IOR.TailTr`, Cb/Ld/LdTowerKit.lean, has): a block whose
oracles are tied to positions of its input (a whole proximity test) is taken as it is; what is tied
is among what the simulator is given (`IOR.given`, Ior/Honest.lean), and so in the demand on the
input's positions, and in the premise of `Spec.pieceV_shared` on `p ∈ R.given ρ T`.

Terms: lean/GLOSSARY.md.
-/
import Ior.LinkVBears

set_option autoImplicit false

namespace Iop
open Prob

namespace Spec
open IOR

def pieceV_local : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (Wi Wo W0 : Type) (H : R.Honest Wi Wo)
      (Ri : X → Ei.Str → Wi → Prop) (Ro : X' → Eo.Str → Wo → Prop)
      (RiV : X → Ei.Str → W0 × Wi → Prop) (RoV : X' → Eo.Str → W0 × Wo → Prop)
      (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (N : ℕ) (qi : QFam Ei N) (qo : QFam Eo N),
    R.IsLocal → H.Acc Ri Ro → H.Exact Ri bud →
    (∀ w x, H.Hid w x = ∅) → (∀ x y w, RiV x y w → Ri x y w.2) →
    (∀ x y w c ρ, RiV x y w → ρ ∉ H.Bad →
      Ro ((H.strat w.2 x c).run ρ).2.1 (R.imp y ((H.strat w.2 x c).run ρ).1)
        ((H.strat w.2 x c).run ρ).2.2 →
      RoV ((H.strat w.2 x c).run ρ).2.1 (R.imp y ((H.strat w.2 x c).run ρ).1)
        (w.1, ((H.strat w.2 x c).run ρ).2.2)) →
    R.BearsV (RoundSplits.allLocal R.shape) (fun J ρs Ts => ∀ j : J, bud (ρs j) (Ts j)) qi qo →
    PieceV R (RoundSplits.allLocal R.shape) (H.localV W0) N RiV RoV
      (fun J ρs Ts => ∀ j : J, bud (ρs j) (Ts j)) qi qo

open Classical in
def pieceV_shared : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (Wi Wo W0 W0' : Type) (H : R.Honest Wi Wo)
      (s0 : W0 → H.Coin → Strat R.shape W0') (Ri : X → Ei.Str → Wi → Prop)
      (Ro : X' → Eo.Str → Wo → Prop) (RiV : X → Ei.Str → W0 × Wi → Prop)
      (RoV : X' → Eo.Str → W0' × Wo → Prop) (bud : Rho R.shape → Finset (OPos R.shape) → Prop)
      (N : ℕ) (f : W0 → Ei.Pos → Ei.Sym) (qi : QFam Ei N) (qo : QFam Eo N),
    R.IsLocal → H.Acc Ri Ro → H.Exact Ri bud → (∀ w x, H.Hid w x = ∅) →
    (∀ x y w, RiV x y w → Ri x y w.2) →
    (∀ x y w c ρ, RiV x y w → ((H.strat w.2 x c).run ρ).1 = ((s0 w.1 c).run ρ).1) →
    (∀ x y w c ρ, RiV x y w → ρ ∉ H.Bad →
      Ro ((H.strat w.2 x c).run ρ).2.1 (R.imp y ((H.strat w.2 x c).run ρ).1)
        ((H.strat w.2 x c).run ρ).2.2 →
      RoV ((H.strat w.2 x c).run ρ).2.1 (R.imp y ((H.strat w.2 x c).run ρ).1)
        (((s0 w.1 c).run ρ).2, ((H.strat w.2 x c).run ρ).2.2)) →
    (∀ x y w ρ T p, RiV x y w → p ∈ R.given ρ T → Ei.rd y p = f w.1 p) →
    R.BearsV (RoundSplits.const (RAnn.ofShared .sh) R.shape)
      (fun J ρs Ts => ∀ j : J, bud (ρs j) (Finset.univ.biUnion Ts)) qi qo →
    PieceV R (RoundSplits.const (RAnn.ofShared .sh) R.shape) (H.sharedV s0) N RiV RoV
      (fun J ρs Ts => ∀ j : J, bud (ρs j) (Finset.univ.biUnion Ts)) qi qo

end Spec

open IOR

theorem pieceV_local :
    Spec.pieceV_local := fun X X' Ei Eo R Wi Wo W0 H Ri Ro RiV RoV bud N _ _ hl ha he hh hi ho hb =>
  { isLocal := hl
    acc := accV_local X X' Ei Eo R Wi Wo W0 H Ri Ro RiV RoV ha hh hi ho
    exact := exactV_local X X' Ei Eo R Wi Wo W0 H Ri RiV bud N he hh hi
    bears := hb }

theorem pieceV_shared :
    Spec.pieceV_shared := fun X X' Ei Eo R Wi Wo W0 W0' H s0 Ri Ro RiV RoV bud N f _ _ hl ha he hh hi hag ho hf hb =>
  { isLocal := hl
    acc := accV_shared X X' Ei Eo R Wi Wo W0 W0' H s0 Ri Ro RiV RoV ha hh hi hag ho
    exact := exactV_shared X X' Ei Eo R Wi Wo W0 W0' H s0 Ri RiV bud N f he hh hi hag hf
    bears := hb }

end Iop
