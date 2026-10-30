-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/GoodOf.lean: the structure Good at a Seated side, at every pre, assembled from
its fields fits and fresh and from ExactAt, which gives its field exact. If Spec.sendExactAt and
Spec.sendFreshAt hold and the book is clear at the sender
(BookClear), the side has Good, with the fields plays and acc vacuous. It claims no property of the
protocol: not hiding, not zero knowledge.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean. Limits of the
folder: Johnson/SendSim/Defs.lean.

What this file proves.
  good_of_specs     Spec.sendExactAt and Spec.sendFreshAt imply: every Seated side has Good at every
                    book that is clear at the sender (BookClear), at On := True and the bound budAt,
                    with the predicates A and B that never hold, so that plays and acc hold
                    vacuously.
  good_of_fields    For any side: fits, ExactAt and FreshAt give Good, at every pre, with the
                    predicates A and B that never hold. ExactAt gives the field exact by dropping
                    the field's premise on the opened columns. The fields plays (the row can be
                    played) and acc (the verifier
                    accepts) then hold vacuously.
  place_of_seated   A side that Side.seated returns at a place a has its sub-protocol at a. So a
                    simulator with the address (a, 0) has the side's own address.

Limits.
Implications only: this file proves no equation between distributions by itself. The two premises of
good_of_specs that are named propositions are proved as sendExactAt in
Johnson/SendSim/At/ExactAt.lean and as sendFreshAt in Johnson/SendSim/At/FreshAtMember.lean. Seated
and BookClear stay premises (for BookClear see Johnson/SendSim/At/Fresh.lean, Limits).
A and B are not the framework's predicates: whoever substitutes those has plays and acc to prove.

How it fits. good_seated (Johnson/SendSim/At/FreshAtMember.lean) and good_at
(Johnson/SendSim/Seat/Row.lean) apply good_of_specs. good_of_fields also gives Good under the wider
condition (Johnson/SendSim/At/BookWide.lean) and in Johnson/SendSim/Seat/AtDescLots.lean, where it
serves Spec.handAtLots.
-/
import Johnson.SendSim.At.Fresh

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc

variable {S Cl V W X Pb : Type}

/-- The field fits, ExactAt and the field fresh (FreshAt) of a side give the structure Good with the
predicates A and B that never hold, so that the fields plays and acc hold vacuously.
pre is tied to no description; of Good's fields exact alone reads it, and at each pre that field
says no more than ExactAt. -/
theorem good_of_fields {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    {φ : Face V W Pb} {σ : Side S Cl V W X Pb} {Bk : ProverCoinCounts} {ord : List Place}
    {chain firstTree : Nat}
    {On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop}
    {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop} (hf : σ.fits = true)
    (he : ExactAt φ σ chain firstTree On bud) (hr : FreshAt φ σ Bk ord bud) :
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False) On bud :=
  ⟨hf, fun _ _ _ _ _ h => h.elim, fun _ _ _ _ _ h => h.elim,
    fun u hu ca m front ds asks hO hs _ => he u hu ca m front ds asks hO hs, hr⟩

/-- A side that Side.seated returns at a place a has its sub-protocol at the place a. -/
theorem place_of_seated {bs : List (Block S Cl)} {a : Place}
    {row : List (ProofFile.Honest.Part V W X × Sim Pb)} {fs : List (Fall S)} {σ : Side S Cl V W X Pb}
    (h : Side.seated bs a row fs = some σ) :
    σ.block.place = a := by
  unfold Side.seated at h
  cases hb : bs.find? fun b => b.place == a with
  | none => rw [hb] at h; cases h
  | some b =>
    rw [hb] at h
    have hp := List.find?_some hb
    cases h
    simpa using hp

/-- If Spec.sendExactAt and Spec.sendFreshAt hold, a side that is Seated at J has the structure Good
at every book that is clear at the sender (BookClear), at On := True, the bound budAt and predicates
A and B that never hold, so that plays and acc hold vacuously. The two premises are proved as
sendExactAt in Johnson/SendSim/At/ExactAt.lean and as sendFreshAt in
Johnson/SendSim/At/FreshAtMember.lean.
pre is tied to no description; of Good's fields exact alone reads it, and at each pre that field
says no more than ExactAt. -/
theorem good_of_specs {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    (He : Spec.sendExactAt) (Hr : Spec.sendFreshAt) (φ : Face V W Pb)
    (σ : Side S Cl V W X Pb) (J : SendJob W X) (Bk : ProverCoinCounts) (ord : List Place)
    (chain firstTree : Nat) (h : Seated σ J)
    (hB : BookClear J.P J.ride Bk ord ⟨σ.block.place, 0⟩) :
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      (fun _ _ _ _ => True) fun _ _ asks => budAt J.P asks :=
  good_of_fields h.fits (He S Cl V W X Pb φ σ J chain firstTree h)
    (Hr S Cl V W X Pb φ σ J Bk ord h hB)

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.good_of_fields
#print axioms OnBytes.SendSim.At.place_of_seated
#print axioms OnBytes.SendSim.At.good_of_specs
