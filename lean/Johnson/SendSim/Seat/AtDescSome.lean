-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/AtDescSome.lean: if the maker of the proof file's description (ProofFile.onlineDescription)
succeeds, and the public part's first segment is not of the kind .head, then Side.seated returns a
side for the sender's row (sendRow, "our row") at the first segment's opening, and that side is
Seated.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file proves. The premises of the first two are IM.Open (the maker has succeeded), that the
public part has a segment number 0 (h0), and that this segment is not of the kind .head (hh).
  seatedAt_first_some For every wit, first, D and fs₀ there is a side that Side.seated returns from
                      F.first.blocksInOrder for our row at the opening's job, and it is Seated at that job.
                      So the premise hσ of seatedAt_first can be met, and that theorem is not
                      vacuous there.
  member_at_first     The first chain's list has a member at the opening's place. By chainBy_places.
  opening_in_places   If segment number 0 is not of the kind .head, the opening's place is among the
                      places that the description's driver lists (First.flatPlacesOf).
  seated_of_member    For any list of sub-protocols: if the list has a member at the place,
                      Side.seated returns a side.

Limits.
The two premises h0 and hh are not needed. stands_at_job (AtDescStands.lean) proves from IM.Open,
without them, that the list has a member at the opening's place, at each segment's reads and digits,
and at the place of the request's own table. The kind .head is excluded here because in a segment of
that kind the reply is at piece 1, and the opening's place is another.
That the maker succeeds at given public files is not proved here (see the Limits of AtDesc.lean).
The statements are about single values: no distribution is named.

How it fits. seatedAt_first and openJob are in AtDesc.lean, chainBy_places in
Johnson/Desc/ProofFile/Law/OrderCovered.lean. seated_of_member serves fieldsAtFirst_of_lots
(AtDescLots.lean) and fieldsAtOwn_of (AtDescOwn.lean). seatedAt_first_some serves Spec.fieldsAtFirst
(AtDescHand.lean), the earlier statement, which is only at the opening.
-/
import Johnson.SendSim.Seat.AtDesc
import Johnson.Desc.ProofFile.Law.OrderCovered

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At

variable {V W X Xi Pb : Type}

/-- If a list of sub-protocols has a member at the place a, Side.seated returns a side at a, for
every row. -/
theorem seated_of_member {S Cl : Type} {bs : List (Block S Cl)} {a : Place}
    (row : List (ProofFile.Honest.Part V W X × Sim Pb)) (fs : List (Fall S))
    (h : ∃ m ∈ bs, m.place = a) : ∃ σ : Side S Cl V W X Pb, Side.seated bs a row fs = some σ := by
  obtain ⟨m, hm, hp⟩ := h
  have h1 : (bs.find? fun b => b.place == a).isSome :=
    List.find?_isSome.2 ⟨m, hm, beq_iff_eq.2 hp⟩
  have h2 : (Side.seated bs a row fs).isSome := by
    unfold Side.seated
    rw [Option.isSome_map]
    exact h1
  exact Option.isSome_iff_exists.1 h2

/-- If segment number 0 is there (h0) and is not of the kind .head (hh), the opening's place is
among the places First.flatPlacesOf. -/
theorem opening_in_places {links : List First.ModelPart} {sub : First.ModelPart} (h0 : links[0]? = some sub)
    (hh : sub ≠ .head) (several : Bool) :
    (⟨1, some 0, 1, .K1⟩ : Place) ∈ First.flatPlacesOf links several := by
  unfold First.flatPlacesOf
  refine List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_flatMap.2 ⟨(sub, 0), List.mk_mem_zipIdx_iff_getElem?.2 (by simpa using h0), ?_⟩)))
  cases sub with
  | head => exact absurd rfl hh
  | layers => simp [First.linkPlaces, First.kindsBeforeBatching, First.addresses]
  | attention => simp [First.linkPlaces, First.kindsBeforeBatching, First.addresses]

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block First.S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- If the maker has succeeded (IM.Open), the public part has a segment number 0 (h0) and it is not
of the kind .head (hh), the first chain's list has a member at the opening's place. -/
theorem member_at_first (O : IM.Open o pol lay KL F Z Bs base c A B) {sub : First.ModelPart}
    (h0 : (ProofFile.subsOf Z)[0]? = some sub) (hh : sub ≠ .head) :
    ∃ m ∈ c.blocksInOrder, m.place = ⟨1, some 0, 1, .K1⟩ := by
  have h := opening_in_places h0 hh (base.any fun b => b.place.kind == KindName.K13)
  rw [← ProofFile.Law.chainBy_places O.chain] at h
  obtain ⟨m, hm, hp⟩ := List.mem_map.1 h
  exact ⟨m, hm, hp⟩

/-- If the maker has succeeded (IM.Open), the public part has a segment number 0 (h0) and it is not
of the kind .head (hh), then for every wit, first, D and fs₀ there is a side that Side.seated
returns from the description's first chain for our row at the opening's job, and it is Seated at
that job.
-/
theorem seatedAt_first_some (O : IM.Open o pol lay KL F Z Bs base c A B) {sub : First.ModelPart}
    (h0 : (ProofFile.subsOf Z)[0]? = some sub) (hh : sub ≠ .head) (wit : W → PlaceIn Xi) (first : Nat)
    (D : RowDataOf Xi) (fs₀ : List (Fall F.S₁)) :
    ∃ σ₀ : Side F.S₁ F.Cl V W X Pb,
      Side.seated F.first.blocksInOrder (sendRow (V := V) (Pb := Pb)
                   (openJob (X := X) Z Bs.G₀ first D).P.place
                   (jobOver (openJob (X := X) Z Bs.G₀ first D) wit)).place
        (sendRow (V := V) (Pb := Pb) (openJob (X := X) Z Bs.G₀ first D).P.place
          (jobOver (openJob (X := X) Z Bs.G₀ first D) wit)).row fs₀ = some σ₀ ∧
      Seated σ₀ (jobOver (openJob (X := X) Z Bs.G₀ first D) wit) := by
  have hm : ∃ m ∈ F.first.blocksInOrder, m.place = (sendRow (V := V) (Pb := Pb)
               (openJob (X := X) Z Bs.G₀ first D).P.place
               (jobOver (openJob (X := X) Z Bs.G₀ first D) wit)).place := by
    have e := O.desc
    subst e
    exact member_at_first O h0 hh
  obtain ⟨σ₀, hσ⟩ := seated_of_member _ fs₀ hm
  exact ⟨σ₀, hσ, seatedAt_first O wit first D hσ⟩

end

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.member_at_first
#print axioms OnBytes.SendSim.Seat.seatedAt_first_some
