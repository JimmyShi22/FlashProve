-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/SmpOfFence.lean: code switching, the fifth tie: OF THE STRUCTURE K2Owes
(Johnson/Top/H0/K2Ties/T5.lean) THE FIELD smp FOLLOWS FROM THE FIELD fence, where the reader of OOD
samples is the named one at the laid list's places. NO SUB-PROTOCOL IMPORTS THIS FILE.
WHY. smp_of_named (K2Ties/SmpLeft.lean) has the field smp from «inside the fence a sampled message
stands at the fixed number of each member at the index masks' tenant»: a premise there. The facts on
reached states that the field fence names (IndexFence, K2Ties/Pile.lean) hold already that the
state's book follows the laid list and is in step with the statement; the fence's own promise holds
that the sample at the index masks' tenant is held. named_there_mem (Tw/K2C/NamedThere.lean) joins
the two.
  placesAre_of_seats   seatsCarriedB L B and «in step» give placesAre L.places st B
                       (Johnson/Desc/Sound/SmpPlaces.lean)
  held_in_fence        inside the fence the sample at the index masks' tenant is held, where that
                       tenant is among the sampled ones that stand open at the border
  smp_of_fence         THE STATEMENT: the field smp, to the letter
LIMITS. Three premises stay: the reader IS smpNamed at L.places · the index masks' tenant is among
the sampled ones at the border · the field fence. No soundness is claimed.
-/
import Johnson.Top.H0.K2Ties.SmpLeft
import Johnson.Top.H0.Tw.K2C.NamedThere
import Johnson.P1K2R.TieTwoS
import Johnson.Desc.K12.Door.DoorGives

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1Named
open VerifiableInference.Desc (placesAre)
open VerifiableInference.Desc.K12.Door (Laid seatsCarriedB place_of_seats)

theorem placesAre_of_seats {L : Laid} {B : OnBytes.TreeBook} {st : OnBytes.Statement}
    (h : seatsCarriedB L B = true) (hs : B.place.size = st.oracles.size) :
    placesAre L.places st B = true := by
  have hle : B.place.size ≤ L.places.length := by
    have h' := h
    unfold seatsCarriedB at h'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
    exact h'.1.1.2
  unfold placesAre
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true, List.mem_range]
  exact ⟨⟨hle, hs.symm⟩, fun k hk => place_of_seats h k hk⟩

end P1Named

namespace VerifiableInference.Desc.First.K2Ties
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc (Place smpHeld)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Meaning onAt sampledIn)
open VerifiableInference.Desc.K12.Door (Laid)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public} {Fr : Frame}

theorem held_in_fence (D : MgData Xi P Tok rows cols nR X) (Mg₀ : Meaning P (Wq rows cols Tok))
    (links : List ModelPart) (ps : List Place) (k : ℕ) (z : P) (Rch : First.S × Fr.E.Str → Prop)
    (hidx : D.N.index ∈ sampledIn D.N (IM.openAt links ps k)) (a : First.S × Fr.E.Str)
    (ha : fenceAt D Mg₀ links ps k z Rch a) :
    smpHeld a.1.st a.1.book D.N.index.1 D.N.index.2 = true := by
  have ha' : onAt D.N (mgAll D Mg₀) links ps[k]? (IM.openAt links ps k)
      (P1K2.pubAt (mgAll D Mg₀) links ps k) (z, a.1) (strsOf Fr a.2) := ha.1
  exact P1K2.held_of_on ha' ha.2.2 hidx

/-- **The field smp of K2Owes, from its field fence.** -/
theorem smp_of_fence (D : MgData Xi P Tok rows cols nR X) (Mg₀ : Meaning P (Wq rows cols Tok))
    (links : List ModelPart) (ps : List Place) (k : ℕ) (z : P) (Rch : First.S × Fr.E.Str → Prop)
    {M : List OnBytes.OracleShape} {L : Laid} (hD : D.smp = smpNamed D.cs L.places)
    (hidx : D.N.index ∈ sampledIn D.N (IM.openAt links ps k))
    (hF : ∀ a : First.S × Fr.E.Str, fenceAt D Mg₀ links ps k z Rch a → IndexFence D.N M L a.1) :
    ∀ (a : First.S × Fr.E.Str) (s' : First.S), fenceAt D Mg₀ links ps k z Rch a → Left a.1 s' →
      ∀ x ∈ D.ms, SitsAt x D.N.index.1 D.N.index.2 →
        D.smp (z, s') x.1 x.2 = D.smp (z, a.1) x.1 x.2 :=
  smp_of_named D Mg₀ links ps k z Rch L.places hD fun a ha x _ hs =>
    P1Named.named_there_mem (P1Named.placesAre_of_seats (hF a ha).seats (hF a ha).step)
      (held_in_fence D Mg₀ links ps k z Rch hidx a ha) x hs

end VerifiableInference.Desc.First.K2Ties

#print axioms P1Named.placesAre_of_seats
#print axioms VerifiableInference.Desc.First.K2Ties.held_in_fence
#print axioms VerifiableInference.Desc.First.K2Ties.smp_of_fence
