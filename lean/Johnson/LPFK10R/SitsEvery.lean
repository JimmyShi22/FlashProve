-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK10R/SitsEvery.lean: THE ROW K10_sits FOR THE FIRST CHAIN, OVER THE PLACES OF THE KIND, WITH NO PREMISE ON SCOPE, AT EVERY o FOR THE SECOND HASH FUNCTION AND AT ANY ROW OF SEGMENTS.
WHY. k10_sits_each (SitsAll.lean, beside this file) runs over every block of the first chain's flat list whose place is of the kind K10, but in scope, at OnBytes.secondHashFunction, at the 25 sorts: its table of places is one evaluation by the
kernel there. k10_sits_alone (SitsO.lean) has no scope and a letter o, but runs over the links. Another file types what joins the two: Johnson/Desc/ProofFile/Law/KindPlaces.lean:
k10_places (a place of the kind K10 in the driver's table is the second place of the closing of a segment l) and flatPlaces_nodup (no place stands twice in that table): general in the row of segments.
  nodup_ix          in a list without a double a member has one number.
  k10_sits_every    O : Open o pol lay KL F Z Bs base c A B (o a letter) · HeadIsTwo Z: AT EVERY BLOCK b OF c.blocksInOrder WHOSE PLACE IS OF THE KIND K10: l, sub, Lk, p, Q: (ProofFile.subsOf Z)[l]? = some sub · c.links[l]? = some Lk ·
                    k9At Z l = some p · ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q · Lk.close[1]? = some b · LaidAlone ProofFile.sameReply b (K9.closing Q).retype b.name (cAt l sub 1 K10).
  k10_law_every     and K10LawAt b Q (SitsLaw.lean): the law at the piece of that very block.
LIMITS. (1) HeadIsTwo Z is a premise: shown in scope, at secondHashFunction (head_is_two). (2) That onlineDescription returns is a premise (Open). (3) THE FIRST CHAIN ALONE: that no block of the two later chains is of the kind is
typed elsewhere (Johnson/Desc/ProofFile/Law/LaterKinds.lean: no_k10_later): not joined here. The key file: not here. (4) All limits of Sits.lean and SitsLaw.lean but scope, size and secondHashFunction. Nothing on soundness.
Statements and proofs.
-/
import Johnson.LPFK10R.SitsO
import Johnson.LPFK10R.SitsAll
import Johnson.Desc.ProofFile.Law.KindPlaces

set_option autoImplicit false

namespace LPFK10
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S ModelPart flatPlacesOf flat_places)
open VerifiableInference.Desc.First.Close (Par K10LawAt k10LawAt_of)
open ProofFile (Cl)
open IM

/-- In a list without a double a member has one number. -/
theorem nodup_ix {α : Type} {l : List α} (h : l.Nodup) {i j : ℕ} {a : α} (hi : l[i]? = some a)
    (hj : l[j]? = some a) : i = j := by
  obtain ⟨hi', ei⟩ := List.getElem?_eq_some_iff.1 hi
  obtain ⟨hj', ej⟩ := List.getElem?_eq_some_iff.1 hj
  exact (List.Nodup.getElem_inj_iff h).1 (ei.trans ej.symm)

variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **K10_sits at every place of the kind in the first chain: no scope; every o; any size.** -/
theorem k10_sits_every (O : Open o pol lay KL F Z Bs base c A B) (hk2 : HeadIsTwo Z) :
    ∀ b ∈ c.blocksInOrder, b.place.kind = KindName.K10 →
      ∃ (l : ℕ) (sub : ModelPart) (Lk : Link S Cl) (p : VerifiableInference.Desc.K9.Where) (Q : Par),
        (ProofFile.subsOf Z)[l]? = some sub ∧ c.links[l]? = some Lk ∧ k9At Z l = some p ∧
        ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q ∧ Lk.close[1]? = some b ∧
        LaidAlone ProofFile.sameReply b
          (VerifiableInference.Desc.K9.closing Q : Block S Unit).retype b.name
          (cAt l sub 1 KindName.K10) := by
  intro b hb hk
  obtain ⟨H, several, hf⟩ := chain_first O
  have hp := flat_places H _ several c hf
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hb
  have hpi : (flatPlacesOf (ProofFile.subsOf Z) several)[i]? = some b.place := by
    rw [← hp, List.getElem?_map, hi]
    rfl
  obtain ⟨l, sub, hsub, e⟩ := ProofFile.Law.k10_places _ several i b.place hpi hk
  obtain ⟨Lk, p, Q, b1, h1, h2, h3, h4, h5⟩ := k10_sits_alone O hk2 l sub hsub
  obtain ⟨j, h6⟩ : ∃ j, c.blocksInOrder[j]? = some b1 := ⟨_, link_at_flat h1 (close_at_flat h4)⟩
  have hp1 : (flatPlacesOf (ProofFile.subsOf Z) several)[j]? = some b1.place := by
    rw [← hp, List.getElem?_map, h6]
    rfl
  have e1 : b1.place = b.place := by
    rw [alone_place h5, e]
  rw [e1] at hp1
  have hij := nodup_ix (ProofFile.Law.flatPlaces_nodup _ several) hpi hp1
  rw [← hij] at h6
  obtain rfl : b = b1 := Option.some.inj (hi.symm.trans h6)
  exact ⟨l, sub, Lk, p, Q, hsub, h1, h2, h3, h4, h5⟩

/-- **And the law at that very block.** -/
theorem k10_law_every (O : Open o pol lay KL F Z Bs base c A B) (hk2 : HeadIsTwo Z) :
    ∀ b ∈ c.blocksInOrder, b.place.kind = KindName.K10 →
      ∃ (l : ℕ) (p : VerifiableInference.Desc.K9.Where) (Q : Par),
        k9At Z l = some p ∧ ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q ∧ K10LawAt b Q := by
  intro b hb hk
  obtain ⟨l, sub, Lk, p, Q, -, -, h2, h3, -, h5⟩ := k10_sits_every O hk2 b hb hk
  exact ⟨l, p, Q, h2, h3, k10LawAt_of h5 (by simp)⟩

end LPFK10

#print axioms LPFK10.nodup_ix
#print axioms LPFK10.k10_sits_every
#print axioms LPFK10.k10_law_every
