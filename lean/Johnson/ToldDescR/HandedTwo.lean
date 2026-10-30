-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/HandedTwo.lean: no soundness is claimed.
(H1) of the last chain's ledger: which messages the own group holds that the first chain hands on, and at which seats: spent out of the first table's promise at its last border, which the last table's promise bears as its first clause (as HandedAtEnd.lean).
  ownSits_at       ocEnd … p y · no mark · FillsOwnSits Mg₁ V · «K13.ownSits» is open at the last border · firstOfS (get p).2 = some f ⇒ OwnSits V f
  seat_of_place    in a book whose tree at place z bears the number z: a message's seat (tree's number, part: seatBy noFirst) is its place, where the tree is there
  HandedTwo wI wW sI sW f   the sharper sentence: the handed own group's members are #[i₁, i₂]; i₁ sits at the seat wI with the shape sI, i₂ at wW with sW
  **handedTwo_at**  inside the last table's promise at any border k (Oc := ocEnd … · Mg := tiedMeaning get Mg₁ MgS): FillsOwnSits · FillsK12 at ft = 0 · both items and «K12.bookFits» open at the last border ⇒ HandedTwo V.index V.w V.indexShape V.wShape f
  **handedSits_of_two**  HandedTwo … f and two tests on «mine» (one of mine sits at each of the two seats with that shape) ⇒ HandedSits mine f (Johnson/LLT25R/LastSeamEnds.lean's sentence, typed out here so that this file stands beneath it)
Left, by name. On the table: the three items are open at the first chain's last border. Of make: FillsOwnSits Mg₁ V · FillsK12 Mg₁ d · d.ft = 0. On the plan: the two tests on mine.
Does not show. That «K13.ownSits» is earned or kept: not typed here. No member. Nothing on soundness.
-/
import Johnson.ToldDescR.HandedAtEnd
import Johnson.Desc.First.FillOwnSits
import Johnson.Desc.Sound.TabAt
import Johnson.Desc.Sound.BookTestsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open OnBytes OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.First (ModelPart Meaning Numbers pubSets moreItem nSits FillsOwnSits)
open VerifiableInference.Desc.Third (S₃ SharedOut firstOfS)
open VerifiableInference.Desc.K12.Door (FillsK12 K12Data nBook nFits)
open VerifiableInference.Desc.Book (BookFits)

section
variable {A P₀ W : Type} (get : A → P₀ × First.S) (N₁ : Numbers) (Mg₁ : Meaning P₀ W)
  (links : List ModelPart) (ps : List Place)

/-- The item, spent at the first chain's last border. -/
theorem ownSits_at (V : OwnSeats) (hV : FillsOwnSits Mg₁ V)
    (hq : moreItem nSits ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD []) (p : A) (y : Strs)
    (h : ocEnd get N₁ Mg₁ links ps p y) (hm : (get p).2.failed = none) {f : Handed}
    (hf : firstOfS (get p).2 = some f) : OwnSits V f := by
  have hb := ocEnd_pub get N₁ Mg₁ links ps p y h hm _ hq
  rw [hV.sits] at hb
  exact (ownSitsB_iff V _).1 hb f hf

/-- "K12.bookFits", spent there. -/
theorem fits_at (d : K12Data) (hM : FillsK12 Mg₁ d)
    (hq : moreItem nFits ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD []) (p : A) (y : Strs)
    (h : ocEnd get N₁ Mg₁ links ps p y) (hm : (get p).2.failed = none) {f : Handed}
    (hf : firstOfS (get p).2 = some f) : BookFits f.book := by
  have hb := ocEnd_pub get N₁ Mg₁ links ps p y h hm _ hq
  rw [hM.fits] at hb
  have hb' : bookFitsB (get p).2.book = true := hb
  unfold firstOfS at hf
  obtain ⟨e, _, rfl⟩ := Option.map_eq_some_iff.1 hf
  exact (bookFitsB_iff _).1 hb'

end

/-- In a book that fits and whose tree at place z bears the number z, a message's seat is its
place. -/
theorem seat_of_place {B : TreeBook} (hF : BookFits B)
    (hN : ∀ (j : ℕ) (T : Tree), B.trees[j]? = some T → T.number = j) {i : ℕ} {q : ℕ × ℕ}
    (hq : B.place[i]? = some q) : seatBy noFirst B i = some q := by
  obtain ⟨T, hT, _⟩ := hF i q hq
  unfold seatBy
  rw [hq]
  show (B.trees[q.1]?).map (fun T => (noFirst q.1 T, q.2)) = some q
  rw [hT]
  show some (T.number, q.2) = some q
  rw [hN q.1 T hT]

/-- **The sharper sentence**: which two, in which order, at which seats, with which shapes. -/
def HandedTwo (wI wW : ℕ × ℕ) (sI sW : OracleShape) (f : Handed) : Prop :=
  ∃ (G : Group) (i₁ i₂ : ℕ), f.st.groups[f.own]? = some G ∧ G.members.toList = [i₁, i₂] ∧
    seatBy noFirst f.book i₁ = some wI ∧ seatBy noFirst f.book i₂ = some wW ∧
    (f.st.oracles[i₁]?).map (·.shape) = some sI ∧ (f.st.oracles[i₂]?).map (·.shape) = some sW

theorem handedTwo_of_sits {V : OwnSeats} {f : Handed} (h : OwnSits V f) (hF : BookFits f.book)
    (hN : ∀ (j : ℕ) (T : Tree), f.book.trees[j]? = some T → T.number = j) :
    HandedTwo V.index V.w V.indexShape V.wShape f := by
  obtain ⟨G, i₁, i₂, hG, hm, h1, h2, h3, h4⟩ := h
  exact ⟨G, i₁, i₂, hG, hm, seat_of_place hF hN h1, seat_of_place hF hN h2, h3, h4⟩

section
variable {P S₁ S₂ P₀ Wt : Type} {Fr : Frame} (get : P × S₁ → P₀ × First.S) (N₁ : Numbers)
  (Ns : NumbersS) (Mg₁ : Meaning P₀ Wt) (MgS : MeaningS S₂ (P × S₁) Wt) (Pm : PromMeaning S₂)
  (PL : PromMeaningL S₂ S₃ (P × S₁)) (links : List ModelPart) (ps : List Place)

/-- **`HandedTwo` inside the last table's promise.** -/
theorem handedTwo_at (V : OwnSeats) (hV : FillsOwnSits Mg₁ V) (d : K12Data) (hM : FillsK12 Mg₁ d)
    (h0 : d.ft = 0)
    (hqS : moreItem nSits ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD [])
    (hqB : moreItem nBook ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD [])
    (hqF : moreItem nFits ∈ (pubSets Mg₁.more links ps)[ps.length]?.getD []) (k : ℕ)
    (a : ((P × S₁ × S₂) × S₃) × Fr.E.Str)
    (ha : onQ₃ (Fr := Fr) (tiedNumbers N₁ Ns) (tiedMeaning get Mg₁ MgS) Pm PL
      (ocEnd get N₁ Mg₁ links ps) k a)
    {f : Handed} (hf : firstOfS (get (a.1.1.1, a.1.1.2.1)).2 = some f) :
    HandedTwo V.index V.w V.indexShape V.wShape f := by
  have hS := ownSits_at get N₁ Mg₁ links ps V hV hqS _ _ ha.1 ha.2.1 hf
  have hF := fits_at get N₁ Mg₁ links ps d hM hqF _ _ ha.1 ha.2.1 hf
  obtain ⟨-, hN⟩ := handed_two get N₁ Mg₁ links ps d hM hqB _ _ ha.1 ha.2.1 hf
  exact handedTwo_of_sits hS hF fun j T hT => by rw [hN j T hT, h0, Nat.zero_add]

end

/-- **(H1)**, from the sharper sentence and two tests on "mine". -/
theorem handedSits_of_two {wI wW : ℕ × ℕ} {sI sW : OracleShape} {f : Handed}
    (h : HandedTwo wI wW sI sW f) (mine : List Mem)
    (hI : ∃ x ∈ mine, seatOf x = wI ∧ (x.1.l.get x.2).1 = sI)
    (hW : ∃ x ∈ mine, seatOf x = wW ∧ (x.1.l.get x.2).1 = sW) :
    ∀ Gh, f.st.groups[f.own]? = some Gh → ∀ i ∈ Gh.members.toList, ∃ x ∈ mine,
      seatBy noFirst f.book i = some (seatOf x) ∧
        (f.st.oracles[i]?).map (·.shape) = some (x.1.l.get x.2).1 := by
  obtain ⟨G, i₁, i₂, hG, hm, h1, h2, h3, h4⟩ := h
  intro Gh hGh i hi
  obtain rfl : G = Gh := Option.some.inj (hG.symm.trans hGh)
  rw [hm] at hi
  rcases List.mem_cons.1 hi with rfl | hi
  · obtain ⟨x, hx, e1, e2⟩ := hI
    exact ⟨x, hx, by rw [e1]; exact h1, by rw [e2]; exact h3⟩
  · obtain rfl : i = i₂ := by simpa using hi
    obtain ⟨x, hx, e1, e2⟩ := hW
    exact ⟨x, hx, by rw [e1]; exact h2, by rw [e2]; exact h4⟩

end ToldDesc

#print axioms ToldDesc.ownSits_at
#print axioms ToldDesc.fits_at
#print axioms ToldDesc.seat_of_place
#print axioms ToldDesc.handedTwo_at
#print axioms ToldDesc.handedSits_of_two
