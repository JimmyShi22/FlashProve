-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/Tied.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS, AT THE PROOF FILE's DESCRIPTION:
OVER A VERSION OF THE FILES BELOW IT, WITH ANOTHER
FILE OF ProofFile's LAID OVER. JOININGS, after the pattern of Johnson/K11R/Tied.lean (the merge's).
WHAT IS SAID.
  ixOf l            the number, in the first chain's flat list, of the kind's block at link l: 14 l + 6; at the head's link (24): 343.
  k08_tied_at       at an opening's letters, for three rows of pieces that hold the description's blocks (OfDesc): where a block b of link l, number i among the link's blocks in front of the batching, is the lot's block B₀ ALONE at an address that is not K7's, and stands at number k of the flat list: the piece at number k of the first row, with an extractor that lays nothing, is TiedBy at the table's own words, IF SeatLaws holds at B₀. General in the kind.
  k08_tied          in scope: THAT AT ALL 25 PLACES OF THE KIND: at link l ≤ 24, with Xl the built link: the piece at number ixOf l is TiedBy, IF SeatLaws holds at K8.whole (k8ParW Z G₀ Xl l).
  k8AllB_full · k8_places_full     by Lean's kernel (decide +kernel): in the written list of places of the full size the kind K8 stands at the numbers ixOf l, l ≤ 24, alone.
  k08_kindTied      THE KIND K8's SHARE OF THE CHAIN OF PROMISES (KindTied … K8, Johnson/Desc/Sound/TiedPlaces.lean), under SeatLaws at the constant at each of the 25 places.
WHAT STANDS WHERE. That the block at the place is the lot's block alone: in Johnson/IMR/ (K8Seat.lean: k8_of_layers | k8_of_attention | k8_of_head; SeatForm.lean; FlatIx.lean | FlatScope.lean). The rule from SeatLaws to TiedBy, OfDesc.pieceAt, KindTied: in Johnson/Desc/Sound/ (TiedSeat.lean · AtDriver.lean · TiedPlaces.lean). In this file: the joining.
LIMITS. SeatLaws AT THE KIND's BLOCK IS A PREMISE, PAID NOWHERE HERE. IT SPEAKS OF THE BLOCK's ROUNDS AND DECISION ALONE, WHICH ARE THE DRAW's (K8's files' debt): a piece's run reads a block's name, rounds and decision; the block's three runs of claims are run at the batching's entries and are the batching's files' to treat: SO «K8, WHOLE» IS NOT TO BE CLAIMED FROM THIS FILE. THE VERSION OF THE FILES BELOW IT OVER WHICH THIS FILE WAS WRITTEN IS NOT THE FROZEN ONE. «onlineDescription returns in scope» stands behind the opening's letters. The reference shape; secondHashFunction. k08_kindTied is idle where the row of pieces has no entry at a number. That the description's own flat list has the written list's places: the driver's law, not called. No soundness. Nothing on hiding.
-/
import Johnson.IMR.K8Seat
import Johnson.IMR.FlatScope
import Johnson.Desc.Sound.AtDriver
import Johnson.Desc.Sound.TiedPlaces
import Johnson.Desc.Sound.TiedSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P1K8T

open Iop
open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open _root_.Run.PQ (CK)
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers flatPlacesOf)
open ProofFile (Cl)

/-- The number of the kind's block at link l in the first chain's flat list. -/
def ixOf (l : ℕ) : ℕ := if l = 24 then 343 else 14 * l + 6

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  {C : CK} {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
  {T : ThreeAt C D all
    (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
    X₁ X₂ W}

/-- **A lot's block that sits alone is tied at the table, where its authors' four hold at it.** -/
theorem k08_tied_at (hT : OfDesc _ T) {l i k : ℕ} {Lk : Link S Cl} {b B₀ : Block S Cl}
    {name : String} {a : Place} (e1 : c.links[l]? = some Lk) (e2 : Lk.hear[i]? = some b)
    (ef : IM.flatIx c l i = k) (hla : IM.LaidAlone ProofFile.sameReply b B₀ name a)
    (hk : a.kind ≠ KindName.K7)
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W}
    (hq : (T.p₁ :: T.l₁)[k]? = some q)
    (links : List ModelPart) (ps : List Place) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ a b w, E a b w = w) (H : SeatLaws links ps k q N Mg B₀) :
    TiedBy N Mg links ps (fun a => a) k (q.withMap E) (onQ N Mg links ps (fun a => a) k)
      (onQ N Mg links ps (fun a => a) (k + 1))
      (relAt (meansQ N Mg fun a => a) (insQ links ps k))
      (relAt (meansQ N Mg fun a => a) (outsQ links ps k)) := by
  have h3 := IM.hear_at_flat e1 e2
  rw [ef] at h3
  exact tiedBy_of_seatLaws links ps k B₀ b q
    ⟨IM.alone_underR hla, fun s rs gs t hy => ((IM.yes_alone hla hk s t rs gs).1 hy).2.1⟩
    (OfDesc.pieceAt hT hq h3) N Mg E hE H

/-- **THE SMALLNESS TEST's PIECE IS TIED AT THE TABLE, AT EACH OF ITS 25 PLACES, where its authors'
four hold at the kind's block there.** -/
theorem k08_tied (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hT : OfDesc _ T)
    {l : ℕ} (hl : l ≤ 24) {Xl : LinkH} (hX : Bs.G₀.built[l]? = some Xl)
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W}
    (hq : (T.p₁ :: T.l₁)[ixOf l]? = some q)
    (links : List ModelPart) (ps : List Place) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ a b w, E a b w = w)
    (H : SeatLaws links ps (ixOf l) q N Mg
      (VerifiableInference.Desc.First.K8.whole (ProofFile.k8ParW Z Bs.G₀ Xl l))) :
    TiedBy N Mg links ps (fun a => a) (ixOf l) (q.withMap E)
      (onQ N Mg links ps (fun a => a) (ixOf l)) (onQ N Mg links ps (fun a => a) (ixOf l + 1))
      (relAt (meansQ N Mg fun a => a) (insQ links ps (ixOf l)))
      (relAt (meansQ N Mg fun a => a) (outsQ links ps (ixOf l))) := by
  by_cases h24 : l = 24
  · subst h24
    obtain ⟨Lk, b, Xl', e1, e2, e3, hla, _⟩ := IM.k8_of_head hS hR O
    obtain rfl : Xl' = Xl := Option.some.inj (e3.symm.trans hX)
    exact k08_tied_at hT e1 e2 (IM.flatIx_scope hS hR O (by decide) 5) hla (fun e => nomatch e) hq links ps
      N Mg E hE H
  · have ei : ixOf l = 14 * l + 4 + 2 := by
      unfold ixOf
      rw [if_neg h24]
    rw [ei] at hq H ⊢
    by_cases he : l % 2 = 0
    · obtain ⟨Lk, b, Xl', _, e1, e2, e3, hla, _⟩ := IM.k8_of_layers hS hR O (l / 2) (by omega)
      rw [show 2 * (l / 2) = l by omega] at e1 e3 hla
      obtain rfl : Xl' = Xl := Option.some.inj (e3.symm.trans hX)
      exact k08_tied_at hT e1 e2 (IM.flatIx_scope hS hR O hl 4) hla (fun e => nomatch e) hq links ps N Mg E
        hE H
    · obtain ⟨Lk, b, Xl', _, e1, e2, e3, hla, _⟩ := IM.k8_of_attention hS hR O (l / 2) (by omega)
      rw [show 2 * (l / 2) + 1 = l by omega] at e1 e3 hla
      obtain rfl : Xl' = Xl := Option.some.inj (e3.symm.trans hX)
      exact k08_tied_at hT e1 e2 (IM.flatIx_scope hS hR O hl 4) hla (fun e => nomatch e) hq links ps N Mg E
        hE H

end

/-- In scope every link up to the head's is built. -/
theorem built_at {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l ≤ 24) :
    ∃ Xl, Bs.G₀.built[l]? = some Xl := by
  by_cases h24 : l = 24
  · subst h24
    obtain ⟨_, _, Xl, _, _, e3, _⟩ := IM.k8_of_head hS hR O
    exact ⟨Xl, e3⟩
  · by_cases he : l % 2 = 0
    · obtain ⟨_, _, Xl, _, _, _, e3, _⟩ := IM.k8_of_layers hS hR O (l / 2) (by omega)
      rw [show 2 * (l / 2) = l by omega] at e3
      exact ⟨Xl, e3⟩
    · obtain ⟨_, _, Xl, _, _, _, e3, _⟩ := IM.k8_of_attention hS hR O (l / 2) (by omega)
      rw [show 2 * (l / 2) + 1 = l by omega] at e3
      exact ⟨Xl, e3⟩

/-- The test over a list of places: every entry of the kind K8 stands at a number ixOf l, l ≤ 24. -/
def k8AllB (ps : List Place) : Bool :=
  (List.range ps.length).all fun i =>
    match ps[i]? with
    | some a => a.kind != KindName.K8 || (List.range 25).any fun l => i == ixOf l
    | none => true

set_option maxRecDepth 1000000 in
theorem k8AllB_full : k8AllB (flatPlacesOf linksFull true) = true := by decide +kernel

/-- **Where the kind stands in the full list of places**: at the numbers ixOf l, l ≤ 24, alone. -/
theorem k8_places_full (i : ℕ) (a : Place) (ha : (flatPlacesOf linksFull true)[i]? = some a)
    (hk : a.kind = KindName.K8) : ∃ l, l ≤ 24 ∧ i = ixOf l := by
  have hi : i < (flatPlacesOf linksFull true).length := (List.getElem?_eq_some_iff.1 ha).1
  have h := List.all_eq_true.1 k8AllB_full i (List.mem_range.2 hi)
  rw [ha] at h
  rcases (Bool.or_eq_true _ _).mp h with h1 | h1
  · rw [hk] at h1
    exact absurd h1 (by decide)
  · obtain ⟨l, hl, e⟩ := List.any_eq_true.1 h1
    exact ⟨l, Nat.le_of_lt_succ (List.mem_range.1 hl), by simpa using e⟩

/-- **THE KIND K8's SHARE OF THE CHAIN OF PROMISES, at the proof file's written description.** -/
theorem k08_kindTied {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {C : CK} {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
    {T : ThreeAt C D all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ W}
    (hT : OfDesc _ T) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ l, l ≤ 24 → ∀ a b w, E (ixOf l) a b w = w)
    (H : ∀ l Xl q, l ≤ 24 → Bs.G₀.built[l]? = some Xl → (T.p₁ :: T.l₁)[ixOf l]? = some q →
      SeatLaws linksFull (flatPlacesOf linksFull true) (ixOf l) q N Mg
        (VerifiableInference.Desc.First.K8.whole (ProofFile.k8ParW Z Bs.G₀ Xl l))) :
    KindTied N Mg linksFull (flatPlacesOf linksFull true) E (T.p₁ :: T.l₁) KindName.K8 := by
  intro i q a hq ha hk
  obtain ⟨l, hl, rfl⟩ := k8_places_full i a ha hk
  obtain ⟨Xl, hX⟩ := built_at hS hR O hl
  exact (k08_tied hS hR O hT hl hX hq linksFull _ N Mg (E _) (hE l hl) (H l Xl q hl hX hq)).tiedAt

end P1K8T

#print axioms P1K8T.k08_tied_at
#print axioms P1K8T.k08_tied
#print axioms P1K8T.k8AllB_full
#print axioms P1K8T.k8_places_full
#print axioms P1K8T.k08_kindTied
