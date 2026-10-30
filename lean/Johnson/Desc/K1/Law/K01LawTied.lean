-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/K01LawTied.lean: K01_law's FRAME: THE KIND K1's SHARE OF THE CHAIN OF PROMISES AT THE PROOF FILE's WRITTEN DESCRIPTION: KindTied N Mg linksFull (flatPlacesOf linksFull true) E (T.p₁ :: T.l₁) KindName.K1, IN SCOPE, FROM
THE KIND's TIES AT THE LOTS' OWN BLOCKS: by the kind-free road tiedAt_of_seatTie (Johnson/Desc/AtSeats/Road.lean: tiedBy_of_part · below_narrows · OfDesc.pieceAt; no SeatLaws). AFTER two earlier files of ours, not in this repository (the socket with
SeatLaws): their two lemmas on the flat list and their three on the places are taken over to the letter.
  k01_flat_reads | k01_flat_digits     in scope the flat list's entry at 14 l + k1Ix l d + 2 is the lot's own block, laid alone (k1_reads_of | k1_digits_of · hear_at_flat · flatIx_scope)
  firstNo · wNo · k1AllB_full · others_full · k01_places_full     [kernel] the kind stands at the fifty, at 2 and at wNo, and nowhere else
  wNo_eq                               [kernel] wNo = 356
  tiedReads_of | tiedDigits_of         **a later place**: the description's own piece is tied where the kind's tie holds at every block under the lot's own, at every z
  k01_law_frame                        **the kind's share**: from three hypotheses: the ties at the fifty (HL), at link 0's first place (H0) and at W's place (HW)
What is not claimed. The ties themselves (K1/Law/FiftyAtFull.lean, under their named premises); hQ (the piece has the sending's letters); hE. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.ThreePlaces
import Johnson.IMR.K1Scope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start flatPlacesOf)
open VerifiableInference.Desc.K13.Law (tiedAt_of_seatTie below_underR)
open OnBytes.Model.Stages (LinkH)
open ProofFile (Cl)
open IM (Open LaidAlone k1Reads k1Ix k1PlaceL)

/-- The number of link 0's first place in the flat list. -/
def firstNo : ℕ := 2

/-- The numbers of the list at which the kind stands and which are none of the fifty. -/
def otherNos (ps : List Place) : List ℕ :=
  (List.range ps.length).filter fun i =>
    match ps[i]? with
    | some a => a.kind == KindName.K1 &&
        !((List.range 25).any fun l => [false, true].any fun d => i == 14 * l + k1Ix l d + 2)
    | none => false

/-- The number of W's place behind the links: the last of these. -/
@[irreducible] def wNo : ℕ := (otherNos (flatPlacesOf linksFull true)).getLastD 0

/-- The test: number i and place a are those of one of the fifty later places. -/
def k1AtB (i : ℕ) (a : Place) : Bool :=
  (List.range 25).any fun l => [false, true].any fun d =>
    i == 14 * l + k1Ix l d + 2 && decide (a = k1PlaceL l d)

/-- The test over a list of places: every entry of the kind K1 passes k1AtB or stands at one of the two other numbers. -/
def k1AllB (ps : List Place) : Bool :=
  (List.range ps.length).all fun i =>
    match ps[i]? with
    | some a => a.kind != KindName.K1 || k1AtB i a || i == firstNo || i == wNo
    | none => true

set_option maxRecDepth 1000000 in
theorem k1AllB_full : k1AllB (flatPlacesOf linksFull true) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The two other numbers, and what stands there. -/
theorem others_full : (otherNos (flatPlacesOf linksFull true)).length = 2 ∧
    (flatPlacesOf linksFull true)[firstNo]? = some { chain := 1, link := some 0, piece := 1, kind := .K1 } ∧
    (flatPlacesOf linksFull true)[wNo]? = some { chain := 1, link := none, piece := 4, kind := .K1 } := by
  decide +kernel

/-- **Where the kind stands in the full list of places.** -/
theorem k01_places_full (i : ℕ) (a : Place) (ha : (flatPlacesOf linksFull true)[i]? = some a)
    (hk : a.kind = KindName.K1) :
    (∃ l, l < 25 ∧ ∃ d : Bool, i = 14 * l + k1Ix l d + 2 ∧ a = k1PlaceL l d) ∨ i = firstNo ∨ i = wNo := by
  have hi : i < (flatPlacesOf linksFull true).length := (List.getElem?_eq_some_iff.1 ha).1
  have h := List.all_eq_true.1 k1AllB_full i (List.mem_range.2 hi)
  rw [ha] at h
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  rcases h with ((h | h) | h) | h
  · exact absurd hk h
  · left
    obtain ⟨l, hl, h3⟩ := List.any_eq_true.1 h
    obtain ⟨d, -, h4⟩ := List.any_eq_true.1 h3
    obtain ⟨h5, h6⟩ := (Bool.and_eq_true _ _).mp h4
    exact ⟨l, List.mem_range.1 hl, d, by simpa using h5, of_decide_eq_true h6⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)


set_option maxRecDepth 1000000 in
theorem wNo_eq : wNo = 356 := by decide +kernel

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **The flat list's entry at a reads' place.** -/
theorem k01_flat_reads (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25) :
    ∃ (b : Block S Cl) (Xl : LinkH) (reads : Option (List ℕ)),
      c.blocksInOrder[14 * l + k1Ix l false + 2]? = some b ∧ Bs.G₀.built[l]? = some Xl ∧
      LaidAlone ProofFile.sameReply b (k1Reads Z Bs.G₀ l Xl (k1Ix l false + 1) reads).retype b.name
        (k1PlaceL l false) := by
  obtain ⟨Lk, b, Xl, pd, reads, digits, e1, e2, hX, -, h⟩ := IM.k1_reads_of hS hR O l hl
  have h5 := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) (k1Ix l false)] at h5
  exact ⟨b, Xl, reads, h5, hX, h⟩

/-- **The flat list's entry at a digits' place.** -/
theorem k01_flat_digits (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25) :
    ∃ (b : Block S Cl) (digits : Option (List ℕ)),
      c.blocksInOrder[14 * l + k1Ix l true + 2]? = some b ∧
      LaidAlone ProofFile.sameReply b
        (laterAt Bs.G₀.first (gpOf Z) l (k1Ix l true + 1) 2 digits : Block S Unit).retype b.name
        (k1PlaceL l true) := by
  obtain ⟨Lk, b, Xl, pr, reads, digits, e1, e2, -, -, h⟩ := IM.k1_digits_of hS hR O l hl
  have h5 := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) (k1Ix l true)] at h5
  exact ⟨b, digits, h5, h⟩


variable {C : CK} {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type}
  {T : ThreeAt C D all
    (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c) X₁ X₂ W}

/-- **A reads' place.** -/
theorem tiedReads_of (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hT : OfDesc _ T) (l : ℕ) (hl : l < 25)
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W}
    (hq : (T.p₁ :: T.l₁)[14 * l + k1Ix l false + 2]? = some q)
    (links : List ModelPart) (ps : List Place) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ a b w, E a b w = w)
    (pc : Block S Cl → Piece C (frameAt D all D.key₁ T.ft₁) S Cl W)
    (hQ : ∀ c' : Block S Cl, (⟨c', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece C (frameAt D all D.key₁ T.ft₁) S Cl W) = pc c')
    (H : ∀ (Xl : LinkH) (reads : Option (List ℕ)), Bs.G₀.built[l]? = some Xl → ∀ c' : Block S Cl,
      c'.UnderR ((k1Reads Z Bs.G₀ l Xl (k1Ix l false + 1) reads).retype : Block S Cl) →
      ∀ z : ProofFile.InstPub,
        TiedAt N Mg links ps (fun s : S => (z, s)) (14 * l + k1Ix l false + 2) (pc c')) :
    TiedAt N Mg links ps (fun a => a) (14 * l + k1Ix l false + 2) (q.withMap E) := by
  obtain ⟨b, Xl, reads, h5, hX, h⟩ := k01_flat_reads hS hR O l hl
  exact tiedAt_of_seatTie hT h5 hq links ps N Mg E hE pc hQ
    (H Xl reads hX _ (below_underR (IM.alone_underR h)))

/-- **A digits' place.** -/
theorem tiedDigits_of (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hT : OfDesc _ T) (l : ℕ) (hl : l < 25)
    {q : Piece C (frameAt D all D.key₁ T.ft₁) (ProofFile.InstPub × S) Cl W}
    (hq : (T.p₁ :: T.l₁)[14 * l + k1Ix l true + 2]? = some q)
    (links : List ModelPart) (ps : List Place) (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (hE : ∀ a b w, E a b w = w)
    (pc : Block S Cl → Piece C (frameAt D all D.key₁ T.ft₁) S Cl W)
    (hQ : ∀ c' : Block S Cl, (⟨c', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece C (frameAt D all D.key₁ T.ft₁) S Cl W) = pc c')
    (H : ∀ (digits : Option (List ℕ)) (c' : Block S Cl),
      c'.UnderR ((laterAt Bs.G₀.first (gpOf Z) l (k1Ix l true + 1) 2 digits : Block S Unit).retype :
        Block S Cl) →
      ∀ z : ProofFile.InstPub,
        TiedAt N Mg links ps (fun s : S => (z, s)) (14 * l + k1Ix l true + 2) (pc c')) :
    TiedAt N Mg links ps (fun a => a) (14 * l + k1Ix l true + 2) (q.withMap E) := by
  obtain ⟨b, digits, h5, h⟩ := k01_flat_digits hS hR O l hl
  exact tiedAt_of_seatTie hT h5 hq links ps N Mg E hE pc hQ
    (H digits _ (below_underR (IM.alone_underR h)))

/-- **THE KIND K1's SHARE, FROM THE TIES OF THE DESCRIPTION's OWN 52 PIECES.** -/
theorem k01_law_frame (N : Numbers) (Mg : Meaning ProofFile.InstPub W)
    (E : ℕ → (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × S) × (frameAt D all D.key₁ T.ft₁).E.Str → W → W)
    (HL : ∀ l, l < 25 → ∀ d : Bool, ∀ q, (T.p₁ :: T.l₁)[14 * l + k1Ix l d + 2]? = some q →
      TiedAt N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) (14 * l + k1Ix l d + 2)
        (q.withMap (E (14 * l + k1Ix l d + 2))))
    (H0 : ∀ q, (T.p₁ :: T.l₁)[2]? = some q →
      TiedAt N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) 2 (q.withMap (E 2)))
    (HW : ∀ q, (T.p₁ :: T.l₁)[356]? = some q →
      TiedAt N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) 356 (q.withMap (E 356))) :
    KindTied N Mg linksFull (flatPlacesOf linksFull true) E (T.p₁ :: T.l₁) KindName.K1 := by
  intro i q a hq ha hk
  rcases k01_places_full i a ha hk with ⟨l, hl, d, rfl, -⟩ | h | h
  · exact HL l hl d q hq
  · subst h
    exact H0 q hq
  · rw [wNo_eq] at h
    subst h
    exact HW q hq

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.k01_flat_reads
#print axioms VerifiableInference.Desc.K1.k01_flat_digits
#print axioms VerifiableInference.Desc.K1.k01_places_full
#print axioms VerifiableInference.Desc.K1.wNo_eq
#print axioms VerifiableInference.Desc.K1.tiedReads_of
#print axioms VerifiableInference.Desc.K1.tiedDigits_of
#print axioms VerifiableInference.Desc.K1.k01_law_frame
