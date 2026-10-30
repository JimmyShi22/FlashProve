-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5K3R/SitsKinds.lean: the kind "lookup"'s share of the chain of promises' field, at the
proof file's written description.

Why. The rule for the first chain asks a tie at the table's own words of every piece of the first
row (`EachTied`). Johnson/Desc/Sound/TiedPlaces.lean cuts that field into one debt a kind
(`KindTied`, `eachTied_of_kinds`). Here the kind K3's debt is paid under `SeatLaws`.

Main names:
  `k03_places_full`: at the driver's list of places for the full list of segments: an entry of the
    kind K3 stands at a number 14 l + i + 2, l below 25, and is the driver's address of link l's
    lookup on the calls or on the digits. By the kernel, on the written list.
  `k03_kindTied`: at the letters of `k03_tied`: where `SeatLaws` holds at the constant at all fifty
    places and the table's extractor lays nothing there: `KindTied` of the kind K3.

Limits: a joining of rules. `SeatLaws` is a premise. `k03_places_full` speaks of the written list
`flatPlacesOf linksFull true`; that the description's own flat list has these places is the driver's
law and is not called here. Nothing on soundness; nothing on hiding.


-/
import Johnson.P5K3R.SitsTied
import Johnson.Desc.Sound.TiedPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K3Lot

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start flatPlacesOf)
open ProofFile (Cl)

/-- The test: number i and place a are those of one of the fifty lookups. -/
def k3AtB (i : ℕ) (a : Place) : Bool :=
  (List.range 25).any fun l => [false, true].any fun d =>
    i == 14 * l + IM.k3Ix l d + 2 && decide (a = IM.k3Place l d)

/-- The test over a list of places: every entry of the kind K3 passes `k3AtB`. -/
def k3AllB (ps : List Place) : Bool :=
  (List.range ps.length).all fun i =>
    match ps[i]? with
    | some a => a.kind != KindName.K3 || k3AtB i a
    | none => true

set_option maxRecDepth 1000000 in
theorem k3AllB_full : k3AllB (flatPlacesOf linksFull true) = true := by decide +kernel

/-- **Where the kind stands in the full list of places.** -/
theorem k03_places_full (i : ℕ) (a : Place) (ha : (flatPlacesOf linksFull true)[i]? = some a)
    (hk : a.kind = KindName.K3) :
    ∃ l, l < 25 ∧ ∃ d : Bool, i = 14 * l + IM.k3Ix l d + 2 ∧ a = IM.k3Place l d := by
  have hi : i < (flatPlacesOf linksFull true).length := (List.getElem?_eq_some_iff.1 ha).1
  have h := List.all_eq_true.1 k3AllB_full i (List.mem_range.2 hi)
  rw [ha] at h
  have h2 : k3AtB i a = true := by
    rcases (Bool.or_eq_true _ _).mp h with h1 | h1
    · rw [hk] at h1
      exact absurd h1 (by decide)
    · exact h1
  obtain ⟨l, hl, h3⟩ := List.any_eq_true.1 h2
  obtain ⟨d, -, h4⟩ := List.any_eq_true.1 h3
  obtain ⟨h5, h6⟩ := (Bool.and_eq_true _ _).mp h4
  exact ⟨l, List.mem_range.1 hl, d, by simpa using h5, of_decide_eq_true h6⟩

/-- **The kind K3's share, at the proof file's written description.** -/
theorem k03_kindTied {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
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
    (hE : ∀ l, l < 25 → ∀ d : Bool, ∀ a b w, E (14 * l + IM.k3Ix l d + 2) a b w = w)
    (H : ∀ l, l < 25 → ∀ (d : Bool) q, (T.p₁ :: T.l₁)[14 * l + IM.k3Ix l d + 2]? = some q →
      ∀ b', VerifiableInference.Desc.K3.theStated K3Lot.ofForm (K3Lot.readersAt Bs.G₀.W)
          Bs.G₀.W Z.first.codes Z.first.shape (IM.k3Place l d) = some b' →
        SeatLaws linksFull (flatPlacesOf linksFull true) (14 * l + IM.k3Ix l d + 2) q N Mg b') :
    KindTied N Mg linksFull (flatPlacesOf linksFull true) E (T.p₁ :: T.l₁) KindName.K3 := by
  intro i q a hq ha hk
  obtain ⟨l, hl, d, rfl, -⟩ := k03_places_full i a ha hk
  exact (k03_tied hS hR O hT l hl d hq linksFull _ N Mg (E _) (hE l hl d) (H l hl d q hq)).tiedAt

end K3Lot
