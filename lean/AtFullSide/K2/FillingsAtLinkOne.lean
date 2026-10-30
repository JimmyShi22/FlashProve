-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/FillingsAtLinkOne.lean: the kind "the code switch" (K2): THE TIE OF THE TWO FILLINGS
AT THE OPENING's MESSAGES THAT LINK 1's KEPT COPIES COPY: the premise hdat of `msgs_at_link_one` and
`msgs_at_join_all` (AtFullSide/K2/), in its own text, AT THE SWITCHES' FILLING `withSwitchData S₀ Dk
Zp G` (Johnson/Desc/ProofFile/Honest/K2/OwnData.lean) AND THE SENDER's FILLING `Dk Zp G`: Dk: any
lot's data, a letter. Both read one filling at one address. Under the library's head and the
opening. One definition, a public test; one closed fact by evaluation in Lean's kernel, with a
control; lemmas.

  `asRow_c0`        over the base field the first coordinate of an entry as a row takes it is the
                    element of the base field there, and 0 where there is none
  `firstAddrsOk`, `firstAddrsW`   A PUBLIC TEST at the written lists: at each written place below
                    link 2 and each of its kept copies: the address that the place names for the
                    copied message of the first segment is the opening's sender's, at the same
                    number; that message lies over the base field; BY LEAN's KERNEL; A CONTROL:
                    against the next number it says no
  `fillings_at_link_one`   THE END

By. Named here: `with_other_kind` (Honest/K2/Law/OwnDataApart.lean): at a sender that is no
switch's the joined filling is the other lot's · `places_at_head`, `segments_at_head`
(Honest/K2/Law/PlacesWritten.lean) · `at_of_take` (Honest/K2/Law/ClosingSame.lean): a filling hands
the same at two lists of challenges that agree as far as it reads · `order_at_link_one`
(MsgsAtJoinAll.lean). Of other authors, in the library: `K1.asE_inl` (Honest/K1/AgreeTools.lean).
What it is for: hdat → the field msgs of `SwitchLeftV` (Honest/K2/Law/MadeValuesLeft.lean) → the
kind's debt under "the exchange", by kind.

Limits. THREE PREMISES BESIDE THE HEAD AND THE OPENING: hI, hR: at each input that is meant the
sender's reader wit hands the input's own instance and the readers that the switches read · hH:
PUBLIC, ON Dk: at the opening's sender's addresses it reads no more challenges than stand in front
of the opening: paid at no filling here. THE CONTROL BENDS THE NUMBER IN THE ADDRESS ALONE: the
test's second limb, on the field, has no control. No Script, no coin and no run occurs. It says that
two texts read one filling alike: not what the filling holds. It speaks at the head's own size and
hash: the full size, the format's second hash function. Nothing on any property.
-/
import AtFullSide.K2.MsgsAtJoinAll
import Johnson.Desc.ProofFile.Honest.K2.Law.OwnDataApart
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingSame
import Johnson.Desc.ProofFile.Honest.K1.AgreeTools

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.K2.Honest (zeroG)
open VerifiableInference.Desc.K1 (firstPar gpOf)
open OnBytes.HonestTrace (Sz)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law

/-! ## 1 General -/

/-- Over the base field: the first coordinate of an entry as a row takes it. -/
theorem asRow_c0 (o : Option (Cb.Gl.F ⊕ Cb.Gl.E)) :
    (asRow false o).c0 = (match o with | some (.inl x) => x | _ => (0 : Cb.Gl.F)) := by
  cases o with
  | none => rfl
  | some v =>
    cases v with
    | inl x =>
      show (asE (some (.inl x))).c0 = x
      rw [K1.asE_inl]
      rfl
    | inr x => rfl

/-! ## 2 At the written constants -/

/-- **A PUBLIC TEST** at the written lists. d: a bend for the control; 0 in earnest. -/
def firstAddrsOk (d : Nat) : Bool :=
  (segsW[0]?).any fun Sg => (placesW.filter fun p => decide (p.link < 2)).all fun p =>
    (List.range p.sizes.target.kept.size).all fun i =>
      decide (p.addrs 0 (VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg Sg false) i) =
        some ⟨K1.firstAddr,
          VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg Sg false) i + d⟩) &&
      !(((Sg.ownShapes true).getD
        (VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg Sg false) i) {}).mainDeg == 3)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The test says yes**; a control: against the next number it says no. -/
theorem firstAddrsW : firstAddrsOk 0 = true ∧ firstAddrsOk 1 = false := by decide +kernel

/-! ## 3 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
  {W₀ Rc Xi Tr X : Type} {wit : Local W₀ Rc Xi Tr → K1.PlaceIn Xi}
  {readers : Local W₀ Rc Xi Tr → Readers}

/-- hI, hR AND hH ARE PREMISES. **THE TWO TEXTS READ ONE FILLING ALIKE**: hdat of
`msgs_at_link_one`, in its own text, at these two fillings. -/
theorem fillings_at_link_one (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (S₀ : Sz) (Dk : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Vd : Local W₀ Rc Xi Tr → Prop) (f₀ : Nat)
    (hI : ∀ w, Vd w → (wit w).x = w.x) (hR : ∀ w, Vd w → (wit w).R = readers w)
    (hH : ∀ w, Vd w → ∀ n, (Dk Zp Bs.G₀ w.x).heardAt ⟨K1.firstAddr, n⟩ ≤ 0 + roundsTo cF.blocksInOrder 2) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, p.link < 2 → ∀ Sg, segsW[0]? = some Sg →
      ∀ i, i < p.sizes.target.kept.size → ∀ w, Vd w →
      ∀ (hd : List Fmt.Drawn) (fr : Front X), fr.heard = hd.take (0 + roundsTo cF.blocksInOrder 2) →
      ∀ a b, a < ((switchSent p.sizes p.others).getD (1 + i) default).shape.mainRows →
      b < (p.sizes.codes.base.getD
        ((switchSent p.sizes p.others).getD (1 + i) default).shape.code default).ell →
      (match (K1.placeJob (X := X) (firstPar Bs.G₀.first (gpOf Zp)) f₀
          (K1.firstFold Bs.G₀.first) (Dk Zp Bs.G₀)).data (wit w) fr
          (VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg Sg false) i) a b with
        | some (.inl x) => x | _ => (0 : Cb.Gl.F)) =
      (lotOwn (segmentsOf Zp Bs.G₀) p (withSwitchData S₀ Dk Zp Bs.G₀ w.x) (readers w)
        ((hd.take (0 + roundsTo cF.blocksInOrder (switchNo p))).take
          ((hd.take (0 + roundsTo cF.blocksInOrder (switchNo p))).length - 0)) (0 + 0)
        (VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg Sg false) i) a b).c0 := by
  intro p hp h2 Sg hSg i hi w hv hd fr hfr a b _ _
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  have hT := firstAddrsW.1
  unfold firstAddrsOk at hT
  rw [hSg] at hT
  have hT' := List.all_eq_true.1 (List.all_eq_true.1
    (show ((placesW.filter fun p => decide (p.link < 2)).all _) = true from hT) p
    (List.mem_filter.2 ⟨hpW, decide_eq_true h2⟩)) i (List.mem_range.2 hi)
  rw [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hT'
  obtain ⟨c1, c2⟩ := hT'
  have e1 : lotOwn (segmentsOf Zp Bs.G₀) p (withSwitchData S₀ Dk Zp Bs.G₀ w.x) (readers w)
      ((hd.take (0 + roundsTo cF.blocksInOrder (switchNo p))).take
        ((hd.take (0 + roundsTo cF.blocksInOrder (switchNo p))).length - 0)) (0 + 0)
      (VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg Sg false) i) a b =
      asRow false ((withSwitchData S₀ Dk Zp Bs.G₀ w.x).at_ (readers w)
        ((hd.take (0 + roundsTo cF.blocksInOrder (switchNo p))).take
          ((hd.take (0 + roundsTo cF.blocksInOrder (switchNo p))).length - 0))
        ⟨K1.firstAddr, VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg Sg false) i + 0⟩
        a b) := by
    show ownBy _ _ p.addrs _ _ 0 _ a b = _
    unfold ownBy
    rw [c1]
    rw [segments_at_head h.toAtMg O]
    show asRow (((((segsW[0]?).map fun (x : SegmentPub) => x.ownShapes (0 == 0)).getD []).getD
      (VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg Sg false) i) {}).mainDeg == 3) _ = _
    rw [hSg]
    show asRow (((Sg.ownShapes true).getD
      (VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg Sg false) i) {}).mainDeg == 3) _ = _
    rw [c2]
  rw [e1, asRow_c0, (with_other_kind S₀ Dk Zp Bs.G₀ w.x
    ⟨K1.firstAddr, VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg Sg false) i + 0⟩
    (by
      show K1.firstAddr.place.kind ≠ .K2
      decide)).2.2.2.2.1]
  show (match (Dk Zp Bs.G₀ (wit w).x).at_ (wit w).R fr.heard ⟨K1.firstAddr, _⟩ a b with
    | some (.inl x) => x | _ => (0 : Cb.Gl.F)) = _
  rw [hI w hv, hR w hv, hfr]
  have hq := hH w hv (VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg Sg false) i)
  have ho := order_at_link_one h O p hp h2
  rw [at_of_take (Dk Zp Bs.G₀ w.x) (readers w) (heard := hd.take (0 + roundsTo cF.blocksInOrder 2))
    (heard' := (hd.take (0 + roundsTo cF.blocksInOrder (switchNo p))).take
      ((hd.take (0 + roundsTo cF.blocksInOrder (switchNo p))).length - 0))
    ⟨K1.firstAddr, VerifiableInference.Desc.K2.Honest.keptNo (membersOfSeg Sg false) i⟩
    (by
      rw [Nat.sub_zero, List.take_length, List.take_take, List.take_take,
        Nat.min_eq_left hq, Nat.min_eq_left (by omega)]) a b]
  rfl

end AtFullSide.K2

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms AtFullSide.K2.asRow_c0
#print axioms AtFullSide.K2.firstAddrsOk
#print axioms AtFullSide.K2.firstAddrsW
#print axioms AtFullSide.K2.fillings_at_link_one
