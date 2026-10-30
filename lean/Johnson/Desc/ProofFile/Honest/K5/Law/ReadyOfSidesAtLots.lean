-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ReadyOfSidesAtLots.lean: A TEST THAT THE GENERAL JOIN
BITES. Conditional: at the prover that the maker `onlineProverFromPublicFiles` returns at a filling, what a lot pays
(`LotPays`, ReadyOfLots.lean in this folder) gives what its sides pay (`SidePays`, `KindPays`,
Honest/Law/ReadyOfSides.lean), and the maker's own tests give the public fields of `ReadyDebts`: so
two laws of this folder that end in a return of `ready` are had again, each to its own statement, BY
THE NEW ROAD. No definition; eight theorems; nothing is evaluated.

  `sidePays_of_lotPays`          a lot that pays: each of its sides pays, in the first chain. One
                                 member w of the view's type is asked: `LotPays` speaks at the views
                                 `some w` alone
  `kindPays_of_lots`             where each lot of the filling pays: every kind pays at the maker's
                                 first chain
  `readyDebts_of_lots`           `ReadyDebts` at the maker's description, book and prover. THE TWO
                                 LATER CHAINS' SIDES HAVE SLOTS: o₂, o₃, p₂, p₃ are premises
  `ready_of_lots_desc_by_sides`  the statement of `ready_of_lots_desc` (ReadyOfLots.lean), by
                                 `ready_of_sides`
  `readyDebts_k5`                under the library's head: `ReadyDebts` at a filling whose one lot
                                 is the kind K5's and whose later chains have no side. IT IS NOT THE
                                 HONEST PROVER: TEN OF THE ELEVEN KINDS SEND NOTHING
  `k5_side_there`                THE TEST IS NOT HOLLOW: under the library's head, at each of the
                                 twelve groups, a side of the kind K5 stands in the maker's first
                                 chain, at the place of a member of the description's list
  `kindPays_k5`                  the kind K5 pays at the maker's first chain, at such a filling
  `ready_of_lots_k5_by_sides`    the statement of `ready_of_lots_k5` (LotPaysK5.lean), by
                                 `ready_of_sides`

Limits.
  * Implications, but for what `lotPays_k5` pays under the head. In `readyDebts_of_lots` the four
    premises on the two later chains are shown of no filling that lays a side there: in the laws
    behind it they are met because these chains have no side.
  * That hL, hS, h2 and hA can be met together is not shown in this file.
  * A filling with few lots is NOT THE HONEST PROVER: the kinds without a lot send nothing. Never
    under a law over coins, never as "the prover", never as a ground that anything is simulated.
  * "`ready` returns" says nothing on whether a part plays, a round is reached or a verifier
    accepts.
  * The last four theorems: the full size and the format's second hash function alone.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.ReadyOfSides
import Johnson.Desc.ProofFile.Honest.K5.Law.LotPaysK5

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block FileDescription Place Chain KindName)
open P5J (AtMgA TS)

/-! ## 1 From a lot to its sides -/

/-- **A lot that pays: each of its sides pays.** -/
theorem sidePays_of_lotPays {Xi V W X : Type} {F : FileDescription Xi} {B : ProverCoinCounts} {Z : Pub} {G : Ground}
    {L : HLot V W X} (hL : LotPays F B Z G L) (w : V) :
    ∀ g ∈ L.halves Z G, SidePays B 0 F.first.blocksInOrder g := by
  intro g hg b hb hp hs hf v k
  obtain ⟨l, hl⟩ := hL.2 g hg b hb hp hs hf w k
  exact chainSteps_any (fun _ => rfl) B (B.rowsOf 0) (some w) v hs [b] l hl

section
variable {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {W₀ Rc Tr X₀ X : Type}
  {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **Where each lot of the filling pays, every kind pays at the maker's first chain.** -/
theorem kindPays_of_lots (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A)
    (hpay : ∀ L ∈ P.lots, LotPays A.F A.B A.Z A.G L) (w : Local W₀ Rc ProofFile.Inst Tr) :
    ∀ κ, KindPays A.B 0 A.F.first.blocksInOrder A.H.first κ := by
  obtain ⟨-, -, -, -, -, -, -, eH1, -⟩ := atPure_ok hA
  intro κ g hg _
  rw [eH1] at hg
  obtain ⟨L, hL, hgL⟩ := List.mem_flatMap.1 (hg : g ∈ P.lots.flatMap fun L => L.halves A.Z A.G)
  exact sidePays_of_lotPays (hpay L hL) w g hgL

/-- **`ReadyDebts` at the maker's description, book and prover**: the book, the seats and the dummy
from the maker's own tests; the first chain from the lots; the two later chains' four fields are
premises. -/
theorem readyDebts_of_lots (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A) (hpl : A.F.planOk = true)
    (hpay : ∀ L ∈ P.lots, LotPays A.F A.B A.Z A.G L)
    (hap : P.lots.Pairwise fun L M =>
      ∀ x ∈ L.halves A.Z A.G, ∀ y ∈ M.halves A.Z A.G, x.place ≠ y.place)
    (o₂ : twice A.H.shared = []) (o₃ : twice A.H.second = [])
    (p₂ : ∀ κ, KindPays A.B 1 A.F.shared.blocksInOrder A.H.shared κ)
    (p₃ : ∀ κ, KindPays A.B 2 A.F.second.blocksInOrder A.H.second κ) (w : Local W₀ Rc ProofFile.Inst Tr) :
    ReadyDebts A.F A.B A.H := by
  obtain ⟨-, -, -, -, -, -, -, eH1, -⟩ := atPure_ok hA
  obtain ⟨hw, s1, s2, s3, hd⟩ := atPure_tests hA
  have t1 : twice A.H.first = [] := by
    rw [eH1]
    exact twice_firstOf A.Z A.G P.lots (fun L hL => (hpay L hL).1) hap
  exact ⟨hpl, Johnson.RunOne.Sound.placesOk_of_planOk _ hpl, hw, List.isEmpty_iff.1 s1,
    List.isEmpty_iff.1 s2, List.isEmpty_iff.1 s3, t1, o₂, o₃, hd, kindPays_of_lots hA hpay w, p₂,
    p₃⟩

end

/-- **The statement of `ready_of_lots_desc`, by the new road.** A filling with few lots is not the
honest prover. -/
theorem ready_of_lots_desc_by_sides {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {W₀ Rc Tr X₀ X : Type}
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (hA : onlineProverFromPublicFiles o pol lay KL P = .ok A)
    (hpl : A.F.planOk = true) (hpay : ∀ L ∈ P.lots, LotPays A.F A.B A.Z A.G L)
    (hap : P.lots.Pairwise fun L M =>
      ∀ x ∈ L.halves A.Z A.G, ∀ y ∈ M.halves A.Z A.G, x.place ≠ y.place)
    (hS : ∀ Z' G', P.shared Z' G' = []) (h2 : ∀ Z' G', P.second Z' G' = []) {w₀ : W₀}
    {x : ProofFile.Inst} {tr : Tr} (hi : P.inRange w₀ = true) (ht : P.trace A.Z w₀ x = some tr) (rc : Rc)
    (k : Coins A.B) : ∃ R, ready A.F A.B A.H w₀ rc x k = .ok R := by
  obtain ⟨-, -, -, eT, -, eI, -, -, eSh, eSe, -, -⟩ := atPure_ok hA
  have eH2 : A.H.shared = [] := eSh.trans (hS _ _)
  have eH3 : A.H.second = [] := eSe.trans (h2 _ _)
  have D : ReadyDebts A.F A.B A.H :=
    readyDebts_of_lots hA hpl hpay hap (by rw [eH2]; rfl) (by rw [eH3]; rfl)
      (by rw [eH2]; exact fun _ _ hg => absurd hg (List.not_mem_nil))
      (by rw [eH3]; exact fun _ _ hg => absurd hg (List.not_mem_nil)) ⟨w₀, rc, x, tr⟩
  exact ready_of_sides D (by rw [eI]; exact hi) (by rw [eT, ht]; rfl) rc k

/-! ## 2 Under the library's head, at the kind K5's lot -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **`ReadyDebts` at a filling whose one lot is the kind K5's and whose later chains have no
side.** IT IS NOT THE HONEST PROVER: TEN OF THE ELEVEN KINDS SEND NOTHING. -/
theorem readyDebts_k5 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {W₀ Rc X₀ X : Type}
    {P : OnlineProverParts W₀ Rc Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    (hL : P.lots = [k5LotK id keyOfK3]) (hS : ∀ Z' G', P.shared Z' G' = [])
    (h2 : ∀ Z' G', P.second Z' G' = [])
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (w : Local W₀ Rc ProofFile.Inst Cells) :
    ReadyDebts (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.B A.H := by
  obtain ⟨e1, -, e3, -, -, -, -, -, eSh, eSe, -, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  have eF : A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF := Except.ok.inj (e3.symm.trans h.laid.value)
  have eH2 : A.H.shared = [] := eSh.trans (hS _ _)
  have eH3 : A.H.second = [] := eSe.trans (h2 _ _)
  have hpl : A.F.planOk = true := by
    rw [eF]
    exact h.laid.planOk
  have hpay : ∀ L ∈ P.lots, LotPays A.F A.B A.Z A.G L := by
    rw [eF, eZ, hL]
    intro L hLm
    obtain rfl := List.mem_singleton.1 hLm
    exact lotPays_k5 h hA
  have hap : P.lots.Pairwise fun L M =>
      ∀ x ∈ L.halves A.Z A.G, ∀ y ∈ M.halves A.Z A.G, x.place ≠ y.place := by
    rw [hL]
    exact List.pairwise_singleton _ _
  have res := readyDebts_of_lots hA hpl hpay hap (by rw [eH2]; rfl) (by rw [eH3]; rfl)
    (by rw [eH2]; exact fun _ _ hg => absurd hg (List.not_mem_nil))
    (by rw [eH3]; exact fun _ _ hg => absurd hg (List.not_mem_nil)) w
  rw [eF] at res
  exact res

/-- **The test is not hollow: at each of the twelve groups a side of the kind K5 stands in the
maker's first chain, at the place of a member of the description's list.** -/
theorem k5_side_there (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {W₀ Rc X₀ X : Type}
    {P : OnlineProverParts W₀ Rc Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    (hL : P.lots = [k5LotK id keyOfK3])
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {j : Nat} (hj : j < 12) :
    ∃ g ∈ A.H.first, ∃ b ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder,
      b.place = g.place ∧ g.place = placeOf j ∧ g.place.kind = KindName.K5 := by
  obtain ⟨e1, eG, -, -, -, -, -, eH1, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := by
    rw [← eZ]
    exact eG
  obtain ⟨blk, a, hm, Pl, Dc⟩ := k5_member h hj
  have hfind := k5LotK_find_K3 (W₀ := W₀) (Rc := Rc) (X := X) h hj hG id Pl.plan
  have hmem := List.mem_of_find?_eq_some hfind
  have hpl : (k5Half (W₀ := W₀) (Rc := Rc) (Xi := ProofFile.Inst) (X := X) id
      (seatOf keyOfK3 Zp A.G cF j a)).place = placeOf j := by
    simpa using List.find?_some hfind
  refine ⟨_, ?_, blk, List.mem_of_getElem? hm, Dc.place.trans hpl.symm, hpl, ?_⟩
  · rw [eH1, hL, eZ]
    exact List.mem_flatMap.2 ⟨_, List.mem_singleton.2 rfl, hmem⟩
  · rw [hpl]

/-- **The kind K5 pays at the maker's first chain**, at such a filling. -/
theorem kindPays_k5 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {W₀ Rc X₀ X : Type}
    {P : OnlineProverParts W₀ Rc Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    (hL : P.lots = [k5LotK id keyOfK3]) (hS : ∀ Z' G', P.shared Z' G' = [])
    (h2 : ∀ Z' G', P.second Z' G' = [])
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (w : Local W₀ Rc ProofFile.Inst Cells) :
    KindPays A.B 0 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder A.H.first KindName.K5 :=
  (readyDebts_k5 h hL hS h2 hA w).pays₁ KindName.K5

/-- **The statement of `ready_of_lots_k5`, by the new road.** IT IS NOT THE HONEST PROVER: TEN OF
THE ELEVEN KINDS SEND NOTHING. -/
theorem ready_of_lots_k5_by_sides (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {W₀ Rc X₀ X : Type}
    {P : OnlineProverParts W₀ Rc Cells X₀ X} {A : OnlineProverWithDescription W₀ Rc Cells X₀ X}
    (hL : P.lots = [k5LotK id keyOfK3]) (hS : ∀ Z' G', P.shared Z' G' = [])
    (h2 : ∀ Z' G', P.second Z' G' = [])
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) {w₀ : W₀} {x : ProofFile.Inst} {tr : Cells}
    (hi : P.inRange w₀ = true) (ht : P.trace Zp w₀ x = some tr) (rc : Rc) (k : Coins A.B) :
    ∃ R, ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) A.B A.H w₀ rc x k = .ok R := by
  obtain ⟨e1, -, -, eT, -, eI, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  exact ready_of_sides (readyDebts_k5 h hL hS h2 hA ⟨w₀, rc, x, tr⟩) (by rw [eI]; exact hi)
    (by rw [eT, eZ, ht]; rfl) rc k

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.sidePays_of_lotPays
#print axioms ProofFile.Honest.K5.kindPays_of_lots
#print axioms ProofFile.Honest.K5.readyDebts_of_lots
#print axioms ProofFile.Honest.K5.ready_of_lots_desc_by_sides
#print axioms ProofFile.Honest.K5.readyDebts_k5
#print axioms ProofFile.Honest.K5.k5_side_there
#print axioms ProofFile.Honest.K5.kindPays_k5
#print axioms ProofFile.Honest.K5.ready_of_lots_k5_by_sides
