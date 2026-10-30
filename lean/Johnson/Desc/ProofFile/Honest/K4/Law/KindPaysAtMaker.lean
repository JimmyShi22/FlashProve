-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/KindPaysAtMaker.lean: CONDITIONAL.

What is here. AT THE PROVER THAT THE FRAME's MAKER `onlineProverFromPublicFiles` RETURNS, AT A FREE FILLING: THE KIND K4
PAYS, IN THE FORM OF `SidePays` AND `KindPays` (Honest/Law/ReadyOfSides.lean), IN THE FIRST CHAIN. It
says that the book lends K4's row, so that `chainSteps` returns at the list of one member, at each
member at the place of a side of the kind K4. It is K4's share of the field `pays₁` of `ReadyDebts`. IT SAYS NOTHING ON WHAT IS PLAYED, SENT OR ACCEPTED:
that is the other debt, the five statements at K4's twelve borders (Honest/Thread/PaysS.lean).

  `k4Places_inj`            the twelve written places are apart
  `k4_member_is_laid`       under h, the only member of the first chain at K4's place of a group is
                            the one that `LaidK4` names
  `k4_sidePays_at_half`     K4's half at a member that `LaidK4` names pays
  `k4_kindPays_at_maker`    **the kind K4 pays at the maker's first chain**
  `k4_sender_found_at_maker` **that is not empty**: at each of the twelve groups a search of the
                            maker's first chain finds K4's sender at the member that `LaidK4` names
  `k4_members_of_kind`      every member of the kind K4 stands at one of the twelve places
  `k4_no_block_later`       no member of the two later chains is of the kind K4
  `k4_kindPays_later`       so the kind K4 pays there, for want of members

Limits. CONDITIONAL: on h and hA; `k4_kindPays_at_maker` on ho too (no lot of the filling has a half at
a place of the kind K4 but with the halves of K4's lot), `k4_sender_found_at_maker` on hM, hE and ho.
THE FILLING IS A LETTER: that hM, hE and ho hold at the term's filling is another file's.
`k4_kindPays_at_maker` alone holds where no side of the kind K4 stands at all, which is why
`k4_sender_found_at_maker` goes with it. Honest/K4/Part.lean is laws.14's own, with no stop at a zero
challenge. THE FIRST CHAIN
AND, FOR WANT OF MEMBERS, THE TWO LATER ONES. `ho` lets two lots have K4's halves: `KindPays` then holds and `once₁` of `ReadyDebts` does not:
that field is another file's. THE FULL SIZE ALONE,
AND THE FORMAT's EARLIER HASH ALONE.
Nothing on soundness,
on completeness or on any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.Law.ReadyOfSides
import Johnson.Desc.ProofFile.Honest.K4.Law.W.BookAtPure
import Johnson.Desc.ProofFile.Honest.K4.Law.W.StepsAtK4
import Johnson.Desc.ProofFile.Honest.K4.Law.W.LendsK4
import Johnson.Desc.ProofFile.Honest.K4.Law.W.PubGOf
import Johnson.Desc.ProofFile.Honest.K4.Law.HgAtPure
import Johnson.Desc.ProofFile.Honest.K4.Law.DescAtPure
import Johnson.Desc.ProofFile.Honest.K4.Law.LaidAtGroup
import Johnson.Desc.ProofFile.Honest.K4.Law.LotTwelve
import Johnson.Desc.ProofFile.Honest.K4.Law.HalfAtPureBy
import Johnson.Desc.ProofFile.Law.LaterKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4 (Par entries)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Block KindName)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4 laid_at)
open ProofFile.Honest.K4.W (k4Book_at_atPure k4_tests_fit k4_rounds_fit k4_lends_row k4PubG_of)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place} {W₀ Rc Tr X₀ X' : Type}

/-- The twelve written places are apart. -/
theorem k4Places_inj {g g' : ℕ} (hg : g < 12) (hg' : g' < 12)
    (e : IM.k4Place g = IM.k4Place g') : g = g' :=
  List.inj_on_of_nodup_map k4Places_once (List.mem_range.2 hg) (List.mem_range.2 hg') e

/-- CONDITIONAL on h, Lh and hp. **The only member of the first chain at K4's place of group g is
the one that `LaidK4` names.** -/
theorem k4_member_is_laid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    {b : Block TS ProofFile.Cl} (hb : b ∈ cF.blocksInOrder) (hp : b.place = IM.k4Place g) : b = blk := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hb
  have hpl := IM.place_at h.scope h.reads O hi
  rw [Meaning.K2.placesW_linksFull] at hpl
  have hk : b.place.kind = .K4 := by
    rw [hp]
  obtain ⟨g', hg', hi', e⟩ := OnBytes.Road.K4.k04_places_full i b.place hpl hk
  have eg : g' = g := by
    have hg := Lh.lt
    exact k4Places_inj hg' hg (e.symm.trans hp)
  subst eg
  have := Lh.member
  rw [Lh.num, ← hi'] at this
  exact Option.some.inj (hi.symm.trans this)

/-- CONDITIONAL on h, Lh and hA. **K4's half at a member that `LaidK4` names pays.** -/
theorem k4_sidePays_at_half (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {W₁ Rc₁ Xi Tr₁ X₁ : Type} (cells : Tr₁ → Cells) (weights : W₁ → Weights)
    (tokens : Xi → Array Nat) (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) :
    SidePays A.B 0 (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder
      (k4Half (Rc := Rc₁) (X := X₁) cells weights tokens look (k4PubAt cF k x)) := by
  refine sidePays_of_tests _ _ _ _ fun b hb hp => ?_
  have hpl : b.place = k4Place (k4PubAt cF k x) := hp
  obtain rfl : b = blk := k4_member_is_laid h Lh hb (hpl.trans (pubAt_place Lh))
  have hr : b.rounds = (entries (k4PubAt cF k x).P (k4PubAt cF k x).hp (k4PubAt cF k x).g).map
      fun e => ({ entry := e } : Fmt.DeclaredRound) := by
    rw [IM.alone_rounds Lh.laid]
    rfl
  have hB := ProofFile.Honest.K14.atPure_book_at_head h hA
  have hpo := Johnson.RunOne.Sound.placesOk_of_planOk _ h.laid.planOk
  obtain ⟨hl, hc, -⟩ := k4Book_at_atPure (Rc := Rc₁) (X := X₁) h hA cells weights tokens
    (look (k4PubAt cF k x)) g Lh.lt (k4PubAt cF k x) (k4PubG_of Lh (k4Pub_head h Lh))
  obtain ⟨t1, t2⟩ := k4_tests_fit (Rc := Rc₁) (X := X₁) hB hpo hb cells weights tokens
    (look (k4PubAt cF k x)) hpl hr
  obtain ⟨sh, -, -⟩ := planOk_all h.laid.planOk
  refine ⟨(shaped_parts (sh b hb).2).1, k4_rounds_fit cells weights tokens
    (look (k4PubAt cF k x)) hpl hr, ?_, t1, t2, default, ?_⟩
  · rw [hpl]
    exact hc
  · rw [hpl]
    exact (lendsRow_iff default 0 (k4Place (k4PubAt cF k x)) _).2
      ((k4_lends_row cells weights tokens look (k4PubAt cF k x) A.B).trans hl)

/-- CONDITIONAL on h, hA and ho. **The kind K4 pays at the maker's first chain**: at every side of
the kind K4, at every member at its place, every list of sides that finds it, every view and every
run's coins, `chainSteps` returns at the list of that one member. It says that the book lends the
row; it says nothing on what is played, sent or accepted. The full size alone, the format's second
hash function alone. -/
theorem k4_kindPays_at_maker (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G) :
    KindPays A.B 0 A.F.first.blocksInOrder A.H.first KindName.K4 := by
  rw [atPure_desc h hA]
  have eZ : A.Z = Zp := atPure_pub h hA
  have hG := atPure_ground h hA
  obtain ⟨-, -, -, -, -, -, -, eH1, -⟩ := atPure_ok hA
  intro s hs hk
  rw [eH1] at hs
  obtain ⟨L, hL, hsL⟩ := List.mem_flatMap.1 (hs : s ∈ P.lots.flatMap fun L => L.halves A.Z A.G)
  rcases ho L hL with hno | hsame
  · exact absurd hk (hno s hsL)
  rw [hsame, eZ] at hsL
  obtain ⟨gi, hgi, e⟩ := List.mem_map.1 ((k4HLot_place_iff h hG cells weights look s.place).1
    (List.mem_map_of_mem hsL))
  obtain ⟨x, blk, Lh⟩ := laid_at h (List.mem_range.1 hgi)
  obtain ⟨G₁, hG₁, hx⟩ := Lh.lot
  obtain rfl : G₁ = A.G := Option.some.inj (hG₁.symm.trans hG)
  have hf := lot_half_head (Rc := Rc) (X' := X') h Lh cells weights look hx
  have hz := List.mem_of_find?_eq_some hf
  have hzp : (k4Half (Rc := Rc) (X := X') cells weights k4Tokens (look Zp A.G)
      (k4PubAt cF (28 * gi + 4) x)).place = IM.k4Place gi := by
    have hq := List.find?_some hf
    exact beq_iff_eq.1 hq
  have es := List.inj_on_of_nodup_map (k4HLot_places_once cells weights look Zp A.G) hsL hz
    (e.symm.trans hzp.symm)
  rw [es]
  exact k4_sidePays_at_half h Lh hA cells weights k4Tokens (look Zp A.G)

/-- CONDITIONAL on h, hA, hM, hE and ho. **`k4_kindPays_at_maker` is not empty**: at each of the
twelve groups a search of the maker's first chain finds, at K4's place of the group, K4's sender at
the public data of the member that `LaidK4` names, which stands in cF: the first chain of `A.F` by
`atPure_desc`. The twelve places differ: `k4Places_once`. The full size alone, the format's second
hash function alone. -/
theorem k4_sender_found_at_maker (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard)
    {M : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X'} (hM : M ∈ P.lots)
    (hE : M.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G)
    (ho : ∀ M' ∈ P.lots, (∀ y ∈ M'.halves A.Z A.G, y.place.kind ≠ .K4) ∨
      M'.halves A.Z A.G = (k4HLot cells weights look).halves A.Z A.G) {g : ℕ} (hg : g < 12) :
    ∃ x blk, LaidK4 Zp cF (28 * g + 4) (2 * g) g x blk ∧ blk ∈ cF.blocksInOrder ∧
      A.H.first.find? (fun q => q.place == IM.k4Place g) =
        some (k4Half cells weights k4Tokens (look Zp A.G) (k4PubAt cF (28 * g + 4) x)) := by
  obtain ⟨x, blk, Lh⟩ := laid_at h hg
  exact ⟨x, blk, Lh, List.mem_of_getElem? Lh.member,
    half_atPure_at h Lh hA cells weights look hM hE ho⟩

/-- CONDITIONAL on h and hA. **Every member of the kind K4 stands at one of the twelve places.** -/
theorem k4_members_of_kind (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∀ b ∈ A.F.first.blocksInOrder, b.place.kind = .K4 → ∃ g, g < 12 ∧ b.place = IM.k4Place g := by
  rw [atPure_desc h hA]
  intro b hb hk
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨i, hi⟩ := List.getElem?_of_mem (show b ∈ cF.blocksInOrder from hb)
  have hpl := IM.place_at h.scope h.reads O hi
  rw [Meaning.K2.placesW_linksFull] at hpl
  obtain ⟨g, hg, -, e⟩ := OnBytes.Road.K4.k04_places_full i b.place hpl hk
  exact ⟨g, hg, e⟩

/-- CONDITIONAL on h. **No member of the two later chains is of the kind K4.** -/
theorem k4_no_block_later (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) :
    (∀ b ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder, b.place.kind ≠ KindName.K4) ∧
      ∀ b ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder, b.place.kind ≠ KindName.K4 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  rw [O.desc]
  refine ⟨fun b hb hk => ?_, fun b hb hk => ?_⟩
  · have e := ProofFile.Law.shared_kinds O.shared (γ := ProofFile.Cl) b hb
    rw [hk] at e
    rcases e with e | e | e | e <;> cases e
  · have e := ProofFile.Law.second_kinds O.second (γ := ProofFile.Cl) b hb
    rw [hk] at e
    rcases e with e | e | e <;> cases e

/-- CONDITIONAL on h and hA. **The kind K4 pays in the two later chains, for want of members**: a
side of that kind stands at no member's place there. -/
theorem k4_kindPays_later (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    {P : OnlineProverParts W₀ Rc Tr X₀ X'} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    KindPays A.B 1 A.F.shared.blocksInOrder A.H.shared KindName.K4 ∧
      KindPays A.B 2 A.F.second.blocksInOrder A.H.second KindName.K4 := by
  rw [atPure_desc h hA]
  obtain ⟨n1, n2⟩ := k4_no_block_later h
  exact ⟨fun _ _ hk b hb hp => absurd (by rw [hp]; exact hk) (n1 b hb),
    fun _ _ hk b hb hp => absurd (by rw [hp]; exact hk) (n2 b hb)⟩

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_member_is_laid
#print axioms ProofFile.Honest.K4.k4_sidePays_at_half
#print axioms ProofFile.Honest.K4.k4_kindPays_at_maker
#print axioms ProofFile.Honest.K4.k4_sender_found_at_maker
#print axioms ProofFile.Honest.K4.k4_members_of_kind
#print axioms ProofFile.Honest.K4.k4_no_block_later
#print axioms ProofFile.Honest.K4.k4_kindPays_later
