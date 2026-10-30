-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/FreshSixAtHead.lean: the kind "the code switch" (K2): SIX OF
THE EIGHT PREMISES `FreshAsks` (Honest/K2/Fresh.lean), ALL PUBLIC, UNDER THE LIBRARY's HEAD AND THE
OPENING, AT EACH SWITCH OF THE PLAN, AT THE LETTERS AT WHICH THE KIND's LOT OF ROWS LAYS ITS ROW
(`switchSLot`, Honest/K2/Rows.lean): seated · blocks · two · fits · seeds · oneRow. THE TWO THAT ARE
LEFT, book AND sendFresh, STAY PREMISES OF THE END. IT DOES NOT SAY THAT `FreshAsks` IS MET, and it
draws nothing from it. No definition; one closed fact by evaluation in Lean's kernel, with a
control; lemmas.

  `find_at_findIdx`   general: the first member that passes a test stands at the test's first index
  `numbers_at_place`   general in the plan: at a place of the kind's lot the lot's numbers
                    (`numbersAt`) are `IM.k2P` at the plan's numbers of the place's link, under some
                    name and dress
  `rounds_at_place`   so the rounds that the lot hands its row (`roundsAt`) are the kind's own two
                    at these numbers, each with its oracle messages; name and dress are not read
  `oneRowW`         BY LEAN's KERNEL: at each written place a fresh mask rides, and it has one mask
                    row; a control: asked for two rows the like test says no somewhere
  `freshAsks_of_two`   THE END: book and sendFresh give `FreshAsks` at these letters

By, ours: `k2_member_at_head`, `k2_block_at_head`, `four_public_at_head` (Honest/K2/Law/
RecordAtHead.lean, BlockAtHead.lean, PublicMoreAtHead.lean) · `fits_at_head`, `placeFits`,
`placeOneRow`, `placeOneRow_yes`, `seeds_at_place` (PublicAtHead.lean, PlanAsks.lean,
SeedsOfDraw.lean) · of other authors: `borderNo_written` (Honest/K1/Law/MembersByBorder.lean). Of
the files named in this paragraph none is sealed.

Limits. hbook AND hsend ARE PREMISES: of book and sendFresh nothing is shown here. D, readers, ok,
fs, the book and the order stay free letters: the lot lays ok := its public test on the instance.
The sender is the core's, the closing the lot's own. The full size and the format's second hash function
alone. THE HEAD AND THE OPENING ARE HYPOTHESES: THIS FILE SHOWS THEM MET BY NOTHING: WHERE NOTHING
MEETS THEM THE LAWS THAT NAME THEM HOLD EMPTILY. sendFresh IS A LAW OVER COINS: it comes in as a
premise, to the letter, and goes out unturned; in the six that are shown stands no measure and no
coin. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.RecordAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.BlockAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicMoreAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.SeedsOfDraw
import Johnson.Desc.ProofFile.Honest.K2.Fresh

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Place Block Oracle)
open VerifiableInference.Desc.First.K2 (rounds)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)
open IM (k2P)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- The first member that passes a test stands at the test's first index. -/
theorem find_at_findIdx {α : Type} (p : α → Bool) : ∀ l : List α, l.find? p = l[l.findIdx p]?
  | [] => rfl
  | a :: t => by
    rw [List.find?_cons, List.findIdx_cons]
    cases h : p a with
    | true => rfl
    | false =>
      simp only [cond_false, List.getElem?_cons_succ]
      exact find_at_findIdx p t

/-- **At a place of the kind's lot the lot's numbers are `IM.k2P` at the plan's numbers.** -/
theorem numbers_at_place {Z : ProofFile.Pub} {G : ProofFile.Ground} {Pp : P1K2.Prep} {n : P1K2.Nums}
    (hP : P1K2.prepOf Z G = some Pp) {p : SwitchPlace} (hp : p ∈ switchPlaces Z G)
    (hn : P1K2.numsAt Pp p.place.link = some n) :
    ∃ (nm : String) (st : First.K2.At), numbersAt Z G p.place = some (k2P Z p.place nm st n) := by
  unfold switchPlaces at hp
  rw [hP] at hp
  cases hs : ProofFile.spotsOf Z.cuts with
  | none =>
    rw [hs] at hp
    cases hp
  | some sps =>
    rw [hs] at hp
    obtain ⟨sp, hsp, e⟩ := List.mem_map.1 hp
    have epl : p.place = sp.place := by rw [← e]
    have hn' : P1K2.numsAt Pp sp.place.link = some n := by
      rw [← epl]
      exact hn
    have hl : P1K2.pureSpots Z G = (sps.filter fun s => s.place.kind == .K2).filterMap fun s =>
        (P1K2.p2With Pp Z s).map fun q => (s, q) := by
      unfold P1K2.pureSpots P1K2.p2All
      rw [hs, hP]
      rfl
    unfold numbersAt
    rw [hl]
    cases hf : ((sps.filter fun s => s.place.kind == .K2).filterMap fun s =>
        (P1K2.p2With Pp Z s).map fun q => (s, q)).find? (fun x => x.1.place == p.place) with
    | none =>
      exfalso
      have mem : (sp, k2P Z sp.place sp.name (P1K2.standsOf sp) n) ∈
          (sps.filter fun s => s.place.kind == .K2).filterMap fun s =>
            (P1K2.p2With Pp Z s).map fun q => (s, q) :=
        List.mem_filterMap.2 ⟨sp, hsp, by
          unfold P1K2.p2With
          rw [hn']
          rfl⟩
      have c := List.find?_eq_none.1 hf _ mem
      apply c
      rw [epl]
      exact beq_self_eq_true _
    | some x =>
      have hx : (x.1.place == p.place) = true :=
        List.find?_some (p := fun y : ProofFile.Spot × First.K2.P2 => y.1.place == p.place) hf
      obtain ⟨s', -, e'⟩ := List.mem_filterMap.1 (List.mem_of_find?_eq_some hf)
      obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.1 e'
      unfold P1K2.p2With at hq
      obtain ⟨n', hn'', rfl⟩ := Option.map_eq_some_iff.1 hq
      have ep : s'.place = p.place := beq_iff_eq.1 hx
      obtain rfl : n' = n := by
        rw [ep] at hn''
        exact Option.some.inj (hn''.symm.trans hn)
      refine ⟨s'.name, P1K2.standsOf s', ?_⟩
      rw [← ep]
      rfl

/-- **The rounds that the lot hands its row are the kind's own two at the plan's numbers.** nm, st:
any: they are not read. -/
theorem rounds_at_place {Z : ProofFile.Pub} {G : ProofFile.Ground} {Pp : P1K2.Prep} {n : P1K2.Nums}
    (hP : P1K2.prepOf Z G = some Pp) {p : SwitchPlace} (hp : p ∈ switchPlaces Z G)
    (hn : P1K2.numsAt Pp p.place.link = some n) (nm : String) (st : First.K2.At) :
    roundsAt Z G p.place =
      (rounds (k2P Z p.place nm st n)).zip [(k2P Z p.place nm st n).sent, []] := by
  obtain ⟨nm', st', e⟩ := numbers_at_place hP hp hn
  unfold roundsAt
  rw [e]
  rfl

set_option maxRecDepth 1000000 in
/-- **At each written place a fresh mask rides, and it has one mask row**; a control: asked for two
rows the like test says no somewhere. -/
theorem oneRowW : (placesW.all placeOneRow) = true ∧
    (placesW.all fun p => (switchFresh p.sizes p.others p.foldVars).isSome) = true ∧
    (placesW.all fun p => (switchFresh p.sizes p.others p.foldVars).all fun x =>
      ((switchSent p.sizes p.others).getD x.1 default).shape.maskRows == 2) = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {p : SwitchPlace} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
  {W₀ Rc Xi Tr X : Type}

/-- **SIX OF THE EIGHT PREMISES PAID: book AND sendFresh GIVE `FreshAsks`**, at the letters at which
the kind's lot of rows lays its row. σ: the side that `Side.seated` lays at the place. -/
theorem freshAsks_of_two (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (ok : Xi → Bool) (fs : List (Fall TS)) {Bk : ProverCoinCounts} {ord : List Place}
    (hbook : ∀ q : Addr, bookFits p.sizes.codes (switchSent p.sizes p.others)
      (switchFresh p.sizes p.others p.foldVars) (Bk.spentBy ⟨p.place, 0⟩ q)
      (Bk.knownBy ord ⟨p.place, 0⟩ q) = true)
    (hsend : ∀ q : Addr, SendFreshLaw (coreSender freshTable) p.sizes.codes
      (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars)
      (Bk.spentBy ⟨p.place, 0⟩ q) (Bk.knownBy ord ⟨p.place, 0⟩ q)) :
    ∃ σ : Side TS ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi,
      FreshAsks (coreSender freshTable) D readers (lotClosing Zp Bs.G₀) p ok
        (roundsAt Zp Bs.G₀ p.place) cF.blocksInOrder fs σ Bk ord := by
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  obtain ⟨blk, member, -⟩ := k2_member_at_head h O hp
  obtain ⟨Pp, n, nm, st, before, after, hP, hn, -, ⟨-, hr, ho⟩, -, -⟩ :=
    k2_block_at_head h O hp member
  have hR := rounds_at_place hP hp hn nm st
  obtain ⟨nm', st', hq⟩ := numbers_at_place hP hp hn
  obtain ⟨-, -, s1, s2⟩ := four_public_at_head h O hp hP hn p.place nm' st'
  have hfind : cF.blocksInOrder.find? (fun b => b.place == p.place) = some blk := by
    rw [find_at_findIdx]
    have e := K1.borderNo_written h p.place
    unfold borderNo at e
    rw [e]
    exact member
  refine ⟨{ block := blk
            row := switchRow (coreSender freshTable) D readers (lotClosing Zp Bs.G₀) p ok
              (roundsAt Zp Bs.G₀ p.place)
            fall := fallOf fs p.place }, ?_⟩
  exact
    { seated := by
        unfold Side.seated
        rw [hfind]
        rfl
      blocks := by
        show blk.rounds.zip blk.oracles = _
        rw [hr, ho, hR]
      two := by
        rw [hR]
        rfl
      fits := fits_at_head h.toAtMg O p hp
      seeds := seeds_at_place Zp Bs.G₀ p.place hq s1 s2
      oneRow := placeOneRow_yes (List.all_eq_true.1 oneRowW.1 p hpW)
      book := hbook
      sendFresh := hsend }

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.find_at_findIdx
#print axioms ProofFile.Honest.K2.Law.numbers_at_place
#print axioms ProofFile.Honest.K2.Law.rounds_at_place
#print axioms ProofFile.Honest.K2.Law.oneRowW
#print axioms ProofFile.Honest.K2.Law.freshAsks_of_two
