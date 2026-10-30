-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/LotsAtHead.lean: THE SHARED "SENDING" (the kind K1): K1's OWN
LOTS AGREE AMONG THEMSELVES, AT THE OPENING AND THE FIFTY LATER SENDINGS, UNDER THE LIBRARY's HEAD:
two lots of messages of ours with one number are one lot; two lots of pads of ours at one seat are
one lot. One definition with code, seven statements and their proofs.

  k1Members, mem_k1Members
      the 51 members, each with its number in the first chain: 2; K1.noL l d for l < 25. THE JOBS
      ARE LETTERS (J₂; Jl l d)
  k1_same_of_num
      UNDER h (the library's head: A HYPOTHESIS), O, and the jobs' plans being the description's own
      ground's: two messages of two members with one number of the witness (k1Num,
      K1NumAtHead.lean) are one message of one member. By K1NumApart.lean's three ends
  k1MsgLots_one, k1PadLots_one
      so two of our lots with one number (at one seat) are one lot
  k1MsgLots_agree, k1PadLots_agree
      MsgsAgree | PadsAgree (Honest/Thread/ScriptLots.lean) OF OUR OWN TWO LISTS
  tie_at_own_lots
      so at a Script that is laid from OUR lots alone the record's msgs and pads hold at each of the
      51 members

PUBLIC DATA ALONE decide all of it: plans, seats, numbers. The lots' texts (msgTxt, padTxt) stand
under binders and are never opened: that two lots are ONE lot makes their answers one.

Limits. NO OTHER SENDER's LOT IS SPOKEN OF: that a number or a seat of ours is no other house's
lot's is proved nowhere. tie_at_own_lots' SCRIPT IS NOBODY's: it lays 0 at every message that K1
does not send: IT PROVES THAT "LIES IN AND AGREES" CAN BE MET AT THE REAL NUMBERS, NOT THAT ANY
PROVER's SCRIPT MEETS IT. THE PLANS ARE THE DESCRIPTION's GROUND's. 51 PLACES: W's sending is not
here. THE FULL SIZE ALONE. At a book that does not cover a part's count its lots answer nothing.
Nothing says how a coin is made. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.LotsLaid
import Johnson.Desc.ProofFile.Honest.K1.Law.K1NumApart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile.Honest.FirstThread (Script MsgLot PadLot TreeLot OwnMsgs OwnPads LotsAgree PadLotsAgree
  MsgsAgree PadsAgree)

variable {Xi X : Type}

/-- **The 51 members, each with its number in the first chain.** The jobs are letters. -/
def k1Members (J₂ : SendJob (PlaceIn Xi) X) (Jl : ℕ → Bool → SendJob (PlaceIn Xi) X) :
    List (Nat × SendJob (PlaceIn Xi) X) :=
  (2, J₂) :: (List.range 25).flatMap fun l =>
    [(K1.noL l false, Jl l false), (K1.noL l true, Jl l true)]

theorem mem_k1Members {J₂ : SendJob (PlaceIn Xi) X} {Jl : ℕ → Bool → SendJob (PlaceIn Xi) X}
    {x : Nat × SendJob (PlaceIn Xi) X} :
    x ∈ k1Members J₂ Jl ↔ x = (2, J₂) ∨ ∃ l, l < 25 ∧ ∃ d, x = (K1.noL l d, Jl l d) := by
  unfold k1Members
  rw [List.mem_cons, List.mem_flatMap]
  constructor
  · rintro (h | ⟨l, hl, hx⟩)
    · exact Or.inl h
    · rw [List.mem_cons, List.mem_singleton] at hx
      rcases hx with hx | hx
      · exact Or.inr ⟨l, List.mem_range.1 hl, false, hx⟩
      · exact Or.inr ⟨l, List.mem_range.1 hl, true, hx⟩
  · rintro (h | ⟨l, hl, d, hx⟩)
    · exact Or.inl h
    · refine Or.inr ⟨l, List.mem_range.2 hl, ?_⟩
      rw [List.mem_cons, List.mem_singleton]
      cases d
      · exact Or.inl hx
      · exact Or.inr hx

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- **ONE NUMBER, ONE MESSAGE OF ONE MEMBER.** -/
theorem k1_same_of_num (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    {J₂ : SendJob (PlaceIn Xi) X} {Jl : ℕ → Bool → SendJob (PlaceIn Xi) X}
    (hP₂ : J₂.P = K1.firstPar Bs.G₀.first (K1.gpOf Zp))
    (hPl : ∀ l, l < 25 → ∀ d, (Jl l d).P = K1.parL Zp Bs.G₀ l d)
    {x x' : Nat × SendJob (PlaceIn Xi) X} (hx : x ∈ k1Members J₂ Jl) (hx' : x' ∈ k1Members J₂ Jl)
    {n n' : ℕ} (hn : n < x.2.P.sent.size) (hn' : n' < x'.2.P.sent.size)
    (e : k1Num Zp cF.blocksInOrder x.1 x.2.P n = k1Num Zp cF.blocksInOrder x'.1 x'.2.P n') : x = x' ∧ n = n' := by
  obtain rfl | ⟨l, hl, d, rfl⟩ := mem_k1Members.1 hx <;>
    obtain rfl | ⟨l', hl', d', rfl⟩ := mem_k1Members.1 hx' <;> dsimp only at hn hn' e
  · rw [hP₂] at hn hn' e
    exact ⟨rfl, k1Num_apart_two h O hn hn' e⟩
  · rw [hP₂] at hn e
    rw [hPl l' hl' d'] at hn' e
    exact absurd e (k1Num_apart_two_fifty h O hn hl' d' hn')
  · rw [hP₂] at hn' e
    rw [hPl l hl d] at hn e
    exact absurd e.symm (k1Num_apart_two_fifty h O hn' hl d hn)
  · rw [hPl l hl d] at hn e
    rw [hPl l' hl' d'] at hn' e
    obtain ⟨rfl, rfl, rfl⟩ := k1Num_apart_fifty h O hl hl' d d' hn hn' e
    exact ⟨rfl, rfl⟩

section
variable {Bk : ProverCoinCounts} {Wl : Type}
  (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
  (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
    (seatZ Zp Np) (secondAt Zp Np))
  {J₂ : SendJob (PlaceIn Xi) X} {Jl : ℕ → Bool → SendJob (PlaceIn Xi) X}
  (hP₂ : J₂.P = K1.firstPar Bs.G₀.first (K1.gpOf Zp))
  (hPl : ∀ l, l < 25 → ∀ d, (Jl l d).P = K1.parL Zp Bs.G₀ l d)
include h O hP₂ hPl

/-- **Two of our lots of messages with one number are one lot.** -/
theorem k1MsgLots_one (front : Nat) (wit : Wl → PlaceIn Xi) (own₀ : X) {L L' : MsgLot Bk Wl}
    (hL : L ∈ k1MsgLots cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ (k1Members J₂ Jl))
    (hL' : L' ∈ k1MsgLots cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ (k1Members J₂ Jl))
    (e : L'.n = L.n) : L' = L := by
  obtain ⟨x, hx, hm⟩ := List.mem_flatMap.1 hL
  obtain ⟨n, hr, rfl⟩ := List.mem_map.1 hm
  obtain ⟨x', hx', hm'⟩ := List.mem_flatMap.1 hL'
  obtain ⟨n', hr', rfl⟩ := List.mem_map.1 hm'
  obtain ⟨rfl, rfl⟩ := k1_same_of_num h O hP₂ hPl hx' hx (List.mem_range.1 hr')
    (List.mem_range.1 hr) e
  rfl

/-- **Two of our lots of pads at one seat are one lot**: one seat has one number. -/
theorem k1PadLots_one {L L' : PadLot Bk Wl} (hL : L ∈ k1PadLots cF.blocksInOrder (k1Members J₂ Jl))
    (hL' : L' ∈ k1PadLots cF.blocksInOrder (k1Members J₂ Jl)) (ej : L'.j = L.j) (et : L'.t = L.t) :
    L' = L := by
  obtain ⟨x, hx, hm⟩ := List.mem_flatMap.1 hL
  obtain ⟨n, hr, rfl⟩ := List.mem_map.1 hm
  obtain ⟨x', hx', hm'⟩ := List.mem_flatMap.1 hL'
  obtain ⟨n', hr', rfl⟩ := List.mem_map.1 hm'
  have e : k1Num Zp cF.blocksInOrder x'.1 x'.2.P n' = k1Num Zp cF.blocksInOrder x.1 x.2.P n := by
    unfold k1Num
    dsimp only at ej et
    rw [ej, et]
  obtain ⟨rfl, rfl⟩ := k1_same_of_num h O hP₂ hPl hx' hx (List.mem_range.1 hr')
    (List.mem_range.1 hr) e
  rfl

/-- **OUR OWN LOTS OF MESSAGES AGREE.** -/
theorem k1MsgLots_agree (front : Nat) (wit : Wl → PlaceIn Xi) (own₀ : X) :
    MsgsAgree (k1MsgLots (Bk := Bk) cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ (k1Members J₂ Jl)) := by
  intro L hL L' hL' hno k w hd mask row place y y' hy hy'
  obtain rfl := k1MsgLots_one h O hP₂ hPl front wit own₀ hL hL' hno
  exact Option.some.inj (hy'.symm.trans hy)

/-- **OUR OWN LOTS OF PADS AGREE.** -/
theorem k1PadLots_agree :
    PadsAgree (k1PadLots (Bk := Bk) (Wl := Wl) cF.blocksInOrder (k1Members J₂ Jl)) := by
  intro L hL L' hL' hj ht k w mask row place y y' hy hy'
  obtain rfl := k1PadLots_one h O hP₂ hPl hL hL' hj ht
  exact Option.some.inj (hy'.symm.trans hy)

/-- THAT SCRIPT IS NOBODY's. **AT A SCRIPT LAID FROM OUR LOTS ALONE THE TIE HOLDS AT EACH OF THE 51
MEMBERS**: the record's fields msgs and pads, to the letter. -/
theorem tie_at_own_lots {Cells Tok : Type} (front : Nat) (cells : Wl → Cells) (tok : Wl → Tok)
    (tl : Nat → TreeLot Bk Wl) (wit : Wl → PlaceIn Xi) (own₀ : X) (Vd : Wl → Prop)
    {x : Nat × SendJob (PlaceIn Xi) X} (hx : x ∈ k1Members J₂ Jl) :
    (∀ n, n < x.2.P.sent.size →
      OwnMsgs (Script.ofLots cF.blocksInOrder front cells tok (k1PadLots cF.blocksInOrder (k1Members J₂ Jl)) tl
          (k1MsgLots cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ (k1Members J₂ Jl))) Vd
        (front + roundsTo cF.blocksInOrder x.1)
        (P5J.At.arr Zp (seatAtMember cF.blocksInOrder x.1 x.2.P n).1 (seatAtMember cF.blocksInOrder x.1 x.2.P n).2)
        (front + roundsTo cF.blocksInOrder x.1) (msgTxt 0 wit x.2 own₀ n)) ∧
    ∀ n, n < x.2.P.sent.size →
      OwnPads (Script.ofLots cF.blocksInOrder front cells tok (k1PadLots cF.blocksInOrder (k1Members J₂ Jl)) tl
          (k1MsgLots cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ (k1Members J₂ Jl))) Vd
        (seatAtMember cF.blocksInOrder x.1 x.2.P n).1 (seatAtMember cF.blocksInOrder x.1 x.2.P n).2
        (fun k _ => padTxt 0 x.2 n k) :=
  ⟨msgs_of_lots cF.blocksInOrder front cells tok _ tl _ (P5J.At.arr Zp) wit own₀ x
      (hin_msgs_of_agree (fun _ hL => hL) (k1MsgLots_agree h O hP₂ hPl front wit own₀) hx) Vd,
    pads_of_lots cF.blocksInOrder front cells tok _ tl _ x
      (hin_pads_of_agree (fun _ hL => hL) (k1PadLots_agree h O hP₂ hPl) hx) Vd⟩

end

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1Members
#print axioms ProofFile.Honest.K1.mem_k1Members
#print axioms ProofFile.Honest.K1.k1_same_of_num
#print axioms ProofFile.Honest.K1.k1MsgLots_one
#print axioms ProofFile.Honest.K1.k1PadLots_one
#print axioms ProofFile.Honest.K1.k1MsgLots_agree
#print axioms ProofFile.Honest.K1.k1PadLots_agree
#print axioms ProofFile.Honest.K1.tie_at_own_lots
