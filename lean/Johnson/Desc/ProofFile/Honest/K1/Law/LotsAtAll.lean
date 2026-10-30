-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/LotsAtAll.lean: THE SHARED "SENDING" (the kind K1): THE LIST BY
NUMBERS WITH W's SENDING: ALL 52 SENDERS OF THE KIND ON THE FIRST CHAIN; AND K1's OWN LOTS AGREE
AMONG THEMSELVES AT ALL 52, UNDER THE LIBRARY's HEAD. One definition with code; fourteen theorems.

WHY. LotsAtHead.lean's list k1Members has 51 members: "W's sending is not here". K1NumApartW.lean
has the three facts that part W's two numbers from each other and from the 51's. Here they are
joined.

  k1MembersW, mem_k1MembersW, k1MembersW_length, k1MembersW_nodup
      the list: k1Members J₂ Jl ++ [(356, Jw)]. THE JOBS ARE LETTERS. It has 52 entries; no number
      stands in it twice (arithmetic on K1.noL; evaluated in Lean's kernel)
  k1_same_of_num_w
      UNDER h (the library's head: A HYPOTHESIS), O, and the three plans being the description's
      own: two messages of two members with one number of the witness (k1Num) are one message of one
      member. Nine cases: four are k1_same_of_num (LotsAtHead.lean); five by K1NumApartW.lean
  msgLots_one_of, padLots_one_of, msgLots_agree_of, padLots_agree_of
      four of LotsAtHead.lean's five laws ONCE MORE AT A LETTER jobs, under hs: "one number, one
      message", written out as a premise. NO HEAD IS ASKED. The 51's four are instances
  k1MsgLotsW_agree, k1PadLotsW_agree
      at the 52
  msgTxt_isSome, padTxt_isSome
      WHETHER A LOT's TEXT ANSWERS IS A PUBLIC TEST: bookCovers (and, for a pad, padB): by
      lentCut_isSome (Honest/K1/ScriptAtLaw.lean). General in the job
  w_not_in_51, w_at_two_refused
      A FACT: 356 is no number of the 51. A NEGATIVE TEST: with W's job laid at the opening's number
      2 the list's numbers are NOT without a double: so k1MembersW_nodup's test can say no

PUBLIC DATA ALONE decide all of it: plans, seats, numbers, the book's counts. The lots' texts
(msgTxt, padTxt) stand under binders; msgTxt_isSome and padTxt_isSome unfold them one step, to the
Option that lentCut returns, and read no value of it.

KIN, TOLD. The four at a letter jobs have four of LotsAtHead.lean's five as instances at k1Members
under k1_same_of_num; these stay where they are. The fifth, the tie at a Script laid from these lots
alone, is not taken up here. That the closed comparison of keys can say no: apartAll_no
(K1NumApart.lean): not restated.

Limits. NO OTHER SENDER's LOT IS SPOKEN OF. NO SCRIPT IS NAMED: THAT THE LOTS AGREE IS NO TIE. hs
at a list that holds one number twice with two jobs is met by nothing. THE PLANS ARE THE
DESCRIPTION's GROUND's. THE FULL SIZE ALONE. At a book that does not cover a part's count its lots
answer nothing. Nothing says how a coin is made. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.LotsAtHead
import Johnson.Desc.ProofFile.Honest.K1.Law.K1NumApartW
import Johnson.Desc.ProofFile.Honest.K1.ScriptAtLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)
open Johnson.Prover.Send (shapeAt)
open ProofFile.Honest.FirstThread (MsgLot PadLot LotsAgree PadLotsAgree MsgsAgree PadsAgree)

/-! ## 1 Whether a text answers is public -/

section
variable {Bk : ProverCoinCounts} {W Wl X : Type}

/-- **WHETHER A MESSAGE's TEXT ANSWERS IS THE PUBLIC TEST bookCovers**, at every entry alike. -/
theorem msgTxt_isSome (ch : Nat) (hc : ch ≤ 1) (wit : Wl → W) (J : SendJob W X) (own₀ : X) (n : Nat)
    (k : Coins Bk) (w : Wl) (h : List Fmt.Drawn) (mask : Bool) (r j : Nat) :
    (msgTxt ch wit J own₀ n k w h mask r j).isSome =
      bookCovers Bk ch ⟨J.P.place, 0⟩ (dueR J.P J.ride) := by
  unfold msgTxt
  rw [Option.isSome_map]
  exact lentCut_isSome k ch hc _ _

/-- **WHETHER A PAD's TEXT ANSWERS IS TWO PUBLIC TESTS**: the entry is a pad's, and bookCovers. -/
theorem padTxt_isSome (ch : Nat) (hc : ch ≤ 1) (J : SendJob W X) (n : Nat) (k : Coins Bk)
    (mask : Bool) (r j : Nat) :
    (padTxt ch J n k mask r j).isSome =
      (padB J.P.codes (shapeAt J.P n) mask r j &&
        bookCovers Bk ch ⟨J.P.place, 0⟩ (dueR J.P J.ride)) := by
  unfold padTxt
  cases hp : padB J.P.codes (shapeAt J.P n) mask r j with
  | true =>
    rw [if_pos rfl, Option.isSome_map, Bool.true_and]
    exact lentCut_isSome k ch hc _ _
  | false =>
    rw [if_neg (by simp), Bool.false_and]
    rfl

end

/-! ## 2 The list -/

variable {Xi X : Type}

/-- **The 52 members, each with its number in the first chain**: the 51 (k1Members,
LotsAtHead.lean), then W's sending at number 356. The jobs are letters. -/
def k1MembersW (J₂ : SendJob (PlaceIn Xi) X) (Jl : ℕ → Bool → SendJob (PlaceIn Xi) X)
    (Jw : SendJob (PlaceIn Xi) X) : List (Nat × SendJob (PlaceIn Xi) X) :=
  k1Members J₂ Jl ++ [(356, Jw)]

theorem mem_k1MembersW {J₂ : SendJob (PlaceIn Xi) X} {Jl : ℕ → Bool → SendJob (PlaceIn Xi) X}
    {Jw : SendJob (PlaceIn Xi) X} {x : Nat × SendJob (PlaceIn Xi) X} :
    x ∈ k1MembersW J₂ Jl Jw ↔ x ∈ k1Members J₂ Jl ∨ x = (356, Jw) := by
  unfold k1MembersW
  rw [List.mem_append, List.mem_singleton]

/-- **52 entries.** -/
theorem k1MembersW_length (J₂ : SendJob (PlaceIn Xi) X) (Jl : ℕ → Bool → SendJob (PlaceIn Xi) X)
    (Jw : SendJob (PlaceIn Xi) X) : (k1MembersW J₂ Jl Jw).length = 52 := by
  unfold k1MembersW k1Members
  simp

/-- **NO NUMBER STANDS IN THE LIST TWICE.** No premise. -/
theorem k1MembersW_nodup (J₂ : SendJob (PlaceIn Xi) X) (Jl : ℕ → Bool → SendJob (PlaceIn Xi) X)
    (Jw : SendJob (PlaceIn Xi) X) : ((k1MembersW J₂ Jl Jw).map (·.1)).Nodup := by
  unfold k1MembersW k1Members
  rw [List.map_append, List.map_cons, List.map_flatMap]
  show (2 :: (List.range 25).flatMap (fun l => [K1.noL l false, K1.noL l true]) ++ [356]).Nodup
  decide +kernel

/-- A fact: 356 is no number of the 51. -/
theorem w_not_in_51 (J₂ : SendJob (PlaceIn Xi) X) (Jl : ℕ → Bool → SendJob (PlaceIn Xi) X) :
    356 ∉ (k1Members J₂ Jl).map (·.1) := by
  unfold k1Members
  rw [List.map_cons, List.map_flatMap]
  show 356 ∉ 2 :: (List.range 25).flatMap (fun l => [K1.noL l false, K1.noL l true])
  decide +kernel

/-- **A NEGATIVE TEST**: W's job laid at the opening's number: the numbers have a double. -/
theorem w_at_two_refused (J₂ : SendJob (PlaceIn Xi) X) (Jl : ℕ → Bool → SendJob (PlaceIn Xi) X)
    (Jw : SendJob (PlaceIn Xi) X) :
    ¬ ((k1Members J₂ Jl ++ [(2, Jw)] : List (Nat × SendJob (PlaceIn Xi) X)).map (·.1)).Nodup := by
  unfold k1Members
  rw [List.map_append, List.map_cons, List.map_flatMap]
  show ¬ (2 :: (List.range 25).flatMap (fun l => [K1.noL l false, K1.noL l true]) ++ [2]).Nodup
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- **ONE NUMBER, ONE MESSAGE OF ONE MEMBER, AT ALL 52.** -/
theorem k1_same_of_num_w (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    {J₂ : SendJob (PlaceIn Xi) X} {Jl : ℕ → Bool → SendJob (PlaceIn Xi) X}
    {Jw : SendJob (PlaceIn Xi) X}
    (hP₂ : J₂.P = K1.firstPar Bs.G₀.first (K1.gpOf Zp))
    (hPl : ∀ l, l < 25 → ∀ d, (Jl l d).P = K1.parL Zp Bs.G₀ l d)
    (hPw : Jw.P = K1.parW Zp.first (wGp Zp) 4 wMsgFull)
    {x x' : Nat × SendJob (PlaceIn Xi) X} (hx : x ∈ k1MembersW J₂ Jl Jw)
    (hx' : x' ∈ k1MembersW J₂ Jl Jw)
    {n n' : ℕ} (hn : n < x.2.P.sent.size) (hn' : n' < x'.2.P.sent.size)
    (e : k1Num Zp cF.blocksInOrder x.1 x.2.P n = k1Num Zp cF.blocksInOrder x'.1 x'.2.P n') : x = x' ∧ n = n' := by
  rcases mem_k1MembersW.1 hx with hx | rfl <;> rcases mem_k1MembersW.1 hx' with hx' | rfl
  · exact k1_same_of_num h O hP₂ hPl hx hx' hn hn' e
  · exfalso
    dsimp only at hn' e
    rw [hPw] at hn' e
    obtain rfl | ⟨l, hl, d, rfl⟩ := mem_k1Members.1 hx <;> dsimp only at hn e
    · rw [hP₂] at hn e
      exact k1Num_apart_w_two h O hn' hn e.symm
    · rw [hPl l hl d] at hn e
      exact k1Num_apart_w_fifty h O hn' hl d hn e.symm
  · exfalso
    dsimp only at hn e
    rw [hPw] at hn e
    obtain rfl | ⟨l, hl, d, rfl⟩ := mem_k1Members.1 hx' <;> dsimp only at hn' e
    · rw [hP₂] at hn' e
      exact k1Num_apart_w_two h O hn hn' e
    · rw [hPl l hl d] at hn' e
      exact k1Num_apart_w_fifty h O hn hl d hn' e
  · dsimp only at hn hn' e
    rw [hPw] at hn hn' e
    exact ⟨rfl, k1Num_apart_w h O hn hn' e⟩

/-! ## 3 The four laws at a letter jobs -/

section
variable {Bk : ProverCoinCounts} {Wl : Type} {jobs : List (Nat × SendJob (PlaceIn Xi) X)}
  (hs : ∀ x ∈ jobs, ∀ x' ∈ jobs, ∀ n n', n < x.2.P.sent.size → n' < x'.2.P.sent.size →
    k1Num Zp cF.blocksInOrder x.1 x.2.P n = k1Num Zp cF.blocksInOrder x'.1 x'.2.P n' → x = x' ∧ n = n')
include hs

/-- **Two lots of messages of the list with one number are one lot.** -/
theorem msgLots_one_of (front : Nat) (wit : Wl → PlaceIn Xi) (own₀ : X) {L L' : MsgLot Bk Wl}
    (hL : L ∈ k1MsgLots cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs)
    (hL' : L' ∈ k1MsgLots cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs)
    (e : L'.n = L.n) : L' = L := by
  obtain ⟨x, hx, hm⟩ := List.mem_flatMap.1 hL
  obtain ⟨n, hr, rfl⟩ := List.mem_map.1 hm
  obtain ⟨x', hx', hm'⟩ := List.mem_flatMap.1 hL'
  obtain ⟨n', hr', rfl⟩ := List.mem_map.1 hm'
  obtain ⟨rfl, rfl⟩ := hs x' hx' x hx n' n (List.mem_range.1 hr') (List.mem_range.1 hr) e
  rfl

/-- **Two lots of pads of the list at one seat are one lot**: one seat has one number. -/
theorem padLots_one_of {L L' : PadLot Bk Wl} (hL : L ∈ k1PadLots cF.blocksInOrder jobs)
    (hL' : L' ∈ k1PadLots cF.blocksInOrder jobs) (ej : L'.j = L.j) (et : L'.t = L.t) : L' = L := by
  obtain ⟨x, hx, hm⟩ := List.mem_flatMap.1 hL
  obtain ⟨n, hr, rfl⟩ := List.mem_map.1 hm
  obtain ⟨x', hx', hm'⟩ := List.mem_flatMap.1 hL'
  obtain ⟨n', hr', rfl⟩ := List.mem_map.1 hm'
  have e : k1Num Zp cF.blocksInOrder x'.1 x'.2.P n' = k1Num Zp cF.blocksInOrder x.1 x.2.P n := by
    unfold k1Num
    dsimp only at ej et
    rw [ej, et]
  obtain ⟨rfl, rfl⟩ := hs x' hx' x hx n' n (List.mem_range.1 hr') (List.mem_range.1 hr) e
  rfl

/-- **The list's lots of messages agree.** -/
theorem msgLots_agree_of (front : Nat) (wit : Wl → PlaceIn Xi) (own₀ : X) :
    MsgsAgree (k1MsgLots (Bk := Bk) cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs) := by
  intro L hL L' hL' hno k w hd mask row place y y' hy hy'
  obtain rfl := msgLots_one_of hs front wit own₀ hL hL' hno
  exact Option.some.inj (hy'.symm.trans hy)

/-- **The list's lots of pads agree.** -/
theorem padLots_agree_of : PadsAgree (k1PadLots (Bk := Bk) (Wl := Wl) cF.blocksInOrder jobs) := by
  intro L hL L' hL' hj ht k w mask row place y y' hy hy'
  obtain rfl := padLots_one_of hs hL hL' hj ht
  exact Option.some.inj (hy'.symm.trans hy)

end

/-! ## 4 At the 52 -/

section
variable {Bk : ProverCoinCounts} {Wl : Type}
  (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
  (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
    (seatZ Zp Np) (secondAt Zp Np))
  {J₂ : SendJob (PlaceIn Xi) X} {Jl : ℕ → Bool → SendJob (PlaceIn Xi) X}
  {Jw : SendJob (PlaceIn Xi) X}
  (hP₂ : J₂.P = K1.firstPar Bs.G₀.first (K1.gpOf Zp))
  (hPl : ∀ l, l < 25 → ∀ d, (Jl l d).P = K1.parL Zp Bs.G₀ l d)
  (hPw : Jw.P = K1.parW Zp.first (wGp Zp) 4 wMsgFull)
include h O hP₂ hPl hPw

/-- **OUR OWN LOTS OF MESSAGES AGREE, AT ALL 52.** -/
theorem k1MsgLotsW_agree (front : Nat) (wit : Wl → PlaceIn Xi) (own₀ : X) :
    MsgsAgree
      (k1MsgLots (Bk := Bk) cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ (k1MembersW J₂ Jl Jw)) :=
  msgLots_agree_of (fun _ hx _ hx' _ _ hn hn' e => k1_same_of_num_w h O hP₂ hPl hPw hx hx' hn hn' e)
    front wit own₀

/-- **OUR OWN LOTS OF PADS AGREE, AT ALL 52.** -/
theorem k1PadLotsW_agree :
    PadsAgree (k1PadLots (Bk := Bk) (Wl := Wl) cF.blocksInOrder (k1MembersW J₂ Jl Jw)) :=
  padLots_agree_of (fun _ hx _ hx' _ _ hn hn' e => k1_same_of_num_w h O hP₂ hPl hPw hx hx' hn hn' e)

end

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.msgTxt_isSome
#print axioms ProofFile.Honest.K1.padTxt_isSome
#print axioms ProofFile.Honest.K1.k1MembersW
#print axioms ProofFile.Honest.K1.mem_k1MembersW
#print axioms ProofFile.Honest.K1.k1MembersW_length
#print axioms ProofFile.Honest.K1.k1MembersW_nodup
#print axioms ProofFile.Honest.K1.w_not_in_51
#print axioms ProofFile.Honest.K1.w_at_two_refused
#print axioms ProofFile.Honest.K1.k1_same_of_num_w
#print axioms ProofFile.Honest.K1.msgLots_one_of
#print axioms ProofFile.Honest.K1.padLots_one_of
#print axioms ProofFile.Honest.K1.msgLots_agree_of
#print axioms ProofFile.Honest.K1.padLots_agree_of
#print axioms ProofFile.Honest.K1.k1MsgLotsW_agree
#print axioms ProofFile.Honest.K1.k1PadLotsW_agree
