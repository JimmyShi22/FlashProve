-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K5/TieAtJoinOpening.lean: conditional: the attention sub-protocol's premise at the opening,
at the joined list of message lots. No definition; six theorems.

  opening_text_eq           the text of the shared sending's own job at the opening, at the data
                            K1.lotData S, is the text of K1.firstJob, where the reader inside wit is rd
  lot_mem_join              the lot of message n of a job of the list lies in the joined list
  bookCovers_of_eq          where the book's count at an address is just the due, it covers the due
  openingLot_at_join_of     K5's premise at the opening holds at the joined list, at a numbering and a
                            member's number that are letters
  openingLot_at_join_head   the same at the numbering P5J.At.arr Zp and member number 2, under the head
  coins_at_opening          from the field coins of JoinFit to the premise on the book's count

The premises of openingLot_at_join_head: h, the library's head; hA, the maker returns; hm, all lots of one
message agree; hx, the opening's job, at the data K1.lotData S, stands in the list at number 2; hwit, the reader inside
wit is wt's; hBk, the book's count at the opening's address covers the part's due; hAd, the address is the
opening's.

Limits.
  * Conditional. This file proves none of its premises of any list, reader, book, instance or filling.
  * The index type W₀ and its reader wt are letters: their values come from the caller's filling.
  * NOT IN FRONT OF A LAW OVER COINS. The full size alone, the first chain alone, at the
    earlier hash OnBytes.secondHashFunction, a fixed function.
  * Through its imports it stands above the files under ThirdParty/ (lean/LIMITS.md, L15).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
  * hwit names one reader. At a wit whose reader holds other weights this file says nothing, though the
    opening's data may not read the weights: that is not looked into here.
  * All limits of OpeningNumberAtHead.lean hold here.
-/
import AtFullSide.K5.TieAtJoin
import Johnson.Desc.ProofFile.Honest.K5.Law.OpeningNumberAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K5
open ProofFile ProofFile.Honest ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Block Place Strs Chain KindName)
open VerifiableInference.Desc.First.Look (lookAt sigListCalls)
open VerifiableInference.Desc.Sound (MsgT)
open H2K5.Honest (K5KeepsM K5KeepsAt)
open ProofFile.Honest.FirstThread (Script WtF lettersHead b0Head MsgLot PadLot TreeLot LotsAgree MsgsAgree Covers
  Others JoinFit joinQ joinMl joinPl joinTl)
open P5J (AtMgA TS CellsM)

/-! ## 1 The two texts at the opening are one function; two small facts -/

variable {W₀ : Type} {wt : W₀ → Weights} {cellsOf : W₀ → P5J.CellsM OnBytes.Flat.numsFull}

section
variable {Bk : ProverCoinCounts} {Cl Wl Xi Xo : Type}

/-- **The text of the shared sending's own job at the opening, at the data `K1.lotData S`, is the
text of `K1.firstJob`**, where the reader inside wit is rd. The field first is a letter: the text
does not read it. -/
theorem opening_text_eq (S : Sz) (Zq : ProofFile.Pub) (G : ProofFile.Ground) (first : ℕ)
    {wit : Wl → K1.PlaceIn ProofFile.Inst} {rd : Wl → Readers} (hwit : ∀ v, (wit v).R = rd v)
    (own₀ : Xo) (n : ℕ) :
    K1.msgTxt (Bk := Bk) 0 wit (K1.placeJob (K1.firstJob (X := Xo) S Zq G).P first
        (K1.firstFold G.first) (K1.lotData S Zq G)) own₀ n =
      K1.msgTxt 0 rd (K1.firstJob (X := Xo) S Zq G) own₀ n := by
  funext k w hd mask r j
  have e : ∀ fr, (K1.placeJob (X := Xo) (K1.firstJob (X := Xo) S Zq G).P first
      (K1.firstFold G.first) (K1.lotData S Zq G)).data (wit w) fr =
      (K1.firstJob (X := Xo) S Zq G).data (rd w) fr := by
    intro fr
    funext k' r' j'
    rw [← hwit w]
    exact K1.data_first S Zq G (wit w).x (wit w).R fr.heard k' r' j'
  unfold K1.msgTxt K1.scriptMsg K1.rowsLaid
  rw [e]
  rfl

/-- The lot of message n of a job of the list lies in the joined list of message lots. -/
theorem lot_mem_join {bs : List (Block TS Cl)} {front : ℕ} {arr : ℕ → ℕ → ℕ}
    {wit : Wl → K1.PlaceIn Xi} {own₀ : Xo} {jobs : List (ℕ × K1.SendJob (K1.PlaceIn Xi) Xo)}
    {O : Others Bk Wl} {b : ℕ} {J : K1.SendJob (K1.PlaceIn Xi) Xo} (hx : (b, J) ∈ jobs) {n : ℕ}
    (hn : n < J.P.sent.size) :
    (⟨arr (K1.seatAtMember bs b J.P n).1 (K1.seatAtMember bs b J.P n).2, front + roundsTo bs b,
      K1.msgTxt 0 wit J own₀ n⟩ : MsgLot Bk Wl) ∈ joinMl bs front arr wit own₀ jobs O :=
  List.mem_append.2 (Or.inl (List.mem_flatMap.2 ⟨(b, J), hx,
    List.mem_map.2 ⟨n, List.mem_range.2 hn, rfl⟩⟩))

/-- Where the book's count at an address is just the due, it covers the due. -/
theorem bookCovers_of_eq {ch : ℕ} {a : Addr} {d : Due} (hC : dueAt (Bk.rowsOf ch) a = d) :
    K1.bookCovers Bk ch a d = true := by
  unfold K1.bookCovers
  rw [hC]
  exact decide_eq_true ⟨Nat.le_refl _, Nat.le_refl _⟩

end

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {S : OnBytes.HonestTrace.Sz} {X₀ X : Type}

/-! ## 2 K5's premise at the opening holds at the joined list -/

section
variable {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells X₀ X}

/-- **K5's premise at the opening holds at the joined list of message lots**, at a numbering arr and
a member's number b that are letters. Conditional: hm; hx; hwit; hBk; hseat, a fact on public
numbers; hAd. -/
theorem openingLot_at_join_of
    {arr : ℕ → ℕ → ℕ} {Xo : Type}
    {wit : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → K1.PlaceIn ProofFile.Inst} {own₀ : Xo}
    {jobs : List (ℕ × K1.SendJob (K1.PlaceIn ProofFile.Inst) Xo)}
    {O : Others A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)}
    (hm : MsgsAgree (joinMl cF.blocksInOrder 0 arr wit own₀ jobs O))
    {b first : ℕ}
    (hx : (b, (K1.placeJob (X := Xo) (K1.firstJob (X := Xo) S Zp A.G).P first (K1.firstFold A.G.first)
      (K1.lotData S Zp A.G))) ∈ jobs)
    (hwit : ∀ v, (wit v).R = ⟨v.trace, wt v.w₀, v.rc⟩)
    (hBk : K1.bookCovers A.B 0 ⟨(K1.firstJob (X := Xo) S Zp A.G).P.place, 0⟩
      (K1.dueR (K1.firstJob (X := Xo) S Zp A.G).P (K1.firstJob (X := Xo) S Zp A.G).ride) = true)
    (hseat : ∀ n m', K1.firstSeat h.𝔇.sent.shape 0 ⟨K1.firstAddr, n⟩ = some (0, m') →
      n < (K1.placeJob (X := Xo) (K1.firstJob (X := Xo) S Zp A.G).P first (K1.firstFold A.G.first)
      (K1.lotData S Zp A.G)).P.sent.size ∧
      arr (K1.seatAtMember cF.blocksInOrder b (K1.placeJob (X := Xo) (K1.firstJob (X := Xo) S Zp A.G).P first (K1.firstFold A.G.first)
               (K1.lotData S Zp A.G)).P n).1
        (K1.seatAtMember cF.blocksInOrder b (K1.placeJob (X := Xo) (K1.firstJob (X := Xo) S Zp A.G).P first (K1.firstFold A.G.first)
               (K1.lotData S Zp A.G)).P n).2 = P5J.At.num Zp 0 m')
    {Ad : MsgAddr} {m : ℕ} (hAd : typedSeat h A.G 0 Ad = some (0, m)) :
    OpeningLotForFillLean Zp (joinMl cF.blocksInOrder 0 arr wit own₀ jobs O) S A.G
      (fun v => ⟨v.trace, wt v.w₀, v.rc⟩) Ad m := by
  have es : typedSeat h A.G 0 = K1.firstSeat h.𝔇.sent.shape 0 := if_pos rfl
  rw [es] at hAd
  obtain ⟨s, n⟩ := Ad
  have e1 : s = K1.firstAddr := congrArg MsgAddr.sender (seated_at_opening hAd).1
  subst e1
  obtain ⟨hn, hnum⟩ := hseat n m hAd
  have hmem := lot_mem_join (Bk := A.B) (bs := cF.blocksInOrder) (front := 0) (arr := arr) (wit := wit)
    (own₀ := own₀) (O := O) hx hn
  rw [hnum, opening_text_eq (Bk := A.B) S Zp A.G first
    (rd := (fun v => ⟨v.trace, wt v.w₀, v.rc⟩)) hwit own₀ n] at hmem
  exact ⟨Xo, own₀, _, 0, hmem, hm _ hmem, Nat.zero_le _, hBk⟩

end

section
variable {P : OnlineProverParts W₀ IndexCommitterCoins Cells X₀ X} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells X₀ X}

/-- **The same at the numbering `P5J.At.arr Zp` and member number 2**: the fact on public numbers is
paid under the head. Conditional: h; hA; hm; hx; hwit; hBk; hAd. -/
theorem openingLot_at_join_head
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {Xo : Type}
    {wit : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → K1.PlaceIn ProofFile.Inst} {own₀ : Xo}
    {jobs : List (ℕ × K1.SendJob (K1.PlaceIn ProofFile.Inst) Xo)}
    {O : Others A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)}
    (hm : MsgsAgree (joinMl cF.blocksInOrder 0 (P5J.At.arr Zp) wit own₀ jobs O))
    {first : ℕ}
    (hx : (2, (K1.placeJob (X := Xo) (K1.firstJob (X := Xo) S Zp A.G).P first (K1.firstFold A.G.first)
      (K1.lotData S Zp A.G))) ∈ jobs)
    (hwit : ∀ v, (wit v).R = ⟨v.trace, wt v.w₀, v.rc⟩)
    (hBk : K1.bookCovers A.B 0 ⟨(K1.firstJob (X := Xo) S Zp A.G).P.place, 0⟩
      (K1.dueR (K1.firstJob (X := Xo) S Zp A.G).P (K1.firstJob (X := Xo) S Zp A.G).ride) = true)
    {Ad : MsgAddr} {m : ℕ} (hAd : typedSeat h A.G 0 Ad = some (0, m)) :
    OpeningLotForFillLean Zp (joinMl cF.blocksInOrder 0 (P5J.At.arr Zp) wit own₀ jobs O) S A.G
      (fun v => ⟨v.trace, wt v.w₀, v.rc⟩) Ad m := by
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := by
    obtain ⟨h1, h2, -⟩ := atPure_ok hA
    rw [← (Except.ok.inj (h1.symm.trans h.laid.pub) : A.Z = Zp)]
    exact h2
  obtain ⟨Bs, base, Op⟩ := h.toAtMg.laid.opened
  have eG0 : Bs.G₀ = A.G := Option.some.inj (Op.blank.symm.trans hG)
  refine openingLot_at_join_of h hm hx hwit hBk (fun n m' hq => ?_) hAd
  have key := opening_number_head h Op hq
  rw [eG0] at key
  have eP : (K1.placeJob (X := Xo) (K1.firstJob (X := Xo) S Zp A.G).P first (K1.firstFold A.G.first)
      (K1.lotData S Zp A.G)).P =
      VerifiableInference.Desc.K1.firstPar A.G.first (VerifiableInference.Desc.K1.gpOf Zp) := rfl
  rw [eP]
  exact key

/-- From the field coins of "the list is fit" to the premise hBk. -/
theorem coins_at_opening
    {arr : ℕ → ℕ → ℕ} {Xo : Type}
    {wit : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → K1.PlaceIn ProofFile.Inst} {own₀ : Xo}
    {jobs : List (ℕ × K1.SendJob (K1.PlaceIn ProofFile.Inst) Xo)}
    {O : Others A.B (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)}
    {seats : List (ℕ × ℕ)} (F : JoinFit cF.blocksInOrder 0 arr seats wit own₀ jobs O)
    {b first : ℕ}
    (hx : (b, (K1.placeJob (X := Xo) (K1.firstJob (X := Xo) S Zp A.G).P first (K1.firstFold A.G.first)
      (K1.lotData S Zp A.G))) ∈ jobs) :
    K1.bookCovers A.B 0 ⟨(K1.firstJob (X := Xo) S Zp A.G).P.place, 0⟩
      (K1.dueR (K1.firstJob (X := Xo) S Zp A.G).P (K1.firstJob (X := Xo) S Zp A.G).ride) = true :=
  bookCovers_of_eq (F.coins _ hx)

end

end AtFullSide.K5

#print axioms AtFullSide.K5.opening_text_eq
#print axioms AtFullSide.K5.lot_mem_join
#print axioms AtFullSide.K5.bookCovers_of_eq
#print axioms AtFullSide.K5.openingLot_at_join_of
#print axioms AtFullSide.K5.openingLot_at_join_head
#print axioms AtFullSide.K5.coins_at_opening
