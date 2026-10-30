-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/BookFitsCarried.lean: **ALONG THE SHARED CHAIN THE BOOK FITS; AND AT ITS LAST BORDER o_omega IS PART 0 OF ITS TREE: TWO OF THE FIVE CLAUSES THAT THE LAST CHAIN's DOOR OWES ON THE SHARED CHAIN's LAST RECORD.**
Definitions with code; statements and proofs.

What for. The last chain's door (Johnson/Desc/Last/ShapeDoor.lean: DoorOwed.shared; the premise (SH₃) of the second glue) asks five tests of the shared chain's last record. By its cut two are the
book's: (2) bookFitsB d.book · (3) tenantB. The tests stand in Johnson/Desc/Sound/BookTests.lean (their laws: BookTestsLaw.lean); the invariant and its law at a receiving stand in Johnson/Desc/Book/BookFits.lean.
  fitsX k d          := bookFitsB d.book: A BOOL TO BE LAID BESIDE sharedX IN "shape k" (besideP: it can be laid again and again): at every border alike.
  bookFits_received  a receiving in the fence's form (Received) hands BookFits on: its first two conjuncts are what the law asks (the layout is layTrees'; statement and book are in step).
  fitsX_first · fitsX_front · fitsX_k14 · fitsX_onGu · fitsX_onGomega     EVERY BLOCK HANDS IT ON, in decide-form (the chain's end leaves the record).
  nine_fits · ten_fits   nine_paid | ten_paid's conclusions with fitsX laid beside (clause_beside).
  tenant_zero        under sharedX at 12: whatever place the book gives the message that the small record notes as o_omega has the part 0 (sharedX_twelve; layTrees_fits, Johnson/Desc/Book/BookFits.lean, at the sending's first message).
  **door_two_three** under sharedX 12 and fitsX 12: bookFitsB d.book = true ∧ tenantB ⟨d.st, d.book, ψ, d.loc.oOmega⟩ = true, for every ψ.
Limits. At St. That what the last chain takes of K14's end has d's book and o_omega's number is another file's (sharedOfEnd_ended, Johnson/Desc/Third/Law/Row0AtWords.lean). With a split (sharedX). The door's other three clauses (the statement in order · o_omega's own shape · one
sample row) are not here. It closes no row. NO SOUNDNESS.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K12.Coin.BookFitsThrough
import Johnson.Desc.Sound.BookTestsLaw
import Johnson.Desc.Sound.TenAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law.Fence
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker Desc.Plain
open Iop Prob _root_.Run
open VerifiableInference.Desc (Block FileDescription Strs Wit)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.Book (BookFits bookFits_empty layTrees_fits)

/-- **The Bool.** -/
def fitsX (_k : ℕ) (d : St) : Bool := bookFitsB d.book

theorem fitsX_iff (k : ℕ) (d : St) : fitsX k d = true ↔ BookFits d.book := bookFitsB_iff d.book

/-- A receiving in the fence's form hands BookFits on. -/
theorem bookFits_received (ft : ℕ) (sent : Array OracleNotice) (lay : TreeLay) (st : Statement)
    (bk : TreeBook) (roots : ℕ) (st' : Statement) (bk' : TreeBook) (roots' : ℕ)
    (h : Received ft sent lay st bk roots st' bk' roots') (hB : BookFits bk) : BookFits bk' := by
  obtain ⟨hl, hs, _, rb, _⟩ := h
  rw [rb]
  exact bookFits_recvBook ft bk _ sent lay st.oracles.size roots hl hs hB

theorem fitsX_first (codes : Codes) (key : TableKey) : fitsX 0 (first codes key) = true :=
  (fitsX_iff 0 _).2 bookFits_empty

theorem fitsX_front (c : Model.Verify.Chains) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (frontBlock c).decide d rs gs = .ok d')
    (hX : fitsX 0 d = true) : fitsX 1 d' = true := by
  rw [bookStep_front c d d' rs gs h]
  exact hX

/-- **K14's eight blocks hand it on.** -/
theorem fitsX_k14 (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (b : Block St Unit)
    (hb : b ∈ [b1, b2, b3, b4, b5, b6, b7, b8]) (j k : ℕ) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : b.decide d rs gs = .ok d')
    (hX : fitsX j d = true) : fitsX k d' = true := by
  have hB := (fitsX_iff j d).1 hX
  refine (fitsX_iff k d').2 ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  have own : (b = b1 ∨ b = b3 ∨ b = b4 ∨ b = b6 ∨ b = b7 ∨ b = b8) → BookFits d'.book := fun hq => by
    rw [(own_leave P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hq d rs gs d' h).1]
    exact hB
  have snd : (b = b2 ∨ b = b5) → BookFits d'.book := fun hq => by
    obtain ⟨sent, lay, hr⟩ := send_first P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hq d rs gs d' h
    exact bookFits_received _ sent lay _ _ _ _ _ _ hr hB
  rcases hb with e | e | e | e | e | e | e | e
  · exact own (.inl e)
  · exact snd (.inl e)
  · exact own (.inr (.inl e))
  · exact own (.inr (.inr (.inl e)))
  · exact snd (.inr e)
  · exact own (.inr (.inr (.inr (.inl e))))
  · exact own (.inr (.inr (.inr (.inr (.inl e)))))
  · exact own (.inr (.inr (.inr (.inr (.inr e)))))

theorem fitsX_onGu (p : P12) (he : p.early = true) (ha : p.answers = 1) (j k : ℕ) (d d' : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (Seat.onGu (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide d rs gs = .ok d')
    (hX : fitsX j d = true) : fitsX k d' = true :=
  (fitsX_iff k d').2 (onGu_bookFits p he ha d d' rs gs h ((fitsX_iff j d).1 hX))

theorem fitsX_onGomega (p : P12) (he : p.early = true) (ha : p.answers = 1) (j k : ℕ) (d d' : St)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (Seat.onGomega (proximityTestKind guardedProximityTestParts p : Block T12 Unit)).decide d rs gs = .ok d')
    (hX : fitsX j d = true) : fitsX k d' = true :=
  (fitsX_iff k d').2 (onGomega_bookFits p he ha d d' rs gs h ((fitsX_iff j d).1 hX))

/-- **At the chain's last border o_omega is part 0 of its tree.** -/
theorem tenant_zero (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (codes : Codes)
    (hlO : layTrees codes (withOmega P.S) = some layO) (hO : 0 < (withOmega P.S).size) (d : St)
    (hX : sharedX P sentU layU layO 12 d = true) (q : ℕ × ℕ)
    (hq : d.book.place[d.loc.oOmega]? = some q) : q.2 = 0 := by
  obtain ⟨_, e, p1, _⟩ := sharedX_twelve P sentU layU layO d hO hX
  rw [e, p1] at hq
  rw [← Option.some.inj hq]
  exact ((layTrees_fits hlO) 0 hO).2

/-- **THE DOOR's CLAUSES (2) AND (3).** -/
theorem door_two_three (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (codes : Codes)
    (hlO : layTrees codes (withOmega P.S) = some layO) (hO : 0 < (withOmega P.S).size) (d : St)
    (hX : sharedX P sentU layU layO 12 d = true) (hF : fitsX 12 d = true) (ψ : List E) :
    bookFitsB d.book = true ∧ tenantB ⟨d.st, d.book, ψ, d.loc.oOmega⟩ = true :=
  ⟨hF, (tenantB_iff _).2 fun q hq => tenant_zero P sentU layU layO codes hlO hO d hX q hq⟩

section
variable (cs : Codes) {Xi P₁ Cl Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ) (ms : List Mem)
  (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (c₀ : Cells) (N : NumbersS)
  (Mg : MeaningS St P₁ (Wit Cells Tok MsgT)) (Pm₀ : PromMeaning St) (Oc : P₁ → Strs → Prop)
  {Fr : Frame} (oNo : Mem → ℕ) (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay)
  (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))
  (π : P12) (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (he : π.early = true) (ha1 : π.answers = 1) (ε : Err (uLT (ckP .two) x.ds))

/-- Inside the promise with fitsX beside, it holds of the record. -/
theorem fits_of_on (k : ℕ) (a : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ N (besideP (pmX cs G ms N Pm₀ oNo P sentU layU layO) fitsX) Oc true f l k a) :
    fitsX k a.1.2 = true := ((promQ_beside N _ true f l fitsX k _).1 ha.1).2

include he ha1 in
/-- **The clause at block 9 with fitsX laid beside.** -/
theorem nine_fits
    (hb : Alike (held (P := P₁) (Seat.onGu (proximityTestKind guardedProximityTestParts π : Block T12 Unit))) x.b)
    (h : ClauseAt N (meaningSigS cs G arr (smpSt cs oNo stSh) ms decT₂ Mg)
      (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l
      (e₀H cs G arr (smpSt cs oNo stSh) ms decT₂ c₀ N true Fr) 9 x ε) :
    ClauseAt N (meaningSigS cs G arr (smpSt cs oNo stSh) ms decT₂ Mg)
      (besideP (pmX cs G ms N Pm₀ oNo P sentU layU layO) fitsX) Oc true f l
      (e₀H cs G arr (smpSt cs oNo stSh) ms decT₂ c₀ N true Fr) 9 x ε :=
  clause_beside N _ _ Oc true f l _ fitsX 9 x ε (fun a τ b ha hout => by
    obtain ⟨rs, gs, hd, _⟩ := held_decides _ x hb a b τ hout
    exact fitsX_onGu π he ha1 9 10 _ _ rs gs hd
      (fits_of_on cs G ms N Pm₀ Oc oNo P sentU layU layO f l 9 a ha)) h

include he ha1 in
/-- **The clause at block 10 with fitsX laid beside.** -/
theorem ten_fits
    (hb : Alike (held (P := P₁) (Seat.onGomega (proximityTestKind guardedProximityTestParts π : Block T12 Unit))) x.b)
    (h : ClauseAt N (meaningSigS cs G arr (smpSt cs oNo stSh) ms decT₂ Mg)
      (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l
      (e₀H cs G arr (smpSt cs oNo stSh) ms decT₂ c₀ N true Fr) 10 x ε) :
    ClauseAt N (meaningSigS cs G arr (smpSt cs oNo stSh) ms decT₂ Mg)
      (besideP (pmX cs G ms N Pm₀ oNo P sentU layU layO) fitsX) Oc true f l
      (e₀H cs G arr (smpSt cs oNo stSh) ms decT₂ c₀ N true Fr) 10 x ε :=
  clause_beside N _ _ Oc true f l _ fitsX 10 x ε (fun a τ b ha hout => by
    obtain ⟨rs, gs, hd, _⟩ := held_decides _ x hb a b τ hout
    exact fitsX_onGomega π he ha1 10 11 _ _ rs gs hd
      (fits_of_on cs G ms N Pm₀ Oc oNo P sentU layU layO f l 10 a ha)) h

end

/-- A control: a book whose one place points past its trees fails. -/
theorem fitsX_fails (k : ℕ) (codes : Codes) (key : TableKey) :
    fitsX k { first codes key with book := { trees := #[], place := #[(0, 0)] } } = false := by
  cases h : fitsX k { first codes key with book := { trees := #[], place := #[(0, 0)] } } with
  | false => rfl
  | true => exact absurd ((fitsX_iff k _).1 h) VerifiableInference.Desc.Book.past_fails

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.bookFits_received
#print axioms Desc.K14.Law.Fence.fitsX_k14
#print axioms Desc.K14.Law.Fence.fitsX_onGu
#print axioms Desc.K14.Law.Fence.fitsX_onGomega
#print axioms Desc.K14.Law.Fence.tenant_zero
#print axioms Desc.K14.Law.Fence.door_two_three
#print axioms Desc.K14.Law.Fence.nine_fits
#print axioms Desc.K14.Law.Fence.ten_fits
#print axioms Desc.K14.Law.Fence.fitsX_fails
