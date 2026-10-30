-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/NineAt.lean: **THE LEDGER's CLAUSE AT THE SHARED CHAIN's BLOCK 9 (THE PROXIMITY TEST ON G_u, WITH A SPLIT), AT THE PIECE THAT A DESCRIPTION HOLDS: THE KIND's LAW, THE PINS' AND THE PROMISE's RIDERS
PAID; WHAT IS LEFT IS NAMED.** Statements and proofs.

ClauseAt (Johnson/Desc/Sound/LedgerClause.lean) at: smp₂ := smpSt cs oNo (the sending's files' reading of a sample, Johnson/Desc/Sound/SmpShared.lean, at the member's number) · the book's reader := shiftBook N.lo · the promise
:= besideP (promSigS …) X with X := sharedX (Johnson/Desc/Sound/SharedX.lean) · the extractor := e₀H (the table's files' extS, Johnson/Desc/Sound/BordersSharedFill.lean).
  held_decides     a yes of a piece whose block is alike to held t (at whatever type of claims) is a yes of t's decision at the second part, and the first part rides.
  x_of_on          inside the promise at the border k the one X holds of the record.
  x_numbers        under X at 9 | 10: o_u's, o_omega's and o_sp's numbers are messages of the record.
  smp_nine         the test on G_u leaves smp₂ at every member of ms.
  law_nine         K12's law (GameHeldBook.lean; leads_alike) at the piece, from inside the ledger's promise, towards the kind's own conclusion QN π (NTuple …).
  **nine_paid**    THE CLAUSE. PAID HERE: the law's promise (by X) · o_sp's pin rides back · o_omega's pin rides back and past the extractor · the promise at 10: "no collision" of o_omega and o_sp · X 10.
LEFT, NAMED, EACH A PREMISE: seam (IT IS HANDED THE PIECE's YES TOO: QN π (NTuple …) ⟹ TestSays: the seam of the files on the row words_are_committed) · hrow | hcong (Say's filling; asked inside the promise at 9; hcong under agreement at o_u AND o_sp) · hrows (three classes of rows on G_omega ride back and past the extractor) ·
htab (the stored table's promise rides) · hshape (the book-keeping's own step 9 → 10)
ON THE PLAN: K12's law's own premises · the numbers (SentBefore · apartAt · hsit · hN · oNo on ms) · sentU.size = 2 = (withOmega P.S).size.
Limits. NO MEMBER. It closes no row. NO SOUNDNESS IS CLAIMED.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K12.Coin.GameHeldBook
import Johnson.Desc.K12.Coin.Alike
import Johnson.Desc.Sound.SmpShared
import Johnson.Desc.Sound.LedgerBeside
import Johnson.Desc.Sound.SharedJointCountTestsFill
import Johnson.Desc.Sound.FenceK14AtDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law.Fence
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker Desc.Plain
open Iop Prob _root_.Run
open VerifiableInference.Desc (Block FileDescription Strs Wit smpHeld)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.leave)
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0)
open H2K.First (batOneOk)

/-- A yes of a piece whose block is alike to held t is a yes of t's decision at the second part. -/
theorem held_decides {P₁ Cl W : Type} {Fr : Frame} (t : Block St Unit)
    (x : Piece (ckP .two) Fr (P₁ × St) Cl W) (hb : Alike (held (P := P₁) t) x.b)
    (a b : (P₁ × St) × Fr.E.Str) (τ : Iop.Tr (uLT (ckP .two) x.ds))
    (hout : x.ior.red.out a τ = some b) :
    ∃ rs gs, t.decide a.1.2 rs gs = .ok b.1.2 ∧ b.1.1 = a.1.1 := by
  obtain ⟨_, gs, hd⟩ := piece_yes x a τ b hout
  rw [hb.decide] at hd
  exact ⟨_, gs, decide_below_lift t a.1 b.1 _ gs hd⟩

/-- Under the one X at 9 | 10: o_u's, o_omega's and o_sp's numbers are messages of the record. -/
theorem x_numbers (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (k : ℕ)
    (hk : k = 9 ∨ k = 10) (d : St) (hX : sharedX P sentU layU layO k d = true)
    (hsU : sentU.size = 2) (hsO : (withOmega P.S).size = 2) (n : ℕ)
    (hn : n = 0 ∨ n = sentU.size ∨ n = sentU.size + 1) : n < d.st.oracles.size := by
  obtain ⟨_, hs, _, hf⟩ := (sharedX_parts P sentU layU layO k d).1 hX
  obtain ⟨pU, pO⟩ := seatX_place P sentU layU layO k d (by omega) hs
  have f2 := ((fitX_iff d).1 hf).2
  refine Nat.lt_of_lt_of_le ?_ f2
  rcases hn with rfl | rfl | rfl
  · exact (Array.getElem?_eq_some_iff.1 (pU 0 (by omega)).1).1
  · exact (Array.getElem?_eq_some_iff.1 (pO 0 (by omega)).1).1
  · exact (Array.getElem?_eq_some_iff.1 (pO 1 (by omega)).1).1

section
variable (cs : Codes) {Xi P₁ Cl Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ) (ms : List Mem)
  (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (c₀ : Cells) (N : NumbersS)
  (Mg : MeaningS St P₁ (Wit Cells Tok MsgT)) (Pm₀ : PromMeaning St) (Oc : P₁ → Strs → Prop)
  {Fr : Frame} (oNo : Mem → ℕ) (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay)
  (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))

/-- The promise at these terms. -/
abbrev pmX : PromMeaning St :=
  besideP (promSigS cs G (smpSt cs oNo stSh) ms stSh (fun s : St => shiftBook N.lo s.book) Pm₀)
    (sharedX P sentU layU layO)

/-- It is the table's files' filling of the book-keeping (promSigS) with X beside. -/
theorem pmX_eq : pmX cs G ms N Pm₀ oNo P sentU layU layO =
    promSigS cs G (smpSt cs oNo stSh) ms stSh (fun s : St => shiftBook N.lo s.book)
      (besideP Pm₀ (sharedX P sentU layU layO)) := rfl

/-- Inside the promise at the border k the one X holds of the record. -/
theorem x_of_on (k : ℕ) (a : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l k a) :
    sharedX P sentU layU layO k a.1.2 = true :=
  ((promQ_beside N _ true f l (sharedX P sentU layU layO) k _).1 ha.1).2

variable (π : P12) (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (hb : Alike (held (P := P₁) (Seat.onGu (proximityTestKind guardedProximityTestParts π : Block T12 Unit))) x.b)
  (he : π.early = true) (ha1 : π.answers = 1) (hsU : sentU.size = 2)
  (hsO : (withOmega P.S).size = 2)
  (hms : ∀ z ∈ ms, oNo z = 0 ∨ oNo z = sentU.size ∨ oNo z = sentU.size + 1)
include hb he ha1 hsU hsO hms

/-- **The test on G_u leaves smp₂ at every member.** -/
theorem smp_nine (a b : (P₁ × St) × Fr.E.Str) (τ : Iop.Tr (uLT (ckP .two) x.ds))
    (ha : onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 9 a)
    (hout : x.ior.red.out a τ = some b) :
    ∀ z ∈ ms, smpSt cs oNo stSh b.1.2 z.1 z.2 = smpSt cs oNo stSh a.1.2 z.1 z.2 := by
  intro z hz
  have hX := x_of_on cs G ms N Pm₀ Oc oNo P sentU layU layO f l 9 a ha
  obtain ⟨rs, gs, hd, _⟩ := held_decides _ x hb a b τ hout
  have hm := (membX_nine _ _ ((sharedX_parts P sentU layU layO 9 _).1 hX).2.2.1).2
  refine smpSt_onGu cs oNo π he ha1 _ _ rs gs hd z
    (x_numbers P sentU layU layO 9 (.inl rfl) _ hX hsU hsO _ (hms z hz)) ?_
  rw [hm]
  intro e
  have e' : 1 = oNo z := Option.some.inj e
  rcases hms z hz with h | h | h <;> omega


variable (t₁ t₂ c : ℕ) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (dB : RDT)
  (dt : List RDT) (e : ℕ) (εt : Err (uLT (ckP .two) dt)) (r : Fmt.M1.Stage → ℕ)
  (ε : Err (uLT (ckP .two) x.ds)) (h0 : x.back = []) (hds : x.ds = dB :: dt)
  (herr : HEq ε ((e, εt) : Err (uLT (ckP .two) (dB :: dt))))
  (hA : AtPlace Fr π (VerifiableInference.Desc.numAt t₁ t₂ c) L mC mS mW rad x.base dB dt εt)
  (hr : ∀ s, rad s = r s.st) (hj : johOk π r = true) (hb1 : batOneOk π = true)
  (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e)
  (ho : π.nums.ownMask = false) (hP : ownLabelsB π = true)
  (n2 : ∀ n, n < π.nums.free → VerifiableInference.Desc.numAt t₁ t₂ c (.own n) < x.base)
  (n3 : ∀ c' n, (c' + 1, n) ∈ π.before →
    VerifiableInference.Desc.numAt t₁ t₂ c (.taken c' n) < x.base)
  (hft : π.nums.firstTree = P.par.toGPar.firstTree)

omit he ha1 hsU hsO hms in
include h0 hds herr hA hr hj hb1 hle ho hP n2 n3 hft in
/-- **K12's law at the piece, from inside the ledger's promise.** -/
theorem law_nine :
    x.ior.red.Leads (onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 9)
      (fun a _ => ∃ t, inGu a.1.2 = .ok t ∧ QN π (NTuple Fr π (noAt t₁ t₂ c) rad rd) (t, a.2)) ε := by
  have k := k12_held_onGu_book P₁ Fr (Wit Cells Tok MsgT) π t₁ t₂ c L mC mS mW rad rd x.base dB dt e εt
    r ⟨held (P := P₁) (Seat.onGu (proximityTestKind guardedProximityTestParts π : Block T12 Unit)), x.base, x.ds, x.back,
      fun _ _ w => w, ε⟩ rfl h0 rfl hds herr hA hr hj hb1 hle ho hP n2 n3
  have k' := leads_alike
    (⟨held (P := P₁) (Seat.onGu (proximityTestKind guardedProximityTestParts π : Block T12 Unit)), x.base, x.ds, x.back,
      fun _ _ w => w, ε⟩ : Piece (ckP .two) Fr (P₁ × St) Unit (Wit Cells Tok MsgT))
    ({ x with err := ε } : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) hb rfl rfl rfl
    HEq.rfl _ _ k
  refine Reduction.Leads.conseq (K := x.ior.red) k' (fun a ha => ?_) fun a _ _ _ _ hq => ?_
  · exact sharedX_gives_nine P sentU layU layO π hft _
      (x_of_on cs G ms N Pm₀ Oc oNo P sentU layU layO f l 9 a ha)
  · obtain ⟨⟨t, _, ht, _, hQ⟩, _⟩ := hq
    exact ⟨t, ht, hQ⟩

variable (Say : St → RowS → Tup cs → Prop)

include h0 hds herr hA hr hj hb1 hle ho hP n2 n3 hft in
/-- **THE CLAUSE AT BLOCK 9.** -/
theorem nine_paid
    (seam : ∀ a τ b t, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 9 a →
      x.ior.red.out a τ = some b →
      inGu a.1.2 = .ok t → QN π (NTuple Fr π (noAt t₁ t₂ c) rad rd) (t, a.2) →
      TestSays N f l Say (candT cs G (smpSt cs oNo stSh) ms N) 9 .oU [.oSp]
        [.sample .oU, .recG, .loc, .foldU] a)
    (hsit : ∃ y ∈ ms, SitsAt y (N.tenant .oU).1 (N.tenant .oU).2)
    (hN : ((mineS N ms true 9).map (numOf arr)).Nodup)
    (hapS : apartAt N arr true 9 (.msg .oSp) = true)
    (hapO : apartAt N arr true 9 (.msg .oOmega) = true)
    (sb : ∀ m, m = Msg2.oOmega ∨ m = .oSp → SentBefore N f l 9 x m)
    (hrow : ∀ q ∈ [RowS.sample .oU, .recG, .loc, .foldU], ∀ a, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 9 a → ∀ w,
      Say a.1.2 q (rgT cs arr w) → Mg.row q a.1.2 w)
    (hcong : ∀ q ∈ [RowS.sample .oU, .recG, .loc, .foldU], ∀ a, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 9 a → ∀ m m',
      (∀ μ, μ = Msg2.oU ∨ μ ∈ [Msg2.oSp] → sameT cs ms N μ m m') → Say a.1.2 q m → Say a.1.2 q m')
    (htab : ∀ a τ b, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 9 a →
      x.ior.red.out a τ = some b → Pm₀.tablePromise b.1.2 (strsOfAct Fr ((actQ N f l 10).2 b)))
    (hshape : ∀ a τ b, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 9 a →
      x.ior.red.out a τ = some b → Pm₀.shape 10 b.1.2 = true)
    (hrows : ∀ i ∈ [ItemS.row (.sample .oOmega), .row (.sample .oSp), .row .foldOmega], ∀ a τ b w,
      onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 9 a →
      x.ior.red.out a τ = some b →
      muQ N (meaningSigS cs G arr (smpSt cs oNo stSh) ms decT₂ Mg) f l i 10 ((actQ N f l 10).2 b) w →
      muQ N (meaningSigS cs G arr (smpSt cs oNo stSh) ms decT₂ Mg) f l i 9 ((actQ N f l 9).2 a)
        (e₀H cs G arr (smpSt cs oNo stSh) ms decT₂ c₀ N true Fr 9 ((actQ N f l 9).2 a) w)) :
    ClauseAt N (meaningSigS cs G arr (smpSt cs oNo stSh) ms decT₂ Mg)
      (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l
      (e₀H cs G arr (smpSt cs oNo stSh) ms decT₂ c₀ N true Fr) 9 x ε := by
  have hsm := smp_nine cs G ms N Pm₀ Oc oNo P sentU layU layO f l π x hb he ha1 hsU hsO hms
  refine nine_split_sig cs G arr (smpSt cs oNo stSh) ms decT₂ c₀ stSh
    (fun s : St => shiftBook N.lo s.book) N Mg (besideP Pm₀ (sharedX P sentU layU layO)) Oc Say f l x
    ε hsit hN hapS ?_ ?_ hrow hcong ?_ ?_
  · exact Reduction.Leads.conseq (K := x.ior.red)
      (law_nine cs G ms N Pm₀ Oc oNo P sentU layU layO f l π x hb t₁ t₂ c L mC mS mW rad rd dB dt e εt
        r ε h0 hds herr hA hr hj hb1 hle ho hP n2 n3 hft) (fun _ ha => ha)
      fun a τ b ha hb hq => by
        obtain ⟨t, ht, hQ⟩ := hq
        exact seam a τ b t ha hb ht hQ
  · intro a τ b w ha hout h
    exact pin_rides cs G arr (smpSt cs oNo stSh) ms decT₂ N Mg f l 9 x .oSp (sb _ (.inr rfl)) a b τ
      hout (fun z hz => (hsm a b τ ha hout z hz).symm) w h
  · intro a τ b ha hout q hq
    have e10 : promsAt true 10 = [.tablePromise, .shape 10, .noColl .oOmega, .noColl .oSp] :=
      promsAt_tests.2.1
    rw [e10] at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    obtain ⟨rs, gs, hd, _⟩ := held_decides _ x hb a b τ hout
    have hX := x_of_on cs G ms N Pm₀ Oc oNo P sentU layU layO f l 9 a ha
    rcases hq with rfl | rfl | rfl | rfl
    · exact htab a τ b ha hout
    · exact Bool.and_eq_true_iff.2 ⟨hshape a τ b ha hout,
        sharedX_onGu P sentU layU layO π hft he ha1 _ _ rs gs hd hX⟩
    · exact noColl_rides cs G (smpSt cs oNo stSh) ms stSh (fun s : St => shiftBook N.lo s.book) N _ f l
        9 x .oOmega (sb _ (.inl rfl)) a b τ hout (hsm a b τ ha hout)
        (ha.1 (.noColl .oOmega) (by decide))
    · exact noColl_rides cs G (smpSt cs oNo stSh) ms stSh (fun s : St => shiftBook N.lo s.book) N _ f l
        9 x .oSp (sb _ (.inr rfl)) a b τ hout (hsm a b τ ha hout)
        (ha.1 (.noColl .oSp) (by decide))
  · intro i hi a τ b w ha hout h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | hi
    · exact pin_past_ext cs G arr (smpSt cs oNo stSh) ms decT₂ c₀ N true 9 .oOmega (by decide) hapO _ w
        (pin_rides cs G arr (smpSt cs oNo stSh) ms decT₂ N Mg f l 9 x .oOmega (sb _ (.inl rfl)) a b τ
          hout (fun z hz => (hsm a b τ ha hout z hz).symm) w h)
    · exact hrows i (by simpa using hi) a τ b w ha hout h

end

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.held_decides
#print axioms Desc.K14.Law.Fence.x_numbers
#print axioms Desc.K14.Law.Fence.x_of_on
#print axioms Desc.K14.Law.Fence.smp_nine
#print axioms Desc.K14.Law.Fence.law_nine
#print axioms Desc.K14.Law.Fence.nine_paid
