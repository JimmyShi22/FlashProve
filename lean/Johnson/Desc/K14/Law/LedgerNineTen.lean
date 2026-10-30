-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerNineTen.lean: THE LEDGER's CLAUSES AT THE SHARED CHAIN's TWO PROXIMITY
TESTS (BLOCKS 9 AND 10) AT OUR FILLING, AND THE WALK OF WHAT STANDS BESIDE shapeK FROM THE CHAIN's
FIRST RECORD TO ITS LAST BORDER. share_seamed (Johnson/Desc/K14/Law/LedgerSeamRow.lean) has two
premises h9 | h10. HERE THEY ARE HAD, to the letter, from nine_paid | ten_paid
(Johnson/Desc/Sound/NineAt.lean, TenAt.lean) BY NAME, at Mg := our mgI, Pm₀ := pmE, Say := our SayK
(Johnson/Desc/K14/Law/LedgerSay.lean).

  EK, XK          **the test that is meant in pmK's slot X**: sharedX && (the
                  record's codes are the plan's: codX) && (o_omega, o_u, o_sp have each the plan's
                  shape, the mark and its sample rows: omY, msgY) && (the statement is tidy: tidY).
  pmE, pmK_is     the letter Pm₀ of pmX, filled; our promise at XK IS pmX at
                  pmE, as terms.
  beside_of_on    inside the promise at a border: each of the tests.
  XK_first, XK_front, XK_point, handsAt_XK   **THE WALK**: at the chain's first record K14.first
                  Q.codes key: by make (Tidy.start; the codes; no message) · the front leaves the
                  record · "LIN point", at the piece · the kind's other seven and the end: HandsAt,
                  as share_filled | share_seamed ask it. Over blocks 9 and 10 XK is handed on INSIDE
                  nine_at_K | ten_at_K (their conclusions hold the promise behind).
  nine_at_K, ten_at_K   **h9 | h10.** seam := seam_nine | seam_ten from ITS CORE
                  (TupleNine | TupleTen: a premise) · hrow := say_row · hcong := cong_nine_at |
                  cong_ten_at · htab := tab_rides where the test leaves the small record · hshape :=
                  the four tests' hand-ons over the test (layX_codes · codX_onGu · omY_onGu ·
                  onGu_tidy, whose Codes.lengthsOk comes from codX and ONE TEST ON THE
                  PLAN: hl) · hrows (at 9): (fold_omega) by foldOmega_nine; THE
                  TWO SAMPLES' CLASSES HERE, under "the statement is in order", from the filling's
                  equation hsmp: so its bare premises SampleOwn | SampleRides on the letter Mg₀ are
                  NOT asked.
WHAT STAYS. THE CORE (TupleNine | TupleTen: at a yes, under the promise, from K12's law's end: one
tuple of typed messages of which the test's rows say their claims and which is a candidate at the
laid and the kept message): stated in SeamCore.lean; other files' to show, K12's among them · K12's
law's own premises on the plan and the written rounds (hb … hft: theirs, to the letter) · hsmp (the
samples' rows are filled by SmpSay: an equation of a letter) · hdk (the decoder reads the record's
key alone) · hl (the plan's codes' lengths) · the plan's mem | num | ms | N at the three messages ·
hN, hapS, hapO, sb (numbers) · hP10 | hP11 (the letter Pm₁'s book-keeping at 10 | 11) · in the walk:
hp (the kind's blocks' tests on the plan), hlU, hlO, hS, hm, hk.
What is not claimed. NO MEMBER IS SHOWN. It closes no row. No soundness of a verifier; no level.

-/
import Johnson.Desc.Sound.NineAt
import Johnson.Desc.Sound.TenAt
import Johnson.Desc.Sound.HrowsNineG
import Johnson.Desc.Sound.SeamCore
import Johnson.Desc.K12.Coin.TidyThrough
import Johnson.Desc.K14.Law.LedgerTidy
import Johnson.Desc.K14.Law.LedgerNew
import Johnson.Desc.K14.Law.LedgerSeamRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker Desc.Plain Cb Johnson.Pack
open Iop Prob _root_.Run
open VerifiableInference.Desc (Block FileDescription Strs Wit Grows)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open OnBytes.Means (Tidy InOrder)

/-- **What is laid beside shapeK and sharedX**: the record's codes are the
plan's · o_omega, o_u and o_sp have each its shape by the plan, its mark and its sample rows · the
statement is tidy · AND A LETTER: whatever else is laid. sO: the three shapes (o_u's, o_omega's,
o_sp's) and that letter Y : ℕ → St → Bool. -/
def EK (Q : P14) (sO : OracleShape × OracleShape × OracleShape × (ℕ → St → Bool)) (nO : ℕ) :
    ℕ → St → Bool :=
  fun k s => codX Q k s && omY sO.2.1 nO k s && tidY k s && msgY sO.1 0 2 k s &&
    msgY sO.2.2.1 (nO + 1) 5 k s && sO.2.2.2 k s

theorem EK_iff (Q : P14) (sO : OracleShape × OracleShape × OracleShape × (ℕ → St → Bool)) (nO k : ℕ)
    (s : St) : EK Q sO nO k s = true ↔ codX Q k s = true ∧ omY sO.2.1 nO k s = true ∧
      tidY k s = true ∧ msgY sO.1 0 2 k s = true ∧ msgY sO.2.2.1 (nO + 1) 5 k s = true ∧
      sO.2.2.2 k s = true := by
  unfold EK
  simp only [Bool.and_eq_true, and_assoc]

/-- **The test that is meant in pmK's slot X.** -/
def XK (Q : P14) (sentU : Array OracleNotice) (layU layO : TreeLay)
    (sO : OracleShape × OracleShape × OracleShape × (ℕ → St → Bool)) (nO : ℕ) : ℕ → St → Bool :=
  fun k s =>
  sharedX Q sentU layU layO k s && EK Q sO nO k s

variable {Cells : Type} (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells)
  (Pm₁ : PromMeaning St) (Q : P14) (n nU nO : ℕ)
  (sO : OracleShape × OracleShape × OracleShape × (ℕ → St → Bool))

/-- The letter Pm₀ of pmX, filled: our pmI with the layout's test and EK beside.
    -/
abbrev pmE : PromMeaning St :=
  besideP (pmI decT₂ Pm₁ Q.par n nU nO) fun k s => layX Q k s && EK Q sO nO k s

variable (cs : Codes) {Xi P₁ Cl Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ) (ms : List Mem)
  (c₀ : Cells) (N : NumbersS) (Mg₀ : MeaningS St P₁ (Wit Cells Tok MsgT)) (Oc : P₁ → Strs → Prop)
  {Fr : Frame} (oNo : Mem → ℕ) (sentU : Array OracleNotice) (layU layO : TreeLay)
  (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (l : List (Piece (ckP .two) Fr (P₁ ×
      St) Cl (Wit Cells Tok MsgT)))
  (mem : ℕ → Option Mem) (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE)
  (e' : ℕ) (num : Msg2 → ℕ)

/-- **Our promise at XK is pmX at pmE**: as terms. -/
theorem pmK_is : pmK cs G (smpSt cs oNo stSh) ms decT₂ (shiftBook N.lo) Pm₁ n nU nO Q
      (XK Q sentU layU layO sO nO) = (pmX cs G ms N (pmE decT₂ Pm₁ Q n nU nO sO) oNo Q sentU layU
          layO) := by
  have e : (fun (k : ℕ) (s : St) => (pmI decT₂ Pm₁ Q.par n nU nO).shape k s &&
        (layX Q k s && (sharedX Q sentU layU layO k s && EK Q sO nO k s))) =
      fun k s => ((pmI decT₂ Pm₁ Q.par n nU nO).shape k s && (layX Q k s && EK Q sO nO k s)) &&
        sharedX Q sentU layU layO k s := by
    funext k s
    cases (pmI decT₂ Pm₁ Q.par n nU nO).shape k s <;> cases layX Q k s <;>
      cases sharedX Q sentU layU layO k s <;> cases EK Q sO nO k s <;> rfl
  show PromMeaning.mk _ _ _ _ _ _ = PromMeaning.mk _ _ _ _ _ _
  exact congrArg (fun sh => PromMeaning.mk _ _ _ _ sh _) e

/-- Inside the promise at border k: what stands beside shapeK. -/
theorem beside_of_on (k : ℕ) (a : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ N (pmX cs G ms N (pmE decT₂ Pm₁ Q n nU nO sO) oNo Q sentU layU layO) Oc true f l k a)
        :
    sharedX Q sentU layU layO k a.1.2 = true ∧ layX Q k a.1.2 = true ∧
      EK Q sO nO k a.1.2 = true ∧ (pmI decT₂ Pm₁ Q.par n nU nO).shape k a.1.2 = true := by
  have hX := Fence.x_of_on cs G ms N (pmE decT₂ Pm₁ Q n nU nO sO) Oc oNo Q sentU layU layO f l k a
      ha
  have h0 := ((promQ_beside N _ true f l (sharedX Q sentU layU layO) k _).1 ha.1).1
  have hk : PromS.shape k ∈ promsAt true k := by
    unfold promsAt
    simp
  have h1 : (pmE decT₂ Pm₁ Q n nU nO sO).shape k a.1.2 = true := h0 (.shape k) hk
  obtain ⟨h2, h3⟩ := Bool.and_eq_true_iff.1 h1
  obtain ⟨h4, h5⟩ := Bool.and_eq_true_iff.1 h3
  exact ⟨hX, h4, h5, h2⟩

/-! ## The walk of XK: from the chain's first record through every block -/

section walk
open VerifiableInference.Desc.K1 (shapesOf shapeAt sampledAt)

/-- XK, with the brackets to the left, in the order in which the tests are earned. -/
theorem XK_eq : XK Q sentU layU layO sO nO = fun k s =>
    (((((sharedX Q sentU layU layO k s && codX Q k s) && omY sO.2.1 nO k s) && msgY sO.1 0 2 k s) &&
      msgY sO.2.2.1 (nO + 1) 5 k s) && tidY k s) && sO.2.2.2 k s := by
  funext k s
  unfold XK EK
  cases sharedX Q sentU layU layO k s <;> cases codX Q k s <;> cases omY sO.2.1 nO k s <;>
    cases tidY k s <;> cases msgY sO.1 0 2 k s <;> cases msgY sO.2.2.1 (nO + 1) 5 k s <;>
    cases sO.2.2.2 k s <;> rfl

theorem XK_iff (k : ℕ) (s : St) : XK Q sentU layU layO sO nO k s = true ↔
    sharedX Q sentU layU layO k s = true ∧ codX Q k s = true ∧ omY sO.2.1 nO k s = true ∧
      tidY k s = true ∧ msgY sO.1 0 2 k s = true ∧ msgY sO.2.2.1 (nO + 1) 5 k s = true ∧
      sO.2.2.2 k s = true := by
  unfold XK
  rw [Bool.and_eq_true, EK_iff]

/-- **At the chain's first record**: by make. -/
theorem XK_first (key : TableKey) (hY : sO.2.2.2 0 (first Q.codes key) = true) :
    XK Q sentU layU layO sO nO 0 (first Q.codes key) = true :=
  (XK_iff Q nO sO sentU layU layO 0 _).2 ⟨sharedX_first Q sentU layU layO Q.codes key,
    codX_first Q key, (omY_iff sO.2.1 nO 0 _).2 (Or.inl (by omega)),
    (tidY_iff 0 _).2 (OnBytes.Means.Tidy.start Q.codes), (msgY_iff _ _ _ 0 _).2 (Or.inl (by omega)),
    (msgY_iff _ _ _ 0 _).2 (Or.inl (by omega)), hY⟩

/-- **The front** leaves the record. -/
theorem XK_front (c : Model.Verify.Chains) (d d' : St) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (frontBlock c).decide d rs gs = .ok d')
    (hY : ∀ s, sO.2.2.2 0 s = true → sO.2.2.2 1 s = true)
    (hx : XK Q sentU layU layO sO nO 0 d = true) : XK Q sentU layU layO sO nO 1 d' = true := by
  obtain ⟨h1, h2, _, h4, _, _, h7⟩ := (XK_iff Q nO sO sentU layU layO 0 d).1 hx
  refine (XK_iff Q nO sO sentU layU layO 1 d').2 ⟨sharedX_front Q sentU layU layO c d d' rs gs h h1,
    codX_front Q c d d' rs gs h h2, (omY_iff sO.2.1 nO 1 _).2 (Or.inl (by omega)), ?_,
    (msgY_iff _ _ _ 1 _).2 (Or.inl (by omega)), (msgY_iff _ _ _ 1 _).2 (Or.inl (by omega)), ?_⟩
  · rw [bookStep_front c d d' rs gs h]
    exact h4
  · rw [bookStep_front c d d' rs gs h]
    exact hY d h7

variable (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
  (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hUw : withU Q.S = some sentU)
  (hlU : layTrees Q.codes sentU = some layU) (hlO : layTrees Q.codes (withOmega Q.S) = some layO)
  (hS : Q.S.sharedSplitNeeded = true) (hm : Q.par.S.masksAhead = true)
  (hp : ∀ b ∈ [b1, b2, b3, b4, b5, b6, b7, b8], b.planOk = true)

include hbl hUw hlU hlO hS hm hp

/-- **"LIN point"**, at the piece. -/
theorem XK_point (c1 : Block St Cl) (hc : DecidesAs c1 b1) (hr : c1.rounds = b1.rounds)
    (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (hx : x.b = heldW c1) (a : (P₁ × St)
        × Fr.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) x.ds)) (y : (P₁ × St) × Fr.E.Str)
    (hout : x.ior.red.out a τ = some y) (hY : sO.2.2.2 2 y.1.2 = true)
    (h : XK Q sentU layU layO sO nO 1 a.1.2 = true) : XK Q sentU layU layO sO nO 2 y.1.2 = true :=
        by
  obtain ⟨h1, h2, _, h4, _, _, _⟩ := (XK_iff Q nO sO sentU layU layO 1 _).1 h
  obtain ⟨rs, gs, hd⟩ := held_yes x c1 hx a τ y hout
  rw [hc] at hd
  have hB : blocksOr Q = [b1, b2, b3, b4, b5, b6, b7, b8] := by
    unfold blocksOr
    rw [hbl]
    rfl
  exact (XK_iff Q nO sO sentU layU layO 2 _).2
    ⟨sharedX_k14 Q b1 b2 b3 b4 b5 b6 b7 b8 hbl sentU hUw layU layO hlU hlO hS hm 0 b1 rfl _ _ rs gs
        hd
        h1,
      codX_k14 Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b1 (by simp) 1 2 _ _ rs gs hd h2,
      (omY_iff sO.2.1 nO 2 _).2 (Or.inl (by omega)),
      tidy_piece Q b1 (by rw [hB]; simp) (hp b1 (by simp)) c1 hc hr x hx a τ y hout 1 2 h4,
      (msgY_iff _ _ _ 2 _).2 (Or.inl (by omega)), (msgY_iff _ _ _ 2 _).2 (Or.inl (by omega)), hY⟩

/-- **The kind's other seven and the end: HandsAt for XK**, at the three messages' shapes by the
plan (o_u: the first of "send o_u"; o_omega, o_sp: the first and the second of "send o_omega") and
nO := the number of o_u's sending's messages. -/
theorem handsAt_XK (on : ℕ → (P₁ × St) × Fr.E.Str → Prop)
    (hU0 : 0 < (shapesOf (parU Q sentU)).length) (hkU : sampledAt (parU Q sentU) ⟨0, hU0⟩)
    (h0 : 0 < (shapesOf (parO Q)).length) (hk : sampledAt (parO Q) ⟨0, h0⟩)
    (h1 : 1 < (shapesOf (parO Q)).length) (hkS : sampledAt (parO Q) ⟨1, h1⟩) (Y : ℕ → St → Bool)
    (hY : HandsAt (Cl := Cl) (Cells := Cells) (Tok := Tok) on [b1, b2, b3, b4, b5, b6, b7, b8] Y)
    (hon : ∀ k a, on k a → XK Q sentU layU layO (shapeAt (parU Q sentU) ⟨0, hU0⟩,
      shapeAt (parO Q) ⟨0, h0⟩, shapeAt (parO Q) ⟨1, h1⟩, Y) sentU.size k a.1.2 = true) :
    HandsAt (Cl := Cl) (Cells := Cells) (Tok := Tok) on [b1, b2, b3, b4, b5, b6, b7, b8]
      (XK Q sentU layU layO (shapeAt (parU Q sentU) ⟨0, hU0⟩, shapeAt (parO Q) ⟨0, h0⟩,
        shapeAt (parO Q) ⟨1, h1⟩, Y) sentU.size) := by
  rw [XK_eq]
  obtain ⟨u, hu, e2, e5⟩ := blocks_two Q b1 b2 b3 b4 b5 b6 b7 b8 hbl
  obtain rfl : u = sentU := Option.some.inj (hu.symm.trans hUw)
  have mb : ∀ k d, sharedX Q u layU layO k d = true → membX u.size k d = true := fun k d h =>
    ((sharedX_parts Q u layU layO k d).1 h).2.2.1
  have hA := (handsOn_sharedX Q b1 b2 b3 b4 b5 b6 b7 b8 hbl u hUw layU layO hlU hlO hS hm).and
    (handsOn_codX Q b1 b2 b3 b4 b5 b6 b7 b8 hbl)
  have hB := hands_omY Q b1 b2 b3 b4 b5 b6 b7 b8 hbl _ hA u.size (fun d hd =>
    ((membX45 u.size d 5 (.inr rfl)).1 (mb 5 d (Bool.and_eq_true_iff.1 hd).1)).2.2.2.1) h0 hk
  have hC := hands_msgY Q b1 b2 b3 b4 b5 b6 b7 b8 hbl _ hB 1 _ _ _ _ _ (behindU_book Q.par)
    (by rw [e2]; rfl) 0 (fun d hd => ((membX2 u.size d).1 (mb 2 d (Bool.and_eq_true_iff.1
      (Bool.and_eq_true_iff.1 hd).1).1)).2.2.2) ⟨0, hU0⟩ hkU (by omega)
  have hD := hands_msgY Q b1 b2 b3 b4 b5 b6 b7 b8 hbl _ hC 4 _ _ _ _ _ (behindOmega_book Q.par)
    (by rw [e5]; rfl) u.size (fun d hd => ((membX45 u.size d 5 (.inr rfl)).1 (mb 5 d
      (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hd).1).1).1)).2.2.2.1)
    ⟨1, h1⟩ hkS (by omega)
  have hE := HandsAt.tidy (Cl := Cl) (Cells := Cells) (Tok := Tok) Q b1 b2 b3 b4 b5 b6 b7 b8 hbl hp
    (hD.at on fun k a ha => by
      obtain ⟨g1, g2, g3, _, g5, g6, _⟩ := (XK_iff Q u.size _ u layU layO k _).1 (hon k a ha)
      exact Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2 ⟨Bool.and_eq_true_iff.2
        ⟨Bool.and_eq_true_iff.2 ⟨g1, g2⟩, g3⟩, g5⟩, g6⟩) fun k a ha =>
    ((XK_iff Q u.size _ u layU layO k _).1 (hon k a ha)).2.2.2.1
  exact ⟨fun i b hi hb c hc hr x hx a τ y ha hout => Bool.and_eq_true_iff.2
      ⟨hE.step i b hi hb c hc hr x hx a τ y ha hout, hY.step i b hi hb c hc hr x hx a τ y ha hout⟩,
    fun s z h => Bool.and_eq_true_iff.2 ⟨hE.zeta s z (Bool.and_eq_true_iff.1 h).1,
      hY.zeta s z (Bool.and_eq_true_iff.1 h).2⟩,
    fun s h => Bool.and_eq_true_iff.2 ⟨hE.last s (Bool.and_eq_true_iff.1 h).1,
      hY.last s (Bool.and_eq_true_iff.1 h).2⟩⟩

end walk

section nine
variable (π : P12) (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (hb : Alike (held (P := P₁) (Seat.onGu (proximityTestKind guardedProximityTestParts π : Block T12 Unit))) x.b)
  (he : π.early = true) (ha1 : π.answers = 1) (hsU : sentU.size = 2)
  (hsO : (withOmega Q.S).size = 2)
  (hms : ∀ z ∈ ms, oNo z = 0 ∨ oNo z = sentU.size ∨ oNo z = sentU.size + 1)
  (t₁ t₂ c : ℕ) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rdN : ℕ → ℕ) (dB : RDT)
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
  (hft : π.nums.firstTree = Q.par.toGPar.firstTree)
  (hnO : nO = sentU.size) (hl : Q.codes.lengthsOk = true)
  (hdk : ∀ c (s s' : St), s'.loc.key = s.loc.key → decT₂ c s' = decT₂ c s)
  (hsmp : ∀ μ s w, Mg₀.row (.sample μ) s w ↔ SmpSay (num μ) s (rgOf cs arr mem rd w))
  (hn0 : num .oU = 0) (hn1 : num .oOmega = sentU.size) (hn2 : num .oSp = sentU.size + 1)
  (xU xO xS : Mem) (hmU : mem 0 = some xU) (hmO : mem sentU.size = some xO)
  (hmS : mem (sentU.size + 1) = some xS) (mU : xU ∈ ms) (mO : xO ∈ ms) (mS' : xS ∈ ms)
  (sitU : SitsAt xU (N.tenant .oU).1 (N.tenant .oU).2)
  (sitO : SitsAt xO (N.tenant .oOmega).1 (N.tenant .oOmega).2)
  (sitS : SitsAt xS (N.tenant .oSp).1 (N.tenant .oSp).2)

include hb he ha1 hsU hsO hms h0 hds herr hA hr hj hb1 hle ho hP n2 n3 hft hnO hl hdk hsmp hn0
  hn1 hn2 hmU hmO hmS mU mO mS' sitU sitO sitS

/-- **THE LEDGER's CLAUSE AT BLOCK 9, AT OUR FILLING**: h9 of share_seamed, by
nine_paid BY NAME. -/
theorem nine_at_K
    (core : TupleNine cs G ms N (pmE decT₂ Pm₁ Q n nU nO sO) Oc oNo Q sentU layU layO f l mem rd π
        t₁ t₂ c rad rdN x)
    (hN : ((mineS N ms true 9).map (VerifiableInference.Desc.Sound.numOf arr)).Nodup)
    (hapS : apartAt N arr true 9 (.msg .oSp) = true)
    (hapO : apartAt N arr true 9 (.msg .oOmega) = true)
    (sb : ∀ m, m = Msg2.oOmega ∨ m = .oSp → SentBefore N f l 9 x m)
    (hP10 : ∀ a τ b, onQ₂ N (pmX cs G ms N (pmE decT₂ Pm₁ Q n nU nO sO) oNo Q sentU layU layO) Oc
        true f l 9 a → x.ior.red.out a τ = some b →
      Pm₁.shape 10 b.1.2 = true)
    (hY10 : ∀ a τ b, onQ₂ N (pmX cs G ms N (pmE decT₂ Pm₁ Q n nU nO sO) oNo Q sentU layU layO) Oc
        true f l 9 a → x.ior.red.out a τ = some b →
      sO.2.2.2 10 b.1.2 = true) :
    ClauseAt N (mgK cs G arr (smpSt cs oNo stSh) ms decT₂ Mg₀ mem rd e' n nO Q)
      (pmK cs G (smpSt cs oNo stSh) ms decT₂ (shiftBook N.lo) Pm₁ n nU nO Q (XK Q sentU layU layO sO
          nO)) Oc true
      f l (exK cs G arr (smpSt cs oNo stSh) ms decT₂ c₀ N Fr) 9 x ε := by
  rw [pmK_is]
  have hon := fun a ha => beside_of_on decT₂ Pm₁ Q n nU nO sO cs G ms N Oc oNo sentU layU layO f l 9
      a ha
  have hTd : ∀ a, onQ₂ N (pmX cs G ms N (pmE decT₂ Pm₁ Q n nU nO sO) oNo Q sentU layU layO) Oc true
      f l 9 a → tidY 9 a.1.2 = true := fun a ha =>
    ((EK_iff Q sO nO 9 _).1 (hon a ha).2.2.1).2.2.1
  have hMb : ∀ a, onQ₂ N (pmX cs G ms N (pmE decT₂ Pm₁ Q n nU nO sO) oNo Q sentU layU layO) Oc true
      f l 9 a → membX sentU.size 9 a.1.2 = true := fun a ha =>
    ((sharedX_parts Q sentU layU layO 9 _).1 (hon a ha).1).2.2.1
  refine nine_paid cs G arr ms decT₂ c₀ N (mgI cs arr Mg₀ mem rd Q.par (uRK Q.par) (omWK cs arr mem
      rd nO Q) e' n) (pmE decT₂ Pm₁ Q n nU nO sO) Oc oNo Q sentU layU layO f l π x hb he ha1 hsU
    hsO hms t₁ t₂ c L mC mS mW rad rdN dB dt e εt r ε h0 hds herr hA hr hj hb1 hle ho hP n2 n3 hft
    (SayK cs mem rd Q.par n num) ?seam ⟨xU, mU, sitU⟩ hN hapS hapO sb ?hrow ?hcong ?htab ?hshape
    ?hrows
  case seam =>
    exact seam_nine cs G ms N (pmE decT₂ Pm₁ Q n nU nO sO) Oc oNo Q sentU layU layO f l mem rd Q.par
        n num π t₁ t₂ c rad rdN x
      hsU hsO core (fun a ha => ((tidY_iff 9 _).1 (hTd a ha)).kinds) hn0
  case hrow =>
    exact fun q _ a _ w h => say_row cs arr mem rd Mg₀ Q.par (uRK Q.par) (omWK cs arr mem rd nO Q)
        e' n
      num (fun μ s w => (hsmp μ s w).2) q a.1.2 w h
  case hcong =>
    exact fun q hq a ha m m' hs h => cong_nine_at cs mem rd ms N Q.par n num sentU.size a.1.2 (hTd a
        ha)
      (hMb a ha) hn0 xU xS hmU hmS mU mS' sitU sitS m m' hs q hq h
  case htab =>
    intro a τ b ha hout
    obtain ⟨rs, gs, hd, _⟩ := held_decides _ x hb a b τ hout
    have lv := onGu_leaves π he ha1 _ _ rs gs hd
    exact tab_rides decT₂ N f l hdk 9 x a b τ hout (by rw [lv.2.2.2.1])
      (ha.1 .tablePromise (by decide))
  case hshape =>
    intro a τ b ha hout
    obtain ⟨rs, gs, hd, _⟩ := held_decides _ x hb a b τ hout
    have lv := onGu_leaves π he ha1 _ _ rs gs hd
    obtain ⟨_, hL, hE, _⟩ := hon a ha
    obtain ⟨e1, e2, e3, e4, e5, _⟩ := (EK_iff Q sO nO 9 _).1 hE
    have hl' : a.1.2.st.codes.lengthsOk = true := by
      rw [(codX_iff Q 9 _).1 e1]
      exact hl
    have hm : a.1.2.loc.firstMask ≠ some nO := by
      rw [(membX_nine sentU.size _ (hMb a ha)).2, hnO, hsU]
      decide
    have hm0 : a.1.2.loc.firstMask ≠ some 0 := by
      rw [(membX_nine sentU.size _ (hMb a ha)).2]
      decide
    have hm3 : a.1.2.loc.firstMask ≠ some (nO + 1) := by
      rw [(membX_nine sentU.size _ (hMb a ha)).2, hnO, hsU]
      decide
    refine Bool.and_eq_true_iff.2 ⟨?_, Bool.and_eq_true_iff.2 ⟨layX_codes Q 9 10 _ _ lv.1 hL,
      (EK_iff Q sO nO 10 _).2 ⟨codX_onGu Q π he ha1 9 10 _ _ rs gs hd e1,
        omY_onGu sO.2.1 nO π he ha1 _ _ rs gs hd hm e2,
        (tidY_iff 10 _).2 (onGu_tidy π _ _ rs gs hd hl' ((tidY_iff 9 _).1 e3)),
        msgY_onGu _ 0 2 (by omega) π he ha1 _ _ rs gs hd hm0 e4,
        msgY_onGu _ (nO + 1) 5 (by omega) π he ha1 _ _ rs gs hd hm3 e5, hY10 a τ b ha hout⟩⟩⟩
    have e10 : (pmI decT₂ Pm₁ Q.par n nU nO).shape 10 = Pm₁.shape 10 := by
      show (if 2 ≤ 10 ∧ 10 ≤ 9 then shapeK Q.par nU nO n 10 else Pm₁.shape 10) = Pm₁.shape 10
      exact if_neg fun h => absurd h.2 (by decide)
    rw [e10]
    exact hP10 a τ b ha hout
  case hrows =>
    have smp : ∀ (ν : Msg2) (y : Mem), num ν = sentU.size ∨ num ν = sentU.size + 1 →
        Comp.msg ν ∉ laysAtS true 9 → apartAt N arr true 9 (.msg ν) = true → mem (num ν) = some y →
        SitsAt y (N.tenant ν).1 (N.tenant ν).2 → ∀ a τ b w, onQ₂ N (pmX cs G ms N (pmE decT₂ Pm₁ Q n
            nU nO sO) oNo Q sentU layU layO) Oc true f l 9 a →
        x.ior.red.out a τ = some b → Mg₀.row (.sample ν) b.1.2 w → Mg₀.row (.sample ν) a.1.2
          (e₀H cs G arr (smpSt cs oNo stSh) ms decT₂ c₀ N true Fr 9 ((actQ N f l 9).2 a) w) := by
      intro ν y hν hnl hap hy sy a τ b w ha hout h
      obtain ⟨rs, gs, hd, _⟩ := held_decides _ x hb a b τ hout
      have lt := x_numbers Q sentU layU layO 9 (.inl rfl) _ (hon a ha).1 hsU hsO (num ν) (.inr hν)
      have e := (onGu_leaves π he ha1 _ _ rs gs hd).2.1 (num ν) lt (by
        rw [(membX_nine sentU.size _ (hMb a ha)).2]
        intro e
        have e' : 1 = num ν := Option.some.inj e
        rcases hν with h | h <;> omega)
      refine (hsmp ν _ _).2 (smpSay_agree (num ν) a.1.2 (tidY_order 9 _ (hTd a ha)) _ _
        (fun part i => (rg_past_nine cs G arr ms decT₂ c₀ N oNo mem rd ν hnl hap (num ν) y hy sy _ w
          part i).symm)
        (smpSay_rides (num ν) a.1.2 b.1.2 _ (grows_nine π x hb a b τ hout) e ((hsmp ν _ _).1 h)))
    intro i hi a τ b w ha hout h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact smp .oOmega xO (.inl hn1) (by decide) hapO (by rw [hn1]; exact hmO) sitO a τ b w ha hout
        h
    · exact smp .oSp xS (.inr hn2) (by decide) hapS (by rw [hn2]; exact hmS) sitS a τ b w ha hout h
    · exact foldOmega_nine cs G arr ms decT₂ c₀ N (pmE decT₂ Pm₁ Q n nU nO sO) Oc oNo Q sentU layU
        layO f l mem rd π x hb he ha1
        (fun a ha => tidY_order 9 _ (hTd a ha)) xO xS hmO hmS sitO sitS hapO hapS a b τ w ha hout h

end nine

section ten
variable (π : P12) (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (hb : Alike (held (P := P₁) (Seat.onGomega (proximityTestKind guardedProximityTestParts π : Block T12 Unit))) x.b)
  (he : π.early = true) (ha1 : π.answers = 1) (hsU : sentU.size = 2)
  (hsO : (withOmega Q.S).size = 2)
  (hms : ∀ z ∈ ms, oNo z = 0 ∨ oNo z = sentU.size ∨ oNo z = sentU.size + 1)
  (t₁ t₂ c : ℕ) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rdN : ℕ → ℕ) (dB : RDT)
  (dt : List RDT) (e v₀ : ℕ) (εt : Err (uLT (ckP .two) dt))
  (ε : Err (uLT (ckP .two) x.ds)) (h0 : x.back = []) (hds : x.ds = dB :: dt)
  (herr : HEq ε ((e, εt) : Err (uLT (ckP .two) (dB :: dt))))
  (hA : AtPlaceOwn Fr π (VerifiableInference.Desc.numAt t₁ t₂ c) L mC mS mW rad x.base dB dt εt)
  (hPay : PayPub π rad dB.entry.rows v₀) (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0])
  (hlog : dB.entry.logN ≤ 64) (hle : v₀ * (bsRound .two dB.entry dB.kind).w ≤ e)
  (ho : π.nums.ownMask = true) (hP : ownLabelsB π = true)
  (n2 : ∀ n, n < π.nums.free → VerifiableInference.Desc.numAt t₁ t₂ c (.own n) < x.base)
  (n3 : ∀ c' n, (c' + 1, n) ∈ π.before →
    VerifiableInference.Desc.numAt t₁ t₂ c (.taken c' n) < x.base)
  (hft : π.nums.firstTree = Q.par.toGPar.firstTree)
  (hl : Q.codes.lengthsOk = true)
  (hdk : ∀ c (s s' : St), s'.loc.key = s.loc.key → decT₂ c s' = decT₂ c s)
  (hsmp : ∀ μ s w, Mg₀.row (.sample μ) s w ↔ SmpSay (num μ) s (rgOf cs arr mem rd w))
  (hn1 : num .oOmega = sentU.size) (hn2 : num .oSp = sentU.size + 1)
  (xO xS : Mem) (hmO : mem sentU.size = some xO)
  (hmS : mem (sentU.size + 1) = some xS) (mO : xO ∈ ms) (mS' : xS ∈ ms)
  (sitO : SitsAt xO (N.tenant .oOmega).1 (N.tenant .oOmega).2)
  (sitS : SitsAt xS (N.tenant .oSp).1 (N.tenant .oSp).2)

include hb he ha1 hsU hsO hms h0 hds herr hA hPay h1 hlog hle ho hP n2 n3 hft hl hdk hsmp hn1 hn2
    hmO hmS
  mO mS' sitO sitS

/-- **THE LEDGER's CLAUSE AT BLOCK 10, AT OUR FILLING**: h10 of share_seamed, by
ten_paid BY NAME. -/
theorem ten_at_K
    (core : TupleTen cs G ms N (pmE decT₂ Pm₁ Q n nU nO sO) Oc oNo Q sentU layU layO f l mem rd π t₁
        t₂ c rad rdN x)
    (hN : ((mineS N ms true 10).map (VerifiableInference.Desc.Sound.numOf arr)).Nodup)
    (hapO : apartAt N arr true 10 (.msg .oOmega) = true)
    (sb : SentBefore N f l 10 x .oOmega)
    (hP11 : ∀ a τ b, onQ₂ N (pmX cs G ms N (pmE decT₂ Pm₁ Q n nU nO sO) oNo Q sentU layU layO) Oc
        true f l 10 a → x.ior.red.out a τ = some b →
      Pm₁.shape 11 b.1.2 = true)
    (hY11 : ∀ a τ b, onQ₂ N (pmX cs G ms N (pmE decT₂ Pm₁ Q n nU nO sO) oNo Q sentU layU layO) Oc
        true f l 10 a → x.ior.red.out a τ = some b →
      sO.2.2.2 11 b.1.2 = true) :
    ClauseAt N (mgK cs G arr (smpSt cs oNo stSh) ms decT₂ Mg₀ mem rd e' n nO Q)
      (pmK cs G (smpSt cs oNo stSh) ms decT₂ (shiftBook N.lo) Pm₁ n nU nO Q (XK Q sentU layU layO sO
          nO)) Oc true
      f l (exK cs G arr (smpSt cs oNo stSh) ms decT₂ c₀ N Fr) 10 x ε := by
  rw [pmK_is]
  have hon := fun a ha => beside_of_on decT₂ Pm₁ Q n nU nO sO cs G ms N Oc oNo sentU layU layO f l
      10 a ha
  have hTd : ∀ a, onQ₂ N (pmX cs G ms N (pmE decT₂ Pm₁ Q n nU nO sO) oNo Q sentU layU layO) Oc true
      f l 10 a → tidY 10 a.1.2 = true := fun a ha =>
    ((EK_iff Q sO nO 10 _).1 (hon a ha).2.2.1).2.2.1
  have hMb : ∀ a, onQ₂ N (pmX cs G ms N (pmE decT₂ Pm₁ Q n nU nO sO) oNo Q sentU layU layO) Oc true
      f l 10 a → membX sentU.size 10 a.1.2 = true := fun a ha =>
    ((sharedX_parts Q sentU layU layO 10 _).1 (hon a ha).1).2.2.1
  refine ten_paid cs G arr ms decT₂ c₀ N (mgI cs arr Mg₀ mem rd Q.par (uRK Q.par) (omWK cs arr mem
      rd nO Q) e' n) (pmE decT₂ Pm₁ Q n nU nO sO) Oc oNo Q sentU layU layO f l π x hb he ha1 hsU
    hsO hms t₁ t₂ c L mC mS mW rad rdN dB dt e v₀ εt ε h0 hds herr hA hPay h1 hlog hle ho hP n2 n3
        hft
    (SayK cs mem rd Q.par n num) ?seam ⟨xS, mS', sitS⟩ hN hapO sb ?hrow ?hcong ?htab ?hshape
  case seam =>
    exact seam_ten cs G ms N (pmE decT₂ Pm₁ Q n nU nO sO) Oc oNo Q sentU layU layO f l mem rd Q.par
        n num π t₁ t₂ c rad rdN x
      hsU hsO core (fun a ha => ((tidY_iff 10 _).1 (hTd a ha)).kinds) hn1 hn2
  case hrow =>
    exact fun q _ a _ w h => say_row cs arr mem rd Mg₀ Q.par (uRK Q.par) (omWK cs arr mem rd nO Q)
        e' n
      num (fun μ s w => (hsmp μ s w).2) q a.1.2 w h
  case hcong =>
    exact fun q hq a ha m m' hs h => cong_ten_at cs mem rd ms N Q.par n num sentU.size a.1.2 (hTd a
        ha)
      (hMb a ha) hn1 hn2 xO xS hmO hmS mO mS' sitO sitS m m' hs q hq h
  case htab =>
    intro a τ b ha hout
    obtain ⟨rs, gs, hd, _⟩ := held_decides _ x hb a b τ hout
    have lv := onGomega_leaves π he ha1 _ _ rs gs hd
    exact tab_rides decT₂ N f l hdk 10 x a b τ hout (by rw [lv.2.2.2.1])
      (ha.1 .tablePromise (by decide))
  case hshape =>
    intro a τ b ha hout
    obtain ⟨rs, gs, hd, _⟩ := held_decides _ x hb a b τ hout
    have lv := onGomega_leaves π he ha1 _ _ rs gs hd
    obtain ⟨_, hL, hE, _⟩ := hon a ha
    obtain ⟨e1, e2, e3, e4, e5, _⟩ := (EK_iff Q sO nO 10 _).1 hE
    have hl' : a.1.2.st.codes.lengthsOk = true := by
      rw [(codX_iff Q 10 _).1 e1]
      exact hl
    refine Bool.and_eq_true_iff.2 ⟨?_, Bool.and_eq_true_iff.2 ⟨layX_codes Q 10 11 _ _ lv.1 hL,
      (EK_iff Q sO nO 11 _).2 ⟨codX_onGomega Q π he ha1 10 11 _ _ rs gs hd e1,
        omY_onGomega sO.2.1 nO π he ha1 _ _ rs gs hd e2,
        (tidY_iff 11 _).2 (onGomega_tidy π _ _ rs gs hd hl' ((tidY_iff 10 _).1 e3)),
        msgY_onGomega _ 0 2 (by omega) π he ha1 _ _ rs gs hd e4,
        msgY_onGomega _ (nO + 1) 5 (by omega) π he ha1 _ _ rs gs hd e5, hY11 a τ b ha hout⟩⟩⟩
    have e11 : (pmI decT₂ Pm₁ Q.par n nU nO).shape 11 = Pm₁.shape 11 := by
      show (if 2 ≤ 11 ∧ 11 ≤ 9 then shapeK Q.par nU nO n 11 else Pm₁.shape 11) = Pm₁.shape 11
      exact if_neg fun h => absurd h.2 (by decide)
    rw [e11]
    exact hP11 a τ b ha hout

end ten

end Desc.K14.Law

#print axioms Desc.K14.Law.XK_first
#print axioms Desc.K14.Law.XK_front
#print axioms Desc.K14.Law.XK_point
#print axioms Desc.K14.Law.handsAt_XK
#print axioms Desc.K14.Law.ten_at_K
#print axioms Desc.K14.Law.nine_at_K
#print axioms Desc.K14.Law.pmK_is
#print axioms Desc.K14.Law.beside_of_on
