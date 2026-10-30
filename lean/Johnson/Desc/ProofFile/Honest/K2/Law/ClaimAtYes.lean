-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ClaimAtYes.lean: the kind "the code switch" (K2): THE FIELD
claim OF `MadeAsks` (ExchangeAtMade.lean of this folder), IN ITS OWN TEXT, AT THE KIND's OWN YES, AT
EACH OF THE 25 WRITTEN SWITCHES, IN ALL THREE DRESSES: FROM THE THREAD's INVARIANT WITH `Said`,
THREE PREMISES ON LETTERS (hOk, hst, hty), ANY STRINGS y₀, AND ONE PREMISE ON ENTRIES AND CHALLENGES
(`LockAsks`, ClaimOfLock.lean of this folder). A JOIN: calls alone. No definition; statements with
their proofs.

  `frontAt_stands`  the front that a switch is handed hangs, of the place's numbers, on the word
                    "stands" alone
  `rch_at_head`     from the thread's invariant with `Said`: the library's `AtMg.rch`: "reached"
                    (`reach_at_head`, MadeAtHead.lean of this folder) and: the instance's public
                    part is a typed instance's (hty: a premise)
  `sizes_front_at_yes`   at a yes at a reached state: the sizes read off the statement behind the
                    joins are those read off the front's
  `claim_core`      `claim_at_head` (ClaimOfLock.lean) at a letter m with p.link = m + 1
  `claim_at_link`   at a link's first place (23 switches)
  `claim_at_yes`    THE END: at whatever dress and steps `SwitchArm` (BlockAtHead.lean of this
                    folder) ties to the place

HOW THE SEAM BETWEEN THE TWO FRONTS CLOSES. The carry's sentence names the front that `frontAt`
takes at `ProofFile.pAtK2 Zp m` off what `doorZ` hands on; the field names `AtYes`' front, at `IM.k2P …`,
off the state behind the place's step in front. Under "reached", at a link's first place: `doorZ`
hands on the reached state itself and `ProofFile.pAtK2 Zp m` stands as a link's (`link_door`); the arm's
dress is "link" and its step in front does nothing (`SwitchArm`); `frontAt` reads "stands" alone. At
the head's link's second place the like by `head_door`. Behind the links `doorZ` hands on what the
quiet step in front returns at the reached state (`fin_door`): that is the arm's own step in front,
so the state at which the yes stands.

By: `claim_at_head` (ClaimOfLock.lean) · `link_lockedAt`, `head_lockedAt`, `fin_lockedAt`
(LockAtFront.lean) · `front_test_at_reach`, `sizes_of_tables` (SizesAtYes.lean) · `placeLinksW`
(AtYesMore.lean) · `segments_at_head`, `places_at_head` (PlacesWritten.lean), of this folder ·
`link_door`, `head_door`, `fin_door` (Johnson/Desc/K2/Honest/Returns/DoorReached.lean) ·
`AlikeKept.sizes` (Returns/AlikeKept.lean) · `pin_facts` (Johnson/Top/H0/K2Hands/FrontFacts.lean).

Limits. AN IMPLICATION: hA, `LockAsks`, IS AS A WHOLE PAID NOWHERE: see ClaimOfLock.lean. hOk, hst
AND hty ARE PREMISES. hty IS A PREMISE ON THE INPUT: its instance's public part is a typed
instance's: THE BINDERS OF `SwitchLeft.made` DO NOT HOLD IT: whoever joins this law there must have
it of every valid input. y₀: strings of the library's type, any: no term of that type is laid here.
The thread's invariant, the yes and the closing's return are premises. One run's coins: never quoted
for a law. NOT IN FRONT OF A LAW OVER COINS. The full size; the format's second
hash function. The line that takes the instance `Inst.Model.Scl.ref` out of reach is LockAtFront.lean's own,
and the library's. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ClaimOfLock
import Johnson.Desc.ProofFile.Honest.K2.Law.MadeAtHead
import Johnson.Desc.K2.Honest.Returns.DoorReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K2.Law
open OnBytes
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Block Strs)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 AtYes frontAt)
open VerifiableInference.Desc.First.K2Hands (Pinned frontB2 pin_facts)
open VerifiableInference.Desc.First.K2Caller (doorZ)
open VerifiableInference.Desc.K2.Honest (Left ClaimTrue sizesAt carryExact)
open VerifiableInference.Desc.K2.Honest.Returns (AlikeKept link_door head_door fin_door)
open VerifiableInference.Desc.Sound (MsgT below allOf EAll wordsFirst)
open Johnson.Desc.First.Walk.Tied (Reach)
open Johnson.G (fxAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread (Script lettersHead WtF)
open IM (k2P)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- The front hangs, of the place's numbers, on the word "stands" alone. -/
theorem frontAt_stands {p q : P2} (e : p.stands = q.stands) (s : S) :
    frontAt p s = frontAt q s := by
  unfold frontAt
  rw [e]

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (Kp : VerifiableInference.Desc.Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- hOk, hst AND hty ARE PREMISES. **FROM THE THREAD TO THE LIBRARY's `AtMg.rch`**, at any strings
y. -/
theorem rch_at_head (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m)
    (hst : ∀ v i x u, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.stored v i x =
      some u → ∀ a ∈ u, a < fieldPrimeWord)
    {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hb : b ≤ cF.blocksInOrder.length)
    (hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b k s m E)
    (hty : ∃ z : LPFD.Full.XF × OnBytes.Flat.RecFull, m.st.input.x.pub = (LPFD.Full.instanceAsPlainRecord z).pub)
    (y : (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str) :
    h.toAtMg.rch b ((m.st.input.x.pub, s), y) :=
  ⟨reach_at_head h H Q test item n₁ n₂ b₀ Vd Rd Kp w carryX hOk hst hb hT, hty⟩

include h in
/-- **At a yes at a reached state: the sizes behind the joins are the front's.** -/
theorem sizes_front_at_yes
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) {n : P1K2.Nums} {st : First.K2.At}
    {before : TS → Except String TS} {after : TS → TS → Except String TS}
    (hA : SwitchArm Zp Bs.G₀ p st before after) {z₀ : ProofFile.InstPub} {s s₁ t : TS}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (switchNo p) (z₀, s))
    (hb : before s = .ok s₁) (nm : String) {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {x : _root_.Tw.K2.Front} {z : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {cd : Code}
    (A : AtYes (k2P Zp p.place nm st n) s₁ t r₁ r₂ gs x z S3 Y rows G cd) :
    sizesAt S3 x.f.rows x.T = sizesAt x.st x.f.rows x.T := by
  obtain ⟨v, W, -, -, ht⟩ := front_test_at_reach h O hp hA hr hb nm A.front
  simp only [frontB2, Bool.and_eq_true] at ht
  have Pn : Pinned (fxAt v) x := pin_facts ht.1.1
  have K : AlikeKept x.f.rows x.st z.st :=
    ⟨A.sent.codes, fun o ho => A.sent.old o (Pn.below o ho)⟩
  rw [sizes_of_tables A.same, K.sizes]

/-- `claim_at_head` at a letter m with p.link = m + 1. All but hp and el are premises. -/
theorem claim_core {p : SwitchPlace} (hp : p ∈ placesW) {k : Coins Bk} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {Ev : Env}
    (hT : Thr (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
      w).thread (switchNo p) k s m Ev)
    {l : Nat} (el : p.link = l + 1) {t : TS} {x : _root_.Tw.K2.Front}
    (hd : doorZ Zp l s = some t) (hf : frontAt (ProofFile.pAtK2 Zp l) t = some x) (ds : List Fmt.Drawn)
    {lay : OnBytes.Params.ReqLayout} {D : RowData} {Rr : Readers} {heard : List Fmt.Drawn}
    {kk : Nat → Except String Stretch} {Wl : Left}
    (hW : lotClosingAt lay segsW p D Rr heard kk = .ok Wl)
    (hLk : ∀ y, closingFrom freshTable (lotOwn segsW p D Rr heard) heard kk (segsW.take (l + 1)) 0 0
      none = .ok y → LockedAt freshTable (lotOwn segsW p D Rr heard) heard kk l y x)
    (hA : LockAsks freshTable (lotOwn segsW p D Rr heard) heard kk (p.link - 1) x
      (wordsFirst (P5J.At.arr Zp) x.st t.book (Q.wit k m.st.input (m.st.heard ++ ds))))
    {S3 : Statement} (hsz : sizesAt S3 x.f.rows x.T = sizesAt x.st x.f.rows x.T) :
    ClaimTrue (sizesAt S3 x.f.rows x.T) x.f.rows Wl := by
  obtain rfl : l = p.link - 1 := by omega
  exact claim_at_head h H Q test item n₁ n₂ b₀ Vd Rd Kp w hp hT hd hf ds hW el hLk hA hsz

/-- hOk, hst, hty, hT, A, hW AND hA ARE PREMISES. **THE FIELD claim, IN ITS OWN TEXT, AT THE KIND's
OWN YES, AT A LINK's FIRST PLACE.** One run's coins: never quoted for a law.
NOT IN FRONT OF A LAW OVER COINS. -/
theorem claim_at_link
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m)
    (hst : ∀ v i x u, (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
      w).thread.stored v i x = some u → ∀ a ∈ u, a < fieldPrimeWord)
    {p : SwitchPlace} (hp : p ∈ placesW) {n : P1K2.Nums} {before : TS → Except String TS}
    {after : TS → TS → Except String TS} (hArm : SwitchArm Zp Bs.G₀ p .link before after)
    (h1 : 1 ≤ p.link) (h24 : p.link < 24) (hno : switchNo p = 14 * p.link + 2)
    (hbe : before = fun s => .ok s) (hlen : switchNo p ≤ cF.blocksInOrder.length)
    {k : Coins Bk} {s s₁ t : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {Ev : Env}
    (hT : ThrS (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
      w).thread Said (switchNo p) k s m Ev)
    (hty : ∃ z : LPFD.Full.XF × OnBytes.Flat.RecFull, m.st.input.x.pub = (LPFD.Full.instanceAsPlainRecord z).pub)
    (y₀ : (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hb : before s = .ok s₁) (nm : String) {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {x : _root_.Tw.K2.Front} {z : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {cd : Code}
    (A : AtYes (k2P Zp p.place nm .link n) s₁ t r₁ r₂ gs x z S3 Y rows G cd)
    (ds : List Fmt.Drawn) {lay : OnBytes.Params.ReqLayout} {D : RowData} {Rr : Readers}
    {heard : List Fmt.Drawn} {kk : Nat → Except String Stretch} {Wl : Left}
    (hW : lotClosingAt lay (segmentsOf Zp Bs.G₀) p D Rr heard kk = .ok Wl)
    (hA : LockAsks freshTable (lotOwn segsW p D Rr heard) heard kk (p.link - 1) x
      (wordsFirst (P5J.At.arr Zp) x.st s.book (Q.wit k m.st.input (m.st.heard ++ ds)))) :
    ClaimTrue (sizesAt S3 x.f.rows x.T) x.f.rows Wl := by
  have hpS : p ∈ switchPlaces Zp Bs.G₀ := by
    rw [places_at_head h.toAtMg O]
    exact hp
  obtain rfl : s = s₁ := by
    rw [hbe] at hb
    exact Except.ok.inj hb
  have h23 : p.link - 1 < 23 := by omega
  have el : p.link = (p.link - 1) + 1 := by omega
  have eno : switchNo p = 14 * ((p.link - 1) + 1) + 2 := by
    rw [hno, ← el]
  have hR := rch_at_head h H Q test item n₁ n₂ b₀ Vd Rd Kp w (carryExact Zp (P5J.At.arr Zp)) hOk hst
    hlen hT hty y₀
  have hR' : h.toAtMg.rch (14 * ((p.link - 1) + 1) + 2) ((m.st.input.x.pub, s), y₀) := by
    rw [← eno]
    exact hR
  obtain ⟨hstd, hdoor⟩ := link_door h h23 _ hR'
  have hf : frontAt (ProofFile.pAtK2 Zp (p.link - 1)) s = some x :=
    (frontAt_stands (q := k2P Zp p.place nm .link n) hstd s).trans A.front
  rw [segments_at_head h.toAtMg O] at hW
  exact claim_at_head h H Q test item n₁ n₂ b₀ Vd Rd Kp w hp hT.1 hdoor hf ds hW el
    (fun y hy => link_lockedAt h h23 _ hR' hstd hf hy) hA
    (sizes_front_at_yes h O hpS hArm hR.1 hb nm A)

/-- hOk, hst, hty, hT, A, hW AND hA ARE PREMISES. **THE FIELD claim, IN ITS OWN TEXT, AT THE KIND's
OWN YES, AT EVERY WRITTEN SWITCH, IN WHATEVER DRESS `SwitchArm` TIES TO IT.** One run's coins: never
quoted for a law. NOT IN FRONT OF A LAW OVER COINS. -/
theorem claim_at_yes
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m)
    (hst : ∀ v i x u, (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
      w).thread.stored v i x = some u → ∀ a ∈ u, a < fieldPrimeWord)
    {p : SwitchPlace} (hp : p ∈ placesW) {n : P1K2.Nums} {st : First.K2.At}
    {before : TS → Except String TS} {after : TS → TS → Except String TS}
    (hArm : SwitchArm Zp Bs.G₀ p st before after) (hlen : switchNo p ≤ cF.blocksInOrder.length)
    {k : Coins Bk} {s s₁ t : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {Ev : Env}
    (hT : ThrS (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
      w).thread Said (switchNo p) k s m Ev)
    (hty : ∃ z : LPFD.Full.XF × OnBytes.Flat.RecFull, m.st.input.x.pub = (LPFD.Full.instanceAsPlainRecord z).pub)
    (y₀ : (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hb : before s = .ok s₁) (nm : String) {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {x : _root_.Tw.K2.Front} {z : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {cd : Code}
    (A : AtYes (k2P Zp p.place nm st n) s₁ t r₁ r₂ gs x z S3 Y rows G cd)
    (ds : List Fmt.Drawn) {lay : OnBytes.Params.ReqLayout} {D : RowData} {Rr : Readers}
    {heard : List Fmt.Drawn} {kk : Nat → Except String Stretch} {Wl : Left}
    (hW : lotClosingAt lay (segmentsOf Zp Bs.G₀) p D Rr heard kk = .ok Wl)
    (hA : LockAsks freshTable (lotOwn segsW p D Rr heard) heard kk (p.link - 1) x
      (wordsFirst (P5J.At.arr Zp) x.st s₁.book (Q.wit k m.st.input (m.st.heard ++ ds)))) :
    ClaimTrue (sizesAt S3 x.f.rows x.T) x.f.rows Wl := by
  have hpS : p ∈ switchPlaces Zp Bs.G₀ := by
    rw [places_at_head h.toAtMg O]
    exact hp
  have hlk : p.link = p.place.link.getD 25 := beq_iff_eq.1 (List.all_eq_true.1 placeLinksW.1 p hp)
  have hR := rch_at_head h H Q test item n₁ n₂ b₀ Vd Rd Kp w (carryExact Zp (P5J.At.arr Zp)) hOk hst
    hlen hT hty y₀
  have hsz := sizes_front_at_yes h O hpS hArm hR.1 hb nm A
  have hArm' := hArm
  rcases hArm' with ⟨rfl, -, h1, h24, ei, rfl, -⟩ | ⟨rfl, ep, ei, rfl, -⟩ | ⟨rfl, ep, ei, rfl, -⟩
  · have e : s = s₁ := Except.ok.inj hb
    rw [← e] at hA
    exact claim_at_link h H Q test item n₁ n₂ b₀ Vd Rd Kp w O hOk hst hp hArm h1 h24 ei rfl hlen hT
      hty y₀ hb nm A ds hW hA
  · obtain rfl : s = s₁ := Except.ok.inj hb
    have e24 : p.link = 23 + 1 := by
      rw [hlk, ep]
      rfl
    have hR' : h.toAtMg.rch 339 ((m.st.input.x.pub, s), y₀) := by
      rw [← ei]
      exact hR
    obtain ⟨hstd, hdoor⟩ := head_door h _ hR'
    have hf : frontAt (ProofFile.pAtK2 Zp 23) s = some x :=
      (frontAt_stands (q := k2P Zp p.place nm .head n) hstd s).trans A.front
    rw [segments_at_head h.toAtMg O] at hW
    exact claim_core h H Q test item n₁ n₂ b₀ Vd Rd Kp w hp hT.1 e24 hdoor hf ds hW
      (fun y hy => head_lockedAt h _ hR' hstd hf hy) hA hsz
  · have e25 : p.link = 24 + 1 := by
      rw [hlk, ep]
      rfl
    have hR' : h.toAtMg.rch 353 ((m.st.input.x.pub, s), y₀) := by
      rw [← ei]
      exact hR
    obtain ⟨hstd, hdoor⟩ := fin_door h _ hR' hb
    have hf : frontAt (ProofFile.pAtK2 Zp 24) s₁ = some x :=
      (frontAt_stands (q := k2P Zp p.place nm .finish n) hstd s₁).trans A.front
    rw [segments_at_head h.toAtMg O] at hW
    exact claim_core h H Q test item n₁ n₂ b₀ Vd Rd Kp w hp hT.1 e25 hdoor hf ds hW
      (fun y hy => fin_lockedAt h _ hR' hb hstd hf hy) hA hsz

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.frontAt_stands
#print axioms ProofFile.Honest.K2.Law.rch_at_head
#print axioms ProofFile.Honest.K2.Law.sizes_front_at_yes
#print axioms ProofFile.Honest.K2.Law.claim_core
#print axioms ProofFile.Honest.K2.Law.claim_at_link
#print axioms ProofFile.Honest.K2.Law.claim_at_yes
