-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ElevenHead.lean: CONDITIONAL.

What is here. The first eleven hypotheses of the library's `eleven_at_all`
(Johnson/Road/K4/More/ElevenAtAll.lean), as `k4_behind_head` (Law/BehindHead.lean) asks them, and
`k4_accepted_head` (Law/ReadyHead.lean) four of them, at the data of `lettersHead`
(Honest/Thread/FirstHead.lean: a thread of the first chain, at the public files' own data, any
prover and a run's input): all eleven from h : AtMgA and `LaidK4` (Law/SeatedHead.lean). And so two
of the hypotheses that the thread's rule asks at the member of the feed-forward layers' own rounds
(sub-protocol K4): `Behind` and `AcceptedS`. The others there (`Plays`, `Exchange`, `RidesPast`, the
shares) are not here. One definition, and statements with their proofs: calls of the library's
statements, after the proof text of its `k4Row_wide_scope` (Johnson/Road/K4/K4RowWideScope.lean).

  `eAll_is`   the library's two terms for the struck parts' data are one. A check: no statement of
      this file calls it.
  `laidK4_one`   `LaidK4` fixes the group, the parameters and the member.
  `atK4_of_laid`   `AtK4` out of `LaidK4`.
  `K4Nine`, `nine_head`   **nine of the eleven**, as one structure, at k, m, `parOf x`; with "a
      member stands behind member k". (The library's structure `K4Here` on the member:
      `k4Here_head`, Law/SeatedHead.lean.)
  `named_head`   **`K4NamedW`**: the one test on public data that the library's statement leaves is
      had under h (`k4Row_of_head`, Johnson/Road/K4/K4RowOfHead.lean).
  `k4_behind_all`   **`Behind` at the member**, from h, AtK4, b₀ ≠ k + 1, hKp and hRd.
  `k4SeatedA_head`   `K4SeatedA` (Law/SeatedA.lean) at the thread, from `LaidK4`, hQ and half.
  `k4_accepted_all`   **`AcceptedS` at the member**, from h, `LaidK4` and what is named below.

Words. The member: one sub-protocol of the chain's flat list. A border: the place between two
members; border k stands in front of member k. The thread: `Thread` (Honest/Thread/Thr.lean): what
is said of an honest run at a border. The promise in front: the library's condition on the
verifier's state at a border (`onAt`, Johnson/Desc/First/Borders.lean). The fence: `K4Fence`, six
facts on that state which the promise does not hold. The riders: the thread's parameter `rides`:
sentences that are carried from border to border. The fall: a test on the sampled challenges; where
it says something, `AcceptedS` asks nothing. The struck parts' data: the second argument of the
library's wider meaning (`WideData`, Johnson/Desc/Sound/MgWide.lean).

Not shown here. THAT THE TOPS' HYPOTHESES CAN HOLD TOGETHER: this file gives no example (by binder,
beside h: `k4_behind_all`: A, hb₀, hKp, hRd · `k4SeatedA_head`: Lh, hQ, half · `k4_accepted_all`:
Lh, hQ, half, hPl, hSh, hn, h2, hLook, hTok, hf). `nine_head` and `named_head` take h and `LaidK4`
alone: `LaidK4` asks nothing beyond h (`laid_head`, Law/SeatedHead.lean, at the library's
`atK4_full`), and of h alone: the side library AtFullSide proves, with no hypothesis, that h has a
member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). `Behind` and `AcceptedS` speak only where the thread stands: that
it stands at any run is not shown. NOT COMPLETENESS. FOR `Behind` STAY: `AtK4` (the library's
`atK4_full` has it at each of the twelve groups), AND THREE HYPOTHESES ON THE THREAD's OWN
PARAMETERS: b₀ ≠ k + 1; that `K4KeepsM` gives the place's clause Kp; that it lets the riders Rd
pass. FOR `AcceptedS` STAY, BY NAME: the structure Lh : LaidK4 on the member (h and AtK4 give one:
`laid_head`; it is one: `laidK4_one`; the hypotheses below speak of ITS x and g) · hQ (that
`k4PubOf` returns the public data at the member's parameters: Law/FrontCount.lean has it under h and
`LaidK4`) · half (the prover's list of halves holds K4's half at the member's place) · a proof of
`k4PlanB` and of `k4ShapeB` at the member's parameters (an evaluation gives no term) · two
comparisons of public numbers (hn · lt ≤ dT) (ALL OF THESE TESTS ON THE PLAN STAND UNDER h AND
`LaidK4`: Law/PublicOne.lean, Law/DearX.lean) · `K4LookLaid` (Law/ReadyHead.lean; IT STANDS UNDER h
AND `LaidK4` by Law/LookMemberHead.lean and Law/LookJoin.lean, the second by a statement of the
writers of Honest/K3/) · the test on the tokens that the verifier's state holds (`tokensFit`), IN
THE FIRST GROUP ALONE (in the eleven others it holds by unfolding; Law/TokensHead.lean has it under
h and `LaidK4`) · that where the fall says nothing the honest side's test on one sampled element
says nothing. THE MEMBER's STEP TESTS NO SENT VALUE (Law/Hears.lean): it accepts every play of the
right shape, a false one too. THE FULL SIZE ALONE, and at `OnBytes.secondHashFunction`, the format's second
hash function, alone. A LAW, NOT A PART: no file that defines a part of the proof file's description
may import this one: its imports reach Johnson/Goal/. Following import lines, and stopping unopened
at every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/ and at every module
whose name begins Cb.Bridge, its imports reach 70 modules under Johnson/Goal/, 7 under
Johnson/Bridge/ and 1 whose name begins Cb.Bridge, and none of the others; what lies behind these is
not counted; 46 of the modules that it reaches have RecCompile in their names, none of them
RecCompile's Honest*, Both or PassH*. An earlier walk, which opened every module that it reached,
counted 163 modules under Johnson/Goal/, 53 whose name holds RecCompile and 140 under ThirdParty/;
another, which stopped unopened at Johnson/Goal/, Johnson/D/ and ThirdParty/ alone, met 2 modules
under ThirdParty/. No statement or proof of a file under Johnson/Goal/ or ThirdParty/ was read for
this file, and none is called by name in it.

Kin. `K4Nine` gathers in one structure nine of the first eleven hypotheses of the library's
`eleven_at_all` (Johnson/Road/K4/More/ElevenAtAll.lean), which takes them one by one: all but `AtK4`
and `K4NamedW`. Other kinds' like laws at their own members, at the same thread:
`k5_owes_all_head_M` (Honest/K5/Law/HeadM.lean), `k13_accepted_at_head_filler`
(Honest/K13/AcceptedAtHeadFiller.lean).

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.HeadTops
import Johnson.Desc.ProofFile.Honest.K4.Law.SeatedHead
import Johnson.Road.K4.K4FillAll
import Johnson.Road.K4.K4NamedPaid
import Johnson.Road.K4.K4HeadWritten
import Johnson.Road.K4.K4RowTestLaws
import Johnson.Road.K4.K4RowOfHead
import Johnson.Road.K4.K04Tied
import Johnson.Road.K4.K4RowWideScope
import Johnson.Road.K4.Riders.SeatsAtDesc
import Johnson.P5J.ReadsTestsAtHead
import Johnson.P5J.RowsAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Desc.First.K4.Rt (k4Takes)
open OnBytes.Desc.First.K4.RtPub (tokensFit)
open OnBytes.Desc.First.K4.Riders (ObjRun GuestRun)
open OnBytes.Road.K4 (AtK4 K4OnX K4OnD K4NamedW parOf eAll k4Fill_all k4Row_two k4Row_of_head
  named_const written_of_head cut_of_head k4OnD_of_fill k04_sits_one atK4_full k4PlaceAt)
open OnBytes.Road.K4.Riders (seats_at_open)
open OnBytes.Road.K4.InT (StatesAt)
open OnBytes.Road.K4.More (PS)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Claim Link Block K9.statesOfLink)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.Sound (MsgT linksFull)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4 laid_head k4Here_head k4OnX_head k4Sits_head k4NoMark_head
  k4SitsBack_head member_head pub_of)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **The library's two terms for the struck parts' data are one.** A check: no statement of this
file calls it: `named_head` closes through the same unfolding. -/
theorem eAll_is (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl)
    (L : VerifiableInference.Desc.K12.Door.Laid) : eAll Zp cF L = P5J.At.E Zp cF L := rfl

/-- CONDITIONAL: on a and b. **`LaidK4` is one**: at one k the group, the parameters and the member
are fixed. -/
theorem laidK4_one {k m g g' : ℕ} {x x' : Bool × Par} {blk blk' : Block TS ProofFile.Cl}
    (a : LaidK4 Zp cF k m g x blk) (b : LaidK4 Zp cF k m g' x' blk') :
    g = g' ∧ x = x' ∧ blk = blk' := by
  have eg : g = g' := by
    have h1 := a.num
    have h2 := b.num
    omega
  subst eg
  obtain ⟨G₀, hG, hx⟩ := a.lot
  obtain ⟨G₁, hG', hx'⟩ := b.lot
  obtain rfl : G₀ = G₁ := Option.some.inj (hG.symm.trans hG')
  exact ⟨rfl, k04_sits_one hx hx' a.link b.link, Option.some.inj (a.member.symm.trans b.member)⟩

/-- **`AtK4` out of `LaidK4`**: the library's `atK4_full` at the group. -/
theorem atK4_of_laid {k m g : ℕ} {x : Bool × Par} {blk : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk) : AtK4 linksFull PS k m (k4PlaceAt g) := by
  have hm := Lh.seg
  have hk := Lh.num
  subst hm
  subst hk
  exact atK4_full g Lh.lt

/-- **Nine of the eleven hypotheses, as one structure**, at the data of a hypothesis h : AtMgA; with
"a member stands behind member k". A definition: `nine_head`'s conclusion. Nothing is claimed by the
definition. -/
structure K4Nine (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) (k m : ℕ) (par : Par) : Prop where
  hH : isLay h.𝔇.links (headLink (P5J.At.X Zp)) = false
  Sx : K4OnX (P5J.At.X Zp) Z.pol Z.KL (some Z.lay) m par
  Sd : K4OnD h.𝔇 m par (Forest.elems (P5J.At.X Zp).y.fo)
  runs : ∃ (l : Link S Claim) (runO runG : ℕ → S → Except String (List Claim × S)),
    h.𝔇.lk m = some l ∧
    (∀ u, StatesAt (K9.statesOfLink l) 2 par "front" u ∧
      StatesAt (K9.statesOfLink l) 2 par "back" u) ∧
    (K9.statesOfLink l 1).find? (fun r => r.1 == "objects") = some ("objects", runO) ∧
    ObjRun runO ∧
    (K9.statesOfLink l 1).find? (fun r => r.1 == "guests") = some ("guests", runG) ∧
    GuestRun runG
  border : k + 1 < cF.blocksInOrder.length

/-- **NINE OF THE ELEVEN, UNDER h AND `LaidK4` ALONE.** (The tenth, `AtK4`: `atK4_of_laid` has it
out of `LaidK4`; of the tops `k4_behind_all` asks it; the library's `atK4_full` has it at each of
the twelve groups.) -/
theorem nine_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) : K4Nine h k m (parOf x) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨G₀, hG, -, Hh⟩ := k4Here_head h Lh
  obtain rfl : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans hG)
  have Fl := k4Fill_all h VerifiableInference.Desc.K13.Law.LFull
  obtain ⟨Lk, x', e1, e3, e5, st, runO, runG, fO, oRun, fG, gRun⟩ :=
    seats_at_open h.scope h.reads O Lh.lt
  obtain rfl : x = x' := k04_sits_one Hh.mem e3 Lh.link e5
  have hH : isLay h.𝔇.links (headLink (P5J.At.X Zp)) = false := by
    rw [Fl.links, P5J.headLink_in_scope h.scope h.reads h.pubOne]
    decide +kernel
  have hlk : h.𝔇.lk (2 * g) = some Lk := by
    rw [Fl.lk]
    exact e1
  have Sd := k4OnD_of_fill h.𝔇 h.scope h.reads O O.W Lh.lt Hh.mem Lh.link Fl
  have hm := Lh.seg
  have hk := Lh.num
  subst hm
  subst hk
  exact ⟨hH, k4OnX_head h Lh, Sd, ⟨Lk, runO, runG, hlk, st, fO, oRun, fG, gRun⟩, Hh.more⟩

/-- **THE ELEVENTH (nine tests with code), UNDER h AND `LaidK4` ALONE**: the one test on public data
that the library's statement leaves is had under h (`k4Row_of_head`,
Johnson/Road/K4/K4RowOfHead.lean). -/
theorem named_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) :
    K4NamedW h.𝔇 (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) k m (parOf x)
      (cF.blocksInOrder.map fun b => b.oracles.flatMap id) (Forest.elems (P5J.At.X Zp).y.fo) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨G₀, hG, -, Hh⟩ := k4Here_head h Lh
  obtain rfl : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans hG)
  have Sn := named_const h (P5J.laid_at_head h.toAtMg) (written_of_head h.toAtMg)
    (cut_of_head h.toAtMg) (k4Row_two h (k4Row_of_head h)) O g Lh.lt x blk Hh
  have hm := Lh.seg
  have hk := Lh.num
  subst hm
  subst hk
  exact Sn

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **`Behind` AT THE MEMBER**: under h, `AtK4` and three hypotheses on the thread's own
parameters. CONDITIONAL. -/
theorem k4_behind_all {k m : ℕ} {pl : Place} (A : AtK4 linksFull PS k m pl) (hb₀ : b₀ ≠ k + 1)
    (hKp : ∀ s s', K4KeepsM s s' → Kp pl s s')
    (hRd : ∀ v s s', Rd k v s → K4KeepsM s s' → Rd (k + 1) v s') :
    Behind (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k := by
  obtain ⟨g, x, blk, Lh⟩ := laid_head h A
  obtain ⟨hH, Sx, Sd, ⟨l, runO, runG, hlk, st, fO, oRun, fG, gRun⟩, hbd⟩ := nine_head h Lh
  exact k4_behind_top h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hH A Sx Sd
    (named_head h Lh) hlk st fO oRun fG gRun
    (k4Sits_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lh)
    (k4NoMark_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lh) (by omega) hb₀ hKp hRd

/-- **`K4SeatedA` AT THE THREAD** (Law/SeatedA.lean: what the statements on the accepting step read
of the seat), from `LaidK4`, that `k4PubOf` returns the public data, and the prover's half. -/
theorem k4SeatedA_head {k m g : ℕ} {x : Bool × Par} {blk : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk) {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp)
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights tokens look Qp)) :
    K4SeatedA (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k cells weights tokens
      look Qp (parOf x) blk := by
  refine ⟨member_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lh, laid_rounds Lh.laid,
    (pub_of Lh hQ).1, ?_⟩
  rw [IM.alone_place Lh.laid]
  exact half

/-- **`AcceptedS` AT THE MEMBER**: under h, `LaidK4`, and what is named in the head.
CONDITIONAL. -/
theorem k4_accepted_all (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop)
    {k m g : ℕ} {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    {cells : Tr → Cells}
    {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    {fall : Nat → S → List Fmt.Drawn → Option String} (hQ : k4PubOf Zp x.2 = some Qp)
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights tokens look Qp))
    (hPl : k4PlanB (parOf x) = true) (hSh : k4ShapeB (parOf x) = true)
    (hn : Forest.elems (P5J.At.X Zp).y.fo + k4Takes (parOf x).P (parOf x).hp (parOf x).g ≤
      (parOf x).hp.ns)
    (h2 : (parOf x).P.y.h.lt ≤ (parOf x).P.y.fo.dT)
    (hLook : ∀ j q, k = j + 1 → PS[j]? = some q → q.link = some m → q.piece = 2 →
      K4LookLaid cF.blocksInOrder (ProofFile.startS Zp) j (parOf x))
    (hTok : g = 0 → ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said k c s mm E →
      tokensFit { (parOf x).P with tokv := seatS.tokv s } (parOf x).g = true)
    (hf : ∀ s ds, fall k s ds = none → k4CoinZero Qp ds = none) :
    AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall k := by
  obtain ⟨hH, Sx, Sd, -, hbd⟩ := nine_head h Lh
  have hTok' : ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said k c s mm E →
      tokensFit { (parOf x).P with tokv := seatS.tokv s } (parOf x).g = true := by
    intro c s mm E hT
    by_cases hg : g = 0
    · exact hTok hg c s mm E hT
    · unfold tokensFit
      rw [Bool.or_eq_true]
      refine Or.inl (bne_iff_ne.mpr ?_)
      show x.2.g ≠ 0
      rw [Lh.grp]
      exact hg
  exact k4_accepted_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) Said
    (k4SeatedA_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lh hQ half)
    (k4SitsBack_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lh) hPl hSh hH (atK4_of_laid Lh) Sx
    Sd (k' := 0) hn h2 (by omega) hLook hTok' hf

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.eAll_is
#print axioms ProofFile.Honest.K4.laidK4_one
#print axioms ProofFile.Honest.K4.atK4_of_laid
#print axioms ProofFile.Honest.K4.K4Nine
#print axioms ProofFile.Honest.K4.nine_head
#print axioms ProofFile.Honest.K4.named_head
#print axioms ProofFile.Honest.K4.k4_behind_all
#print axioms ProofFile.Honest.K4.k4SeatedA_head
#print axioms ProofFile.Honest.K4.k4_accepted_all
