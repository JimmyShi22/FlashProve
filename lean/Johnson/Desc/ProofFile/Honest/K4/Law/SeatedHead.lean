-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/SeatedHead.lean: CONDITIONAL.

What is here: at a thread of the first chain, at the public files' own data, any prover and a run's
input (`lettersHead`, Honest/Thread/FirstHead.lean), at a member number k that stands at K4's place
of a layers' segment m in the written lists (`AtK4`, Johnson/Road/K4/K4AtTable.lean): the member is
K4's lot's own sub-protocol, seated alone. With it the hypotheses `K4Sits` (Law/Sits.lean),
`K4NoMark` (Law/KeepsStep.lean) and `K4SitsBack` (Law/Accepted.lean) hold there, and `K4OnX`
(Johnson/Road/K4/K4OnX.lean) at the member's parameters. `K4Seated`'s three open fields are asked
once as the fields stand (`k4Seated_head`) and once in the thread's own values (`k4Seated_letters`).
Definitions, and statements with their proofs.

How. h holds all three hypotheses of the library's `IM.k4_of` (Johnson/IMR/K4Seat.lean): the scope,
that the files are read, and the opening of the description's maker AT THE CHAIN cF ITSELF
(`LaidAt.opened`, Johnson/P5J/LaidOpens.lean). `IM.flatIx_scope` and `IM.hear_at_flat`
(Johnson/IMR/) give the member's number in the flat list: 28 g + 4. That a number at which `AtK4`
holds is one of these twelve is a test on the two written lists, BY LEAN's KERNEL.

  1  `k4NumsFitAt`, `k4NumsFit`, `k4_nums_full`, `k4_nums_off`, `k4_nums_stride`, `k4_nums_bound`,
     `atK4_only`   the test; by the kernel: true; three negative tests, by the kernel: at another
     offset, at another stride, and at the bound 11, where the last of the twelve places alone says
     no, the test is false; so `AtK4` at (k, m) gives a group g below 12 with k = 28 g + 4, m = 2 g
  2  `LaidK4 Zp cF k m g x blk`, `laid_head`   free of the thread: the member, the equation on it,
     and what the library says of its parameters x; **h and `AtK4` give it**
  3  `member_head`, `hb_head`   at the thread: the hypothesis hb of Law/SitsAt.lean, to the letter
  4  `k4Sits_head`, `k4NoMark_head`, `k4SitsBack_head`, `k4OnX_head`   each one call;
     `k4Here_head`   the library's `K4Here` at the member
  5  `pub_of`, `k4Seated_head`, `k4Seated_letters`   what `k4PubOf`'s return has of x; **`K4Seated`
     at the thread**; the same with half, front and fits at the prover's own list of halves, the
     chain's flat list and the run's input

Words. K4: the sub-protocol of the feed-forward layers' own rounds. The thread: `Thread`
(Honest/Thread/Thr.lean): a chain's list of sub-protocols (its members) with the honest side's
halves and what is said of a run between two members. K4's lot: `ProofFile.k4Lot`
(Johnson/Desc/ProofFile/Lot/K4.lean): the list of K4's sub-protocols, one for each layers' segment,
that the description's maker lays; `ProofFile.k4Block x` is its sub-protocol at the parameters x. Seated
alone: `IM.LaidAlone` (Johnson/IMR/SeatForm.lean): the member is that sub-protocol under the maker's
wrappers (a name, a place, a guard on the mark, a guard on the reply) and nothing else. The ground:
`ProofFile.Ground`, what the maker computes of the public part in front of the lots.

Not shown here. THAT THE HYPOTHESIS h : AtMgA CAN HOLD: The side library AtFullSide proves, with no
hypothesis, that h has a member at Z := VerifierAndGoals.storedPublicFiles, D := dpZ storedPublicFiles, r := theProofRun (asDescriptionFiles
storedPublicFiles) (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say
what it is worth). VerifierAndGoals.storedPublicFiles is three terms written in Ladder/Stored.lean, meant to be the
full-size example's three public files, tied to those files by no theorem; the example's weights are
synthetic. One example alone; of AtMgA, not of AtMgR. The closed facts beneath it are proved by
evaluation in Lean's kernel, which no independent checker has replayed. It is not called here, and
nothing in the library proper imports it. Of h together with hQ, half, front and fits this file
gives no example; A (`AtK4`) holds at each of the twelve groups (the library's `atK4_full`), and h
and A give Lh (`laid_head`). No field of `LaidK4` reads x.1, the lot's Bool at the place: where it
is false the sub-protocol's test on the plan is false; that it is true is not shown here. OF THE
NINE FIELDS OF `K4Seated` (Law/Seated.lean) THREE COME WITH THE MEMBER (member, rounds, oracles),
THREE MORE WHERE `k4PubOf` (Honest/K4/Part.lean) RETURNS THE PUBLIC DATA (place, own, seg), AND
THREE STAY HYPOTHESES: half, front, fits. SO FOUR HYPOTHESES STAY, BY NAME: hQ: the public data are
what `k4PubOf` returns at the public part and the member's parameters: that it returns (the public
part's table has the step "G‹g›.2.call") is not shown here (`k4Pub_head`, Law/FrontCount.lean, has
it under h and `LaidK4`); half: the prover's list of halves holds K4's half at the member's place:
K4's lot lays one there only where the public test `k4TableFits` accepts the public data besides,
and at its own `tokens` and `look`; front: as many rounds stand in front of the member as the public
data count (`front_head`, Law/FrontCount.lean, has it under h, `LaidK4` and hQ, in the form in which
`k4Seated_letters` asks it); fits: the public test `k4Fits`. `atK4_only` speaks of the written list
of places (`PS`); that member number k of the chain stands at the place `PS[k]` is not stated here
(the library's `P5J.At.places_paid`, Johnson/P5J/PlacesPaid.lean, has the whole flat list's places
under what h holds; `IM.link_flat_places`, Johnson/IMR/FlatScope.lean, a segment's). `K4Sits` and
its kin speak of the member's step alone. What that step tests of a value that is sent is not shown
here; the heads of Law/Hears.lean and Law/Accepted.lean say, by their writers' reading of the
sub-protocol's text: THE MEMBER's DECISION TESTS NO SENT VALUE: where their hypotheses on the plan
and the state hold, rounds of the right shape that hold other values than the honest ones are
accepted too. THE FULL SIZE ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`). Nothing
on soundness, on completeness or on any other property.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 18 modules under Johnson/Goal/ and at 5 under Johnson/Bridge/; it saw 46 modules whose
names hold RecCompile, none under Johnson/D/ or ThirdParty/, none that begins Cb.Bridge and none of
the three names. What lies behind the 23 is not counted: all the numbers are floors. They come with
h and with `IM.k4_of`. A LAW, NOT A PART: no file that defines a part of the proof file's
description may import this one.

Kin. `atK4_only` is the converse of the library's `atK4_full` (Johnson/Road/K4/K04Tied.lean), which
spells the place `k4PlaceAt g`: one term with `IM.k4Place g`; that K4's places in the written list
are twelve stands in the library's `k4_pinI_full` (Johnson/Road/K4/Rec/OpenNextAt.lean).
`k4NumsFitAt` is the library's `atK4s` (Johnson/Road/K4/Riders/PlanTests.lean: at every place of
K4's a test on the border's number and the segment's) at a test of its own; `k4PrevFitAt`
(Law/ReadyHead.lean) is it at another. `LaidK4` stands beside three of the library's: `K4Here`
(Johnson/Road/K4/K04Tied.lean): `k4Here_head` draws it from `LaidK4`; `K4SitsAt` and the end of
`k04_sits_desc` (Johnson/Road/K4/K04Sits.lean). `k04_sits_desc` has, by the same calls as
`laid_head`, the member at number 28 g + 4 of the flat list with the same equation, at every g below
12: from `onlineDescription`'s return, at a chain under «there is». `laid_head` has it at h's own chain cF,
from a number k at which `AtK4` holds, with the piece and the name besides, as one structure. Laws
of the same short names on other matters: `member_head` (Honest/K3/Law/MemberYes.lean), `laid_head`
(Johnson/P1K8R/FrontAtSeat.lean), `hb_head` (Johnson/P1K9R/CallerAtLetters.lean).

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.Road.K4.More.FrontList
import Johnson.Desc.ProofFile.Honest.K4.Law.SitsAt
import Johnson.Desc.ProofFile.Honest.K4.Law.SeatedAt
import Johnson.IMR.FlatScope
import Johnson.Road.K4.Riders.OnXOfPlan
import Johnson.IMR.PlanOkFlat
import Johnson.IMR.K8Seat
import Johnson.Road.K4.K04Sits
import Johnson.Road.K4.K04Tied

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.SeatedHead
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Road.K4 (AtK4 K4OnX)
open OnBytes.Road.K4.More (PS)
open OnBytes.Road.K4.Riders (atK4s atK4s_at k4OnX_of_scope)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block)
open VerifiableInference.Desc.Sound (MsgT linksFull)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead sits_head head_valid)

/-! ## 1 Which numbers stand at K4's places in the written lists -/

/-- A TEST ON THE TWO WRITTEN LISTS: at every number k of the list of places that stands at K4's
place of a layers' segment m: m is even, m / 2 is below the bound, k is stride · (m / 2) + off, and
the place written there is the library's address of K4 at group m / 2. -/
def k4NumsFitAt (stride off bound : Nat) : Bool :=
  atK4s linksFull PS fun k m =>
    decide (k = stride * (m / 2) + off) && decide (m % 2 = 0) && decide (m / 2 < bound) &&
      decide (PS[k]? = some (IM.k4Place (m / 2)))

/-- The test at the stride 28, the offset 4 and the bound 12. -/
def k4NumsFit : Bool := k4NumsFitAt 28 4 12

set_option maxRecDepth 1000000 in
theorem k4_nums_full : k4NumsFit = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: at another offset. -/
theorem k4_nums_off : k4NumsFitAt 28 5 12 = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: at another stride. -/
theorem k4_nums_stride : k4NumsFitAt 14 4 12 = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: at the bound 11 the test says false. -/
theorem k4_nums_bound : k4NumsFitAt 28 4 11 = false := by decide +kernel

/-- **A number at which `AtK4` holds in the written lists is one of the twelve**: the converse of
the library's `atK4_full` (Johnson/Road/K4/K04Tied.lean). Public. -/
theorem atK4_only {k m : ℕ} {pl : Place} (A : AtK4 linksFull PS k m pl) :
    ∃ g, g < 12 ∧ k = 28 * g + 4 ∧ m = 2 * g ∧ pl = IM.k4Place g := by
  have h0 := k4_nums_full
  unfold k4NumsFit k4NumsFitAt at h0
  have h := atK4s_at A h0
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h
  exact ⟨m / 2, c, a, by omega, Option.some.inj (A.here.symm.trans d)⟩

/-! ## 2 The member, free of the thread -/

/-- **Member number k of the chain's flat list is K4's lot's own sub-protocol at the parameters x,
seated alone at K4's place of group g**, with what the library says of x. It is a definition.
Nothing is claimed of it. -/
structure LaidK4 (Zp : ProofFile.Pub) (cF : Chain TS ProofFile.Cl) (k m g : ℕ) (x : Bool × Par)
    (blk : Block TS ProofFile.Cl) : Prop where
  /-- the group; the member's number; the segment's -/
  lt : g < 12
  num : k = 28 * g + 4
  seg : m = 2 * g
  /-- blk is the member -/
  member : cF.blocksInOrder[k]? = some blk
  /-- the equation on it -/
  laid : IM.LaidAlone ProofFile.sameReply blk (ProofFile.k4Block x) blk.name (IM.k4Place g)
  /-- x is a member of the lot's own list, at the ground that is made of the public part -/
  lot : ∃ G₀, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧
    x ∈ ProofFile.k4From Zp G₀ G₀.built.toList 0 none
  /-- its link, group, piece and name -/
  link : x.2.link = 2 * g
  grp : x.2.g = g
  piece : x.2.piece = 3
  name : x.2.name = s!"{"G" ++ toString g}:3"
  /-- its public data and plan are those of the public part's own structure -/
  P : x.2.P = (P5J.At.X Zp).layers
  hp : (P5J.At.X Zp).G[g]? = some x.2.hp

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **h AND `AtK4` GIVE IT.** CONDITIONAL: on h and A. -/
theorem laid_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m : ℕ} {pl : Place}
    (A : AtK4 linksFull PS k m pl) : ∃ g x blk, LaidK4 Zp cF k m g x blk := by
  obtain ⟨g, hg, hk, hm, _⟩ := atK4_only A
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, x, e1, e2, hx, hla, el, eg, eP, ehp, _, _⟩ := IM.k4_of h.scope h.reads O g hg
  obtain ⟨_, _, epc, enm⟩ := IM.k4_seated_scope h.scope h.reads O.pub O.blank hx
  have hi : IM.flatIx cF (2 * g) 2 = 28 * g + 4 := by
    rw [IM.flatIx_scope h.scope h.reads O (by omega) 2]
    omega
  have hf : cF.blocksInOrder[k]? = some b := by
    rw [hk, ← hi]
    exact IM.hear_at_flat e1 e2
  rw [eg] at enm
  rw [O.W] at eP ehp
  exact ⟨g, x, b, hg, hk, hm, hf, hla, ⟨Bs.G₀, O.blank, hx⟩, el, eg, epc, enm, eP, ehp⟩

/-! ## 3 At the thread -/

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  {k m g : ℕ} {x : Bool × Par} {blk : Block TS ProofFile.Cl}

/-- blk is the thread's member number k. -/
theorem member_head (Lh : LaidK4 Zp cF k m g x blk) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[k]? = some blk :=
  (congrArg (·[k]?) (sits_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).2.2.2.1).trans Lh.member

/-- **THE HYPOTHESIS hb OF Law/SitsAt.lean, AT THE THREAD.** -/
theorem hb_head (Lh : LaidK4 Zp cF k m g x blk) :
    ∀ blk', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[k]? = some blk' →
      ∃ name g', IM.LaidAlone ProofFile.sameReply blk' (ProofFile.k4Block x) name (IM.k4Place g') := by
  intro blk' hb
  obtain rfl : blk = blk' := Option.some.inj
    ((member_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lh).symm.trans hb)
  exact ⟨_, g, Lh.laid⟩

/-! ## 4 The seat's three hypotheses; `K4OnX` and `K4Here` at the member -/

/-- **`K4Sits` at the thread.** -/
theorem k4Sits_head (Lh : LaidK4 Zp cF k m g x blk) :
    K4Sits (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k
      { x.2 with k3Runs := true } :=
  k4Sits_of_laid (hb_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lh)

/-- **`K4NoMark` at the thread.** -/
theorem k4NoMark_head (Lh : LaidK4 Zp cF k m g x blk) :
    K4NoMark (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k :=
  k4NoMark_of_laid (hb_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lh)

/-- **`K4SitsBack` at the thread.** -/
theorem k4SitsBack_head (Lh : LaidK4 Zp cF k m g x blk) :
    K4SitsBack (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k
      { x.2 with k3Runs := true } :=
  k4SitsBack_of_laid (hb_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lh)

include h in
/-- **`K4OnX` at the member's parameters**: nine facts on the public parameters, one of the first
eleven hypotheses of `k4_behind_head` (Law/BehindHead.lean). Free of the thread. CONDITIONAL: on h
and Lh. -/
theorem k4OnX_head (Lh : LaidK4 Zp cF k m g x blk) :
    K4OnX (P5J.At.X Zp) Z.pol Z.KL (some Z.lay) m { x.2 with k3Runs := true } := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨G₀, hG, hx⟩ := Lh.lot
  obtain rfl : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans hG)
  have q := k4OnX_of_scope h.scope h.reads O Lh.lt hx Lh.link
  rw [O.W, ← Lh.seg] at q
  exact q

include h in
/-- **The library's `K4Here` (Johnson/Road/K4/K04Tied.lean) at the member**: what its statements on
K4's place at the table ask of the lot's member of group g: at the ground that is made of the public
part. Free of the thread. CONDITIONAL: on h and Lh. -/
theorem k4Here_head (Lh : LaidK4 Zp cF k m g x blk) :
    ∃ G₀, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧ G₀.W = P5J.At.X Zp ∧
      OnBytes.Road.K4.K4Here cF Zp G₀ g x blk := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨G₀, hG, hx⟩ := Lh.lot
  obtain rfl : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans hG)
  obtain ⟨e1, e2, _⟩ := ProofFile.k4From_par Zp Bs.G₀ _ _ _ x hx
  obtain ⟨Lk', b8, _, _, f1, f2, _⟩ := IM.k8_of_layers h.scope h.reads O g Lh.lt
  have hi8 : IM.flatIx cF (2 * g) 4 = 28 * g + 6 := by
    rw [IM.flatIx_scope h.scope h.reads O (by have := Lh.lt; omega) 4]
    omega
  have hf8 : cF.blocksInOrder[28 * g + 6]? = some b8 := by
    rw [← hi8]
    exact IM.hear_at_flat f1 f2
  have hl : 28 * g + 6 < cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hf8).1
  have hf : cF.blocksInOrder[28 * g + 4]? = some blk := by
    rw [← Lh.num]
    exact Lh.member
  exact ⟨Bs.G₀, hG, O.W, hx, Lh.grp, Lh.link, e1, e2, hf, by omega,
    OnBytes.Road.K4.declares_alone Lh.laid⟩

/-! ## 5 `K4Seated` at the thread -/

/-- **What `k4PubOf`'s return has of the member's parameters**: the fields own and seg of `K4Seated`
and the two equations of `k4Seated_of_laid` (Law/SeatedAt.lean). -/
theorem pub_of (Lh : LaidK4 Zp cF k m g x blk) {Qp : K4Pub} (hQ : k4PubOf Zp x.2 = some Qp) :
    (x.2.P = Qp.P ∧ x.2.hp = Qp.hp ∧ x.2.g = Qp.g ∧ x.2.link = Qp.link ∧ x.2.piece = Qp.piece) ∧
      (Qp.seg = Qp.link ∧ Qp.link = 2 * Qp.g) ∧ Qp.g = g ∧ Qp.piece = 3 := by
  unfold k4PubOf at hQ
  obtain ⟨r0, _, rfl⟩ := Option.map_eq_some_iff.1 hQ
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, ⟨?_, ?_⟩, Lh.grp, Lh.piece⟩
  · show 2 * x.2.g = x.2.link
    rw [Lh.link, Lh.grp]
  · show x.2.link = 2 * x.2.g
    rw [Lh.link, Lh.grp]

/-- **`K4Seated` AT THE THREAD.** CONDITIONAL: on h, Lh, hQ, half, front and fits. -/
theorem k4Seated_head (Lh : LaidK4 Zp cF k m g x blk) {cells : Tr → Cells}
    {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp)
    (half : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.hs.find?
      (fun z => z.place == blk.place) = some (k4Half cells weights tokens look Qp))
    (front : Qp.r0 = (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.front +
      roundsTo (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs k)
    (fits : ∀ fr v,
      drawsFit ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.ahead ++
        declsTo (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs k) fr = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.valid v →
      k4Fits Qp (look Qp fr) (tokens v.x) = true) :
    K4Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k cells weights
      tokens look Qp { x.2 with k3Runs := true } blk := by
  obtain ⟨own, seg, hg, hp⟩ := pub_of Lh hQ
  exact k4Seated_of_laid Lh.laid (member_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lh) own seg
    hg hp half front fits

/-- **`K4Seated` AT THE THREAD, ITS THREE OPEN FIELDS IN THE THREAD's OWN VALUES**: the halves are
the prover's own list; no round stands in front of the first chain; a valid input is the run's.
CONDITIONAL: on h, Lh, hQ, half, front and fits. -/
theorem k4Seated_letters (Lh : LaidK4 Zp cF k m g x blk) {cells : Tr → Cells}
    {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp)
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights tokens look Qp))
    (front : Qp.r0 = roundsTo cF.blocksInOrder k)
    (fits : ∀ fr, drawsFit (declsTo cF.blocksInOrder k) fr = true → Vd w →
      k4Fits Qp (look Qp fr) (tokens w.x) = true) :
    K4Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k cells weights
      tokens look Qp { x.2 with k3Runs := true } blk := by
  refine k4Seated_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lh hQ ?_ ?_ ?_
  · rw [IM.alone_place Lh.laid]
    exact half
  · show Qp.r0 = 0 + roundsTo cF.blocksInOrder k
    rw [Nat.zero_add]
    exact front
  · intro fr v hd hv
    obtain ⟨rfl, hV⟩ := (head_valid h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w v).1 hv
    exact fits fr hd hV

end ProofFile.Honest.K4.SeatedHead

#print axioms ProofFile.Honest.K4.SeatedHead.k4NumsFitAt
#print axioms ProofFile.Honest.K4.SeatedHead.k4NumsFit
#print axioms ProofFile.Honest.K4.SeatedHead.k4_nums_full
#print axioms ProofFile.Honest.K4.SeatedHead.k4_nums_off
#print axioms ProofFile.Honest.K4.SeatedHead.k4_nums_stride
#print axioms ProofFile.Honest.K4.SeatedHead.k4_nums_bound
#print axioms ProofFile.Honest.K4.SeatedHead.atK4_only
#print axioms ProofFile.Honest.K4.SeatedHead.LaidK4
#print axioms ProofFile.Honest.K4.SeatedHead.laid_head
#print axioms ProofFile.Honest.K4.SeatedHead.member_head
#print axioms ProofFile.Honest.K4.SeatedHead.hb_head
#print axioms ProofFile.Honest.K4.SeatedHead.k4Sits_head
#print axioms ProofFile.Honest.K4.SeatedHead.k4NoMark_head
#print axioms ProofFile.Honest.K4.SeatedHead.k4SitsBack_head
#print axioms ProofFile.Honest.K4.SeatedHead.k4OnX_head
#print axioms ProofFile.Honest.K4.SeatedHead.k4Here_head
#print axioms ProofFile.Honest.K4.SeatedHead.pub_of
#print axioms ProofFile.Honest.K4.SeatedHead.k4Seated_head
#print axioms ProofFile.Honest.K4.SeatedHead.k4Seated_letters
