-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/MaskBelowHead.lean: CONDITIONAL. Statements with their
proofs.

What is here. THE ENTRIES OF THE SEGMENT's MASK ROW THAT THE TIE `K4MaskTieAt` (Law/ScriptAt.lean)
ASKS LIE BELOW THE PLAN's NUMBER OF ENTRIES, AND SO BELOW THE ROW's LAST PLACE, wherever the thread
with the library's own values (`lettersHead`, Honest/Thread/FirstHead.lean) stands in front of the
member of the feed-forward layers' own rounds (sub-protocol K4). The tie asks the entries a.F.next +
j with j + 1 below the number of coins that the member's row spends; it reads the mask row at the
numbers of the open ledger a.F's slots, so one number, the plan's hp.ns, is spoken of here as slots
and as entries. `maskEntries_below_head`: for each such j, a.F.next + j + 2 ≤ (parOf x).hp.ns.
`maskEntries_fence_head`: a.F.next + j + 3 ≤ 8192. `seg_open_head`: where the thread stands there a
segment is open: so wherever the thread stands there, these statements say something.
`maskEntries_room_head`: under `MaskRowPub` (Law/W/MaskSixHead.lean), a.F.next + j + 2 ≤ xl.ns and
a.F.next + j + 3 is within the mask code's length at the member u's shape.
How. Four links. (1) `k4_coins_total`, `spent_total`: the row spends as many coins as the hearing
takes slots (`k4Takes`, Johnson/Desc/First/K4/Returns/Whole.lean): at every public data, with no
hypothesis; the number of coins hangs on the row's types alone, so nothing is asked of the book that
lends them. (2) `ledger_at_all`, `fork_of_tests`, `ledger_front_head`: where the thread stands, the
open ledger's next free slot is the number of the lookup's entries and its number of slots is the
plan's: two of the promise's public tests (the items callerIn and freeAbove; the library's
`has_callerIn`, `has_freeAbove`, Johnson/Road/K4/More/FrontList.lean), drawn as `ownFront_at_all`
(Law/FrontHead.lean) draws its seven (freeAbove among them); the first of the two says besides that
a segment is open (`seg_of_test`). (3) `takes_room_head`: the lookup's entries and the member's are
within the plan's number: the sixth conjunct of `light_head` (Johnson/Road/K4/C/PublicLight.lean).
(4) `slotsSharp_head` and `maskRow_ell_is` (Law/W/MaskEllHead.lean) carry that number to 8192 and to
the mask code's length.

Not shown here. WHAT ANY ENTRY HOLDS: the tie itself stays a hypothesis of the statements that ask
it. The lookup's entries are counted in front; those of the segment's later members are not spoken
of. Nothing behind the member's step. THAT THE THREAD HOLDS AT ANY RUN: hT : Thr is a hypothesis:
WHERE THE THREAD STANDS NOWHERE THIS STATEMENT IS EMPTY. The hypotheses of the tops, all: h (the
library's `P5J.AtMgA` on the public files), `LaidK4`, hQ (a name of a public value: `k4Pub_head`,
Law/FrontCount.lean, has it), hT, and, in `maskEntries_room_head`, P, hl and hns, which follow from
h and `LaidK4` (`maskRow_laid`, Law/W/MaskRowAtSeg.lean); of h together with `LaidK4`, hQ and hT no
example is known to us. That h can hold: the side library AtFullSide proves, with no hypothesis,
that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). CAN THEY HOLD TOGETHER
AT AN HONEST SCRIPT: none of them names the script, the prover or a coin; hQ follows from h and
`LaidK4`; there are such j, since the row spends at least three coins (`k4_coins_b`,
Law/SlotsTrue.lean); we see no conflict among them: this was read, not checked by Lean; nothing has
been evaluated. THE FULL SIZE ALONE, and the format's second hash function alone, in all but (1),
`seg_of_test`, `fork_of_tests` and `ledger_at_all`, which stands at the full size's written lists
and names no hash. Beneath (2), (3) and (4) stand closed facts by Lean's own kernel, which no
independent checker has replayed: beneath (2) the library's `has_callerIn` and `has_freeAbove` and
one in `nine_head` (Law/ElevenHead.lean); beneath (3) and (4) those that the heads of
Johnson/Road/K4/C/PublicLight.lean and Law/W/MaskEllHead.lean name. A program's walk from import to
import, which reads import lines alone and stops unopened at Johnson/Goal/, ThirdParty/, Johnson/D/,
Johnson/Bridge/ and Cb/Bridge*, stopped at 70 modules under Johnson/Goal/, at 7 under
Johnson/Bridge/ and at 1 that begins Cb.Bridge, and saw 46 whose names hold RecCompile: floors. A
LAW, NOT A PART: no file that defines a part of the proof file's description may import this one.
Nothing on soundness, on completeness or on any other property. No property is claimed.

  `k4_coins_total`, `spent_total`   the coins that the row spends are `k4Takes`
  `ledger_at_all`, `seg_of_test`, `fork_of_tests`   two public tests; what they say of the segment
  `seg_open_head`   **where the thread stands a segment is open**
  `ledger_front_head`   **the ledger's next free slot and number of slots, where the thread stands**
  `takes_room_head`   the lookup's entries and the member's are within the plan's number
  `maskEntries_below_head`   **a.F.next + j + 2 ≤ (parOf x).hp.ns**
  `maskEntries_fence_head`, `maskEntries_room_head`   **against 8192; against xl.ns and the length**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MaskEllHead
import Johnson.Desc.ProofFile.Honest.K4.Law.FrontHead
import Johnson.Desc.ProofFile.Honest.K4.Law.SlotsTrue
import Johnson.Road.K4.C.PublicLight
import Johnson.Road.K4.More.FrontList
import Johnson.Road.K4.InT.ReaderAtK4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open Johnson.Pack (pMask)
open OnBytes.Desc.First.K4 (Par k0)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Rt (k4Takes slotsNorms slotsTerms slotsStack slotsGated slotsMerge nclp)
open OnBytes.Road.K4 (AtK4 K4OnD CellsK parOf k4DataWide k4Means_mgWide)
open OnBytes.Road.K4.C (light_head)
open OnBytes.Road.K4.Rec (RecPlan)
open OnBytes.Road.K4.More (PS front_mem hasAtK4 has_freeAbove has_callerIn)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Block Wit First.S)
open VerifiableInference.Desc.First (pubAll ePubAt pubWide_hand freeAboveB)
open VerifiableInference.Desc.First.FillK4 (isLay callerInLayB)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (MsgT Mem mgWide MgData WideData mgBase linksFull moreAll
  mgAll_more_base)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4 pub_of)

/-- The table's public items (`Pub` alone would name another type in this namespace). -/
local notation "PubI" => VerifiableInference.Desc.First.Pub

/-! ## 1 The coins that the row spends -/

/-- **THE ROW SPENDS AS MANY COINS AS THE HEARING TAKES SLOTS.** Public; no hypothesis. -/
theorem k4_coins_total (Q : K4Pub) :
    spentTo (k4RowIn Q) (k4RowIn Q).length = k4Takes Q.P Q.hp Q.g := by
  have len : (k4RowIn Q).length = k0 Q.g + 16 := by
    rw [k4RowIn_all, List.length_append, List.length_replicate]
    rfl
  have c16 := k4_coins_at Q 16
  rw [k4Tail_coins] at c16
  simp only [List.take_succ_cons, List.take_zero, List.sum_cons, List.sum_nil, Nat.add_zero]
    at c16
  rw [len, c16]
  unfold k4Takes slotsNorms slotsTerms slotsStack slotsGated slotsMerge nclp nStack ownOf
  omega

/-- The same of the list of the coins that the half's row is handed, whatever these are. -/
theorem spent_total {W₀ Rc Xi Tr X : Type} (cells : Tr → Cells) (weights : W₀ → Weights)
    (tokens : Xi → Array Nat) (look : K4Pub → List Fmt.Drawn → Forest.Heard) (Q : K4Pub)
    (c : RowCoins (k4Half (Rc := Rc) (X := X) cells weights tokens look Q).parts) :
    (spentOf _ c).length = k4Takes Q.P Q.hp Q.g := by
  rw [spentOf_length]
  show spentTo ((k4RowIn Q).map _) ((k4RowIn Q).map _).length = _
  rw [spentTo_lift, List.length_map]
  exact k4_coins_total Q

/-! ## 2 The open ledger in front of the member -/

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : Verify.Public}
  {Dm : MgData Xi P Tok rows cols nR X}

/-- The closed base, at the witness's type. -/
local notation "Bm" => (mgBase (P := P) (W := Wit (CellsK rows cols) Tok MsgT))

/-- **Two of the promise's public tests in front of the member**, after the proof texts of
`ownFront_at_all` (Law/FrontHead.lean) and `k4ReadyS_of_tests` (Law/ReadyOfPromise.lean). E₀: any
value serves. CONDITIONAL on every hypothesis named. -/
theorem ledger_at_all (E₀ : WideData P) {k m : ℕ} {pl : Place} {par : Par} {n : ℕ}
    (hH : isLay Dm.links (headLink X) = false) (H : AtK4 linksFull PS k m pl)
    (Sd : K4OnD Dm m par n) {z : P} {s : First.S}
    (hE : ePubAt (pubAll Dm.pubD (Bm).pub) moreAll linksFull PS k (z, s) = true) :
    callerInLayB n s = true ∧ freeAboveB par.hp.ns s = true := by
  have Em := k4Means_mgWide Dm E₀ Bm hH (fun _ _ _ _ h => h) fun _ _ _ => rfl
  have hand : ∀ (q : PubI), VerifiableInference.Desc.First.classA q = false → ∀ a,
      (mgWide Dm E₀ Bm).pub q a = pubAll Dm.pubD (Bm).pub q a := fun q hq a =>
    pubWide_hand E₀.d12 E₀.dP Dm.pubD (Bm).pub q hq a
  have fr : ∀ {f : ℕ → PubI}, hasAtK4 moreAll linksFull PS f = true →
      VerifiableInference.Desc.First.classA (f m) = false →
      (mgWide Dm E₀ Bm).pub (f m) (z, s) = true := fun {f} hf hc => by
    rw [hand _ hc]
    exact List.all_eq_true.1 hE _ (front_mem H hf)
  have hlay : isLay Dm.links m = true := by
    rw [Sd.links]
    unfold isLay
    rw [H.sub]
    rfl
  have f2 := fr (f := fun m => .freeAbove m) has_freeAbove rfl
  rw [Em.freeAbove] at f2
  have f2' : freeAboveB par.hp.ns s = true := by
    have e : (k4DataWide Dm E₀ Bm).nsOf m = some par.hp.ns := Sd.nsOf
    rw [e] at f2
    exact f2
  have f3 := fr (f := fun m => .callerIn m) has_callerIn rfl
  rw [Em.callerIn m _ hlay] at f3
  have f3' : callerInLayB n s = true := by
    have e : (k4DataWide Dm E₀ Bm).nextOf m = some n := Sd.nextOf
    rw [e] at f3
    exact f3
  exact ⟨f3', f2'⟩

end

/-- **Where the first test accepts a segment is open.** CONDITIONAL on hc. -/
theorem seg_of_test {s : First.S} {nu : ℕ} (hc : callerInLayB nu s = true) :
    ∃ a, segAt? s = some a := by
  unfold callerInLayB at hc
  cases hh : s.here with
  | lay a₀ =>
    obtain ⟨A, hA, -, -⟩ := OnBytes.Desc.First.K4.InT.segAt_lay hh
    exact ⟨A, hA⟩
  | _ =>
    rw [hh] at hc
    cases hc

/-- **What the two tests say of the open segment's ledger.** CONDITIONAL on hc and hf. -/
theorem fork_of_tests {s : First.S} {nu ns : ℕ} (hc : callerInLayB nu s = true)
    (hf : freeAboveB ns s = true) :
    ∀ a, segAt? s = some a → a.F.next = nu ∧ a.F.ns = ns := by
  intro a ha
  unfold callerInLayB at hc
  cases hh : s.here with
  | lay a₀ =>
    rw [hh] at hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨A, hA, eF, -⟩ := OnBytes.Desc.First.K4.InT.segAt_lay hh
    obtain rfl : A = a := Option.some.inj (hA.symm.trans ha)
    have e0 : s.fork? = some a₀.F := by simp only [First.S.fork?, hh]
    unfold freeAboveB at hf
    rw [e0] at hf
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at hf
    rw [eF]
    exact ⟨hc.2, hf.2⟩
  | _ =>
    rw [hh] at hc
    cases hc

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL on h and Lh. **The lookup's entries and the member's are within the plan's number
of entries of the mask row.** -/
theorem takes_room_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀) :
    Forest.elems (P5J.At.X Zp).y.fo + k4Takes x.2.P x.2.hp x.2.g ≤ (parOf x).hp.ns := by
  have l := (light_head h Lh.lt Lh.hp).2.2.2.2.2.1
  have e : Forest.elems x.2.P.y.fo + k4Takes x.2.P x.2.hp x.2.g ≤ x.2.hp.ns := by
    rw [Lh.P, Lh.grp]
    exact l
  rw [(nine_head h Lh).Sx.shape]
  exact e

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL on h, Lh and hT. **WHERE THE THREAD STANDS IN FRONT OF THE MEMBER, THE OPEN LEDGER's
NEXT FREE SLOT IS THE NUMBER OF THE LOOKUP's ENTRIES, AND ITS NUMBER OF SLOTS IS THE PLAN's.** -/
theorem ledger_front_head {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E) :
    ∀ a, segAt? s = some a →
      a.F.next = Forest.elems (P5J.At.X Zp).y.fo ∧ a.F.ns = (parOf x).hp.ns := by
  have A := atK4_of_laid Lh
  obtain ⟨hH, _, Sd, _, _⟩ := nine_head h Lh
  obtain ⟨_, t2, _⟩ := thr_tests h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hT
  obtain ⟨f3, f2⟩ := ledger_at_all
    (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) hH A Sd
    (ePubAt_of_held (Dm := h.𝔇)
      (Mg := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP) rfl
      (mgAll_more_base h.𝔇) t2)
  exact fork_of_tests f3 f2

/-- CONDITIONAL on h, Lh and hT. **WHERE THE THREAD STANDS IN FRONT OF THE MEMBER A SEGMENT IS
OPEN.** -/
theorem seg_open_head {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E) :
    ∃ a, segAt? s = some a := by
  have A := atK4_of_laid Lh
  obtain ⟨hH, _, Sd, _, _⟩ := nine_head h Lh
  obtain ⟨_, t2, _⟩ := thr_tests h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ hT
  exact seg_of_test (ledger_at_all
    (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull) hH A Sd
    (ePubAt_of_held (Dm := h.𝔇)
      (Mg := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).mgP) rfl
      (mgAll_more_base h.𝔇) t2)).1

/-! ## 3 The entries that the tie asks -/

/-- CONDITIONAL on h, Lh, hQ and hT. **EVERY ENTRY THAT `K4MaskTieAt` ASKS, AND ONE MORE, LIES BELOW
THE PLAN's NUMBER OF ENTRIES OF THE MASK ROW.** c': any term of the type of what the row is handed:
it is not asked to come of the book. -/
theorem maskEntries_below_head {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E) :
    ∀ a, segAt? s = some a →
      ∀ (c' : RowCoins (k4Half (Rc := Rc) (X := X') cells weights tokens look Qp).parts) (j : ℕ),
        j + 1 < (spentOf _ c').length → a.F.next + j + 2 ≤ (parOf x).hp.ns := by
  intro a ha c' j hj
  obtain ⟨⟨eP, eh, eg, -, -⟩, -, -, -⟩ := pub_of Lh hQ
  rw [spent_total, ← eP, ← eh, ← eg] at hj
  have n1 := (ledger_front_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hT a ha).1
  have r1 := takes_room_head h Lh
  omega

/-- CONDITIONAL on h, Lh, hQ and hT. **AGAINST 8192.** -/
theorem maskEntries_fence_head {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E) :
    ∀ a, segAt? s = some a →
      ∀ (c' : RowCoins (k4Half (Rc := Rc) (X := X') cells weights tokens look Qp).parts) (j : ℕ),
        j + 1 < (spentOf _ c').length → a.F.next + j + 3 ≤ 8192 := by
  intro a ha c' j hj
  have b :=
    maskEntries_below_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hQ hT a ha c' j hj
  have s1 : (parOf x).hp.ns + 1 ≤ 8192 := slotsSharp_head h Lh.lt Lh.hp
  omega

/-- CONDITIONAL on h, Lh, hQ, hT, P, hl and hns. **AGAINST THE LOOKUP's PLACE's NUMBER OF ENTRIES
AND THE MASK CODE's LENGTH AT u's SHAPE.** -/
theorem maskEntries_room_head {k m g : ℕ} {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk₀) {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread k c s mm E)
    {R : RecPlan} {n : ℕ} {xl : VerifiableInference.Desc.First.Look.Place} {o : ℕ} {u : Mem}
    (P : MaskRowPub h R n m xl o u) (hl : xl.link = m) (hns : xl.ns = (parOf x).hp.ns) :
    ∀ a, segAt? s = some a →
      ∀ (c' : RowCoins (k4Half (Rc := Rc) (X := X') cells weights tokens look Qp).parts) (j : ℕ),
        j + 1 < (spentOf _ c').length →
          a.F.next + j + 2 ≤ xl.ns ∧ a.F.next + j + 3 ≤ (pMask h.𝔇.cs (u.1.l.get u.2).1).ell := by
  intro a ha c' j hj
  refine ⟨?_, ?_⟩
  · rw [hns]
    exact maskEntries_below_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hQ hT a ha c' j hj
  · rw [maskRow_ell_is h Lh P hl]
    exact maskEntries_fence_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ Lh hQ hT a ha c' j hj

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4_coins_total
#print axioms ProofFile.Honest.K4.W.spent_total
#print axioms ProofFile.Honest.K4.W.ledger_at_all
#print axioms ProofFile.Honest.K4.W.seg_of_test
#print axioms ProofFile.Honest.K4.W.fork_of_tests
#print axioms ProofFile.Honest.K4.W.takes_room_head
#print axioms ProofFile.Honest.K4.W.ledger_front_head
#print axioms ProofFile.Honest.K4.W.seg_open_head
#print axioms ProofFile.Honest.K4.W.maskEntries_below_head
#print axioms ProofFile.Honest.K4.W.maskEntries_fence_head
#print axioms ProofFile.Honest.K4.W.maskEntries_room_head
