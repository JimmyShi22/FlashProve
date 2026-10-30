-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Xch/Says.lean: at the first chain's thread under the library's head, at the border
before the closing of a segment (kind K10): every row that the proximity test on the segment's group takes in says its
claim of the words of the run's witness. The conclusion is, to the letter, the premise named hs of
`carryExact_from_front` (Johnson/Desc/K10/Honest/CarryWords.lean), at arr := `P5J.At.arr Zp`, t₀ := s, D := D₀ and
v := the run's witness. No definition; one local notation.

The words.
  A thread: the structure of parameters of one chain's invariant (`Thread`, `Thr`: Honest/Thread/Thr.lean). `ThrS`
      is the invariant together with a second condition `Said` (Honest/Thread/Said.lean).
  The head: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean), here at the older hash. The head's
      thread is the field `thread` of `lettersHead` at its parameters (Honest/Thread/FirstHead.lean).
  Border b: the position in the chain before sub-protocol number b. The closing of segment l is sub-protocol number
      14 l + `IM.nAt l` + 5, where `IM.nAt l` is 9 at l = 24 and 7 elsewhere (Johnson/IMR/WrittenList.lean).
  An item: an entry of the table of joints (Johnson/Desc/First/Borders.lean). `Item.row l c` is the item of the
      class c of rows of segment l; `rowsOf l` lists the items of the classes that the closing's row asks. `(𝕋).means`
      gives the sentence that an item stands for.
  The record: `K9.recOf s`, the part of the first chain's state s that the closing reads: what is owed, the live
      frame, the statement. `CloseBase` lists facts on that record (Johnson/Desc/K10/Honest/Base.lean).
  The run's witness: `Sc.wit` at the run's coins, its input and a list of challenges.
  The test, a class, a row says its claim of words: see the head of Johnson/Desc/K10/Honest/TakenIn.lean (`AllSay`,
      `Says`: Johnson/Desc/Means/Says.lean).

The premises' names.
  hT: the invariant holds at the border before the closing of segment l.
  Hb: `CloseBase` holds of the record. The field `there` alone is read: the statement has the group D₀.G at the
      number that the record's frame names.
  hGrp: the group that the record's frame names is the table's number for segment l.
  hF, hf: the thread's clause `formP` holds at the border; the state bears no mark of failure.
  hJ: the sentences of the items of `rowsOf l` hold, at one witness.

What is proved.
  `row_says`: at the library's meaning `mgAll`, at any parameters, the sentence of `Item.row m c` gives `rowSays` at
      the parameters' numbers and at the reader `wordsAtFirst`. By `mgAll_row` (Johnson/Desc/Sound/MgAll.lean).
  `frame_of_open`: where a link is open, the record's frame is that link's frame.
  `means_row_at_head`: `row_says` at the meaning of the head's thread, at `P5J.At.N Zp cF` and `P5J.At.arr Zp`.
  `held_at_head`: hF and hf at a border b give `rowsHeld` and `membersHeld` at the table's open set `P5J.oAt b`.
  `says_of_means`: from hF, hf, Hb, hGrp and hJ: all rows that the test takes in say their claims of the words of
      the witness of hJ.
  `group_at_thr`: hT gives hGrp. The invariant's clause on how the state was made says that a fold of the chain's
      first sub-protocols, from the chain's first state, returns the state; the library's `Meaning.K2.group_all`
      (Johnson/IMR/GroupHead.lean) says of such a state that link l is open and that its frame names group l.
  `says_at_thr`: from hT and Hb: the conclusion of `says_of_means` at the run's witness, at every continuation ds of
      the challenges heard.
  `says_at_head`: the same from `ThrS`, at every Said.

By: `allSay_at_base`, `held_of_onAt`, `only_of_listed` (Johnson/Desc/K10/Honest/TakenIn.lean); the library's facts on
the table's open sets at the 25 closings, `hm_at` (Johnson/LPFE1R/K10Small.lean), `covered_laid` and `listed_at_k10`
(Johnson/LPFE1R/RowsDueAt.lean); `number_is` (Johnson/Desc/K10/Honest/KeepsSeat.lean); `front_open_at_head`
(Xch/RowAt.lean). Of the head three fields are used, `scope`, `reads` and `laid`, beside what the thread's own text
takes from it.

The notation, and the option in front of it. 𝕋 stands for the head's thread, written out once. It declares no new
name, neither a definition nor a theorem: each use is that text, elaborated anew. A field of it is written with
brackets, `(𝕋).means`: without them Lean reads `𝕋.means` as one name. When a notation is declared, Lean looks through
its text for names that are not bound, and that early look has no case for a field access.
`set_option quotPrecheck false in` turns that one look off for the one command behind it; it loosens nothing in what
Lean checks of a theorem.

Limits. The premises of `says_at_thr` and `says_at_head` are the head h, l < 25, hT and Hb. Hb is shown of no state
here. The premises of `says_of_means` are the head h, l < 25, hF, hf, Hb, hGrp and hJ. The prover H, the book Bk, the
further parameters of `lettersHead` (Sc, test, carryX, item, n₁, n₂, b₀, Vd, Rd, Kp, w) and Said are variables: the
statements hold at each of them, so at every value of carryX. The statements are implications. They are idle at a
border at which the invariant holds at no state, and at a group from which the test takes nothing in. It is not shown
that the invariant holds in any run, or that the sentence of a class of rows holds at any state of a run: here it is
read off the invariant. Whether the head can be had at any files is not shown here. The full size and the older hash
alone.
No property of the protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Xch.RowAt
import Johnson.Desc.K10.Honest.TakenIn
import Johnson.Desc.K10.Honest.KeepsSeat
import Johnson.LPFE1R.RowsDueAt
import Johnson.LPFE1R.K10Small
import Johnson.IMR.GroupHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Chain Place Strs Wit foldBlocks)
open VerifiableInference.Desc.First (S Item RowClass Meaning onAt pubSets rowsOf rowsHeld membersHeld rowSays
  wordsAtFirst)
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.K9 (recOf)
open VerifiableInference.Desc.LinkJoin (hm_at covered_laid listed_at_k10)
open VerifiableInference.Desc.Sound (MsgT MgData mgAll mgBase mgAll_row CellsQ wordsFirst)
open OnBytes.Means (AllSay)
open OnBytes.Slice (rdE)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)

/-! ## At the library's meaning -/

/-- At the library's meaning, the sentence of the item of a class of rows gives `rowSays` at the parameters' numbers
and at the reader `wordsAtFirst`. -/
theorem row_says {Xi P Tok : Type} {rows cols nR : Nat} {X : OnBytes.Model.Verify.Public}
    (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (m : Nat)
    (c : RowClass) (a : P × S) (y : Strs) (v : Wit (CellsQ rows cols) Tok MsgT)
    (h0 : (mgAll 𝔇 Mg).row m c a y v) : rowSays 𝔇.N (wordsAtFirst 𝔇.arr) m c a y v := by
  rw [mgAll_row] at h0
  exact h0

/-- Where a link is open, the frame of the record `K9.recOf s` is that link's frame. -/
theorem frame_of_open {s : S} {L : OnBytes.Model.LinkCtx} (hL : s.link? = some L) :
    (recOf s).frame = L.check.frame := by
  show s.live.frame = _
  unfold VerifiableInference.Desc.First.S.live
  rw [hL]

/-! ## At the head's thread -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

-- The first chain's thread under the head. Why the option stands here: this file's head, "The notation, and the
-- option in front of it".
set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- At the meaning of the head's thread, the sentence of the item of a class of rows gives `rowSays` at the head's
numbers and at the reader `wordsAtFirst`. -/
theorem means_row_at_head (l : Nat) (c : RowClass) (u : Local W₀ Rc ProofFile.Inst Tr) {p : ProofFile.InstPub} {s : TS}
    {y : Strs} {v : WtF} (h0 : (𝕋).means u (Item.row l c) (p, s) y v) :
    rowSays (P5J.At.N Zp cF) (wordsAtFirst (P5J.At.arr Zp)) l c (p, s) y v := by
  have h1 : (mgAll { h.𝔇 with decT := fun _ _ => some (Sc.cells u), cr1 := carryX } mgBase).row l c (p, s) y v := h0
  have h2 := row_says { h.𝔇 with decT := fun _ _ => some (Sc.cells u), cr1 := carryX } mgBase l c (p, s) y v h1
  exact h2

/-- The thread's clause `formP` at a border, at a state without a mark of failure, gives `rowsHeld` and `membersHeld` at
the table's open set at that border. -/
theorem held_at_head (b : Nat) {p : ProofFile.InstPub} {s : TS} (hF : (𝕋).formP b (p, s)) (hf : s.failed = none) :
    rowsHeld (P5J.At.N Zp cF) (P5J.oAt b) s = true ∧ membersHeld (P5J.At.N Zp cF) (P5J.oAt b) s = true := by
  have hon : onAt (P5J.At.N Zp cF) (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP P5J.At.links
      P5J.At.ps[b]? (P5J.oAt b)
      (((pubSets (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.more P5J.At.links
        P5J.At.ps)[b]?).getD []) (p, s) noStrs := hF
  exact TakenIn.held_of_onAt hon hf

/-- **From the sentences of the items of `rowsOf l` at one witness**, with hF, hf, Hb and hGrp: all rows that the test
on the segment's group takes in say their claims of that witness's words. -/
theorem says_of_means (l : Nat) (hl : l < 25) (u : Local W₀ Rc ProofFile.Inst Tr) {p : ProofFile.InstPub} {s : TS} {y : Strs}
    {v : WtF} (hF : (𝕋).formP (14 * l + IM.nAt l + 5) (p, s)) (hf : s.failed = none) {Qc : Par} {D₀ : BaseData}
    (Hb : CloseBase Qc (recOf s) D₀) (hGrp : (recOf s).frame.group = (P5J.At.N Zp cF).groupAt l)
    (hJ : ∀ j ∈ rowsOf l, (𝕋).means u j (p, s) y v) :
    AllSay rdE (recOf s).st (OnBytes.Slice.runRows (recOf s).st D₀.G).toList
      (wordsFirst (P5J.At.arr Zp) s.st s.book v) := by
  have e2 : LPFK10.ixK10 l = 14 * l + IM.nAt l + 5 := YesFree.number_is l
  obtain ⟨hR, hM⟩ := held_at_head h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w (14 * l + IM.nAt l + 5) hF hf
  rw [← e2] at hR hM
  have hrows : ∀ c : RowClass, Item.row l c ∈ rowsOf l →
      rowSays (P5J.At.N Zp cF) (wordsAtFirst (P5J.At.arr Zp)) l c (p, s) y v :=
    fun c hc => means_row_at_head h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w l c u (hJ _ hc)
  exact TakenIn.allSay_at_base (P5J.At.arr Zp) p s y v Hb hGrp hR hM (hm_at hl)
    (covered_laid h.scope h.laid hl) (TakenIn.only_of_listed (listed_at_k10 hl)) hrows

/-- **Wherever the invariant holds at the border before the closing of segment l, the group that the record's frame
names is the table's number for segment l.** -/
theorem group_at_thr (l : Nat) (hl : l < 25) {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr 𝕋 (14 * l + IM.nAt l + 5) k s m E) :
    (recOf s).frame.group = (P5J.At.N Zp cF).groupAt l := by
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, -, -, hMd, -, -⟩ := hT'
  unfold Thread.Made at hMd
  obtain ⟨-, -, -, -, s₀, cols, hb, -, hfold⟩ := hMd
  have hb' : s₀ = ProofFile.startS Zp m.st.input.x.pub := hb
  have hfd : foldBlocks 0 (cF.blocksInOrder.take (14 * l + IM.nAt l + 5)) (ProofFile.startS Zp m.st.input.x.pub)
      (m.seen.drop (𝕋).front) cols = .ok (s, [], []) := by
    rw [← hb']
    exact hfold
  have hn : IM.nAt l = if l = 24 then 9 else 7 := rfl
  have b1 : 14 * l + 3 + (if l = 24 then 1 else 0) ≤ 14 * l + IM.nAt l + 5 := by
    rw [hn]
    by_cases e : l = 24
    · rw [if_pos e, if_pos e]
      omega
    · rw [if_neg e, if_neg e]
      omega
  have b2 : 14 * l + IM.nAt l + 5 ≤ 14 * l + 14 + (if l = 24 then 2 else 0) := by
    rw [hn]
    by_cases e : l = 24
    · rw [if_pos e, if_pos e]
      omega
    · rw [if_neg e, if_neg e]
      omega
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨L, hL, -, hg⟩ := _root_.Meaning.K2.group_all h.scope h.reads O hl b1 b2 hfd
  show (recOf s).frame.group = l
  rw [frame_of_open hL]
  exact hg

/-- **Wherever the invariant holds at the border before the closing of segment l and `CloseBase` holds of the record**:
all rows that the test takes in say their claims of the words of the run's witness, at every continuation of the
challenges heard. -/
theorem says_at_thr (l : Nat) (hl : l < 25) {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr 𝕋 (14 * l + IM.nAt l + 5) k s m E) {Qc : Par} {D₀ : BaseData} (Hb : CloseBase Qc (recOf s) D₀)
    (ds : List Fmt.Drawn) :
    AllSay rdE (recOf s).st (OnBytes.Slice.runRows (recOf s).st D₀.G).toList
      (wordsFirst (P5J.At.arr Zp) s.st s.book (Sc.wit k m.st.input (m.st.heard ++ ds))) := by
  have hGrp := group_at_thr h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w l hl hT
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, hP, hI, -, -, -⟩ := hT'
  have hn : s.failed.isNone = true := hP.1
  have hf : s.failed = none := Option.isNone_iff_eq_none.1 hn
  have hF : (𝕋).formP (14 * l + IM.nAt l + 5) (m.st.input.x.pub, s) := hP.2
  have hJ : ∀ j ∈ rowsOf l, (𝕋).means m.st.input j (m.st.input.x.pub, s) ((𝕋).strs E)
      (Sc.wit k m.st.input (m.st.heard ++ ds)) :=
    fun j hj => hI ds j
      (front_open_at_head h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w l hl j (List.mem_append_left _ hj))
  exact says_of_means h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w l hl m.st.input hF hf Hb hGrp hJ

/-- The same from the invariant together with a second condition `Said`, at every `Said`. -/
theorem says_at_head (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (l : Nat) (hl : l < 25)
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : ThrS 𝕋 Said (14 * l + IM.nAt l + 5) k s m E) {Qc : Par} {D₀ : BaseData}
    (Hb : CloseBase Qc (recOf s) D₀) (ds : List Fmt.Drawn) :
    AllSay rdE (recOf s).st (OnBytes.Slice.runRows (recOf s).st D₀.G).toList
      (wordsFirst (P5J.At.arr Zp) s.st s.book (Sc.wit k m.st.input (m.st.heard ++ ds))) :=
  says_at_thr h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w l hl hT.1 Hb ds

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.row_says
#print axioms ProofFile.Honest.K10.frame_of_open
#print axioms ProofFile.Honest.K10.means_row_at_head
#print axioms ProofFile.Honest.K10.held_at_head
#print axioms ProofFile.Honest.K10.says_of_means
#print axioms ProofFile.Honest.K10.group_at_thr
#print axioms ProofFile.Honest.K10.says_at_thr
#print axioms ProofFile.Honest.K10.says_at_head
