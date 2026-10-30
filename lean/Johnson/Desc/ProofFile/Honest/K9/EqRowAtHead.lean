-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/EqRowAtHead.lean: K9's MEMBER "THE ONE EQUATION", THE HONEST DIRECTION, UNDER THE
LIBRARY's HEAD, AT ONE STATE: what the two twins of Honest/K9/EqRowFwd.lean ask, paid pointwise; and the whole join,
free of the thread. The library has these facts at the states of the verifier's side's frame (under the table's promise
and "reached" there); here the same stones are laid at a state with plain premises: reached, no mark, three of the
promise's tests. Statements and proofs ON THE VERIFIER's STATE AND, IN THE LAST, A WITNESS UNDER "FOR ALL"; but for
`head_eq_open` no thread is in this file, and no prover but that thread's letter H; no goal is stated.
  § 0 `eq_numA`, `eq_numB`, `eq_numC`   the member's number 14 l + `IM.nAt l` + 4 in the spellings of the lemmas that
      are called · § 1 `eq_step_sealed`: whatever block stands there: each of its yeses is `K9.oneEquation`'s (the
      library's `P5J.sits_at`) · § 2 `tabAt_eq_step`: the accessor's tables behind the step are those in front (the
      library's `tabAt_equation`'s own lines, at a step) · § 3 `ff_raw`: the frame's `foldFacts_raw` at the raw
      "reached" · § 4 `layout_inside_at`: every block of a required array lies inside it (`inside_of_fact`'s lines at
      one state)
  § 5 `totFit_W`, `totalIn_of_xk`, `bools_of_xk`   out of the promise's five tests (`IM.XK`): "the one sum can be taken"
      (`K9.totalIn`: THE ITEM total DOES NOT HOLD IT; the promise does) in front; `rowsHeld` and `bookAt`, at the
      library's other spelling of the lists · § 6 `eq_open`: the item total m is open in front of the member: a closed
      test, by the kernel; `eq_open_control`: ITS CONTROL: one border on it is open no more, and the row's item is not
      open in front; `head_eq_open`: at the frame's own thread · § 7 `insideAt_eq`: `insideAt_at_wrap`
      (Honest/K9/InsideAtWrap.lean) at its third border; `grp_behind`
  § 8 `eq_order`, `eq_codes`, `eq_shapes`, `eq_numbers`, `eq_places`, `rowOpen_e`, `hdue_e`, `hmem_e`, `eq_rows_size`,
      `eq_member`, **`eqRowAsks_behind`**   the library's `EqRowAsks`, field by field, at the state behind the step
  § 9 **`rowSays_behind`**   l < 25 · a yes of `K9.oneEquation`'s step from s to s' · in front: reached by the wrapped
      blocks, no mark, `totalIn` · behind: reached, no mark, `bookAt`, `rowsHeld` · AT EVERY WITNESS v: `totalQ` of the
      segment's group at s and `seatTab` gives `rowSays … l .equation (z, s') y v`. The bound on the number of oracle
      messages, a free letter in the sealed lemmas, is laid at `s.st.oracles.size`
DEVICES: "decide +kernel" twice (§ 6), under raised limits for recursion and instance search, as in the frame's
Honest/Law/Rule/OpenForms.lean. The first import stands so that the names in the folder's common "open" lines are there.
TACTICS THAT SEARCH: omega at numbers; simp at the lens's answers.
WHAT IS NOT CLAIMED. That any such state is there. The head is a premise. At the full size and the format's second hash function
alone. `rowSays_behind`, `head_eq_open`, `eq_step_sealed`, `totalIn_of_xk` and `bools_of_xk` are called by
Honest/K9/EqExchangeHead.lean; `eq_step_sealed` and `eq_rows_size` also by Honest/K9/EqRowNotIdle.lean. Nothing on any
property.
GROUND: beneath this file, beside the sealed library (laws.11), lie 380 files, this one among them: reading copies, all
but ours.
-/
import Johnson.Desc.ProofFile.Honest.K9.TotalExchangeHead
import Johnson.Desc.ProofFile.Honest.K9.InsideBehind
import Johnson.Desc.ProofFile.Honest.K9.EqRowFwd
import Johnson.Desc.ProofFile.Honest.K9.XkEqReach
import Johnson.Desc.ProofFile.Honest.K9.InsideAtWrap
import Johnson.Desc.ProofFile.Honest.Law.Rule.OpenForms
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.First.Link.Law.TieThreeAll
import Johnson.Desc.First.Link.Law.EqHands
import Johnson.Desc.First.Link.Law.TotOfPromise
import Johnson.Desc.First.Link.Law.K09Open
import Johnson.Desc.First.Link.Law.K09Lens
import Johnson.Desc.First.Batch.Law.TableTabs
import Johnson.Desc.First.Batch.Law.Layout
import Johnson.P5J.InsideAtMg
import Johnson.P5J.K09List
import Johnson.P5J.FoldJ3
import Johnson.P5T.MemThereAtMg
import Johnson.LPFK9R.FactsAtConstant
import Johnson.LPFK9R.HtinAtConstant
import Johnson.LPFK9R.SharesAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin (batchAt pi8 SegAt)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.First.K8.Honest (ThetaAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile.Honest.K8 (FrontAtStandN ValuesAtStand k8Share FoldOnce)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open LPFK9.HandsAt (EW)
open VerifiableInference.Desc.Sound (moreAll)
open VerifiableInference.Desc.K13.Law (LFull)
open VerifiableInference.Desc.K12.Door (msgShapesB msgShape_at bookInOrderB numbers_of_book0)

/-! ## 0 The number of "the one equation", in its spellings -/

/-- As the library's facts on the seat spell it. -/
theorem eq_numA {l : ℕ} (hl : l < 25) :
    batchAt P5J.fullLinks P5J.At.ps l + 1 + 1 = 14 * l + IM.nAt l + 4 := by
  have e := LPFK9.batch_nAt l hl
  omega

/-- As `insideAt_at_wrap` spells it. -/
theorem eq_numB {l : ℕ} (hl : l < 25) :
    batchAt P5J.fullLinks P5J.At.ps l + 2 = 14 * l + IM.nAt l + 4 := by
  have e := LPFK9.batch_nAt l hl
  omega

/-- The border behind, as the library's closed facts spell it. -/
theorem eq_numC {l : ℕ} (hl : l < 25) :
    batchAt P5J.fullLinks P5J.At.ps l + 1 + 1 + 1 = 14 * l + IM.nAt l + 4 + 1 := by
  have e := LPFK9.batch_nAt l hl
  omega

/-! ## 1 The step is the library's own -/

include h in
/-- Whatever block stands at that number of the first chain's flat list: each of its yeses is the one equation's. -/
theorem eq_step_sealed {l : ℕ} (hl : l < 25) {blk : Block S ProofFile.Cl}
    (hblk : cF.blocksInOrder[14 * l + IM.nAt l + 4]? = some blk) :
    ∃ p : Desc.K9.Where, ∀ ft s rs cols y, blk.step ft s rs cols = .ok y →
      (Desc.K9.oneEquation (Cl := ProofFile.Cl) Desc.K9.atS p).step ft s rs cols = .ok y := by
  obtain ⟨L, p, Qc, b₃, b₅, St⟩ := P5J.sits_at h l hl
  have e : cF.blocksInOrder[14 * l + IM.nAt l + 4]? = some b₃ := by
    rw [← eq_numA hl]
    exact St.atK2
  obtain rfl : b₃ = blk := Option.some.inj (e.symm.trans hblk)
  exact ⟨p, St.hb₃⟩

/-! ## 2 The accessor's tables behind the step are those in front -/

/-- The library's `tabAt_equation` at a step (there: at a piece): its own lines. -/
theorem tabAt_eq_step {Cl : Type} (own : List (ℕ × ℕ)) (rd : ℕ × ℕ → Sound.MsgQ) (p : Desc.K9.Where) (ft : ℕ)
    (s : S) (rs : List Fmt.RoundView) (cols : List Desc.OpenedColumn) (s' : S) (k : ℕ)
    (hs : (Desc.K9.oneEquation (Cl := Cl) Desc.K9.atS p).step ft s rs cols = .ok (s', k)) :
    K9L.tabAt own rd s' = K9L.tabAt own rd s := by
  obtain ⟨a0, out, ha0, hdoor, hs'⟩ := K9L.oneEquation_inv Desc.K9.atS p ft s rs cols s' k hs
  obtain ⟨n, q, G, row, d1, _, _, _, hrow, hd, _, _⟩ := K9L.door_parts _ _ _ _ _ out hdoor
  obtain ⟨a1, ha1, _, _, e3⟩ :=
    K9L.atS_reads s { a0 with owed := out.owed, L := out.L, F := out.F, d := out.d } (by simp [ha0])
  rw [← hs'] at ha1
  have hst : a1.d.st = out.d.st := e3
  refine K9L.tabAt_same own rd s s' a0 a1 ha0 ha1 ?_ (by rw [hs', K9L.book_set])
  rw [hst, hd]
  exact (K9L.asRow_bits _ _ _ _ _ _ hrow).trans (K9L.withRow_bits _ _ _)

/-! ## 3 The library's facts at what the chain's own members' steps reach -/

include h in
/-- `FoldFacts` at the raw "reached": the frame's `foldFacts_raw`, called as `hne_of_reach` calls it. -/
theorem ff_raw :
    FoldFacts (fun k (a : ProofFile.InstPub × S) => Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a) (fun a => a)
      (P5J.At.foldD Zp cF LFull) P5J.At.reqW P5J.At.links P5J.At.ps :=
  ProofFile.Honest.FirstThread.foldFacts_raw h.toAtMg
    (fun k (a : ProofFile.InstPub × S) => Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a) (fun a => a) (fun _ _ hr => hr)
    (P5J.laid_at_head h.toAtMg) (P5J.startB_at_head h.toAtMg)
    (P5J.sendsB_of_madeRow h.toAtMg (P5J.madeRow_at_head h.toAtMg))

/-! ## 4 The layout's "inside", at one state -/

include h in
/-- Every block of a required array lies inside it: the library's `inside_of_fact` at one reached state. -/
theorem layout_inside_at {k : ℕ} {z : ProofFile.InstPub} {s : S}
    (hR : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (z, s)) (hu : s.failed = none) {a : Desc.K9.Part}
    (ha : Desc.K9.atS.get? s = some a) :
    ∀ born name r, reqArray a.L.check.rows.layout born name = some r → ∀ bl ∈ r.blocks, K9L.Inside r bl := by
  intro born name r hr
  have h1 : s.live.rows.layout = (P5J.At.foldD Zp cF LFull).sent.layout :=
    (ff_raw h).liveLayout k (z, s) hR hu
  have hl : s.live = a.L.check := by
    unfold S.live
    rw [(LinkJoin.part_reads s a ha).1]
  rw [hl] at h1
  rw [h1] at hr
  exact K9L.inside_of_layoutOk _ _ _ (P5J.AtMg.layoutOk h.toAtMg LFull) born name r hr

/-! ## 5 "The one sum can be taken", out of the promise's Bools in front -/

/-- The library's test on the tables, at the written list. -/
theorem totFit_W : LinkJoin.totFitE moreAll IM.linksW IM.placesW = true := by
  rw [P5J.placesW_at, P5J.linksW_at]
  exact LinkJoin.totFitE_links

/-- From XK in front: after `index_of_xk` (Honest/K9/XkEqReach.lean), line for line. -/
theorem totalIn_of_xk {l : ℕ} (hl : l < 25) {N : Numbers} {Dp : PubData} {P : Type}
    {base : First.Pub → P × S → Bool} {z : P} {s : S}
    (hx : IM.XK N IM.linksW IM.placesW (EW Dp base z) (14 * l + IM.nAt l + 4) s = true) :
    Desc.K9.totalIn (Dp.N.group l) s = true := by
  obtain ⟨p, _, h1, _, h3, h4⟩ := LPFK9.HandsAt.place_W (l := l) (i := 2) hl (by omega)
  have hmem := LinkJoin.totE_at moreAll IM.linksW IM.placesW totFit_W _ l p h1 h3 h4
  have he : EW Dp base z (14 * l + IM.nAt l + 2 + 2) s = true := (IM.xk_parts hx).2.2.2.2
  have h5 : pubAll Dp base (.totalIn l) (z, s) = true := List.all_eq_true.1 he (.totalIn l) hmem
  rw [pubAll_totalIn] at h5
  exact h5

/-- The two Bools of XK that the row's road spends, at the library's other spelling of the lists. -/
theorem bools_of_xk {N : Numbers} {E : ℕ → S → Bool} {k : ℕ} {s : S}
    (hx : IM.XK N IM.linksW IM.placesW E k s = true) :
    rowsHeld N ((openSets P5J.fullLinks P5J.At.ps (start P5J.fullLinks))[k]?.getD []) s = true ∧
      bookAt N P5J.At.ps[k]? s = true := by
  obtain ⟨-, h2, -, h4, -⟩ := IM.xk_parts hx
  unfold IM.openAt at h2
  rw [P5J.placesW_at, P5J.linksW_at] at h2
  rw [P5J.placesW_at] at h4
  exact ⟨h2, h4⟩

/-! ## 6 The item "total" is open in front of the one equation -/

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem eq_open : ∀ m, m < 25 →
    Item.total m ∈ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
      (batchAt P5J.At.links P5J.At.ps m + 2) := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- A control: behind the one equation it is open no more, and in front of it the row's item is not open yet. -/
theorem eq_open_control : ∀ m, m < 25 →
    Item.total m ∉ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
      (batchAt P5J.At.links P5J.At.ps m + 3) ∧
    Item.row m .equation ∉ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps)
      (batchAt P5J.At.links P5J.At.ps m + 2) := by
  decide +kernel

/-- At the frame's own thread at the head. -/
theorem head_eq_open {l : ℕ} (hl : l < 25) :
    Item.total l ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened (14 * l + IM.nAt l + 4) := by
  rw [head_opened, ← eq_numB hl]
  exact eq_open l hl

/-! ## 7 In front of the step: "inside", and the group's number -/

/-- `insideAt_at_wrap` at its third border, at the number's other spelling. -/
theorem insideAt_eq {l : ℕ} (hl : l < 25) {z : ProofFile.InstPub} {s : S}
    (hw : Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) (14 * l + IM.nAt l + 4) (z, s))
    (hu : s.failed = none) {pa : Desc.K9.Part} (hpa : Desc.K9.atS.get? s = some pa) :
    Sound.InsideAt h.𝔇.cs h.𝔇.ms (h.𝔇.N.group l) pa := by
  rw [← eq_numB hl] at hw
  exact insideAt_at_wrap h hl (i := 2) (by omega) hw hu hpa

/-- Behind the step the link's check names the plan's group: `hg_of_reach` in front, the library's `grp_step`. -/
theorem grp_behind {l : ℕ} (hl : l < 25) {z : ProofFile.InstPub} {s : S}
    (hR : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 4) (z, s)) {Cl : Type} (p : Desc.K9.Where)
    (ft : ℕ) (rs : List Fmt.RoundView) (cols : List Desc.OpenedColumn) (s' : S) (n : ℕ)
    (hs : (Desc.K9.oneEquation (Cl := Cl) Desc.K9.atS p).step ft s rs cols = .ok (s', n)) :
    ∀ a', Desc.K9.atS.get? s' = some a' → a'.L.check.group = h.𝔇.N.groupAt l :=
  LinkJoin.grp_step p ft s rs cols s' n hs _ fun x hx => (hg_of_reach h hl hR x hx).symm

/-! ## 8 What the library's `EqRowAsks` asks of the state behind, a field a lemma -/

include h in
theorem eq_order {k : ℕ} {z : ProofFile.InstPub} {s : S} (hR : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (z, s))
    (hu : s.failed = none) : OnBytes.Means.InOrder s.st := by
  have e : OnBytes.Means.tidy4B s.st = true := (ff_raw h).tidy k (z, s) hR hu
  exact (OnBytes.Means.tidy4B_iff.1 e).inOrder

theorem eq_codes {k : ℕ} {z : ProofFile.InstPub} {s : S} (hR : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (z, s))
    (hu : s.failed = none) : s.st.codes = h.𝔇.cs := by
  have e : s.st.codes = (P5J.At.foldD Zp cF LFull).sent.codes := (ff_raw h).codes k (z, s) hR hu
  exact e

include h in
theorem eq_shapes {k : ℕ} {z : ProofFile.InstPub} {s : S} (hR : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (z, s))
    (hu : s.failed = none) : ∀ o, o < s.st.oracles.size →
      (s.st.oracles[o]?).map (·.shape) = (P5J.At.foldD Zp cF LFull).M[o]? := by
  have hsh : msgShapesB (P5J.At.foldD Zp cF LFull).M s.st = true := (ff_raw h).msgShapes k (z, s) hR hu
  exact fun o ho => msgShape_at hsh o ho

include h in
theorem eq_numbers {k : ℕ} {z : ProofFile.InstPub} {s : S} (hR : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (z, s))
    (hu : s.failed = none) : ∀ (t : ℕ) (T : OnBytes.Tree), s.book.trees[t]? = some T → T.number = t := by
  have hbk : bookInOrderB 0 s.book s.roots = true := (ff_raw h).bookInOrder k (z, s) hR hu
  exact fun t T hT => numbers_of_book0 hbk t T hT

include h in
theorem eq_places {k : ℕ} {z : ProofFile.InstPub} {s : S} (hR : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k (z, s))
    (hu : s.failed = none) {N : Numbers} {pl : Option Place} (hB : bookAt N pl s = true) :
    ∀ o, o < s.st.oracles.size → ∃ q : ℕ × ℕ, s.book.place[o]? = some q ∧ q.1 < s.book.trees.size := by
  have hf : Sound.bookFitsB s.book = true := (ff_raw h).bookFits k (z, s) hR hu
  have hfit : VerifiableInference.Desc.Book.BookFits s.book := (Sound.bookFitsB_iff s.book).1 hf
  unfold VerifiableInference.Desc.First.bookAt at hB
  simp only [Bool.and_eq_true, beq_iff_eq] at hB
  have hsz : s.book.place.size = s.st.oracles.size := hB.1.2
  intro o ho
  have ho' : o < s.book.place.size := by
    rw [hsz]
    exact ho
  have hq : s.book.place[o]? = some s.book.place[o] := Array.getElem?_eq_getElem ho'
  obtain ⟨t, ht, _⟩ := hfit o _ hq
  exact ⟨_, hq, (Array.getElem?_eq_some_iff.1 ht).1⟩

/-- The library's closed fact: behind the one equation the row's item is open in the table. -/
theorem rowOpen_e {l : ℕ} (hl : l < 25) : Item.row l .equation ∈
    ((openSets P5J.fullLinks P5J.At.ps (start P5J.fullLinks))[14 * l + IM.nAt l + 4 + 1]?.getD []) := by
  rw [← eq_numC hl]
  exact LinkJoin.rowOpen_at P5J.fullLinks P5J.At.ps LinkJoin.rowOpenFit_links l
    (by rw [LinkJoin.links_25]; exact hl)

/-- The library's `hdue_at`, at the number's other spelling. -/
theorem hdue_e {l : ℕ} (hl : l < 25) :
    rowsDue h.𝔇.N
      ((openSets P5J.fullLinks P5J.At.ps (start P5J.fullLinks))[14 * l + IM.nAt l + 4 + 1]?.getD []) l =
      (h.𝔇.N.rowsAt l .equation).1 + 1 := by
  rw [← eq_numC hl]
  exact LPFK9.hdue_at h l hl

/-- The library's `AtMg.hmem`, at the number's other spelling and the data's own letters. -/
theorem hmem_e {l : ℕ} (hl : l < 25) :
    LinkJoin.membersThereB (P5J.At.foldD Zp cF LFull) h.𝔇.ms (h.𝔇.N.group l)
      (h.𝔇.N.msgsAt P5J.At.ps[14 * l + IM.nAt l + 4 + 1]?) = true := by
  rw [← eq_numC hl]
  exact h.toAtMg.hmem (P5J.laid_at_head h.toAtMg) hl

/-- The group's list ends with the equation's row. -/
theorem eq_rows_size {l : ℕ} (hl : l < 25) {s' : S}
    (hRows : rowsHeld h.𝔇.N
      ((openSets P5J.fullLinks P5J.At.ps (start P5J.fullLinks))[14 * l + IM.nAt l + 4 + 1]?.getD []) s' = true) :
    ∀ G, s'.st.groups[h.𝔇.N.groupAt l]? = some G → G.rows.size = (h.𝔇.N.rowsAt l .equation).1 + 1 := by
  intro G hG
  have hm : l ∈ rowSegs
      ((openSets P5J.fullLinks P5J.At.ps (start P5J.fullLinks))[14 * l + IM.nAt l + 4 + 1]?.getD []) :=
    VerifiableInference.Desc.First.mem_rowSegs (rowOpen_e hl)
  have e := LinkJoin.rows_size h.𝔇.N _ s' l G hm hG hRows
  exact e.trans (hdue_e h hl)

/-- A member sits at a seat of the segment's own list, with the listed shape. -/
theorem eq_member {l : ℕ} (hl : l < 25) {z : ProofFile.InstPub} {s' : S}
    (hR : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 4 + 1) (z, s')) (hu : s'.failed = none)
    (hB : bookAt h.𝔇.N P5J.At.ps[14 * l + IM.nAt l + 4 + 1]? s' = true) {o : ℕ} {q : ℕ × ℕ}
    (hq : s'.book.place[o]? = some q) (hown : (h.𝔇.N.group l).contains q = true) :
    ∃ y, (h.𝔇.ms.find? fun y => decide (Sound.seatOf y = q)) = some y ∧
      (P5J.At.foldD Zp cF LFull).M[o]? = some (y.1.l.get y.2).1 :=
  LinkJoin.member_listed (ff_raw h) h.𝔇.N h.𝔇.ms (h.𝔇.N.group l) (k := 14 * l + IM.nAt l + 4 + 1)
    (a := (z, s')) hR hu hB hq hown (hmem_e h hl)

/-- **`EqRowAsks` at the state behind the step**, from plain premises at that state, and hgrp and hseat, which come
from the step. -/
theorem eqRowAsks_behind {l : ℕ} (hl : l < 25) {z : ProofFile.InstPub} {s' : S}
    (hR : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 4 + 1) (z, s')) (hu : s'.failed = none)
    (hB : bookAt h.𝔇.N P5J.At.ps[14 * l + IM.nAt l + 4 + 1]? s' = true)
    (hRows : rowsHeld h.𝔇.N
      ((openSets P5J.fullLinks P5J.At.ps (start P5J.fullLinks))[14 * l + IM.nAt l + 4 + 1]?.getD []) s' = true)
    (hgrp : ∀ a, Desc.K9.atS.get? s' = some a → a.L.check.group = h.𝔇.N.groupAt l)
    (hseat : ∀ a G row, Desc.K9.atS.get? s' = some a → a.d.st.groups[a.L.check.group]? = some G →
      G.rows.back? = some row → ∀ o part J, Reading.gl.val (row.coefficient o part J) ≠ 0 →
      ∀ q, a.d.book.place[o]? = some q → (h.𝔇.N.group l).contains q = true)
    {a' : Desc.K9.Part} (ha' : Desc.K9.atS.get? s' = some a') {Nb : ℕ} (hNb : s'.st.oracles.size ≤ Nb) :
    LinkJoin.EqRowAsks h.𝔇.cs h.𝔇.ms (P5J.At.foldD Zp cF LFull).M (h.𝔇.N.groupAt l)
      (h.𝔇.N.rowsAt l .equation).1 Nb s' :=
  { order := ⟨eq_order h hR hu, hNb⟩
    grp := hgrp
    rows := eq_rows_size h hl hRows
    codes := eq_codes h hR hu
    shapes := eq_shapes h hR hu
    numbers := eq_numbers h hR hu
    places := eq_places h hR hu hB
    member := fun G row hG hr o part J hz q hq =>
      eq_member h hl hR hu hB hq
        (hseat a' G row ha' (by rw [K9L.st_part s' a' ha', hgrp a' ha']; exact hG) hr o part J hz q
          (by rw [LinkJoin.book_part s' a' ha']; exact hq)) }

/-! ## 9 The join, free of the thread: from "total" in front to the row's sentence behind -/

/-- **From the one sum in front of a yes of the one equation's step to the item's sentence behind it**, at one pair of
states, from plain premises: reached · no mark · the promise's Bools. -/
theorem rowSays_behind {l : ℕ} (hl : l < 25) {z : ProofFile.InstPub} {s s' : S} {p : Desc.K9.Where} {ft : ℕ}
    {rs : List Fmt.RoundView} {cols : List Desc.OpenedColumn} {n : ℕ}
    (hs : (Desc.K9.oneEquation (Cl := ProofFile.Cl) Desc.K9.atS p).step ft s rs cols = .ok (s', n))
    (hw : Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) (14 * l + IM.nAt l + 4) (z, s))
    (hu : s.failed = none) (hT : Desc.K9.totalIn (h.𝔇.N.group l) s = true)
    (hR' : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 4 + 1) (z, s')) (hu' : s'.failed = none)
    (hB' : bookAt h.𝔇.N P5J.At.ps[14 * l + IM.nAt l + 4 + 1]? s' = true)
    (hRows' : rowsHeld h.𝔇.N
      ((openSets P5J.fullLinks P5J.At.ps (start P5J.fullLinks))[14 * l + IM.nAt l + 4 + 1]?.getD []) s' = true)
    (y : Strs) (v : WtF)
    (h0 : Sound.totalQ (h.𝔇.N.group l) s (Sound.seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v)) :
    rowSays h.𝔇.N (wordsAtFirst h.𝔇.arr) l .equation (z, s') y v := by
  have hraw : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 4) (z, s) := reach_raw hw
  -- the parts in front and behind
  obtain ⟨a, out, ha, hdoor, hs'⟩ := K9L.oneEquation_inv Desc.K9.atS p ft s rs cols s' n hs
  obtain ⟨a', ha', -, -, -⟩ :=
    K9L.atS_reads s { a with owed := out.owed, L := out.L, F := out.F, d := out.d } (by simp [ha])
  rw [← hs'] at ha'
  have hpart : (Desc.K9.atS.get? s').isSome = true := by simp [ha']
  -- the bound on the number of oracle messages: ours to choose
  obtain ⟨_, _, _, _, _, EL⟩ := LinkJoin.eq_lays p (Desc.K9.oneEquation (Cl := ProofFile.Cl) Desc.K9.atS p)
    (fun _ _ _ _ _ e => e) ft s rs cols s' n hs
  have hNb : s'.st.oracles.size ≤ s.st.oracles.size := Nat.le_of_eq EL.oracles
  -- the lens's law, as the library's `core3` has it
  have lens : ∀ (t : S) (b : Desc.K9.Part), (Desc.K9.atS.get? t).isSome = true →
      ∃ b', Desc.K9.atS.get? (Desc.K9.atS.set t b) = some b' ∧ b'.L = b.L ∧ b'.d.st = b.d.st := by
    intro t b hb
    obtain ⟨b', e0, _, e2, e3⟩ := K9L.atS_reads t b hb
    exact ⟨b', e0, e2, e3⟩
  -- the public premises of the row's law
  have P : ∀ a1 q G, Desc.K9.atS.get? s = some a1 → Desc.K9.equation a1.L a1.F = .ok (q, G) →
      K9L.RowPremises a1.L.check a1.d.st s.st.oracles.size q := by
    intro a1 q G h1 hq
    have e : a1 = a := Option.some.inj (h1.symm.trans ha)
    subst e
    exact K9L.door_facts _ _ _ _ _ out _ (Nat.le_of_eq (by rw [K9L.st_part s a1 h1]))
      (layout_inside_at h hraw hu h1) hdoor q G hq
  -- the one sum, in the row's words; the step forward; the tables behind
  have h1 := (K9L.total_iff (h.𝔇.N.group l) (Sound.seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v) s).1 h0
  have L0 : K9L.LastRowAt Desc.K9.atS Reading.gl s.st.oracles.size s'
      (K9L.tabAt (h.𝔇.N.group l) (Sound.seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v) s) :=
    equation_last_fwd Desc.K9.atS Reading.gl p ft s rs cols s' n s.st.oracles.size _ lens P hs h1.2
  have et := tabAt_eq_step (h.𝔇.N.group l) (Sound.seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v) p ft s rs cols s' n hs
  have L1 : K9L.rowEqQ (h.𝔇.N.group l) s.st.oracles.size s' (Sound.seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms v) := by
    unfold K9L.rowEqQ
    rw [et]
    exact L0
  -- what the reader's turn asks
  have hseat := K9L.seats_first (h.𝔇.N.group l) p ft s rs cols s' n hs hT
  have hins := K9L.rowInside_step h.𝔇.cs h.𝔇.ms (h.𝔇.N.group l) p ft s rs cols s' n s.st.oracles.size hs
    (fun x hx => insideAt_eq h hl hw hu hx)
  have hgrp := grp_behind h hl hraw p ft rs cols s' n hs
  have A := eqRowAsks_behind h hl hR' hu' hB' hRows' hgrp hseat ha' hNb
  have E := says_of_rowEq h.𝔇.cs h.𝔇.arr h.𝔇.ms (h.𝔇.N.group l) (P5J.At.foldD Zp cF LFull).M (h.𝔇.N.groupAt l)
    (h.𝔇.N.rowsAt l .equation).1 (h.𝔇.N.rowsAt l .equation).2 s.st.oracles.size s' v A hpart hseat hins L1
  exact E

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.eq_numA
#print axioms ProofFile.Honest.K9.eq_numB
#print axioms ProofFile.Honest.K9.eq_numC
#print axioms ProofFile.Honest.K9.eq_step_sealed
#print axioms ProofFile.Honest.K9.tabAt_eq_step
#print axioms ProofFile.Honest.K9.ff_raw
#print axioms ProofFile.Honest.K9.layout_inside_at
#print axioms ProofFile.Honest.K9.totFit_W
#print axioms ProofFile.Honest.K9.totalIn_of_xk
#print axioms ProofFile.Honest.K9.bools_of_xk
#print axioms ProofFile.Honest.K9.eq_open
#print axioms ProofFile.Honest.K9.eq_open_control
#print axioms ProofFile.Honest.K9.head_eq_open
#print axioms ProofFile.Honest.K9.insideAt_eq
#print axioms ProofFile.Honest.K9.grp_behind
#print axioms ProofFile.Honest.K9.eq_order
#print axioms ProofFile.Honest.K9.eq_codes
#print axioms ProofFile.Honest.K9.eq_shapes
#print axioms ProofFile.Honest.K9.eq_numbers
#print axioms ProofFile.Honest.K9.eq_places
#print axioms ProofFile.Honest.K9.rowOpen_e
#print axioms ProofFile.Honest.K9.hdue_e
#print axioms ProofFile.Honest.K9.hmem_e
#print axioms ProofFile.Honest.K9.eq_rows_size
#print axioms ProofFile.Honest.K9.eq_member
#print axioms ProofFile.Honest.K9.eqRowAsks_behind
#print axioms ProofFile.Honest.K9.rowSays_behind
