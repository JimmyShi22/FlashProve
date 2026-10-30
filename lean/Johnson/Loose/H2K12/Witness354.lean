-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Loose/H2K12/Witness354.lean:
THE LAW OF THE PROXIMITY TEST (the kind K12) ON THE PROOF FILE's FIRST
CHAIN: THE SECOND HALF OF THE FOURTH TIE of what is owed there (TiedAtR,
Johnson/Desc/Sound/ChainOfPromisesR.lean): from one tuple of candidates to the items that the test's
row closes, AT THE WITNESS THAT THE TABLE's ONE EXTRACTOR GIVES. Definitions, statements and proofs.

What is said. In front: the middle of the fourth tie (Tuple354, H2K12/Frame354.lean):
the door enterFinish lets the state in; there is one tuple m of typed messages of which
every row that the test takes in says its claim, and m is a candidate (in the word's list, with the
answers of the out-of-domain (OOD) sample; our files call it the record) at each member of the group
under test. Behind: at the witness extQAt (Johnson/Desc/Sound/BordersFill.lean), which lays the
row's own members' messages and pads from what the committed words decode to: the pin of every
tenant that the last group's moment 0 sends, the three classes of rows (carried, the samples of
moment 0, position), and "no mark".
Main names:
  pK              the test's place in the table's list: ⟨1, none, 2, K12⟩.
  openFitB, openFit_gives   a test on the table's lists at a number k: what the row at pK closes is
                  open in front, and the pins of the last group's moments 1 and 2 are not.
  openFit_full    the test passes at the written lists at number 354: decided by the kernel.
  openFit_353, openFit_355   the test can fail: at the two numbers beside. (That a test can fail
                  does not show that the premises below can be met.)
  mine_nodup      no two of the row's own members have one number, from two tests on the plan:
                  laysNodup (Johnson/Desc/First/Borders.lean) and "no two members at one seat".
  ext_msg, ext_pad   what the extractor lays at one of the row's own members that decodes.
  words_laid      at a message whose member's two components are laid from the tuple, the words
                  built of the tuple (wordsT, Johnson/Desc/K14/Law/LedgerSay.lean) are the words
                  that the table's reader wordsFirst (Johnson/Desc/Sound/WordsAt.lean) reads off the
                  witness: at both tables and at EVERY index: the extractor lays the whole decoded
                  table, which is 0 outside the message's ranges.
  Spent           what is spent of the verifier's state beside the table's promise: six fields.
  members_sit     by the promise's membersHeld: the places of the members of the group under test
                  are just the tenants of the last group's moment 0, both ways.
  witness_core    the statement at plain letters (the group, the tuple, the rows, the candidates).
  enter_st        what the door returns has the state's own statement.
  witness_at      THE HALF TIE (T4bAt, H2K12/Frame354.lean) at whichever
                  number k of the list has the place pK.
  place_full, witness_354   the same at the written lists and number 354: there the place and the
                  test on the lists are decided by the kernel, and are premises no more.
By: dec_of_cand, agree_of_nodup (Johnson/Desc/Sound/WordsLaw.lean) · pin_ext, msgAt_of, tabBy_of
(Johnson/Desc/Sound/World.lean) · run_agree, rdK_tabP (Johnson/Desc/Sound/SeamWords.lean) ·
allSay_same (Johnson/Desc/K14/Law/Shapes.lean) · listClass_taken, sampleClass_taken
(Johnson/Desc/First/Close/Law/FillRow.lean).
OF THE TABLE's PROMISE AT THE BORDER (onAt, Johnson/Desc/First/Borders.lean) THREE CLAUSES ARE
SPENT, at an unmarked state: rowsHeld · membersHeld · "no collision" at the tenants of the last
group's moment 0. Not spent: decodes, the book-keeping's other four tests, samplesHeld, shown, pubP;
nor the condition Rch, the accept, or what the row opens, but as far as Spent is handed under the
first.
Limits. (1) A JOINING OVER LETTERS: the meaning Mg enters by three named equations (pin, noColl,
row); the tuple and Spent are premises. WHETHER ALL PREMISES CAN BE MET TOGETHER AT ONE STATE IS
SHOWN NOWHERE HERE: where they cannot, the statement is true and says nothing. (2) laysNodup and "no
two members at one seat" are tests on the plan that no other statement asks: they are named
premises. (3) Spent is proved of no state. (4) openFit_full is decided at one version of the written
lists; at another it would have to be decided again. (5) nodup_of_eachOnce has a like in
Johnson/Desc/First/Link/Law/EqNumbersOf.lean (eachOnce_nodup), which is not imported: its cone is
not needed here. No soundness statement. Nothing on hiding.

-/
import Johnson.Desc.Sound.SeamWords
import Johnson.Desc.Sound.SeamRows
import Johnson.Desc.Sound.BordersFill
import Johnson.Desc.Sound.ReadAt
import Johnson.Desc.First.Close.Law.FillRowFirst
import Johnson.Desc.Sound.AtDriver
import Johnson.Loose.H2K12.Frame354

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace H2K12.Wit354

open VerifiableInference.Desc (FileDescription Strs Wit Place)
open VerifiableInference.Desc.Sound (Mem Sending MsgT seatOf numOf toMsgT Frame strsOf)
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers)

/-- The place of the proximity test at the end of the proof file's first chain. -/
abbrev pK : Place := ⟨1, none, 2, .K12⟩

/-! ## 1 The table's row at that place, by the make -/

theorem ins_at (links : List ModelPart) : (VerifiableInference.Desc.First.rowOf links pK).ins =
    [.row links.length .carried, .row links.length (.sample 0), .row links.length .position,
      .pin links.length 0] := rfl

theorem ctx_at (links : List ModelPart) : (VerifiableInference.Desc.First.rowOf links pK).ctx = [] := rfl

theorem laysSeats_at (N : Numbers) (links : List ModelPart) :
    VerifiableInference.Desc.First.laysSeats N links pK = N.group links.length := rfl

theorem laysPads_at (N : Numbers) (links : List ModelPart) :
    VerifiableInference.Desc.First.laysPads N links pK = [] := rfl

/-- **A test on the table's lists**: at number k, in front of the sub-protocol, every item that the
row at pK closes is open, and the pins of the last group's moments 1 and 2 are not. -/
def openFitB (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  (VerifiableInference.Desc.First.rowOf links pK).ins.all
      ((VerifiableInference.Desc.First.openSets links ps
        (VerifiableInference.Desc.First.start links))[k]?.getD []).contains &&
    !((VerifiableInference.Desc.First.openSets links ps
        (VerifiableInference.Desc.First.start links))[k]?.getD []).contains
      (.pin links.length 1) &&
    !((VerifiableInference.Desc.First.openSets links ps
        (VerifiableInference.Desc.First.start links))[k]?.getD []).contains
      (.pin links.length 2)

theorem openFit_gives (links : List ModelPart) (ps : List Place) (k : ℕ)
    (h : openFitB links ps k = true) :
    (∀ i ∈ (VerifiableInference.Desc.First.rowOf links pK).ins,
      i ∈ (VerifiableInference.Desc.First.openSets links ps
        (VerifiableInference.Desc.First.start links))[k]?.getD []) ∧
    Item.pin links.length 1 ∉ (VerifiableInference.Desc.First.openSets links ps
        (VerifiableInference.Desc.First.start links))[k]?.getD [] ∧
    Item.pin links.length 2 ∉ (VerifiableInference.Desc.First.openSets links ps
        (VerifiableInference.Desc.First.start links))[k]?.getD [] := by
  unfold openFitB at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨fun i hi => List.contains_iff_mem.1 (List.all_eq_true.1 h.1.1 i hi), fun c => ?_,
    fun c => ?_⟩
  · rw [List.contains_iff_mem.2 c] at h
    exact absurd h.1.2 (by decide)
  · rw [List.contains_iff_mem.2 c] at h
    exact absurd h.2 (by decide)

/-! ## 2 No two of the row's own members have one number -/

theorem nodup_of_eachOnce : ∀ l : List (ℕ × ℕ),
    VerifiableInference.Desc.First.eachOnce l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: l, h => by
    have h' := Bool.and_eq_true_iff.1 h
    refine List.nodup_cons.2 ⟨fun hx => ?_, nodup_of_eachOnce l h'.2⟩
    have : l.contains x = true := List.contains_iff_mem.2 hx
    rw [this] at h'
    exact absurd h'.1 (by decide)

/-- From the two tests on the plan: laysNodup, and "no two members of the list at one seat". -/
theorem mine_nodup (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (links : List ModelPart)
    (ps : List Place) (p : Place) (hp : p ∈ ps)
    (hL : VerifiableInference.Desc.First.laysNodup arr N links ps = true)
    (hS : (ms.map seatOf).Nodup) :
    ((VerifiableInference.Desc.Sound.mineAt ms N links p).map (numOf arr)).Nodup := by
  have h0 := (Bool.and_eq_true_iff.1 (List.all_eq_true.1 hL p hp)).1
  have hn := nodup_of_eachOnce _ h0
  refine List.Nodup.map_on ?_ ((List.Nodup.of_map _ hS).filter _)
  intro x hx y hy e
  have hx' := List.mem_filter.1 hx
  have hy' := List.mem_filter.1 hy
  have es : seatOf x = seatOf y :=
    List.inj_on_of_nodup_map hn (List.contains_iff_mem.1 hx'.2) (List.contains_iff_mem.1 hy'.2)
      (by
        show (numOf arr x, 0) = (numOf arr y, 0)
        rw [e])
  exact List.inj_on_of_nodup_map hS hx'.1 hy'.1 es

/-! ## 3 What the extractor lays at a member that decodes -/

section
variable (cs : OnBytes.Codes) {Xi A Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → A → Option Cells) (c₀ : Cells)

theorem ext_msg (mine minePad : List Mem) (cellsToo : Bool) (tokNew : Option Tok) (a : A)
    (y : Strs) (w : Wit Cells Tok MsgT) (x : Mem) (hx : x ∈ mine) (M : MsgT)
    (hd : VerifiableInference.Desc.Sound.decAt cs G smp x.1 x.2 a y = some M)
    (hA : VerifiableInference.Desc.Sound.Agree cs G arr smp mine a y (numOf arr x)) :
    (VerifiableInference.Desc.Sound.extAt cs G arr smp decT c₀ mine minePad cellsToo tokNew a y
      w).msg (numOf arr x) = M := by
  show (if numOf arr x ∈ mine.map (numOf arr) then
    VerifiableInference.Desc.Sound.msgAt cs G arr smp mine a y (numOf arr x)
    else w.msg (numOf arr x)) = M
  rw [if_pos (List.mem_map.2 ⟨x, hx, rfl⟩),
    VerifiableInference.Desc.Sound.msgAt_of cs G arr smp mine a y x hx M hd hA]

theorem ext_pad (mine minePad : List Mem) (cellsToo : Bool) (tokNew : Option Tok) (a : A)
    (y : Strs) (w : Wit Cells Tok MsgT) (x : Mem) (hx : x ∈ mine) (M : MsgT)
    (hd : VerifiableInference.Desc.Sound.decAt cs G smp x.1 x.2 a y = some M)
    (hS : VerifiableInference.Desc.Sound.AgreeBy cs G smp seatOf (mine ++ minePad) a y
      (seatOf x)) :
    (VerifiableInference.Desc.Sound.extAt cs G arr smp decT c₀ mine minePad cellsToo tokNew a y
      w).pad (seatOf x).1 (seatOf x).2 = M := by
  show (if ((seatOf x).1, (seatOf x).2) ∈ (mine ++ minePad).map seatOf then
    VerifiableInference.Desc.Sound.padAt cs G smp (mine ++ minePad) a y (seatOf x).1 (seatOf x).2
    else w.pad (seatOf x).1 (seatOf x).2) = M
  rw [if_pos (List.mem_map.2 ⟨x, List.mem_append_left _ hx, rfl⟩)]
  exact VerifiableInference.Desc.Sound.tabBy_of cs G smp seatOf (mine ++ minePad) a y x
    (List.mem_append_left _ hx) M hd hS

end

/-! ## 4 The two readers of a row's words are one at such a member -/

section
variable (cs : OnBytes.Codes) {Cells Tok : Type} (arr : ℕ → ℕ → ℕ)

/-- A witness whose message of a seat's number and whose pad at the seat are one table M has M for
its table at whichever message of the statement sits there. -/
theorem tab_of_comps (seatAt : ℕ → Option (ℕ × ℕ)) (S : OnBytes.Statement)
    (w : Wit Cells Tok MsgT) (q : ℕ × ℕ) (o : ℕ) (X : OnBytes.Oracle) (M : MsgT)
    (hs : seatAt o = some q) (hX : S.oracles[o]? = some X) (h1 : w.msg (arr q.1 q.2) = M)
    (h2 : w.pad q.1 q.2 = M) :
    VerifiableInference.Desc.Sound.tabAt cs arr seatAt S w o = M := by
  unfold VerifiableInference.Desc.Sound.tabAt
  rw [hs, hX]
  funext mask row place
  show (if VerifiableInference.Desc.padB cs X.shape mask row place = true then
      w.pad q.1 q.2 mask row place else w.msg (arr q.1 q.2) mask row place) = _
  rw [h1, h2]
  split <;> rfl

/-- **At a message whose member's two components are laid from the tuple, the words built of the
tuple are the words that the table's reader reads off the witness**: at both tables, at every index.
-/
theorem words_laid (mem : ℕ → Option Mem)
    (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → OnBytes.Part → ℕ → OnBytes.Slice.GE)
    (hrd : ∀ x m part i, rd x m part i = H2K.Pin.tabP cs (x.1.l.get x.2).1 m part i)
    (m : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg) (st : OnBytes.Statement)
    (book : OnBytes.TreeBook) (w : Wit Cells Tok MsgT) (o : ℕ) (x : Mem) (X : OnBytes.Oracle)
    (hm : mem o = some x) (hc : st.codes = cs) (hX : st.oracles[o]? = some X)
    (hsh : X.shape = (x.1.l.get x.2).1)
    (hseat : VerifiableInference.Desc.Sound.seatBy VerifiableInference.Desc.Sound.noFirst book o =
      some (seatOf x))
    (h1 : w.msg (numOf arr x) = toMsgT cs x.1.l x.2 (m x))
    (h2 : w.pad (seatOf x).1 (seatOf x).2 = toMsgT cs x.1.l x.2 (m x)) (part : OnBytes.Part)
    (i : ℕ) :
    _root_.Desc.K14.Law.wordsT cs mem rd m o part i =
      VerifiableInference.Desc.Sound.wordsFirst arr st book w o part i := by
  subst hc
  have eT := tab_of_comps st.codes arr
    (VerifiableInference.Desc.Sound.seatBy VerifiableInference.Desc.Sound.noFirst book) st w
    (seatOf x) o X _ hseat hX h1 h2
  have hb : st.rowBits o part = OnBytes.ceilLog2 ((x.1.l.get x.2).1.rows part) := by
    unfold OnBytes.Statement.rowBits
    rw [hX]
    show OnBytes.ceilLog2 (X.shape.rows part) = _
    rw [hsh]
  have hr : OnBytes.Means.realRows st o part = (x.1.l.get x.2).1.rows part := by
    unfold OnBytes.Means.realRows
    rw [hX]
    show X.shape.rows part = _
    rw [hsh]
  have eL : _root_.Desc.K14.Law.wordsT st.codes mem rd m o part i = rd x (m x) part i := by
    unfold _root_.Desc.K14.Law.wordsT
    rw [hm]
  rw [eL, hrd, ← _root_.Desc.K14.Law.Fence.rdK_tabP]
  unfold VerifiableInference.Desc.Sound.wordsFirst VerifiableInference.Desc.Sound.wordsBy
    OnBytes.Means.wordsOn _root_.Desc.K14.Law.rdK
  rw [hb, hr, eT]

end

/-! ## 5 What is spent of the state in front of the test -/

/-- **What this file spends of the verifier's state in front of the proximity test**, beside the
table's promise. mem: which member of the list the tuple's words read at a message's number. g, G0:
the number of the group under test, and the group. -/
structure Spent (cs : OnBytes.Codes) (ms : List Mem) (N : Numbers) (links : List ModelPart)
    (mem : ℕ → Option Mem) (s : VerifiableInference.Desc.First.S) (g : ℕ) (G0 : OnBytes.Group) :
    Prop where
  /-- the group under test is the one that the table's numbers name behind the last segment -/
  g_eq : g = N.groupAt links.length
  /-- the statement's codes are the plan's -/
  codes : s.st.codes = cs
  /-- the statement is in order -/
  inOrder : OnBytes.Means.InOrder s.st
  /-- no two oracle messages have one place in the book -/
  apart : VerifiableInference.Desc.First.PlacesApart s
  /-- the tree at a place of the book bears that place for its number -/
  numbered : ∀ (z : ℕ) (T : OnBytes.Tree), s.book.trees[z]? = some T → T.number = z
  /-- of each member of the group under test, at the place that the book gives it: the book holds
  the place's tree; mem names a member of the list, which sits at that place and has the message's
  shape -/
  named : ∀ o ∈ G0.members.toList, ∀ q : ℕ × ℕ, s.book.place[o]? = some q →
    q.1 < s.book.trees.size ∧ ∃ (x : Mem) (X : OnBytes.Oracle), mem o = some x ∧ x ∈ ms ∧
      seatOf x = q ∧ s.st.oracles[o]? = some X ∧ X.shape = (x.1.l.get x.2).1

/-- **Where the members of the group under test sit, by the table's promise**: where the promise's
membersHeld holds, a class of rows of segment n and the pin of its moment 0 are open and the pins of
its moments 1 and 2 are not: the members' places in the book are just the tenants of moment 0. -/
theorem members_sit (N : Numbers) (O : List Item) (s : VerifiableInference.Desc.First.S)
    (hM : VerifiableInference.Desc.First.membersHeld N O s = true) (n : ℕ)
    (c : VerifiableInference.Desc.First.RowClass) (hc : Item.row n c ∈ O) (G0 : OnBytes.Group)
    (hG : s.st.groups[N.groupAt n]? = some G0) (h0 : Item.pin n 0 ∈ O) (h1 : Item.pin n 1 ∉ O)
    (h2 : Item.pin n 2 ∉ O) :
    (∀ o ∈ G0.members.toList, ∃ q, s.book.place[o]? = some q ∧ q ∈ N.sent n 0) ∧
      ∀ q ∈ N.sent n 0, ∃ o ∈ G0.members.toList, s.book.place[o]? = some q := by
  have h := List.all_eq_true.1 hM n (VerifiableInference.Desc.First.mem_rowSegs hc)
  rw [hG] at h
  simp only [Bool.and_eq_true, VerifiableInference.Desc.First.sameMembers] at h
  obtain ⟨hs, hab, hba⟩ := h
  refine ⟨fun o ho => ?_, fun q hq => ?_⟩
  · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (List.all_eq_true.1 hs o ho)
    refine ⟨q, hq, ?_⟩
    have h3 := List.contains_iff_mem.1
      (List.all_eq_true.1 hab q (List.mem_filterMap.2 ⟨o, ho, hq⟩))
    obtain ⟨t, ht, hqt⟩ := List.mem_flatMap.1 h3
    have ht' : t = 0 ∨ t = 1 ∨ t = 2 := by
      have := List.mem_range.1 ht
      omega
    rcases ht' with rfl | rfl | rfl
    · split at hqt
      · exact hqt
      · cases hqt
    · rw [if_neg (fun e => h1 (List.contains_iff_mem.1 e))] at hqt
      cases hqt
    · rw [if_neg (fun e => h2 (List.contains_iff_mem.1 e))] at hqt
      cases hqt
  · have h3 : q ∈ (List.range 3).flatMap fun t =>
        if O.contains (Item.pin n t) then N.sent n t else [] := by
      refine List.mem_flatMap.2 ⟨0, List.mem_range.2 (by decide), ?_⟩
      rw [if_pos (List.contains_iff_mem.2 h0)]
      exact hq
    obtain ⟨o, ho, e⟩ :=
      List.mem_filterMap.1 (List.contains_iff_mem.1 (List.all_eq_true.1 hba q h3))
    exact ⟨o, ho, e⟩

/-! ## 6 The tuple gives what the test's row closes, at the table's extractor's witness -/

section
variable (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × VerifiableInference.Desc.First.S → (s : Sending) → (i : Fin s.l.length) →
    Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × VerifiableInference.Desc.First.S → Option Cells)
  (c₀ : Cells) (tokOf : P × VerifiableInference.Desc.First.S → Tok) (N : Numbers)
  (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place) {Fr : Frame}

/-- **FROM ONE TUPLE OF CANDIDATES OF WHICH ALL ROWS THAT THE TEST TAKES IN SAY THEIR CLAIMS, TO
EVERY ITEM THAT THE TEST's ROW CLOSES, AT THE WITNESS THAT THE TABLE's EXTRACTOR GIVES.** -/
theorem witness_core (k : ℕ) (hp : ps[k]? = some pK) (hfit : openFitB links ps k = true)
    (hpin : Mg.pin = VerifiableInference.Desc.Sound.pinJT cs G arr smp ms)
    (hnc : Mg.noColl = VerifiableInference.Desc.Sound.noCollJT cs G smp ms)
    (hrow : Mg.row = VerifiableInference.Desc.First.rowSays N
      (VerifiableInference.Desc.First.wordsAtFirst arr))
    (hGS : VerifiableInference.Desc.Sound.GroupsSeated ms N)
    (hL : VerifiableInference.Desc.First.laysNodup arr N links ps = true)
    (hSeats : (ms.map seatOf).Nodup)
    (mem : ℕ → Option Mem)
    (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → OnBytes.Part → ℕ → OnBytes.Slice.GE)
    (hrd : ∀ x m part i, rd x m part i = H2K.Pin.tabP cs (x.1.l.get x.2).1 m part i)
    (a b : (P × VerifiableInference.Desc.First.S) × Fr.E.Str) (w : Wit Cells Tok MsgT)
    (hon : VerifiableInference.Desc.Sound.onQ N Mg links ps
      (fun x : P × VerifiableInference.Desc.First.S => x) k a)
    (hm : ¬ a.1.2.failed ≠ none) (g : ℕ) (G0 : OnBytes.Group)
    (m : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg) (hG : a.1.2.st.groups[g]? = some G0)
    (hsay : OnBytes.Means.AllSay OnBytes.Model.Reading.gl (OnBytes.Slice.begun a.1.2.st g G0)
      (OnBytes.Slice.runRows a.1.2.st G0).toList (_root_.Desc.K14.Law.wordsT cs mem rd m))
    (cand : ∀ o ∈ G0.members.toList, ∀ x, mem o = some x →
      VerifiableInference.Desc.Sound.CandAt cs G smp x a.1 (strsOf Fr a.2) (m x))
    (hF : Spent cs ms N links mem a.1.2 g G0) :
    VerifiableInference.Desc.Sound.relAt
      (VerifiableInference.Desc.Sound.meansQ N Mg
        (fun x : P × VerifiableInference.Desc.First.S => x))
      (VerifiableInference.Desc.Sound.insQ links ps k) a
      (VerifiableInference.Desc.Sound.extQAt cs G arr smp ms decT c₀ tokOf N links ps
        (fun x : P × VerifiableInference.Desc.First.S => x) k a b w) := by
  have hu : a.1.2.failed = none := not_not.1 hm
  have hN := mine_nodup arr ms N links ps pK (List.mem_of_getElem? hp) hL hSeats
  obtain ⟨hO, hO1, hO2⟩ := openFit_gives links ps k hfit
  -- the promise's three clauses
  have hon' : VerifiableInference.Desc.First.onAt N Mg links ps[k]?
      ((VerifiableInference.Desc.First.openSets links ps
        (VerifiableInference.Desc.First.start links))[k]?.getD [])
      ((VerifiableInference.Desc.First.pubSets Mg.more links ps)[k]?.getD []) a.1
      (strsOf Fr a.2) := hon
  generalize hOdef : (VerifiableInference.Desc.First.openSets links ps
    (VerifiableInference.Desc.First.start links))[k]?.getD [] = O at hO hO1 hO2 hon'
  obtain ⟨-, hor⟩ := hon'
  rcases hor with hbad | ⟨hB, -, hSN, -⟩
  · exact absurd hbad hm
  simp only [Bool.and_eq_true] at hB
  obtain ⟨⟨⟨⟨⟨-, hR⟩, hM⟩, -⟩, -⟩, -⟩ := hB
  have oC : Item.row links.length .carried ∈ O := hO _ (by rw [ins_at]; simp)
  have oS : Item.row links.length (.sample 0) ∈ O := hO _ (by rw [ins_at]; simp)
  have oP : Item.row links.length .position ∈ O := hO _ (by rw [ins_at]; simp)
  have oN : Item.pin links.length 0 ∈ O := hO _ (by rw [ins_at]; simp)
  -- the extractor's witness
  have hpad : VerifiableInference.Desc.Sound.minePadAt ms N links pK = [] := by
    unfold VerifiableInference.Desc.Sound.minePadAt
    rw [laysPads_at]
    exact List.filter_eq_nil_iff.2 fun _ _ => by simp
  obtain ⟨tk, ew⟩ : ∃ tk : Option Tok,
      VerifiableInference.Desc.Sound.extQAt cs G arr smp ms decT c₀ tokOf N links ps
        (fun x : P × VerifiableInference.Desc.First.S => x) k a b w =
      VerifiableInference.Desc.Sound.extAt cs G arr smp decT c₀
        (VerifiableInference.Desc.Sound.mineAt ms N links pK) [] false tk a.1 (strsOf Fr a.2)
        w := by
    refine ⟨if VerifiableInference.Desc.First.laysTok links pK then (some b.1).map tokOf else none,
      ?_⟩
    unfold VerifiableInference.Desc.Sound.extQAt
    rw [hp]
    show VerifiableInference.Desc.Sound.extQ cs G arr smp ms decT c₀ tokOf N links pK a.1
      (strsOf Fr a.2) (some b.1) w = _
    unfold VerifiableInference.Desc.Sound.extQ
    rw [hpad]
  rw [ew]
  have hA := fun n => VerifiableInference.Desc.Sound.agree_of_nodup cs G arr smp
    (VerifiableInference.Desc.Sound.mineAt ms N links pK) hN a.1 (strsOf Fr a.2) n
  have hS : ∀ q, VerifiableInference.Desc.Sound.AgreeBy cs G smp seatOf
      (VerifiableInference.Desc.Sound.mineAt ms N links pK ++ []) a.1 (strsOf Fr a.2) q :=
    fun q => by
      rw [List.append_nil]
      exact VerifiableInference.Desc.Sound.agreeSeat_of_nodup cs G arr smp _ hN a.1
        (strsOf Fr a.2) q
  have inG : ∀ q ∈ N.sent links.length 0, q ∈ N.group links.length := fun q hq =>
    List.mem_append_left _ (List.mem_append_left _ hq)
  have hG' : a.1.2.st.groups[N.groupAt links.length]? = some G0 := hF.g_eq ▸ hG
  obtain ⟨sit1, sit2⟩ := members_sit N O a.1.2 hM links.length .carried oC G0 hG' oN hO1 hO2
  -- a member of the list at a seat whose pin the test closes: one of the row's own; it decodes to
  -- the tuple's message
  have key : ∀ z ∈ ms, seatOf z ∈ N.sent links.length 0 →
      z ∈ VerifiableInference.Desc.Sound.mineAt ms N links pK ∧
      VerifiableInference.Desc.Sound.decAt cs G smp z.1 z.2 a.1 (strsOf Fr a.2) =
        some (toMsgT cs z.1.l z.2 (m z)) := by
    intro z hz hs
    refine ⟨List.mem_filter.2 ⟨hz, ?_⟩, ?_⟩
    · rw [laysSeats_at]
      exact List.contains_iff_mem.2 (inG _ hs)
    · have h1 := (hSN (seatOf z) (List.mem_flatMap.2 ⟨.pin links.length 0, oN, hs⟩)).2
      rw [hnc] at h1
      obtain ⟨o, ho, hq⟩ := sit2 _ hs
      obtain ⟨-, x, -, hmo, hx, ex, -, -⟩ := hF.named o ho _ hq
      obtain rfl : x = z := List.inj_on_of_nodup_map hSeats hx hz ex
      exact VerifiableInference.Desc.Sound.dec_of_cand cs G smp x a.1 (strsOf Fr a.2) (m x)
        (h1 x hz rfl) (cand o ho x hmo)
  -- all rows that the test takes in say their claims of the words that the table's reader gives
  have taken : OnBytes.Means.AllSay OnBytes.Slice.rdE a.1.2.st
      (OnBytes.Slice.runRows a.1.2.st G0).toList
      (VerifiableInference.Desc.Sound.wordsFirst arr a.1.2.st a.1.2.book
        (VerifiableInference.Desc.Sound.extAt cs G arr smp decT c₀
          (VerifiableInference.Desc.Sound.mineAt ms N links pK) [] false tk a.1 (strsOf Fr a.2)
          w)) := by
    refine _root_.Desc.K14.Law.allSay_same OnBytes.Model.Reading.gl a.1.2.st
      (OnBytes.Slice.begun a.1.2.st g G0) (VerifiableInference.Desc.grows_begun _ _ _)
      (H2K.Out.closeLedgers_size _ _) _ _
      (_root_.Desc.K14.Law.Fence.run_agree a.1.2.st (OnBytes.Slice.begun a.1.2.st g G0) hF.inOrder
        (VerifiableInference.Desc.grows_begun _ _ _) g G0 hG _ _ ?_ hsay)
    intro o ho part i
    obtain ⟨q, hq, hqs⟩ := sit1 o ho
    obtain ⟨hlt, x, X, hmo, hx, ex, hX, hsh⟩ := hF.named o ho q hq
    have hT : a.1.2.book.trees[q.1]? = some a.1.2.book.trees[q.1] := Array.getElem?_eq_getElem hlt
    have hseat : VerifiableInference.Desc.Sound.seatBy VerifiableInference.Desc.Sound.noFirst
        a.1.2.book o = some (seatOf x) := by
      rw [VerifiableInference.Desc.Sound.seatBy_some _ a.1.2.book o q _ hq hT, ex]
      show some ((a.1.2.book.trees[q.1]).number, q.2) = some q
      rw [hF.numbered q.1 _ hT]
    obtain ⟨hmine, hd⟩ := key x hx (ex ▸ hqs)
    exact words_laid cs arr mem rd hrd m a.1.2.st a.1.2.book _ o x X hmo hF.codes hX hsh hseat
      (ext_msg cs G arr smp decT c₀ _ [] false tk a.1 (strsOf Fr a.2) w x hmine _ hd (hA _))
      (ext_pad cs G arr smp decT c₀ _ [] false tk a.1 (strsOf Fr a.2) w x hmine _ hd (hS _)) part i
  -- item by item
  intro i hi
  have hi' : i ∈ (VerifiableInference.Desc.First.rowOf links pK).ins ++
      (VerifiableInference.Desc.First.rowOf links pK).ctx ++ [Item.unmarked] := by
    unfold VerifiableInference.Desc.Sound.insQ VerifiableInference.Desc.Sound.rowQ at hi
    rw [hp] at hi
    exact hi
  rw [ins_at, ctx_at] at hi'
  simp only [List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl | rfl
  · show Mg.row links.length .carried a.1 (strsOf Fr a.2) _
    rw [hrow]
    exact fun r hr => taken r (VerifiableInference.Desc.First.listClass_taken N O a.1.2 hR
      links.length .carried rfl oC G0 hG' r hr)
  · show Mg.row links.length (.sample 0) a.1 (strsOf Fr a.2) _
    rw [hrow]
    exact fun r hr => taken r (VerifiableInference.Desc.First.sampleClass_taken N O a.1.2 hM
      hF.apart links.length 0 (by decide) oS oN G0 hG' r hr)
  · show Mg.row links.length .position a.1 (strsOf Fr a.2) _
    rw [hrow]
    exact fun r hr => taken r (VerifiableInference.Desc.First.listClass_taken N O a.1.2 hR
      links.length .position rfl oP G0 hG' r hr)
  · show ∀ q ∈ N.sent links.length 0, Mg.pin q.1 q.2 a.1 (strsOf Fr a.2) _
    intro q hq
    rw [hpin]
    obtain ⟨y, hy, ey⟩ := hGS links.length q (inG q hq)
    refine ⟨⟨y, hy, ey⟩, fun z hz hs => ?_⟩
    have hs' : seatOf z ∈ N.sent links.length 0 := by
      have e : seatOf z = q := hs
      rw [e]
      exact hq
    obtain ⟨hmine, hd⟩ := key z hz hs'
    exact VerifiableInference.Desc.Sound.pin_ext cs G arr smp decT c₀ _ [] false tk a.1
      (strsOf Fr a.2) w z hmine _ hd (hA _) (hS _)
  · exact hu

end

/-! ## 7 The door's statement; the fourth tie's second half -/

/-- What the door enterFinish returns has the state's own statement. -/
theorem enter_st (s : VerifiableInference.Desc.First.S) (t : VerifiableInference.Desc.K12.T12)
    (h : VerifiableInference.Desc.K12.enterFinish s = .ok t) : t.st = s.st := by
  unfold VerifiableInference.Desc.K12.enterFinish at h
  split at h
  · cases h1 : s.noneWaits <;> cases h2 : s.failed.isNone <;>
      simp [h1, h2, VerifiableInference.Desc.need, bind, Except.bind, pure, Except.pure] at h
    rw [← h]
  · cases h

section
variable (cs : OnBytes.Codes) {Xi P Cells Tok Cl : Type} {C : _root_.Run.PQ.CK}
  (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × VerifiableInference.Desc.First.S → (s : Sending) → (i : Fin s.l.length) →
    Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × VerifiableInference.Desc.First.S → Option Cells)
  (c₀ : Cells) (tokOf : P × VerifiableInference.Desc.First.S → Tok) (N : Numbers)
  (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place) {Fr : Frame}

/-- **THE FOURTH TIE's SECOND HALF, AT WHICHEVER NUMBER OF THE LIST THE PLACE pK HAS.** -/
theorem witness_at (k : ℕ) (hp : ps[k]? = some pK) (hfit : openFitB links ps k = true)
    (hpin : Mg.pin = VerifiableInference.Desc.Sound.pinJT cs G arr smp ms)
    (hnc : Mg.noColl = VerifiableInference.Desc.Sound.noCollJT cs G smp ms)
    (hrow : Mg.row = VerifiableInference.Desc.First.rowSays N
      (VerifiableInference.Desc.First.wordsAtFirst arr))
    (hGS : VerifiableInference.Desc.Sound.GroupsSeated ms N)
    (hL : VerifiableInference.Desc.First.laysNodup arr N links ps = true)
    (hSeats : (ms.map seatOf).Nodup)
    (mem : P × VerifiableInference.Desc.First.S → ℕ → Option Mem)
    (Rch : ℕ → (P × VerifiableInference.Desc.First.S) × Fr.E.Str → Prop)
    (q : VerifiableInference.Desc.Sound.Piece C Fr (P × VerifiableInference.Desc.First.S) Cl
      (Wit Cells Tok MsgT))
    (hF : ∀ (a : (P × VerifiableInference.Desc.First.S) × Fr.E.Str)
      (t : VerifiableInference.Desc.K12.T12) (G0 : OnBytes.Group),
      VerifiableInference.Desc.Sound.onQ N Mg links ps
        (fun x : P × VerifiableInference.Desc.First.S => x) k a → Rch k a →
      ¬ a.1.2.failed ≠ none → VerifiableInference.Desc.K12.enterFinish a.1.2 = .ok t →
      t.st.groups[t.g]? = some G0 → Spent cs ms N links (mem a.1) a.1.2 t.g G0) :
    H2K12.T4bAt N Mg links ps Rch k q
      (VerifiableInference.Desc.Sound.extQAt cs G arr smp ms decT c₀ tokOf N links ps
        (fun x : P × VerifiableInference.Desc.First.S => x) k)
      (fun a => H2K12.Tuple354 cs G smp (mem a.1) a.1 (strsOf Fr a.2)) := by
  intro a _ b w hon hr hm _ _ hT
  obtain ⟨t, G0, m, hT⟩ := hT
  have hs := hF a t G0 hon hr hm hT.enter hT.group
  have e := enter_st a.1.2 t hT.enter
  have hG := hT.group
  have hA := hT.allSay
  rw [e] at hG hA
  exact witness_core cs G arr smp ms decT c₀ tokOf N Mg links ps k hp hfit hpin hnc hrow hGS hL
    hSeats (mem a.1) (H2K12.rdTab cs) (fun _ _ _ _ => rfl) a b w hon hm t.g G0 m hG hA hT.cand hs

end

/-! ## 8 The test on the table's lists, at the written lists -/

set_option maxRecDepth 1000000 in
/-- By the kernel, at the written lists, at number 354. -/
theorem openFit_full : openFitB VerifiableInference.Desc.Sound.linksFull
    (VerifiableInference.Desc.First.flatPlacesOf VerifiableInference.Desc.Sound.linksFull true)
    354 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The test can fail: one number earlier, in front of the last switch, the rows are not open yet.
-/
theorem openFit_353 : openFitB VerifiableInference.Desc.Sound.linksFull
    (VerifiableInference.Desc.First.flatPlacesOf VerifiableInference.Desc.Sound.linksFull true)
    353 = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The test can fail: one number later, behind the test, what it has closed is open no more. -/
theorem openFit_355 : openFitB VerifiableInference.Desc.Sound.linksFull
    (VerifiableInference.Desc.First.flatPlacesOf VerifiableInference.Desc.Sound.linksFull true)
    355 = false := by decide +kernel

/-- By the kernel: number 354 of the written list is the place pK. -/
theorem place_full : (VerifiableInference.Desc.First.flatPlacesOf
    VerifiableInference.Desc.Sound.linksFull true)[354]? = some pK := by decide +kernel

end H2K12.Wit354

namespace H2K12

open VerifiableInference.Desc (FileDescription Wit)
open VerifiableInference.Desc.Sound (Mem Sending MsgT seatOf Frame strsOf)
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (Meaning Numbers)

/-- **THE FOURTH TIE's SECOND HALF AT THE WRITTEN LISTS, AT NUMBER 354.** -/
theorem witness_354 (cs : OnBytes.Codes) {Xi P Cells Tok Cl : Type} {C : _root_.Run.PQ.CK}
    (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp : P × VerifiableInference.Desc.First.S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem)
    (decT : (ℕ → Option (ℕ × List UInt64)) → P × VerifiableInference.Desc.First.S → Option Cells)
    (c₀ : Cells) (tokOf : P × VerifiableInference.Desc.First.S → Tok) (N : Numbers)
    (Mg : Meaning P (Wit Cells Tok MsgT)) {Fr : Frame}
    (hpin : Mg.pin = VerifiableInference.Desc.Sound.pinJT cs G arr smp ms)
    (hnc : Mg.noColl = VerifiableInference.Desc.Sound.noCollJT cs G smp ms)
    (hrow : Mg.row = VerifiableInference.Desc.First.rowSays N
      (VerifiableInference.Desc.First.wordsAtFirst arr))
    (hGS : VerifiableInference.Desc.Sound.GroupsSeated ms N)
    (hL : VerifiableInference.Desc.First.laysNodup arr N VerifiableInference.Desc.Sound.linksFull
      (VerifiableInference.Desc.First.flatPlacesOf VerifiableInference.Desc.Sound.linksFull true) =
        true)
    (hSeats : (ms.map seatOf).Nodup)
    (mem : P × VerifiableInference.Desc.First.S → ℕ → Option Mem)
    (Rch : ℕ → (P × VerifiableInference.Desc.First.S) × Fr.E.Str → Prop)
    (q : VerifiableInference.Desc.Sound.Piece C Fr (P × VerifiableInference.Desc.First.S) Cl
      (Wit Cells Tok MsgT))
    (hF : ∀ (a : (P × VerifiableInference.Desc.First.S) × Fr.E.Str)
      (t : VerifiableInference.Desc.K12.T12) (G0 : OnBytes.Group),
      VerifiableInference.Desc.Sound.onQ N Mg VerifiableInference.Desc.Sound.linksFull
        (VerifiableInference.Desc.First.flatPlacesOf VerifiableInference.Desc.Sound.linksFull true)
        (fun x : P × VerifiableInference.Desc.First.S => x) 354 a → Rch 354 a →
      ¬ a.1.2.failed ≠ none → VerifiableInference.Desc.K12.enterFinish a.1.2 = .ok t →
      t.st.groups[t.g]? = some G0 →
      Wit354.Spent cs ms N VerifiableInference.Desc.Sound.linksFull (mem a.1) a.1.2 t.g G0) :
    T4bAt N Mg VerifiableInference.Desc.Sound.linksFull
      (VerifiableInference.Desc.First.flatPlacesOf VerifiableInference.Desc.Sound.linksFull true)
      Rch 354 q
      (VerifiableInference.Desc.Sound.extQAt cs G arr smp ms decT c₀ tokOf N
        VerifiableInference.Desc.Sound.linksFull
        (VerifiableInference.Desc.First.flatPlacesOf VerifiableInference.Desc.Sound.linksFull true)
        (fun x : P × VerifiableInference.Desc.First.S => x) 354)
      (fun a => Tuple354 cs G smp (mem a.1) a.1 (strsOf Fr a.2)) :=
  Wit354.witness_at cs G arr smp ms decT c₀ tokOf N Mg _ _ 354 Wit354.place_full
    Wit354.openFit_full hpin hnc hrow hGS hL hSeats mem Rch q hF

end H2K12

#print axioms H2K12.Wit354.mine_nodup
#print axioms H2K12.Wit354.words_laid
#print axioms H2K12.Wit354.members_sit
#print axioms H2K12.Wit354.witness_core
#print axioms H2K12.Wit354.witness_at
#print axioms H2K12.Wit354.openFit_full
#print axioms H2K12.Wit354.openFit_353
#print axioms H2K12.Wit354.openFit_355
#print axioms H2K12.Wit354.place_full
#print axioms H2K12.witness_354
