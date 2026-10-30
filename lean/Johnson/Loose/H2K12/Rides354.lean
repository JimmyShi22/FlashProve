-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Loose/H2K12/Rides354.lean:
THE LAW OF THE PROXIMITY TEST (the kind K12) ON THE PROOF FILE's FIRST
CHAIN: THE FIFTH TIE of what is owed there (TiedAtR, Johnson/Desc/Sound/ChainOfPromisesR.lean):
every item that is open in front of the test and that its row does not close rides back across the
test, AT THE WITNESS THAT THE TABLE's ONE EXTRACTOR GIVES. Definitions, statements and proofs.

What is said. Three items ride past the test: the stored table's pin (pinW), the pending rows on the
table of weights (pile), the pin of the index masks' message (pinI). Each holds behind the test at a
witness w, since it is open there. In front, at the extractor's value: the extractor lays the
message and the pad of the test's own members alone, and none of the three reads these.
Main names:
  pK              the test's place in the table's list: ⟨1, none, 2, K12⟩.
  ridersB, riders_of   a test on the table's lists at a number k, and what a yes gives, with the
                  table's tests readsOpen (Johnson/Desc/First/Borders.lean) and rowsApart
                  (Johnson/Desc/Sound/SpineList.lean): a rider is one of the three.
  clearB, clear_gives   a test on the table's numbers at k: the row lays neither the cells nor the
                  message or the pad of the index masks' seat.
  agree_across    the reader of the pending rows (rwBook, Johnson/Desc/K13/Law/ReaderByBook.lean)
                  reads one message alike at two states and two witnesses, where the later state
                  keeps the codes, the message's shape and its seat, and the witnesses have the same
                  cells and the same two components at that seat.
  Across          what is spent of the two states at an accept of the test: nine fields.
  rides_at        THE TIE (T5At, H2K12/Frame354.lean) at whichever number k of
                  the list has the place pK.
  riders_full, readsOpen_written, rowsApart_written, place_written   the tests on the lists at the
                  written lists: decided by the kernel. riders_353: the first can fail. (That a test
                  can fail does not show that the premises below can be met.)
  rides_354       the tie at the written lists and number 354: four premises fewer.
By: openIsList, openL_iff_openSets (Johnson/Desc/Sound/SpineList.lean) · extQAt_keeps
(Johnson/Desc/Sound/BordersSides.lean) · pinJT_col (Johnson/Desc/Sound/ReadsTreeAt.lean) · pin_congr
(Johnson/Desc/Sound/World.lean) · holds_congr (Johnson/Desc/K13/Law/Agree.lean) · wordsBy_congr
(Johnson/Desc/Sound/WordsAt.lean) · wordsBy_reads (Johnson/Desc/Sound/WordsMore.lean) · out_strs
(Johnson/Desc/First/Link/Law/OracleRides.lean) · stays_behind
(Johnson/Top/H0/Walk/StaysBehind.lean).
ITS KIN: t5R_of_sides (Johnson/Desc/Sound/BordersSidesOnR.lean) gives the same tie as a rule, from
"no rider reads what a row lays" AT EVERY NUMBER of the list and a clause on every item's reading.
Here its three steps are taken at the one number, under the two tests at that number.
Limits. (1) A JOINING OVER LETTERS: the meaning Mg enters by three named equations (pin, pinW,
pile); the decoder by "it reads the public part alone" (DecBlind,
Johnson/Desc/K13/Law/SigDecodes.lean); Across is a premise, asked inside the promise in front, the
condition Rch, no mark, an accept and the promise behind. IT IS PROVED OF NO PAIR OF STATES HERE.
WHETHER ALL PREMISES CAN BE MET TOGETHER IS SHOWN NOWHERE HERE: where they cannot, the statement is
true and says nothing. (2) clearB and "the index masks' tree is sent in front of the test" are
premises on the table's numbers. (3) The four lines by the kernel are decided at one version of the
written lists. No soundness statement. Nothing on hiding.

-/
import Johnson.Desc.K13.Law.ReaderByBook
import Johnson.Desc.K13.Law.SigDecodes
import Johnson.Desc.Sound.BordersSides
import Johnson.Desc.Sound.WordsMore
import Johnson.Top.H0.Walk.StaysBehind
import Johnson.Desc.First.Link.Law.OracleRides
import Johnson.Desc.Sound.AtDriver
import Johnson.Loose.H2K12.Frame354

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace H2K12.Rid354

open VerifiableInference.Desc (FileDescription Strs Wit Place)
open VerifiableInference.Desc.Sound (Mem Sending MsgT seatOf numOf strsOf)
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers Comp)

/-- The place of the proximity test at the end of the proof file's first chain. -/
abbrev pK : Place := ⟨1, none, 2, .K12⟩

/-! ## 1 Which items ride past the test -/

/-- **A test on the table's lists**: at number k, every item that is open in front of the
sub-protocol is closed or read by the row at pK, is "no mark", or is one of three: the stored
table's pin, the pending rows, the index masks' pin. -/
def ridersB (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  ((VerifiableInference.Desc.First.openSets links ps
      (VerifiableInference.Desc.First.start links))[k]?.getD []).all fun i =>
    ((VerifiableInference.Desc.First.rowOf links pK).ins ++
      (VerifiableInference.Desc.First.rowOf links pK).ctx ++ [Item.unmarked]).contains i ||
      [Item.pinW, Item.pile, Item.pinI].contains i

/-- Where the test passes, with the table's two tests readsOpen and rowsApart: what rides past the
sub-protocol at pK is one of the three. -/
theorem riders_of (links : List ModelPart) (ps : List Place) (k : ℕ) (hp : ps[k]? = some pK)
    (h : ridersB links ps k = true)
    (hro : VerifiableInference.Desc.First.readsOpen links ps
      (VerifiableInference.Desc.First.start links) = true)
    (hra : VerifiableInference.Desc.Sound.rowsApart links ps = true) (i : Item)
    (ho : VerifiableInference.Desc.Sound.openAfter (VerifiableInference.Desc.Sound.insQ links ps)
      (VerifiableInference.Desc.Sound.outsQ links ps)
      (· ∈ VerifiableInference.Desc.First.start links) k i)
    (hn : ¬ VerifiableInference.Desc.Sound.insQ links ps k i) :
    i = .pinW ∨ i = .pile ∨ i = .pinI := by
  have hu : Item.unmarked ∈ VerifiableInference.Desc.First.start links :=
    List.mem_append_left _ List.mem_cons_self
  have hk : k ≤ ps.length := Nat.le_of_lt (List.getElem?_eq_some_iff.1 hp).1
  have hL := (VerifiableInference.Desc.Sound.openIsList Item
    (VerifiableInference.Desc.Sound.insL links ps) (VerifiableInference.Desc.Sound.outsL links ps)
    (VerifiableInference.Desc.First.start links) k i).1 ho
  have hO := (VerifiableInference.Desc.Sound.openL_iff_openSets links ps
    (VerifiableInference.Desc.First.start links) hro hra hu k hk i).1 hL
  rcases Bool.or_eq_true_iff.1 (List.all_eq_true.1 h i hO) with h5 | h5
  · refine absurd ?_ hn
    show i ∈ (VerifiableInference.Desc.Sound.rowQ links ps k).ins ++
      (VerifiableInference.Desc.Sound.rowQ links ps k).ctx ++ [.unmarked]
    unfold VerifiableInference.Desc.Sound.rowQ
    rw [hp]
    exact List.contains_iff_mem.1 h5
  · simpa using List.contains_iff_mem.1 h5

/-- **A test on the table's numbers**: what the row at number k lays is none of the three components
of the witness that the three riders read: the cells, and the message and the pad of the index
masks' seat. -/
def clearB (arr : ℕ → ℕ → ℕ) (N : Numbers) (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  [Comp.cells, Comp.msg (arr N.index.1 N.index.2), Comp.pad N.index.1 N.index.2].all fun c =>
    !(VerifiableInference.Desc.Sound.laysAtQ arr N links ps k).contains c

theorem clear_gives (arr : ℕ → ℕ → ℕ) (N : Numbers) (links : List ModelPart) (ps : List Place) (k : ℕ)
    (h : clearB arr N links ps k = true) (c : Comp)
    (hc : c ∈ [Comp.cells, Comp.msg (arr N.index.1 N.index.2), Comp.pad N.index.1 N.index.2]) :
    c ∉ VerifiableInference.Desc.Sound.laysAtQ arr N links ps k := by
  intro hm
  have h1 := List.all_eq_true.1 h c hc
  rw [List.contains_iff_mem.2 hm] at h1
  exact absurd h1 (by decide)

/-! ## 2 The reader of the pending rows, across the test and past the extractor -/

section
variable {Pp Cells Tok : Type} {nR kk : ℕ} (arr : ℕ → ℕ → ℕ)
  (mat : Cells → Fin nR → (Fin kk → Bool) → OnBytes.Slice.GE)

/-- **Two states of which the later keeps the table of codes, the message's shape and the seat that
the book gives it, and two witnesses with the same cells and the same two components at that seat,
are read alike at that message.** -/
theorem agree_across (xa xb : Pp × VerifiableInference.Desc.First.S) (i₀ : ℕ)
    (w w' : Wit Cells Tok MsgT) (hc : xb.2.st.codes = xa.2.st.codes)
    (hsh : (xb.2.st.oracles[i₀]?).map (·.shape) = (xa.2.st.oracles[i₀]?).map (·.shape))
    (hse : VerifiableInference.Desc.Sound.seatBy VerifiableInference.Desc.Sound.noFirst xb.2.book
      i₀ = VerifiableInference.Desc.Sound.seatBy VerifiableInference.Desc.Sound.noFirst xa.2.book
      i₀)
    (hce : w'.cells = w.cells)
    (hw : ∀ q, VerifiableInference.Desc.Sound.seatBy VerifiableInference.Desc.Sound.noFirst
      xa.2.book i₀ = some q →
      w'.msg (arr q.1 q.2) = w.msg (arr q.1 q.2) ∧ w'.pad q.1 q.2 = w.pad q.1 q.2) :
    VerifiableInference.Desc.K13.Law.AgreeAt i₀
      (VerifiableInference.Desc.K13.Law.rwBook arr mat xb w)
      (VerifiableInference.Desc.K13.Law.rwBook arr mat xa w') := by
  refine ⟨?_, fun i => ?_⟩
  · show mat w.cells = mat w'.cells
    rw [hce]
  · show VerifiableInference.Desc.K13.Law.maskCut xb.2.st
        (VerifiableInference.Desc.Sound.wordsFirst arr xb.2.st xb.2.book w) ⟨i₀, i⟩ =
      VerifiableInference.Desc.K13.Law.maskCut xa.2.st
        (VerifiableInference.Desc.Sound.wordsFirst arr xa.2.st xa.2.book w') ⟨i₀, i⟩
    unfold VerifiableInference.Desc.K13.Law.maskCut
    show (if i < OnBytes.Means.tableSize xb.2.st i₀ .mask then
        VerifiableInference.Desc.Sound.wordsFirst arr xb.2.st xb.2.book w i₀ .mask i else 0) =
      (if i < OnBytes.Means.tableSize xa.2.st i₀ .mask then
        VerifiableInference.Desc.Sound.wordsFirst arr xa.2.st xa.2.book w' i₀ .mask i else 0)
    have e0 : VerifiableInference.Desc.Sound.wordsFirst arr xb.2.st xb.2.book w i₀ .mask i =
        VerifiableInference.Desc.Sound.wordsFirst arr xa.2.st xa.2.book w i₀ .mask i :=
      VerifiableInference.Desc.Sound.wordsBy_congr arr _ _ xa.2.st xb.2.st w i₀ i₀ hc hse hsh .mask
        i
    rw [VerifiableInference.Desc.K13.Law.tableSize_of_shape hc hsh, e0]
    have e : VerifiableInference.Desc.Sound.wordsFirst arr xa.2.st xa.2.book w' i₀ .mask i =
        VerifiableInference.Desc.Sound.wordsFirst arr xa.2.st xa.2.book w i₀ .mask i :=
      VerifiableInference.Desc.Sound.wordsBy_reads arr _ xa.2.st w w' i₀ hw .mask i
    rw [e]

end

/-! ## 3 What an accept of the test leaves -/

/-- **What this file spends of the two states at an accept of the test.** -/
structure Across (cs : OnBytes.Codes) {P : Type} {Fr : VerifiableInference.Desc.Sound.Frame}
    (smp : P × VerifiableInference.Desc.First.S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (N : Numbers)
    (a b : (P × VerifiableInference.Desc.First.S) × Fr.E.Str) : Prop where
  /-- the public part rides -/
  pub : b.1.1 = a.1.1
  /-- the reader of the out-of-domain (OOD) samples answers alike, in front and behind, at the
  members that sit at the index masks' seat -/
  smpI : ∀ z ∈ ms, VerifiableInference.Desc.Sound.SitsAt z N.index.1 N.index.2 →
    smp b.1 z.1 z.2 = smp a.1 z.1 z.2
  /-- the pending rows stay -/
  rows : b.1.2.rows = a.1.2.rows
  /-- so does the number of the index masks' message -/
  idx : b.1.2.out.indexMasks = a.1.2.out.indexMasks
  /-- the pending rows name mask entries of that message alone -/
  onLedger : ∀ r ∈ a.1.2.rows,
    VerifiableInference.Desc.K13.Law.OnLedger a.1.2.out.indexMasks r
  /-- the table of codes stays -/
  codes : b.1.2.st.codes = a.1.2.st.codes
  /-- that message keeps its shape -/
  shape : (b.1.2.st.oracles[a.1.2.out.indexMasks]?).map (·.shape) =
    (a.1.2.st.oracles[a.1.2.out.indexMasks]?).map (·.shape)
  /-- and the seat that the book gives it -/
  seatSame : VerifiableInference.Desc.Sound.seatBy VerifiableInference.Desc.Sound.noFirst
      b.1.2.book a.1.2.out.indexMasks =
    VerifiableInference.Desc.Sound.seatBy VerifiableInference.Desc.Sound.noFirst a.1.2.book
      a.1.2.out.indexMasks
  /-- by the book in front, that message sits at the seat that the table's numbers name -/
  seat : ∀ q, VerifiableInference.Desc.Sound.seatBy VerifiableInference.Desc.Sound.noFirst
    a.1.2.book a.1.2.out.indexMasks = some q → q = N.index

/-! ## 4 The fifth tie -/

section
variable (cs : OnBytes.Codes) {Xi P Cells Tok Cl : Type} {C : _root_.Run.PQ.CK} {nR kk : ℕ}
  (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × VerifiableInference.Desc.First.S → (s : Sending) → (i : Fin s.l.length) →
    Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × VerifiableInference.Desc.First.S → Option Cells)
  (c₀ : Cells) (tokOf : P × VerifiableInference.Desc.First.S → Tok) (N : Numbers)
  (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place)
  {Fr : VerifiableInference.Desc.Sound.Frame}
  (mat : Cells → Fin nR → (Fin kk → Bool) → OnBytes.Slice.GE)

/-- **THE FIFTH TIE, AT WHICHEVER NUMBER OF THE LIST THE PLACE pK HAS**: every item that is open in
front of the test and that its row does not close rides back, at the table's extractor's witness. -/
theorem rides_at (k : ℕ) (hp : ps[k]? = some pK) (hrid : ridersB links ps k = true)
    (hro : VerifiableInference.Desc.First.readsOpen links ps
      (VerifiableInference.Desc.First.start links) = true)
    (hra : VerifiableInference.Desc.Sound.rowsApart links ps = true)
    (hcl : clearB arr N links ps k = true)
    (hpin : Mg.pin = VerifiableInference.Desc.Sound.pinJT cs G arr smp ms)
    (hpinW : Mg.pinW = VerifiableInference.Desc.Sound.pinWOf decT)
    (hpile : Mg.pile = fun x _ w => VerifiableInference.Desc.K13.Law.RowsTrue
      (VerifiableInference.Desc.K13.Law.rwBook arr mat x) x.2 w)
    (hdec : VerifiableInference.Desc.K13.Law.DecBlind decT)
    (Rch : ℕ → (P × VerifiableInference.Desc.First.S) × Fr.E.Str → Prop)
    (q : VerifiableInference.Desc.Sound.Piece C Fr (P × VerifiableInference.Desc.First.S) Cl
      (Wit Cells Tok MsgT))
    (hfen : N.index.1 < q.base)
    (hA : ∀ a τ b, VerifiableInference.Desc.Sound.onQ N Mg links ps
        (fun x : P × VerifiableInference.Desc.First.S => x) k a → Rch k a →
      ¬ a.1.2.failed ≠ none → q.ior.red.out a τ = some b →
      VerifiableInference.Desc.Sound.onQ N Mg links ps
        (fun x : P × VerifiableInference.Desc.First.S => x) (k + 1) b →
      Across cs smp ms N a b) :
    H2K12.T5At N Mg links ps Rch k q
      (VerifiableInference.Desc.Sound.extQAt cs G arr smp ms decT c₀ tokOf N links ps
        (fun x : P × VerifiableInference.Desc.First.S => x) k) := by
  intro a τ b w i hon hr hm hb hon' hall ho hn
  have A := hA a τ b hon hr hm hb hon'
  have hbw := hall i (Or.inl ⟨ho, hn⟩)
  have hst : Johnson.Desc.First.Walk.Tied.Stays q.base (strsOf Fr a.2) (strsOf Fr b.2) := by
    rw [VerifiableInference.Desc.LinkJoin.out_strs hb]
    exact Johnson.Desc.First.Walk.Tied.stays_behind C Fr q.base q.ds a.2 τ
  have keep := fun c hc => VerifiableInference.Desc.Sound.extQAt_keeps cs G arr smp ms decT c₀ tokOf
    N links ps (fun x : P × VerifiableInference.Desc.First.S => x) k a b w c
    (clear_gives arr N links ps k hcl c hc)
  have kC : w.cells = (VerifiableInference.Desc.Sound.extQAt cs G arr smp ms decT c₀ tokOf N links
      ps (fun x : P × VerifiableInference.Desc.First.S => x) k a b w).cells :=
    keep .cells (by simp)
  have kM : w.msg (arr N.index.1 N.index.2) = (VerifiableInference.Desc.Sound.extQAt cs G arr smp
      ms decT c₀ tokOf N links ps (fun x : P × VerifiableInference.Desc.First.S => x) k a b w).msg
      (arr N.index.1 N.index.2) := keep (.msg _) (by simp)
  have kP : w.pad N.index.1 N.index.2 = (VerifiableInference.Desc.Sound.extQAt cs G arr smp ms decT
      c₀ tokOf N links ps (fun x : P × VerifiableInference.Desc.First.S => x) k a b w).pad
      N.index.1 N.index.2 := keep (.pad _ _) (by simp)
  rcases riders_of links ps k hp hrid hro hra i ho hn with rfl | rfl | rfl
  · -- the stored table's pin
    have h1 : Mg.pinW b.1 (strsOf Fr b.2) w := hbw
    show Mg.pinW a.1 (strsOf Fr a.2) _
    rw [hpinW] at h1 ⊢
    unfold VerifiableInference.Desc.Sound.pinWOf at h1 ⊢
    have ec : (strsOf Fr b.2).cell = (strsOf Fr a.2).cell := funext hst.1
    have eb : b.1 = (a.1.1, b.1.2) := by rw [← A.pub]
    rw [ec, eb, hdec (strsOf Fr a.2).cell a.1.1 a.1.2 b.1.2] at h1
    rw [← kC]
    exact h1
  · -- the pending rows
    have h1 : Mg.pile b.1 (strsOf Fr b.2) w := hbw
    show Mg.pile a.1 (strsOf Fr a.2) _
    rw [hpile] at h1 ⊢
    intro r hr'
    have hrb : r ∈ b.1.2.rows := by rw [A.rows]; exact hr'
    refine (VerifiableInference.Desc.K13.Law.holds_congr VerifiableInference.Desc.K13.Law.ρg
      (A.onLedger r hr') (agree_across arr mat a.1 b.1 a.1.2.out.indexMasks w _ A.codes A.shape
        A.seatSame kC.symm fun q' hq' => ?_)).1 (h1 r hrb)
    rw [A.seat q' hq']
    exact ⟨kM.symm, kP.symm⟩
  · -- the index masks' pin
    have h1 : Mg.pin N.index.1 N.index.2 b.1 (strsOf Fr b.2) w := hbw
    show Mg.pin N.index.1 N.index.2 a.1 (strsOf Fr a.2) _
    rw [hpin] at h1 ⊢
    have h2 := VerifiableInference.Desc.Sound.pinJT_col cs G arr smp ms N.index.1 N.index.2 b.1
      (strsOf Fr b.2) (strsOf Fr a.2) w (fun x => (hst.2 N.index.1 x hfen).symm) h1
    refine ⟨h2.1, fun z hz hs => ?_⟩
    obtain ⟨v, hv, h3, h4⟩ := h2.2 z hz hs
    have es : z.1.seat z.2 = (N.index.1, N.index.2) := hs
    refine VerifiableInference.Desc.Sound.pin_congr cs G arr smp z.1 z.2 a.1 (strsOf Fr a.2) w _ ?_
      ?_ ⟨v, ?_, h3, h4⟩
    · rw [es]
      exact kM.symm
    · rw [es]
      exact kP.symm
    · show smp a.1 z.1 z.2 = some v
      rw [← A.smpI z hz hs]
      exact hv

end

/-! ## 5 The tests on the table's lists, at the written lists -/

set_option maxRecDepth 1000000 in
/-- By the kernel, at the written lists, at number 354. -/
theorem riders_full : ridersB VerifiableInference.Desc.Sound.linksFull
    (VerifiableInference.Desc.First.flatPlacesOf VerifiableInference.Desc.Sound.linksFull true)
    354 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The test can fail: one number earlier two more items are open: the claim that the last segment
hands on, and the pins of the messages that are kept. -/
theorem riders_353 : ridersB VerifiableInference.Desc.Sound.linksFull
    (VerifiableInference.Desc.First.flatPlacesOf VerifiableInference.Desc.Sound.linksFull true)
    353 = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- By the kernel: the table's test readsOpen at the written lists. -/
theorem readsOpen_written : VerifiableInference.Desc.First.readsOpen
    VerifiableInference.Desc.Sound.linksFull
    (VerifiableInference.Desc.First.flatPlacesOf VerifiableInference.Desc.Sound.linksFull true)
    (VerifiableInference.Desc.First.start VerifiableInference.Desc.Sound.linksFull) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- By the kernel: the table's test rowsApart at the written lists. -/
theorem rowsApart_written : VerifiableInference.Desc.Sound.rowsApart
    VerifiableInference.Desc.Sound.linksFull
    (VerifiableInference.Desc.First.flatPlacesOf VerifiableInference.Desc.Sound.linksFull true) =
    true := by decide +kernel

/-- By the kernel: number 354 of the written list is the place pK. -/
theorem place_written : (VerifiableInference.Desc.First.flatPlacesOf
    VerifiableInference.Desc.Sound.linksFull true)[354]? = some pK := by decide +kernel

end H2K12.Rid354

namespace H2K12

open VerifiableInference.Desc (FileDescription Wit)
open VerifiableInference.Desc.Sound (Mem Sending MsgT)
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (Meaning Numbers)

/-- **THE FIFTH TIE AT THE WRITTEN LISTS, AT NUMBER 354.** -/
theorem rides_354 (cs : OnBytes.Codes) {Xi P Cells Tok Cl : Type} {C : _root_.Run.PQ.CK}
    {nR kk : ℕ} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp : P × VerifiableInference.Desc.First.S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem)
    (decT : (ℕ → Option (ℕ × List UInt64)) → P × VerifiableInference.Desc.First.S → Option Cells)
    (c₀ : Cells) (tokOf : P × VerifiableInference.Desc.First.S → Tok) (N : Numbers)
    (Mg : Meaning P (Wit Cells Tok MsgT)) {Fr : VerifiableInference.Desc.Sound.Frame}
    (mat : Cells → Fin nR → (Fin kk → Bool) → OnBytes.Slice.GE)
    (hcl : Rid354.clearB arr N VerifiableInference.Desc.Sound.linksFull
      (VerifiableInference.Desc.First.flatPlacesOf VerifiableInference.Desc.Sound.linksFull true)
      354 = true)
    (hpin : Mg.pin = VerifiableInference.Desc.Sound.pinJT cs G arr smp ms)
    (hpinW : Mg.pinW = VerifiableInference.Desc.Sound.pinWOf decT)
    (hpile : Mg.pile = fun x _ w => VerifiableInference.Desc.K13.Law.RowsTrue
      (VerifiableInference.Desc.K13.Law.rwBook arr mat x) x.2 w)
    (hdec : VerifiableInference.Desc.K13.Law.DecBlind decT)
    (Rch : ℕ → (P × VerifiableInference.Desc.First.S) × Fr.E.Str → Prop)
    (q : VerifiableInference.Desc.Sound.Piece C Fr (P × VerifiableInference.Desc.First.S) Cl
      (Wit Cells Tok MsgT))
    (hfen : N.index.1 < q.base)
    (hA : ∀ a τ b, VerifiableInference.Desc.Sound.onQ N Mg
        VerifiableInference.Desc.Sound.linksFull
        (VerifiableInference.Desc.First.flatPlacesOf VerifiableInference.Desc.Sound.linksFull true)
        (fun x : P × VerifiableInference.Desc.First.S => x) 354 a → Rch 354 a →
      ¬ a.1.2.failed ≠ none → q.ior.red.out a τ = some b →
      VerifiableInference.Desc.Sound.onQ N Mg VerifiableInference.Desc.Sound.linksFull
        (VerifiableInference.Desc.First.flatPlacesOf VerifiableInference.Desc.Sound.linksFull true)
        (fun x : P × VerifiableInference.Desc.First.S => x) (354 + 1) b →
      Rid354.Across cs smp ms N a b) :
    T5At N Mg VerifiableInference.Desc.Sound.linksFull
      (VerifiableInference.Desc.First.flatPlacesOf VerifiableInference.Desc.Sound.linksFull true)
      Rch 354 q
      (VerifiableInference.Desc.Sound.extQAt cs G arr smp ms decT c₀ tokOf N
        VerifiableInference.Desc.Sound.linksFull
        (VerifiableInference.Desc.First.flatPlacesOf VerifiableInference.Desc.Sound.linksFull true)
        (fun x : P × VerifiableInference.Desc.First.S => x) 354) :=
  Rid354.rides_at cs G arr smp ms decT c₀ tokOf N Mg _ _ mat 354 Rid354.place_written
    Rid354.riders_full Rid354.readsOpen_written Rid354.rowsApart_written hcl hpin hpinW hpile hdec
    Rch q hfen hA

end H2K12

#print axioms H2K12.Rid354.riders_of
#print axioms H2K12.Rid354.agree_across
#print axioms H2K12.Rid354.rides_at
#print axioms H2K12.Rid354.riders_full
#print axioms H2K12.Rid354.riders_353
#print axioms H2K12.Rid354.readsOpen_written
#print axioms H2K12.Rid354.rowsApart_written
#print axioms H2K12.Rid354.place_written
#print axioms H2K12.rides_354
