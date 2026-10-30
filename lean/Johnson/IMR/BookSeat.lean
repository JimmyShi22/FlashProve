-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/BookSeat.lean: orderedP (AS MANY ROOTS AS TREES; TREE z BEARS THE NUMBER z) AT THE
PROOF FILE's SEAT: THE CARRIER's WALK, GENERAL IN A SENTENCE P ON THE BOOK OF TREES AND THE COUNT OF
ROOTS: if P holds of an empty book with no root, then behind a yes of the file's decision it holds
of the first chain's LAST record's book and count.

THE RELATION: PR P := ByC (fun a b => P a.book a.roots → P b.book b.roots) coreS
  (Johnson/Desc/CoreKeeps.lean: ByC; Johnson/Desc/K1/KeepsAtSCore.lean: coreS).
WHAT IS ASKED OF P: structure BookLaw P:
  recv: the plain ground's receiving AT THE FIRST TREE's NUMBER 0 hands P on;
  same: P rides over a book with the same numbers, sources, shapes and parts (K2.SameNumbers,
    Johnson/Top/H0/Tw/K2C/BookKept.lean: the code switch counts at how many lists a tree is opened);
  k12: kind K12's block at the first chain's last test, AT THE NUMBERS THAT THE MAKER LAYS THERE AND
    WHERE IT PASSES ITS OWN TEST ON THE PLAN, hands P on. IT RECEIVES TREES OF ITS OWN.
WHO PAYS THE WALK:
  the sendings (K1's two; W's, under K13's atM4) and K13's atM3: the library's walk over the three
    (RelCore.firstAtS_keeps, commitAtS_keeps, sendAtS_keeps; K13.RelCore.atM3_keeps, atM4_keeps) at
    coreRecv_sentence: through Johnson/Goal/Meaning/CoreSeated.lean.
  the frames, K9's, K10's and every Quiet maker: they leave the book and the count: CoreSeated.lean.
  kind K2: BookKept.lean's yes_hands (general in P) and its four quiet steps' laws.
  the start: an empty book and no root, at every request: start_empty.
TOPS: seatKeeps_sentence, seatBack_sentence, descPure_sentence; descPure_sentenceAt: the same of
  every record that the first chain's fold passes through.
TWO SENTENCES:
  numberedP: Book.NumberedC 0 (Johnson/Desc/Book/BookNumbersCore.lean), written on book and count:
    recv by Book.recvP_numbered, same by numbered_sameNumbers: descPure_numbered, UNDER k12 AT IT.
  orderedP (as many roots as trees; the tree at place z bears the
    number z):
    same by BookKept.lean's ordered_same: descPure_ordered, UNDER recv AND k12 AT IT.
OBJECT: ProofFile.onlineDescription's value, at every o.
coreRecv_sentence IS GENERAL IN P: Book.coreRecv_numbered 0 is its instance at numberedP.
Not claimed: that the count of roots is what the plan's declared rounds hold. No soundness.
-/
import Johnson.IMR.RecRun
import Johnson.Goal.Meaning.CoreSeated
import Johnson.Desc.Book.BookNumbersCore
import Johnson.Top.H0.Tw.K2C.BookKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Ground (Core ByC CoreStill CoreRecv coreStill_same)
open VerifiableInference.Desc.K1.RelCore (coreS)
open ProofFile (Pub)

variable {P : TreeBook → Nat → Prop}

/-- **The relation**: if the sentence holds in front, it holds behind. -/
abbrev PR (P : TreeBook → Nat → Prop) : S → S → Prop :=
  ByC (fun a b => P a.book a.roots → P b.book b.roots) coreS

theorem pr_same (a b : Core) (h1 : b.book = a.book) (h2 : b.roots = a.roots) :
    P a.book a.roots → P b.book b.roots := by
  rw [h1, h2]
  exact id

theorem pr_fn {f : S → Except String S}
    (h : ∀ s t, f s = .ok t → t.book = s.book ∧ t.roots = s.roots) : Fn (PR P) f :=
  fun s t k => pr_same _ _ (h s t k).1 (h s t k).2

/-- **WHAT IS ASKED OF THE SENTENCE.** -/
structure BookLaw (P : TreeBook → Nat → Prop) : Prop where
  recv : ∀ {L : Type} (d d' : _root_.Desc.Plain.DState L) (sent : Array OracleNotice)
    (ids : Array Nat), Ground.recvP 0 d sent = some (ids, d') → P d.book d.roots →
    P d'.book d'.roots
  same : ∀ (A B : TreeBook) (r : Nat), K2.SameNumbers A B → P A r → P B r
  /-- AT THE SEAT's OWN NUMBERS ALONE, AND UNDER THE BLOCK's OWN TEST ON THE PLAN -/
  k12 : ∀ (m : Johnson.G.OfPlan.Made) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))), (K12.atFinish (H2U.p12OfMade m)).planOk = true →
    (K12.atFinish (H2U.p12OfMade m)).decide s rs gs = .ok s' → P s.book s.roots →
    P s'.book s'.roots

/-- The library's frame for a chain that receives all its trees, at the sentence. -/
theorem coreRecv_sentence
    (hrecv : ∀ {L : Type} (d d' : _root_.Desc.Plain.DState L) (sent : Array OracleNotice)
      (ids : Array Nat), Ground.recvP 0 d sent = some (ids, d') → P d.book d.roots →
      P d'.book d'.roots) :
    CoreRecv 0 fun a b => P a.book a.roots → P b.book b.roots where
  refl := fun _ => id
  trans := fun h k x => k (h x)
  newGroup := fun d d' c m n h =>
    pr_same _ _ (coreStill_same.newGroup d d' c m n h).1 (coreStill_same.newGroup d d' c m n h).2
  admit := fun d d' o r h =>
    pr_same _ _ (coreStill_same.admit d d' o r h).1 (coreStill_same.admit d d' o r h).2
  join := fun d d' g o k h =>
    pr_same _ _ (coreStill_same.join d d' g o k h).1 (coreStill_same.join d d' g o k h).2
  addRow := fun d d' g r h =>
    pr_same _ _ (coreStill_same.addRow d d' g r h).1 (coreStill_same.addRow d d' g r h).2
  takeMask := fun d d' o n h =>
    pr_same _ _ (coreStill_same.takeMask d d' o n h).1 (coreStill_same.takeMask d d' o n h).2
  closeLedger := fun d d' o h =>
    pr_same _ _ (coreStill_same.closeLedger d d' o h).1 (coreStill_same.closeLedger d d' o h).2
  spendAsMask := fun d d' o h =>
    pr_same _ _ (coreStill_same.spendAsMask d d' o h).1 (coreStill_same.spendAsMask d d' o h).2
  elsewhere := fun d d' m o t h =>
    pr_same _ _ (coreStill_same.elsewhere d d' m o t h).1
      (coreStill_same.elsewhere d d' m o t h).2
  recv := fun d d' sent ids h => hrecv d d' sent ids h

/-! ## The seat -/

theorem k2_sentence (H : BookLaw P) (p : K2.P2) (h0 : p.firstTree = 0) :
    Whole (PR P) (K2.codeSwitchKind p : Block S Unit) :=
  ⟨fun _ _ _ _ h hN => K2.yes_hands (P := P)
      (fun d d₁ sent ids e k => H.recv d d₁ sent ids (h0 ▸ e) k) H.same h hN,
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

theorem seatKeeps_sentence (H : BookLaw P) : SeatKeeps (PR P) where
  refl := fun _ => id
  trans := fun _ _ _ h k x => k (h x)
  frames := fun _ h => framesOf_core pr_same h
  k1First := fun q gp h0 => firstAtS_core (coreRecv_sentence H.recv) q gp h0
  k1Later := fun q gp l p m a h0 => laterAt_core (coreRecv_sentence H.recv) q gp l p m a h0
  reads := fun h => whole_core pr_same (readsQuietAt_quiet h)
  k3 := fun c r X cs sh a _ h => whole_core pr_same (theStated_quiet c r X cs sh a h)
  k4 := fun p => whole_core pr_same (blockAtC_quiet p)
  k5 := fun W l g bf _ h => whole_core pr_same (k5AtN_quiet W l g bf h)
  k6 := fun h => whole_core pr_same (seatedClaims_quiet h)
  k7 := fun W l => whole_core pr_same (k7Of_quiet W l)
  k8 := fun p => whole_core pr_same (k8Whole_quiet p)
  closeOf := closeOf_core pr_same
  batch := fun p _ hcl => batch_core pr_same (fun h k x => k (h x)) p hcl
  k11 := fun Q => whole_core pr_same (headMerge11_quiet Q)
  k2 := k2_sentence H
  front := fun _ => pr_fn fun _ _ h => K2.headFrontQ_book h
  openQ := fun _ _ => pr_fn fun _ _ h => K2.headOpenQ_book h
  finFront := pr_fn fun _ _ h => K2.finishFrontQ_book h
  finBehind := pr_fn fun _ _ h => K2.finishBehindQ_book h

theorem seatBack_sentence (H : BookLaw P) : SeatBack (PR P) where
  k12 := fun m hp => ⟨fun s rs gs s' h => H.k12 m s s' rs gs hp h, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩
  k13M3 := fun p => atM3_core (coreRecv_sentence H.recv).toCoreStill p
  k13M4 := fun p Q h0 => atM4_core (coreRecv_sentence H.recv) p Q h0

/-! ## The start -/

/-- **The first record holds an empty book and no root, at every request.** -/
theorem start_empty {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (p : ProofFile.InstPub) :
    (ProofFile.startS Z p).book = { trees := #[], place := #[] } ∧ (ProofFile.startS Z p).roots = 0 := by
  have e : Z.s₀.book = { trees := #[], place := #[] } ∧ Z.s₀.roots = 0 := by
    have k := pub_start h
    unfold S.startP at k
    split at k
    · rw [← Option.some.inj k]
      exact ⟨rfl, rfl⟩
    · cases k
  unfold ProofFile.startS
  dsimp only
  split
  · exact e
  · exact ⟨rfl, rfl⟩

/-! ## The row -/

/-- **A YES OF THE FILE's DECISION: THE SENTENCE HOLDS OF THE FIRST CHAIN's LAST RECORD.** -/
theorem descPure_sentence (H : BookLaw P) (h0 : P { trees := #[], place := #[] } 0)
    {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) {x : ProofFile.Inst} {v₁ v₂ v₃ : Fmt.View}
    (hr : F.run x v₁ v₂ v₃ = true) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl) (e₁ : S),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      chainAt "the first chain" 0 c.blocksInOrder (ProofFile.startS Z x.pub) (withEmptySealRound v₁) = .ok e₁ ∧
      P e₁.book e₁.roots := by
  obtain ⟨Z, A, B, c, e₁, hZ, e, j, k⟩ :=
    descPure_end (seatKeeps_sentence H) (seatBack_sentence H) (fun _ _ => trivial) h hr
  refine ⟨Z, A, B, c, e₁, hZ, e, j, k ?_⟩
  show P (ProofFile.startS Z x.pub).book (ProofFile.startS Z x.pub).roots
  rw [(start_empty hZ x.pub).1, (start_empty hZ x.pub).2]
  exact h0

/-- **AND OF EVERY RECORD THAT THE FIRST CHAIN's FOLD PASSES THROUGH.** -/
theorem descPure_sentenceAt (H : BookLaw P) (h0 : P { trees := #[], place := #[] } 0)
    {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) {x : ProofFile.Inst} {v₁ v₂ v₃ : Fmt.View}
    (hr : F.run x v₁ v₂ v₃ = true) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      ∀ (l₁ l₂ : List (Block S ProofFile.Cl)) (t : S) (rs : List Fmt.RoundView)
        (cols : List VerifiableInference.Desc.OpenedColumn), c.blocksInOrder = l₁ ++ l₂ →
        foldBlocks 0 l₁ (ProofFile.startS Z x.pub) (withEmptySealRound v₁).rounds (withEmptySealRound v₁).opened =
          .ok (t, rs, cols) → P t.book t.roots := by
  obtain ⟨Z, A, B, c, e₁, hZ, e, -, k⟩ :=
    descPure_passes (seatKeeps_sentence H) (seatBack_sentence H) (fun _ _ => trivial) h hr
  refine ⟨Z, A, B, c, hZ, e, fun l₁ l₂ t rs cols hl hf => (k t ⟨l₁, l₂, rs, cols, hl, hf⟩).1 ?_⟩
  show P (ProofFile.startS Z x.pub).book (ProofFile.startS Z x.pub).roots
  rw [(start_empty hZ x.pub).1, (start_empty hZ x.pub).2]
  exact h0

/-! ## Two sentences -/

/-- Book.NumberedC 0, written on the book and the count. -/
def numberedP (B : TreeBook) (r : Nat) : Prop :=
  r = B.trees.size ∧
    ∀ (j : Nat) (t : Tree), B.trees[j]? = some t → t.number = 0 + j ∧ t.src = .own j

theorem numberedP_iff (T : Core) : Book.NumberedC 0 T ↔ numberedP T.book T.roots := Iff.rfl

theorem numbered_sameNumbers (A B : TreeBook) (r : Nat) (h : K2.SameNumbers A B)
    (k : numberedP A r) : numberedP B r := by
  refine ⟨k.1.trans h.1.symm, fun j t ht => ?_⟩
  obtain ⟨T₀, h₀, e, f, -⟩ := h.2.2 j t ht
  rw [e, f]
  exact k.2 j T₀ h₀

theorem empty_numbered : numberedP { trees := #[], place := #[] } 0 :=
  ⟨rfl, fun _ _ ht => absurd (Array.getElem?_eq_some_iff.1 ht).1 (Nat.not_lt_zero _)⟩

/-- **The sentence Book.NumberedC 0, with the trees' sources: UNDER KIND K12's SHARE AT IT.** -/
theorem descPure_numbered
    (k12 : ∀ (m : Johnson.G.OfPlan.Made) (s s' : S) (rs : List Fmt.RoundView)
      (gs : List (List (Nat × List UInt64))), (K12.atFinish (H2U.p12OfMade m)).planOk = true →
      (K12.atFinish (H2U.p12OfMade m)).decide s rs gs = .ok s' → numberedP s.book s.roots →
      numberedP s'.book s'.roots)
    {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) {x : ProofFile.Inst} {v₁ v₂ v₃ : Fmt.View}
    (hr : F.run x v₁ v₂ v₃ = true) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl) (e₁ : S),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      chainAt "the first chain" 0 c.blocksInOrder (ProofFile.startS Z x.pub) (withEmptySealRound v₁) = .ok e₁ ∧
      Book.NumberedC 0 (coreS e₁) :=
  descPure_sentence (P := numberedP)
    ⟨fun d d' sent ids e k => Book.recvP_numbered 0 d d' sent ids e k, numbered_sameNumbers, k12⟩
    empty_numbered h hr

/-- The row's own form: as many roots as trees; the tree at place z bears the number z. -/
def orderedP (B : TreeBook) (r : Nat) : Prop :=
  r = B.trees.size ∧ ∀ (z : Nat) (T : Tree), B.trees[z]? = some T → T.number = 0 + z

theorem empty_ordered : orderedP { trees := #[], place := #[] } 0 :=
  ⟨rfl, fun _ _ ht => absurd (Array.getElem?_eq_some_iff.1 ht).1 (Nat.not_lt_zero _)⟩

/-- **The row's own form: UNDER THE RECEIVING's AND KIND K12's SHARES AT IT.** -/
theorem descPure_ordered
    (recv : ∀ {L : Type} (d d' : _root_.Desc.Plain.DState L) (sent : Array OracleNotice)
      (ids : Array Nat), Ground.recvP 0 d sent = some (ids, d') → orderedP d.book d.roots →
      orderedP d'.book d'.roots)
    (k12 : ∀ (m : Johnson.G.OfPlan.Made) (s s' : S) (rs : List Fmt.RoundView)
      (gs : List (List (Nat × List UInt64))), (K12.atFinish (H2U.p12OfMade m)).planOk = true →
      (K12.atFinish (H2U.p12OfMade m)).decide s rs gs = .ok s' → orderedP s.book s.roots →
      orderedP s'.book s'.roots)
    {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) {x : ProofFile.Inst} {v₁ v₂ v₃ : Fmt.View}
    (hr : F.run x v₁ v₂ v₃ = true) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl) (e₁ : S),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      chainAt "the first chain" 0 c.blocksInOrder (ProofFile.startS Z x.pub) (withEmptySealRound v₁) = .ok e₁ ∧
      e₁.roots = e₁.book.trees.size ∧
      ∀ (z : Nat) (T : Tree), e₁.book.trees[z]? = some T → T.number = z := by
  obtain ⟨Z, A, B, c, e₁, a1, a2, a3, n1, n2⟩ := descPure_sentence (P := orderedP)
    ⟨recv, fun A B r hs k => K2.ordered_same 0 A B r hs k, k12⟩ empty_ordered h hr
  refine ⟨Z, A, B, c, e₁, a1, a2, a3, n1, fun z T hT => ?_⟩
  have := n2 z T hT
  rwa [Nat.zero_add] at this

/-- A control: the sentence is not true of every book: a tree that bears another number. -/
theorem not_ordered_skipped (s : TreeShape) :
    ¬ orderedP { trees := #[{ shape := s, number := 1 }], place := #[] } 1 := fun h =>
  Nat.one_ne_zero (h.2 0 { shape := s, number := 1 } rfl)

#print axioms seatKeeps_sentence
#print axioms seatBack_sentence
#print axioms start_empty
#print axioms descPure_sentence
#print axioms descPure_sentenceAt
#print axioms descPure_numbered
#print axioms descPure_ordered
#print axioms not_ordered_skipped

end Meaning.K2
