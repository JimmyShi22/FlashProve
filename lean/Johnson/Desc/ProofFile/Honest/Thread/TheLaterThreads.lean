-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/TheLaterThreads.lean: the two later chains' threads at values.
TheFirstThread.lean gives sharedThread and lastThread over structures of fields. In the shared
chain's the witness is a pair, the first chain's kind of witness and K14's family of words, read by
the lens on the second component. K14's maker lays every item that the shared thread reads but the
stored table's pin, which says nothing here: so the first component and the fields of onFirst are
read by no clause of this thread. The form says nothing at borders 0, 1, 10 and 11 and «ended» at
12: whoever proves those members takes what they need from the state's own make or from a rider.
What is left in sharedParts: the tables, the number at which each is fixed, the riders, keeps
outside K14's members, and the witness's first component.

What these values do not give. K14's laws at sharedParts stand under premises on the run's input and
on reads: the columns, the table, the key, the seeds and the answers at that input. The input's key
being the committer's make is not said here; the top statement has to bring it.

  WtShared         the pair
  MeaningS.onFirst  a meaning read at the first component, the pin of the stored table said by nothing
  LaterLetters     what is left
  sharedParts      the structure of fields at these values
  enters_sharedParts   the shared thread holds at the start that ready gives, where no rider begins
                   at border 0
  lastWords        K14's words, read off the second chain's witness
  LastLetters, lastParts   the same for the second chain
  lastEnds         the value of the letter ends, by endsBy
  tiedRider, lastRiders, lastKeeps   values for the riders and keeps of the second chain
  FirstTreesAreOneNumber, SampledReadOneTable   two sentences that whoever shows the items dot and
                   pinO owes; stated here, proved nowhere here
-/
import Johnson.Desc.ProofFile.Honest.Thread.EntersFirst
import Johnson.Desc.ProofFile.Honest.K14.DoorRider
import Johnson.Desc.ProofFile.Honest.K14.DotAtLastStart
import Johnson.Desc.ProofFile.Honest.K14.EvAtLastStart
import Johnson.Desc.ProofFile.Honest.K14.MeaningReads
import Johnson.Desc.ProofFile.Honest.K14.TiedAhead
import Johnson.Desc.ProofFile.Honest.Thread.OneState

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (Msg2 MeaningS)
open P5J (TS)

variable {W₀ Rc Tr X₀ X : Type}

/-- The shared chain's witness: the first chain's kind of witness, and K14's family of words. -/
abbrev WtShared : Type := WtF × OnBytes.Means.Words Cb.Gl.E

/-- **A meaning read at the first component.** Every item reads the first component of the pair; the
stored table's pin says nothing: K14 reads nothing of it, and the honest side's decoder of the stored
table is a constant. -/
def onFirst {S P W V : Type} (M : MeaningS S P W) : MeaningS S P (W × V) where
  pin := fun j t s y w => M.pin j t s y w.1
  pinT := fun _ _ _ => True
  pin₁ := fun j t p y w => M.pin₁ j t p y w.1
  nearU := fun s y w => M.nearU s y w.1
  recRow := fun s w => M.recRow s w.1
  omU := fun s w => M.omU s w.1
  row := fun c s w => M.row c s w.1
  claimM := fun p y w => M.claimM p y w.1
  dot := fun p s y w => M.dot p s y w.1
  ev := fun p y w => M.ev p y w.1
  unmarked1 := M.unmarked1

/-- **What the shared chain's thread still takes**: the witness's first component, the trees' tables,
the number at which each is fixed, the riders, and what a step keeps outside K14's members. -/
structure LaterLetters (A : OnlineProverWithDescription W₀ Rc Tr X₀ X) where
  rest : Coins A.B → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn → WtShared
  table : Fmt.TreeSource → Coins A.B → Common W₀ Rc OnBytes.TableKey → List Fmt.Drawn → Place × Table
  fixed : Fmt.TreeSource → Nat
  riders : List (RiderCl (Common W₀ Rc OnBytes.TableKey) Desc.K14.St)
  keeps : Place → Desc.K14.St → Desc.K14.St → Prop

/-- **The shared thread's fields at these values.** -/
def sharedParts {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : HeadAtReturn files A)
    (L : LaterLetters A) : SharedThreadParts A WtShared where
  lens := ProofFile.Honest.K14.WitLens.snd WtF
  meaning := fun _ => onFirst h.sharedMeaning
  shape := fun _ _ => true
  rest := L.rest
  table := L.table
  fixed := L.fixed
  rides := ridersOf L.riders
  keeps := L.keeps

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  {h : HeadAtReturn files A} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst}
  {k : Coins A.B} {R : Ready W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X}

/-- **The shared thread holds at the start that ready gives**, where no rider begins at border 0. -/
theorem enters_sharedParts {reads : IndexReaders W₀ Rc} {L : LaterLetters A}
    (hR : ready h.description A.B A.H w₀ rc x k = .ok R)
    (late : ∀ c ∈ L.riders, 0 < c.lo) :
    Enters₂ h.description A.H (sharedThread h reads (sharedParts h L) R.common) w₀ rc x k R :=
  enters_sharedThread hR rfl (fun _ => trivial)
    (fun c hc hlo _ => absurd hlo (Nat.not_le.2 (late c hc)))

/-! ## The second chain -/

/-- **K14's words at a witness of the second chain**: at the number of a sampled message, the table
that the witness holds at the message's seat, read as wordsOn reads a table; 0 at other numbers. It
reads no state: the seats are the plan's. -/
def lastWords {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : HeadAtReturn files A) (v : WtF) :
    OnBytes.Means.Words Cb.Gl.E :=
  fun o part i =>
    match ([.oU, .oOmega, .oSp] : List Msg2).find? fun m => ProofFile.Honest.K14.num m == o with
    | some m =>
      let rowBits := OnBytes.ceilLog2 ((sharedShape A.Z h.places m).rows part)
      v.tab (VerifiableInference.Desc.K1.qAt A.Z h.places).codes (sharedShape A.Z h.places m)
        (P5J.At.arr A.Z (h.sharedNumbers.tenant m).1 (h.sharedNumbers.tenant m).2)
        (h.sharedNumbers.tenant m).1 (h.sharedNumbers.tenant m).2
        (part == .mask) (i % 2 ^ rowBits) (i / 2 ^ rowBits)
    | none => 0

theorem find_sampled {α : Type} [BEq α] [LawfulBEq α] {f : Msg2 → α}
    (hf : Function.Injective f) (m : Msg2) :
    ([.oU, .oOmega, .oSp] : List Msg2).find? (fun m' => f m' == f m) = some m := by
  have ne : ∀ a b : Msg2, a ≠ b → (f a == f b) = false := fun a b e =>
    beq_false_of_ne fun e' => e (hf e')
  cases m
  · simp [List.find?]
  · simp [List.find?, ne .oU .oOmega (by decide)]
  · simp [List.find?, ne .oU .oSp (by decide), ne .oOmega .oSp (by decide)]

theorem num_injective : Function.Injective ProofFile.Honest.K14.num := by
  intro a b e
  cases a <;> cases b <;> first | rfl | cases e

/-- **lastWitness holds the shared table at a sampled message's number and seat**, where the numbers
are apart. -/
theorem lastWitness_tab {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    {h : HeadAtReturn files A} (hap : SharedTenantsApart h) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (k : Coins A.B) (w : Local W₀ Rc ProofFile.Inst Tr)
    (heard : List Fmt.Drawn) (m : Msg2) (c : OnBytes.Codes) (shape : OnBytes.OracleShape) :
    (lastWitness h first reads k w heard).tab c shape
        (P5J.At.arr A.Z (h.sharedNumbers.tenant m).1 (h.sharedNumbers.tenant m).2)
        (h.sharedNumbers.tenant m).1 (h.sharedNumbers.tenant m).2 =
      sharedTable h reads k ⟨w.w₀, w.rc, A.H.key w.x⟩
        (heard.drop (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length) m := by
  have hten : Function.Injective h.sharedNumbers.tenant := fun a b e =>
    hap.1 (by
      show P5J.At.arr A.Z _ _ = P5J.At.arr A.Z _ _
      rw [e])
  funext mask row place
  unfold VerifiableInference.Desc.Wit.tab
  split
  · have e : (lastWitness h first reads k w heard).pad (h.sharedNumbers.tenant m).1
        (h.sharedNumbers.tenant m).2 =
        match ([.oU, .oOmega, .oSp] : List Msg2).find?
          (fun m' => h.sharedNumbers.tenant m' ==
            ((h.sharedNumbers.tenant m).1, (h.sharedNumbers.tenant m).2)) with
        | some m' => sharedTable h reads k ⟨w.w₀, w.rc, A.H.key w.x⟩
            (heard.drop (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length) m'
        | none => (first.script.wit k w heard).pad (h.sharedNumbers.tenant m).1
            (h.sharedNumbers.tenant m).2 := rfl
    rw [e, Prod.mk.eta, find_sampled hten m]
  · have e : (lastWitness h first reads k w heard).msg
        (P5J.At.arr A.Z (h.sharedNumbers.tenant m).1 (h.sharedNumbers.tenant m).2) =
        match ([.oU, .oOmega, .oSp] : List Msg2).find?
          (fun m' => P5J.At.arr A.Z (h.sharedNumbers.tenant m').1 (h.sharedNumbers.tenant m').2 ==
            P5J.At.arr A.Z (h.sharedNumbers.tenant m).1 (h.sharedNumbers.tenant m).2) with
        | some m' => sharedTable h reads k ⟨w.w₀, w.rc, A.H.key w.x⟩
            (heard.drop (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length) m'
        | none => (first.script.wit k w heard).msg
            (P5J.At.arr A.Z (h.sharedNumbers.tenant m).1 (h.sharedNumbers.tenant m).2) := rfl
    rw [e, find_sampled (f := fun m' =>
      P5J.At.arr A.Z (h.sharedNumbers.tenant m').1 (h.sharedNumbers.tenant m').2) hap.1 m]

/-- **What lastWords reads off lastWitness are K14's honest words**, at each sampled message's number,
at the shared chain's input and challenges. -/
theorem lastWords_at_lastWitness {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    {h : HeadAtReturn files A} (hap : SharedTenantsApart h) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (k : Coins A.B) (w : Local W₀ Rc ProofFile.Inst Tr)
    (heard : List Fmt.Drawn) (m : Msg2) (part : OnBytes.Part) (i : Nat) :
    lastWords h (lastWitness h first reads k w heard) (ProofFile.Honest.K14.num m) part i =
      _root_.Desc.K14.Honest.words2 (VerifiableInference.Desc.K1.qAt A.Z h.places)
        (sentFirstOf A.Z h.places)
        (_root_.Desc.K14.first (VerifiableInference.Desc.K1.qAt A.Z h.places).codes (A.H.key w.x))
        (ProofFile.Honest.K14.firstRv
          (heard.drop (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length))
        (ProofFile.Honest.K14.holds2 (VerifiableInference.Desc.K1.qAt A.Z h.places) reads.weights reads.rand
          k ⟨w.w₀, w.rc, A.H.key w.x⟩)
        (ProofFile.Honest.K14.num m) part i := by
  unfold lastWords
  rw [find_sampled num_injective m]
  show (lastWitness h first reads k w heard).tab _ _ _ _ _ _ _ _ = _
  rw [lastWitness_tab hap]
  unfold sharedTable tableOfWords
  cases part <;> simp [Nat.mod_add_div']

/-- **The three names of the first chain's count of trees are one number**: the one that the library's
table reads, the description's, and the plan of the shared table's. -/
def FirstTreesAreOneNumber {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : HeadAtReturn files A) : Prop :=
  ((VerifierAndGoals.AtTheName.dpZ files).at OnBytes.Slice.frS.P.T.a).t₁ = h.description.t₁ ∧
    _root_.Desc.K14.Law.Sh.t₁ h.head.toAtMg.shPlan = h.description.t₁

/-- **A sampled message is read as one table**: at the real rows of message o of a statement, the
words that a reader of the shared chain's book sees are the words that lastWords reads at the
message's number. -/
def SampledReadOneTable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : HeadAtReturn files A) (st : OnBytes.Statement) (book : OnBytes.TreeBook) (m : Msg2)
    (o : Nat) : Prop :=
  ∀ (v : WtF) (part : OnBytes.Part) (i : Nat),
    i % 2 ^ st.rowBits o part < OnBytes.Means.realRows st o part →
      VerifiableInference.Desc.Sound.wordsShared (P5J.At.arr A.Z)
          ((VerifierAndGoals.AtTheName.dpZ files).at OnBytes.Slice.frS.P.T.a).t₁ st book v o part i =
        lastWords h v (ProofFile.Honest.K14.num m) part i

/-- **What the second chain's thread still takes**: the trees taken over, what was handed, the trees'
tables, the number at which each is fixed, the riders behind the door, and what a step keeps outside
K14's member. -/
structure LastLetters (A : OnlineProverWithDescription W₀ Rc Tr X₀ X) where
  taken : List Fmt.TreeSource
  ends : Coins A.B → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → (ProofFile.InstPub × TS) × Desc.K14.St
  table : Fmt.TreeSource → Coins A.B → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Place × Table
  /-- each table that a round of the last chain opens has the depth at which the round opens it, at
  every coins, input and challenges: so a value has to be total in the coins -/
  tableDepths : ∀ d ∈ A.F.second.blocksInOrder.flatMap (·.rounds), ∀ o ∈ d.opens, ∀ k w h,
    (table o.2 k w h).2.logLength = o.1.a
  fixed : Fmt.TreeSource → Nat
  riders : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) VerifiableInference.Desc.Third.S₃)
  keeps : Place → VerifiableInference.Desc.Third.S₃ → VerifiableInference.Desc.Third.S₃ → Prop

/-- **The rider at border 1**: the taken trees' sources are tied to the own test's declared rounds.
It is what makes member 1 accept (takenSources_exact): every member of the own group and the mask
has a tree in the book, declared as taken from the chain that sent it, and no other tree is. Member 0
lays it from the test at border 0 (lays_tied, Honest/K14/FiveAtLastThreadTied.lean). -/
def tiedRider (W : Type) (places : H2U.Places4) : RiderCl W VerifiableInference.Desc.Third.S₃ :=
  ⟨1, 1, fun _ _ s => VerifiableInference.Desc.Third.Law.Tied (LLT25.c2 places) s⟩

/-- **The second chain's riders**: at border 0 the test on the start's record that says Tied ahead;
at border 1 Tied; then the later ones, each of which begins at border 2 or later. -/
def lastRiders {W : Type} (places : H2U.Places4)
    (later : List (RiderCl W VerifiableInference.Desc.Third.S₃)) :
    List (RiderCl W VerifiableInference.Desc.Third.S₃) :=
  ProofFile.Honest.K14.tiedAheadRider W (LLT25.c2 places).rounds :: tiedRider W places :: later

/-- **The clause keeps at the second chain's two frames**: members 1 and 3 hand the record on as it
is (takenSources_exact; chainEnd's decide); at the own test's place another clause stands. -/
def lastKeeps (own : Place → VerifiableInference.Desc.Third.S₃ → VerifiableInference.Desc.Third.S₃ → Prop)
    (q : Place) (s s' : VerifiableInference.Desc.Third.S₃) : Prop :=
  (q = ⟨3, none, 1, .frame⟩ ∨ q = ⟨3, none, 3, .frame⟩ → s' = s) ∧ own q s s'

/-- **What the second chain is handed**: the two earlier chains' last states, at the run's input, by
endsBy: where each has one state for each run, the function returns these two. Said₁ and Said₂ are
the two chains' letters (at the door, SaidWalk from the first stands). It is defined by choice and
computes nothing. -/
def lastEnds {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} {Wt : Type} [Inhabited TS]
    [Inhabited Desc.K14.St] (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (shared : SharedThreadParts A Wt)
    (R : Ready W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
    (Said₁ : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (Said₂ : Nat → Coins A.B → Mid (Common W₀ Rc OnBytes.TableKey) X₀ → Prop) (k : Coins A.B)
    (w : Local W₀ Rc ProofFile.Inst Tr) (heard : List Fmt.Drawn) : (ProofFile.InstPub × TS) × Desc.K14.St :=
  let both := endsBy (firstThread h first R.own) Said₁ h.description.first.blocksInOrder.length
    (sharedThread h reads shared R.common) Said₂ h.description.shared.blocksInOrder.length id
    (fun v : Local W₀ Rc ProofFile.Inst Tr =>
      (⟨v.w₀, v.rc, A.H.key v.x⟩ : Common W₀ Rc OnBytes.TableKey)) k w heard
  ((w.x.pub, both.1), both.2)

/-- **The second chain's fields at these values.** The meaning is K14's maker over the library's
shared table, reading lastWords, with the first chain's pins as the first thread holds them, and the
items (Dot) and (Eval) at the fillings at which K14's laws stand (second_hDot, second_hEv). The
door's eleven tests are a rider at border 0. -/
def lastParts {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : HeadAtReturn files A)
    (first : FirstThreadParts A) (L : LastLetters A) : LastThreadParts A where
  meaning := fun v =>
    ProofFile.Honest.K14.mgReads (lastWords h) (VerifiableInference.Desc.K1.qAt A.Z h.places)
      h.sharedNumbers
      { h.sharedMeaning with
        pin₁ := fun j t p y w => (firstLetters h first v).mgP.pin j t p y w
        dot := VerifiableInference.Desc.Third.Law.dotI (ToldDesc.p14At A.Z).S
          (fun q => VerifiableInference.Desc.Third.Law.gOfS q.2)
          (fun d w => VerifiableInference.Desc.Sound.wordsShared (P5J.At.arr A.Z)
            ((VerifierAndGoals.AtTheName.dpZ files).at OnBytes.Slice.frS.P.T.a).t₁ d.st d.book w)
          (fun q => VerifiableInference.Desc.Third.Law.wvW (P5J.At.arr A.Z) (ToldDesc.p14At A.Z)
            (fun a => a.2) q)
        ev := ProofFile.Honest.K14.evAll (P5J.At.arr A.Z) (fun a => a.2) }
  taken := L.taken
  ends := L.ends
  table := L.table
  fixed := L.fixed
  rides := ridersOf
    (ProofFile.Honest.K14.doorRider _ (ToldDesc.p14At A.Z) :: L.riders)
  keeps := L.keeps

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.lastWords
#print axioms ProofFile.Honest.FirstThread.lastWords_at_lastWitness
#print axioms ProofFile.Honest.FirstThread.lastEnds
#print axioms ProofFile.Honest.FirstThread.tiedRider
#print axioms ProofFile.Honest.FirstThread.lastRiders
#print axioms ProofFile.Honest.FirstThread.lastKeeps
#print axioms ProofFile.Honest.FirstThread.lastParts
#print axioms ProofFile.Honest.FirstThread.sharedParts
#print axioms ProofFile.Honest.FirstThread.enters_sharedParts
