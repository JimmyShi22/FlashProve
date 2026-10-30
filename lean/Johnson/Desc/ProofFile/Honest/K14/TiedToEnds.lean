-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K14/TiedToEnds.lean: a clause for the parameter Said of the second
chain's honest thread: THIS RUN COMES BEHIND A PAIR OF STANDS OF THE TWO EARLIER CHAINS' THREADS AT
THEIR LAST BORDERS. Two definitions; statements with their proofs.

A stand of a thread at a border: its invariant Thr (Honest/Thread/Thr.lean), with its companion Said
(ThrS, Honest/Thread/Said.lean), holds there, at some state of the verifier, some state of the
prover's run and some available tables.

Why. A statement at a sub-protocol of the second chain is handed a stand of that chain's thread and
nothing else. Some of these statements speak of what the two earlier chains have left: the sample
rows of the messages that the second chain's proximity test takes over hold because the earlier
chains' threads held at their ends, at the same coins, input and challenges. The invariant Thr of
the second chain does not remember that. Its companion Said (Honest/Thread/Said.lean) is a free
parameter for just such clauses on the run. The clause here has that file's form SaidAt, so it is
carried past every sub-protocol without further proof; it has to be shown once, where the chain is
entered.

  TiedC               the sentence on the coins, the input and the rounds seen in front of the
                      chain: there are stands of the two earlier threads at their borders n₁ and n₂,
                      at these coins, whose runs' inputs are made of this input, and whose runs have
                      seen, one after the other, just these rounds
  TiedToEnds          the clause: SaidAt 0 front TiedC
  tied_next           it is carried past every sub-protocol
  tied_at_start       **it holds at the state at which the frame begins the second chain**
                      (Ready.start₃, Honest/Frame.lean) behind two such stands, where front is the
                      number of challenges that the two runs have heard
  tied_reads_no_columns, tied_at_door   the clause does not read the columns that a state of the run
                      holds as opened: so it holds as well at that state with these columns laid,
                      whatever they are. DoorBehindS asks at the two ends' columns joined
                      (ChainProgress.start, Honest/Walk.lean, lays them so)
  pair_of_tied        **from a stand of the second chain's thread with the clause: the pair of
                      stands**, and: what the two runs have heard, and seen, is the first front
                      challenges, and rounds, of this run's
  pair_at_endsBy      the same pair AT THE TWO STATES THAT THE LIBRARY's TERM endsBy
                      (Honest/Thread/OneState.lean) RETURNS at this run's coins, input and first
                      front challenges (see the limit on endsBy below)
These are general in the threads; tied_at_start and tied_at_door stand at the frame's types of
input.
  last_front          at the three threads as they are written: the number of rounds in front of the
                      second chain is what the two earlier runs have heard at their ends
  tied_at_door_written   **THE ENTRY, at the three threads as they are written**: behind a stand of
                      firstThread and one of sharedThread at their last borders the clause holds, at
                      lastThread's own number of rounds in front, at the state at which the second
                      chain is begun
  tied_at_door_ready  the same at the two inputs that the frame's routine ready returns
  ties_of_pair        from two stands and the equation on the challenges: the two ties on what was
                      heard
  ties_at_last        **at the three threads as they are written** (firstThread, sharedThread,
                      lastThread, Honest/Thread/TheFirstThread.lean): from a stand of lastThread, at
                      any border, with the clause: two stands with one run's coins; the first run's
                      input is this run's; this run has heard what the first run has heard and more;
                      the shared run's input is made of this run's; the first challenge that the
                      shared run has heard is the first behind the first chain's in this run's list,
                      at every continuation; and the two equations on the lists
  ties_at_endsBy      the same with the two stands at endsBy's two states, BUT FOR THE EQUATION ON
                      THE ROUNDS SEEN: endsBy is chosen by the challenges heard alone

Limits.
  * BY WHICH DOOR THE CLAUSE CAN BE ENTERED. The clause asks for two whole stands. The library
    states what is owed where the second chain begins in two forms. DoorBehindS
    (Honest/Thread/FileD.lean)
    hands over the two stands: there the two stands that tied_at_door asks are at hand (its other
    premises, on the inputs and on front, come from the threads' own clauses: at the threads as they
    are written, tied_at_door_written); file_runsD, file_acceptsD and file_accepts_viewsD of that
    file take this form. The other form (the premise e₃ of
    doorBehindS_of in that file, of the three rules of Honest/Thread/FileS.lean, of threadsS,
    onDebts_of_onFromS and file_owed in Honest/Thread/FileOwed.lean, and of the rules that call
    these) hands over the two earlier chains' Said alone, without their invariants: FROM THAT THE
    CLAUSE CANNOT BE SHOWN, unless Said₁ and Said₂ themselves say that such stands exist. So the
    rules of the second form cannot be used with this clause as they stand. The clause is one
    conjunct of what the door owes on Said; the second chain's invariant at its first border is not
    shown here.
  * TiedC and TiedToEnds are definitions, meant as a value of a parameter. NOTHING HERE SHOWS THAT
    ANY THREAD STANDS AT ANY RUN. Where no pair of stands exists the clause is false from the
    border 0 on, and a statement under it is empty.
  * tied_at_start and tied_at_door take the two stands, the tie of the inputs and the number front
    as premises.
  * The pair need not be this run's own two ends: it is some pair at the same coins and inputs that
    has seen the same rounds. Said₁ and Said₂ are free here: whoever enters the clause must take
    them to be the two earlier threads' own, as the door hands them over. The tables available at
    the two stands are tied to nothing of the second chain's stand: Said reads no table, so no
    clause of this form can tie them.
  * ON endsBy. Where the second chain's parameter for the two earlier chains' last states is made of
    endsBy AT THE SAME THREADS, Said₁, Said₂, BORDERS AND MAPS OF THE INPUT, pair_at_endsBy and
    ties_at_endsBy have the stands at its own values; lastThread's parameter returns the public part
    beside the first state, so a caller wraps endsBy; both take that the two types of states are
    inhabited. These two statements do not ask that a run has one state only. THE ROAD AS A WHOLE
    DOES: the second chain's thread begins at what the start returns of that parameter's
    values, and the door hands the start's return at the run's own two ends; so a stand of such a
    thread is entered at the door only where endsBy returns the run's own ends: endsAre_endsBy
    (Honest/Thread/OneState.lean), where each earlier chain has one state for each run. The stands
    at endsBy's states need not be this run's own ends, and need not have seen its rounds.
  * WHAT THE EQUATION ON THE ROUNDS SEEN IS KEPT FOR: to show that the pair's two states are this
    run's own ends. That sentence is not drawn here. In this file the equation is spent once: the
    equation on the challenges heard in pair_of_tied is drawn from it.
  * In ties_at_last and ties_at_endsBy the three inputs w₁, w, w₂ are free. Each thread's invariant
    says that its run's input is the thread's own: so at inputs that are not tied as the clause
    says, the premises cannot hold together.
  * In the statements at the threads as they are written h : HeadAtReturn is a hypothesis
    (Honest/K14/WordsAtLastWitness.lean says what it holds).

This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.K14.TiesAtTheEnds
import Johnson.Desc.ProofFile.Honest.Thread.Said
import Johnson.Desc.ProofFile.Honest.Thread.Hands

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open Desc.K14 (St)
open ProofFile.Honest.FirstThread

section general
variable {Bk : ProverCoinCounts} {S₁ Cl₁ V₁ W₁ X₁ Pb₁ S₂ Cl₂ V₂ W₂ X₂ Pb₂ W₃ : Type}
  (T₁ : Thread Bk S₁ Cl₁ V₁ W₁ X₁ Pb₁) (Said₁ : Nat → Coins Bk → Mid W₁ X₁ → Prop) (n₁ : Nat)
  (T₂ : Thread Bk S₂ Cl₂ V₂ W₂ X₂ Pb₂) (Said₂ : Nat → Coins Bk → Mid W₂ X₂ → Prop) (n₂ : Nat)
  (in₁ : W₃ → W₁) (in₂ : W₃ → W₂)

/-- **There are stands of the two earlier threads at their borders n₁ and n₂**, at the coins k,
whose runs' inputs are made of the input w, and whose runs have seen, one after the other, just the
rounds rs: what was shown in them and the challenges. -/
def TiedC (k : Coins Bk) (w : W₃) (rs : List Fmt.RoundView) : Prop :=
  ∃ e₁ m₁ E₁ e₂ m₂ E₂, ThrS T₁ Said₁ n₁ k e₁ m₁ E₁ ∧ ThrS T₂ Said₂ n₂ k e₂ m₂ E₂ ∧
    m₁.st.input = in₁ w ∧ m₂.st.input = in₂ w ∧ m₁.seen ++ m₂.seen = rs

/-- **The clause**: at every border, front rounds have been seen, and TiedC holds of the run's
coins, its input and the first front rounds seen. -/
def TiedToEnds {X₃ : Type} (front : Nat) : Nat → Coins Bk → Mid W₃ X₃ → Prop :=
  SaidAt 0 front (TiedC T₁ Said₁ n₁ T₂ Said₂ n₂ in₁ in₂)

variable {S₃ Cl₃ V₃ X₃ Pb₃ : Type} (T₃ : Thread Bk S₃ Cl₃ V₃ W₃ X₃ Pb₃)

/-- It is carried past every sub-protocol. -/
theorem tied_next (front b : Nat) :
    SaidNext T₃ (TiedToEnds T₁ Said₁ n₁ T₂ Said₂ n₂ in₁ in₂ front) b :=
  saidNext_carry T₃ (Nat.zero_le b)

/-- The clause does not read the columns that a state of the run holds as opened. -/
theorem tied_reads_no_columns (front b : Nat) (k : Coins Bk) (m : Mid W₃ X₃)
    (o : Option (List VerifiableInference.Desc.OpenedColumn)) :
    TiedToEnds T₁ Said₁ n₁ T₂ Said₂ n₂ in₁ in₂ front b k { m with opened := o } ↔
      TiedToEnds T₁ Said₁ n₁ T₂ Said₂ n₂ in₁ in₂ front b k m := Iff.rfl

/-- **From a stand of the second chain's thread with the clause: the pair of stands**, and what the
two runs have heard, and seen, is the first front challenges, and rounds, of this run's. -/
theorem pair_of_tied {b : Nat} {k : Coins Bk} {s : S₃} {m : Mid W₃ X₃} {E : Env}
    (u : Thr T₃ b k s m E) (front : Nat)
    (ht : TiedToEnds T₁ Said₁ n₁ T₂ Said₂ n₂ in₁ in₂ front b k m) :
    ∃ e₁ m₁ E₁ e₂ m₂ E₂, ThrS T₁ Said₁ n₁ k e₁ m₁ E₁ ∧ ThrS T₂ Said₂ n₂ k e₂ m₂ E₂ ∧
      m₁.st.input = in₁ m.st.input ∧ m₂.st.input = in₂ m.st.input ∧
      m₁.st.heard ++ m₂.st.heard = m.st.heard.take front ∧
      m₁.seen ++ m₂.seen = m.seen.take front := by
  obtain ⟨-, e₁, m₁, E₁, e₂, m₂, E₂, u₁, u₂, i₁, i₂, hs⟩ := ht (Nat.zero_le b)
  refine ⟨e₁, m₁, E₁, e₂, m₂, E₂, u₁, u₂, i₁, i₂, ?_, hs⟩
  rw [← u.2.2.2.2.1.1, ← List.map_take, ← hs, List.map_append, u₁.1.2.2.2.2.1.1,
    u₂.1.2.2.2.2.1.1]

/-- **The pair at the two states that the library's term for the earlier chains' last states
returns**, at this run's coins, input and first front challenges. -/
theorem pair_at_endsBy [Inhabited S₁] [Inhabited S₂] {b : Nat} {k : Coins Bk} {s : S₃}
    {m : Mid W₃ X₃} {E : Env} (u : Thr T₃ b k s m E) (front : Nat)
    (ht : TiedToEnds T₁ Said₁ n₁ T₂ Said₂ n₂ in₁ in₂ front b k m) :
    ∃ m₁ E₁ m₂ E₂,
      ThrS T₁ Said₁ n₁ k
        (endsBy T₁ Said₁ n₁ T₂ Said₂ n₂ in₁ in₂ k m.st.input (m.st.heard.take front)).1 m₁ E₁ ∧
      ThrS T₂ Said₂ n₂ k
        (endsBy T₁ Said₁ n₁ T₂ Said₂ n₂ in₁ in₂ k m.st.input (m.st.heard.take front)).2 m₂ E₂ ∧
      m₁.st.input = in₁ m.st.input ∧ m₂.st.input = in₂ m.st.input ∧
      m₁.st.heard ++ m₂.st.heard = m.st.heard.take front := by
  obtain ⟨e₁, m₁, E₁, e₂, m₂, E₂, u₁, u₂, i₁, i₂, hs, -⟩ :=
    pair_of_tied T₁ Said₁ n₁ T₂ Said₂ n₂ in₁ in₂ T₃ u front ht
  exact endsBy_stands T₁ Said₁ n₁ T₂ Said₂ n₂ in₁ in₂ k m.st.input _
    ⟨(e₁, e₂), m₁, E₁, m₂, E₂, u₁, u₂, i₁, i₂, hs⟩

end general

section start
variable {Bk : ProverCoinCounts} {W₀ Rc Xi Ky Tr X₀ X S₁ Cl₁ V₁ Pb₁ S₂ Cl₂ V₂ Pb₂ : Type}
  (T₁ : Thread Bk S₁ Cl₁ V₁ (Local W₀ Rc Xi Tr) X Pb₁)
  (Said₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) (n₁ : Nat)
  (T₂ : Thread Bk S₂ Cl₂ V₂ (Common W₀ Rc Ky) X₀ Pb₂)
  (Said₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop) (n₂ : Nat)
  (in₁ : Local W₀ Rc Xi Tr → Local W₀ Rc Xi Tr) (in₂ : Local W₀ Rc Xi Tr → Common W₀ Rc Ky)

/-- **The clause holds at the state at which the frame begins the second chain behind two such
stands**, at every border's number. -/
theorem tied_at_start (R : Ready W₀ Rc Xi Ky Tr X₀ X) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    {k : Coins Bk} {e₁ : S₁} {m₁ : Mid (Local W₀ Rc Xi Tr) X} {E₁ : Env} {e₂ : S₂}
    {m₂ : Mid (Common W₀ Rc Ky) X₀} {E₂ : Env} (u₁ : ThrS T₁ Said₁ n₁ k e₁ m₁ E₁)
    (u₂ : ThrS T₂ Said₂ n₂ k e₂ m₂ E₂) (i₁ : m₁.st.input = in₁ R.own)
    (i₂ : m₂.st.input = in₂ R.own) (front : Nat)
    (hf : front = m₁.st.heard.length + m₂.st.heard.length) (b : Nat) :
    TiedToEnds T₁ Said₁ n₁ T₂ Said₂ n₂ in₁ in₂ front b k (R.start₃ H m₁ m₂) := by
  have s₁ : m₁.seen.map (·.drawn) = m₁.st.heard := u₁.1.2.2.2.2.1.1
  have s₂ : m₂.seen.map (·.drawn) = m₂.st.heard := u₂.1.2.2.2.2.1.1
  have hl : (m₁.seen ++ m₂.seen).length = front := by
    rw [hf, ← s₁, ← s₂, List.length_append, List.length_map, List.length_map]
  intro _
  refine ⟨Nat.le_of_eq hl.symm, e₁, m₁, E₁, e₂, m₂, E₂, u₁, u₂, i₁, i₂, ?_⟩
  show _ = (m₁.seen ++ m₂.seen).take front
  rw [← hl, List.take_length]

/-- **The same at that state with opened columns laid**, whatever they are. -/
theorem tied_at_door (R : Ready W₀ Rc Xi Ky Tr X₀ X) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    {k : Coins Bk} {e₁ : S₁} {m₁ : Mid (Local W₀ Rc Xi Tr) X} {E₁ : Env} {e₂ : S₂}
    {m₂ : Mid (Common W₀ Rc Ky) X₀} {E₂ : Env} (u₁ : ThrS T₁ Said₁ n₁ k e₁ m₁ E₁)
    (u₂ : ThrS T₂ Said₂ n₂ k e₂ m₂ E₂) (i₁ : m₁.st.input = in₁ R.own)
    (i₂ : m₂.st.input = in₂ R.own) (front : Nat)
    (hf : front = m₁.st.heard.length + m₂.st.heard.length) (b : Nat)
    (o : Option (List VerifiableInference.Desc.OpenedColumn)) :
    TiedToEnds T₁ Said₁ n₁ T₂ Said₂ n₂ in₁ in₂ front b k
      { R.start₃ H m₁ m₂ with opened := o } :=
  tied_at_start T₁ Said₁ n₁ T₂ Said₂ n₂ in₁ in₂ R H u₁ u₂ i₁ i₂ front hf b

end start

variable {W₀ Rc Tr X₀ X Wt : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- At the three threads as they are written: the number of rounds in front of the second chain is
what the two earlier runs have heard at their last borders. -/
theorem last_front (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (sh : SharedThreadParts A Wt) (parts : LastThreadParts A)
    (w₁ w : Local W₀ Rc ProofFile.Inst Tr) (w₂ : Common W₀ Rc OnBytes.TableKey) {k : Coins A.B}
    {e₁ : P5J.TS} {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E₁ : Env}
    (u₁ : Thr (firstThread h first w₁) h.description.first.blocksInOrder.length k e₁ m₁ E₁) {e₂ : St}
    {m₂ : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E₂ : Env}
    (u₂ : Thr (sharedThread h reads sh w₂) h.description.shared.blocksInOrder.length k e₂ m₂ E₂) :
    (lastThread h first reads parts w).front = m₁.st.heard.length + m₂.st.heard.length := by
  have a₁ : m₁.st.heard.length =
      (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length :=
    drawsFit_length _ _ u₁.2.1
  have a₂ : m₂.st.heard.length =
      (declsTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length).length :=
    drawsFit_length _ _ u₂.2.1
  show (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length ++
    declsTo h.description.shared.blocksInOrder h.description.shared.blocksInOrder.length).length = _
  rw [List.length_append, a₁, a₂]

/-- **THE ENTRY AT THE THREE THREADS AS THEY ARE WRITTEN**: behind a stand of firstThread at the
run's own input and a stand of sharedThread at the shared chain's input made of it, both at their
last borders, the clause holds at lastThread's own number of rounds in front, at the state at which
the second chain is begun, whatever columns are laid as opened. -/
theorem tied_at_door_written (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (sh : SharedThreadParts A Wt) (parts : LastThreadParts A)
    (R : Ready W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said₁ : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (Said₂ : Nat → Coins A.B → Mid (Common W₀ Rc OnBytes.TableKey) X₀ → Prop)
    {k : Coins A.B} {e₁ : P5J.TS} {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E₁ : Env}
    (u₁ : ThrS (firstThread h first R.own) Said₁ h.description.first.blocksInOrder.length k e₁ m₁ E₁)
    {e₂ : St} {m₂ : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E₂ : Env}
    (u₂ : ThrS (sharedThread h reads sh ⟨R.own.w₀, R.own.rc, A.H.key R.own.x⟩) Said₂
      h.description.shared.blocksInOrder.length k e₂ m₂ E₂) (b : Nat)
    (o : Option (List VerifiableInference.Desc.OpenedColumn)) :
    TiedToEnds (firstThread h first R.own) Said₁ h.description.first.blocksInOrder.length
      (sharedThread h reads sh ⟨R.own.w₀, R.own.rc, A.H.key R.own.x⟩) Said₂
      h.description.shared.blocksInOrder.length id (fun v => ⟨v.w₀, v.rc, A.H.key v.x⟩)
      (lastThread h first reads parts w).front b k { R.start₃ A.H m₁ m₂ with opened := o } :=
  tied_at_door _ _ _ _ _ _ _ _ R A.H u₁ u₂ u₁.1.2.2.2.2.2.2.1 u₂.1.2.2.2.2.2.2.1 _
    (last_front h first reads sh parts _ w _ u₁.1 u₂.1) b o

/-- **The entry at the two inputs that the frame's routine ready returns**: firstThread at R.own,
sharedThread at R.common. -/
theorem tied_at_door_ready (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (sh : SharedThreadParts A Wt) (parts : LastThreadParts A)
    {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k₀ : Coins A.B}
    {R : Ready W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X}
    (hR : ready h.description A.B A.H w₀ rc x k₀ = .ok R) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said₁ : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (Said₂ : Nat → Coins A.B → Mid (Common W₀ Rc OnBytes.TableKey) X₀ → Prop)
    {k : Coins A.B} {e₁ : P5J.TS} {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E₁ : Env}
    (u₁ : ThrS (firstThread h first R.own) Said₁ h.description.first.blocksInOrder.length k e₁ m₁ E₁)
    {e₂ : St} {m₂ : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E₂ : Env}
    (u₂ : ThrS (sharedThread h reads sh R.common) Said₂ h.description.shared.blocksInOrder.length k e₂ m₂
      E₂) (b : Nat) (o : Option (List VerifiableInference.Desc.OpenedColumn)) :
    TiedToEnds (firstThread h first R.own) Said₁ h.description.first.blocksInOrder.length
      (sharedThread h reads sh R.common) Said₂ h.description.shared.blocksInOrder.length id
      (fun v => ⟨v.w₀, v.rc, A.H.key v.x⟩) (lastThread h first reads parts w).front b k
      { R.start₃ A.H m₁ m₂ with opened := o } := by
  have e : R.common = ⟨R.own.w₀, R.own.rc, A.H.key R.own.x⟩ := by
    rw [common_of_ready hR, own_of_ready hR R.own.trace]
    rfl
  rw [e] at u₂ ⊢
  exact tied_at_door_written h first reads sh parts R w Said₁ Said₂ u₁ u₂ b o

/-- From two stands and the equation on the lists: this run has heard what the first run has heard
and more, and the first challenge that the shared run has heard is the first behind the first
chain's in this run's list, at every continuation. -/
theorem ties_of_pair (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (sh : SharedThreadParts A Wt) (w₁ : Local W₀ Rc ProofFile.Inst Tr)
    (w₂ : Common W₀ Rc OnBytes.TableKey) {k : Coins A.B} {e₁ : P5J.TS}
    {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E₁ : Env}
    (u₁ : Thr (firstThread h first w₁) h.description.first.blocksInOrder.length k e₁ m₁ E₁) {e₂ : St}
    {m₂ : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E₂ : Env}
    (u₂ : Thr (sharedThread h reads sh w₂) h.description.shared.blocksInOrder.length k e₂ m₂ E₂)
    (heard : List Fmt.Drawn) (front : Nat)
    (hs : m₁.st.heard ++ m₂.st.heard = heard.take front) :
    (∃ rest, heard = m₁.st.heard ++ rest) ∧
      ∀ ds, firstRv m₂.st.heard = firstRv ((heard ++ ds).drop
        (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length) := by
  have hh : heard = m₁.st.heard ++ m₂.st.heard ++ heard.drop front := by
    rw [hs, List.take_append_drop]
  refine ⟨⟨_, by rw [← List.append_assoc]; exact hh⟩, fun ds => ?_⟩
  exact hd_of_split h first reads sh w₁ w₂ u₁ u₂ (heard ++ ds) (heard.drop front ++ ds)
    (by rw [← List.append_assoc, ← hh])

/-- **AT THE THREE THREADS AS THEY ARE WRITTEN: FROM A STAND OF lastThread WITH THE CLAUSE, THE PAIR
OF STANDS AND ITS TIES TO THIS RUN.** -/
theorem ties_at_last (h : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (sh : SharedThreadParts A Wt) (parts : LastThreadParts A)
    (w₁ w : Local W₀ Rc ProofFile.Inst Tr) (w₂ : Common W₀ Rc OnBytes.TableKey)
    (Said₁ : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (Said₂ : Nat → Coins A.B → Mid (Common W₀ Rc OnBytes.TableKey) X₀ → Prop)
    {b : Nat} {k : Coins A.B} {st : VerifiableInference.Desc.Third.S₃}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (u : Thr (lastThread h first reads parts w) b k st m E)
    (ht : TiedToEnds (firstThread h first w₁) Said₁ h.description.first.blocksInOrder.length
      (sharedThread h reads sh w₂) Said₂ h.description.shared.blocksInOrder.length id
      (fun v => ⟨v.w₀, v.rc, A.H.key v.x⟩) (lastThread h first reads parts w).front b k m) :
    ∃ e₁ m₁ E₁ e₂ m₂ E₂,
      ThrS (firstThread h first w₁) Said₁ h.description.first.blocksInOrder.length k e₁ m₁ E₁ ∧
      ThrS (sharedThread h reads sh w₂) Said₂ h.description.shared.blocksInOrder.length k e₂ m₂ E₂ ∧
      m₁.st.input = m.st.input ∧ (∃ rest, m.st.heard = m₁.st.heard ++ rest) ∧
      m₂.st.input = ⟨m.st.input.w₀, m.st.input.rc, A.H.key m.st.input.x⟩ ∧
      (∀ ds, firstRv m₂.st.heard = firstRv ((m.st.heard ++ ds).drop
        (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length)) ∧
      m₁.st.heard ++ m₂.st.heard =
        m.st.heard.take (lastThread h first reads parts w).front ∧
      m₁.seen ++ m₂.seen = m.seen.take (lastThread h first reads parts w).front := by
  obtain ⟨e₁, m₁, E₁, e₂, m₂, E₂, u₁, u₂, i₁, i₂, hs, hv⟩ :=
    pair_of_tied _ _ _ _ _ _ _ _ _ u _ ht
  obtain ⟨a, c⟩ := ties_of_pair h first reads sh w₁ w₂ u₁.1 u₂.1 m.st.heard _ hs
  exact ⟨e₁, m₁, E₁, e₂, m₂, E₂, u₁, u₂, i₁, a, i₂, c, hs, hv⟩

/-- **The same with the two stands at the two states that the library's term endsBy returns** at
this run's coins, input and the challenges heard in front of the second chain; without the equation
on the rounds seen. -/
theorem ties_at_endsBy [Inhabited P5J.TS] [Inhabited St] (h : HeadAtReturn files A)
    (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc) (sh : SharedThreadParts A Wt)
    (parts : LastThreadParts A) (w₁ w : Local W₀ Rc ProofFile.Inst Tr)
    (w₂ : Common W₀ Rc OnBytes.TableKey)
    (Said₁ : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (Said₂ : Nat → Coins A.B → Mid (Common W₀ Rc OnBytes.TableKey) X₀ → Prop)
    {b : Nat} {k : Coins A.B} {st : VerifiableInference.Desc.Third.S₃}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (u : Thr (lastThread h first reads parts w) b k st m E)
    (ht : TiedToEnds (firstThread h first w₁) Said₁ h.description.first.blocksInOrder.length
      (sharedThread h reads sh w₂) Said₂ h.description.shared.blocksInOrder.length id
      (fun v => ⟨v.w₀, v.rc, A.H.key v.x⟩) (lastThread h first reads parts w).front b k m) :
    ∃ m₁ E₁ m₂ E₂,
      ThrS (firstThread h first w₁) Said₁ h.description.first.blocksInOrder.length k
        (endsBy (firstThread h first w₁) Said₁ h.description.first.blocksInOrder.length
          (sharedThread h reads sh w₂) Said₂ h.description.shared.blocksInOrder.length id
          (fun v => ⟨v.w₀, v.rc, A.H.key v.x⟩) k m.st.input
          (m.st.heard.take (lastThread h first reads parts w).front)).1 m₁ E₁ ∧
      ThrS (sharedThread h reads sh w₂) Said₂ h.description.shared.blocksInOrder.length k
        (endsBy (firstThread h first w₁) Said₁ h.description.first.blocksInOrder.length
          (sharedThread h reads sh w₂) Said₂ h.description.shared.blocksInOrder.length id
          (fun v => ⟨v.w₀, v.rc, A.H.key v.x⟩) k m.st.input
          (m.st.heard.take (lastThread h first reads parts w).front)).2 m₂ E₂ ∧
      m₁.st.input = m.st.input ∧ (∃ rest, m.st.heard = m₁.st.heard ++ rest) ∧
      m₂.st.input = ⟨m.st.input.w₀, m.st.input.rc, A.H.key m.st.input.x⟩ ∧
      (∀ ds, firstRv m₂.st.heard = firstRv ((m.st.heard ++ ds).drop
        (declsTo h.description.first.blocksInOrder h.description.first.blocksInOrder.length).length)) ∧
      m₁.st.heard ++ m₂.st.heard =
        m.st.heard.take (lastThread h first reads parts w).front := by
  obtain ⟨m₁, E₁, m₂, E₂, u₁, u₂, i₁, i₂, hs⟩ := pair_at_endsBy _ _ _ _ _ _ _ _ _ u _ ht
  obtain ⟨a, c⟩ := ties_of_pair h first reads sh w₁ w₂ u₁.1 u₂.1 m.st.heard _ hs
  exact ⟨m₁, E₁, m₂, E₂, u₁, u₂, i₁, a, i₂, c, hs⟩

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.tied_next
#print axioms ProofFile.Honest.K14.pair_of_tied
#print axioms ProofFile.Honest.K14.tied_reads_no_columns
#print axioms ProofFile.Honest.K14.tied_at_start
#print axioms ProofFile.Honest.K14.tied_at_door
#print axioms ProofFile.Honest.K14.pair_at_endsBy
#print axioms ProofFile.Honest.K14.last_front
#print axioms ProofFile.Honest.K14.tied_at_door_written
#print axioms ProofFile.Honest.K14.tied_at_door_ready
#print axioms ProofFile.Honest.K14.ties_of_pair
#print axioms ProofFile.Honest.K14.ties_at_last
#print axioms ProofFile.Honest.K14.ties_at_endsBy
