-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Thr/AtThread.lean: the closing of a segment (K10) at the first chain's threads under
the library's head (`lettersHead`, Honest/Thread/FirstHead.lean; the head is `P5J.AtMgA` at the older hash,
Johnson/P5J/MgAtAll.lean). A thread is the structure of parameters of one chain's invariant `Thr`
(Honest/Thread/Thr.lean); a border is a number b: the chain's block number b stands behind it. Here the structure of
premises of Honest/K10/Thr/CloseAt.lean is had at such a thread, and with it three forms at the 25 closings' borders:
`Plays`, `PlaysS`, `AcceptedS` (Honest/Thread/Pays.lean, PaysS.lean). Short terms over Thr/CloseAt.lean, Thr/Plays.lean,
Thr/Yes.lean, Thr/HalfOfLot.lean and `tied_at_head` (Honest/K10/Wipe/AtHead.lean). No definition; one local notation;
eighteen theorems. In the statements b is a variable with hb: b = 14 l + 12 (14 l + 14 at the last link, l = 24).

  `closeAt_of_first`   at any thread T: from `Tied` (Honest/K10/SimLot.lean), hb, "T's blocks are c's flat list" and
                    `ClosingsFirst` (Thr/HalfOfLot.lean) of T's list of halves: `CloseAt` at the lot's job `lotJob`
  `first_of_list_head`, `first_of_lots_head`, `first_of_kinds_head`   the three ways to `ClosingsFirst` of
                    Thr/HalfOfLot.lean, under `P5J.AtMg` (the head's first part) in `IM.Open`'s stead
  `thread_bs`, `thread_hs`, `thread_front`   three facts on the head's thread, each by unfolding: its blocks are cF's
                    flat list; its list of halves is the prover's own field H.first; its test on the form says yes of
                    no state that bears a mark of failure
  **`closeAt_of_tied`**, `closeAt_at_head`   `CloseAt` at the head's thread, from hF: `ClosingsFirst H.first …`: at any
                    Qc and blk that `Tied` names at the link; and at each l < 25 there are such
  **`plays_at_head`**, `playsS_at_head`   from hF, at each l < 25: `Plays`; `PlaysS` at every Said
  **`accepted_of_tied`**, `accepted_base_of_tied`   from hF and ready: `AcceptedS` at every Said and fall. ready, in
                    the first: at every stand of `ThrS` at b and all challenges that fit the block's rounds, where fall
                    says nothing, the two tests of Johnson/Desc/K10/Honest/Split.lean say yes: `closeShapeB Qc` of the
                    record of the verifier's state, `closeValsB` of that record and the challenges. In the second:
                    `closeBaseB Qc` (Johnson/Desc/K10/Honest/BaseB.lean) says yes of that record; it names no
                    challenge. The premise front of Thr/Yes.lean is paid by `thread_front`
  **`accepted_at_head`**, `accepted_base_at_head`   the same at each l < 25, with ready asked at every Qc and blk that
                    `Tied` names at the link (it names one Qc: its first two clauses; and one blk: its third)
  `closeAt_of_lots`, `plays_of_lots`, `accepted_of_lots`   three of these from hT, hLc and hA in hF's stead

The named premises. hF: at each place that the lot reads, the first half of H.first at that place has one part: the move
for "BAT", then the fold's part at the lot's job. In its stead, in the last three: hT: H.first is `firstOf Zp Gr` at
lots Ls, then a lot Lc, then lots Rs; hLc: at Zp and Gr the halves of Lc are `seatLotC`'s; hA: `noK10` says yes of what
Ls lays. ready: no fact on a parameter: a sentence on the verifier's state at every stand of the thread and, in the form
on the two tests, on the challenges of the closing's own rounds.

The notation, and the option in front of it. 𝕋 stands for the head's thread, written out once. It shortens the
statements and declares no definition and no theorem: each use is that text, elaborated anew. When a notation is
declared, Lean looks through its text for names that are not bound, and that early look has no case for a field access:
it refuses `(…).thread`. `set_option quotPrecheck false in` turns that one look off for the one command behind it. It
loosens nothing in what Lean checks of a theorem: wherever 𝕋 is written, the text is elaborated and type-checked as any
term is.

Limits. hF, hT, hLc, hA and ready are premises: they are shown of no prover and of no state here; `noK10` is evaluated
by no line. "The head's thread" is a family: beside the head h, the prover H, the book Bk and `lettersHead`'s further
parameters Sc, test, carryX, item, n₁, n₂, b₀, Vd, Rd, Kp and w are variables of every statement on it. readers, rows,
stAt, Gr, Said and fall are variables too: the forms `Plays`, `PlaysS` and `AcceptedS` hold at every stAt, also at one
that always refuses: they do not tell a closing that speaks of its tables from one that sends the words at empty tables
(Honest/K10/Wipe/Speaks.lean has sentences that do). That the thread's invariant holds at any run is not said: where it
holds at no stand of a border, all three forms hold there for nothing; and `Plays`, `PlaysS` and `AcceptedS` ask nothing
where `chainSteps` returns no steps for the block. Whether the head can be had at any files is no theorem here. At the
full size and the older hash alone: the head's. No property of the protocol is claimed: nothing is said on its
soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Thr.HalfOfLot
import Johnson.Desc.ProofFile.Honest.K10.Thr.Plays
import Johnson.Desc.ProofFile.Honest.K10.Thr.Yes
import Johnson.Desc.ProofFile.Honest.K10.Wipe.AtHead
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Block Chain Place KindName Strs)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-! ## At any thread -/

/-- **`CloseAt` holds at any thread, at the lot's job**, given the tied block, the border's number, that the thread's
blocks are the chain's flat list, and the premise on the thread's list of halves. -/
theorem closeAt_of_first {W₀ Rc Xi Tr X Pb : Type} {Bk : ProverCoinCounts}
    {T : Thread Bk S ProofFile.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat} {c : Chain S ProofFile.Cl}
    {Z : ProofFile.Pub} {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block S ProofFile.Cl}
    (Td : Tied c Z l p Qc blk) (hb : b = 14 * l + (if l = 24 then 9 else 7) + 5) (hbs : T.bs = c.blocksInOrder)
    (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi) (G : ProofFile.Ground)
    (hF : ClosingsFirst T.hs readers rows stAt Z G) :
    CloseAt T b c Z l p blk (lotJob readers rows stAt Z G Qc) :=
  ⟨Td, hb, hbs, hF Qc Td.2.2.2.2.1⟩

/-! ## The premise on a list of halves, under the head -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {W₀ Rc Xi Tr X : Type}

/-- Under the head the premise holds of a list of this form: halves of other kinds, the lot's halves, any list. -/
theorem first_of_list_head (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) (readers : Local W₀ Rc Xi Tr → Readers)
    (rows : RowDataOf Xi) (stAt : StAtOf Xi) (Gr : ProofFile.Ground)
    {hs A B : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)}
    (hT : hs = A ++ (seatLotC readers rows stAt).halves Zp Gr ++ B) (hA : noK10 A = true) :
    ClosingsFirst hs readers rows stAt Zp Gr := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact first_of_list O readers rows stAt Gr hT hA

/-- Under the head the premise holds of what a list of lots lays, where one of them lays the lot's halves and no lot in
front of it lays a half at a place of the kind K10. -/
theorem first_of_lots_head (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) (readers : Local W₀ Rc Xi Tr → Readers)
    (rows : RowDataOf Xi) (stAt : StAtOf Xi) (Gr : ProofFile.Ground)
    {hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)}
    {Ls Rs : List (HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)}
    {Lc : HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X} (hT : hs = firstOf Zp Gr (Ls ++ Lc :: Rs))
    (hLc : Lc.halves Zp Gr = (seatLotC readers rows stAt).halves Zp Gr)
    (hA : noK10 (firstOf Zp Gr Ls) = true) : ClosingsFirst hs readers rows stAt Zp Gr := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact first_of_lots O readers rows stAt Gr hT hLc hA

/-- Under the head the premise holds of what a list of lots lays, where such a lot is in the list and each lot has no
half at a place of the kind K10 or has that lot's halves. -/
theorem first_of_kinds_head (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) (readers : Local W₀ Rc Xi Tr → Readers)
    (rows : RowDataOf Xi) (stAt : StAtOf Xi) (Gr : ProofFile.Ground)
    {hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)}
    {ls : List (HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)}
    {Lc : HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X} (hT : hs = firstOf Zp Gr ls) (hL : Lc ∈ ls)
    (hLc : Lc.halves Zp Gr = (seatLotC readers rows stAt).halves Zp Gr)
    (ho : ∀ M ∈ ls, (∀ e ∈ M.halves Zp Gr, e.place.kind ≠ KindName.K10) ∨ M.halves Zp Gr = Lc.halves Zp Gr) :
    ClosingsFirst hs readers rows stAt Zp Gr := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact first_of_kinds O readers rows stAt Gr hT hL hLc ho

end

/-! ## The head's thread -/

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

/-! ### Three facts on its parameters -/

/-- The thread's list of blocks is the head's own chain's flat list. -/
theorem thread_bs : (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs = cF.blocksInOrder := rfl

/-- The thread's list of halves is the prover's own field `first`. -/
theorem thread_hs : (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.hs = H.first := rfl

/-- The thread's test on the form says yes of no state that bears a mark of failure. -/
theorem thread_front (b : Nat) (a : (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.P) (s : S)
    (e : (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.form b (a, s) = true) :
    s.failed = none := by
  have e' : s.failed.isNone = true := e
  exact Option.isNone_iff_eq_none.1 e'

/-! ### The structure of premises -/

/-- **`CloseAt` holds at the head's thread, at the lot's job**, at any numbers and block that are tied at the link,
given the premise on the prover's list of halves. -/
theorem closeAt_of_tied {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block S ProofFile.Cl}
    (Td : Tied cF Zp l p Qc blk) {b : Nat} (hb : b = 14 * l + (if l = 24 then 9 else 7) + 5)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst) (stAt : StAtOf ProofFile.Inst)
    (Gr : ProofFile.Ground) (hF : ClosingsFirst H.first readers rows stAt Zp Gr) :
    CloseAt 𝕋 b cF Zp l p blk (lotJob readers rows stAt Zp Gr Qc) := by
  have hF' : ClosingsFirst (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.hs readers rows stAt Zp
      Gr := by
    rw [thread_hs h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w]
    exact hF
  exact closeAt_of_first (T := 𝕋) Td hb (thread_bs h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w) readers rows stAt Gr
    hF'

/-- At each link there are numbers and a block at which `CloseAt` holds at the head's thread, given that premise. -/
theorem closeAt_at_head (l : Nat) (hl : l < 25) {b : Nat} (hb : b = 14 * l + (if l = 24 then 9 else 7) + 5)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst) (stAt : StAtOf ProofFile.Inst)
    (Gr : ProofFile.Ground) (hF : ClosingsFirst H.first readers rows stAt Zp Gr) :
    ∃ (p : VerifiableInference.Desc.K9.Where) (Qc : Par) (blk : Block S ProofFile.Cl),
      CloseAt 𝕋 b cF Zp l p blk (lotJob readers rows stAt Zp Gr Qc) := by
  obtain ⟨p, Qc, blk, Td⟩ := tied_at_head h.toAtMg l hl
  exact ⟨p, Qc, blk, closeAt_of_tied h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Td hb readers rows stAt Gr hF⟩

/-! ### It plays -/

/-- **`Plays` holds at each closing's border of the head's thread**, given the premise on the prover's list of
halves. -/
theorem plays_at_head (l : Nat) (hl : l < 25) {b : Nat} (hb : b = 14 * l + (if l = 24 then 9 else 7) + 5)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst) (stAt : StAtOf ProofFile.Inst)
    (Gr : ProofFile.Ground) (hF : ClosingsFirst H.first readers rows stAt Zp Gr) : Plays 𝕋 b := by
  obtain ⟨p, Qc, blk, Hc⟩ :=
    closeAt_at_head h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w l hl hb readers rows stAt Gr hF
  exact close_plays (T := 𝕋) Hc

/-- So does `PlaysS`, the form that is asked from the invariant together with a second condition Said, at every Said. -/
theorem playsS_at_head (l : Nat) (hl : l < 25) {b : Nat} (hb : b = 14 * l + (if l = 24 then 9 else 7) + 5)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst) (stAt : StAtOf ProofFile.Inst)
    (Gr : ProofFile.Ground) (hF : ClosingsFirst H.first readers rows stAt Zp Gr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) : PlaysS 𝕋 Said b :=
  playsS_of 𝕋 Said (plays_at_head h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w l hl hb readers rows stAt Gr hF)

/-! ### It is accepted, under ready -/

/-- **`AcceptedS` holds at a closing's border of the head's thread**, at every Said and fall, given the premise on the
prover's list of halves and ready: the two tests on the record of the verifier's state say yes at the stands, at the
challenges that fit the block's rounds. -/
theorem accepted_of_tied {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block S ProofFile.Cl}
    (Td : Tied cF Zp l p Qc blk) {b : Nat} (hb : b = 14 * l + (if l = 24 then 9 else 7) + 5)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst) (stAt : StAtOf ProofFile.Inst)
    (Gr : ProofFile.Ground) (hF : ClosingsFirst H.first readers rows stAt Zp Gr)
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (fall : Nat → S → List Fmt.Drawn → Option String)
    (ready : ∀ k s m En ds, ThrS 𝕋 Said b k s m En → drawsFit blk.rounds ds = true → fall b s ds = none →
      YesFree.closeShapeB Qc (VerifiableInference.Desc.K9.recOf s) = true ∧
        YesFree.closeValsB (VerifiableInference.Desc.K9.recOf s) (ds.map fun d => (⟨[], d⟩ : Fmt.RoundView)) = true) :
    AcceptedS 𝕋 Said fall b :=
  close_accepted_of_tests (T := 𝕋)
    (closeAt_of_tied h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Td hb readers rows stAt Gr hF) fall
    (thread_front h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w b) ready

/-- The same where ready is one test on the record of the verifier's state, which names no challenge. -/
theorem accepted_base_of_tied {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block S ProofFile.Cl}
    (Td : Tied cF Zp l p Qc blk) {b : Nat} (hb : b = 14 * l + (if l = 24 then 9 else 7) + 5)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst) (stAt : StAtOf ProofFile.Inst)
    (Gr : ProofFile.Ground) (hF : ClosingsFirst H.first readers rows stAt Zp Gr)
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (fall : Nat → S → List Fmt.Drawn → Option String)
    (ready : ∀ k s m En ds, ThrS 𝕋 Said b k s m En → fall b s ds = none →
      YesFree.closeBaseB Qc (VerifiableInference.Desc.K9.recOf s) = true) :
    AcceptedS 𝕋 Said fall b :=
  close_accepted (T := 𝕋)
    (closeAt_of_tied h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Td hb readers rows stAt Gr hF) fall
    (thread_front h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w b) ready

/-- **`AcceptedS` holds at each link's closing**, with ready asked at the numbers and the block that are tied at the
link. -/
theorem accepted_at_head (l : Nat) (hl : l < 25) {b : Nat} (hb : b = 14 * l + (if l = 24 then 9 else 7) + 5)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst) (stAt : StAtOf ProofFile.Inst)
    (Gr : ProofFile.Ground) (hF : ClosingsFirst H.first readers rows stAt Zp Gr)
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (fall : Nat → S → List Fmt.Drawn → Option String)
    (ready : ∀ (p : VerifiableInference.Desc.K9.Where) (Qc : Par) (blk : Block S ProofFile.Cl), Tied cF Zp l p Qc blk →
      ∀ k s m En ds, ThrS 𝕋 Said b k s m En → drawsFit blk.rounds ds = true → fall b s ds = none →
        YesFree.closeShapeB Qc (VerifiableInference.Desc.K9.recOf s) = true ∧
          YesFree.closeValsB (VerifiableInference.Desc.K9.recOf s) (ds.map fun d => (⟨[], d⟩ : Fmt.RoundView)) = true) :
    AcceptedS 𝕋 Said fall b := by
  obtain ⟨p, Qc, blk, Td⟩ := tied_at_head h.toAtMg l hl
  exact accepted_of_tied h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Td hb readers rows stAt Gr hF fall
    (ready p Qc blk Td)

/-- The same at each link where ready is the one test that names no challenge. -/
theorem accepted_base_at_head (l : Nat) (hl : l < 25) {b : Nat}
    (hb : b = 14 * l + (if l = 24 then 9 else 7) + 5) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (rows : RowDataOf ProofFile.Inst) (stAt : StAtOf ProofFile.Inst) (Gr : ProofFile.Ground)
    (hF : ClosingsFirst H.first readers rows stAt Zp Gr)
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (fall : Nat → S → List Fmt.Drawn → Option String)
    (ready : ∀ (p : VerifiableInference.Desc.K9.Where) (Qc : Par) (blk : Block S ProofFile.Cl), Tied cF Zp l p Qc blk →
      ∀ k s m En ds, ThrS 𝕋 Said b k s m En → fall b s ds = none →
        YesFree.closeBaseB Qc (VerifiableInference.Desc.K9.recOf s) = true) :
    AcceptedS 𝕋 Said fall b := by
  obtain ⟨p, Qc, blk, Td⟩ := tied_at_head h.toAtMg l hl
  exact accepted_base_of_tied h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Td hb readers rows stAt Gr hF fall
    (ready p Qc blk Td)

/-! ### From the prover's list of lots -/

/-- `CloseAt` holds at each link, where the prover's list of halves is what a list of lots lays, one of them lays the
lot's halves, and no lot in front of it lays a half at a place of the kind K10. -/
theorem closeAt_of_lots (l : Nat) (hl : l < 25) {b : Nat} (hb : b = 14 * l + (if l = 24 then 9 else 7) + 5)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst) (stAt : StAtOf ProofFile.Inst)
    (Gr : ProofFile.Ground) {Ls Rs : List (HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X)}
    {Lc : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X}
    (hT : H.first = firstOf Zp Gr (Ls ++ Lc :: Rs))
    (hLc : Lc.halves Zp Gr = (seatLotC readers rows stAt).halves Zp Gr)
    (hA : noK10 (firstOf Zp Gr Ls) = true) :
    ∃ (p : VerifiableInference.Desc.K9.Where) (Qc : Par) (blk : Block S ProofFile.Cl),
      CloseAt 𝕋 b cF Zp l p blk (lotJob readers rows stAt Zp Gr Qc) :=
  closeAt_at_head h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w l hl hb readers rows stAt Gr
    (first_of_lots_head h.toAtMg readers rows stAt Gr hT hLc hA)

/-- `Plays` holds at each link under the same three premises. -/
theorem plays_of_lots (l : Nat) (hl : l < 25) {b : Nat} (hb : b = 14 * l + (if l = 24 then 9 else 7) + 5)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst) (stAt : StAtOf ProofFile.Inst)
    (Gr : ProofFile.Ground) {Ls Rs : List (HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X)}
    {Lc : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X}
    (hT : H.first = firstOf Zp Gr (Ls ++ Lc :: Rs))
    (hLc : Lc.halves Zp Gr = (seatLotC readers rows stAt).halves Zp Gr)
    (hA : noK10 (firstOf Zp Gr Ls) = true) : Plays 𝕋 b :=
  plays_at_head h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w l hl hb readers rows stAt Gr
    (first_of_lots_head h.toAtMg readers rows stAt Gr hT hLc hA)

/-- `AcceptedS` holds at each link under the same three premises and ready. -/
theorem accepted_of_lots (l : Nat) (hl : l < 25) {b : Nat} (hb : b = 14 * l + (if l = 24 then 9 else 7) + 5)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst) (stAt : StAtOf ProofFile.Inst)
    (Gr : ProofFile.Ground) {Ls Rs : List (HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X)}
    {Lc : HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X}
    (hT : H.first = firstOf Zp Gr (Ls ++ Lc :: Rs))
    (hLc : Lc.halves Zp Gr = (seatLotC readers rows stAt).halves Zp Gr)
    (hA : noK10 (firstOf Zp Gr Ls) = true)
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (fall : Nat → S → List Fmt.Drawn → Option String)
    (ready : ∀ (p : VerifiableInference.Desc.K9.Where) (Qc : Par) (blk : Block S ProofFile.Cl), Tied cF Zp l p Qc blk →
      ∀ k s m En ds, ThrS 𝕋 Said b k s m En → drawsFit blk.rounds ds = true → fall b s ds = none →
        YesFree.closeShapeB Qc (VerifiableInference.Desc.K9.recOf s) = true ∧
          YesFree.closeValsB (VerifiableInference.Desc.K9.recOf s) (ds.map fun d => (⟨[], d⟩ : Fmt.RoundView)) = true) :
    AcceptedS 𝕋 Said fall b :=
  accepted_at_head h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w l hl hb readers rows stAt Gr
    (first_of_lots_head h.toAtMg readers rows stAt Gr hT hLc hA) fall ready

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.closeAt_of_first
#print axioms ProofFile.Honest.K10.first_of_list_head
#print axioms ProofFile.Honest.K10.first_of_lots_head
#print axioms ProofFile.Honest.K10.first_of_kinds_head
#print axioms ProofFile.Honest.K10.thread_bs
#print axioms ProofFile.Honest.K10.thread_hs
#print axioms ProofFile.Honest.K10.thread_front
#print axioms ProofFile.Honest.K10.closeAt_of_tied
#print axioms ProofFile.Honest.K10.closeAt_at_head
#print axioms ProofFile.Honest.K10.plays_at_head
#print axioms ProofFile.Honest.K10.playsS_at_head
#print axioms ProofFile.Honest.K10.accepted_of_tied
#print axioms ProofFile.Honest.K10.accepted_base_of_tied
#print axioms ProofFile.Honest.K10.accepted_at_head
#print axioms ProofFile.Honest.K10.accepted_base_at_head
#print axioms ProofFile.Honest.K10.closeAt_of_lots
#print axioms ProofFile.Honest.K10.plays_of_lots
#print axioms ProofFile.Honest.K10.accepted_of_lots
