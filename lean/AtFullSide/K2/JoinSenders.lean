-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/JoinSenders.lean: the senders of the kind K1 that a code switch reads, named in the
joined list of jobs.

1. JoinAsks (ExchangeLeft.lean) asks for the records SharedAsks and MaskAsks under "there is" a job,
   a reader and a starting value, at free types. A law on the sender's trees needs more: the very job
   that the joined Script lays.
2. SharedAt and MaskAt: these records at the job that a list holds at a member's number, at the
   Script's own reader wit and own starting value own₀, read at the job's own number of challenges.
3. LaterSenders: the first form at the two later senders of the segment that a switch closes, at
   every switch in front. FirstSenders: the forms at the opening's messages, at the two later
   senders and at the fold's mask, at the switch into the group 1.
4. JoinSenders: both, as one record.
5. firstAsks_of_senders and laterAsks_of_senders: the two limbs of JoinAsks on the senders follow.

This file states forms and proves that the limbs follow from them. It shows none of the forms at any
Script, book or filling.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.LockAsksAtStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K1 (parL noL firstPar gpOf)
open VerifiableInference.Desc.K2.Honest (Left)
open P5J (TS)
open ProofFile.Honest
open ProofFile.Honest.FirstThread (Script)
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Cells Tok Wj Xj : Type}

/-- **SharedAsks at the job that the list holds at the number b.** The record stands at the reader
wit, at own₀, at that job, and at the job's own number of challenges, 0 + roundsTo bs b. cs, e and
dataK stay under "there is": the record's fields pin them. -/
def SharedAt (Zp : ProofFile.Pub) (bs : List (Block S ProofFile.Cl)) (jobs : List (Nat × K1.SendJob Wj Xj))
    (P₀ : VerifiableInference.Desc.K1.Par) (ρ₀ : Nat → Option K1.Ride) (b n ix : Nat)
    (p : SwitchPlace) (k : Coins Bk) (dat : Nat → Nat → Cb.Gl.E)
    (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT) (Vd : Local W₀ Rc Xi Tr → Prop) (N : Nat)
    (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn) (wit : Local W₀ Rc Xi Tr → Wj) (own₀ : Xj) :
    Prop :=
  ∃ x ∈ jobs, x.1 = b ∧ ∃ (cs : Cs (K1.dueR x.2.P x.2.ride)) (e : Ahead)
    (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)),
    SharedAsks Zp bs P₀ ρ₀ b n ix 0 p k dat Q Vd N w hd wit x.2 own₀ cs e dataK (0 + roundsTo bs b)

/-- **MaskAsks at the job that the list holds at the number b**, as SharedAt has it. -/
def MaskAt (Zp : ProofFile.Pub) (bs : List (Block S ProofFile.Cl)) (jobs : List (Nat × K1.SendJob Wj Xj))
    (P₀ : VerifiableInference.Desc.K1.Par) (ρ₀ : Nat → Option K1.Ride) (b n ix : Nat)
    (p : SwitchPlace) (k : Coins Bk) (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT)
    (Vd : Local W₀ Rc Xi Tr → Prop) (N : Nat) (wit : Local W₀ Rc Xi Tr → Wj) (own₀ : Xj) : Prop :=
  ∃ x ∈ jobs, x.1 = b ∧ ∃ (cs : Cs (K1.dueR x.2.P x.2.ride)) (e : Ahead),
    MaskAsks Zp P₀ ρ₀ n ix 0 p k Q Vd N wit x.2 own₀ cs e (0 + roundsTo bs b)

/-- **The two later senders of the segment that the switch p closes**, at each switch p₀ in front
that a switch opened. The text is that of the third limb of JoinAsks, with the job named. -/
def LaterSenders (Zp : ProofFile.Pub) (Bs : ProofFile.PureBase) (cF : Chain TS ProofFile.Cl)
    (jobs : List (Nat × K1.SendJob Wj Xj)) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (p : SwitchPlace) (k : Coins Bk)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries)
    (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT) (Vd : Local W₀ Rc Xi Tr → Prop)
    (w : Local W₀ Rc Xi Tr) (hd ds : List Fmt.Drawn) (wit : Local W₀ Rc Xi Tr → Wj) (own₀ : Xj) :
    Prop :=
  ∀ p₀ ∈ switchPlaces Zp Bs.G₀, p₀.link + 1 = p.link → 1 ≤ p₀.link →
    ∀ (y' : Option (Left × List OnBytes.OracleShape) × Nat) (Sg : SegmentPub),
      closingFrom freshTable (lotOwn (segmentsOf Zp Bs.G₀) p (D w.x) (readers w) hd) hd
        (Stretch.carried p.carries c.2.2) ((segmentsOf Zp Bs.G₀).take (p.link - 1)) 0 0 none =
        .ok y' →
      (segmentsOf Zp Bs.G₀)[p.link - 1]? = some Sg →
      ∀ q, q < 2 → SharedAt Zp cF.blocksInOrder jobs (parL Zp Bs.G₀ (p.link - 1) (q == 1)) (K1.rideOf none)
        (noL (p.link - 1) (q == 1)) 0 (y'.2 + ((Sg.sent.headD #[]).size - 1) + 1 + q) p k
        (lotOwn (segmentsOf Zp Bs.G₀) p (D w.x) (readers w) hd (0 + (p.link - 1))
          ((Sg.sent.headD #[]).size - 1 -
            (if (y'.1.map (·.1)).isSome then 1 + Sg.sizes.kept.length else 0) + q))
        Q Vd (0 + roundsTo cF.blocksInOrder (switchNo p₀)) w (hd ++ ds) wit own₀

/-- **The senders that the switch into the group 1 reads**: the opening's messages in front of the
fold's mask, the two later senders of the first segment, the fold's mask. The text is that of the
field asks of FirstAsks, with the job named: number 2 is the opening's. -/
def FirstSenders (Zp : ProofFile.Pub) (Bs : ProofFile.PureBase) (cF : Chain TS ProofFile.Cl)
    (jobs : List (Nat × K1.SendJob Wj Xj)) (own : Nat → Nat → Nat → Nat → Cb.Gl.E)
    (p : SwitchPlace) (k : Coins Bk) (c : SwitchCoins p.sizes p.others p.foldVars p.carries)
    (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT) (Vd : Local W₀ Rc Xi Tr → Prop) (N : Nat)
    (w : Local W₀ Rc Xi Tr) (hd ds : List Fmt.Drawn) (wit : Local W₀ Rc Xi Tr → Wj) (own₀ : Xj) :
    Prop :=
  ∀ (y' : Option (Left × List OnBytes.OracleShape) × Nat) (Sg : SegmentPub),
    closingFrom freshTable own hd (Stretch.carried p.carries c.2.2)
      ((segmentsOf Zp Bs.G₀).take 0) 0 0 none = .ok y' →
    (segmentsOf Zp Bs.G₀)[0]? = some Sg →
    (∀ n, n < (Sg.sent.headD #[]).size - 1 →
      SharedAt Zp cF.blocksInOrder jobs (firstPar Bs.G₀.first (gpOf Zp))
        (K1.rideOf (K1.firstFold Bs.G₀.first)) 2 n (y'.2 + n) p k
        (dataAtOf Sg (y'.1.map (·.1)) (own (0 + 0)) n) Q Vd N w (hd ++ ds) wit own₀) ∧
    (∀ q, q < 2 → SharedAt Zp cF.blocksInOrder jobs (parL Zp Bs.G₀ 0 (q == 1)) (K1.rideOf none)
      (noL 0 (q == 1)) 0 (y'.2 + ((Sg.sent.headD #[]).size - 1) + 1 + q) p k
      (own (0 + 0) ((Sg.sent.headD #[]).size - 1 -
        (if (y'.1.map (·.1)).isSome then 1 + Sg.sizes.kept.length else 0) + q))
      Q Vd N w (hd ++ ds) wit own₀) ∧
    MaskAt Zp cF.blocksInOrder jobs (firstPar Bs.G₀.first (gpOf Zp))
      (K1.rideOf (K1.firstFold Bs.G₀.first)) 2 ((Sg.sent.headD #[]).size - 1)
      (y'.2 + ((Sg.sent.headD #[]).size - 1)) p k Q Vd N wit own₀

/-- **The senders of the kind K1 at one switch, one input and one list of challenges.** A definition:
the form of a premise. The own data of the field first are read off the written segments, as the
second limb of JoinAsks reads them. -/
structure JoinSenders (Zp : ProofFile.Pub) (Bs : ProofFile.PureBase) (cF : Chain TS ProofFile.Cl)
    (jobs : List (Nat × K1.SendJob Wj Xj)) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (p : SwitchPlace) (k : Coins Bk)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries)
    (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT) (Vd : Local W₀ Rc Xi Tr → Prop)
    (w : Local W₀ Rc Xi Tr) (hd ds : List Fmt.Drawn) (wit : Local W₀ Rc Xi Tr → Wj) (own₀ : Xj) :
    Prop where
  first : p.link = 1 → ∃ N, N ≤ (hd ++ ds).length ∧
    FirstSenders Zp Bs cF jobs (lotOwn segsW p (D w.x) (readers w) hd) p k c Q Vd N w hd ds wit own₀
  later : LaterSenders Zp Bs cF jobs D readers p k c Q Vd w hd ds wit own₀

variable {Zp : ProofFile.Pub} {Bs : ProofFile.PureBase} {cF : Chain TS ProofFile.Cl}
  {jobs : List (Nat × K1.SendJob Wj Xj)} {D : RowDataOf Xi}
  {readers : Local W₀ Rc Xi Tr → Readers} {p : SwitchPlace} {k : Coins Bk}
  {c : SwitchCoins p.sizes p.others p.foldVars p.carries}
  {Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT} {Vd : Local W₀ Rc Xi Tr → Prop}
  {w : Local W₀ Rc Xi Tr} {hd ds : List Fmt.Drawn} {wit : Local W₀ Rc Xi Tr → Wj} {own₀ : Xj}

/-- **The second limb of JoinAsks follows.** -/
theorem firstAsks_of_senders (S₀ : JoinSenders Zp Bs cF jobs D readers p k c Q Vd w hd ds wit own₀)
    (h1 : p.link = 1) :
    ∃ N, FirstAsks (W := Wj) (X := Xj) Zp Bs cF 0 p k c (lotOwn segsW p (D w.x) (readers w) hd) Q Vd
      N w hd ds := by
  obtain ⟨N, hN, A⟩ := S₀.first h1
  refine ⟨N, hN, fun y' Sg hy hS => ?_⟩
  obtain ⟨a1, a2, a3⟩ := A y' Sg hy hS
  refine ⟨fun n hn => ?_, fun q hq => ?_, ?_⟩
  · obtain ⟨x, -, -, cs, e, dataK, B⟩ := a1 n hn
    exact ⟨wit, x.2, own₀, cs, e, dataK, _, B⟩
  · obtain ⟨x, -, -, cs, e, dataK, B⟩ := a2 q hq
    exact ⟨wit, x.2, own₀, cs, e, dataK, _, B⟩
  · obtain ⟨x, -, -, cs, e, B⟩ := a3
    exact ⟨wit, x.2, own₀, cs, e, _, B⟩

/-- **The third limb of JoinAsks follows.** -/
theorem laterAsks_of_senders
    (S₀ : LaterSenders Zp Bs cF jobs D readers p k c Q Vd w hd ds wit own₀) :
    ∀ p₀ ∈ switchPlaces Zp Bs.G₀, p₀.link + 1 = p.link → 1 ≤ p₀.link →
      ∀ (y' : Option (Left × List OnBytes.OracleShape) × Nat) (Sg : SegmentPub),
        closingFrom freshTable (lotOwn (segmentsOf Zp Bs.G₀) p (D w.x) (readers w) hd) hd
          (Stretch.carried p.carries c.2.2) ((segmentsOf Zp Bs.G₀).take (p.link - 1)) 0 0 none =
          .ok y' →
        (segmentsOf Zp Bs.G₀)[p.link - 1]? = some Sg →
        ∀ q, q < 2 → ∃ (wit' : Local W₀ Rc Xi Tr → Wj) (J : K1.SendJob Wj Xj) (own' : Xj)
          (cs : Cs (K1.dueR J.P J.ride)) (e : Ahead)
          (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) (front : Nat),
          SharedAsks Zp cF.blocksInOrder (parL Zp Bs.G₀ (p.link - 1) (q == 1)) (K1.rideOf none)
            (noL (p.link - 1) (q == 1)) 0 (y'.2 + ((Sg.sent.headD #[]).size - 1) + 1 + q) 0 p k
            (lotOwn (segmentsOf Zp Bs.G₀) p (D w.x) (readers w) hd (0 + (p.link - 1))
              ((Sg.sent.headD #[]).size - 1 -
                (if (y'.1.map (·.1)).isSome then 1 + Sg.sizes.kept.length else 0) + q))
            Q Vd (0 + roundsTo cF.blocksInOrder (switchNo p₀)) w (hd ++ ds) wit' J own' cs e dataK front := by
  intro p₀ hp₀ hl h1 y' Sg hy hS q hq
  obtain ⟨x, -, -, cs, e, dataK, B⟩ := S₀ p₀ hp₀ hl h1 y' Sg hy hS q hq
  exact ⟨wit, x.2, own₀, cs, e, dataK, _, B⟩

end AtFullSide.K2

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms AtFullSide.K2.SharedAt
#print axioms AtFullSide.K2.MaskAt
#print axioms AtFullSide.K2.LaterSenders
#print axioms AtFullSide.K2.FirstSenders
#print axioms AtFullSide.K2.JoinSenders
#print axioms AtFullSide.K2.firstAsks_of_senders
#print axioms AtFullSide.K2.laterAsks_of_senders
