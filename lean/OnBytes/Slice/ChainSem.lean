-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ChainSem.lean: the rounds after the link's fifth, taken off in one chain, with all
claims in the field.

The link is the format's protocol between two stored tables. After its first five rounds come the
batching, a fold, a code switch, a second fold, a second code switch and the base case. For each
kind of block a theorem takes its rounds off: if the claim before the block has no witness, the
prover has lost (the library's `Doomed`, Iop/Rbr.lean), provided that it has lost in what follows
whenever the claim after the block has no witness (OnBytes/Slice/BatSem.lean, FoldPeel.lean,
BlockCs.lean, Base.lean). In these theorems the claim after a block is a closed form in the field,
made from the claim before it and from the values that the written rounds hold. No function of a
verifier's text is in them. This file composes the closed forms into one predicate on the written
rounds, `SemAccept`, and joins the blocks: whatever verdict says yes only where `SemAccept` holds
and all tests of work pass, the prover has lost towards its no.

So a verifier's text has to be looked at once, in one direction: its yes implies `SemAccept`.

What `SemAccept` asks, in words. The verifier holds one linear claim at a time: a target and
coefficients on the tables that a tree commits to. "BAT" makes the first claim: the link's rows
under the powers of a drawn element. A fold ("FOLD epsilon", then a "FOLD round" for each row
variable) takes a claim on many rows to a claim on three folded rows, by a sumcheck whose round
polynomials the prover sends. A code switch ("SEND seed", "CS") takes that claim to the tables that
the next tree commits to, and adds rows that tie these tables to the old tree's symbols at drawn
positions. None of these steps tests anything: each says what the next claim is. The base case
("BASE lambda", "BASE") tests the last claim: the prover shows a masked message in the clear, the
claim must hold of it, and its code word must agree with the last tree at drawn positions.

Main definitions.
 `Reads`       how written oracles and messages are read in the field: the rows that are batched, as
               a function of what the verifier holds after the fifth round; the words of the three
               trees; the two messages of the base case. The chain holds for every such record with
               the two properties named below.
 `Claims`      the claims that the verifier holds, one after each step.
 `SemSteps`    the protocol's equations on such claims, one clause a step, under the names that the
               format gives its rounds.
 `SemAccept`   there are claims that meet the equations.
 `foldNext`, `csNextW`   the claim after a fold and after a code switch, from the claim before it.
 `claimBat`, `claimFold1`, `claimCs1`, `claimFold2`, `claimCs2`, `wordFold1`, `wordFold2`   the
               claims and the folded words, written out.
 `BatSem`, `FoldSem`, `CsSem`, `BaseSem`   what the four kinds of block say, as statements.
 `tailSh`      the shape of all these rounds.
Main theorems.
 `semAccept_iff`   the equations leave no choice: `SemAccept` is the base case's test at `claimCs2`.
 `batSem_of`, `foldSem_of`, `csSem_of`, `baseSem_of`   the blocks' theorems give these statements.
 `chain_sem`     the chain, towards any predicate that holds wherever a test of work fails or
                 `SemAccept` fails.
 `chain_sem_acc` the same for a verdict.
What is asked of the record: its rows are the link's rows on every entry that a member of the group
has (`IsRows`), and the first tree's word holds the written symbols (`WordTie`).
Not claimed here. That any verifier's yes implies `SemAccept`. No record of readings is built here (OnBytes/Slice/SemLib.lean has one). Nothing on
the sizes of the error counts.
The rows must not depend on the rounds after the fifth: the batching's theorem takes them as fixed
before its round.
-/
import OnBytes.Slice.BatSem
import OnBytes.Slice.FoldPeel
import OnBytes.Slice.BlockCs
import OnBytes.Slice.Base
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Run

/-! ## What the written rounds hold, in the field -/

/-- The element that a written round draws (the first, if it draws more; 0 if it draws none). -/
abbrev drawnE (d : PQ.RD) (c : (wRound d).Chal) : GE := gOne _ (valsOf d c)

/-- The rounds of a fold at the stage s: one round "FOLD epsilon", then one round "FOLD round" for
each of the stage's h + g row variables. -/
abbrev foldRds (s : Sg) (dE dT : PQ.RD) : List PQ.RD := dE :: List.replicate (s.h + s.g) dT

/-- The point that the rounds "FOLD round" of a fold draw: one coordinate a round. -/
def foldPt (s : Sg) (dE dT : PQ.RD) (τ : Tr (PQ.uL (ckP .two) (foldRds s dE dT))) :
    Fin (s.h + s.g) → GE := ptF dT _ τ.2.2

/-! ## The claim after a block, from the claim before it -/

/-- The claim after a fold, from the claim q before it and the written rounds. The round "FOLD
epsilon" sends an element μ and draws ε; the running claim begins as μ + (target of q) * ε. Each
round "FOLD round" sends two coefficients of a polynomial of degree 2, whose values at 0 and 1 add
up to the running claim, and draws a coordinate; the running claim becomes the polynomial's value
there (`claimF`). The last running claim is the new target. The new coefficients (`midVec`): on the
folded main row, the main rows' coefficients folded at the drawn point, times ε; on the folded
carried mask row, the mask rows' coefficients folded at the point's first h coordinates, times ε and
the product of the later g coordinates; on the folded fresh mask row, the public weights of the
hiding polynomial at the point. -/
def foldNext (s : Sg) (n0 : ℕ) (dE dT : PQ.RD) (q : GE × (s.cIn.J → GE))
    (τ : Tr (PQ.uL (ckP .two) (foldRds s dE dT))) : GE × (s.cMid.J → GE) :=
  (claimF dT _ (sentAt dE τ.1 0 + q.1 * drawnE dE τ.2.1) τ.2.2,
    midVec s n0 q.2 (drawnE dE τ.2.1) (foldPt s dE dT τ))

/-- The claim after a code switch, from the claim q and the word y before it and the two
written rounds. The round "SEND seed" sends the next tree and draws the seed of its sample. The
round "CS" sends the answer to the sample and draws positions of the old tree and an element θ. The
new claim is the sum, under the powers of θ, of: the old claim, carried to the new tables; the
sample with its answer; and, for each drawn position, three rows which say that the new tables hold
messages whose code words have the symbols of y there (`csNext`, written out in
OnBytes/Slice/CsSim.lean: `csNext_fst`, `csNext_snd`). -/
def csNextW {s s' : Sg} (hf : CsFit s s') (dS dC : PQ.RD) (q : GE × (s.cMid.J → GE))
    (y : s.cMid.Word) (τ : Tr (PQ.uL (ckP .two) [dS, dC])) : GE × (s'.cIn.J → GE) :=
  csNext hf q.1 q.2 y (gSeed s'.st.na _ (valsOf dS τ.2.1)) ((ansOf dC τ.2.2.1).getD 0 0)
    (gCs s.C.a s.t _ (valsOf dC τ.2.2.2.1))

/-! ## The readings -/

/-- How written oracles and messages are read in the field. A word of a stage has, at each
position of the stage's tree, one symbol for each row of the stage's tables. -/
structure Reads (S : Sz) (t₀ : ℕ) (s2 s3 : Sg) (d2 dS2 dS3 dL dB : PQ.RD) where
  /-- The rows that "BAT" combines, from what the verifier holds after the link's five rounds: the
  target of row number b, and its coefficients on the first stage's tables. -/
  rows : S.lk.X4 → (ℕ → GE) × (ℕ → (S.sg t₀).cIn.J → GE)
  /-- The number of entries of a mask row on which the first fold's hiding polynomial has
  weights. -/
  n1 : ℕ
  /-- The same number for the second fold. -/
  n2 : ℕ
  /-- The first tree, sent in the link's second round: the word of its main rows and of the mask
  rows that are carried. -/
  w1 : (wRound d2).Orc → (S.sg t₀).cIn.Word
  /-- The first tree: the word of the fresh mask rows, which carry the first fold's hiding
  polynomial. -/
  z1 : (wRound d2).Orc → (S.sg t₀).cFr.Word
  /-- The second tree, sent in the first "SEND seed": main rows and carried mask rows. -/
  w2 : (wRound dS2).Msg → s2.cIn.Word
  /-- The second tree: the fresh mask rows, which carry the second fold's hiding polynomial. -/
  z2 : (wRound dS2).Msg → s2.cFr.Word
  /-- The third tree, sent in the second "SEND seed": the word of the last message. -/
  w3 : (wRound dS3).Msg → s3.cIn.Word
  /-- The third tree: the masking word of the base case. -/
  g3 : (wRound dS3).Msg → s3.cIn.Word
  /-- The element that "BASE lambda" sends: what the claim's form gives on the masking word's
  message. -/
  fu : (wRound dL).Msg → GE
  /-- What "BASE" sends in the clear: a message and tails of the last stage's code. -/
  fs : (wRound dB).Msg → s3.cIn.MR

/-! ## The yes, in the field -/

/-- The claims that the verifier holds, one after each step. A claim on tables is a target and
a vector of coefficients: it says that the coefficients times the tables' entries give the
target. -/
structure Claims (S : Sz) (t₀ : ℕ) (s2 s3 : Sg) where
  /-- after "BAT": a claim on the first stage's tables -/
  bat : GE × ((S.sg t₀).cIn.J → GE)
  /-- after the first "FOLD epsilon": the running claim -/
  eps1 : GE
  /-- after the first stage's rounds "FOLD round": a claim on the three folded rows -/
  fold1 : GE × ((S.sg t₀).cMid.J → GE)
  /-- after the first "CS": a claim on the second stage's tables -/
  cs1 : GE × (s2.cIn.J → GE)
  /-- after the second "FOLD epsilon": the running claim -/
  eps2 : GE
  /-- after the second stage's rounds "FOLD round": a claim on the three folded rows -/
  fold2 : GE × (s2.cMid.J → GE)
  /-- after the second "CS": a claim on the last stage's tables -/
  cs2 : GE × (s3.cIn.J → GE)

section
variable {S : Sz} {t₀ : ℕ} {s2 s3 : Sg} {d2 dS2 dS3 dL dB : PQ.RD}
  (R : Reads S t₀ s2 s3 d2 dS2 dS3 dL dB) (hf1 : CsFit (S.sg t₀) s2) (hf2 : CsFit s2 s3)
  (dA dE1 dT1 dC1 dE2 dT2 dC2 : PQ.RD)
  (x : S.lk.X4) (o2 : (wRound d2).Orc) (cA : (wRound dA).Chal)
  (τF1 : Tr (PQ.uL (ckP .two) (foldRds (S.sg t₀) dE1 dT1)))
  (τC1 : Tr (PQ.uL (ckP .two) [dS2, dC1]))
  (τF2 : Tr (PQ.uL (ckP .two) (foldRds s2 dE2 dT2)))
  (τC2 : Tr (PQ.uL (ckP .two) [dS3, dC2]))
  (τB : Tr (PQ.uL (ckP .two) [dL, dB]))

/-- The equations of the protocol, step by step, under the names that the format gives its
rounds. x: what the verifier holds after the link's five rounds. o2: the first tree. cA: the
verifier message of "BAT". τF1, τC1, τF2, τC2, τB: the written rounds of the first fold, the first
code switch, the second fold, the second code switch and the base case. Every step but the last two
says what the next claim is. The last two are the tests. -/
structure SemSteps (q : Claims S t₀ s2 s3) : Prop where
  /-- "BAT" draws θ. The claim is the sum of the rows under the powers of θ. For a record that meets
  `IsRows` the rows are: one equality row, two sample rows, and one row for each column read of the
  two stored tables (OnBytes/Slice/RowsX.lean gives them in the field). -/
  bat : q.bat = sumStm S t₀ (R.rows x).1 (R.rows x).2 (drawnE dA cA)
  /-- "FOLD epsilon" sends μ and draws ε. The running claim is μ + target * ε. -/
  eps1 : q.eps1 = sentAt dE1 τF1.1 0 + q.bat.1 * drawnE dE1 τF1.2.1
  /-- "FOLD round", once for each row variable. The round sends the constant and the quadratic
  coefficient of a polynomial of degree 2; its linear coefficient is the one with which the values
  at 0 and 1 add up to the running claim. The running claim becomes the polynomial's value at the
  drawn coordinate. The last one is the new target. -/
  round1 : q.fold1.1 = claimF dT1 _ q.eps1 τF1.2.2
  /-- The coefficients on the three folded rows. On the folded main row: the main rows'
  coefficients folded at the drawn point, times ε. On the folded carried mask row: the mask rows'
  coefficients folded at the point's first h coordinates, times ε and the product of the later g
  coordinates. On the folded fresh mask row: the public weights of the hiding polynomial at the
  point. -/
  form1 : q.fold1.2 =
    midVec (S.sg t₀) R.n1 q.bat.2 (drawnE dE1 τF1.2.1) (foldPt (S.sg t₀) dE1 dT1 τF1)
  /-- "SEND seed" sends the second tree and draws the seed of its sample. "CS" sends the answer and
  draws positions of the first tree and θ. The claim on the second stage's tables is the sum under
  the powers of θ of the carried claim, the sample, and three rows for each drawn position, whose
  targets are the first tree's symbols there, folded at the drawn point. Target and coefficients are
  written out in OnBytes/Slice/CsSim.lean: `csNext_fst`, `csNext_snd`. -/
  cs1 : q.cs1 = csNextW hf1 dS2 dC1 q.fold1
    (foldWords (S.sg t₀) (R.w1 o2) (R.z1 o2) (foldPt (S.sg t₀) dE1 dT1 τF1)) τC1
  /-- "FOLD epsilon" of the second stage. -/
  eps2 : q.eps2 = sentAt dE2 τF2.1 0 + q.cs1.1 * drawnE dE2 τF2.2.1
  /-- "FOLD round" of the second stage. -/
  round2 : q.fold2.1 = claimF dT2 _ q.eps2 τF2.2.2
  /-- The coefficients on the second stage's three folded rows, as at the first stage. -/
  form2 : q.fold2.2 = midVec s2 R.n2 q.cs1.2 (drawnE dE2 τF2.2.1) (foldPt s2 dE2 dT2 τF2)
  /-- "SEND seed" and "CS" of the second stage: the claim on the last stage's tables. -/
  cs2 : q.cs2 = csNextW hf2 dS3 dC2 q.fold2
    (foldWords s2 (R.w2 τC1.1) (R.z2 τC1.1) (foldPt s2 dE2 dT2 τF2)) τC2
  /-- "BASE lambda" sends u and draws λ; "BASE" sends a message and tails in the clear. First test:
  the claim's coefficients times that message give u + λ * target. -/
  baseLin : ∑ j, q.cs2.2 j * (R.fs τB.2.2.1).1 j = R.fu τB.1 + drawnE dL τB.2.1 * q.cs2.1
  /-- "BASE" draws positions. Second test, at each of them: the code word of what was sent in the
  clear has the masking word's symbols plus λ times the last message's symbols. -/
  basePos : ∀ i, ldCw s3.cIn (R.fs τB.2.2.1) (gPos s3.C.a s3.t _ (valsOf dB τB.2.2.2.1) i) =
    s3.cIn.T (R.g3 τC2.1) (gPos s3.C.a s3.t _ (valsOf dB τB.2.2.2.1) i) +
      drawnE dL τB.2.1 • s3.cIn.T (R.w3 τC2.1) (gPos s3.C.a s3.t _ (valsOf dB τB.2.2.2.1) i)

/-- The yes, in the field: there are claims that meet the protocol's equations. The equations
leave no choice of the claims (`semAccept_iff`). -/
def SemAccept : Prop :=
  ∃ q : Claims S t₀ s2 s3,
    SemSteps R hf1 hf2 dA dE1 dT1 dC1 dE2 dT2 dC2 x o2 cA τF1 τC1 τF2 τC2 τB q

/-! ## The claims, written out -/

/-- The claim after "BAT". -/
def claimBat : GE × ((S.sg t₀).cIn.J → GE) :=
  sumStm S t₀ (R.rows x).1 (R.rows x).2 (drawnE dA cA)

/-- The claim after the first fold. -/
def claimFold1 : GE × ((S.sg t₀).cMid.J → GE) :=
  foldNext (S.sg t₀) R.n1 dE1 dT1 (claimBat R dA x cA) τF1

/-- The three folded words after the first fold. -/
def wordFold1 : (S.sg t₀).cMid.Word :=
  foldWords (S.sg t₀) (R.w1 o2) (R.z1 o2) (foldPt (S.sg t₀) dE1 dT1 τF1)

/-- The claim after the first code switch. -/
def claimCs1 : GE × (s2.cIn.J → GE) :=
  csNextW hf1 dS2 dC1 (claimFold1 R dA dE1 dT1 x cA τF1) (wordFold1 R dE1 dT1 o2 τF1) τC1

/-- The claim after the second fold. -/
def claimFold2 : GE × (s2.cMid.J → GE) :=
  foldNext s2 R.n2 dE2 dT2 (claimCs1 R hf1 dA dE1 dT1 dC1 x o2 cA τF1 τC1) τF2

/-- The three folded words after the second fold. -/
def wordFold2 : s2.cMid.Word :=
  foldWords s2 (R.w2 τC1.1) (R.z2 τC1.1) (foldPt s2 dE2 dT2 τF2)

/-- The claim after the second code switch. -/
def claimCs2 : GE × (s3.cIn.J → GE) :=
  csNextW hf2 dS3 dC2 (claimFold2 R hf1 dA dE1 dT1 dC1 dE2 dT2 x o2 cA τF1 τC1 τF2)
    (wordFold2 R dC1 dE2 dT2 τC1 τF2) τC2

/-- The yes in the field is the library's base test at the last claim, written out. -/
theorem semAccept_iff :
    SemAccept R hf1 hf2 dA dE1 dT1 dC1 dE2 dT2 dC2 x o2 cA τF1 τC1 τF2 τC2 τB ↔
      LdwAccept (ldCw s3.cIn)
        (ldForm (Slf.idf (E := GE) (J := s3.cIn.J))
          (claimCs2 R hf1 hf2 dA dE1 dT1 dC1 dE2 dT2 dC2 x o2 cA τF1 τC1 τF2 τC2))
        (claimCs2 R hf1 hf2 dA dE1 dT1 dC1 dE2 dT2 dC2 x o2 cA τF1 τC1 τF2 τC2).1
        (s3.cIn.T (R.w3 τC2.1)) (s3.cIn.T (R.g3 τC2.1)) (R.fu τB.1) (drawnE dL τB.2.1)
        (R.fs τB.2.2.1) (gPos s3.C.a s3.t _ (valsOf dB τB.2.2.2.1)) := by
  constructor
  · rintro ⟨q, h⟩
    have e0 : q.bat = claimBat R dA x cA := h.bat
    have e1 : q.fold1 = claimFold1 R dA dE1 dT1 x cA τF1 :=
      Prod.ext (by rw [h.round1, h.eps1, e0]; rfl) (by rw [h.form1, e0]; rfl)
    have e2 : q.cs1 = claimCs1 R hf1 dA dE1 dT1 dC1 x o2 cA τF1 τC1 := by
      rw [h.cs1, e1]
      rfl
    have e3 : q.fold2 = claimFold2 R hf1 dA dE1 dT1 dC1 dE2 dT2 x o2 cA τF1 τC1 τF2 :=
      Prod.ext (by rw [h.round2, h.eps2, e2]; rfl) (by rw [h.form2, e2]; rfl)
    have e4 : q.cs2 = claimCs2 R hf1 hf2 dA dE1 dT1 dC1 dE2 dT2 dC2 x o2 cA τF1 τC1 τF2 τC2 := by
      rw [h.cs2, e3]
      rfl
    rw [← e4]
    exact ⟨h.baseLin, h.basePos⟩
  · intro h
    exact ⟨⟨claimBat R dA x cA, _, claimFold1 R dA dE1 dT1 x cA τF1,
      claimCs1 R hf1 dA dE1 dT1 dC1 x o2 cA τF1 τC1, _,
      claimFold2 R hf1 dA dE1 dT1 dC1 dE2 dT2 x o2 cA τF1 τC1 τF2,
      claimCs2 R hf1 hf2 dA dE1 dT1 dC1 dE2 dT2 dC2 x o2 cA τF1 τC1 τF2 τC2⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h.1, h.2⟩⟩

end

/-! ## The four blocks, as statements in the field -/

/-- The batching is taken off, with the error count εa. -/
def BatSem (S : Sz) (t₀ e : ℕ) (d2 dA : PQ.RD) (εa : ℕ) : Prop :=
  ∀ (t : Shape) (εt : Err t) (o : (wRound d2).Orc) (f : (S.sg t₀).cIn.Word),
    WordTie S t₀ d2 o f →
    ∀ x : S.lk.X4, (∀ w, ¬ S.lk.j4.cf.relR (x, wordsOf S d2 o) w) →
    ∀ (tg : ℕ → GE) (vs : ℕ → (S.sg t₀).cIn.J → GE), IsRows S t₀ x tg vs →
    ∀ bad : Tr (wRound dA :: t) → Prop,
    (∀ m c τ, GChal.pass (b := dA.entry.work) c = false → bad (m, c, τ)) →
    (∀ (m : (wRound dA).Msg) (c : (wRound dA).Chal),
      (∀ w, ¬ (S.sg t₀).RIn e (sumStm S t₀ tg vs (gOne _ (valsOf dA c)), f) w) →
      Doomed t εt fun b => bad (m, c, b)) →
    Doomed (wRound dA :: t) (εa, εt) bad

/-- A fold is taken off, with the error counts εf. -/
def FoldSem (s : Sg) (n0 e : ℕ) (dE dT : PQ.RD)
    (εf : Err (PQ.uL (ckP .two) (foldRds s dE dT))) : Prop :=
  ∀ (t : Shape) (εt : Err t) (q : GE × (s.cIn.J → GE)) (y : s.cIn.Word) (z : s.cFr.Word),
    (∀ w, ¬ s.RIn e (q, y) w) →
    ∀ bad : Tr (PQ.uL (ckP .two) (foldRds s dE dT) ++ t) → Prop,
    (∀ τ b, PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τ) = false → bad (Tr.app τ b)) →
    (∀ τ : Tr (PQ.uL (ckP .two) (foldRds s dE dT)),
      (∀ w, ¬ s.RMid e (foldNext s n0 dE dT q τ, foldWords s y z (foldPt s dE dT τ)) w) →
      Doomed t εt fun b => bad (Tr.app τ b)) →
    Doomed _ (Err.app εf εt) bad

/-- A code switch is taken off, with the error counts εc. -/
def CsSem {s s' : Sg} (hf : CsFit s s') (e e' : ℕ) (dS dC : PQ.RD)
    (εc : Err (PQ.uL (ckP .two) [dS, dC])) : Prop :=
  ∀ (t : Shape) (εt : Err t) (q : GE × (s.cMid.J → GE)) (y : s.cMid.Word)
    (fW : (wRound dS).Msg → s'.cIn.Word),
    (∀ w, ¬ s.RMid e (q, y) w) →
    ∀ bad : Tr (PQ.uL (ckP .two) [dS, dC] ++ t) → Prop,
    (∀ τ b, PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τ) = false → bad (Tr.app τ b)) →
    (∀ τ : Tr (PQ.uL (ckP .two) [dS, dC]),
      (∀ w, ¬ s'.RIn e' (csNextW hf dS dC q y τ, fW τ.1) w) →
      Doomed t εt fun b => bad (Tr.app τ b)) →
    Doomed _ (Err.app εc εt) bad

/-- The base case is taken off, with the error counts εb. -/
def BaseSem (s : Sg) (e : ℕ) (dL dB : PQ.RD) (εb : Err (PQ.uL (ckP .two) [dL, dB])) : Prop :=
  ∀ (q : GE × (s.cIn.J → GE)) (f g : s.cIn.Word) (fu : (wRound dL).Msg → GE)
    (fs : (wRound dB).Msg → s.cIn.MR),
    (∀ w, ¬ s.RIn e (q, f) w) →
    ∀ bad : Tr (PQ.uL (ckP .two) [dL, dB]) → Prop,
    (∀ τ, PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τ) = false → bad τ) →
    (∀ τ : Tr (PQ.uL (ckP .two) [dL, dB]),
      ¬ LdwAccept (ldCw s.cIn) (ldForm (Slf.idf (E := GE) (J := s.cIn.J)) q) q.1 (s.cIn.T f)
        (s.cIn.T g) (fu τ.1) (gOne _ (valsOf dL τ.2.1)) (fs τ.2.2.1)
        (gPos s.C.a s.t _ (valsOf dB τ.2.2.2.1)) → bad τ) →
    Doomed _ εb bad

/-! ## The four blocks' theorems give these statements -/

/-- The batching. -/
theorem batSem_of (S : Sz) (t₀ e d L : ℕ) (hk : SemOK S e d) (hL : (S.sg t₀).cIn.ListAt e L)
    (d2 dA : PQ.RD) (hA : SendsDraws dA 0 1 0 0) : BatSem S t₀ e d2 dA (batErr S L dA) :=
  fun t εt o f hf x hno tg vs hr bad hp H =>
    bat_block_sem S t₀ e d L hk hL d2 dA hA t εt o f hf x hno tg vs hr bad hp H

/-- A fold. -/
theorem foldSem_of (s : Sg) (n0 d e : ℕ) (Lst mC mS mW : ℕ → ℕ)
    (hC : Spec.CodesOK GE s.Ps s.cM s.cZ s.cZ d e) (hE : (s.par 0).ErrOK e Lst mC mS mW)
    (dE dT : PQ.RD) (hR : FoldRounds dE dT) :
    FoldSem s n0 e dE dT (foldErr s dE dT Lst mC mS mW) :=
  fun t εt q y z hno bad hp H =>
    fold_block_sem s n0 d e Lst mC mS mW hC hE dE dT hR t εt q.1 q.2 y z hno bad hp
      fun m c τ h => H (m, c, τ) h

/-- A code switch. -/
theorem csSem_of {s s' : Sg} (hf : CsFit s s') (e e' L : ℕ) (hlaws : s.cMid.Laws)
    (hlist : s'.cIn.ListAt e' L) (dS dC : PQ.RD) (hr : CsRounds s s' dS dC) :
    CsSem hf e e' dS dC (csErr hf e L dS dC) :=
  fun t εt q y fW hno bad hp H =>
    cs_block_sem hf e e' L hlaws hlist dS dC hr t εt q.1 q.2 y fW hno bad
      (fun m c τ h => hp (m, c, τ.1, τ.2.1, ()) τ.2.2
        (by simp only [PQ.passSL, PQ.rhoSL, h, Bool.false_and]))
      (fun m1 c1 m c b h => hp (m1, c1, m, c, ()) b
        (by simp only [PQ.passSL, PQ.rhoSL, h, Bool.false_and, Bool.and_false]))
      fun m1 c1 m2 c2 h => H (m1, c1, m2, c2, ()) h

/-- The base case. -/
theorem baseSem_of (s : Sg) (e exc L2 : ℕ) (dL dB : PQ.RD) {nL aL nB : ℕ}
    (hc : BaseCodes s e exc L2) (hL : SendsDraws dL nL 1 0 aL)
    (hB : SendsDraws dB nB 0 s.t s.C.a) : BaseSem s e dL dB (baseErr s e exc L2 dL dB) :=
  fun q f g fu fs hno bad hp H =>
    base_block_sem s e exc L2 dL dB hc hL hB q f g fu fs hno bad hp
      fun m1 c1 m2 c2 h => H (m1, c1, m2, c2, ()) h

/-! ## The chain -/

/-- A transcript of two shapes joined is two transcripts joined. -/
theorem exists_app {s t : Shape} (τ : Tr (s ++ t)) : ∃ a b, τ = Tr.app (s := s) a b :=
  ⟨Tr.fst τ, Tr.snd (s := s) τ, (Tr.app_fst_snd τ).symm⟩

section
variable {S : Sz} {t₀ : ℕ} {s2 s3 : Sg} {d2 dS2 dS3 dL dB : PQ.RD}
  (R : Reads S t₀ s2 s3 d2 dS2 dS3 dL dB) (hf1 : CsFit (S.sg t₀) s2) (hf2 : CsFit s2 s3)
  (dA dE1 dT1 dC1 dE2 dT2 dC2 : PQ.RD)

/-- The shape of the rounds after the link's fifth: the batching, then fold, switch, fold, switch,
base case. -/
abbrev tailSh (S : Sz) (t₀ : ℕ) (s2 : Sg) (dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB : PQ.RD) :
    Shape :=
  wRound dA :: (PQ.uL (ckP .two) (foldRds (S.sg t₀) dE1 dT1) ++ (PQ.uL (ckP .two) [dS2, dC1] ++
    (PQ.uL (ckP .two) (foldRds s2 dE2 dT2) ++ (PQ.uL (ckP .two) [dS3, dC2] ++
      PQ.uL (ckP .two) [dL, dB]))))

/-- The chain, in the field. If the statement after the link's fifth round has no witness, the
prover has lost in the rounds that follow, towards any predicate that holds wherever a test of work
fails and wherever `SemAccept` fails. Asked: the six blocks' statements, with the error counts of
the conclusion, and `IsRows` and `WordTie` of the record. -/
theorem chain_sem (e1 e2 e3 εa : ℕ)
    (εf1 : Err (PQ.uL (ckP .two) (foldRds (S.sg t₀) dE1 dT1)))
    (εc1 : Err (PQ.uL (ckP .two) [dS2, dC1])) (εf2 : Err (PQ.uL (ckP .two) (foldRds s2 dE2 dT2)))
    (εc2 : Err (PQ.uL (ckP .two) [dS3, dC2])) (εb : Err (PQ.uL (ckP .two) [dL, dB]))
    (hBat : BatSem S t₀ e1 d2 dA εa) (hF1 : FoldSem (S.sg t₀) R.n1 e1 dE1 dT1 εf1)
    (hC1 : CsSem hf1 e1 e2 dS2 dC1 εc1) (hF2 : FoldSem s2 R.n2 e2 dE2 dT2 εf2)
    (hC2 : CsSem hf2 e2 e3 dS3 dC2 εc2) (hB : BaseSem s3 e3 dL dB εb)
    (hrows : ∀ x, IsRows S t₀ x (R.rows x).1 (R.rows x).2)
    (hw1 : ∀ o, WordTie S t₀ d2 o (R.w1 o))
    (x : S.lk.X4) (o2 : (wRound d2).Orc)
    (hno : ∀ w, ¬ S.lk.j4.cf.relR (x, wordsOf S d2 o2) w)
    (bad : Tr (tailSh S t₀ s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB) → Prop)
    (hp : ∀ mA cA τF1 τC1 τF2 τC2 τB,
      (GChal.pass (b := dA.entry.work) cA && PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τF1) &&
        PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τC1) &&
        PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τF2) &&
        PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τC2) &&
        PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τB)) = false →
      bad (mA, cA, Tr.app τF1 (Tr.app τC1 (Tr.app τF2 (Tr.app τC2 τB)))))
    (H : ∀ mA cA τF1 τC1 τF2 τC2 τB,
      ¬ SemAccept R hf1 hf2 dA dE1 dT1 dC1 dE2 dT2 dC2 x o2 cA τF1 τC1 τF2 τC2 τB →
      bad (mA, cA, Tr.app τF1 (Tr.app τC1 (Tr.app τF2 (Tr.app τC2 τB))))) :
    Doomed (tailSh S t₀ s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB)
      (εa, Err.app εf1 (Err.app εc1 (Err.app εf2 (Err.app εc2 εb)))) bad := by
  refine hBat _ _ o2 (R.w1 o2) (hw1 o2) x hno _ _ (hrows x) bad ?_ ?_
  · intro mA cA τ hc
    obtain ⟨τF1, τ, rfl⟩ := exists_app τ
    obtain ⟨τC1, τ, rfl⟩ := exists_app τ
    obtain ⟨τF2, τ, rfl⟩ := exists_app τ
    obtain ⟨τC2, τB, rfl⟩ := exists_app τ
    exact hp mA cA τF1 τC1 τF2 τC2 τB (by simp [hc])
  intro mA cA h0
  refine hF1 _ _ _ (R.w1 o2) (R.z1 o2) h0 (fun b => bad (mA, cA, b)) ?_ ?_
  · intro τF1 τ hc
    obtain ⟨τC1, τ, rfl⟩ := exists_app τ
    obtain ⟨τF2, τ, rfl⟩ := exists_app τ
    obtain ⟨τC2, τB, rfl⟩ := exists_app τ
    exact hp mA cA τF1 τC1 τF2 τC2 τB (by simp [hc])
  intro τF1 h1
  refine hC1 _ _ _ _ R.w2 h1 (fun b => bad (mA, cA, Tr.app τF1 b)) ?_ ?_
  · intro τC1 τ hc
    obtain ⟨τF2, τ, rfl⟩ := exists_app τ
    obtain ⟨τC2, τB, rfl⟩ := exists_app τ
    exact hp mA cA τF1 τC1 τF2 τC2 τB (by simp [hc])
  intro τC1 h2
  refine hF2 _ _ _ (R.w2 τC1.1) (R.z2 τC1.1) h2
    (fun b => bad (mA, cA, Tr.app τF1 (Tr.app τC1 b))) ?_ ?_
  · intro τF2 τ hc
    obtain ⟨τC2, τB, rfl⟩ := exists_app τ
    exact hp mA cA τF1 τC1 τF2 τC2 τB (by simp [hc])
  intro τF2 h3
  refine hC2 _ _ _ _ R.w3 h3 (fun b => bad (mA, cA, Tr.app τF1 (Tr.app τC1 (Tr.app τF2 b)))) ?_ ?_
  · intro τC2 τB hc
    exact hp mA cA τF1 τC1 τF2 τC2 τB (by simp [hc])
  intro τC2 h4
  refine hB _ (R.w3 τC2.1) (R.g3 τC2.1) R.fu R.fs h4
    (fun b => bad (mA, cA, Tr.app τF1 (Tr.app τC1 (Tr.app τF2 (Tr.app τC2 b))))) ?_ ?_
  · intro τB hc
    exact hp mA cA τF1 τC1 τF2 τC2 τB (by simp [hc])
  · intro τB hacc
    exact H mA cA τF1 τC1 τF2 τC2 τB fun h =>
      hacc ((semAccept_iff R hf1 hf2 dA dE1 dT1 dC1 dE2 dT2 dC2 x o2 cA τF1 τC1 τF2 τC2 τB).1 h)

/-- The chain, for a verdict. Let acc be any verdict on the rounds after the link's fifth. If a
yes of acc has all tests of work passed and gives the yes in the field, the prover has lost towards
a no of acc, provided that the statement after the fifth round has no witness. Asked besides: what
`chain_sem` asks of the blocks and of the record. -/
theorem chain_sem_acc (e1 e2 e3 εa : ℕ)
    (εf1 : Err (PQ.uL (ckP .two) (foldRds (S.sg t₀) dE1 dT1)))
    (εc1 : Err (PQ.uL (ckP .two) [dS2, dC1])) (εf2 : Err (PQ.uL (ckP .two) (foldRds s2 dE2 dT2)))
    (εc2 : Err (PQ.uL (ckP .two) [dS3, dC2])) (εb : Err (PQ.uL (ckP .two) [dL, dB]))
    (hBat : BatSem S t₀ e1 d2 dA εa) (hF1 : FoldSem (S.sg t₀) R.n1 e1 dE1 dT1 εf1)
    (hC1 : CsSem hf1 e1 e2 dS2 dC1 εc1) (hF2 : FoldSem s2 R.n2 e2 dE2 dT2 εf2)
    (hC2 : CsSem hf2 e2 e3 dS3 dC2 εc2) (hB : BaseSem s3 e3 dL dB εb)
    (hrows : ∀ x, IsRows S t₀ x (R.rows x).1 (R.rows x).2)
    (hw1 : ∀ o, WordTie S t₀ d2 o (R.w1 o))
    (x : S.lk.X4) (o2 : (wRound d2).Orc)
    (hno : ∀ w, ¬ S.lk.j4.cf.relR (x, wordsOf S d2 o2) w)
    (acc : Tr (tailSh S t₀ s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB) → Bool)
    (hacc : ∀ mA cA τF1 τC1 τF2 τC2 τB,
      acc (mA, cA, Tr.app τF1 (Tr.app τC1 (Tr.app τF2 (Tr.app τC2 τB)))) = true →
      (GChal.pass (b := dA.entry.work) cA && PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τF1) &&
        PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τC1) &&
        PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τF2) &&
        PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τC2) &&
        PQ.passSL (ckP .two) _ (PQ.rhoSL (ckP .two) _ τB)) = true ∧
      SemAccept R hf1 hf2 dA dE1 dT1 dC1 dE2 dT2 dC2 x o2 cA τF1 τC1 τF2 τC2 τB) :
    Doomed (tailSh S t₀ s2 dA dE1 dT1 dS2 dC1 dE2 dT2 dS3 dC2 dL dB)
      (εa, Err.app εf1 (Err.app εc1 (Err.app εf2 (Err.app εc2 εb)))) fun b => acc b = false := by
  refine chain_sem R hf1 hf2 dA dE1 dT1 dC1 dE2 dT2 dC2 e1 e2 e3 εa εf1 εc1 εf2 εc2 εb hBat hF1 hC1
    hF2 hC2 hB hrows hw1 x o2 hno _ ?_ ?_
  · intro mA cA τF1 τC1 τF2 τC2 τB hp
    refine Bool.eq_false_iff.2 fun h => ?_
    rw [(hacc mA cA τF1 τC1 τF2 τC2 τB h).1] at hp
    cases hp
  · intro mA cA τF1 τC1 τF2 τC2 τB hs
    exact Bool.eq_false_iff.2 fun h => hs (hacc mA cA τF1 τC1 τF2 τC2 τB h).2

end

end OnBytes.Slice

#print axioms OnBytes.Slice.semAccept_iff
#print axioms OnBytes.Slice.batSem_of
#print axioms OnBytes.Slice.foldSem_of
#print axioms OnBytes.Slice.csSem_of
#print axioms OnBytes.Slice.baseSem_of
#print axioms OnBytes.Slice.chain_sem
#print axioms OnBytes.Slice.chain_sem_acc
