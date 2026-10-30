-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Xch/Carry.lean: the item `carry l` of the first chain's table of joints at the
closing of segment l (kind K10), at the first chain's thread under the library's head, where the thread's parameter
carryX is the exact carry (`carryExact`, Johnson/Desc/K2/Honest/Carry/Exact.lean). `ExchangeAtS`
(Honest/Thread/SharesS.lean) at that item is proved as one implication: from a structure of nine named premises,
`CarryDebt`, and one more premise, hShows. None of the ten is shown in this file of any run. hShows is proved in
Xch/ShowsAt.lean; Xch/CarryTop.lean restates the theorem with hShows and len proved, and base derived from two
narrower premises: nine premises are left. One structure; four theorems; three local notations.

The words. A thread is the structure of parameters of one chain's invariant (`Thread`, `Thr`: Honest/Thread/Thr.lean).
The head is the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean), here at the older hash; the head's thread
is the field `thread` of `lettersHead` at its parameters (Honest/Thread/FirstHead.lean). Border b is the position in
the chain before sub-protocol number b; the closing of segment l is sub-protocol number 14 l + `IM.nAt l` + 5.
`StepAt`, `rowWords`, `CoefOf`, `ShownAt`: Xch/Shown.lean. The record of a state s is `K9.recOf s`: what the closing
reads of s. `CloseBase Qc r D` (Johnson/Desc/K10/Honest/Base.lean) lists facts on the record r before the closing that
name none of the closing's challenges. `Tied cF Zp l p Qc blk` (Honest/K10/SimLot.lean): blk is the chain's block at
the closing's number of link l, and Qc are that closing's numbers. The job is `lotJob readers rows stAt Zp Gr Qc`
(Honest/K10/Thr/HalfOfLot.lean): the parameters of the honest prover's part at that closing. The run's witness is
`Sc.wit` at the run's coins, its input and a list of challenges; its words are `wordsFirst`
(Johnson/Desc/Sound/WordsAt.lean) at the state's statement and book. `spentRun`: Honest/K10/Sim.lean; `rowsFit`:
Honest/K10/Job.lean; `handSnd`: Honest/Frame.lean.

What the item says there (`means_carry_at_head`; Carry/Exact.lean). At every value of carryX the sentence of `carry l`
at the head's thread is `carryX l`. At the exact carry it says of the state s' after the closing: the way into the
next code switch (`doorZ`) and that switch's front (`K2.frontAt`) return, and the one claim of the single rows that
the closing has laid is true of what the fold leaves of the witness's own tables. It is false where the way in or the
front refuses.

  `means_carry_at_head`   at every carryX: the sentence of `carry l` at the head's thread is `carryX l`. By
      `mgAll_carry` (Johnson/Desc/Sound/MgAll.lean)
  `stand_at_thr`   at every carryX: wherever the invariant holds at the border before the closing of segment l < 25,
      the verifier's state stands inside an open link. From the invariant's clause on the form (`shapeAt`,
      Johnson/Desc/First/Borders.lean) and the library's `stand_k10` (Johnson/P2LawR/SwitchDoorStand.lean)
  `fill_of_filler`   the filler `stAtZero` at the first state as a function of the whole instance is the filler at the
      first state as a function of the instance's public part, read at that part: the two writings are one, by
      unfolding. So a prover whose lot has the first writing for stAt meets the premise fill
  `CarryDebt`   the nine premises, each with a note on who owes it (below)
  **`exchange_carry_at_head`**   from `CarryDebt` at every p, Qc, blk that `Tied` names at the link, and hShows:
      `ExchangeAtS` at `carry l`, at b = 14 l + `IM.nAt l` + 5, at each l < 25 and every Said

The nine premises. Two are on parameters. half: at each closing's place the first half of the prover's list has the
lot's one part (`ClosingsFirst`, Thr/HalfOfLot.lean). fill: the lot's parameter stAt is the filler at made-up columns
(`stAtZero`, Honest/K10/StAtZero.lean). Seven are asked at every `StepAt` of the closing's block, and nowhere else.
base: `CloseBase` holds of the record at some data D. height: the plan's h is the frame's group's. len: the main
code's message length is 2 ^ logEll of the group's layout. made: at the coins cc that the book gives the part
(`closeCoins`, Honest/K10/Fast/Says.lean), the job's `rows` returns rows R that pass the public test `rowsFit`. tie:
the group's tables made of the witness's words are the tables made of `rowWords` of R. fresh: the witness's table at
the fresh mask's message pairs (`Pairs`, Johnson/Prover/Link/FoldHolds.lean) with the coefficients that the run which
the part spends gives. door: at s' the way in and the front return.

What hShows is. It says that the played rounds show the honest sum and round polynomials at the prover's own rows:
`ShownAt` at the tables of `rowWords` of R and at coefficients of the spent run. Its hypotheses are half, fill,
`Tied`, `StepAt`, `CloseBase`, height, len, the equations for cc and R, `rowsFit`, the played rounds as rB, rE, rR,
and the batched row. It is written out in the theorem's statement. It is the statement of `shows_at_head`
(Xch/ShowsAt.lean) at the exact carry, to the letter but for a bound name; this file does not import that one, and
Xch/CarryTop.lean joins the two.

How the theorem is proved. `exchangeAtS_from` (Xch/From.lean), at no open item, leaves the sentence at the run's
witness. `tied_at_head` (Honest/K10/Wipe/AtHead.lean) names Qc. base gives D. `stepped_behind` (Xch/Behind.lean)
writes out the rounds, the batched row and s'. `moved_close_at` (Xch/Coins.lean) names cc. made gives R; hShows what
the rounds show; tie carries that to the witness's tables; fresh gives the pairing; door the way in and the front.
That the state does not yet stand in the head where the next switch does follows from door and `stand_at_thr`, by the
library's `hH_of_stand` and `putRec_standOf`. That the rows which the test takes in hold of the witness's words is
`says_at_head` (Xch/Says.lean), read off the invariant's open rows. `carryExact_from_front`
(Johnson/Desc/K10/Honest/CarryWords.lean) joins these.

The notations, and the option in front of them. 𝕏 stands for the exact carry at the head's letters, 𝕋 for the head's
thread at a variable carryX, 𝕋X for the head's thread at 𝕏. They declare no new name, neither a definition nor
a theorem: each use is that text, elaborated anew. A field is written with brackets, `(𝕋X).means`: without them Lean
reads `𝕋X.means` as one name. When a notation is declared, Lean looks through its text for names that are not bound,
and that early look has no case for a field access or a named argument. `set_option quotPrecheck false in` turns that
one look off for the one command behind it; it loosens nothing in what Lean checks of a theorem.

Limits. Every field of `CarryDebt` is a premise, and so is hShows: none is shown here of any prover, script, state or
run, and it is not shown that they can be met together. The theorem closes nothing on a run. Each of the seven is
asked at every `StepAt`: where one of them fails at one stand, the theorem says nothing at any stand. fill binds
the theorem to one filler, `stAtZero`: for what is said on laying that filler, see the head of
Honest/K10/StAtZero.lean. base is stronger than what an accepted step gives: an acceptance gives the facts at the one
element that was drawn. Without made the sentence fails in general (argued, not proved): the part never refuses, and
where its data are not made it sends the words at empty tables, the step still accepts, and the single rows' target is
made of what was sent. tie and fresh are premises on the `Script` Sc, a parameter for which no value at the first
chain's lots is written; they are a plain equation and a pairing, not yet in the form `OwnMsgs`
(Honest/Thread/ScriptLots.lean) in which premises on a `Script` are meant to be asked: a lemma from that form to these
two is not written. tie is an equation of functions on all numbers (`Tables`, Johnson/Desc/Means/Says.lean): it also
asks agreement beyond the tables' sizes, which the proof does not spend (argued, not proved: the proof spends tie
inside `msgOf` and `keptVal` alone). At a `Script` that puts zero at the fresh mask's rows, fresh is false at a run
whose polynomial is not zero (argued, not proved). door: of l the sentence reads `ProofFile.pAtK2 Zp l` alone. That these
are a place's numbers and not the dead ones (`ProofFile.deadP2`) is proved by no lemma here; where they are the dead ones,
the sentence speaks of no place of the description. The library has parts of it under this head. The head's field opts
(Johnson/P5J/MgAtAll.lean) says, in its field spots, that the test `spotsB Zp Z.lay` (Johnson/P5J/OptsOk.lean)
accepts: `tableOf Zp.pol Z.lay Zp.KL` returns a table, and `ProofFile.pAtK2? Zp m` answers at every m below that table's
length. `tableWritten_head` (Johnson/Top/H0/K2Ties/AtHead3.lean) says that `tableOf Z.pol Z.lay Z.KL` returns the
written table `tableFullLit`, and `rows25` (Johnson/Top/H0/K2Caller/ClosedAt25.lean) that the written table has 25
rows. These are not called here, and nothing here joins them, or Zp's `pol` and `KL` with Z's. At l = 24 the table of
joints has the item spent by the switch behind the last segment; of that switch's numbers the library also has that
they do not stand in the head's dress (`P1L20.stands24_atAll`, Johnson/P1L20R/Stands24AtAll.lean). The statement is
idle at a border at which the invariant holds at no state and at a step that is not accepted. `ExchangeAtS` is a
definition, meant as a hypothesis of a lemma that gathers a whole chain; it is none of the library's goals. The thread
stands at the exact carry: a lemma that gathers a chain at a thread with another carryX cannot spend the theorem. The
prover H, the book Bk, the further parameters of `lettersHead` (Sc, test, item, n₁, n₂, b₀, Vd, Rd, Kp, w), the lot's
parameters (readers, rows, stAt, Gr) and Said are variables. Whether the head can be had at any files is not shown
here. The full size and the older hash alone. No property of the protocol is claimed: nothing is said on its
soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Xch.From
import Johnson.Desc.ProofFile.Honest.K10.Xch.Says
import Johnson.Desc.ProofFile.Honest.K10.Xch.Behind
import Johnson.Desc.ProofFile.Honest.K10.Xch.Coins
import Johnson.Desc.ProofFile.Honest.K10.Xch.Shown
import Johnson.Desc.ProofFile.Honest.K10.Thr.AtThread
import Johnson.Desc.K10.Honest.CarryWords
import Johnson.P2LawR.SwitchDoorStand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First (Item onAt pubSets)
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.First.K2Caller (doorZ)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.Sound (MsgT mgAll mgBase mgAll_carry wordsFirst)
open OnBytes.Maker (WholeD)
open Johnson.Prover.Link (drawnOf Pairs)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)
open ProofFile.Honest.K10.LeftIs (stageB freshB)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String)

/-! ## At every value of the parameter carryX -/

section
variable (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

-- The first chain's thread under the head. Why the option stands here: this file's head, "The notations, and the
-- option in front of them".
set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- **At the head's thread the sentence of the item `carry l` is the parameter carryX at l.** -/
theorem means_carry_at_head (l : Nat) (u : Local W₀ Rc ProofFile.Inst Tr) (a : ProofFile.InstPub × TS) (y : Strs) (v : WtF) :
    (𝕋).means u (Item.carry l) a y v ↔ carryX l a y v := by
  constructor
  · intro h0
    have h1 : (mgAll { h.𝔇 with decT := fun _ _ => some (Sc.cells u), cr1 := carryX } mgBase).carry l a y v := h0
    rw [mgAll_carry] at h1
    exact h1
  · intro h0
    have h1 : (mgAll { h.𝔇 with decT := fun _ _ => some (Sc.cells u), cr1 := carryX } mgBase).carry l a y v := by
      rw [mgAll_carry]
      exact h0
    exact h1

/-- **Wherever the invariant holds at the border before the closing of segment l < 25, the verifier's state stands
inside an open link.** -/
theorem stand_at_thr (l : Nat) (hl : l < 25) {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr 𝕋 (14 * l + IM.nAt l + 5) k s m En) : ∃ sub, First.standOf s = .link sub := by
  have hT' := hT
  unfold Thr at hT'
  obtain ⟨-, -, hP, -, -, -, -⟩ := hT'
  have hn : s.failed.isNone = true := hP.1
  have hf : s.failed = none := Option.isNone_iff_eq_none.1 hn
  have hF : (𝕋).formP (14 * l + IM.nAt l + 5) (m.st.input.x.pub, s) := hP.2
  have hon : onAt (P5J.At.N Zp cF) (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP P5J.At.links
      P5J.At.ps[14 * l + IM.nAt l + 5]? (P5J.oAt (14 * l + IM.nAt l + 5))
      (((pubSets (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP.more P5J.At.links
        P5J.At.ps)[14 * l + IM.nAt l + 5]?).getD []) (m.st.input.x.pub, s) noStrs := hF
  obtain ⟨p, sub, hp, hs⟩ := P2Notices.stand_k10 hl
  have e2 : LPFK10.ixK10 l = 14 * l + IM.nAt l + 5 := YesFree.number_is l
  rw [e2] at hp
  rcases hon.2 with c | c
  · exact absurd hf c
  · have e := c.1
    simp only [Bool.and_eq_true] at e
    have hh := e.1.1.1.1.1
    rw [hp] at hh
    unfold First.shapeAt at hh
    simp only [Bool.and_eq_true, beq_iff_eq] at hh
    exact ⟨sub, hh.1.1.trans hs⟩

end

/-! ## The filler, in two writings -/

/-- The filler at the first state as a function of the whole instance is the filler at the first state as a function
of the public part, read at the instance's public part. -/
theorem fill_of_filler :
    (stAtZero cF.blocksInOrder fun ξ : ProofFile.Inst => ProofFile.startS Zp ξ.pub) =
      fun ξ : ProofFile.Inst => stAtZero cF.blocksInOrder (ProofFile.startS Zp) ξ.pub := rfl

/-! ## At the exact carry -/

section
variable (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst) (stAt : StAtOf ProofFile.Inst)
  (Gr : ProofFile.Ground) (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

-- The exact carry at the head's letters; the first chain's thread under the head at that value of carryX.
set_option quotPrecheck false in
local notation "𝕏" => (carryExact (P := ProofFile.InstPub) (Cells := CellsM OnBytes.Flat.numsFull) (Tok := P5J.At.Tok) Zp
  (P5J.At.arr Zp))
set_option quotPrecheck false in
local notation "𝕋X" => (lettersHead h H Sc test 𝕏 item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- **Every unpaid premise of the exchange at the item `carry l`, by name.** l: the segment. Qc, blk: the closing's
numbers and block, as `Tied` names them. It is a structure of hypotheses: nothing is claimed of it, and it is shown of
no run. -/
structure CarryDebt (l : Nat) (Qc : Par) (blk : Block TS ProofFile.Cl) : Prop where
  /-- On a parameter, the prover's list of halves: at each closing's place its first half has the lot's one part. Owed
  by whoever fills the prover; `first_of_lots_head` (Honest/K10/Thr/AtThread.lean) has it from three premises on a
  list of lots. -/
  half : ClosingsFirst H.first readers rows stAt Zp Gr
  /-- On a parameter, the lot's stAt: it is the filler at made-up columns, from the chain's own first state. Owed by
  whoever fills the prover. -/
  fill : stAt = fun ξ : ProofFile.Inst => stAtZero cF.blocksInOrder (ProofFile.startS Zp) ξ.pub
  /-- The facts on the record before the closing that name none of its challenges hold, at some data D. Owed by the
  authors of the closing (kind K10): it is near the premise ready of `accepted_base_at_head`
  (Honest/K10/Thr/AtThread.lean): that one asks the test `closeBaseB` at every stand where no fall is named; this one
  asks the facts themselves, at the stands with an accepted step, with no excuse of a fall. -/
  base : ∀ {k s m En ds y cols s'}, StepAt 𝕋X Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
    ∃ D, CloseBase Qc (K9.recOf s) D
  /-- The plan's h at the closing is the h of the frame's group. Owed by the authors of the closing, with base: no
  fact of `CloseBase` reads the plan's h. -/
  height : ∀ {k s m En ds y cols s'}, StepAt 𝕋X Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
    ∀ {D}, CloseBase Qc (K9.recOf s) D → Qc.h = D.Gq.h
  /-- The main code's message length is 2 ^ logEll of the group's layout. Owed by the authors of the closing;
  `hlen_of_lengthsOk` (Johnson/Desc/K10/Honest/CloseLen.lean) has it from the program's test on the lengths of the
  state's codes. -/
  len : ∀ {k s m En ds y cols s'}, StepAt 𝕋X Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
    ∀ {D}, CloseBase Qc (K9.recOf s) D →
      2 ^ (Own.layoutOf (K9.recOf s).st D.G).logEll =
        ((D.S1 (K9.recOf s)).codes.base.getD (K9.recOf s).frame.shape.code default).ell
  /-- At the coins that the book gives the part, the job's rows are made and pass the public test. Owed by the authors
  of the closing together with those of the code switch (kind K2), whose text makes the rows. Without it the part
  sends the words at empty tables. -/
  made : ∀ {k s m En ds y cols s'}, StepAt 𝕋X Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
    ∀ {D}, CloseBase Qc (K9.recOf s) D → ∀ {cc},
      closeCoins (V := Local W₀ Rc ProofFile.Inst Tr) (X := X) Bk (Bk.rowsOf (𝕋X).chain) (k.look (𝕋X).chain) blk.place
        (lotJob readers rows stAt Zp Gr Qc) = .ok cc →
      ∃ R, (lotJob readers rows stAt Zp Gr Qc).rows m.st.input m.st.heard (handSnd cc).2.2 = .ok R ∧
        rowsFit s.st D.G R = true
  /-- On the `Script`: the group's tables made of the witness's words are the tables made of the prover's own rows.
  Owed by whoever writes the `Script` and by the kinds that send the group's members (K1, K2); meant to be derived
  from `OwnMsgs` at the members' numbers by a lemma that the authors of the closing owe. An equation of functions on
  all numbers: it also asks agreement beyond the tables' sizes, which the proof does not spend (argued, not proved).
  -/
  tie : ∀ {k s m En ds y cols s'}, StepAt 𝕋X Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
    ∀ {D}, CloseBase Qc (K9.recOf s) D → ∀ {cc},
      closeCoins (V := Local W₀ Rc ProofFile.Inst Tr) (X := X) Bk (Bk.rowsOf (𝕋X).chain) (k.look (𝕋X).chain) blk.place
        (lotJob readers rows stAt Zp Gr Qc) = .ok cc →
      ∀ {R}, (lotJob readers rows stAt Zp Gr Qc).rows m.st.input m.st.heard (handSnd cc).2.2 = .ok R →
      rowsFit s.st D.G R = true → ∀ ds',
      OnBytes.Means.tablesOf (D.S1 (K9.recOf s)) (Own.layoutOf (K9.recOf s).st D.G)
          (wordsFirst (P5J.At.arr Zp) s.st s.book (Sc.wit k m.st.input (m.st.heard ++ (ds ++ ds')))) =
        OnBytes.Means.tablesOf (D.S1 (K9.recOf s)) (Own.layoutOf (K9.recOf s).st D.G) (rowWords D (K9.recOf s) R)
  /-- On the `Script`: the witness's table at the fresh mask's message pairs with the coefficients of the run that the
  part spends. Owed by whoever writes the `Script` and by the kind that sends the fresh mask (K1 at segment 0, else
  K2), whose law on that sending it needs. -/
  fresh : ∀ {k s m En ds y cols s'}, StepAt 𝕋X Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
    ∀ {D}, CloseBase Qc (K9.recOf s) D → ∀ {cc},
      closeCoins (V := Local W₀ Rc ProofFile.Inst Tr) (X := X) Bk (Bk.rowsOf (𝕋X).chain) (k.look (𝕋X).chain) blk.place
        (lotJob readers rows stAt Zp Gr Qc) = .ok cc →
      ∀ ds' W, CoefOf (spentRun (lotJob readers rows stAt Zp Gr Qc) (handSnd cc)) W →
      Pairs (stageB D (K9.recOf s)) (stageB D (K9.recOf s)).Z.l W
        (freshB D (K9.recOf s)
          (wordsFirst (P5J.At.arr Zp) s.st s.book (Sc.wit k m.st.input (m.st.heard ++ (ds ++ ds')))))
  /-- At the state after the closing the way into the next code switch and that switch's front return. Public: it
  reads no witness. Owed by the authors of the code switch (kind K2), carried back from the switch's own border to the
  closing's. -/
  door : ∀ {k s m En ds y cols s'}, StepAt 𝕋X Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
    ∃ t fx, doorZ Zp l s' = some t ∧ First.K2.frontAt (ProofFile.pAtK2 Zp l) t = some fx

/-- **From the nine named premises and hShows: `ExchangeAtS` holds at the item `carry l` at the closing of segment
l**, at the head's thread at the exact carry, for each l < 25 and every Said. -/
theorem exchange_carry_at_head (l : Nat) (hl : l < 25) {b : Nat} (hb : b = 14 * l + IM.nAt l + 5)
    (Dt : ∀ p Qc blk, Tied cF Zp l p Qc blk →
      CarryDebt h H Sc test item n₁ n₂ b₀ Vd Rd Kp w readers rows stAt Gr Said l Qc blk)
    (hShows : ClosingsFirst H.first readers rows stAt Zp Gr →
      stAt = (fun ξ : ProofFile.Inst => stAtZero cF.blocksInOrder (ProofFile.startS Zp) ξ.pub) →
      ∀ {p Qc blk}, Tied cF Zp l p Qc blk → ∀ {k s m En ds y cols s'},
      StepAt 𝕋X Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
      ∀ {D}, CloseBase Qc (K9.recOf s) D → Qc.h = D.Gq.h →
      2 ^ (Own.layoutOf (K9.recOf s).st D.G).logEll =
        ((D.S1 (K9.recOf s)).codes.base.getD (K9.recOf s).frame.shape.code default).ell →
      ∀ {cc},
      closeCoins (V := Local W₀ Rc ProofFile.Inst Tr) (X := X) Bk (Bk.rowsOf (𝕋X).chain) (k.look (𝕋X).chain) blk.place
        (lotJob readers rows stAt Zp Gr Qc) = .ok cc →
      ∀ {R}, (lotJob readers rows stAt Zp Gr Qc).rows m.st.input m.st.heard (handSnd cc).2.2 = .ok R →
      rowsFit s.st D.G R = true →
      ∀ {rB rE rR row}, roundsOf y.1 = rB :: rE :: rR →
      Own.batch (D.S1 (K9.recOf s)) (K9.recOf s).frame.group
        ⟨Own.layoutOf (K9.recOf s).st D.G, OnBytes.Slice.runRows (K9.recOf s).st D.G⟩ (drawnOf rB) = some row →
      ∃ W, CoefOf (spentRun (lotJob readers rows stAt Zp Gr Qc) (handSnd cc)) W ∧
        ShownAt D (K9.recOf s) row rE rR
          (OnBytes.Means.tablesOf (D.S1 (K9.recOf s)) (Own.layoutOf (K9.recOf s).st D.G)
            (rowWords D (K9.recOf s) R)) W) :
    ExchangeAtS 𝕋X Said b (Item.carry l) := by
  subst hb
  refine exchangeAtS_from 𝕋X Said [] (fun j hj => by cases hj) ?_
  intro blk hblk k s m En ds y cols s' ds' hA hd hS _
  obtain ⟨p, Qc, blk', Td'⟩ := tied_at_head h.toAtMg l hl
  have e1 : cF.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk := hblk
  have e2 : cF.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk' := Td'.2.2.1
  have eb : blk' = blk := Option.some.inj (e2.symm.trans e1)
  have Td : Tied cF Zp l p Qc blk := by
    rw [← eb]
    exact Td'
  have St : StepAt 𝕋X Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' := ⟨hA, hd, hS⟩
  have Db := Dt p Qc blk Td
  obtain ⟨D, Hb⟩ := Db.base St
  obtain ⟨rB, rE, rR, row, hrs, hlr, hsh, hrow, hs₁, -⟩ := stepped_behind 𝕋X Td Hb hS
  have Hc := closeAt_of_tied h H Sc test 𝕏 item n₁ n₂ b₀ Vd Rd Kp w Td (b := 14 * l + IM.nAt l + 5) rfl readers rows
    stAt Gr Db.half
  obtain ⟨-, -, -, -, -, -, hr, ho⟩ := Hc.tied
  obtain ⟨_, _, _, cc, hcc, _⟩ :=
    moved_close_at 𝕋X (lotJob readers rows stAt Zp Gr Qc) blk hr ho Hc.halfAt k m En ds y cols hd hS.1
  obtain ⟨R, hR, hfit⟩ := Db.made St Hb hcc
  have hlen := Db.len St Hb
  obtain ⟨W, hW, hσ, γ, hSh⟩ :=
    hShows Db.half Db.fill Td St Hb (Db.height St Hb) hlen hcc hR hfit hrs hrow
  rw [← Db.tie St Hb hcc hR hfit ds'] at hSh
  have hP := Db.fresh St Hb hcc ds' W hW
  obtain ⟨t, fx, hdo, hfr⟩ := Db.door St
  obtain ⟨sub, hst⟩ := stand_at_thr h H Sc test 𝕏 item n₁ n₂ b₀ Vd Rd Kp w l hl hA.1
  have hst' : First.standOf s' = .link sub := by
    rw [hs₁]
    exact (First.putRec_standOf _ _).trans hst
  have hH := P2Notices.hH_of_stand hst' hdo
  have hs := says_at_head h H Sc test 𝕏 item n₁ n₂ b₀ Vd Rd Kp w Said l hl hA Hb (ds ++ ds')
  have e := LeftIs.carryExact_from_front (Cl := Unit) Zp (P5J.At.arr Zp) l m.st.input.x.pub s
    ((𝕋X).strs (En.add y.1)) (Sc.wit k m.st.input (m.st.heard ++ (ds ++ ds'))) Hb rB rE rR [] hlr hsh hrow s' hs₁ hH
    hdo hfr hlen hs W γ hP hσ hSh
  have e' : (𝕋X).means m.st.input (Item.carry l) (m.st.input.x.pub, s') ((𝕋X).strs (En.add y.1))
      (Sc.wit k m.st.input (m.st.heard ++ (ds ++ ds'))) :=
    (means_carry_at_head h H Sc test 𝕏 item n₁ n₂ b₀ Vd Rd Kp w l m.st.input _ _ _).2 e
  exact e'

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.means_carry_at_head
#print axioms ProofFile.Honest.K10.stand_at_thr
#print axioms ProofFile.Honest.K10.fill_of_filler
#print axioms ProofFile.Honest.K10.CarryDebt
#print axioms ProofFile.Honest.K10.exchange_carry_at_head
