-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Xch/CarryTop.lean: the exchange at the item `carry l` at the closing of segment l
(kind K10), at the first chain's thread under the library's head at the exact carry, from one structure of nine named
premises, `CarryOwed`, alone. It stands over `exchange_carry_at_head` (Xch/Carry.lean). Of that theorem's ten premises
it proves hShows, by `shows_at_head` (Xch/ShowsAt.lean), and the field len of `CarryDebt`, and it derives the field
base from two narrower premises, by `closeBase_at_stepped` (Xch/BaseAt.lean): nine premises are left. With the
exchange at `pinKept l` (Xch/PinKept.lean), from the same nine premises at all 25 closings, it gives the exchange at
every item that a closing's row owes. One structure; four theorems; three local notations.

The words are those of the head of Xch/Carry.lean: a thread, the head, a border, `StepAt`, the record `K9.recOf s`,
`CloseBase`, `Tied`, the job, the run's witness and its words, and what the item says at the exact carry.

  `len_at_thr`   at a block that `Tied` names (Td): wherever the invariant holds at the border before the closing of
      segment l and `CloseBase` holds of the record: the main code's message length is 2 ^ logEll of the group's
      layout. The state's codes are the head's (`facts_at_thr`, Xch/BaseAt.lean), the program's test on the codes'
      lengths accepts these (`P5J.AtMgA.three`, Johnson/P5J/K03OneOwnAt.lean), and `hlen_of_lengthsOk`
      (Johnson/Desc/K10/Honest/CloseLen.lean) does the rest. At every value of the thread's parameter carryX
  `CarryOwed`   the nine premises that are left, each with a note on who owes it: `CarryDebt` without base and len,
      with terms and mask
  `carryDebt_of_owed`   at a block that `Tied` names: `CarryOwed` gives `CarryDebt`
  **`exchange_carry_top`**   from `CarryOwed` at every p, Qc, blk that `Tied` names at the link: `ExchangeAtS`
      (Honest/Thread/SharesS.lean) at `carry l`, at b = 14 l + `IM.nAt l` + 5, at each l < 25 and every Said
  **`exchange_owes_top`**   from `CarryOwed` at all l < 25: `ExchangeAtS` at every item that the row of a closing
      owes, stated with the unused extra hypothesis of `exchange_of_two` (Xch/RowAt.lean). By `exchange_of_carry`
      (Xch/PinKept.lean)

The nine premises. On parameters: half, fill. At every `StepAt` of the closing's block, and nowhere else: terms, mask,
height, made, tie, fresh, door. Seven are the fields of `CarryDebt` of the same names, the same types, sign for sign;
the head of Xch/Carry.lean says what each is. terms: every structured vector among the terms on a main table, of every
row that the proximity test on the group takes in, is in order (`Tensor.ok`): the field termsOk of `CloseBase`. mask:
the group's mask code is the one that the frame's shape names: the field maskCode of `CloseBase`. height, made, tie
and fresh are asked at every D at which `CloseBase` holds, so they serve at the D that `closeBase_at_stepped` returns.

The notations, and the option in front of them. 𝕏 stands for the exact carry at the head's letters, 𝕋 for the head's
thread at a variable carryX, 𝕋X for the head's thread at 𝕏. They declare no new name, neither a definition nor
a theorem: each use is that text, elaborated anew. A field is written with brackets, `(𝕋X).row`: without them Lean reads
`𝕋X.row` as one name. When a notation is declared, Lean looks through its text for names that are not bound, and that
early look has no case for a field access or a named argument. `set_option quotPrecheck false in` turns that one look
off for the one command behind it; it loosens nothing in what Lean checks of a theorem.

Limits. None of the nine fields of `CarryOwed` is shown of a run: each is a premise, shown here of no prover, script
or state, and it is not shown that the nine can be met together. The two main theorems are implications and close
nothing on a run. Each of the seven is asked at every `StepAt`: where one of them fails at one stand of a closing,
`exchange_carry_top` says nothing at any stand of that closing, and `exchange_owes_top` says nothing at all. fill
binds both to one filler, `stAtZero`: for what is said on laying that filler, see the head of
Honest/K10/StAtZero.lean. Where made fails, the sentence of `carry l` is not claimed: the prover's part never refuses,
and where its data are not made it falls back on the words at empty tables, the step still accepts, and the single
rows' target is made of what was sent, so that the sentence fails in general (argued, not proved). tie and fresh are
premises on the `Script` Sc, a parameter for which no value at the first chain's lots is written; they are a plain
equation and a pairing, not yet in the form `OwnMsgs` (Honest/Thread/ScriptLots.lean); at a `Script` that puts zero at
the fresh mask's rows, fresh is false at a run whose polynomial is not zero (argued, not proved). tie is an equation
of functions on all numbers (`Tables`, Johnson/Desc/Means/Says.lean): it also asks agreement beyond the tables' sizes,
which the proof does not spend (argued, not proved: the proof spends tie inside `msgOf` and `keptVal` alone). door: of
l the sentence reads `ProofFile.pAtK2 Zp l` alone. That these are a place's numbers and not the dead ones (`ProofFile.deadP2`) is
proved by no lemma here; where they are the dead ones, the sentence speaks of no place of the description: a sentence
that no code switch could spend. The library has parts of it under this head. The head's field opts
(Johnson/P5J/MgAtAll.lean) says, in its field spots, that the test `spotsB Zp Z.lay` (Johnson/P5J/OptsOk.lean)
accepts: `tableOf Zp.pol Z.lay Zp.KL` returns a table, and `ProofFile.pAtK2? Zp m` answers at every m below that table's
length. `tableWritten_head` (Johnson/Top/H0/K2Ties/AtHead3.lean) says that `tableOf Z.pol Z.lay Z.KL` returns the
written table `tableFullLit`, and `rows25` (Johnson/Top/H0/K2Caller/ClosedAt25.lean) that the written table has 25
rows. These are not called here, and nothing here joins them, or Zp's `pol` and `KL` with Z's. At l = 24 the table of
joints has the item spent by the switch behind the last segment; of that switch's numbers the library also has that
they do not stand in the head's dress (`P1L20.stands24_atAll`, Johnson/P1L20R/Stands24AtAll.lean). By its text
(`finishFrontQ`, Johnson/Top/H0/Tw/K2C/Finish.lean) the way in there asks, among other things, that the frame stands
behind the last link and that the state bears no mark; that it returns is the premise door, and nothing of it is shown
here. terms and mask are derived neither from the invariant nor from the acceptance (the head of Xch/BaseAt.lean says
what the library has near them). The statements are idle at a border at which the invariant holds at no state and at a
step that is not accepted; at l = 24 the part of `exchange_owes_top` on `pinKept 24` says nothing
(`means_pinKept_last`, Xch/PinKept.lean). `ExchangeAtS` is a definition, meant as a hypothesis of a lemma that gathers
a whole chain; it is none of the library's goals. The thread stands at the exact carry: a lemma that gathers a chain
at a thread with another carryX cannot spend these theorems. The prover H, the book Bk, the further parameters of
`lettersHead` (Sc, test, item, n₁, n₂, b₀, Vd, Rd, Kp, w), the lot's parameters (readers, rows, stAt, Gr) and Said are
variables. Whether the head can be had at any files is not shown here. The full size and the older hash alone. No
property of the protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Xch.Carry
import Johnson.Desc.ProofFile.Honest.K10.Xch.ShowsAt
import Johnson.Desc.ProofFile.Honest.K10.Xch.BaseAt
import Johnson.Desc.ProofFile.Honest.K10.Xch.PinKept
import Johnson.Desc.K10.Honest.CloseLen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.First.K2Caller (doorZ)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.Sound (MsgT wordsFirst)
open OnBytes.Maker (WholeD)
open Johnson.Prover.Link (Pairs)
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

/-! ## The main code's message length, at every value of the parameter carryX -/

section
variable (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

-- The first chain's thread under the head. Why the option stands here: this file's head, "The notations, and the
-- option in front of them".
set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- **At a block that `Tied` names: wherever the invariant holds at the border before the closing of segment l and
`CloseBase` holds of the record, the main code's message length is 2 ^ logEll of the group's layout.** -/
theorem len_at_thr {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}
    (Td : Tied cF Zp l p Qc blk)
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr 𝕋 (14 * l + IM.nAt l + 5) k s m En) {D : BaseData} (Hb : CloseBase Qc (K9.recOf s) D) :
    2 ^ (Own.layoutOf (K9.recOf s).st D.G).logEll =
      ((D.S1 (K9.recOf s)).codes.base.getD (K9.recOf s).frame.shape.code default).ell := by
  have hblk : cF.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk := Td.2.2.1
  have hb : 14 * l + IM.nAt l + 5 ≤ cF.blocksInOrder.length := Nat.le_of_lt (List.getElem?_eq_some_iff.1 hblk).1
  obtain ⟨-, hc, -, -⟩ := facts_at_thr h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT
  have hC : s.st.codes.lengthsOk = true := by
    rw [hc]
    exact h.three.1
  exact LeftIs.hlen_of_lengthsOk Hb hC

end

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

/-- **Every premise of the exchange at the item `carry l` that is still unpaid, by name.** l: the segment. Qc, blk:
the closing's numbers and block, as `Tied` names them. It is a structure of hypotheses: nothing is claimed of it, and
it is shown of no run. -/
structure CarryOwed (l : Nat) (Qc : Par) (blk : Block TS ProofFile.Cl) : Prop where
  /-- On a parameter, the prover's list of halves: at each closing's place its first half has the lot's one part. Owed
  by whoever fills the prover; `first_of_lots_head` (Honest/K10/Thr/AtThread.lean) has it from three premises on a
  list of lots. -/
  half : ClosingsFirst H.first readers rows stAt Zp Gr
  /-- On a parameter, the lot's stAt: it is the filler at made-up columns, from the chain's own first state. Owed by
  whoever fills the prover; `fill_of_filler` (Xch/Carry.lean) has it at the filler's other writing. -/
  fill : stAt = fun ξ : ProofFile.Inst => stAtZero cF.blocksInOrder (ProofFile.startS Zp) ξ.pub
  /-- Every structured vector among the terms on a main table, of every row that the test on the group takes in, is in
  order. Owed by the authors of all kinds that lay such rows (the code switch K2, the one equation K9, the sendings K1
  with their sample rows): it would be a new clause of an invariant along the chain. -/
  terms : ∀ {k s m En ds y cols s'}, StepAt 𝕋X Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
    ∀ G, (K9.recOf s).st.groups[(K9.recOf s).frame.group]? = some G →
      ∀ q ∈ (OnBytes.Slice.runRows (K9.recOf s).st G).toList, ∀ u ∈ q.terms.toList, u.part = .main → u.v.ok = true
  /-- The group's mask code is the one that the frame's shape names. Owed by the authors of the closing: the library
  has the group's two codes through its sentence on the members' shapes, at a stronger sense of "reached" than the
  invariant gives. -/
  mask : ∀ {k s m En ds y cols s'}, StepAt 𝕋X Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
    ∀ G, (K9.recOf s).st.groups[(K9.recOf s).frame.group]? = some G → G.maskCode = (K9.recOf s).frame.shape.maskCode
  /-- The plan's h at the closing is the h of the frame's group. Owed by the authors of the closing: no fact of
  `CloseBase` reads the plan's h. -/
  height : ∀ {k s m En ds y cols s'}, StepAt 𝕋X Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
    ∀ {D}, CloseBase Qc (K9.recOf s) D → Qc.h = D.Gq.h
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

/-- At a block that `Tied` names, the nine premises that are left give the nine of `CarryDebt`. -/
theorem carryDebt_of_owed {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}
    (Td : Tied cF Zp l p Qc blk)
    (O : CarryOwed h H Sc test item n₁ n₂ b₀ Vd Rd Kp w readers rows stAt Gr Said l Qc blk) :
    CarryDebt h H Sc test item n₁ n₂ b₀ Vd Rd Kp w readers rows stAt Gr Said l Qc blk where
  half := O.half
  fill := O.fill
  base := fun St =>
    closeBase_at_stepped h H Sc test 𝕏 item n₁ n₂ b₀ Vd Rd Kp w Td St.thr.1 St.step (O.terms St) (O.mask St)
  height := O.height
  len := fun St _ Hb => len_at_thr h H Sc test 𝕏 item n₁ n₂ b₀ Vd Rd Kp w Td St.thr.1 Hb
  made := O.made
  tie := O.tie
  fresh := O.fresh
  door := O.door

/-- **From the nine premises that are left: `ExchangeAtS` holds at the item `carry l` at the closing of segment l**,
at the head's thread at the exact carry, for each l < 25 and every Said. -/
theorem exchange_carry_top (l : Nat) (hl : l < 25) {b : Nat} (hb : b = 14 * l + IM.nAt l + 5)
    (Ow : ∀ p Qc blk, Tied cF Zp l p Qc blk →
      CarryOwed h H Sc test item n₁ n₂ b₀ Vd Rd Kp w readers rows stAt Gr Said l Qc blk) :
    ExchangeAtS 𝕋X Said b (Item.carry l) :=
  exchange_carry_at_head h H Sc test item n₁ n₂ b₀ Vd Rd Kp w readers rows stAt Gr Said l hl hb
    (fun p Qc blk Td =>
      carryDebt_of_owed h H Sc test item n₁ n₂ b₀ Vd Rd Kp w readers rows stAt Gr Said Td (Ow p Qc blk Td))
    (shows_at_head h H Sc test 𝕏 item n₁ n₂ b₀ Vd Rd Kp w readers rows stAt Gr Said l hl)

/-- **From these premises at all 25 closings: `ExchangeAtS` holds at every item that a closing's row owes**, stated
with the unused extra hypothesis of `exchange_of_two`. -/
theorem exchange_owes_top
    (Ow : ∀ l, l < 25 → ∀ p Qc blk, Tied cF Zp l p Qc blk →
      CarryOwed h H Sc test item n₁ n₂ b₀ Vd Rd Kp w readers rows stAt Gr Said l Qc blk) :
    ∀ l, l < 25 → ∀ j : Item, j ∈ ((𝕋X).row (14 * l + IM.nAt l + 5)).owes →
      (j ∈ (𝕋X).opened (14 * l + IM.nAt l + 5) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ P5J.parts4 → j ≠ Item.constr m q) →
      ExchangeAtS 𝕋X Said (14 * l + IM.nAt l + 5) j :=
  exchange_of_carry h H Sc test 𝕏 item n₁ n₂ b₀ Vd Rd Kp w Said fun l hl =>
    exchange_carry_top h H Sc test item n₁ n₂ b₀ Vd Rd Kp w readers rows stAt Gr Said l hl rfl (Ow l hl)

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.len_at_thr
#print axioms ProofFile.Honest.K10.CarryOwed
#print axioms ProofFile.Honest.K10.carryDebt_of_owed
#print axioms ProofFile.Honest.K10.exchange_carry_top
#print axioms ProofFile.Honest.K10.exchange_owes_top
