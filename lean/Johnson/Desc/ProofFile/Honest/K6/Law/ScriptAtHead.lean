-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/ScriptAtHead.lean: THE OUTPUT HEAD'S OWN ROUNDS: A MEMBER OF
K6Script (Law/OutAtThread.lean) AT THE FIRST CHAIN'S THREAD AT THE LIBRARY'S HEAD, BORDER 341, UNDER
THE LIBRARY'S HYPOTHESIS h AND FOURTEEN NAMED PREMISES, OF WHICH SIX ARE TYPED BY NOBODY.
WHAT IT IS NOT. CONDITIONAL THROUGHOUT: NO FIELD OF K6HeadDebts IS SHOWN HERE OF ANY RUN, ANY PROVER
OR ANY PUBLIC DATA; whether they can be met together is not known. It joins: every field of K6Script
is another theorem, called; no new mathematics. That the thread holds at any border is shown
nowhere. THE LAST THEOREM STANDS, THROUGH Law/PlanesAtHead.lean, OVER A FILE OF OTHER AUTHORS THAT
IS A READING COPY AND HAS NOT BEEN HANDED IN (Honest/K3/Law/Total/PlanesAt341MgAll.lean). At the
full size and the format's second hash function alone, as h. The small input is headWit'
(Honest/K6/Wit.lean) at two readers that are letters: no trace of any model is named. Seven further
letters (o, d, rowOf, own, base, cnt, free) are free: whoever pays names them. Nothing on chance.
Nothing on whether the verifier accepts a proof, on soundness, on completeness or on what a proof
hides. No example.
THE FOURTEEN FIELDS OF K6HeadDebts, BY WHAT IS KNOWN OF EACH TO THIS FILE'S AUTHOR; each field's
docstring says it again. "Typed by nobody": no Lean text that ends in the premise's form, at these
letters or at general ones, is known to it. A premise for which lemmas are compiled while its answer
at the sizes is only printed or evaluated stands in the second class. TYPED BY NOBODY (six): index,
points, guests, cellsOn, reader, within. PRINTED OR EVALUATED, NOT PROVED (three; their authors' own
words are in Law/MaskAtHead.lean's head): stretch, room, fence. TYPED BY THEIR AUTHORS, CALLED BY NO
FILE YET (three; two of them under a test that is shown at no code switch): sender, inside, lent. ON
LETTERS (two): reply, ground.
WHAT IS NO PREMISE, AND WHY. The facts on the layout of the committed weights: weightsLaid_at_head
(Law/WeightsAtHead.lean), under h. The ledger's number in front of the member: a closed term of the
public parameters, Forest.elems (At.X Zp).HLy.fs: ledgerIs_k6_closed (Law/MaskAtHead.lean), under h.
That the two items which the member's row takes in are open at border 341: open_at_341
(Law/LettersAtHead.lean), by Lean's kernel on the written lists. "The script's cells are in range"
is the first half of the field index; what Cells/TieOfTies.lean asks on the index at a stand is that
field at the stand's input, which the thread says is valid.
THE SEVEN FIELDS OF K6Script, AND WHAT PAYS EACH HERE. cellsTie: k6_cellsTie_head, by
cellsTie_of_ties (Cells/TieOfTies.lean): ground, cellsOn, index. maskTie: k6_maskTie_head, by
maskTie_at_head (Law/MaskAtHead.lean): sender, lent, inside, reader, stretch, room, fence, within.
Four by Law/ScriptFields.lean: keyTie: k6_keyTie_of_points: reply, points. idn: k6_idn_thr: index:
neither the token nor the lookup's points are asked. keys: k6_keys_thr: index. left: k6_left_thr: h
alone. guests: guests.
  K6HeadDebts                   a structure of premises: nothing is claimed of it.
  K6ExchangeDebts               it, and one field more, halves: the premise of
                                Law/PlanesAtHead.lean's k6_exchangeS_at_head_free beside K6Script
                                and "the script's cells are in range". At every letter Kp; the debt
                                BehindS is not asked. The debt's share at the item formsT 24 3
                                "planes" is no field: that file pays it, over another sub-protocol's
                                authors' law, WHICH IS A READING COPY AND HAS NOT BEEN HANDED IN;
                                the item worth 24 3 "planes" in front is read there off the thread's
                                sentence: whoever shows that the thread holds at the border pays
                                it.
  inRange_of_index              the first half of the field index.
  k6_cellsTie_head, k6_maskTie_head   two fields of K6Script, each with its statement written
                                out.
  k6Script_at_head              THE MEMBER: here the seven ends are laid into the structure's seven
                                fields.
  k6_exchangeS_at_head_of_debts the debt ExchangeS at border 341 under K6ExchangeDebts.

-/
import Johnson.Desc.ProofFile.Honest.K6.Law.PlanesAtHead
import Johnson.Desc.ProofFile.Honest.K6.Law.MaskAtHead
import Johnson.Desc.ProofFile.Honest.K6.Law.ScriptFields
import Johnson.Desc.ProofFile.Honest.K6.Law.WeightsAtHead
import Johnson.Desc.ProofFile.Honest.K6.Cells.TieOfTies

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open Inst.Model.Head (oH)
open OnBytes (E)
open OnBytes.Model (Fork)
open OnBytes.Model.Verify (borderOf)
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles.Flat (Holds InRange)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS At.layout At.num At.X)
open ProofFile.Honest (ProverCoinCounts Coins Local Mid Prover ThrS ExchangeS Addr Due Cs
  SenderLaysOwn OwnIs ReaderReads CellsTieOn MaskTieOn spentOf oneStretch rowEntries)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K6 (K6Script K6HalfAt headRow headWit' headMats headWhereOf cellsTie_of_ties
  weightsLaid_at_head maskTie_at_head k6_left_thr k6_keyTie_of_points k6_idn_thr k6_keys_thr)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
  (cells : Tr → ProofFile.Honest.Cells) (weights : W₀ → ProofFile.Honest.Weights) (G : ProofFile.Ground)
  (o : Addr) (d : Due) (rowOf : Cs d → Nat → E) (own : Coins Bk → Cs d) (base cnt free : Nat)

/-- **WHAT IS LEFT TO PAY FOR A MEMBER OF K6Script AT THE LIBRARY'S HEAD.** A field a premise. o, d,
rowOf, own, base, cnt, free: the letters of the frame's lemma on the mask's tie: free: whoever pays
names them. A definition: a structure of premises. Nothing is claimed of it. -/
structure K6HeadDebts : Prop where
  /-- from border b₀ on the state's reply is the one that the instance asks about
  (Honest/Thread/FirstHead.lean); the member's border lies behind it. ON A LETTER: whoever lays the
  letters chooses b₀, in a window: too small a b₀ empties the thread, since no reply is laid yet
  there [argued; no theorem]. -/
  reply : b₀ ≤ 341
  /-- the ground's public parameters are the library's own. ON A LETTER; the field cellsOn reads G
  further, and the premise on the prover's halves (K6ExchangeDebts.halves) speaks of the frame's own
  ground: so the three can be met together at that ground alone [argued; no theorem]. -/
  ground : G.W = At.X Zp
  /-- the cells that the script makes of a valid input hold an index, whose entries, in the output
  matrix's two bands of rows, the reader of the committed digits reads at that input. TYPED BY
  NOBODY; a road is sketched on paper (no file), over another author's structure of premises of
  which no member is shown. -/
  index : ∀ v, (v = w ∧ Vd v) → ∃ i : Cm.Idx, Holds (Q.cells v) i ∧
    ∀ row col, oH ≤ row → row < oH + 2 * 5120 → col < 202048 →
      (ZMod.valMinAbs ((weights v.w₀).entry row col) : Int) = i.mat row col
  /-- what the head's text reads at the state as the lookup's points is what the small input makes
  of the challenges heard: the border to the lookup on the head's calls. TYPED BY NOBODY. -/
  points : ∀ k s m E, ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
    k s m E →
    (seatAt (At.X Zp).hS (readsOf (At.X Zp))).lookup s =
      some ((headWit' cells weights Zp G m.st.input).lookup m.st.heard)
  /-- AT THE PROVER'S CELLS the two guests are 0 at every position's corner: a fact on the trace.
  TYPED BY NOBODY. -/
  guests : ∀ k s m E, ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
    k s m E →
    letI : Given := (headWit' cells weights Zp G m.st.input).given (parOf (At.X Zp).hS (workOf (At.X
      Zp))) m.st.heard
    CornerGuests (headWit' cells weights Zp G m.st.input).cells.toCells
  /-- inside the four ranges the prover's cell of the head's segment, as the integer of least
  absolute value, is segment 24's own integer off the thread's witness, at every continuation
  (Honest/Law/Rule/TiesOn.lean: CellsTieOn, at these letters). TYPED BY NOBODY; the same sketch on
  paper (no file). -/
  cellsOn : CellsTieOn (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
    (ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341)
    (fun _ => some ())
    (fun v a rr c =>
      (ZMod.valMinAbs (headMats (headWhereOf Zp G) (cells v.trace) a rr c) : Int))
    (fun _ _ _ v a rr c => P5J.ownQ (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay)
      (P5J.At.N Zp cF) (Meaning.sizesOf (At.X Zp))
      (seatLay (At.X Zp) (At.layout Zp) (At.num Zp)) v 24 a rr c)
    (InFour (At.X Zp).hS (At.X Zp).HLy (borderOf (At.X Zp).y))
  /-- what the reader of the head's law reads off the thread's witness under a number is the mask
  row's entry (ReaderReads). TYPED BY NOBODY (its form's authors say so of the wider sentence, at
  every number below the free entries). The number is the format's (place times the number of mask
  rows, plus the row): a reader that takes the library's index agrees with it just where the number
  of mask rows is a power of two: whoever types this field carries that (Law/MaskAtHead.lean's
  head). THIS READER takes entry number j at row 0, place j (Law/PlanK6At.lean: plAt at rb := 0):
  the two numbers are one where the message has ONE mask row [that it has: not held here]; and it
  reads 0 from (At.X Zp).H.ns on (Law/K6ReadAt.lean: maskQ): SO THE FIELD IS ASKED BELOW THE FREE
  ENTRIES AND BELOW THAT NUMBER ALONE: beyond it, it would ask that the sender's coin read as 0. -/
  reader : ReaderReads (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
    (ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341)
    (fun s : S => s.fork?)
    (fun (_ : Fork) (_ : S) v u ν => rd ((cutAtHead h Q carryX v u).2 ν)) rd
    (fun k _ _ ν => rowOf (own k) ν) (fun ν => ν < free ∧ ν < (At.X Zp).H.ns)
  /-- what the row's parts spend is one stretch of one sender's coins, which begins at base + the
  ledger's number in front of the member. PRINTED, NOT PROVED: lemmas are compiled, the test's
  answers printed at two sizes; the sender's own base against the book's is nobody's. -/
  stretch : oneStretch (rowEntries Bk IM.k6Place
    (headRow (X := X) (headWit' (Rc := Rc) cells weights Zp G)
      (parOf (At.X Zp).hS (workOf (At.X Zp))) IM.k6Place).length 0) =
      some (o, base + OnBytes.Model.Forest.elems (At.X Zp).HLy.fs, cnt)
  /-- the stretch lies inside the count. EVALUATED: the book's own test. -/
  room : ∀ k : Coins Bk, base + OnBytes.Model.Forest.elems (At.X Zp).HLy.fs + cnt ≤
    (k.look (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.chain o).1.e
  /-- the member's slots lie below the mask row's free entries. NOT PROVED FOR A MEMBER: a lemma at
  one stretch is compiled; that a member's stretch is made of stretches that the maker's test has
  seen is not shown (Honest/Law/Rule/TiesFree.lean's own Limits). -/
  fence : OnBytes.Model.Forest.elems (At.X Zp).HLy.fs + cnt ≤ free
  /-- the member's slots lie inside the head's plan: below its own number of entries of the link's
  mask row in use, up to which the reader of the head's law reads the witness. On public numbers and
  the book's count cnt alone. TYPED BY NOBODY. -/
  within : OnBytes.Model.Forest.elems (At.X Zp).HLy.fs + cnt ≤ (At.X Zp).H.ns
  /-- the mask row's entry is the sender's own coin (SenderLaysOwn). TYPED BY THE SENDER'S AUTHORS,
  by their own word, under a test on the sending that is shown at no code switch (evaluated at two
  sizes: it accepts; not proved); called by no file yet. -/
  sender : SenderLaysOwn rowOf base (· < free)
  /-- that coin's number lies inside the part's count. The same authors', under the same test. -/
  inside : ∀ ν, ν < free → base + ν < d.e
  /-- what the frame lends the part as its own is there at every run's coins (OwnIs). By a lemma of
  the frame's authors'; not called here. -/
  lent : OwnIs Bk (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.chain o d own

/-- **WHAT IS LEFT TO PAY FOR THE DEBT ExchangeS AT BORDER 341.** A definition: a structure of
premises. Nothing is claimed of it. -/
structure K6ExchangeDebts : Prop extends
    K6HeadDebts h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells weights G o d rowOf own base
      cnt free where
  /-- the prover's half at the member's place is this sub-protocol's row at the small input
  (Law/SeatedAtHead.lean: K6HalfAt). SHOWN OF NO PROVER. -/
  halves : K6HalfAt Zp H (headWit' cells weights Zp G)

variable {h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells weights G o d rowOf own base cnt
  free}

/-- The script's cells are in range at every valid input: the first half of the field index. -/
theorem inRange_of_index
    (Dt : K6HeadDebts h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells weights G o d rowOf own
      base cnt free) :
    ∀ v, (v = w ∧ Vd v) → InRange (Q.cells v) :=
  fun v hv =>
  let ⟨i, hi, _⟩ := Dt.index v hv
  ⟨i, hi⟩

/-- **THE FIELD cellsTie.** -/
theorem k6_cellsTie_head
    (Dt : K6HeadDebts h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells weights G o d rowOf own
      base cnt free) :
    ∀ k s m E, ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 k s m E
      → ∀ ds,
      letI : Given := (headWit' cells weights Zp G m.st.input).given (parOf (At.X Zp).hS (workOf
        (At.X Zp))) m.st.heard
      SameCells (headWit' cells weights Zp G m.st.input).cells (cutAtHead h Q carryX m.st.input
        ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.wit k m.st.input
          (m.st.heard ++ ds))).1 := by
  intro k s m E hT ds
  letI : Given := (headWit' cells weights Zp G m.st.input).given (parOf (At.X Zp).hS (workOf (At.X
    Zp))) m.st.heard
  show SameCells (headWit' cells weights Zp G m.st.input).cells
      (compCut (P5J.At.cs Zp) (P5J.At.arr Zp) (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF)
        (Meaning.sizesOf (At.X Zp)) (seatLay (At.X Zp) (At.layout Zp) (At.num Zp)) (At.X Zp)
        (plAt (At.num Zp 24 0) 0) (Q.wit k m.st.input (m.st.heard ++ ds))).1
  exact cellsTie_of_ties h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells weights G Dt.ground
    Dt.cellsOn (weightsLaid_at_head h)
    (fun _ _ m' _ hT' => Dt.index m'.st.input hT'.1.2.2.2.2.2.2) k s m E hT ds

/-- **THE FIELD maskTie.** -/
theorem k6_maskTie_head
    (Dt : K6HeadDebts h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells weights G o d rowOf own
      base cnt free) :
    MaskTieOn (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341) IM.k6Place
      (headRow (X := X) (headWit' cells weights Zp G) (parOf (At.X Zp).hS (workOf (At.X Zp)))
        IM.k6Place)
      (fun s => s.fork?) (fun F _ v u j => rd ((cutAtHead h Q carryX v u).2 (F.next + j))) rd
      (spentOf _) (fun n j => j < n) :=
  maskTie_at_head (lim := (At.X Zp).H.ns) h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
    (headWit' cells weights Zp G) IM.k6Place
    (cutAtHead h Q carryX) Dt.sender Dt.lent Dt.inside Dt.reader Dt.stretch Dt.room Dt.fence
    Dt.within

/-- **A MEMBER OF K6Script**, all seven fields, at the small input that the two shared readers make
(headWit'), the member's place and the reader of the head's law at the library's own letters:
CONDITIONAL on the hypothesis h and on K6HeadDebts. -/
theorem k6Script_at_head
    (Dt : K6HeadDebts h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells weights G o d rowOf own
      base cnt free) :
    K6Script (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
      (At.X Zp) (headWit' cells weights Zp G) IM.k6Place (cutAtHead h Q carryX) :=
  { cellsTie := k6_cellsTie_head Dt
    maskTie := k6_maskTie_head Dt
    keyTie := k6_keyTie_of_points h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said Dt.reply
      (headWit' cells weights Zp G) (fun _ => rfl) (fun _ => rfl) Dt.points
    idn := k6_idn_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
      (headWit' cells weights Zp G) (fun _ => rfl) (inRange_of_index Dt)
    guests := Dt.guests
    left := k6_left_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
    keys := k6_keys_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said (inRange_of_index Dt) }

/-- **THE DEBT ExchangeS AT BORDER 341**: CONDITIONAL on the hypothesis h and on K6ExchangeDebts:
the whole of what is left, on one screen. -/
theorem k6_exchangeS_at_head_of_debts
    (Dt : K6ExchangeDebts h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells weights G o d rowOf
      own base cnt free) :
    ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 :=
  k6_exchangeS_at_head_free h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
    (inRange_of_index Dt.toK6HeadDebts) (headWit' cells weights Zp G) Dt.halves
    (k6Script_at_head Dt.toK6HeadDebts)

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.inRange_of_index
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_cellsTie_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_maskTie_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6Script_at_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_exchangeS_at_head_of_debts
