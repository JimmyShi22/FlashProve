-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/DebtsLess.lean: THE OUTPUT HEAD'S OWN ROUNDS: K6HeadDebts
(Law/ScriptAtHead.lean) FROM THIRTEEN OF ITS FOURTEEN FIELDS: ONE IS SAVED: room FOLLOWS FROM THREE
OTHERS; THREE MORE (within, fence, ground) HAVE A LEMMA EACH FOR WHOEVER PAYS THEM.
WHAT IT IS NOT. NO FIELD OF K6HeadDebtsLess IS SHOWN HERE OF ANY RUN, ANY PROVER OR ANY PUBLIC DATA;
whether they can be met together is not known. ONE FIELD IS SAVED, NOT THREE: within_of_takes and
fence_of_within exchange a field for a STRONGER premise (at the full size the ceiling is 173, while
within asks no more than 3570 - 1995 = 1575 of cnt): so they are lemmas for a payer, and the
structure keeps the weaker asks. No new mathematics: calls of the library's lemmas on public
numbers, one unfolding, arithmetic. At the full size and the format's second hash function alone, as h.
Nothing on whether the verifier accepts a proof, on soundness, on completeness or on what a proof
hides. No example.
WHY. Readers of Law/ScriptAtHead.lean found that the structure counts more than is owed, and that
five of its docstrings are darker than the library.
  room_of_own         general in the book, the chain and the letters: what is lent as a part's own
                      is cut out of the whole count (OwnIs; Cs.cut answers only inside it): so the
                      part's count is no more than the whole; inside at the last slot gives room.
                      It asks that there be a slot: 0 < nu0 + cnt: without one the end says more
                      than the premises.
  ground_of_blank     at the ground that the maker lays the field ground is the library's
                      ProofFile.Law.blankBy_W (Johnson/Desc/ProofFile/Law/MakerPublic.lean). Called by
                      nothing here: G is a letter, and the field stays.
  within_of_takes     under h: Forest.elems (At.X Zp).HLy.fs + takesOf .. is no more than
                      (At.X Zp).H.ns: by calls_place and the last clause of k6Pub_says at
                      k6Pub_in_scope (Johnson/Desc/Kinds/Law/K6PubInScope.lean, K6PubNumbers.lean):
                      so within follows from "cnt is no more than takesOf ..". Called by nothing
                      here.
  fence_of_within     fence from within where (At.X Zp).H.ns is no more than free. Called by nothing
                      here.
  K6HeadDebtsLess     a structure of premises: nothing is claimed of it.
  K6HeadDebtsLess.debts   THE JOIN: K6HeadDebts at the same letters; the slot is there since the
                      lookup's number of scalars is 1995 (the library's fs_in_scope).
  k6HeadDebts_iff_less    and back, by projections: under h the two say the same. THAT THE THIRTEEN
                      CANNOT BE CUT FURTHER IS NOT SAID: fence follows from within wherever the
                      plan's number is no more than free.

-/
import Johnson.Desc.ProofFile.Honest.K6.Law.ScriptAtHead
import Johnson.Desc.Kinds.Law.HeadFsWritten
import Johnson.Desc.ProofFile.Law.MakerPublic

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
open VerifiableInference.OnPublicFiles.Flat (Holds)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS At.layout At.num At.X)
open ProofFile.Honest (ProverCoinCounts Coins Local Mid Prover ThrS Addr Due Cs SenderLaysOwn OwnIs ReaderReads
  CellsTieOn oneStretch rowEntries)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K6 (headRow headWit' headMats headWhereOf)

/-- **THE FIELD room FROM lent, inside AND fence**, general in the book, the chain and the letters.
-/
theorem room_of_own {Bk : ProverCoinCounts} {ch : Nat} {o : Addr} {d : Due} {own : Coins Bk → Cs d}
    {base ν₀ cnt free : Nat} (ho : OwnIs Bk ch o d own) (hin : ∀ ν, ν < free → base + ν < d.e)
    (hfree : ν₀ + cnt ≤ free) (hpos : 0 < ν₀ + cnt) :
    ∀ k : Coins Bk, base + ν₀ + cnt ≤ (k.look ch o).1.e := by
  intro k
  have hk := ho k
  unfold ProofFile.Honest.Cs.cut at hk
  split at hk
  · rename_i hle
    have h2 : 0 + d.e ≤ (k.look ch o).1.e := hle.2
    have h3 := hin (ν₀ + cnt - 1) (by omega)
    omega
  · cases hk

/-- **THE FIELD ground AT THE GROUND THAT THE MAKER LAYS.** -/
theorem ground_of_blank {mk : ProofFile.LinksBy} {Zp : ProofFile.Pub} {G : ProofFile.Ground}
    (hG : ProofFile.blankBy mk Zp = some G) : G.W = At.X Zp :=
  ProofFile.Law.blankBy_W hG

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

include h in
/-- **THE PUBLIC HALF OF THE FIELD within**, under the one hypothesis: the member's slots, counted
at the count's ceiling, lie inside the head's plan. -/
theorem within_of_takes {cnt' : Nat}
    (hc : cnt' ≤ takesOf (parOf (At.X Zp).hS (workOf (At.X Zp)))) :
    OnBytes.Model.Forest.elems (At.X Zp).HLy.fs + cnt' ≤ (At.X Zp).H.ns := by
  obtain ⟨p, hp, hs, h0, hn⟩ := InScope.calls_place h.scope h.pubOne
  obtain ⟨_, _, _, _, _, p8, sh8, _, _, hall⟩ :=
    k6Pub_says (At.X Zp) (InScope.k6Pub_in_scope h.scope h.reads h.pubOne)
  obtain ⟨e1, e2, _⟩ := hall p _ hp hs
  rw [h0] at e1
  rw [hn] at e2
  omega

/-- **THE FIELD fence FROM within**, where the plan's number of entries in use is no more than free.
-/
theorem fence_of_within {cnt' free' : Nat}
    (hw : OnBytes.Model.Forest.elems (At.X Zp).HLy.fs + cnt' ≤ (At.X Zp).H.ns)
    (hf : (At.X Zp).H.ns ≤ free') :
    OnBytes.Model.Forest.elems (At.X Zp).HLy.fs + cnt' ≤ free' :=
  le_trans hw hf

/-- **WHAT IS LEFT TO PAY FOR A MEMBER OF K6Script AT THE LIBRARY'S HEAD, WITHOUT THE FIELD room.**
The thirteen other fields of K6HeadDebts, their types to the letter; five docstrings (ground,
index, guests, fence, within) say what has been found of these since. A definition: a structure of
premises. Nothing is claimed of it. -/
structure K6HeadDebtsLess : Prop where
  /-- from border b₀ on the state's reply is the one that the instance asks about
  (Honest/Thread/FirstHead.lean); the member's border lies behind it. ON A LETTER: whoever lays the
  letters chooses b₀, in a window: too small a b₀ empties the thread, since no reply is laid yet
  there [argued; no theorem]. -/
  reply : b₀ ≤ 341
  /-- the ground's public parameters are the library's own. ON A LETTER: at the ground that the
  maker lays it is the library's lemma (ground_of_blank, above); the field stays, since G is a
  letter. The field cellsOn reads G further, and the premise on the prover's halves
  (K6ExchangeDebts.halves) speaks of the frame's own ground: so the three can be met together at
  that ground alone [argued; no theorem]. -/
  ground : G.W = At.X Zp
  /-- the cells that the script makes of a valid input hold an index, whose entries, in the output
  matrix's two bands of rows, the reader of the committed digits reads at that input. TYPED BY
  NOBODY; a road is sketched on paper (no file), over another author's structure of premises of
  which no member is shown. FOR ITS FIRST HALF ("in range") the library has, under h: whatever h's
  own decoder returns is in range (Johnson/Desc/Kinds/Law/DecInRange.lean: dec_inRange,
  inRange_of_pin): at this thread the decoder is turned into the constant Q.cells, so neither pays
  it; whoever supplies Q as what that decoder returns has it from there. -/
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
  LAWS AT GENERAL CELLS ARE TYPED: among this sub-protocol's own files rider_of_headCl
  (Johnson/Desc/K6/Honest/Law/Back/IdnOfHeadCl.lean): from the test on the plan, Same, Wide and the
  library's relation HeadCl at the cells: its end is CornerGuests unfolded; and in the library
  (Johnson/Desc/Kinds/Law/LibBackWhole.lean) guests_of_rf, from the same three and its field
  relation RF at the cells, and nine_of_headCl, from HeadCl under more premises. THAT THE PROVER'S
  CELLS MEET THEIR PREMISES IS TYPED BY NOBODY. -/
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
  /-- the member's slots lie below the mask row's free entries. NOT PROVED FOR A MEMBER: a lemma at
  one stretch is compiled; that a member's stretch is made of stretches that the maker's test has
  seen is not shown (Honest/Law/Rule/TiesFree.lean's own Limits). It follows from within where the
  plan's number is no more than free (fence_of_within, above); for that bound the library has
  head_ns_fits, of the shape (Johnson/Desc/Kinds/Law/HeadNsFits.lean: H.ns and the answers have
  room in the mask's code): the tie to free is typed by nobody. -/
  fence : OnBytes.Model.Forest.elems (At.X Zp).HLy.fs + cnt ≤ free
  /-- the member's slots lie inside the head's plan: below its own number of entries of the link's
  mask row in use, up to which the reader of the head's law reads the witness. ITS PUBLIC HALF IS
  THE LIBRARY'S UNDER h: it follows from "cnt is no more than the count's ceiling takesOf .."
  (within_of_takes, above); THAT BOUND ON THE BOOK'S COUNT cnt IS TYPED BY NOBODY (the library's
  k6_decide_takes, Johnson/Desc/Kinds/Law/TakesAt.lean: behind an accepting decision the verifier's
  ledger has taken some t that is no more than that ceiling: the other side of the same count). -/
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

variable {h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells weights G o d rowOf own
  base cnt free}

/-- **THE JOIN**: K6HeadDebts at the same letters. CONDITIONAL on the hypothesis h and on
K6HeadDebtsLess. -/
theorem K6HeadDebtsLess.debts
    (Dl : K6HeadDebtsLess h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells weights G o d rowOf
      own base cnt free) :
    K6HeadDebts h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells weights G o d rowOf own base
      cnt free :=
  have he := (InScope.fs_in_scope h.scope h.reads h.pubOne).elems
  { reply := Dl.reply
    ground := Dl.ground
    index := Dl.index
    points := Dl.points
    guests := Dl.guests
    cellsOn := Dl.cellsOn
    reader := Dl.reader
    stretch := Dl.stretch
    room := room_of_own Dl.lent Dl.inside Dl.fence (by omega)
    fence := Dl.fence
    within := Dl.within
    sender := Dl.sender
    inside := Dl.inside
    lent := Dl.lent }

/-- **AND BACK**: thirteen projections: so, under h, the two structures say the same. -/
theorem k6HeadDebts_iff_less :
    K6HeadDebts h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells weights G o d rowOf own base
        cnt free ↔
      K6HeadDebtsLess h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells weights G o d rowOf own
        base cnt free :=
  ⟨fun Dt =>
    { reply := Dt.reply
      ground := Dt.ground
      index := Dt.index
      points := Dt.points
      guests := Dt.guests
      cellsOn := Dt.cellsOn
      reader := Dt.reader
      stretch := Dt.stretch
      fence := Dt.fence
      within := Dt.within
      sender := Dt.sender
      inside := Dt.inside
      lent := Dt.lent }, K6HeadDebtsLess.debts⟩

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.within_of_takes
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.fence_of_within
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.room_of_own
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.ground_of_blank
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.K6HeadDebtsLess.debts
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6HeadDebts_iff_less
