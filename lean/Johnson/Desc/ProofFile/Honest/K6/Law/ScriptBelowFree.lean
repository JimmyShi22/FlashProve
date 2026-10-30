-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/ScriptBelowFree.lean: THE OUTPUT HEAD'S OWN ROUNDS: A MEMBER OF
K6Script AT THE LIBRARY'S HEAD FROM ELEVEN OF K6HeadDebts' FOURTEEN FIELDS AND ONE BOUND ON PUBLIC
NUMBERS AND free: WITHOUT room, within AND fence.
WHAT IT IS NOT. TWELVE PREMISES STILL: fence IS EXCHANGED, NOT SAVED: for "below": the same bound
with the library's takesOf in the place of the book's count cnt. NO FIELD OF K6HeadBelow IS SHOWN
HERE OF ANY RUN, ANY PROVER OR ANY PUBLIC DATA; that they can be met together is not shown here (all
twelve at one set of letters, under thirteen named premises: headBelowUnderNamed,
AtFullSide/K6/BelowAtAnyIndex.lean).
NEITHER OF fence (K6HeadDebts, Law/ScriptAtHead.lean) AND below GIVES THE OTHER: at a book that
never lends the row cnt is tied to takesOf by nothing. room, within and fence are not proved from
these: they are not needed: the frame's form of the mask's tie (MaskTieOn) hands in "lendRow returns
at these coins": there cnt is takesOf (Law/LentInside.lean: from the lending and the one stretch
alone), so below is fence, room follows (Law/DebtsLess.lean: room_of_own) and within follows under
h. AT A BOOK THAT NEVER LENDS THE ROW THE FIELD maskTie HOLDS EMPTILY, as Law/MaskAtHead.lean's own
does: nothing here shows that a book lends. The other six fields of K6Script are laid as in
Law/ScriptAtHead.lean, by the same calls: two short proofs stand here for the third time. That this
thread holds at any border is shown nowhere. At the full size and the format's second hash function alone,
as h. Nothing on whether the verifier accepts a proof, on soundness, on completeness or on what a
proof hides. No example.
  below_of_wide, below_of_free_one   for whoever pays below: under h, from "the plan's number is no
                          more than free"; and from "free is no less than Send.freeMaskEntries at
                          one mask row, at the first chain's mask code and answers"
                          (Law/WideAtFree.lean: wide_at_free_one). Called by nothing here.
  k6_maskTie_of_below     the field maskTie from sender, lent, inside, reader, stretch, below.
  K6HeadBelow: a structure of premises: eleven fields of K6HeadDebts, their types to the letter, and
                          below: nothing is claimed of it.
  inRange_of_below, k6_cellsTie_of_below   as Law/ScriptAtHead.lean's two.
  k6Script_of_below       THE MEMBER.
  k6_exchangeS_of_below   the debt ExchangeS at border 341 from these and the premise on the
                          prover's halves.

-/
import Johnson.Desc.ProofFile.Honest.K6.Law.DebtsLess
import Johnson.Desc.ProofFile.Honest.K6.Law.LentInside
import Johnson.Desc.ProofFile.Honest.K6.Law.WideAtFree

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
open ProofFile.Honest (ProverCoinCounts Coins Local Mid Prover ThrS ExchangeS Addr Due Cs SenderLaysOwn OwnIs
  ReaderReads CellsTieOn MaskTieOn spentOf oneStretch rowEntries)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K6 (K6Script K6HalfAt headRow headWit' headMats headWhereOf cellsTie_of_ties
  weightsLaid_at_head maskTie_at_head cnt_is_takes_of_lent k6_left_thr k6_keyTie_of_points
  k6_idn_thr k6_keys_thr)

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
/-- **THE BOUND below**, under the one hypothesis, where the plan's number is no more than free. -/
theorem below_of_wide {free' : Nat} (hw : (At.X Zp).H.ns ≤ free') :
    OnBytes.Model.Forest.elems (At.X Zp).HLy.fs +
      takesOf (parOf (At.X Zp).hS (workOf (At.X Zp))) ≤ free' :=
  fence_of_within (within_of_takes h (Nat.le_refl _)) hw

include h in
/-- **THE BOUND below**, under the one hypothesis, where free is no less than the programs' own
count of free entries at one mask row. -/
theorem below_of_free_one {free' : Nat}
    (hfree : OnBytes.Send.freeMaskEntries 1
      (Zp.first.codes.mask.getD Zp.first.shape.maskCode default).ell Zp.first.shape.answers ≤
        free') :
    OnBytes.Model.Forest.elems (At.X Zp).HLy.fs +
      takesOf (parOf (At.X Zp).hS (workOf (At.X Zp))) ≤ free' :=
  fence_at_free_one h hfree (Nat.le_refl _)

/-- **THE FIELD maskTie WITHOUT room, within AND fence.** CONDITIONAL on the hypothesis h, on five
premises, each in the form of the field of K6HeadDebts of that name, and on below. The frame's form
hands in "lendRow returns at these coins": there cnt is takesOf. Where the book lends the row at no
coins it holds emptily. -/
theorem k6_maskTie_of_below (sender : SenderLaysOwn rowOf base (· < free))
    (lent : OwnIs Bk (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.chain o d own)
    (inside : ∀ ν, ν < free → base + ν < d.e)
    (reader : ReaderReads (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341)
      (fun s : S => s.fork?) (fun (_ : Fork) (_ : S) v u ν => rd ((cutAtHead h Q carryX v u).2 ν))
      rd (fun k _ _ ν => rowOf (own k) ν)
      (fun ν => ν < free ∧ ν < (At.X Zp).H.ns))
    (stretch : oneStretch (rowEntries Bk IM.k6Place
      (headRow (X := X) (headWit' (Rc := Rc) cells weights Zp G)
        (parOf (At.X Zp).hS (workOf (At.X Zp))) IM.k6Place).length 0) =
        some (o, base + OnBytes.Model.Forest.elems (At.X Zp).HLy.fs, cnt))
    (below : OnBytes.Model.Forest.elems (At.X Zp).HLy.fs +
      takesOf (parOf (At.X Zp).hS (workOf (At.X Zp))) ≤ free) :
    MaskTieOn (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341) IM.k6Place
      (headRow (X := X) (headWit' cells weights Zp G) (parOf (At.X Zp).hS (workOf (At.X Zp)))
        IM.k6Place)
      (fun s => s.fork?) (fun F _ v u j => rd ((cutAtHead h Q carryX v u).2 (F.next + j))) rd
      (spentOf _) (fun n j => j < n) := by
  have he := (InScope.fs_in_scope h.scope h.reads h.pubOne).elems
  intro k s m En hA a c ha hl
  have e := cnt_is_takes_of_lent (headWit' (Rc := Rc) cells weights Zp G)
    (parOf (At.X Zp).hS (workOf (At.X Zp))) IM.k6Place k stretch hl
  have fence : OnBytes.Model.Forest.elems (At.X Zp).HLy.fs + cnt ≤ free := by
    rw [e]
    exact below
  exact maskTie_at_head (lim := (At.X Zp).H.ns) h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
    (headWit' cells weights Zp G) IM.k6Place (cutAtHead h Q carryX) sender lent inside reader
    stretch (room_of_own lent inside fence (by omega)) fence
    (within_of_takes h (Nat.le_of_eq e)) k s m En hA a c ha hl

/-- **WHAT IS LEFT TO PAY FOR A MEMBER OF K6Script AT THE LIBRARY'S HEAD, WITHOUT room, within AND
fence.** Eleven fields of K6HeadDebts, their types to the letter; and below. A definition: a
structure of premises. Nothing is claimed of it. -/
structure K6HeadBelow : Prop where
  /-- from border b₀ on the state's reply is the one that the instance asks about
  (Honest/Thread/FirstHead.lean); the member's border lies behind it. ON A LETTER: whoever lays the
  letters chooses b₀, in a window: too small a b₀ empties the thread, since no reply is laid yet
  there [argued; no theorem]. -/
  reply : b₀ ≤ 341
  /-- the ground's public parameters are the library's own. ON A LETTER: at the ground that the
  maker lays it is the library's lemma (Law/DebtsLess.lean: ground_of_blank); the field stays,
  since G is a letter. The field cellsOn reads G further, and the premise on the prover's halves
  (K6ExchangeDebts.halves) speaks of the frame's own ground: so the three can be met together at
  that ground alone [argued; no theorem]. -/
  ground : G.W = At.X Zp
  /-- the cells that the script makes of a valid input hold an index, whose entries, in the output
  matrix's two bands of rows, the reader of the committed digits reads at that input. IN
  headBelowUnderNamed IT IS A PREMISE (IndexHeld, Honest/K6/Term/IndexPremises.lean); AT THE
  MATRICES IT FOLLOWS FROM TWO PREMISES (indexHeldAtTheMatrices,
  E2E/OutputHeadIndexAtTheHonestProver.lean). FOR ITS FIRST HALF ("in range") the library has, under
  h: whatever h's own decoder returns is in range (Johnson/Desc/Kinds/Law/DecInRange.lean:
  dec_inRange, inRange_of_pin): at this thread the decoder is turned into the constant Q.cells, so
  neither pays it; whoever supplies Q as what that decoder returns has it from there. -/
  index : ∀ v, (v = w ∧ Vd v) → ∃ i : Cm.Idx, Holds (Q.cells v) i ∧
    ∀ row col, oH ≤ row → row < oH + 2 * 5120 → col < 202048 →
      (ZMod.valMinAbs ((weights v.w₀).entry row col) : Int) = i.mat row col
  /-- what the head's text reads at the state as the lookup's points is what the small input makes
  of the challenges heard: the border to the lookup on the head's calls. Under h, at the ground that
  the maker lays: k6_points_at_head (Law/PointsAtHead.lean). -/
  points : ∀ k s m E, ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
    k s m E →
    (seatAt (At.X Zp).hS (readsOf (At.X Zp))).lookup s =
      some ((headWit' cells weights Zp G m.st.input).lookup m.st.heard)
  /-- AT THE PROVER'S CELLS the two guests are 0 at every position's corner: a fact on the trace.
  LAWS AT GENERAL CELLS ARE TYPED: among this sub-protocol's own files rider_of_headCl
  (Johnson/Desc/K6/Honest/Law/Back/IdnOfHeadCl.lean): from the test on the plan, Same, Wide and the
  library's relation HeadCl at the cells: its end is CornerGuests unfolded; and in the library
  (Johnson/Desc/Kinds/Law/LibBackWhole.lean) guests_of_rf, from the same three and its field
  relation RF at the cells, and nine_of_headCl, from HeadCl under more premises. THE FIELD follows,
  under h and at the ground that the maker lays, from one premise, which stays a premise there and
  bears the weight: a valid input's trace is the model's at a served instance (TraceIsTheModels,
  Honest/K6/Term/IndexPremises.lean): k6_guests_of_theTrace (Law/GuestsOfTheTrace.lean); at the
  matrices it follows from one premise (traceIsTheModelsAtTheMatrices,
  E2E/OutputHeadIndexAtTheHonestProver.lean). -/
  guests : ∀ k s m E, ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
    k s m E →
    letI : Given := (headWit' cells weights Zp G m.st.input).given (parOf (At.X Zp).hS (workOf (At.X
      Zp))) m.st.heard
    CornerGuests (headWit' cells weights Zp G m.st.input).cells.toCells
  /-- inside the four ranges the prover's cell of the head's segment, as the integer of least
  absolute value, is segment 24's own integer off the thread's witness, at every continuation
  (Honest/Law/Rule/TiesOn.lean: CellsTieOn, at these letters). AN EXCHANGE: under h, at the ground
  that the maker lays, for three premises (hSym: at the seats of the head's six own matrices the
  witness holds the packing of the input's cells; hSmall: these cells are small; hStream: the
  field's own text inside the range of the borrowed stream): k6_cellsOn_of_sym_and_stream
  (Law/CellsOnOfSym.lean). -/
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
  row's entry (ReaderReads). At a written place of the code switch into link 24 and that switch's
  first part's letters, under h: from the book's public test on that part (hLend), a bound on N, two
  bounds on free, the switch's public test (hv) and a premise on the sender's text (hO), which is
  paid by nothing there: k6_reader_at_link24 (Law/ReaderAtLink24.lean). The number is the format's
  (place times the number of mask rows, plus the row): a reader that takes the library's index
  agrees with it just where the number of mask rows is a power of two: whoever types this field
  carries that (Law/MaskAtHead.lean's head). THIS READER takes entry number j at row 0, place j
  (Law/PlanK6At.lean: plAt at rb := 0): the two numbers are one where the message has ONE mask row
  [that it has: not held here]; and it reads 0 from (At.X Zp).H.ns on (Law/K6ReadAt.lean: maskQ): SO
  THE FIELD IS ASKED BELOW THE FREE ENTRIES AND BELOW THAT NUMBER ALONE: beyond it, it would ask
  that the sender's coin read as 0. -/
  reader : ReaderReads (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
    (ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341)
    (fun s : S => s.fork?)
    (fun (_ : Fork) (_ : S) v u ν => rd ((cutAtHead h Q carryX v u).2 ν)) rd
    (fun k _ _ ν => rowOf (own k) ν) (fun ν => ν < free ∧ ν < (At.X Zp).H.ns)
  /-- what the row's parts spend is one stretch of one sender's coins, which begins at base + the
  ledger's number in front of the member. Under h, at the book of a return of the maker and a
  written place of the switch into link 24: k6_stretch_at_switch
  (AtFullSide/K6/StretchAtSwitch.lean). -/
  stretch : oneStretch (rowEntries Bk IM.k6Place
    (headRow (X := X) (headWit' (Rc := Rc) cells weights Zp G)
      (parOf (At.X Zp).hS (workOf (At.X Zp))) IM.k6Place).length 0) =
      some (o, base + OnBytes.Model.Forest.elems (At.X Zp).HLy.fs, cnt)
  /-- the lookup's scalars and the count's ceiling takesOf lie below the mask row's free entries. ON
  PUBLIC NUMBERS AND THE LETTER free ALONE: the book's count cnt is not in it. Where the book lends
  the row it is the field fence of K6HeadDebts (there cnt is takesOf). UNDER h IT FOLLOWS FROM "free
  is no less than the programs' own count of free entries at one mask row, at the first chain's mask
  code and answers" (below_of_free_one, above): that premise is shown of nothing. -/
  below : OnBytes.Model.Forest.elems (At.X Zp).HLy.fs +
    takesOf (parOf (At.X Zp).hS (workOf (At.X Zp))) ≤ free
  /-- the mask row's entry is the sender's own coin (SenderLaysOwn). At the letters of the code
  switch's first part it holds by the choice of rowOf, and buys nothing: the weight lies in reader:
  sender_at_take (Law/ReaderAtTake.lean). -/
  sender : SenderLaysOwn rowOf base (· < free)
  /-- that coin's number lies inside the part's count. Under h, at a written place of the switch
  into link 24, where free + 1 ≤ 8192: inside_at_link24 (Law/ReaderAtLink24.lean). -/
  inside : ∀ ν, ν < free → base + ν < d.e
  /-- what the frame lends the part as its own is there at every run's coins (OwnIs). By a lemma of
  the frame's authors'; not called here. -/
  lent : OwnIs Bk (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.chain o d own

variable {h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells weights G o d rowOf own
  base cnt free}

/-- The script's cells are in range at every valid input: the first half of the field index. -/
theorem inRange_of_below
    (Dt : K6HeadBelow h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells weights G o d rowOf own
      base cnt free) :
    ∀ v, (v = w ∧ Vd v) → InRange (Q.cells v) :=
  fun v hv =>
  let ⟨i, hi, _⟩ := Dt.index v hv
  ⟨i, hi⟩

/-- **THE FIELD cellsTie**, from these: Law/ScriptAtHead.lean's proof, line for line. -/
theorem k6_cellsTie_of_below
    (Dt : K6HeadBelow h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells weights G o d rowOf own
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

/-- **A MEMBER OF K6Script WITHOUT room, within AND fence**, at the small input that the two shared
readers make (headWit'), the member's place and the reader of the head's law at the library's own
letters: CONDITIONAL on the hypothesis h and on K6HeadBelow. -/
theorem k6Script_of_below
    (Dt : K6HeadBelow h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells weights G o d rowOf own
      base cnt free) :
    K6Script (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341
      (At.X Zp) (headWit' cells weights Zp G) IM.k6Place (cutAtHead h Q carryX) :=
  { cellsTie := k6_cellsTie_of_below Dt
    maskTie := k6_maskTie_of_below h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells weights G o
      d rowOf own base cnt free Dt.sender Dt.lent Dt.inside Dt.reader Dt.stretch Dt.below
    keyTie := k6_keyTie_of_points h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said Dt.reply
      (headWit' cells weights Zp G) (fun _ => rfl) (fun _ => rfl) Dt.points
    idn := k6_idn_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
      (headWit' cells weights Zp G) (fun _ => rfl) (inRange_of_below Dt)
    guests := Dt.guests
    left := k6_left_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
    keys := k6_keys_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said (inRange_of_below Dt) }

/-- **THE DEBT ExchangeS AT BORDER 341 FROM THESE AND THE PREMISE ON THE PROVER'S HALVES.** -/
theorem k6_exchangeS_of_below
    (Dt : K6HeadBelow h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said cells weights G o d rowOf own
      base cnt free) (halves : K6HalfAt Zp H (headWit' cells weights Zp G)) :
    ExchangeS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341 :=
  k6_exchangeS_at_head_free h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said
    (inRange_of_below Dt) (headWit' cells weights Zp G) halves (k6Script_of_below Dt)

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.below_of_wide
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.below_of_free_one
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_maskTie_of_below
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.inRange_of_below
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_cellsTie_of_below
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6Script_of_below
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_exchangeS_of_below
