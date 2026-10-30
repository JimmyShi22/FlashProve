-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/LookOfCut.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME
FOR THE HONEST SIDE: FROM THE CUT TO THE LOOK: ELEMENT NUMBER i OF A PART's CUT (ce c i,
Honest/K1/Coins.lean, at lentCut, Honest/K1/ScriptAt.lean) IS ELEMENT NUMBER i OF WHAT THE RUN HOLDS
AT THE PART's ADDRESS ((k.look ch a).2.eAt i, Honest/Frame.lean); AND SO WHAT THE KIND's
WHOLE-MESSAGE TEXT msgTxt ANSWERS AT AN ENTRY OF A MESSAGE's MASK ROWS IS THE RUN's ELEMENT NUMBER
maskStart + nu AT THE ADDRESS (place, 0). Four theorems; two tests at made-up coins, with their two
definitions.

THE RIDER, WITH EVERY QUOTATION OF ANY OF THE FOUR.
An identity of two readings of one element, at each run's coins: it says WHICH element of the run
the entry is. It says nothing on how that element is drawn, on who else reads or spends it, or that
it stands at no other entry. Of hE, "the key", it pays the step from the cut to the look alone.

  look_of_cut            where lentCut k ch a d = some c, at i below d.e: the look's eAt i is ce c i
  look_of_cut_map        the same from "(lentCut k ch a d).map (ce . i) = some y"
  msgTxt_mask_look       at a message whose table does not ride, at the entry number nu below rows *
                         length: what msgTxt answers at (true, nu % rows, nu / rows) is the look's
                         element number maskStart + nu at (place, 0)
  msgTxt_mask_look_one   the same at a message of one mask row: the entry is (true, 0, nu)
  lookToyBook, lookToyCoins   a book of one row of two elements of E; MADE-UP coins x, y: no run's
  look_one_off           at the coins 1, 0: a start one off is refused
  look_wants_hi          at the coins 1, 1, at i = d.e: the premise hi is not idle

KIN, TOLD. The heart lies at the type Cs: cut_eAt and eAt_of_lt (Honest/K2/Law/Reads.lean) are
CALLED here, with ce_eq (Honest/K1/MaskLaw.lean): no twin is typed. In matter the same, in other
readers: own_e (Honest/K12/CoinsTieBook.lean),
cut_cut (Honest/K14/SplitCoin.lean), lent_e and lent_shared (Honest/K14/SendingsCoins.lean).
cut_of_lendRow, cut_of_lendHalf, cut_of_lendPlace (Honest/K1/ScriptLendRow.lean) and cut_of_lend
(Honest/K1/ScriptAtLaw.lean) END at the cut and read no element.

For whom. msgTxt_mask_slot (Honest/K1/ScriptMaskSlot.lean) ends at the cut; a spender's laws on the
book's entries end at the look. The premise hE, "the key", of K4's two ties at the joined Script
(trials of K4's house; on no list) asks: what the sender's text answers at an entry is (k.look 0
owner).2.eAt (base + nu). OF hE THIS FILE PAYS THAT ONE STEP. STILL OWED FOR hE, AND NOT HERE: that
the maker's owner of the mask row and of the index masks' message is (K1's place, 0) and its base.e
is maskStart at message 0 and 4 of the opening's plan; that these two messages have one mask row;
that 0 and 4 lie below the plan's number of messages; that the places which K4 reads lie below the
mask code's length; that no table rides at 0 and 4 (hr); that K4's own number of mask rows
(k4IndexRows) is the opening's shape's at 4. UNTIL ALL OF THAT LIES hE STAYS A PREMISE THAT NOBODY
PAYS.

hasCoins. At a book whose count at the part's address does not cover the part's due this law holds
for nothing, and it is never quoted as if it spoke there: hasCoins is neither asked nor paid here:
whoever quotes this law at a book names hasCoins at that book beside it.
The equation hasCoins (dueAt (Bk.rowsOf 0) (J.P.place, 0) = dueR J.P J.ride) is no premise here:
"= some" carries what the four need of it: that the book COVERS the due. At a book that does not,
the premise h | hy is met at no coins (lentCut_isSome, Honest/K1/ScriptAtLaw.lean, at ch <= 1).
"COVERS, NOT EQUALS" (bookCovers, Honest/K1/ScriptAt.lean): at a book with MORE at the address the
cut is there and the four speak, of the first d.e elements; the frame's lendPart lends nothing
there. THAT THE PREMISE hy IS NOT IDLE: msgTxt_answers (Honest/K1/LotsLaid.lean): under hasCoins at
a book the text answers at every run, message and entry, at chain 0: so at the returned prover's own
book wherever hasCoins is had there.

sendFits. No premise: no step spends it. Whoever quotes this law at a plan names sendFits at that
plan beside it: hnu reads the mask code's length through "getD ... default": where the shape's
maskCode is no number of the plan's list of mask codes that length is the default code's, and
sendFits (through Own.sentShapeFits: no mask row, or maskCode below the list's size) bars that. The
0 that ce gives beyond the count is barred here by theorem: mask_in (Honest/K1/MaskLaw.lean).

Limits. At a message whose table rides (hr fails), at nu from rows * length on, at n from the plan's
number of messages on: nothing is said. At ch >= 2 look_of_cut and look_of_cut_map hold as well
(lentCut is the look's own cut at every ch); no seat of K1's stands there. THE TWO TESTS TRY THE
DEFINITIONS (lentCut, ce, Coins.look, Cs.eAt, Cs.cut), NOT look_of_cut; NOTHING HERE TRIES
msgTxt_mask_look OR msgTxt_mask_look_one AT A PLAN. An equation at each run. Nothing on any
property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.ScriptMaskSlot
import Johnson.Desc.ProofFile.Honest.K2.Law.Reads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open Johnson.Prover.Send (shapeAt)

variable {Bk : ProverCoinCounts} {W Wl X : Type}

/-- **From the cut to the look**, at any address, count and chain number. An identity of two
readings of one element, at each run's coins. Where the cut is none the premise h is met at no
coins. -/
theorem look_of_cut (k : Coins Bk) (ch : Nat) (a : Addr) (d : Due) (c : Cs d)
    (h : lentCut k ch a d = some c) (i : Nat) (hi : i < d.e) :
    (k.look ch a).2.eAt i = .ok (ce c i) := by
  have h' : (k.look ch a).2.cut ⟨0, 0⟩ d = some c := h
  have e := ProofFile.Honest.K2.Reads.cut_eAt h' (ProofFile.Honest.K2.Reads.eAt_of_lt c hi)
  have e' : (k.look ch a).2.eAt (0 + i) = .ok (c.e ⟨i, hi⟩) := e
  rw [Nat.zero_add] at e'
  rw [ce_eq d c i hi]
  exact e'

/-- The same from the mapped cut. -/
theorem look_of_cut_map (k : Coins Bk) (ch : Nat) (a : Addr) (d : Due) (i : Nat)
    (hi : i < d.e) (y : GE) (h : ((lentCut k ch a d).map fun c => ce c i) = some y) :
    (k.look ch a).2.eAt i = .ok y := by
  cases e : lentCut k ch a d with
  | none => simp [e] at h
  | some c =>
    rw [e] at h
    have hy : ce c i = y := Option.some.inj h
    rw [← hy]
    exact look_of_cut k ch a d c e i hi

/-- **At the text**, by the format's own number of the entry. hi is mask_in. Whoever quotes it at a
plan names sendFits at that plan beside it; at a book, hasCoins at that book. -/
theorem msgTxt_mask_look (ch : Nat) (wit : Wl → W) (J : SendJob W X) (own₀ : X) (n ν : Nat)
    (k : Coins Bk) (w : Wl) (h : List Fmt.Drawn) (hn : n < J.P.sent.size) (hr : J.ride n = none)
    (hν : ν < (shapeAt J.P n).maskRows *
      (J.P.codes.mask.getD (shapeAt J.P n).maskCode default).ell) (y : GE)
    (hy : msgTxt ch wit J own₀ n k w h true (ν % (shapeAt J.P n).maskRows)
        (ν / (shapeAt J.P n).maskRows) = some y) :
    (k.look ch ⟨J.P.place, 0⟩).2.eAt (maskStart J.P J.ride n + ν) = .ok y := by
  rw [msgTxt_mask_slot ch wit J own₀ n ν k w h hr hν] at hy
  exact look_of_cut_map k ch ⟨J.P.place, 0⟩ (dueR J.P J.ride) (maskStart J.P J.ride n + ν)
    (mask_in J.P J.ride n ν hn hr hν) y hy

/-- The same at a message of one mask row. -/
theorem msgTxt_mask_look_one (ch : Nat) (wit : Wl → W) (J : SendJob W X) (own₀ : X) (n ν : Nat)
    (k : Coins Bk) (w : Wl) (h : List Fmt.Drawn) (hn : n < J.P.sent.size) (hr : J.ride n = none)
    (h1 : (shapeAt J.P n).maskRows = 1)
    (hν : ν < (J.P.codes.mask.getD (shapeAt J.P n).maskCode default).ell) (y : GE)
    (hy : msgTxt ch wit J own₀ n k w h true 0 ν = some y) :
    (k.look ch ⟨J.P.place, 0⟩).2.eAt (maskStart J.P J.ride n + ν) = .ok y := by
  refine msgTxt_mask_look ch wit J own₀ n ν k w h hn hr ?_ y ?_
  · rw [h1, Nat.one_mul]
    exact hν
  · rw [h1, Nat.mod_one, Nat.div_one]
    exact hy

/-- A book of one row: two elements of E at the default address. -/
def lookToyBook : ProverCoinCounts := ⟨[(default, ⟨0, 2⟩)], [], [], [], []⟩

/-- MADE-UP coins at that book: x, y. No run's. -/
def lookToyCoins (x y : GE) : Coins lookToyBook :=
  ⟨((⟨fun i => i.elim0, fun i => if i.1 = 0 then x else y⟩ : Cs ⟨0, 2⟩), ()), (), ()⟩

/-- **A start one off is refused**: at the coins 1, 0 the cut of one element holds 1; element number
1 is 0. A ce that gave its 0 everywhere would make the two sides equal. -/
theorem look_one_off : ∃ c, lentCut (lookToyCoins 1 0) 0 default ⟨0, 1⟩ = some c ∧
    ((lookToyCoins 1 0).look 0 default).2.eAt (0 + 1) ≠ .ok (ce c 0) := by
  refine ⟨_, rfl, ?_⟩
  intro h
  have h' : (Except.ok (0 : GE) : Except String GE) = .ok 1 := h
  exact zero_ne_one (Except.ok.inj h')

/-- **hi is not idle**: at the coins 1, 1, at i = d.e: ce gives 0 beyond the cut's count; the look
still has element number 1, which is 1. -/
theorem look_wants_hi : ∃ c, lentCut (lookToyCoins 1 1) 0 default ⟨0, 1⟩ = some c ∧
    ((lookToyCoins 1 1).look 0 default).2.eAt 1 ≠ .ok (ce c 1) := by
  refine ⟨_, rfl, ?_⟩
  intro h
  have h' : (Except.ok (1 : GE) : Except String GE) = .ok 0 := h
  exact one_ne_zero (Except.ok.inj h')

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.look_of_cut
#print axioms ProofFile.Honest.K1.look_of_cut_map
#print axioms ProofFile.Honest.K1.msgTxt_mask_look
#print axioms ProofFile.Honest.K1.msgTxt_mask_look_one
#print axioms ProofFile.Honest.K1.lookToyBook
#print axioms ProofFile.Honest.K1.lookToyCoins
#print axioms ProofFile.Honest.K1.look_one_off
#print axioms ProofFile.Honest.K1.look_wants_hi
