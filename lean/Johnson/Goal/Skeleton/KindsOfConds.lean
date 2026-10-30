-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/KindsOfConds.lean: `KindsConds`: what this file still asks as hypotheses of
the kinds of sub-protocol that have a place on the proof file's first chain. It has TWO
fields: k9, the bare law of the one kind whose law this file does not call, and frame25, the bare
law of the kind "frame" (the rows of the fold's own text)
at 25 places.
`KindsConds.all`: they give every kind's field
in the form in which a kind's law is counted, `P5J.AtMgA.Kind h 𝔏 K` (Johnson/P5J/RowsAtAll.lean). A
CUT IN WHICH EVERY FIELD IS A KIND'S LAW IN THE COUNTED FORM, BARE: of the fourteen kinds 12 (k1,
k2, k3, k4, k5, k6, k7, k8, k10, k11, k12, k13) have their laws called from the head and have no
field; 1 has the bare field (k9); the frame's field is its bare law at 25 of its 77 places, the
other 52 being shown or called; no kind's own named condition stands in a field's place.

Why. The top (Johnson/Goal/Skeleton/SoundOfKindsTop.lean) asks sixteen bare fields "h.Kind 𝔏 K".
With this file its list of hypotheses names what each kind's files
still owe.

The called laws. Each is called here, not proved here: its proof stands in the file that is named,
which this file imports, so Lean compiles the two together and checks the fit at the arm. A
called law is a theorem of another file whose binders are the head h (over the entry tests as this
tree has them: FOURTEEN rows; from the fourteenth, `rowsMadeB`, follows the
condition on the rows read (`P5J.owed_of_live`): that
condition is not proved from the other thirteen rows: `verify` itself asks its like, as the
fourteenth), the filling 𝔏 and the lists' heads q₁ q₂ q₃ (K12's: q₁ and `LastTypedAt`; the frame's:
and `FrameBehind`). The head is a hypothesis, and it holds more than the fourteen tests: fields of
its plan and opts that no entry test asks. WHAT VOUCHES FOR A CALLED LAW:
(i) its own answer on axioms, by name, within Lean's three, over one build of the whole library;
(ii) its binders and its fit at this file's arm, which Lean checks in `KindsConds.all`; (iii) the
definitions that the statements hang on, which are for a reader to judge: by a walk in Lean they are
one cone for all (some 19,000 constants; none of this library under Johnson/ is partial or hides its
body; of Lean's own that hide theirs, the platform's word size and the hash mixer are reached
through the planner's side, by a road that no theorem covers; the second hash function reaches no
mixer, and the word size by one function alone, which a theorem writes away); (iv) a member of the
head: proved at `VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap` alone (at secondHashFunction, with `fixedConfigurationDigest` in the digest's
place; side library AtFullSide/Top/); at other files or another hash none is shown.
THE PROOFS BENEATH ARE LEAN's WORD: all called laws lean on one induction along the run.


The fourteen, each with what it is at this cut.
  k1 (52 places): NO FIELD: K1's LAW IS CALLED: `P5J.k01_kind_of_head`
    (Johnson/Desc/AtSeats/K01CondOfHead.lean): `k01_kind_all`
    at `k1Cond_of_head`. A theorem of this library; this file
    applies it to h, 𝔏, q₁ q₂ q₃ alone. By a walk in Lean,
    which no theorem states: K1's proof goes by its own text
    of the fold's data (`K1.foldDAt`), bound inside the
    proof; no tie to `At.foldD` is spent or needed.
  k2 (25 places): NO FIELD: K2's LAW IS CALLED:
    `VerifiableInference.Desc.First.K2Caller.k02_kind_of_head` (Johnson/P1K2R/K2FromHead.lean).
    A theorem of this library. By its statement its binders are the head, the filling, q₁ q₂ q₃
    and nothing else, and its end is the kind's law in the counted form (what would be the bare
    field: `h.Kind 𝔏 .K2`, the end of this file's arm). The head holds
    eleven further conditions that no entry test asks (its plan's seven, headAt, cols13, opts, k3);
    "the maker returns" is moved onto the top's one owed condition on the rows read, not spared.
  k3 (50 places): NO FIELD: K3's LAW IS CALLED: `P5J.k03_kind_head` (Johnson/P5J/K03FromHead.lean):
    `k03_kind_all` (Kinds/K3Bridge.lean) at `k03_cond_head`. The head is
    a hypothesis, so by itself the law proves nothing of any files. A theorem of this library.
    By its statement its binders are h, 𝔏, q₁ q₂ q₃ alone; `h.K3Cond 𝔏` is `k03_kind_all`'s
    binder; its end is this file's arm. By reading, not shown here: rides is proved, not moved.
  k4 (12 places): NO FIELD: K4's LAW IS CALLED: `OnBytes.Road.K4.k04_of_head`
    (Johnson/Road/K4/K04OfHead.lean): `k04_counted_of_last` at `k4Last_of_head`: that the one closed
    test `k4RowB` accepts is a theorem from the head (`k4Row_of_head`). A MARK: one
    file beneath (RowHead/FrontFreeK.lean) proves a fact by the tactic `kernel_rfl`
    (Johnson/Unfolds/KernelRfl.lean), which hands the kernel an `Eq.refl` that the elaborator has
    not compared: used on the terms in that file's head; it is the one
    use of that tactic beneath a called law.
    `k4Row_of_head` calls `rowLight_of_head_noPin` and by reading, not shown here,
    spends no entry test. BY READING: that proof gives two numbers of lin (its rows, its
    column bits), not "lin is the written one", which elsewhere comes of an
    entry test; and for K4 as a whole four things stay moved into the head,
    not paid: sends, written, cut, laid. By its statement `k04_of_head`'s
    binders are `k04_counted_of_last`'s less the one test: nothing is added;
    its end is this file's arm. By reading, not shown here: of the head
    `k4Row_of_head`'s cone spends scope, reads, pubOne and laid.pub alone, and
    `k04_of_head` as a whole stands over the entry tests (laid.asks, row 9).
  k5 (12 places): NO FIELD: K5's LAW IS CALLED: `H2K5.Door.k05_kind_of_head`
    (Johnson/Desc/First/Att/Door/Law/K5KindWhole.lean): FROM THE HEAD (OVER THE ENTRY TESTS:
    FOURTEEN ROWS IN THIS TREE) AND q₁ q₂ q₃. The head is a
    hypothesis; a member of it is proved at `storedPublicFiles` and
    `zGap` alone: at secondHashFunction, with `fixedConfigurationDigest` in the digest's place; side library AtFullSide/Top/.
    A theorem of this library; this file applies it to h, 𝔏, q₁ q₂ q₃
    alone, and its end is `h.Kind 𝔏 .K5`, this file's arm. By reading,
    not shown here: it also spends seven fields of the head that no entry
    test asks (opts.laid, k3, plan.shape, laid, named, fit, groups). K5's
    law is called under the head: that is less than "K5 is proved".
  k6 (1 place): NO FIELD: K6's LAW IS CALLED:
    `VerifiableInference.Desc.Kinds.Head.Law.AtTable.k06_counted_head`
    (Johnson/Desc/Kinds/Law/K06CountedHead.lean): FROM THE HEAD (OVER THE ENTRY TESTS: FOURTEEN ROWS
    IN THIS TREE) AND q₁ q₂ q₃. ▸ A joining of theorems of this library; at
    `OnBytes.secondHashFunction` alone. This file applies it to h, 𝔏, q₁ q₂ q₃ alone. By
    reading, not shown here: its condition `K6Cond` holds no part of the
    conclusion; in the 43 files of the cone beneath `k06_counted_head` no
    premise in disguise was found; and the law also spends fields of the head that no
    entry test asks: plan.named, laid, fit, groups, shape, opts.laid, headAt.
    K6's law is called under the head: that is less than "K6 is proved".
  k7 (1 place): NO FIELD: K7's LAW IS CALLED:
    `VerifiableInference.Desc.Kinds.Head.Law.k07_kind_of_head`
    (Johnson/Desc/Kinds/Law/K07KindOfHead.lean, over
    `k07_kind_of_facts`): FROM THE HEAD (OVER THE ENTRY TESTS: FOURTEEN ROWS IN THIS TREE) AND THE
    THREE LISTS' HEADS q₁ q₂ q₃. Two of its payers (fenceT's; the written division under `hs_atAll`)
    stand over rows 9 and 10 of the entry tests (madeRow, cutRow). Two written values
    rest on prints of Lean's evaluator (these two rows): that costs the proof nothing and
    the head something: a print only begot a literal; what is said of the literal is by
    the kernel; its tie to the files is a test of the door, a field of the head: were a
    literal wrong, the law would be true and the head empty. Moved into the head, not
    paid. By reading, not shown here: the cone holds no premise in disguise but the
    head's. K7's law is called under the head: that is less than "K7 is proved": the head
    stays a hypothesis, of which a member is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction, with
    `fixedConfigurationDigest` in the digest's place; side library AtFullSide/Top/), and that the rows accept at
    honest files is
    asserted, not shown here, of the first thirteen rows; of the fourteenth this file holds
    no word.
  k8 (25 places): NO FIELD: K8's LAW IS CALLED: `P1K8T.k08_kind_head`
    (Johnson/P1K8R/KindFromHead.lean): `k08_kind_head_of_ownSizes` at
    `P5J.ownSizes_at_head` (Johnson/P5J/K8OwnSizesAtHead.lean). It may be
    idle; the head holds fields that no entry test asks (k3, plan.radii); for the third of
    `ownSizes_at_head`'s three parts there is no kernel's twin. Three theorems
    of this library. By their statements: `k08_kind_head_of_ownSizes` (this
    file's binders and q's, and one more, hO); `k08_kind_head` (its binders
    are h, 𝔏, q₁ q₂ q₃ and nothing else; its end is this file's arm);
    `ownSizes_at_head` (from h alone; its end is `K8Cond`'s fourth conjunct,
    hO). By reading, not shown here: it is not idle by a failing look-up.
  k9 (75 places): BARE AT THIS CUT. What lies in this tree, NOT CALLED BY THIS FILE:
    `P5J.k09_kind_of_head` (Johnson/P5J/K09EndC.lean): the law from the head, 𝔏 and q₁ q₂ q₃, over
    its `AtMgA.K9Cond` and `k09_kind` (Johnson/P5J/K09Kind.lean: the three pieces' laws and the
    ties, clauses over reached states and closed conjuncts); `kindsLaws_at_head`
    (KindsLawsAtHead.lean) calls it. An implication from the head; that
    the head can be met is not said in it; a join of theorems
    from six sets of files of this library, which Lean compiles
    together. ▸ By reading, not shown here: two of the
    law's premises are drawn from the promise (public items of K5's and K3's rows), which these rows
    must keep: not tried.
  k10 (25 places): NO FIELD: K10's LAW IS CALLED: `P5J.k10_kind_free`
    (Johnson/P5J/K10Free.lean): `k10_kind_head` with its one further antecedent, `rowsRead Z`, fed
    from the head by `rowsRead_at_head` (Johnson/P2LawR/RowsReadAtHead.lean). ▸ A
    caution: the top makes the head from `rowsRead`: the order is: the live test and
    the entry tests give `rowsRead`, that gives the plan's radii, these the head, and inside the
    kinds the head gives `rowsRead` again: so `rowsRead_at_head` does not let the top drop
    `rowsRead` as a hypothesis (that would be a circle), and it is no proof that the maker returns;
    it only lets the kinds beneath the head take it from h. `k10_kind_free`
    and `rowsRead_at_head` are theorems of this library; this file applies
    the first to h, 𝔏, q₁ q₂ q₃ alone, and its end is this file's arm.
  k11 (1 place): NO FIELD: K11's LAW IS CALLED: `K11.k11_kind_head`
    (Johnson/K11R/KindAtFree.lean). A theorem of this library. By its statement
    `k11_kind_head` holds h, 𝔏, q₁ q₂ q₃ and nothing more; the end and the three equations are the
    cut's arm sign for sign.
  k12 (1 place): NO FIELD: K12's LAW IS CALLED: `H2K12.k12_kind_at_head`
    (Johnson/Loose/H2K12/K12AtHead.lean): FROM THE HEAD (OVER THE ENTRY TESTS: FOURTEEN ROWS IN THIS
    TREE), THE FIRST LIST'S HEAD q₁ AND `H2K12.LastTypedAt` at Z's three files (which this theorem's
    statement has in hand). By reading it also spends the head's plan (radii, fit, groups),
    and radii comes down to the top's one owed condition on the rows read: no new debt. The pins
    compare with written values; the written cut rests on prints of Lean's evaluator; the induction
    behind `FoldFacts` stands in other files, taken here at
    their statements. A theorem of this library. By reading,
    not shown here: no premise is the conclusion or holds a
    part of the end; no premise in disguise; rows 1, 9 and
    10 of the entry tests carry it. K12's law is called
    under the head: that is less than "K12 is proved".
  k13 (1 place): NO FIELD: K13's LAW IS CALLED: `VerifiableInference.Desc.K13.Law.k13_kind_of_head`
    (Johnson/Goal/Skeleton/K13OfHead.lean, over `k13_kindD` and
    the door's `pins_of_laid`): FROM THE HEAD (OVER THE ENTRY TESTS: FOURTEEN ROWS IN THIS TREE) and
    the three lists' heads: the two pins are not paid but moved into the head (two of the tests
    behind its field laid). It pays no premise of the head. By a walk in Lean its term
    also reaches five of the seven closed tests of the head's field plan, which no entry test asks
    (shape, laid, named, fit, groups: four of them only because the closed constant in the statement
    is made of them); not plan.radii. A theorem of this library; this file
    applies it to h, 𝔏, q₁ q₂ q₃ alone. K13's law is called under the head:
    that is less than "K13 is proved": the head stays a hypothesis; a
    member of it is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction, with `fixedConfigurationDigest` in the digest's
    place; side library AtFullSide/Top/).
  frame (77 places): THE FIELD frame25 IS THE FRAME's OWN LAW, BARE, AT 25 OF ITS 77 PLACES:
    `P1L20.FrameBehind h 𝔏` (Johnson/P1L20R/FrameOfBehind.lean): the tie in the counted form
    (`TiedAtR`) at the 25 places behind the batchings: A PART OF THE CONCLUSION: a law's share, no
    kind's own condition. `P1L20.frame_of_behind` gives the kind's field from it, the head
    and q₁ q₂ q₃: at 51 places the tie is shown under the head; at 1 (the seal's, 357) another
    file's theorem is called: 52 PLACES ARE NO HYPOTHESIS. WHAT IT IS NOT: THIS FILE SHOWS
    `FrameBehind` NOWHERE. In this tree it is a theorem from the head by two calls that this file
    does not make (`P1L20.frameBehind_of_k9`, in that same file, at `P5J.k09_cond_of_head`,
    Johnson/P5J/K09CondHead.lean; `kindsLaws_at_head` makes them), and so it weighs what K9's road
    weighs. The 52 rest on `fence_atAll`, which needs rows among the ninth to the
    thirteenth of the entry tests; a member of the head is proved at `storedPublicFiles` and `zGap`
    alone (at secondHashFunction, with `fixedConfigurationDigest` in the digest's place; side library AtFullSide/Top/).
    `frame_of_behind` is a theorem of this library: a conditional and a joining.
    `FrameBehind` holds a part of the conclusion and nothing else, so the debt does not
    fall: at this cut 100 of the 358 places stay hypotheses (k9's 75, the frame's 25).
  K14, K15 (no place): NO FIELD: their share of the first chain is free (`AtMgA.kind_K14`,
    `AtMgA.kind_K15`, Johnson/Goal/Skeleton/KindsWithoutPlaceAtMg.lean). Their laws are owed on the
    shared chain and in the copy's file, not here.

WHICH FIELDS ARE FOLD-SHAPED (facts of the form "at every reached state that bears no mark, this
test with code on the state accepts"): IN THIS CUT NONE.

Limits. A JOINING: IT PROVES NO LAW ITSELF; TWELVE KINDS' LAWS (K1's, K2's, K3's, K4's, K5's, K6's,
K7's, K8's, K10's, K11's, K12's, K13's) ARE CALLED FROM OTHER FILES, AND THE FRAME's AT 52 OF ITS 77
PLACES: EACH "CALLED, NOT PROVED". THIS FILE SHOWS NO FIELD TO HOLD. `KindsConds h h.free` holds
under every head (`kindsConds_at_head`, KindsCondsAtHead.lean: calls alone); a head with it is
proved in scope where the files are read and `protocolDataWellFormed` accepts (`P5J.headJoins_of_live`,
Johnson/P5J/HeadJoinsOfLive.lean), and so at `VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap` (`headJoins_named`,
AtFullSide/Top/HeadJoins.lean, side library): at the filling `h.free` and at `OnBytes.secondHashFunction` alone.
(In this tree each of the two fields follows from the head in its own file: `P5J.k09_kind_of_head`,
Johnson/P5J/K09EndC.lean; `P1L20.frameBehind_of_k9`, Johnson/P1L20R/FrameOfBehind.lean, at
`P5J.k09_cond_of_head`,
Johnson/P5J/K09CondHead.lean; `kindsConds_at_head` joins them with no proof but calls, and that the
tests from which a head follows (`head_exists_at_name`) pass is proved, in the side library
AtFullSide/Top/, only at `VerifierAndGoals.storedPublicFiles`, at `VerifierAndGoals.zGap` and at `storedPublicFiles` under every other policy
within the bounds of `theLive_zAt`; at other files it is not proved. The top,
`sound_of_verify_at` (SoundOfVerifyAt.lean), does not go through `KindsConds`: it has the bare laws
by `kindsLaws_at_head` (KindsLawsAtHead.lean).) A condition that holds a part of the conclusion
(marked ▸ above) moves no weight off that part. Wherever a condition here says "reached", it is the
form's own condition beside the promise ("reached, at a typed instance's public part") or that with
"and no mark", not every state of `RchAt`; a field that asks a fact of a reached state WITHOUT "no
mark" may have no payer at marked states; some fields of the kinds' named conditions say no
"reached" at all and range over every state (four are known: two in K3's digits' ledger, two in
K2's). General in the filling 𝔏; the kinds' named conditions have content only where the three
lists' heads are 𝔏's (q₁, q₂, q₃). At `OnBytes.secondHashFunction` alone. The full size alone.
No soundness is claimed. ONE FIELD THAT CANNOT BE MET EMPTIES THE WHOLE STRUCTURE, and every theorem
that takes it. Whatever follows from the head h and from the two pins that the head gives is no
condition: a payer under `KindsConds` has h in hand. (At
this cut no kind's named condition stands in a field's
place: both fields are bare.)



-/
import Johnson.P5J.RowsAtAll
import Johnson.Loose.H2K12.K12LawR
import Johnson.Loose.H2K12.K12AtHead
import Johnson.Goal.Skeleton.KindsWithoutPlaceAtMg
import Johnson.Goal.Skeleton.K13OfHead
import Johnson.P1L20R.FrameOfBehind
import Johnson.Desc.AtSeats.K01CondOfHead
import Johnson.P1K2R.K2FromHead
import Johnson.P5J.K03FromHead
import Johnson.Road.K4.K04OfHead
import Johnson.Desc.First.Att.Door.Law.K5KindWhole
import Johnson.Desc.Kinds.Law.K06CountedHead
import Johnson.P1K8R.KindFromHead
import Johnson.P5J.K10Free
import Johnson.K11R.KindAtFree
import Johnson.Desc.Kinds.Law.K07KindOfHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals.AtTheName

open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc.Sound (frameAt allOf)
open VerifiableInference.Desc (Chain KindName)
open P5J

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **What this cut still asks: the bare law of the one kind that it does not call (K9), and the
bare law of the kind "frame" at 25 places.** -/
structure KindsConds (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok) : Prop where
  k9 : h.Kind 𝔏 .K9
  frame25 : P1L20.FrameBehind h 𝔏

/-- **All sixteen kinds' fields**; K12's behind its one named condition on the public
files. -/
theorem KindsConds.all {h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x}
    {𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok} (C : KindsConds h 𝔏)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    ∀ K, (K = KindName.K12 → H2K12.LastTypedAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL) → h.Kind 𝔏 K
  | .K1, _ => k01_kind_of_head h 𝔏 q₁ q₂ q₃
  | .K2, _ => VerifiableInference.Desc.First.K2Caller.k02_kind_of_head h 𝔏 q₁ q₂ q₃
  | .K3, _ => k03_kind_head h 𝔏 q₁ q₂ q₃
  | .K4, _ => OnBytes.Road.K4.k04_of_head h 𝔏 q₁ q₂ q₃
  | .K5, _ => H2K5.Door.k05_kind_of_head h 𝔏 q₁ q₂ q₃
  | .K6, _ =>
    VerifiableInference.Desc.Kinds.Head.Law.AtTable.k06_counted_head h 𝔏 q₁ q₂ q₃
  | .K7, _ => VerifiableInference.Desc.Kinds.Head.Law.k07_kind_of_head h 𝔏 q₁ q₂ q₃
  | .K8, _ => P1K8T.k08_kind_head h 𝔏 q₁ q₂ q₃
  | .K9, _ => C.k9
  | .K10, _ => k10_kind_free h 𝔏 q₁ q₂ q₃
  | .K11, _ => K11.k11_kind_head h 𝔏 q₁ q₂ q₃
  | .K12, hT => H2K12.k12_kind_at_head h 𝔏 q₁ (hT rfl)
  | .K13, _ => VerifiableInference.Desc.K13.Law.k13_kind_of_head h 𝔏 q₁ q₂ q₃
  | .K14, _ => h.kind_K14 𝔏
  | .K15, _ => h.kind_K15 𝔏
  | .frame, _ => P1L20.frame_of_behind h 𝔏 q₁ q₂ q₃ C.frame25

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.KindsConds.all
