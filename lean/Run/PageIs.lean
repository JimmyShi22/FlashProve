-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageIs.lean: the compiled verifier behind the lenient reader, compared with the format's own
strict verifier. Definitions and statements only. Many statements of this library are written twice:
a definition in the namespace `Spec` states a proposition, and a theorem of the same name outside
that namespace proves it (lean/GLOSSARY.md).

Two verifiers for a proof file are compared, for every description S of a file format within the
limits of the generic construction, every choice of challenge types that fits (the parameter C : CK:
for each round the type of the verifier's message, and the map from such a message to the format's
record of what was drawn), every decision dec, and every oracle O on byte strings with answers of 32
bytes (h := Fmt.HO O is the format's hash function built from O).
   `laxV O S C K chal dec file`. The lenient reader at h, then the evaluable form of the compiled
   verifier (`verifyP`, Run/ThinDefs.lean; proved equal to the run of `Compile.Batch.verifyOneProtocol`:
   `thin_verify`, stated in Run/ThinTie.lean, proved in Run/ThinTieProofs.lean) at the typed oracle
   functions that O induces (Run/CodingFn.lean: famOf O (PDS ..)), at the data made from S, that
   choice and dec (Run/PlanQS.lean). The lenient reader (`laxWhole`, Run/ParseLax.lean; "lax" in
   names) only cuts the file into its parts. The lenient reader also refuses some files (what it
   refuses: part 1 of the head of Run/ParseLax.lean). It still recomputes the hash chain, because
   the drawn positions say how long the parts are; it tests no proof of work, walks no path and
   compares no root. Behind it the compiled verifier makes these checks itself.
   Fmt.verifyW (m := Id) h S (fun _ => dec) () file (Fmt/M1View.lean). The format's side: the strict
   reader of Fmt/Rules8.lean (form, spellings, proof of work, listed positions, every opening
   against its root, one value at a vertex under one root), then dec on what was read. It is this
   library's rendering of the verifier that the format page (docs/format/FORMAT.md, which comes with
   the programs; this file has not been held against the page as it ships) prescribes.
The generic construction (Run/PlanQTypes.lean, Run/PlanQS.lean) makes a typed protocol and its
wiring from a description. Its limits are the test `PQ.ok` (Run/PlanQTypes.lean): S passes
`Fmt.Spec.ok`; a round sends at most one root; every opened tree is the chain's own; each tree is
opened at most once; the chain's random bytes are in the file.

This file proves nothing. All parts and all four main statements (both listed under 3) are proved,
as stated here:
   `pi_typed`: Run/PageIsTopProofs.lean. `pi_chain`: Run/PageIsChain.lean. `pi_facts`, `pi_strict1`:
   Run/PageIsReaders.lean. `pi_after`: Run/PageIsAfter.lean. `pi_strict2`: Run/PageIsStrict2.lean.
   `pi_formula`, `pi_half`, `pi_kits`: Run/PageIsProofs.lean, where `PiFit` is also shown to hold at
   the format's oracle at both choices of challenge types in use, for every S within the limits.
   `pi_core` (F2): Run/PageIsCoreProofs.lean.

1. What the file contains.
   The middle term: what the lenient reader hands out, o, and three tests on it: `passL` and
   `rootsAll`, which hash, and the decision dec.
      `TraceL`, `LaxFacts`: what o is: each round's items are its message read; what was drawn is
         the format's draw on the round's blocks; each opening stands at the list of the draw, under
         the root sent, in the right shape.
      `rootsDiffer`: it is true if the roots that the file sends are pairwise different, and also
         where the reader reads nothing.
      `KitFits`: the view that the choice of challenge types gives of the wiring's message is the
         format's draw on the first blocks. This is true of both choices in use: challenges as
         sampled values (`ck`: a round's verifier message is the values that the format draws, field
         elements and positions among them; the wiring applies the sampling rule) and challenges as
         hash blocks (`ckP`: the message is the round's 256-bit blocks themselves; reads and
         decision apply the sampling rule) (Run/PlanDraws.lean: `planDraws_tie`; Run/PlanPull.lean:
         `planPull_view`).

2. What is checked when the file compiles. Nothing beyond the types; there are no tests (#guard)
here.

3. Theorems. None is proved here; the statements (Run.PQ.Spec.pi_*) are these.
   The parts. The lines below leave out some of their hypotheses: that S lies within the limits
   (`PQ.ok`), the lengths of the hash function's or the oracle's answers, o.run = some run, and for
   `pi_chain` and `pi_after` `LaxFacts` and more. See each statement.
      `pi_facts`: laxWhole h S b = some o → LaxFacts h S o.
      `pi_strict1`: wholeChain h S b = some o' → there is o with laxWhole h S b = some o, the same
         view, passL, rootsAll.
      `pi_strict2`: laxWhole h S b = some o, passL, rootsAll, rootsDiffer → there is o' with
         wholeChain h S b = some o' and the same view.
      `pi_chain`: on the argument string made from the reader's output the verifier's chain yields:
         what was drawn is o's; its test bits pass iff passL; each round's root is o's; it has not
         joined.
      `pi_after`: given what the chain yields: the strict format holds, and what follows the chain
         is rootsAll ∧ (the test bits pass) ∧ dec on o's view.
      `pi_typed`: the step that types the reader's output does not refuse: LaxFacts, the limits →
         toBPrfP gives a string, its list the one digest.
   The main statements. `pi_formula`, `pi_half`, `pi_core` and `pi_kits` each have the hypothesis
   PiFit O S C K chal (for `pi_kits`: at both choices), which the lines below leave out: O's answers
   have 32 bytes; S lies within the limits (`PQ.ok`); `KitFits`; every round's blocks number at most
   K.
      `pi_formula`: laxV .. file = (if laxWhole gives nothing: false; if it gives o: passL ∧
         rootsAll ∧ dec (viewOf S.firstTree o)).
      `pi_half`: (F1) What the format's verifier accepts, the compiled verifier behind the lenient
         reader accepts.
      `pi_core`: (F2) Where the roots that the file sends differ, the two give one verdict.
      `pi_kits`: two choices of challenge types that both fit give one verdict on every file. (The
         right side of `pi_formula` does not name the choice.) ((F1) is used at the run functions in
         Run/PageIsRun.lean (`run_half`), (F2) in Run/PageIsCore.lean.)

   Two hypotheses for `pi_strict2` and `pi_core`: (1) is a clause of the limits, which both assume;
   (2) is a premise of both.
      (1) saltLenOK S.plan.salt. Without this hypothesis the two statements are false: the format
      page's bounds on the length of a leaf's salt are then tested inside the strict reader of an
      opening alone, so that at a plan which breaks them the strict side refuses every file and the
      other side need not. The test is a clause of Fmt.Spec.ok, and so of the limits.

      (2) rootsDiffer. The strict reader's record of the vertices met is keyed by the root's 32
      bytes (R7.14 in the edition named under "Why"). In several other editions of the format page,
      none the one that ships, R7.14 speaks of a tree as it was sent (the first of them is known
      here by a restatement, the others by reading the page's own list of changes): with the record
      kept under the start of a tree's leaves and the number in their labels it never refuses within
      the limits, and the hypothesis is not needed. (That Fmt/Rules8.lean has the page's rule on the
      record in general is not said.)

   Why `rootsDiffer`. By R7.14 at a further edition of the page, the strict reader keeps one
   record of the vertices met for every root that is opened, keyed by the root's 32 bytes, and
   refuses a second value at a vertex. Within the limits each tree is opened at most once; but two
   trees may be sent
   with the same bytes as roots, and then the record joins them, while the compiled verifier walks
   each opened tree by itself. A file on which the two sides give different verdicts holds two
   openings that end in one root and differ at a vertex: a collision of the vertices' hash, which an
   arbitrary oracle may have (this follows the rule's letter; it is not stated in Run/ or Fmt/). A
   record can only add refusals. So the direction (F1), `pi_half`, needs no such hypothesis, and
   neither do `pi_formula`, `pi_kits` and the other parts; `pi_strict2` and `pi_core` (F2) alone
   have it. The test asks more than the page's own condition, which speaks of the roots that are
   read: it asks that all roots that the file sends differ, which is simple to run.

   Tried by one evaluation, not proved (not part of these files, at Fmt.formatHash). At the description of
   the first toy at the programs' own parameters, tiny parameters (Fmt/M1PlanKnownT.lean), on the 47
   files of Fmt/M1FilesT.lean as that set lay then (it has since changed):
      rootsDiffer holds on all 47;
      each of the three tests is the only one to fail on some file (passL on the three files cut
         anew behind a failing nonce; rootsAll on the two files named alt-05, alt-06; the decision
         on 30).
   (For `rootsDiffer`, tests by `#guard` are part of this library: `allDiffer` at the lists
   `filesT`, `filesR`, `filesF` that Run/M1EngineRoots.lean and Run/M2EngineRoots.lean each define;
   none of them is the set of Fmt/M1FilesT.lean; the tests run the form `rootsDifferF`,
   Run/RootsFast.lean, which is `rootsDiffer Fmt.formatHash` by `rootsF_eq`, Run/RootsFastProofs.lean.)

4. What is not claimed.
   No statement on soundness follows.
   Of a tree that the chain sends and never opens (the limits allow it) these theorems know 32 bytes
   that enter the hash chain, and nothing of what was committed under them: in the protocol its
   oracle is one word that nobody reads. That a later chain opens that root is outside them.
   Fmt.formatHash in the place of Fmt.HO O is the matter of other files (the hash function's domain, bounds
   on sizes: Run/LaxDom.lean, Run/StrictDom.lean).
   That Fmt/Rules8.lean renders the format page is not a theorem. One place that is not settled: by
   R2.7 a verifier refuses beyond R2.3's bounds on sizes (Run/LaxDom.lean's `smallB` is that test
   for the lenient reader's calls: four bounds, a hypothesis of that file's statements;
   `Spec.small`, the first clause of `Spec.ok`, has the first, the second and the fourth of them,
   and in place of the third a bound on each round's message). Sizes are a clause of Fmt.Spec.ok
   (ok_small, see "Sources"); whether that clause is all of R2.7 has not been looked up for this
   head.


   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Sources. Two editions of the format page are compared here, neither the one that ships; this file
follows the second.
By a comparison by program of every rule's text in these two editions, of the rules that the
middle term below renders
   these differ:
      the leaf's label (R2.1, R7.3, R7.4: through the leaves' hash);
      the record of vertices (R7.14);
      as conditions on the public description: a salt's length (R7.3), sizes (R2.7), a tree's depth
         (R7.16), which are clauses of Fmt.Spec.ok under the names ok_salt, ok_small, ok_depth
         (Fmt/Rules8Ok.lean);
      kind 2 with exactly one element and kind 4 with at least one position (R6.2, R6.10),
         conditions on an entry: whether Entry.fits (ok_fits) tests both has not been looked up for
         this head (`Entry.fits`, Fmt/Rules6Round.lean: at `.join` `e.drawE == 1`, at `.positions`
         `1 ≤ e.poss`; `Kind.num`, Fmt/Plan.lean: 2 at `.join`, 4 at `.positions`);
      R4.6 differs for stored tables alone, which the limits of the generic construction shut out;
      R7.7 in words alone. The same in these two editions: R4.4, R4.5, R5.2, R5.4, R5.5, R6.1,
   R6.6, R6.11, R7.9, R7.15, R8.8.
By a comparison of the same kind with a third edition (also not the one that ships; not held against
the page that ships): none of these eleven differs there; of the rules named above as differing,
R7.4, R7.14 and R4.6 (for stored tables) differ there from the second edition. R7.14 is treated
above.

Terms: lean/GLOSSARY.md.
-/
import Run.PlanQS
import Run.WalkTieProofs
import Run.LaxDom
import Run.ParseLaws
import Fmt.M1View

set_option autoImplicit false

namespace Run.PQ
open Rom Iop Compile Compile.Batch Run.Twin Run.Thin
open _root_.Fmt (Chain RoundOut ChainOut OpenOut Plan Src)

/-! ## The middle term -/

section
variable (h : HId)

/-- A round's blocks, made again from the round's message and nonce as read. -/
def rowBs (c : Chain) (r : _root_.Fmt.Round) (ro : RoundOut) : Array ByteArray :=
  _root_.Fmt.fetchW (m := Id) h c.label c.rho (c.round + 1) ro.msg r.kind r.entry.work ro.nonce
    (_root_.Fmt.firstBlock r.entry.work + (_root_.Fmt.wordsAtMost r.entry r.kind + 3) / 4)

/-- The chain after a round. -/
def nextOf (c : Chain) (r : _root_.Fmt.Round) (ro : RoundOut) : Chain :=
  ⟨c.label, _root_.Fmt.nextA r.entry.work (rowBs h c r ro), c.round + 1⟩

/-- Every round's proof-of-work test. -/
def passL : List _root_.Fmt.Round → List RoundOut → Chain → Bool
  | r :: rs, ro :: ros, c =>
    _root_.Fmt.passesA r.entry.work (rowBs h c r ro) && passL rs ros (nextOf h c r ro)
  | _, _, _ => true

/-- The root to which an opening walks. Every leaf starts from the run's value: right within the
limits of the generic construction (`PQ.ok`: own trees alone, none stored). -/
def rootOf (cfg run : ByteArray) (sh : _root_.Fmt.Shape) (xs : List ℕ) (op : OpenOut) : ByteArray :=
  (Octopus.octF (fun (l r : ByteArray) => (h 166 0 0 cfg (l ++ r) : ByteArray)) sh.a xs
    (WalkTie.leafV h sh run xs (op.cols.zip op.salts)) op.given).headD default

/-- Every opening walks to the root that was sent. -/
def rootsAll (cfg run : ByteArray) (ros : List RoundOut) : Bool :=
  ros.all fun ro => ro.opens.all fun x => rootOf h cfg run x.1 x.2.1 x.2.2 == x.2.2.root

/-- What an opening in the lenient reader's output is. -/
structure OpenFacts (P : Plan) (roots : Array ByteArray) (poss : List ℕ)
    (x : _root_.Fmt.Shape × Src) (y : _root_.Fmt.Shape × List ℕ × OpenOut) : Prop where
  sh   : y.1 = x.1
  xs   : y.2.1 = _root_.Fmt.listOf (poss.map (· % 2 ^ x.1.a))
  okl  : _root_.Fmt.listOK x.1.a y.2.1 = true
  root : (match x.2 with
    | .own n => roots[n]?
    | .given r _ => some r) = some y.2.2.root
  okb  : (⟨x.1.a, y.2.1, y.2.2.cols, y.2.2.salts, y.2.2.given⟩ : OpenB).ok P.salt x.1.W = true

/-- What the rounds of the lenient reader's output are. -/
def TraceL (P : Plan) : List _root_.Fmt.Round → List RoundOut → Chain → Array ByteArray → Prop
  | [], [], _, _ => True
  | r :: rs, ro :: ros, c, roots =>
      _root_.Fmt.askOK c.label c.rho (c.round + 1) ro.msg r.kind r.entry.work ro.nonce = true ∧
      _root_.Fmt.whole (_root_.Fmt.readItems P.field r.items) ro.msg = some ro.vals ∧
      ro.drawn =
        _root_.Fmt.drawRound P.field r.entry r.kind
          (_root_.Fmt.rowOf (_root_.Fmt.msgA r.entry.work (rowBs h c r ro))) ∧
      ro.list = _root_.Fmt.listOf ro.drawn.poss ∧
      List.Forall₂ (OpenFacts P (roots ++ (_root_.Fmt.rootsOf ro.vals).toArray) ro.drawn.poss)
        r.opens ro.opens ∧
      TraceL P rs ros (nextOf h c r ro) (roots ++ (_root_.Fmt.rootsOf ro.vals).toArray)
  | _, _, _, _ => False

/-- What the lenient reader's output is. -/
structure LaxFacts (S : _root_.Fmt.Spec) (o : ChainOut) : Prop where
  pd    : o.pd = h 169 0 1 _root_.Fmt.zero32 S.params
  run   : ∃ rnd : ByteArray,
    rnd.size = 32 ∧ o.run = some (h 172 0 S.label _root_.Fmt.zero32 (o.pd ++ rnd))
  rho0  : ∀ run, o.run = some run →
    o.rho0 = _root_.Fmt.firstValueW (m := Id) h S.label o.pd S.statement ByteArray.empty (some run)
  trace : TraceL h S.plan S.rounds o.rounds.toList ⟨S.label, o.rho0, 0⟩ #[]

end

/-- The view that the choice of challenge types C (the kit) gives of the wiring's message is the
format's draw on the first blocks. -/
def KitFits (f : _root_.Fmt.Fld) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) :
    Prop :=
  ∀ e k (u : Fin K → Dig 256), C.dr e k (chal e k u) =
    _root_.Fmt.drawRound f e k
      (rowOfDigs (firstBlocks 256 K (_root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost e k)) u))

/-! ## The verifier's side -/

section
variable (O : ByteArray → ByteArray) (S : _root_.Fmt.Spec) (C : CK) (K : ℕ)
  (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (dec : View → Bool)

/-- The evaluable form of the compiled verifier (`Thin.verifyP`) at the typed oracle functions that
O induces. -/
def VO (cm : Dig 256) (π : OneProtocolProof 256 (PSof C (rds S) dec).up) : Bool :=
  Thin.verifyP (lam := 256) (K := K + 1) (fun _ => LbS C (rds S) dec)
    (famOf O (PDS S C dec) (K + 1)) id none (256 + 8 * S.plan.salt) 256 .onl (PSof C (rds S) dec)
    (wqS C K chal (rds S) dec) (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩)) (embPS C (rds S) dec) some
    (fun s => some (.inl s)) 0 [cm] () π

/-- The verifier behind the lenient parser. -/
def laxV (file : ByteArray) : Bool :=
  match parseLaxWP (m := Id) (_root_.Fmt.HO O) (PSof C (rds S) dec) S (TYS S C dec) file with
  | some ([cm], π) => VO O S C K chal dec cm π
  | _ => false

/-- What the chain yields for the roots, round by round. It takes the first root of a round's items:
right within the limits of the generic construction (`PQ.ok`: at most one root a round). -/
def rtSL : (ds : List RD) → List RoundOut → RootsOfChain 256 (uL C ds)
  | [], _ => ()
  | _ :: ds, [] => ((none, some none), rtSL ds [])
  | _ :: ds, ro :: ros =>
    ((none, some ((_root_.Fmt.rootsOf ro.vals).head?.map bytesToDig)), rtSL ds ros)

end

/-- The roots that the file sends are pairwise different, as bytes; true where the lenient reader
does not read. -/
def rootsDiffer (h : HId) (S : _root_.Fmt.Spec) (file : ByteArray) : Bool :=
  match laxWhole (m := Id) h S file with
  | none => true
  | some o => decide ((rootsB o).map ByteArray.data).Nodup

namespace Spec

def pi_facts : Prop :=
  ∀ (h : HId), (∀ n t i s b, ByteArray.size (h n t i s b) = _root_.Fmt.dlen n) →
    ∀ (S : _root_.Fmt.Spec) (b : ByteArray) (o : ChainOut),
      ok S = true → laxWhole (m := Id) h S b = some o → LaxFacts h S o

def pi_strict1 : Prop :=
  ∀ (h : HId), (∀ n t i s b, ByteArray.size (h n t i s b) = _root_.Fmt.dlen n) →
    ∀ (S : _root_.Fmt.Spec) (b : ByteArray) (o' : ChainOut), ok S = true →
      _root_.Fmt.wholeChain (m := Id) h S b = some o' →
      ∃ o run,
        laxWhole (m := Id) h S b = some o ∧
        o.run = some run ∧
        _root_.Fmt.viewOf S.firstTree o = _root_.Fmt.viewOf S.firstTree o' ∧
        passL h S.rounds o.rounds.toList ⟨S.label, o.rho0, 0⟩ = true ∧
        rootsAll h S.cfg run o.rounds.toList = true

def pi_strict2 : Prop :=
  ∀ (h : HId), (∀ n t i s b, ByteArray.size (h n t i s b) = _root_.Fmt.dlen n) →
    ∀ (S : _root_.Fmt.Spec) (b : ByteArray) (o : ChainOut) (run : ByteArray), ok S = true →
      laxWhole (m := Id) h S b = some o → o.run = some run →
      passL h S.rounds o.rounds.toList ⟨S.label, o.rho0, 0⟩ = true →
      rootsAll h S.cfg run o.rounds.toList = true → rootsDiffer h S b = true →
      ∃ o',
        _root_.Fmt.wholeChain (m := Id) h S b = some o' ∧
        _root_.Fmt.viewOf S.firstTree o' = _root_.Fmt.viewOf S.firstTree o

def pi_chain : Prop :=
  ∀ (O : ByteArray → ByteArray), (∀ s, (O s).size = 32) →
    ∀ (S : _root_.Fmt.Spec) (C : CK) (K : ℕ)
        (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (dec : View → Bool),
      ok S = true → KitFits S.plan.field C K chal →
      (∀ r ∈ S.rounds, _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind) ≤ K) →
      ∀ (o : ChainOut) (run : ByteArray) (pl : Plains (uL C (rds S))),
        LaxFacts (_root_.Fmt.HO O) S o → o.run = some run →
        plainsSL C (rds S) o.rounds.toList = some pl →
        ∃ (ρ : Rho (uL C (rds S))) (v : Bits),
          chainP (fun _ => LbS C (rds S) dec) (famOf O (PDS S C dec) (K + 1)) id none .onl
              [bytesToDig o.pd] (some () : Option Unit) (bytesToBits run) (fun _ => false)
              (SOf C (rds S)) (allLo (SOf C (rds S))) (wqS C K chal (rds S) dec).sh
              (embPS C (rds S) dec) 0 .first ((rootsB o).map bytesToDig) ((), pl) =
            some ((default, ρ), ((none, some none), rtSL C (rds S) o.rounds.toList), .loc v) ∧
          drawnSL C (rds S) ρ = o.rounds.toList.map (·.drawn) ∧
          passSL C (rds S) ρ = passL (_root_.Fmt.HO O) S.rounds o.rounds.toList ⟨S.label, o.rho0, 0⟩

def pi_typed : Prop :=
  ∀ (h : HId) (S : _root_.Fmt.Spec) (C : CK) (dec : View → Bool) (o : ChainOut), ok S = true →
    LaxFacts h S o →
    ∃ (run : ByteArray) (pl : Plains (uL C (rds S))),
      o.run = some run ∧
      plainsSL C (rds S) o.rounds.toList = some pl ∧
      toBPrfP (PSof C (rds S) dec) (TYS S C dec) o =
        some ([bytesToDig o.pd],
            mkBPrfP (PSof C (rds S) dec) run (rootsB o) ((), pl) (opensAt (TYS S C dec).up run o))

def pi_after : Prop :=
  ∀ (O : ByteArray → ByteArray), (∀ s, (O s).size = 32) →
    ∀ (S : _root_.Fmt.Spec) (C : CK) (K : ℕ)
        (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (dec : View → Bool),
      ok S = true →
      ∀ (o : ChainOut) (run : ByteArray) (pl : Plains (uL C (rds S)))
          (ρ : Rho (uL C (rds S))) (v : Bits),
        LaxFacts (_root_.Fmt.HO O) S o → o.run = some run →
        plainsSL C (rds S) o.rounds.toList = some pl →
        drawnSL C (rds S) ρ = o.rounds.toList.map (·.drawn) →
        strictP (256 + 8 * S.plan.salt) 256 (PSof C (rds S) dec) (wqS C K chal (rds S) dec) 0 ()
            (mkBPrfP (PSof C (rds S) dec) run (rootsB o) ((), pl) (opensAt (TYS S C dec).up run o))
            (default, ρ) ((none, some none), rtSL C (rds S) o.rounds.toList) (.loc v) = true ∧
        afterP (fun _ => LbS C (rds S) dec) (famOf O (PDS S C dec) (K + 1)) (PSof C (rds S) dec)
            (wqS C K chal (rds S) dec) (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩))
            (fun s => some (.inl s)) 0 [bytesToDig o.pd] ()
            (mkBPrfP (PSof C (rds S) dec) run (rootsB o) ((), pl) (opensAt (TYS S C dec).up run o))
            (default, ρ) ((none, some none), rtSL C (rds S) o.rounds.toList) (.loc v) =
          (rootsAll (_root_.Fmt.HO O) S.cfg run o.rounds.toList &&
            (passSL C (rds S) ρ && dec (_root_.Fmt.viewOf S.firstTree o)))

/-- The hypotheses on oracle, description and choice of challenge types. -/
structure PiFit (O : ByteArray → ByteArray) (S : _root_.Fmt.Spec) (C : CK) (K : ℕ)
    (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) : Prop where
  size : ∀ s, (O s).size = 32
  ok   : PQ.ok S = true
  kit  : KitFits S.plan.field C K chal
  room : ∀ r ∈ S.rounds, _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind) ≤ K

/-- The verifier behind the lenient parser, as a formula on what the lenient reader hands out. -/
def pi_formula : Prop :=
  ∀ (O : ByteArray → ByteArray) (S : _root_.Fmt.Spec) (C : CK) (K : ℕ)
      (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (dec : View → Bool) (file : ByteArray),
    PiFit O S C K chal →
    laxV O S C K chal dec file = match laxWhole (m := Id) (_root_.Fmt.HO O) S file with
      | none => false
      | some o =>
        passL (_root_.Fmt.HO O) S.rounds o.rounds.toList ⟨S.label, o.rho0, 0⟩ &&
          rootsAll (_root_.Fmt.HO O) S.cfg (o.run.getD default) o.rounds.toList &&
          dec (_root_.Fmt.viewOf S.firstTree o)

/-- States, under `PiFit`: (F1) What the format's verifier (`Fmt.verifyW`) accepts, the compiled
verifier behind the lenient parser accepts. -/
def pi_half : Prop :=
  ∀ (O : ByteArray → ByteArray) (S : _root_.Fmt.Spec) (C : CK) (K : ℕ)
      (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (dec : View → Bool) (file : ByteArray),
    PiFit O S C K chal →
    _root_.Fmt.verifyW (m := Id) (_root_.Fmt.HO O) S (fun (_ : Unit) => dec) () file = true →
    laxV O S C K chal dec file = true

/-- States, under `PiFit`: (F2) Where the roots that the file sends differ, the two give one
verdict. -/
def pi_core : Prop :=
  ∀ (O : ByteArray → ByteArray) (S : _root_.Fmt.Spec) (C : CK) (K : ℕ)
      (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (dec : View → Bool) (file : ByteArray),
    PiFit O S C K chal → rootsDiffer (_root_.Fmt.HO O) S file = true →
    laxV O S C K chal dec file =
      _root_.Fmt.verifyW (m := Id) (_root_.Fmt.HO O) S (fun (_ : Unit) => dec) () file

/-- States: two choices of challenge types that fit (`PiFit` at both) give one verdict. -/
def pi_kits : Prop :=
  ∀ (O : ByteArray → ByteArray) (S : _root_.Fmt.Spec) (C : CK) (K : ℕ)
      (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (C' : CK) (K' : ℕ)
      (chal' : ∀ e k, (Fin K' → Dig 256) → C'.Ch e k) (dec : View → Bool) (file : ByteArray),
    PiFit O S C K chal → PiFit O S C' K' chal' →
    laxV O S C K chal dec file = laxV O S C' K' chal' dec file

end Spec
end Run.PQ
