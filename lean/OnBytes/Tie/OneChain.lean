-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/OneChain.lean: one accepted chain, and the compiled verifier of the library's theory.

A chain is one run of rounds in a file: in each round the prover sends a message, and a hash of all
that went before gives the verifier's draws. Its description (`Fmt.Spec`) says what each round
sends, draws and opens. A decision is a function from what was read (the view) to yes or no. The
record of tree vertices is the reader's list of the hash-tree nodes that it has met
(OnBytes/Chain/Session.lean).

The library turns a chain's description S and a decision dec into a protocol (Run/PlanQS.lean). It
types what a reader has read of a chain as a proof string of that protocol. And it proves, for a
file that holds one chain and nothing else: if the strict reader reads the file and dec says yes,
then the compiled verifier of that protocol accepts the typed string (Run/PageIsProofs.lean). The
compiled verifier is `Compile.Batch.verifyOneProtocol`: the verifier of one slot, with the strict format,
that the library's compiled scheme calls.

A real file holds several chains, and one verdict reads several files. So this file proves it for
a chain that begins at any byte, under any record of tree vertices, and whose 32 random bytes are
in the file or are given by the description. The typed string is named: it is the library's typing
of what the strict reader has read (`typedOf`).

The limits (`within`). They are the five clauses of the library's `Run.PQ.ok`, the last one made
wider. `inFile S` is in order (`Fmt.Spec.ok`). A round sends at most one root. The chain opens its
own trees only. It opens each tree that it sends at most once. It has random bytes, in the file or
given (the library: in the file). A description outside these limits is not covered. Of the chains
that the program reads, those of the two small test protocols are within the limits at the C++
programs' tiny and full parameters (ToysClosed.lean).


A tree that is sent and never opened. The library types it as a tree of depth 0 with one word in
each column. Of such a tree the compiled verifier knows the 32 bytes of its root, which enter the
hash chain, and nothing more. Whatever the library's theorems give for a prover's table, they give
here for one word that nobody reads, not for the table that the prover committed under that root.
That a later chain opens the same root is no matter of this file.

So "within the limits" does not say that a chain opens every tree that it sends. A description from
which an opening was left out by mistake is still within them: its verifier checks less, and every
theorem of this directory holds of it. For a description that is meant to open all its trees there
is a test beside the limits, `eachOnce` (OnBytes/Tie/Limits.lean). It is evaluated in
TestLimits.lean and TestKeyOneTime.lean (tests, not theorems, and not beyond their descriptions), and it is a theorem at the entries (`rounds0`, `roundsRL`,
`roundsSL`) and at the four descriptions of ToysClosed.lean (`once_product_tiny` and its three kin).

Main definitions: `within`, `typedOf`, `CompiledAcceptsAt`, `CompiledAccepts`.
Main theorems: `within_iff`, `read_facts`, `vo_true`, `vo_compiled`, `read_compiled`,
`plain_compiled`.

Which protocol. An empty round in front, then the description's rounds. It has no statement and no
index of its own: both are the type with one element. It accepts if every proof of work passes and
dec says yes on the view. So all that a chain proves is inside dec. The honest sides, the encoding
and the decoder of the library's interface are placeholders. The chain's label, its statement's
bytes and the configuration's digest (`cfg`) are no inputs of the compiled verifier: they are built
into the typed oracle functions, which are thus made from the hash and from the description.

Which verifier. `verifyOneProtocol` is a general function. Here it is applied to a protocol, a wiring and an
interface that the library makes from the description (the interface is the argument `L`). No
theorem of this directory says that this term is a verifier of the library's compiled scheme (`vBS`,
`vLS`), nor that its wiring obeys the scheme's laws.

Why nothing on soundness follows. Much is missing, not just one step. For the relation that holds of
everything, with error 0, the library proves "sound" the interfaces that this directory's
conclusions use (`Run.BatchDoor.lb_sound`, `Run.PQ.lu_sound`). In its own words that is true and
empty: without a statement and an index, and with a decoder that accepts every string, nothing lies
outside the language, and nothing is asked of any round. (Without stored tables no language has
content; by the head of Run/BatchDoor.lean only a theorem with a witness could. With stored tables
there are the two tables' strings: OnBytes/Tie/StoredMain.lean.) So a sentence that joins those
theorems with the ones here would mean nothing. No theorem of this directory says what a yes of dec
is worth. By the heads of Run/BatchDoor.lean and Run/PlanQXDoor.lean, nothing in the library's Run/
or Fmt/ proves soundness with any content for the protocols at these interfaces. And the library's
soundness theorems speak of runs within the traces of random oracles, not of a run at functions made
from one fixed hash.

What else is not claimed. The converse: the strict reader refuses more than the compiled verifier
does. The compiled verifier does not see the chain's random bytes, only the value hashed from them.
That a description meets `within` is a theorem at four sets of parameter bytes alone
(OnBytes/Tie/ToysClosed.lean). For any other, also one that a call derives from another public file,
it is a test to be evaluated. Typed queries are answered at the strings of the format's hash calls;
that queries go to strings one-to-one is not claimed. How one chain's values enter the next chain's
description is no matter of this file.
-/
import Run.PageIsProofs
import Run.StrictDomProofs
import Run.ParseLaxXIsProofs
import OnBytes.Tie.Stages
import OnBytes.Tie.Limits

set_option autoImplicit false

namespace OnBytes.Tie
open Rom Iop Compile Compile.Batch Run Run.PQ Run.Twin Run.Thin

/-- The limits within which the theorems of this file hold. -/
def within (S : Fmt.Spec) : Bool := Run.PQ.ok (inFile S) && !S.rand.isNone

/-- The limits, clause by clause, in the words of OnBytes/Tie/Limits.lean. -/
theorem within_eq (S : Fmt.Spec) :
    within S = ((inFile S).ok && oneRoot S && ownOnly S && atMostOnce S && !S.rand.isNone) := by
  show ((inFile S).ok && oneRoot S && ownOnly S && atMostOnce S && true && !S.rand.isNone) = _
  rw [Bool.and_true]

/-- A description is within the limits exactly if the test of OnBytes/Tie/Limits.lean names no
limit that it breaks. -/
theorem within_iff (S : Fmt.Spec) : within S = true ↔ limitsOf S = [] := by
  rw [within_eq]
  unfold limitsOf
  cases (inFile S).ok <;> cases oneRoot S <;> cases ownOnly S <;> cases atMostOnce S <;>
    cases S.rand.isNone <;> simp

/-- "Exactly once" gives "at most once". -/
theorem once_le (l : List Nat) (f : Nat → Nat) (h : (l.all fun n => f n == 1) = true) :
    (l.all fun n => decide (f n ≤ 1)) = true := by
  rw [List.all_eq_true] at h ⊢
  intro n hn
  exact decide_eq_true (Nat.le_of_eq (beq_iff_eq.1 (h n hn)))

/-- A trace has as many rounds as the description. -/
theorem trace_len (h : Run.HId) (P : Fmt.Plan) :
    ∀ (rs : List Fmt.Round) (ros : List Fmt.RoundOut) (c : Fmt.Chain) (roots : Array ByteArray),
      TraceL h P rs ros c roots → ros.length = rs.length
  | [], [], _, _, _ => rfl
  | _ :: rs, _ :: ros, _, _, t => by
    obtain ⟨-, -, -, -, -, t'⟩ := t
    exact congrArg (· + 1) (trace_len h P rs ros _ _ t')
  | [], _ :: _, _, _, t => t.elim
  | _ :: _, [], _, _, t => t.elim

/-- Within the limits, let the strict reader have read o', at any byte and under any record. Then
some o has the rounds of o' without the vertices met, and its run value, parameters' digest and
view. This o has the library's `LaxFacts`, all its work passes, and all its openings walk to their
roots. -/
theorem read_facts (h : Run.HId) (S : Fmt.Spec) (hw : within S = true) (seen : Fmt.Seen)
    (b : ByteArray) (i : Nat) (o' : Fmt.ChainOut) (j : Nat)
    (e : Fmt.readChain (m := Id) h S seen b i = some (o', j)) :
    ∃ o : Fmt.ChainOut, LaxFacts h (inFile S) o ∧
      (o.rounds.toList = o'.rounds.toList.map stripR ∧ o.run = o'.run ∧ o.pd = o'.pd) ∧
      Fmt.viewOf S.firstTree o = Fmt.viewOf S.firstTree o' ∧
      o'.rounds.size = S.rounds.length ∧
      passL h S.rounds o.rounds.toList ⟨S.label, o.rho0, 0⟩ = true ∧
      rootsAll h S.cfg (o.run.getD default) o.rounds.toList = true := by
  have hw' := Bool.and_eq_true_iff.1 hw
  have hok : Run.PQ.ok (inFile S) = true := hw'.1
  have hn : S.rand.isNone = false := by simpa using hw'.2
  have hown : ∀ r ∈ S.rounds, ∀ x ∈ r.opens, ∃ n, x.2 = .own n := own_of_ok (inFile S) hok
  obtain ⟨-, x, i0, hd, s, hr, hst, hf, rfl, rfl⟩ := read_stages h S seen b i o' j e
  obtain ⟨rnd, rfl⟩ := rnd_some S b i x i0 hn hr
  obtain ⟨hdrun, rho0⟩ := hd
  obtain ⟨h32, hrun, hrho⟩ := startChain_some h _ _ _ _ _ hst
  obtain ⟨R, hR⟩ : ∃ R : ByteArray, hdrun = some R := ⟨_, hrun⟩
  subst hR
  obtain ⟨ros, g1, g2, g3, g4⟩ := fold_lax h S.cfg S.plan R b S.rounds _ s [] #[] hown hf
  obtain ⟨ros', k1, k2⟩ := cutFold_facts h S.plan _ b S.rounds _ _ g2
  have g1' : s.out.toList = ros := by simpa using g1
  have k1' : ros' = ros.map stripR := by simpa using k1.symm
  subst k1'
  have ht : ((ros.map stripR).toArray).toList = ros.map stripR := by simp
  refine ⟨⟨h 169 0 1 Fmt.zero32 S.params, some R, rho0, s.chain.rho, [],
    (ros.map stripR).toArray⟩, ⟨rfl, ⟨rnd, h32, hrun⟩, ?_, ?_⟩, ⟨?_, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro r hr'
    have hr2 : some r = some _ := hr'.symm.trans hrun
    rw [Option.some.inj hr2]
    exact hrho
  · show TraceL h S.plan S.rounds ((ros.map stripR).toArray).toList ⟨S.label, rho0, 0⟩ #[]
    rw [ht]
    exact k2
  · show ((ros.map stripR).toArray).toList = s.out.toList.map stripR
    rw [ht, g1']
  · exact view_strip S.firstTree _ _ _ _ _ _ _ ros _ _ ht g1'
  · have hlen := trace_len h S.plan S.rounds _ _ _ k2
    have hsz : s.out.size = ros.length := by simpa using congrArg List.length g1'
    show s.out.size = S.rounds.length
    rw [hsz, ← hlen, List.length_map]
  · show passL h S.rounds ((ros.map stripR).toArray).toList ⟨S.label, rho0, 0⟩ = true
    rw [ht]
    exact g3
  · show rootsAll h S.cfg R ((ros.map stripR).toArray).toList = true
    rw [ht]
    exact g4

/-- The library's typing does not look at the vertices met. -/
theorem typed_strip (S : Fmt.Spec) (C : CK) (dec : Fmt.View → Bool) (o o' : Fmt.ChainOut)
    (e1 : o.rounds.toList = o'.rounds.toList.map stripR) (e2 : o.run = o'.run)
    (e3 : o.pd = o'.pd) :
    toBPrfP (PSof C (rds S) dec) (TYS S C dec) o'
      = toBPrfP (PSof C (rds S) dec) (TYS S C dec) o := by
  have hB := lxi_opensB o o' e1
  have hR := lxi_rootsB o o' e1
  have hP : (TYS S C dec).plains o'.rounds = (TYS S C dec).plains o.rounds := by
    show (plainsSL C (rds S) o'.rounds.toList).map _ = (plainsSL C (rds S) o.rounds.toList).map _
    rw [e1, lxi_plains]
  unfold toBPrfP
  rw [← e2, hP, ← hB, ← hR, ← e3]

/-- Under `fit` (see `read_compiled`): if o has `LaxFacts`, all work passes, all openings walk to
their roots and the decision is yes, then the library's typing gives a typed string, and the
evaluable form of the compiled verifier accepts it. Its key is the digest of the description's
parameters: no value of a file. -/
theorem vo_true (O : ByteArray → ByteArray) (S : Fmt.Spec) (C : CK) (K : ℕ)
    (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (dec : Fmt.View → Bool)
    (fit : Spec.PiFit O S C K chal) (o : Fmt.ChainOut) (hf : LaxFacts (Fmt.HO O) S o)
    (hp : passL (Fmt.HO O) S.rounds o.rounds.toList ⟨S.label, o.rho0, 0⟩ = true)
    (hro : rootsAll (Fmt.HO O) S.cfg (o.run.getD default) o.rounds.toList = true)
    (hd : dec (Fmt.viewOf S.firstTree o) = true) :
    ∃ π : OneProtocolProof 256 (PSof C (rds S) dec).up,
      toBPrfP (PSof C (rds S) dec) (TYS S C dec) o = some ([bytesToDig o.pd], π) ∧
      VO O S C K chal dec (bytesToDig (Fmt.HO O 169 0 1 Fmt.zero32 S.params)) π = true := by
  obtain ⟨run, pl, hr, hpl, hty⟩ := pi_typed' (Fmt.HO O) S C dec o hf
  have hro' : rootsAll (Fmt.HO O) S.cfg run o.rounds.toList = true := by
    rw [hr] at hro
    exact hro
  obtain ⟨ρ, v, hc, hdr, hps⟩ :=
    pi_chain O fit.size S C K chal dec fit.ok fit.kit fit.room o run pl hf hr hpl
  obtain ⟨a1, a2⟩ := pi_after O fit.size S C K chal dec fit.ok o run pl ρ v hf hr hpl hdr
  refine ⟨mkBPrfP (PSof C (rds S) dec) run (rootsB o) ((), pl)
    (opensAt (TYS S C dec).up run o), hty, ?_⟩
  rw [← hf.pd]
  unfold VO verifyP
  have hc' : chainP (fun _ => LbS C (rds S) dec) (Run.famOf O (PDS S C dec) (K + 1)) id none .onl
      [bytesToDig o.pd] ((some : Unit → Option Unit) ())
      (mkBPrfP (PSof C (rds S) dec) run (rootsB o) ((), pl) (opensAt (TYS S C dec).up run o)).salt
      (mkBPrfP (PSof C (rds S) dec) run (rootsB o) ((), pl) (opensAt (TYS S C dec).up run o)).rtreq
      (PSof C (rds S) dec).S (PSof C (rds S) dec).ann (wqS C K chal (rds S) dec).sh
      (embPS C (rds S) dec) 0 .first
      (mkBPrfP (PSof C (rds S) dec) run (rootsB o) ((), pl) (opensAt (TYS S C dec).up run o)).roots
      (mkBPrfP (PSof C (rds S) dec) run (rootsB o) ((), pl)
        (opensAt (TYS S C dec).up run o)).plains
      = some ((default, ρ), ((none, some none), rtSL C (rds S) o.rounds.toList), .loc v) := hc
  rw [hc']
  dsimp only
  rw [a1, if_pos rfl, a2, hps, hro', hp, hd]
  rfl

/-- The evaluable form is the run of the compiled verifier of one slot, at the typed oracle
functions that a function O on the format's strings induces. -/
theorem vo_compiled (O : ByteArray → ByteArray) (S : Fmt.Spec) (C : CK) (K : ℕ)
    (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (dec : Fmt.View → Bool) (cm : Dig 256)
    (π : OneProtocolProof 256 (PSof C (rds S) dec).up) :
    VO O S C K chal dec cm π =
      (verifyOneProtocol (lam := 256) (K := K + 1) (L := LbS C (rds S) dec) (256 + 8 * S.plan.salt) 256
        .onl (PSof C (rds S) dec).up (wqS C K chal (rds S) dec)
        (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩)) (embPS C (rds S) dec) some
        (fun s => some (.inl s)) 0 [cm] () π).det (Run.famOf O (PDS S C dec) (K + 1)) :=
  thin_verify Unit Unit 256 (K + 1) (LbS C (rds S) dec) (Run.famOf O (PDS S C dec) (K + 1)) Unit E0
    (256 + 8 * S.plan.salt) 256 .onl (PSof C (rds S) dec) (wqS C K chal (rds S) dec) _ _ some
    (fun s => some (.inl s)) 0 [cm] () π

/-- The typed string that the library's typing makes from what was read of a chain. -/
def typedOf (S : Fmt.Spec) (C : CK) (dec : Fmt.View → Bool) (o : Fmt.ChainOut) :
    Option (OneProtocolProof 256 (PSof C (rds (inFile S)) dec).up) :=
  (toBPrfP (PSof C (rds (inFile S)) dec) (TYS (inFile S) C dec) o).map (·.2)

/-- "The compiled verifier accepts what was read." o is what the strict reader has read of a
chain. The library's typing makes a typed string from o, and on that string the compiled verifier
of one slot says yes. The protocol is the one that the library makes from the description S and the
decision dec. The key is the digest of the description's parameters. The typed oracle functions are
those that O, a function on the format's strings, induces. C, K and chal say how a round's hash
blocks become the verifier's message. -/
def CompiledAcceptsAt (O : ByteArray → ByteArray) (S : Fmt.Spec) (C : CK) (K : ℕ)
    (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (dec : Fmt.View → Bool) (o : Fmt.ChainOut) :
    Prop :=
  ∃ π : OneProtocolProof 256 (PSof C (rds (inFile S)) dec).up, typedOf S C dec o = some π ∧
    (verifyOneProtocol (lam := 256) (K := K + 1) (L := LbS C (rds (inFile S)) dec)
      (256 + 8 * S.plan.salt) 256 .onl (PSof C (rds (inFile S)) dec).up
      (wqS C K chal (rds (inFile S)) dec) (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩))
      (embPS C (rds (inFile S)) dec) some (fun s => some (.inl s)) 0
      [bytesToDig (Fmt.HO O 169 0 1 Fmt.zero32 S.params)] () π).det
      (Run.famOf O (PDS (inFile S) C dec) (K + 1)) = true

/-- The same at the format's own hash. Verifier messages are the round's hash blocks, the form
that the library's laws on wirings ask for. -/
def CompiledAccepts (S : Fmt.Spec) (dec : Fmt.View → Bool) (o : Fmt.ChainOut) : Prop :=
  CompiledAcceptsAt Fmt.oracle S (ckP S.plan.field) (kOf (inFile S))
    (chalP S.plan.field (kOf (inFile S))) dec o

/-- A chain that the strict reader has read, at any byte and under any record, and on which the
decision is yes: the compiled verifier accepts what was read. The reader runs at the hash that O
induces. The hypothesis `fit` gathers four conditions: O's answers have 32 bytes; the description,
with its random bytes taken as standing in the file, is within the library's limits; C, K and chal
turn a round's hash blocks into the format's draws; and K blocks are enough for every round. The
chain has random bytes (`hn`). -/
theorem read_compiled (O : ByteArray → ByteArray) (S : Fmt.Spec) (C : CK) (K : ℕ)
    (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (dec : Fmt.View → Bool)
    (fit : Spec.PiFit O (inFile S) C K chal) (hn : S.rand.isNone = false) (seen : Fmt.Seen)
    (b : ByteArray) (i : Nat) (o' : Fmt.ChainOut) (j : Nat)
    (e : Fmt.readChain (m := Id) (Fmt.HO O) S seen b i = some (o', j))
    (hd : dec (Fmt.viewOf S.firstTree o') = true) : CompiledAcceptsAt O S C K chal dec o' := by
  have hw : within S = true := by
    unfold within
    rw [fit.ok, hn]
    rfl
  obtain ⟨o, hf, ⟨e1, e2, e3⟩, hview, -, hp, hro⟩ := read_facts (Fmt.HO O) S hw seen b i o' j e
  obtain ⟨π, hty, hπ⟩ := vo_true O (inFile S) C K chal dec fit o hf hp hro (by
    show dec (Fmt.viewOf S.firstTree o) = true
    rw [hview]
    exact hd)
  refine ⟨π, ?_, (vo_compiled O (inFile S) C K chal dec _ π).symm.trans hπ⟩
  unfold typedOf
  rw [typed_strip (inFile S) C dec o o' e1 e2 e3, hty]
  rfl

/-- A description in order has one list of stored tables for each round. -/
theorem specX_len (S : Fmt.SpecX) (hS : S.ok = true) :
    S.stored.length = S.base.rounds.length := by
  unfold Fmt.SpecX.ok at hS
  simp only [Bool.and_eq_true, beq_iff_eq] at hS
  exact hS.1.2

/-- A description in order that breaks no limit opens no stored table. -/
theorem plain_of_limits (S : Fmt.SpecX) (hok : S.ok = true) (hl : limitsOfX S = []) :
    S = Fmt.SpecX.plain S.base ∧ limitsOf S.base = [] := by
  unfold limitsOfX at hl
  obtain ⟨h1, h2⟩ := List.append_eq_nil_iff.1 hl
  refine ⟨?_, h1⟩
  have hall : S.stored.all (·.isEmpty) = true := by
    by_contra hc
    rw [if_neg hc] at h2
    cases h2
  have hlen := specX_len S hok
  have key : ∀ (l : List (List Fmt.Stored)) (rs : List Fmt.Round), l.all (·.isEmpty) = true →
      l.length = rs.length → l = rs.map fun _ => [] := by
    intro l
    induction l with
    | nil =>
      intro rs _ h
      cases rs with
      | nil => rfl
      | cons _ _ => cases h
    | cons a l ih =>
      intro rs ha h
      cases rs with
      | nil => cases h
      | cons r rs =>
        rw [List.all_cons, Bool.and_eq_true] at ha
        rw [List.map_cons, List.isEmpty_iff.1 ha.1, ih rs ha.2 (by simpa using h)]
  show S = ⟨S.base, S.base.rounds.map fun _ => []⟩
  conv_lhs => rw [show S = ⟨S.base, S.stored⟩ from rfl, key S.stored S.base.rounds hall hlen]

/-- The strict reader reads under a description in order only. -/
theorem readX_ok (h : Run.HId) (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : Nat)
    (x : Fmt.ChainOut × Nat) (e : Fmt.readChainX (m := Id) h S seen b i = some x) :
    S.ok = true := by
  unfold Fmt.readChainX at e
  split at e
  · cases e
  · rename_i hok
    simpa using hok

/-- Within the limits, the sizes that the hash's domain asks for follow from the description's
being in order, but for the file's own size. -/
theorem smallF_of_within (S : Fmt.Spec) (hw : within S = true) (b : ByteArray)
    (hb : b.size + 16 ≤ 2 ^ 32 - 144) : Run.smallF S b = true := by
  have hok : Run.PQ.ok (inFile S) = true := (Bool.and_eq_true_iff.1 hw).1
  have hS : (inFile S).ok = true := by
    unfold Run.PQ.ok at hok
    simp only [Bool.and_eq_true] at hok
    exact hok.1.1.1.1
  have hsm : (inFile S).small = true := Fmt.ok_small hS
  unfold Fmt.Spec.small at hsm
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hsm
  obtain ⟨⟨⟨⟨s1, s2⟩, -⟩, s4⟩, s5⟩ := hsm
  have htr := Fmt.ok_trees hS
  have hdp := Fmt.ok_depth hS
  simp only [List.all_eq_true, decide_eq_true_eq] at htr hdp
  unfold Run.smallF Run.smallB
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  have hcfg : ((inFile S).cfg.size == 32) = true := Fmt.ok_cfg hS
  refine ⟨⟨⟨⟨⟨s1, s2⟩, hb⟩, s5⟩, hcfg⟩, fun r hr o ho => ?_⟩
  obtain ⟨n, g⟩ := tab_good (inFile S) (tab_limits (inFile S) hok) r hr o ho
  unfold Run.smallO Run.smallSh
  have hd : o.1.a ≤ 48 := by
    have := hdp r hr o ho
    unfold Fmt.depthOK at this
    exact of_decide_eq_true this
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨htr r hr o ho, hd⟩, (s4 r hr o ho).1⟩, (s4 r hr o ho).2⟩, Or.inl g.plain⟩, ?_⟩
  rw [g.src]

/-- The same in the form that fits the program: the reader is the one for descriptions that may
open stored tables, at the format's own hash, and the description breaks no limit. The bound on the
file's size keeps every hashed string within the hash's domain. -/
theorem plain_compiled (S : Fmt.SpecX) (dec : Fmt.View → Bool) (hl : limitsOfX S = [])
    (seen : Fmt.Seen) (b : ByteArray) (i : Nat) (hb : b.size + 16 ≤ 2 ^ 32 - 144)
    (o : Fmt.ChainOut) (j : Nat) (e : Fmt.readChainX (m := Id) Fmt.formatHash S seen b i = some (o, j))
    (hd : dec (Fmt.viewX S o) = true) : CompiledAccepts S.base dec o := by
  obtain ⟨hp, hlb⟩ := plain_of_limits S (readX_ok Fmt.formatHash S seen b i _ e) hl
  have hw : within S.base = true := (within_iff _).2 hlb
  have hs : Run.smallF S.base b = true := smallF_of_within S.base hw b hb
  have hw' := Bool.and_eq_true_iff.1 hw
  have hn : S.base.rand.isNone = false := by simpa using hw'.2
  have hrd1 : Fmt.readChain (m := Id) Fmt.formatHash S.base seen b i = some (o, j) := by
    rw [hp, Fmt.X8.readChain_plain] at e
    exact e
  have hrd2 : Fmt.readChain (m := Id) (Fmt.HO Fmt.oracle) S.base seen b i = some (o, j) :=
    (Run.readChain_dom (h := Fmt.formatHash) (h' := Fmt.HO Fmt.oracle)
      (fun n t i s b hd => Fmt.HO_oracle n t i s b hd) (fun n t i s b => Fmt.size_H n t i s b)
      S.base seen b i hs).trans hrd1
  obtain ⟨-, -, -, -, hsize, -, -⟩ := read_facts (Fmt.HO Fmt.oracle) S.base hw seen b i o j hrd2
  have hv : Fmt.viewX S o = Fmt.viewOf S.base.firstTree o := by
    rw [hp]
    exact Fmt.X8.plain_view S.base o hsize
  rw [hv] at hd
  exact read_compiled Fmt.oracle S.base (ckP S.base.plan.field) (kOf (inFile S.base))
    (chalP S.base.plan.field (kOf (inFile S.base))) dec (fit_pull (inFile S.base) hw'.1) hn seen b
    i o j hrd2 hd

end OnBytes.Tie

#print axioms OnBytes.Tie.within_iff
#print axioms OnBytes.Tie.read_facts
#print axioms OnBytes.Tie.vo_true
#print axioms OnBytes.Tie.vo_compiled
#print axioms OnBytes.Tie.read_compiled
#print axioms OnBytes.Tie.plain_compiled
