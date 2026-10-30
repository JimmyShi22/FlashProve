-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/Batch.lean: N-slot batch IOPs (interactive oracle proofs for N slots, which may share rounds),
and the interface between layers 1 and 2 with batches (`BatchProtocol`). After the work that this protocol
builds on (lean/CREDITS.md, "Further work").

Definitions only, but for three lemmas (`RAnn.ofSlot_coherent`, `RAnn.ofShared_coherent`,
`BatchHonestProver.HVZK.of_exact`). Layer 1 is the compiler (Compile/), layer 2 the interactive protocols that
it compiles. How further masked copies of one commitment are tied to the first by links is not
specified in this file. Other files of Iop/ say protocol with slots for batch IOP, record of
protocols for interface, list of rounds for shape, challenge for verifier message.

How a batch IOP is written. Each non-empty slot has a local verifier V_j, a copy of one algorithm,
which sees the local transcript τ_j = (x_j, all m_0, m_j, ρ_0, ρ_j). So the primary datum is one
ordinary IOP, `loc : InteractiveOracleProof X E`, whose transcripts are the local transcripts. What makes it a batch
IOP is an annotation of its shape (`RoundSplits`): for each round, whether the verifier message is shared
or local, and how a prover message of the local transcript splits into the shared part m_0 and the
slot's part m_j. The batch is then determined: a prover message is (m_0, m_1, .., m_N), a verifier
message is one ρ_0 or a tuple (ρ_1, .., ρ_N). With this choice everything that is defined for
`InteractiveOracleProof` (`IsLocal`, `DView`, `dview`, `Honest`, `Acc`) applies to a slot unchanged, and an ordinary
IOP is, by definition and without any cast, the batch IOP with local rounds only
(`BatchInteractiveOracleProof.ofProto`; Iop/BatchOne.lean shows that at N = 1 `ReadsAtMost`, `HVZK` and `Acc` below
are the bound on the verifier's positions, `Honest.HVZK` and `Honest.Acc`; for (Snd-B) see the
Limits of Iop/BatchOne.lean). A fact on the joint
error of shared rounds is in Iop/BatchSound.lean.

As in Iop/InteractiveOracleProof.lean the structures contain data only; the properties are separate.

Notes on the definitions. (Π: the external oracle; in Lean y : E.Str.)
(D1) Empty slots. The instance vector is Fin N → Option X. In the types every slot has messages;
     those of an empty slot are read by no one.
(D2) That the positions queried in Π are a function of the shared verifier messages is a property
     (`ExtShared`) and not a fact about a type. What layer 1 needs of it is that one execution reads
     at most q_on positions of Π, whatever N is: `ReadsAtMost` (for the given N). `ExtShared` and a
     bound for one slot give `ReadsAtMost`. `BatchProtocol.Reads` asks for `ReadsAtMost`, so that one slot
     with local rounds and positions that depend on x and ρ is a special case.
(D3) (Snd-B): there is a function State of Π and a partial local transcript. The law on verifier
     messages quantifies over the partial transcripts of the full batch; it is written as a
     recursion on the shape (`JointLaw`), in which the state functions of the slots are carried
     along. Errors are counts of values of one verifier message, as everywhere in Iop.
(D4) True by type: the honest shared part (`SStrat`) is a function of the private input, its own
     coins and the shared verifier messages; the honest part of a slot (`LStrat`) of these, x_j, the
     slot's coins and the verifier messages of τ_j; one rule serves all slots; all coins are
     independent and uniform (by the definition of `BatchHonestProver.output`); so no event in one slot
     changes a message of another. That the prover sends fixed substitutes where it cannot continue
     is not expressed (as in Iop/InteractiveOracleProof.lean).
(D5) HVZK is in the exact form of Iop/InteractiveOracleProof.lean: under the hypotheses of its statement, outside a
     set of ρ of probability at most |J| z the simulator's output has exactly the law of the output
     for J. The simulator is given J, (x_j) and (ρ_0, ρ_j) for j ∈ J (as the local randomness of
     each slot of J), and the answers of Π where the verifiers of J read.
(D6) The output for J is a function on J: for each slot of J the disclosed view of its local
     transcript, or the notice. The shared part is therefore repeated in every slot that is shown,
     and absent if none is shown.
(D7) The withheld set of slot j is a set of values of ρ_j, the local verifier messages of the slot
     (`RhoLo`); and there is a public test on the shared verifier messages ρ_0 (`BatchHonestProver.stop0`):
     where it says "stop", every slot is withheld. It is there for verifiers that reject at an event
     of the shared messages: without it (Acc) could not be true for them where a valid input has a ρ
     that is not withheld and meets the event (no theorem says this).
(D8) There is one public set: (Acc) is asked outside Bad ∪ Hid (as in Iop/InteractiveOracleProof.lean), and where
     `stop0` is false ((D7)).
(D9) The number N of slots is any natural number. At N = 0 all statements on slots are empty. 0 < N
     is asked where it is used.
(D10) The simulator's running time is not modelled (as in Iop/InteractiveOracleProof.lean).
(D11) The interface has two more data, `early` and `late`, which say how layer 1 writes an instance
     of Batch into the hash chain of its slot: early x into the first query, x itself into the query
     of the round late. At early = id, late = none the full instance is in the first query. (Snd-B)
     is asked in a form that fits these data (`SndBL`). The IOP itself, its honest prover and its
     simulators do not read them.

Notation: `I : Type`: the type of well-formed indices (`decodeIndex` returns none on a string that does not
decode or that decodes to something that is not well formed, so "Π is good", of a string Π, is
"decodeIndex Π ≠ none"); `X : Type`: in `BatchInteractiveOracleProof X E` (this file): instances in X; `encodeIndex`, `decodeIndex` (fields
of `BatchProtocol`):
the randomised indexer and the decoder; `wordLength : ℕ`, `Symbol : Type`: in `oneExternalString wordLength Symbol` (Iop/InteractiveOracleProof.lean), one
string of n symbols as external oracle; `EncodingRandomness : Type`: in `honestOnlineBatchProver :
BatchHonestProver onlineBatch (I × EncodingRandomness)`, by the docstring of `BatchHonestProver`:
(index, encoding randomness); `b qT qpar qch qon : ℕ`, `εs zT zL zO pT pL pO : ℝ≥0∞`: the fields of
`LH.Nums` (Iop/InteractiveOracleProof.lean): all numbers of the interface; `Ryes`, `Rno : I → X →
Prop`: two relations; in `BatchProtocol.Props` (this file): `sub : ∀ i x, Ryes i x → Rno i x`.

Terms: lean/GLOSSARY.md.
-/
import Iop.State
noncomputable section -- Lean tags what it cannot compile

namespace Iop
open Prob
open scoped ENNReal

/-! ## 1. Shared and local rounds -/

/-- A round is called shared (sh) or local (lo) after its verifier message. -/
inductive Kind
  | sh
  | lo
  deriving DecidableEq

namespace Kind
variable {C : Type}

/-- The verifier message of the whole batch: one uniform string ρ_0 or a tuple (ρ_1, .., ρ_N) of
independent uniform strings. -/
def All (N : ℕ) : Kind → Type → Type
  | sh, C => C
  | lo, C => Fin N → C

/-- What slot j sees of it. -/
def slot {N : ℕ} : (k : Kind) → k.All N C → Fin N → C
  | sh, c, _ => c
  | lo, c, j => c j

/-- The shared part of a verifier message of a local transcript: the message itself in a shared
round, nothing in a local one. -/
def Sh : Kind → Type → Type
  | sh, C => C
  | lo, _ => Unit

/-- Its local part. -/
def Lo : Kind → Type → Type
  | sh, _ => Unit
  | lo, C => C

def shOf : (k : Kind) → C → k.Sh C
  | sh, c => c
  | lo, _ => ()

def loOf : (k : Kind) → C → k.Lo C
  | sh, _ => ()
  | lo, c => c

instance instFintypeAll (N : ℕ) : ∀ (k : Kind) (C : Type) [Fintype C], Fintype (k.All N C)
  | sh, _, i => i
  | lo, C, _ => inferInstanceAs (Fintype (Fin N → C))

instance instNonemptyAll (N : ℕ) : ∀ (k : Kind) (C : Type) [Nonempty C], Nonempty (k.All N C)
  | sh, _, i => i
  | lo, C, _ => inferInstanceAs (Nonempty (Fin N → C))

end Kind

/-- The annotation of one round r of the local shape: its kind, and the splitting of a prover
message of the local transcript into (m_0, m_j). Each part consists of oracles and a plain string:
`own` says to which part an oracle position belongs, and `P0`, `Pj` are the plain strings of the
parts. (Layer 1 hashes the two parts apart: a root and a plain string for m_0, a root and a plain
string for m_j.) -/
structure RAnn (r : Round) where
  kind  : Kind
  /-- the shared part m_0 of a prover message -/
  M0    : Type
  /-- the part m_j of one slot; in Batch all slots have messages of the same shape in each
  round -/
  Mj    : Type
  split : r.Msg ≃ M0 × Mj
  /-- the plain strings of m_0 and of m_j -/
  P0    : Type
  Pj    : Type
  pl0   : M0 → P0
  plj   : Mj → Pj
  plain : r.Plain ≃ P0 × Pj
  /-- does this oracle position lie in m_j (true) or in m_0 (false) -/
  own   : r.Pos → Bool

/-- The prover message of a local transcript. -/
def RAnn.join {r : Round} (a : RAnn r) (m0 : a.M0) (mj : a.Mj) : r.Msg := a.split.symm (m0, mj)

/-- The data of an annotation fit together: the plain string of (m_0, m_j) is the pair of the two
plain strings; an oracle position of m_0 is answered from m_0 alone, one of m_j from m_j alone. -/
structure RAnn.Coherent {r : Round} (a : RAnn r) : Prop where
  plain_join : ∀ m0 mj, a.plain (a.join m0 mj).2 = (a.pl0 m0, a.plj mj)
  rd_shared  : ∀ m0 mj mj' p, a.own p = false → r.rd (a.join m0 mj).1 p = r.rd (a.join m0 mj').1 p
  rd_own     : ∀ m0 m0' mj p, a.own p = true → r.rd (a.join m0 mj).1 p = r.rd (a.join m0' mj).1 p

/-- The annotation of a shape. -/
def RoundSplits : Shape → Type 1
  | [] => PUnit
  | r :: s => RAnn r × RoundSplits s

/-- A round in which only the slots send: there is no shared prover message. -/
def RAnn.ofSlot (k : Kind) (r : Round) : RAnn r where
  kind := k
  M0 := Unit
  Mj := r.Msg
  split := (Equiv.punitProd r.Msg).symm
  P0 := Unit
  Pj := r.Plain
  pl0 := fun _ => ()
  plj := fun m => m.2
  plain := (Equiv.punitProd r.Plain).symm
  own := fun _ => true

/-- A round in which only the shared part is sent: the slots send nothing. -/
def RAnn.ofShared (k : Kind) (r : Round) : RAnn r where
  kind := k
  M0 := r.Msg
  Mj := Unit
  split := (Equiv.prodPUnit r.Msg).symm
  P0 := r.Plain
  Pj := Unit
  pl0 := fun m => m.2
  plj := fun _ => ()
  plain := (Equiv.prodPUnit r.Plain).symm
  own := fun _ => false

theorem RAnn.ofSlot_coherent (k : Kind) (r : Round) : (RAnn.ofSlot k r).Coherent :=
  ⟨fun _ _ => rfl, fun _ _ _ _ h => Bool.noConfusion h, fun _ _ _ _ _ => rfl⟩

theorem RAnn.ofShared_coherent (k : Kind) (r : Round) : (RAnn.ofShared k r).Coherent :=
  ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ h => Bool.noConfusion h⟩

/-- A local round without a shared prover message. -/
def RAnn.allLocal (r : Round) : RAnn r := RAnn.ofSlot .lo r

/-- The same rule of annotation in every round. -/
def RoundSplits.const (f : ∀ r : Round, RAnn r) : (s : Shape) → RoundSplits s
  | [] => PUnit.unit
  | r :: s => (f r, RoundSplits.const f s)

/-- Local rounds only, and no shared prover message: an ordinary IOP. -/
def RoundSplits.allLocal (s : Shape) : RoundSplits s := RoundSplits.const RAnn.allLocal s

/-- The annotation of two shapes one after the other. -/
def RoundSplits.app : {s t : Shape} → RoundSplits s → RoundSplits t → RoundSplits (s ++ t)
  | [], _, _, B => B
  | _ :: _, _, (a, A), B => (a, RoundSplits.app A B)


/-- All annotations of the shape are coherent. -/
def RoundSplits.Coherent : {s : Shape} → RoundSplits s → Prop
  | [], _ => True
  | _ :: _, (a, A) => a.Coherent ∧ RoundSplits.Coherent A

/-- Full transcripts of the whole batch. -/
def BTr (N : ℕ) : (s : Shape) → RoundSplits s → Type
  | [], _ => Unit
  | r :: s, (a, A) => (a.M0 × (Fin N → a.Mj)) × a.kind.All N r.Chal × BTr N s A

/-- The verifier's randomness of a whole execution of the batch: ρ = (ρ_0, ρ_1, .., ρ_N). -/
def BRho (N : ℕ) : (s : Shape) → RoundSplits s → Type
  | [], _ => Unit
  | r :: s, (a, A) => a.kind.All N r.Chal × BRho N s A

/-- The shared verifier messages ρ_0. -/
def RhoSh : (s : Shape) → RoundSplits s → Type
  | [], _ => Unit
  | r :: s, (a, A) => a.kind.Sh r.Chal × RhoSh s A

/-- The local verifier messages ρ_j of one slot. -/
def RhoLo : (s : Shape) → RoundSplits s → Type
  | [], _ => Unit
  | r :: s, (a, A) => a.kind.Lo r.Chal × RhoLo s A

instance instFintypeBRho (N : ℕ) : ∀ (s : Shape) (A : RoundSplits s), Fintype (BRho N s A)
  | [], _ => inferInstanceAs (Fintype Unit)
  | r :: s, (a, A) => by
      haveI := instFintypeBRho N s A
      exact inferInstanceAs (Fintype (a.kind.All N r.Chal × BRho N s A))

instance instNonemptyBRho (N : ℕ) : ∀ (s : Shape) (A : RoundSplits s), Nonempty (BRho N s A)
  | [], _ => inferInstanceAs (Nonempty Unit)
  | r :: s, (a, A) => by
      haveI := instNonemptyBRho N s A
      exact inferInstanceAs (Nonempty (a.kind.All N r.Chal × BRho N s A))

/-- The local transcript τ_j, without x_j: all m_0, m_j, ρ_0, ρ_j. -/
def BTr.slot {N : ℕ} (j : Fin N) : {s : Shape} → {A : RoundSplits s} → BTr N s A → Tr s
  | [], _, _ => ()
  | _ :: _, (a, _), (m, v, τ) => (a.join m.1 (m.2 j), a.kind.slot v j, BTr.slot j τ)

/-- The verifier messages in τ_j. -/
def BRho.slot {N : ℕ} (j : Fin N) : {s : Shape} → {A : RoundSplits s} → BRho N s A → Rho s
  | [], _, _ => ()
  | _ :: _, (a, _), (v, ρ) => (a.kind.slot v j, BRho.slot j ρ)

/-- The shared verifier messages among those of a local transcript. -/
def Rho.sh : {s : Shape} → (A : RoundSplits s) → Rho s → RhoSh s A
  | [], _, _ => ()
  | _ :: _, (a, A), (c, ρ) => (a.kind.shOf c, Rho.sh A ρ)

/-- The local ones. -/
def Rho.lo : {s : Shape} → (A : RoundSplits s) → Rho s → RhoLo s A
  | [], _, _ => ()
  | _ :: _, (a, A), (c, ρ) => (a.kind.loOf c, Rho.lo A ρ)

/-! ## 2. Batch IOPs and the shape (Sh) -/

/-- A batch IOP with instances in X and the external oracle(s) E: the local verifier, and the
annotation of its shape. The number N of slots is an argument of the properties below. -/
structure BatchInteractiveOracleProof (X : Type) (E : ExtSpec) where
  loc : InteractiveOracleProof X E
  ann : RoundSplits loc.shape

variable {X : Type} {E : ExtSpec}

/-- An ordinary IOP as a batch IOP: local rounds only. -/
abbrev BatchInteractiveOracleProof.ofProto (Q : InteractiveOracleProof X E) : BatchInteractiveOracleProof X E := ⟨Q, RoundSplits.allLocal Q.shape⟩

/-- The positions queried in Π are a function of the shared verifier messages. -/
def BatchInteractiveOracleProof.ExtShared (Q : BatchInteractiveOracleProof X E) : Prop :=
  ∀ x x' ρ ρ', Rho.sh Q.ann ρ = Rho.sh Q.ann ρ' → Q.loc.extReads x ρ = Q.loc.extReads x' ρ'

open Classical in
/-- The positions of Π that the local verifiers of the non-empty slots read in one execution. -/
def BatchInteractiveOracleProof.allReads
    (Q : BatchInteractiveOracleProof X E) {N : ℕ} (x : Fin N → Option X) (ρ : BRho N Q.loc.shape Q.ann) :
    Finset E.Pos :=
  Finset.univ.biUnion fun j => match x j with
    | none => ∅
    | some xj => Q.loc.extReads xj (ρ.slot j)

/-- One execution reveals at most q_on positions of Π, whatever N is (for the given N; exactly:
∀ (x : Fin N → Option X) ρ, (Q.allReads x ρ).card ≤ q; see (D2)). -/
def BatchInteractiveOracleProof.ReadsAtMost (Q : BatchInteractiveOracleProof X E) (N q : ℕ) : Prop :=
  ∀ (x : Fin N → Option X) ρ, (Q.allReads x ρ).card ≤ q

/-- Of each round: its kind, "it has no shared prover message", "the slots send no message". -/
def RoundSplits.summary : (s : Shape) → RoundSplits s → List (Kind × Prop × Prop)
  | [], _ => []
  | _ :: s, (a, A) => (a.kind, Subsingleton a.M0, Subsingleton a.Mj) :: RoundSplits.summary s A

/-- The shape (Sh): round 1 is local; the shared rounds form one block, which is not empty and
whose first round is the joining round; a local round has no shared prover message; slots send
messages only in local rounds and in the joining round. -/
def RoundSplits.OneBlock {s : Shape} (A : RoundSplits s) : Prop :=
  ∃ a b c : List (Kind × Prop × Prop), RoundSplits.summary s A = a ++ b ++ c ∧ a ≠ [] ∧ b ≠ [] ∧
    (∀ t ∈ a ++ c, t.1 = .lo ∧ t.2.1) ∧ (∀ t ∈ b, t.1 = .sh) ∧ (∀ t ∈ b.tail, t.2.2)


/-! ## 3. (Snd-B): local state, joint error -/

/-- The law on verifier messages, for every partial transcript of the whole batch before the
verifier message of round i, with j ranging over the non-empty slots. St j is the state function of
slot j on what is left of the protocol (none: the slot is empty).
* a local round:  #{ρ_j : State(τ_j ‖ ρ_j) = 1} ≤ ε_i for each j with State(τ_j) = 0;
* a shared round: #{ρ_0 : ∃ j, State(τ_j) = 0 ∧ State(τ_j ‖ ρ_0) = 1} ≤ ε_i (the joint error). -/
def JointLaw (N : ℕ) : (s : Shape) → RoundSplits s → Err s → (Fin N → Option (PTr s → Bool)) → Prop
  | [], _, _, _ => True
  | r :: s, (a, A), (e, ε), St =>
      ∀ (m0 : a.M0) (m : Fin N → a.Mj),
        (match a.kind with
          | .lo => ∀ j S, St j = some S → S (.atV (Sum.inl (a.join m0 (m j)))) = false →
              cnt (fun c : r.Chal => S (PTr.cons (a.join m0 (m j)) c (PTr.empty s)) = true) ≤ e
          | .sh => cnt (fun c : r.Chal =>
              ∃ j S, St j = some S ∧ S (.atV (Sum.inl (a.join m0 (m j)))) = false ∧
              S (PTr.cons (a.join m0 (m j)) c (PTr.empty s)) = true) ≤ e) ∧
        ∀ v : a.kind.All N r.Chal,
          JointLaw N s A ε fun j =>
            (St j).map fun S τ => S (PTr.cons (a.join m0 (m j)) (a.kind.slot v j) τ)

/-- (Snd-B) for the language L of pairs (x, Π) (in BatchProtocol.Sound: Π is not good, or x ∈ L(D(Π))). There
is a function State(Π, τ) ∈ {0,1} of the external oracle and a partial local transcript of a
non-empty slot such that: State(Π, x_j) = 1 if and only if (x_j, Π) is in L; a prover message never
changes 0 to 1; if State(Π, τ_j) = 0 for a complete τ_j, then V_j rejects; and the law on verifier
messages holds, for every Π and every instance vector. -/
def BatchInteractiveOracleProof.SndB (Q : BatchInteractiveOracleProof X E) (N : ℕ) (L : X → E.Str → Prop) (ε : Err Q.loc.shape) :
    Prop :=
  ∃ State : E.Str → X → PTr Q.loc.shape → Bool,
    (∀ y x, State y x (PTr.empty Q.loc.shape) = true ↔ L x y) ∧
    (∀ y x (τ : AtP Q.loc.shape) (m : τ.round.Msg),
      State y x (.atP τ) = false → State y x (.atV (τ.snoc m)) = false) ∧
    (∀ y x (τ : Tr Q.loc.shape), State y x (.full τ) = false → Q.loc.accept x y τ = false) ∧
    (∀ y (x : Fin N → Option X), JointLaw N Q.loc.shape Q.ann ε fun j => (x j).map (State y))

/-! ## 3a. (Snd-B) for an instance that enters the hash chain in two parts -/

/-- The rounds 0, .., n exist and are local. -/
def RoundSplits.LocalTo : ℕ → (s : Shape) → RoundSplits s → Prop
  | _, [], _ => False
  | 0, _ :: _, (a, _) => a.kind = .lo
  | n + 1, _ :: s, (a, A) => a.kind = .lo ∧ RoundSplits.LocalTo n s A

/-- (Snd-B), late form. Layer 1 may write only a part "early x" of the instance x into the first
query of a chain, and x itself into the query of a later round, number "late" (counted from 0; none:
no later query holds x). A cheating prover then fixes the rest of x only after it has seen the
verifier messages of the rounds before "late". What layer 1 needs against that is (Snd-B) with a
state function that, in those rounds, is given early x in the place of x:
* the round "late" is not the first, and it and all rounds before it are local;
* a false statement starts in state 0 of its early part;
* a prover message never changes 0 to 1, for any fixed instance;
* the switch: if the state of early x is 0 before the prover message of the round "late", then so is
  the state of x, for a false x;
* at the end, state 0 (of x, or of early x if no later query holds x) means that V_j rejects x, for
  a false x;
* the law on verifier messages holds for every vector of instances, with the same errors.
Some clauses are asked for false statements only, other than in SndB; at early = id, late = none the
two are equivalent (Iop/Late.lean: `sndBL_iff_sndB`). That SndBL implies SndB for all early and
late, with the same errors, is shown neither in this file nor in Iop/Late.lean. That with the same
errors SndB does not imply SndBL (the prover that names the rest of x after it has seen a verifier
message) is not proved in this library.
Not asked: anything of the honest prover, or that the verifier's tests in the early rounds do not
read the rest of x. -/
def BatchInteractiveOracleProof.SndBL (Q : BatchInteractiveOracleProof X E) (N : ℕ) (early : X → X) (late : Option ℕ)
    (L : X → E.Str → Prop) (ε : Err Q.loc.shape) : Prop :=
  (∀ n, late = some n → 0 < n ∧ RoundSplits.LocalTo n Q.loc.shape Q.ann) ∧
  ∃ State : E.Str → X → PTr Q.loc.shape → Bool,
    (∀ y x, ¬ L x y → State y (early x) (PTr.empty Q.loc.shape) = false) ∧
    (∀ y x (τ : AtP Q.loc.shape) (m : τ.round.Msg),
      State y x (.atP τ) = false → State y x (.atV (τ.snoc m)) = false) ∧
    (∀ y x (τ : AtP Q.loc.shape), ¬ L x y → late = some τ.idx →
      State y (early x) (.atP τ) = false → State y x (.atP τ) = false) ∧
    (∀ y x (τ : Tr Q.loc.shape), ¬ L x y →
      State y (if late.isSome then x else early x) (.full τ) = false → Q.loc.accept x y τ = false) ∧
    (∀ y (x : Fin N → Option X), JointLaw N Q.loc.shape Q.ann ε fun j => (x j).map (State y))

/-! ## 4. The honest side: slots do not interfere -/

/-- Strategies for the shared part: m_0 in every round; of the verifier messages only the shared
ones are seen. -/
def SStrat : (s : Shape) → RoundSplits s → Type
  | [], _ => Unit
  | r :: s, (a, A) => a.M0 × (a.kind.Sh r.Chal → SStrat s A)

/-- Strategies for the part of one slot: m_j in every round; the verifier messages of τ_j are
seen. -/
def LStrat : (s : Shape) → RoundSplits s → Type
  | [], _ => Unit
  | r :: s, (a, A) => a.Mj × (r.Chal → LStrat s A)

/-- The two together are a strategy on local transcripts. -/
def SStrat.zip : {s : Shape} → {A : RoundSplits s} → SStrat s A → LStrat s A → Strat s Unit
  | [], _, _, _ => ()
  | _ :: _, (a, _), (m0, k0), (mj, kj) =>
    (a.join m0 mj, fun c => SStrat.zip (k0 (a.kind.shOf c)) (kj c))

/-- The honest side of a batch IOP. Wt is the prover's private input for the shared external oracle
(index, encoding randomness). -/
structure BatchHonestProver (Q : BatchInteractiveOracleProof X E) (Wt : Type) where
  /-- the randomness of the shared part -/
  Coin0 : Type
  /-- the randomness of one slot -/
  Coin  : Type
  [finCoin0 : Fintype Coin0]
  [neCoin0  : Nonempty Coin0]
  [finCoin  : Fintype Coin]
  [neCoin   : Nonempty Coin]
  ext    : Wt → E.Str
  /-- m_0 from its inputs for the shared external oracles, the shared verifier messages and
  randomness of its own -/
  strat0 : Wt → Coin0 → SStrat Q.loc.shape Q.ann
  /-- m_j from these, x_j, the verifier messages of τ_j and the randomness of slot j; where it
  cannot continue it is meant to send fixed substitutes -/
  strat  : Wt → Coin0 → X → Coin → LStrat Q.loc.shape Q.ann
  /-- the public bad set, a set of values of ρ_j -/
  Bad    : Set (RhoLo Q.loc.shape Q.ann)
  /-- the rest of the withheld set of a slot: Win(i, x_j), a set of values of ρ_j (as `Honest.Hid`,
  Iop/InteractiveOracleProof.lean) -/
  Hid    : Wt → X → Set (RhoLo Q.loc.shape Q.ann)
  /-- the public stop of the shared rounds: a test on the shared verifier messages ρ_0; where it
  says true, every slot is withheld. (No default value: an honest side that forgot the field would
  silently have no such stop.) -/
  stop0  : RhoSh Q.loc.shape Q.ann → Bool

attribute [instance] BatchHonestProver.finCoin0 BatchHonestProver.neCoin0 BatchHonestProver.finCoin BatchHonestProver.neCoin

variable {Q : BatchInteractiveOracleProof X E} {Wt : Type}

/-- One slot of the honest side, as the honest side of the local verifier's IOP. -/
def BatchHonestProver.one (H : BatchHonestProver Q Wt) : Honest Q.loc Wt where
  Coin := H.Coin0 × H.Coin
  ext := H.ext
  strat := fun w x c => (H.strat0 w c.1).zip (H.strat w c.1 x c.2)
  Bad := {ρ | Rho.lo Q.ann ρ ∈ H.Bad ∨ H.stop0 (Rho.sh Q.ann ρ) = true}
  Hid := fun w x => {ρ | Rho.lo Q.ann ρ ∈ H.Hid w x}

/-! ## 5. Outputs and HVZK for sets of slots, (Acc) -/

open Classical in
/-- The output for J at ρ: the disclosed view at ρ of the slots of J that are not withheld, with
one fixed notice for each other slot of J. A random variable over the coins of the shared part and
of all slots. (J is meant to hold non-empty slots; an empty slot gives the notice.) -/
def BatchHonestProver.output (H : BatchHonestProver Q Wt) {N : ℕ} (w : Wt) (x : Fin N → Option X)
    (ρ : BRho N Q.loc.shape Q.ann) (J : Finset (Fin N)) :
    PMF (J → Option (DView Q.loc)) :=
  (unif (H.Coin0 × (Fin N → H.Coin))).map fun c => fun j =>
    match x j with
    | none => none
    | some xj =>
      if ρ.slot j.1 ∈ H.one.withheld w xj then none
      else some (Q.loc.dview xj (H.ext w) ((H.one.strat w xj (c.1, c.2 j)).run (ρ.slot j.1)).1)

open Classical in
/-- The answers of Π only where the verifiers of J do read it at ρ. -/
def BatchInteractiveOracleProof.extAnsJ (Q : BatchInteractiveOracleProof X E) {N : ℕ} (J : Finset (Fin N)) (xs : J → X)
    (ρs : J → Rho Q.loc.shape) (y : E.Str) : E.Pos → Option E.Sym :=
  fun p => if ∃ j, p ∈ Q.loc.extReads (xs j) (ρs j) then some (E.rd y p) else none

/-- The probability of a set of values of ρ = (ρ_0, ρ_1, .., ρ_N), the slots outside J
included. -/
def prBRho {N : ℕ} {s : Shape} {A : RoundSplits s} (S : Set (BRho N s A)) : ℝ≥0∞ :=
  pr (unif (BRho N s A)) S

/-- HVZK for sets of slots, in the exact form (as in Iop/InteractiveOracleProof.lean). One simulator for all inputs
of the honest prover and all J. It is given J, (x_j) for j ∈ J, the verifier messages of τ_j for j ∈
J, that is ρ_0 and (ρ_j), and the answers of Π where the verifiers of J read. It is given neither
the other instances nor which other slots are non-empty. For every valid input
(`∀ j xj, x j = some xj → valid w xj`) and every set J of non-empty slots its output has exactly the
law of the output for J, at every ρ outside a set of probability at most |J| z. -/
def BatchHonestProver.HVZK (H : BatchHonestProver Q Wt) (N : ℕ) (valid : Wt → X → Prop) (z : ℝ≥0∞) : Prop :=
  ∃ Sim : (J : Finset (Fin N)) → (J → X) → (J → Rho Q.loc.shape) →
      (E.Pos → Option E.Sym) → PMF (J → Option (DView Q.loc)),
    ∀ (w : Wt) (x : Fin N → Option X), (∀ j xj, x j = some xj → valid w xj) →
      ∀ (J : Finset (Fin N)) (xs : J → X), (∀ j : J, x j = some (xs j)) →
        prBRho {ρ | H.output w x ρ J ≠
              Sim J xs (fun j => ρ.slot j.1) (Q.extAnsJ J xs (fun j => ρ.slot j.1) (H.ext w))} ≤
          J.card * z

/-- How HVZK for sets of slots is proved: exactness outside a set S of ρ, and a bound on S. -/
theorem BatchHonestProver.HVZK.of_exact (H : BatchHonestProver Q Wt) (N : ℕ) (valid : Wt → X → Prop) (z : ℝ≥0∞)
    (Sim : (J : Finset (Fin N)) → (J → X) → (J → Rho Q.loc.shape) →
      (E.Pos → Option E.Sym) → PMF (J → Option (DView Q.loc)))
    (S : Wt → (Fin N → Option X) → Finset (Fin N) → Set (BRho N Q.loc.shape Q.ann))
    (hex : ∀ (w : Wt) (x : Fin N → Option X), (∀ j xj, x j = some xj → valid w xj) →
      ∀ (J : Finset (Fin N)) (xs : J → X), (∀ j : J, x j = some (xs j)) →
        ∀ ρ, ρ ∉ S w x J →
          H.output w x ρ J =
            Sim J xs (fun j => ρ.slot j.1) (Q.extAnsJ J xs (fun j => ρ.slot j.1) (H.ext w)))
    (hS : ∀ (w : Wt) (x : Fin N → Option X), (∀ j xj, x j = some xj → valid w xj) →
      ∀ J : Finset (Fin N), (∀ j ∈ J, x j ≠ none) → prBRho (S w x J) ≤ J.card * z) :
    H.HVZK N valid z :=
  ⟨Sim, fun w x hv J xs hxs => le_trans (pr_mono _ fun ρ hρ => by
    by_contra hn
    exact hρ (hex w x hv J xs hxs ρ hn)) (hS w x hv J fun j hj h => by
      have := hxs ⟨j, hj⟩
      rw [h] at this
      cases this)⟩

/-- (Acc) for each slot: V_j accepts the honest prover on every valid input at every ρ = (ρ_0, ρ_j)
outside the withheld set of the slot (a condition on ρ_j and, through stop0, on ρ_0: (D7)), for all
coins. By (D4) this is a statement on one slot. -/
def BatchHonestProver.Acc (H : BatchHonestProver Q Wt) (valid : Wt → X → Prop) : Prop := H.one.Acc valid

/-! ## 6. The interface with batches -/

/-- The five algorithms (I, D, Test, Link, Batch: `encodeIndex`, `decodeIndex`, `offline`, `link`, `onlineBatch`), with the
honest sides of the three protocols (`honestOfflineProver`, `honestLinkProver`, `honestOnlineBatchProver`). -/
structure BatchProtocol (I X : Type) where
  wordLength    : ℕ
  Symbol   : Type
  EncodingRandomness   : Type
  [encodingRandomnessIsFinite : Fintype EncodingRandomness]
  [encodingRandomnessIsNonempty  : Nonempty EncodingRandomness]
  encodeIndex  : I → EncodingRandomness → (Fin wordLength → Symbol)
  decodeIndex  : (Fin wordLength → Symbol) → Option I
  offline : InteractiveOracleProof Unit (oneExternalString wordLength Symbol)
  link : InteractiveOracleProof Unit (twoExternalStrings wordLength Symbol)
  /-- the number of slots -/
  maxBatchSize    : ℕ
  onlineBatch  : BatchInteractiveOracleProof X (oneExternalString wordLength Symbol)
  honestOfflineProver   : Honest offline (I × EncodingRandomness)
  honestLinkProver   : Honest link (I × EncodingRandomness × EncodingRandomness)
  honestOnlineBatchProver   : BatchHonestProver onlineBatch (I × EncodingRandomness)
  /-- what of an instance layer 1 writes into the first query of the chain of a slot of Batch. The
  identity: the whole instance. (No default value: an interface that forgot the field would silently
  have the identity.) -/
  early : X → X
  /-- the round of Batch (counted from 0) into whose query layer 1 writes the whole instance; none:
  there is no such round -/
  late  : Option ℕ

attribute [instance] BatchProtocol.encodingRandomnessIsFinite BatchProtocol.encodingRandomnessIsNonempty

variable {I : Type}

/-- `decodeIndex` inverts `encodeIndex`, and the honest sides' external strings (`ext`) are
encodings of their index: one for Test and for Batch, two for Link. -/
structure BatchProtocol.Wired (L : BatchProtocol I X) : Prop where
  dec_enc : ∀ i r, L.decodeIndex (L.encodeIndex i r) = some i
  extT : ∀ i r, L.honestOfflineProver.ext (i, r) = L.encodeIndex i r
  extL : ∀ i r r', L.honestLinkProver.ext (i, r, r') = (L.encodeIndex i r, L.encodeIndex i r')
  extB : ∀ i r, L.honestOnlineBatchProver.ext (i, r) = L.encodeIndex i r

/-- (Snd-T), (Snd-L), (Snd-B); εs bounds every round-by-round error, as a probability, the joint
errors of the shared rounds included. (Snd-B) is in its late form, for the fields `early` and `late`
of the interface; at early = id, late = none it is (Snd-B) itself (Iop/Late.lean: `sndBL_iff_sndB`).
-/
structure BatchProtocol.Sound (L : BatchProtocol I X) (Rno : I → X → Prop) (εs : ℝ≥0∞) : Prop where
  sndT : ∃ ε, Err.Below ε εs ∧ L.offline.Sound (fun _ y => L.decodeIndex y ≠ none) ε
  sndL : ∃ ε, Err.Below ε εs ∧ L.link.Sound (fun _ y => L.decodeIndex y.1 = none ∨ L.decodeIndex y.2 = L.decodeIndex y.1) ε
  sndB : ∃ ε,
    Err.Below ε εs ∧
    L.onlineBatch.SndBL L.maxBatchSize L.early L.late (fun x y => L.decodeIndex y = none ∨ ∃ i, L.decodeIndex y = some i ∧ Rno i x) ε

/-- Bounds on the numbers of positions that the protocols read in encodings, and the number that an
encoding hides. -/
structure BatchProtocol.Reads (L : BatchProtocol I X) (b qT qpar qch qon : ℕ) : Prop where
  cntT  : ∀ x ρ, (L.offline.extReads x ρ).card ≤ qT
  cntLp : ∀ x ρ, ((L.link.extReads x ρ).filter (fun p => p.isLeft)).card ≤ qpar
  cntLc : ∀ x ρ, ((L.link.extReads x ρ).filter (fun p => p.isRight)).card ≤ qch
  /-- one execution of the batch, with all its slots, reads at most q_on positions -/
  cntB  : L.onlineBatch.ReadsAtMost L.maxBatchSize qon
  /-- (Hid-E): the law of an encoding at any b positions does not depend on the index (exactly:
    `S.card ≤ b`) -/
  hidE  : ∀ (S : Finset (Fin L.wordLength)), S.card ≤ b →
    ∀ i i', (unif L.EncodingRandomness).map (fun r => fun p : S => L.encodeIndex i r p) =
      (unif L.EncodingRandomness).map (fun r => fun p : S => L.encodeIndex i' r p)

/-- (Hid-TL), (Hid-B): a coalition J costs |J| zO. -/
structure BatchProtocol.Hiding (L : BatchProtocol I X) (Ryes : I → X → Prop) (zT zL zO : ℝ≥0∞) : Prop where
  hidT : L.honestOfflineProver.HVZK (fun _ _ => True) zT
  hidL : L.honestLinkProver.HVZK (fun _ _ => True) zL
  hidB : L.honestOnlineBatchProver.HVZK L.maxBatchSize (fun w x => Ryes w.1 x) zO

/-- (Acc), and the probabilities of the withheld sets (for a slot: of its (ρ_0, ρ_j): (D7)). -/
structure BatchProtocol.Complete (L : BatchProtocol I X) (Ryes : I → X → Prop) (pT pL pO : ℝ≥0∞) : Prop where
  accT : L.honestOfflineProver.Acc (fun _ _ => True)
  accL : L.honestLinkProver.Acc (fun _ _ => True)
  accB : L.honestOnlineBatchProver.Acc (fun w x => Ryes w.1 x)
  prT  : ∀ w x, prRho (L.honestOfflineProver.withheld w x) ≤ pT
  prL  : ∀ w x, prRho (L.honestLinkProver.withheld w x) ≤ pL
  prB  : ∀ w x, Ryes w.1 x → prRho (L.honestOnlineBatchProver.one.withheld w x) ≤ pO

/-- All properties together. The numbers are the fields of `LH.Nums` (Iop/InteractiveOracleProof.lean). The shape
(Sh) and ExtShared are not among them: they are asked where they are used (`ExtShared`:
Iop/BatchOne.lean: `readsAtMost_of_extShared`; no file of Compile/ mentions `OneBlock`). The form of
the work that this protocol builds on, with one relation, is Ryes = Rno. -/
structure BatchProtocol.Props (L : BatchProtocol I X) (Ryes Rno : I → X → Prop) (M : LH.Nums) : Prop where
  sub      : ∀ i x, Ryes i x → Rno i x
  wired    : L.Wired
  sound    : L.Sound Rno M.εs
  reads    : L.Reads M.b M.qT M.qpar M.qch M.qon
  hidden   : L.Hiding Ryes M.zT M.zL M.zO
  complete : L.Complete Ryes M.pT M.pL M.pO
  localT   : L.offline.IsLocal
  localL   : L.link.IsLocal
  localB   : L.onlineBatch.loc.IsLocal
  cohB     : L.onlineBatch.ann.Coherent
  pointT   : Nonempty L.offline.shape.IsPoint
  pointL   : Nonempty L.link.shape.IsPoint
  pointB   : Nonempty L.onlineBatch.loc.shape.IsPoint

end Iop
