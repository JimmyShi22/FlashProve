-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Final/ZeroKnowledgeBeforeHashing.lean: honest-verifier zero knowledge of an interactive oracle proof with three
provers, before any hash function. Definitions, for any protocol of the type: nothing is proved here and no protocol is named.

 1. THE OBJECT. An index (the weights) is encoded into tables, each at fresh randomness. Three provers speak of tables. Offline: the
    proof in the key file, on the committed table. Link: from a further table to the first. Online: the proof for one request.
    The provers keep no state from run to run.
 2. THE CLAIM (WholeView). The simulators are fixed first, then any index i₀. For every index i in range, what an unbounded observer
    sees of the honest provers on i is within a stated distance of what it sees of the simulators on tables of i₀.
 3. THE OBSERVER asks in any order, within a budget, for tables (it names each out-of-domain seed and gets the sample), runs and
    single columns. A run shows the verifier's messages, the prover's plain messages, and tables and oracles where the verifier
    reads (an oracle that is not blinded, whole). One request a session.
 4. HONEST VERIFIER. The verifier's messages are uniform among those whose proof-of-work bits are 0; with no proof of work this is
    the usual definition. It reads tables and oracles only where its rule says.
 5. THE SIMULATORS ARE GIVEN each request with its claimed output, one bit (is it served?), the copy's number, all of a run's
    verifier messages at once, and of i₀'s tables the samples and the symbols read. By type they never get i, a table's randomness
    or a prover's coins. So what is hidden is the index beyond these bits: two indices look alike to an observer each of whose
    requests is served at both or at neither.
 6. REFUSED REQUESTS. The honest side runs the online prover at every request and is not told the bit. Where a request is not served
    the prover must show nothing (refuses). «Served» depends on the weights, which the prover holds: the bit is not hidden, and it
    tells whatever makes the prover refuse, which can be more than the model's output. In Lean the observer writes the bit on its
    request and must write it truly: the same as handing the simulator the true bit, since the observer is chosen after the index.
 7. THE ROAD (RunByRun), which the compiler spends. At each fixed index, table and seed, at every message outside the prover's
    private stops, its output and the simulator's have one law over the run's own coins. So these coins must mask everything: none
    may come from the table's randomness. Where the verifier rejects an honest run, the failing run is shown, and the simulator owes
    its law too; it opens its columns like any run, and counts as a run in the tables' budget. With two public facts (how many columns each verifier reads; a table's sample with a stated number of its columns
    has a law free of the index) this gives line 2.
 8. THE ERROR is one number a run: a bound, at every index in range, table randomness and seed, on the measure of the messages at
    which the prover stops for a PRIVATE reason. By type a private stop may read index, table randomness, seed and instance, never a
    coin: a failure over the prover's coins has no seat as a stop; and a stop that reads the instance is charged as private, though
    the instance is public. At a public stop, which reads the messages alone, both sides show nothing: it costs nothing here and is
    counted in completeness. A stop withholds the whole run, earlier rounds too, as after hashing. So the claim is statistical
    wherever a private stop has measure above 0, and it says nothing of laws conditioned on no stop.
 9. NOT CLAIMED: batches (two proofs of one batch share rounds; here each run has coins of its own) · a second commitment to the
    same index · coins derived from a short key · a verifier that deviates · the simulators' running time · hashes, trees, the
    commitment (CompilerTheorems.lean) · any program.
10. READ IT BESIDE COMPLETENESS, AND AT ITS NUMBERS. Provers that send fixed messages and refuse what is not served, or that stop
    publicly at every message, meet it at error 0: so it says something of provers that are also complete, at the same served
    requests and work bits. At stops ≥ 1, or at a budget in which no run fits, the whole statement is idle; and the exactness of
    line 7 is worth what the private stops leave: a prover whose private stop tells a bit of the index at half of the messages
    meets the statement at stops 1/2. Our protocol is plugged in at ZeroKnowledgeAtTheProtocol.lean.
-/
import Johnson.Face.Protocol
import Hiop.CompleteCore
import Hiop.Seeded.AtIndex
import Hiop.Seeded.GameMembers

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Compilation
open Iop Prob Hiop.Seeded
open Hiop (BoundsR)

/-! ## 1 One protocol -/

section OneProtocol
variable {Y : Type} {E : ExtSpec} {Q : InteractiveOracleProof Y E} {Wt : Type}

/-- **Exact outside the private stops.** clear sets a message's bits of proof of work to 0. At every valid private input and
instance, at every such message outside the part of the abort set that may read the private input, the honest output is the
simulator's output, given the instance, the message and the external strings' symbols at the positions that the verifier reads. -/
def ExactOutsideStops (H : Honest Q Wt) (valid : Wt → Y → Prop) (clear : Rho Q.shape → Rho Q.shape)
    (sim : Y → (ρ : Rho Q.shape) → (E.Pos → Option E.Sym) → PMF (Option (DView Q))) : Prop :=
  ∀ w y, valid w y → ∀ ρ, clear ρ ∉ H.Hid w y →
    H.output w y (clear ρ) = sim y (clear ρ) (Q.extAns y (clear ρ) (H.ext w))

/-- **The private stops have measure at most h**, at every valid private input and instance, over uniform messages with the bits of
proof of work set to 0. The public stops are not counted: there both sides show nothing. -/
def PrivateStopsAtMost (H : Honest Q Wt) (valid : Wt → Y → Prop) (work : WorkBits Q.shape) (h : ℝ≥0∞) : Prop :=
  ∀ w y, valid w y → chanceAtPassing work (fun ρ => ρ ∈ H.Hid w y) ≤ h

end OneProtocol

/-! ## 2 The three protocols, run by run -/

section Object
variable {I X : Type} {L : HolographicProtocol I X}

/-- **The numbers of the statement.** Columns of one table that may be shown in all; columns read by one run of the offline
verifier, of the link's on the first table and on the copy, and of the online verifier; bounds on the measure of the PRIVATE stops.
The public stops cost nothing here and are completeness's to count. The three count as numbers: at stops ≥ 1, or at a budget in which no run
fits, the whole statement is idle; and the exactness of the run-by-run line is worth what the private stops leave. -/
structure Budget where
  columns : ℕ
  offlineReads : ℕ
  linkReadsFirst : ℕ
  linkReadsCopy : ℕ
  onlineReads : ℕ
  offlineStops : ℝ≥0∞
  linkStops : ℝ≥0∞
  onlineStops : ℝ≥0∞

/-- **Run by run.** inRange: the indices spoken of. Served: the requests that are served at an index, a letter here. Completeness at the same letter says that the
provers do serve them; the field refuses says that they show nothing at the others. All out-of-domain seeds are spoken of. -/
structure RunByRun (work : PartsWork L) (provers : HonestProvers L) (simulators : RunSimulators L)
    (inRange : I → Prop) (Served : I → X → Prop) (N : Budget) : Prop where
  tables : provers.SpeakOfTheirTables
  offline : ExactOutsideStops provers.offlineProver (fun w y => inRange w.1 ∧ L.validT w y)
    work.offline.cleared simulators.offline
  link : ExactOutsideStops provers.linkProver (fun w y => inRange w.1 ∧ L.validL w y) work.link.cleared
    simulators.link
  /-- at each copy's number -/
  online : ∀ n, ExactOutsideStops (provers.onlineAtCopy n)
    (fun w y => inRange w.1 ∧ L.validB Served w y) work.online.cleared (simulators.online n)
  offlineStops : PrivateStopsAtMost provers.offlineProver (fun w y => inRange w.1 ∧ L.validT w y) work.offline
    N.offlineStops
  linkStops : PrivateStopsAtMost provers.linkProver (fun w y => inRange w.1 ∧ L.validL w y) work.link N.linkStops
  onlineStops : ∀ n, PrivateStopsAtMost (provers.onlineAtCopy n)
    (fun w y => inRange w.1 ∧ L.validB Served w y) work.online N.onlineStops
  /-- at a request that is not served the online prover withholds at EVERY message: it shows nothing -/
  refuses : ∀ n w y, inRange w.1 → y.2 = L.recOf w.1 w.2.1 w.2.2 → ¬ Served w.1 y.1 →
    (provers.onlineAtCopy n).withheld w y = Set.univ

/-! ## 3 The whole view from a fixed index -/

/-- The provers for each table of the experiment. copyOf e is the copy's number with which a session on table e runs. -/
def proversByTable (provers : HonestProvers L) (copyOf : ℕ → ℕ) : RecsG L :=
  ⟨fun _ => provers.offlineProver, fun _ => provers.linkProver, fun e => provers.onlineAtCopy (copyOf e)⟩

/-- The simulators for each table of the experiment. -/
def simulatorsByTable (simulators : RunSimulators L) (copyOf : ℕ → ℕ) : SimsG L :=
  ⟨fun _ => simulators.offline, fun _ => simulators.link, fun e => simulators.online (copyOf e)⟩

/-- **What the runs of the experiment are asked with and what they show.** A run shows its messages and the honest output. A
session is asked with a request and ONE BIT, served or not. The bit is for the simulator: the honest side does not read it. The
observer may ask for every request, and it tells the bit truly: okB. -/
abbrev everyRequest (L : HolographicProtocol I X) : Form X where
  RT := Rho L.offline.shape × Option (DView L.offline)
  RL := Rho L.link.shape × Option (DView L.link)
  QB := X × Bool
  HB := fun _ => Unit
  RB := fun _ => Rho L.onlineBatch.loc.shape × Option (DView L.onlineBatch.loc)
  wt := fun _ => 1
  okB := fun served q _ => served q.1 ↔ q.2 = true

/-- **The honest side on the index i**: messages read through cleared, fresh coins. THE ONLINE PROVER IS RUN AT EVERY REQUEST, served or not. -/
def realSide (L : HolographicProtocol I X) (work : PartsWork L) (P : RecsG L) (i : I) : LawsF L (everyRequest L) where
  rc := fun u => L.recOf i u.1 u.2
  T := fun e u => runAt (P.T e) ((unif (Rho L.offline.shape)).map work.offline.cleared) some (i, u.1, u.2)
    (L.recOf i u.1 u.2)
  Lk := fun e u u' => runAt (P.Lk e) ((unif (Rho L.link.shape)).map work.link.cleared) some (i, u, u')
    (L.recOf i u.1 u.2, L.recOf i u'.1 u'.2)
  B := fun e u q _ =>
    runAt (P.B e) ((unif (Rho L.onlineBatch.loc.shape)).map work.online.cleared) some (i, u.1, u.2) (q.1, L.recOf i u.1 u.2)
  y := fun u p => L.encodeIndex i u.1 p

/-- **The simulated runs.** At the bit «served»: the run's simulator. At «not served»: the messages and nothing else; no column is read. -/
def simulatedRuns (L : HolographicProtocol I X) (work : PartsWork L) (Sm : SimsG L) : SimsF L (everyRequest L) where
  T := fun e x => simAt L.offline (Sm.T e) ((unif (Rho L.offline.shape)).map work.offline.cleared) some x
  Lk := fun e x => simAt L.link (Sm.Lk e) ((unif (Rho L.link.shape)).map work.link.cleared) some x
  B := fun e q rc =>
    simAt L.onlineBatch.loc (Sm.B e) ((unif (Rho L.onlineBatch.loc.shape)).map work.online.cleared)
      (fun ρ => if q.2 = true then some ρ else none) (q.1, rc)

/-- **The whole view from a fixed index.** simulators is fixed before the index. For every way of numbering copies, every budget
that fits, every index i in range and EVERY fixed index i₀ (in range or not): what an observer within the budget sees of the honest side on i is
within the stated distance of what it sees of the simulator that holds encodings of i₀. All out-of-domain seeds may be named. -/
def WholeView (work : PartsWork L) (provers : HonestProvers L) (simulators : RunSimulators L)
    (inRange : I → Prop) (Served : I → X → Prop) (N : Budget) : Prop :=
  ∀ (copyOf : ℕ → ℕ) (B : BoundsR),
    B.Fits N.columns N.offlineReads N.linkReadsFirst N.linkReadsCopy N.onlineReads →
    ∀ i i₀, inRange i →
      ViewNearF (realSide L work (proversByTable provers copyOf) i).host (fun _ => True) (Served i) B
        (simWholeF L (everyRequest L) (simulatedRuns L work (simulatorsByTable simulators copyOf)) i₀)
        (B.err N.offlineStops N.linkStops N.onlineStops)

/-- **Honest-verifier zero knowledge of the interactive oracle proof**, at a value of the provers with its simulators. -/
structure HonestVerifierZeroKnowledge (work : PartsWork L) (provers : HonestProvers L)
    (simulators : RunSimulators L) (inRange : I → Prop) (Served : I → X → Prop) (N : Budget) : Prop where
  /-- the range is no single index -/
  twoIndices : ∃ i i', i ≠ i' ∧ inRange i ∧ inRange i'
  /-- the work bits are the protocols' own: the verifiers ask the work, and the maps clear no more than is tested -/
  faithful : work.Faithful
  runByRun : RunByRun work provers simulators inRange Served N
  wholeView : WholeView work provers simulators inRange Served N

-- Proof road: form_laws (general in the form of runs) with tv_runAt_le at the served arm, 0 at the refused arm.
/-- The second statement follows from the first, from the counts of the columns read and from the hiding of the encoding. -/
def WholeViewFollows (work : PartsWork L) (provers : HonestProvers L) (simulators : RunSimulators L)
    (inRange : I → Prop) (Served : I → X → Prop) (N : Budget) : Prop :=
  ReadsG L (fun _ => True) N.columns N.offlineReads N.linkReadsFirst N.linkReadsCopy N.onlineReads →
    RunByRun work provers simulators inRange Served N →
      WholeView work provers simulators inRange Served N

/-! ## 4 The life of one commitment -/

-- The value of boundsW, Johnson/WholeKey/Wrap.lean:271.
/-- What one commitment lives through: copies further tables; ONE offline run, on the first table; one link to each copy;
sessionsPerCopy sessions on each copy and NONE ON THE FIRST TABLE; no single column. The compiled scheme's simulator plays against
this value. -/
def commitmentLife (copies sessionsPerCopy : ℕ) : BoundsR :=
  ⟨copies, fun e => if e = 0 then 1 else 0, fun e => if e = 0 then 0 else 1,
    fun e => if e = 0 then 0 else sessionsPerCopy, fun _ => 0, 1⟩

/-- **THE CLAIM AT THE LIFE OF ONE COMMITMENT.** error = offlineStops + copies · linkStops + copies · sessionsPerCopy · onlineStops
(err_commitmentLife). A corollary of WholeView where the two budgets hold:
offlineReads + copies · linkReadsFirst ≤ columns and linkReadsCopy + sessionsPerCopy · onlineReads ≤ columns. -/
def WholeLife (work : PartsWork L) (provers : HonestProvers L) (simulators : RunSimulators L)
    (inRange : I → Prop) (Served : I → X → Prop) (N : Budget) (copyNumber : ℕ → ℕ)
    (copies sessionsPerCopy : ℕ) : Prop :=
  ∀ i i₀, inRange i →
    ViewNearF (realSide L work (proversByTable provers fun e => copyNumber (e - 1)) i).host (fun _ => True)
      (Served i) (commitmentLife copies sessionsPerCopy)
      (simWholeF L (everyRequest L)
        (simulatedRuns L work (simulatorsByTable simulators fun e => copyNumber (e - 1))) i₀)
      ((commitmentLife copies sessionsPerCopy).err N.offlineStops N.linkStops N.onlineStops)

end Object

end VerifiableInference.Compilation

/-
WHAT THE SECOND STATEMENT UNFOLDS TO. The library's names that the whole view stands on, each with what it means.

Iop/InteractiveOracleProof.lean
  Honest             an honest prover: its coins, its tables, its strategy, and a public and a private set of messages at which it stops
  Honest.withheld    all messages at which it stops, public and private
  Honest.output      what it shows at a message, over its coins: nothing at a stop, elsewhere the view
  DView              the view: the plain parts, the tables' symbols that the verifier reads, and the oracles that are read or not blinded
  InteractiveOracleProof.extAns       the tables' symbols at the positions that the verifier reads, and nothing else
  InteractiveOracleProof.dview        the view of one transcript
Compile/Life.lean
  SimOf              a run's simulator: from an instance, a message and the symbols read, a law of views
Hiop/RecInterface.lean
  recOf              a table's out-of-domain sample: the seed with the honest answer
  validT, validL, validB   the pairs of private input and instance that the three provers are spoken of at: the samples are the honest ones;
                     the last also asks that the request is served
Hiop/RecWhole.lean
  BoundsR            a budget: further tables, and per table the offline runs, links, sessions and single columns; slots shown in a session
  BoundsR.Fits       no table is read at more columns in all than the stated number
  BoundsR.err        the error: each run asked for pays its stops
Hiop/Seeded/Form.lean
  Form               what the runs of an experiment are asked with and what they show
  EnvF               an observer: a decision tree that asks for tables, runs and columns, draws coins and stops with an output
  EnvF.Adm           it stays within a budget on every path, names the seeds allowed, and tells the truth on what it must
  HostF              who answers an observer
  HostF.view         the experiment: the observer names a seed, gets the first table's sample, then plays against the host
  LawsF              the laws of a host's answers, as functions of each table's randomness and seed
  LawsF.host         the host with these laws: it draws each table's randomness when the table is made
  RunSim             a simulated run: draw an auxiliary value, read the positions it names, say what is shown
  RunSim.law         the law of that run on given tables
  SimsF              simulated runs, for each table and sample
  simLawsF           the laws of a simulator's side: tables of one given index, that index's answers, simulated runs
  simWholeF          the simulator of the whole view: simLawsF at the fixed index
  HidE               a table's answer with a stated number of its columns has one law at every index
  ViewNearF          what any observer within the budget sees of the host is within the stated distance of what it sees of the simulator
Hiop/Seeded/Game.lean
  runAt              a run of an honest prover: draw the message, show it with the output there
  simAt              the simulated run: draw the message, read where the verifier reads, show what the simulator says
  RecsG, SimsG       honest provers and simulators for each number of a table
  ReadsG             the counts of columns that the three verifiers read, and HidE
-/

#print axioms VerifiableInference.Compilation.ExactOutsideStops
#print axioms VerifiableInference.Compilation.PrivateStopsAtMost
#print axioms VerifiableInference.Compilation.Budget
#print axioms VerifiableInference.Compilation.RunByRun
#print axioms VerifiableInference.Compilation.proversByTable
#print axioms VerifiableInference.Compilation.simulatorsByTable
#print axioms VerifiableInference.Compilation.everyRequest
#print axioms VerifiableInference.Compilation.realSide
#print axioms VerifiableInference.Compilation.simulatedRuns
#print axioms VerifiableInference.Compilation.WholeView
#print axioms VerifiableInference.Compilation.HonestVerifierZeroKnowledge
#print axioms VerifiableInference.Compilation.WholeViewFollows
#print axioms VerifiableInference.Compilation.commitmentLife
#print axioms VerifiableInference.Compilation.WholeLife
