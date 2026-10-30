-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/Sim.lean: a simulator for the honest sender of one sending, the bound on queried
positions, and two conditional statements: under public premises, what the sender discloses has the
same distribution for any two data, and that distribution is the one of the simulator's output. It
claims no property of the protocol: not hiding, not zero knowledge.
Terms of Johnson/SendSim/At/: the paragraph "Terms" below; for the book,
Johnson/SendSim/At/Fresh.lean. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file has. Definitions, two named propositions, and one small theorem.
  sendSim         The simulator. It runs the honest sender's own two rounds, by the framework's
                  function play, on a job without data (bare) and on coins of its own, as many as
                  the sender takes. No second definition of a sending is written for it.
  Spec.rowsExact  The main statement, at the level of rows. For all P, first, ride, challenges ds
                  and queried positions asks: if the job fits its place (sendFits), the challenge
                  consists of exactly the seeds (seedsFit), no seed's factor is 0, and the positions
                  are within the bound (budAt), then the distribution of shownR over uniform coins
                  is the same for any two data. Statement only; proved as rowsExact.
  Spec.sendExactAt
                  At every Seated side ExactAt holds, with On := True (no
                  extra condition) and the bound budAt. Written out: for every state m, every front
                  with m.seen = front.seen that has every column that the side's rounds read
                  (front.holds), all challenges that the rounds can sample (drawsFit), and all
                  positions within the bound, what the sender discloses, over its coins, has the
                  distribution of what sendSim outputs, over its own. ExactAt's last premise, that
                  the part does not abort by its second rule, always holds here: sendPart's two
                  rules are constantly none. Statement only; proved as sendExactAt.
  freshAt_of_good
                  FreshAt, this file's copy of the field fresh of Good, is that field verbatim.
                  ExactAt is not the field exact: it lacks the field's premise on the opened
                  columns, and gives the field at every pre (ExactAt's docstring).

What the simulator is given. By its type (Sim) a simulator is given the public part of the input,
the front, the challenges of the part's rounds, for each root the positions that will be queried,
and coins of its own. Two of these depend on the index: the front (it holds values from other parts'
executions: items in the clear, opened columns, stored columns) and the public part of the input
(for the face .shared it is the key; for the face .own it is the instance, which holds the reply).
sendSim reads the challenges, the positions and its coins. It reads neither the front nor the public
part. It is built from P, first, ride and its address. P, first and the address are public data of
the place. ride is taken from the job; at the descriptions it is a term of the public part, and how
far it is connected with the later folding step is in the Limits of
Johnson/SendSim/Seat/AtDescLots.lean. The sender's data, in contrast, are what the job computes from
the prover's input and the earlier state (SendJob.data), so they may depend on the index.

Limits.
  - The statements hold vacuously where a premise fails. Nothing in Seated requires that the side's
    rounds can sample some list of challenges: where they can sample none, every statement at a
    Seated side (exact and fresh, in all their forms) is vacuous. K1's own two rounds can sample
    one, for every P (draws_some, Johnson/SendSim/At/DrawsSome.lean). That a Seated side's rounds
    are these is not part of Seated; for the sub-protocols of K1's own lot see member_of_own
    (Johnson/SendSim/Seat/AtDesc.lean).
  - sendFits is not a premise of Spec.sendExactAt. Where the job does not fit its place, the sender
    and the simulator both disclose the error value, and the statement says nothing.
  - None of the premises is proved in this file. At the descriptions of the release's files, Seated
    is proved only for the sides at the places of the kind K1 that result (3) of
    Johnson/SendSim/Defs.lean names (seatedAt_job, if the maker of the proof file's description
    succeeds; seatedAt_key). The other sendings of that kind are not covered. For sendFits and budAt
    there, see the table of premises in Johnson/SendSim/Defs.lean.
  - ride is a free variable of the job. Nothing here says that it is the one due at the place.
  - Defining a simulator claims nothing: a simulator is data, and exact and fresh are fields of a
    structure of definitions (Good).

Terms.
  sending       two rounds. In "SEND seed" the prover sends new oracle messages and the verifier
                samples seeds. In "SEND answer" the prover sends its answers in the clear. A
                sub-protocol of the kind K1 (Johnson/Desc/K1/Send.lean) is one sending and nothing
                else. K2 and K12 send tables too; they are not covered here.
  P             K1.Par: the public parameters of one sending: its place in the description, the
                codes, and the oracle messages that it announces (P.sent; shapeAt P k is the shape
                of number k).
  oracle message
                one of P.sent. It has main rows and mask rows (OracleShape). A row is encoded by a
                code (Code) with words of length 2^logN: the row's message of ell entries and its
                tail of r entries determine the word. "Message" alone means a row's message.
  tail          the r random entries of a row. As in the model (Johnson/SendSim/Defs.lean) a row's
                symbol at a point is the value of the polynomial whose lowest coefficients are the
                tail, followed by the message.
  tree, column  Oracle messages that share leaves are sent under one root (P.trees). Nothing is
                hashed in this folder: a tree is the table whose column at a position holds one
                symbol of every row of its oracle messages (treeTables). A query of a position
                discloses the whole column.
  seed, factor  The challenge of the first round is a list of seeds (seedsAt): each is a point and a
                factor in the extension field. "The challenge consists of exactly the seeds"
                (seedsFit) means that it has as many field elements as the seeds need: P.seeds *
                (P.coordinates + 1).
  answer, pad   A sampled oracle message (one with at least one answer) has answers, number i made
                with seed number i: a linear form, fixed by the seed, in the entries of its rows.
                The answer's pad is an entry that holds a coin. Its weight in that form is the
                seed's factor, and 0 in the other answers. In a row over the base field a pad takes
                three entries, with the weights factor times 1, θ, θ², where θ generates GE over GF
                (coef_sampleRow_pad, Johnson/SendSim/Tie/Sample.lean). The pads are at the end of
                the last mask row, or of the last main row if there is no mask row.
  mask row      a row that holds coins alone. The free entries of a sampled oracle message are the
                entries of its mask rows before the first pad, in the order of the coins; the
                verifier's own function freeMaskEntries (OnBytes/Iop/Send.lean) counts them. Later
                parts are meant to spend them.
  coin          a uniformly random element of the base field GF or of the extension field GE that
                the honest prover samples. The sender takes dueR P ride of them (Cs): tails, pads,
                mask rows, and the main rows of an oracle message that has main rows and no answer.
                Their order is in the head of Johnson/Desc/ProofFile/Honest/K1/Coins.lean.
  data          the entries of main rows that are not coins. In shownR and Spec.rowsExact they are a
                free function of oracle message, row and entry. In a job they are a function of the
                prover's input and of what came before the sender (SendJob.data). No theorem here
                says what they are.
  index         the part of the prover's input that all requests share (the framework's W₀). For
                background: in the release it is the model's weights; no Lean statement here says
                so.
  face          Face: how the parts of a chain of sub-protocols are given their input, and which
                part of it is public: .own in the first and second chain, .shared in the shared
                chain.
  sent along    An oracle message can be the fresh mask table of a later folding step, sent ahead of
                that step (Ride, with the step's numbers k and h). The table has 2^h mask rows, made
                of 2k + 1 coins: the coefficients of what the library calls the step's hiding
                polynomial (Ride.lay). ride k says whether oracle message k is such a table. Some
                files say that the table "rides".
  job           SendJob: P; first, the number of the first new oracle message; ride; and the data.
                The job fits its place if the public test sendFits accepts
                (Johnson/Desc/ProofFile/Honest/K1/Coins.lean).
  honest sender
                sendPart J (Johnson/Desc/ProofFile/Honest/K1/Part.lean): the honest prover's part
                for the sending. rowsR gives its rows as a function of data and coins.
  discloses     what the verifier sees of a part (Shown): its items in the clear, and the columns of
                its trees at the queried positions. It holds no root, no nonce, no salt and no proof
                of work: these are the compiler's, and nothing is hashed here. shownR writes this
                out for the sender, as a function of P, first, ride, data, challenges, positions and
                coins. That the sender at a Seated side discloses shownR, if the job fits, is a
                theorem (showsAt, stated in Johnson/SendSim/At/Member.lean, proved in
                Johnson/SendSim/At/Shows.lean).
  queried positions
                asks: for each round and each root of the part, the positions that will be queried
                in the whole execution. asked asks τ is the list for tree τ of the first round.
  bound         budAt P asks: for each oracle message in a tree, the queried positions give at most
                r distinct positions modulo the length of the main code, if it has main rows, and at
                most r of the mask code modulo its length, if it has mask rows. It reads no
                challenge.
  at the level of rows
                for the function shownR, without the framework.
  framework     Johnson/Desc/ProofFile/Honest/Frame.lean, and
                Johnson/Desc/ProofFile/Honest/Side.lean. A part (Part) is the honest prover's
                algorithm for the rounds of one sub-protocol, or for a stretch of them. play runs a
                list of rounds on given challenges. A simulator (Sim) is paired with each part; a
                list of such pairs is a row. A side (Side) is a sub-protocol of a description
                (block) with a row; its members (Member) are the parts with their rounds and
                simulators. In Seat/ "member" also means a sub-protocol in a description's list.
  abort         A part has two rules (bad, hid) that say, from the challenges alone (hid also from
                the input, in the first and second chain), when it stops sending. stopAt says
                whether and by which rule it aborts. exact and fresh are required only where the
                part does not abort by hid. The sender has neither rule: it never aborts. An error
                of a round (the job does not fit) does not count as an abort; then the error value
                is disclosed.
  state, front  The state of an execution between two rounds (Mid): the prover's input, the
                challenges heard, what the parts pass on, the rounds seen so far, and the columns
                that the player hands the parts (opened; none: it hands none). The front
                (Before): what a simulator is given of the execution before its part: round by round
                what earlier parts disclose, with their columns at all positions that are queried in
                the whole execution, and the queried columns of stored tables.
  Good          the framework's structure of five fields on a side. fits: the row has one move for
                each round, there are as many lists of oracle messages as rounds, and each simulator
                names its part's address. plays and acc speak of the whole row: it can be run, and
                the verifier accepts. Both have a precondition A, and plays a postcondition B; A and
                B are parameters of Good, and both fields hold vacuously where A never holds. exact
                and fresh: the next entry. On is a further parameter: a condition on a part's
                carried runs, the state and the front. pre is another: a list of declared rounds; of
                the five fields exact alone reads it (the next entry).
  exact, fresh  ExactAt: under On, m.seen = front.seen, drawsFit, the bound, front.holds and
                "no abort by hid", what a part discloses, over its own coins and the runs that it
                spends, at fixed runs that it carries, has the distribution of its simulator's
                output. The field exact has one premise more: m.opened is what the front holds for
                the reads of pre. ExactAt is asked at every m.opened, and gives the field at every
                pre. fresh (FreshAt), and what runs are: Johnson/SendSim/At/Fresh.lean.
  Seated σ J    The side's row is sendPart J alone, with sendSim; the side passes the framework's
                test fits, so it has two rounds; its rounds and oracle messages agree with the
                sender's in what play reads of them (shapeOf); and every list of challenges that its
                rounds can sample (drawsFit) consists of exactly the seeds, with no factor 0.

How it fits. rowsExact (Johnson/SendSim/At/RowsExact.lean) is proved from the model's theorem
sendExact (Johnson/SendSim/CoreProofs.lean) through the instance of Johnson/SendSim/At/Bridge.lean.
Johnson/SendSim/At/Member.lean and Johnson/SendSim/At/Joins.lean carry it to sendExactAt
(Johnson/SendSim/At/ExactAt.lean). Sides that are Seated: Johnson/SendSim/At/SeatedAt.lean;
seatedAt_job is in Johnson/SendSim/Seat/AtDescStands.lean, seatedAt_key in
Johnson/SendSim/Seat/AtKeyStands.lean.

Where each premise comes from. sendFits is an executable test, to be evaluated at each place.
seedsFit and "no factor is 0" follow from what the rounds of a Seated side can sample: K1's
declaration of its first round samples each factor among the elements other than 0 (drawNZ,
Johnson/Desc/K1/Send.lean; seated_of_send, Johnson/SendSim/At/SeatedAt.lean). budAt is for whoever
counts the positions that a whole execution queries of each tree (Johnson/SendSim/Seat/Bud.lean).
Seated is for whoever proves that the sub-protocol at the place is K1's, as the description wraps
it.

The other names.
  bare, standIn   the job without data, at an input and a state of type Unit; a state at which
                  nothing has been heard or seen, and no columns are handed.
  roundsOf        the sending's two rounds with their oracle messages, as K1 declares them.
  shapeOf         what play reads of a round: the items that are not roots, and each oracle
                  message's log-length and number of words.

Notes: where the definitions put a default value (0 or empty). Where the job fits, no default value
stands in for a coin or a pad; this is partly by inspection, and the theorems named in the second
note are for oracle messages that are not sent along.
  - A missing datum (none) reads 0, and so does a datum of GE in a row over GF. Entries that hold
    coins ignore the data: a pad's entry and the main rows of an oracle message without an answer
    are coins whatever the data say (rowsR).
  - A coin's number beyond the sender's number of coins reads 0 (cf and ce read a coin by its
    number). Where the job fits, each slot of a coin (Seat) in an oracle message that is not sent
    along reads the coin with the slot's own number, and that number is within the number of coins
    (seat_reads, Johnson/Desc/ProofFile/Honest/K1/SeatReads.lean; seat_in,
    Johnson/Desc/ProofFile/Honest/K1/Seat.lean). That rowsR reads at no other number is by
    inspection, not proved.
  - The words of oracle messages that are not the place's own count as 0 in the held words from
    which the answers are made, as in the sender's own definition. They reach no answer: an answer
    is a form of the held word of its own oracle message (value_stAt, Johnson/SendSim/At/Stat.lean).
  - An oracle message has at most one answer for each seed that is cut off a challenge, whatever the
    challenge. What can be missing is a seed's factor, for which cutSeeds puts 0, or a coordinate of
    its point, which leaves the point shorter. This is public, and excluded by seedsFit.
  - A word of a column beyond the column's length counts as 0 (treeTables). A missing list of
    positions counts as empty (asked; the framework's shownOf does the same).
  - Where the place's trees cannot be made, the layout counts as empty (budAt; the columns): nothing
    is bounded and no column is disclosed. The answers are still sent; the bound does not concern
    them.
  - The number of a code or of an oracle message beyond its array reads a code or a shape of zeros.
    The test sendFits excludes this; where the job does not fit, the error value is disclosed on
    both sides.

Sources. The statements follow a written argument of this project, which is not in the repository:
run the same algorithm on the data 0; shift the coins by a fixed vector. They differ from it in six
points.
  (1) The main statement, Spec.rowsExact, is below the framework, at the level of rows. It compares
      any two data, for functions of (P, ride, data, coins, challenges, positions). So a sender
      whose data depend on carried coins can use it.
  (2) The bound does not require that a position is below the tree's length.
  (3) One structure, Seated, connects a side with the sender's shapes: two rounds, by the
      framework's own test on a side; what play reads of them; and, for the round of the seeds, not
      clauses on its declaration but what they give: a list that the rounds can sample consists of
      exactly the seeds, with no factor 0 in the field.
  (4) The sender is alone in its row.
  (5) In rowsR data are in main rows alone.
  (6) Which tables are sent along is a free variable of the job.
-/
import Johnson.Desc.ProofFile.Honest.K1.Part
import Johnson.Desc.ProofFile.Honest.Side

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (shapeAt answers held)

variable {S Cl V W X Pb : Type}

/-- The job with the public parameters P, first and ride and without data, at an input and a state
of type Unit. -/
def bare (P : K1.Par) (first : Nat) (ride : Nat → Option Ride) : SendJob Unit Unit :=
  ⟨P, first, ride, fun _ _ _ _ _ => none⟩

/-- A state of an execution at which no challenge has been heard and no round has been seen, and no
columns are handed. -/
def standIn : Mid Unit Unit := ⟨⟨(), [], ()⟩, [], [], none⟩

/-- The sending's two rounds, each with its oracle messages, as K1 declares them. -/
def roundsOf (P : K1.Par) : List (Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle) :=
  (K1.rounds P).zip (K1.oracles P)

/-- The simulator: it runs the honest sender's own two rounds on the job without data, on coins of
its own. Of what a simulator is given it reads the challenges, the queried positions and its
coins. -/
def sendSim (P : K1.Par) (first : Nat) (ride : Nat → Option Ride) (a : Addr) : Sim Pb where
  addr := a
  takes := dueR P ride
  tell := fun _ _ ds asks c =>
    (play ((sendPart (V := Empty) (bare P first ride)).steps "" a (roundsOf P) none (c, (), ()))
      ds [] standIn).toOption.map fun y => shownOf y.1 asks

/-- The queried positions of tree number τ of the sender's first round; the empty list if the list
is missing. -/
def asked (asks : List (List (List Nat))) (τ : Nat) : List Nat := (((asks[0]?).getD [])[τ]?).getD []

/-- The bound on queried positions. For each oracle message k in a tree τ: the positions queried of
τ, reduced modulo the length of the code, are at most r distinct ones, for the main code if k has
main rows and for the mask code if k has mask rows. -/
def budAt (P : K1.Par) (asks : List (List (List Nat))) : Prop :=
  ∀ k τ, k < P.sent.size → ((Own.treesMade P.codes P.sent).getD {}).tree[k]? = some τ →
    ((shapeAt P k).mainRows ≠ 0 →
      ((asked asks τ).map
          (· % 2 ^ (P.codes.base.getD (shapeAt P k).code default).logN)).toFinset.card
        ≤ (P.codes.base.getD (shapeAt P k).code default).r) ∧
    ((shapeAt P k).maskRows ≠ 0 →
      ((asked asks τ).map
          (· % 2 ^ (P.codes.mask.getD (shapeAt P k).maskCode default).logN)).toFinset.card
        ≤ (P.codes.mask.getD (shapeAt P k).maskCode default).r)

/-- What the honest sender discloses in its two rounds, written out: first the columns of its trees
at the queried positions, made of the rows rowsR; then its answers. -/
def shownR (P : K1.Par) (first : Nat) (ride : Nat → Option Ride)
    (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) (c : Cs (dueR P ride)) : List Shown :=
  [⟨[], (treeTables P (rowsR P ride data c)).zipIdx.map fun t =>
      (asked asks t.2).map fun p => (p, t.1.col p)⟩,
   ⟨(answers P (stAt P first) first (held (fun _ _ _ => 0) first P (rowsR P ride data c))
      (seedsAt P ds)).map fun a => (Said.answer (toE a)).got, []⟩]

/-- If the job fits its place, the challenge consists of exactly the seeds, no seed's factor is 0
and the queried positions are within the bound, then the distribution of shownR over uniform coins
is the same for any two data. Statement only; proved as rowsExact in
Johnson/SendSim/At/RowsExact.lean. -/
def Spec.rowsExact : Prop :=
  ∀ (P : K1.Par) (first : Nat) (ride : Nat → Option Ride)
    (data data' : Nat → Nat → Nat → Option (GF ⊕ GE)) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))),
    sendFits P ride = true → seedsFit P ds = true → (∀ s ∈ seedsAt P ds, readE s.2 ≠ 0) →
    budAt P asks →
    (Prob.unif (Cs (dueR P ride))).map (shownR P first ride data ds asks) =
      (Prob.unif (Cs (dueR P ride))).map (shownR P first ride data' ds asks)

/-- ExactAt is the form WITHOUT the premise on the opened columns; ExactMemberAt
(Johnson/Desc/ProofFile/Honest/Small/Field.lean) is the form WITH it, which is the field exact of
Good. ExactAt gives it at every pre (exactAt_of_exact, same file).
For each member of the side, under six premises (On; m.seen = front.seen; the rounds can sample ds;
the bound bud; front.holds; no abort by hid), what the part discloses, over its own coins and the
runs that it spends, at fixed carried runs, has the distribution of its simulator's output. -/
def ExactAt (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (chain firstTree : Nat)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) : Prop :=
  ∀ u ∈ σ.members, ∀ ca m front ds asks, On u ca m front → m.seen = front.seen →
    drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
    front.holds chain firstTree (u.rounds.map (·.1)) ds = true →
    u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid →
    (Prob.unif (Cs u.part.takes × CsAll u.part.spends)).map
        (fun c => σ.shows φ u (c.1, c.2, ca) m ds asks) =
      (Prob.unif (Cs u.sim.takes)).map fun c => u.tells φ c m.st.input front ds asks

/-- The field fresh of Good as a proposition of its own. For each member of the side and each
address p, at fixed runs sp and ca that the part spends and carries, under three premises (the
rounds can sample ds; the bound bud; no abort by hid), over the part's own coins the tuple (the runs
that p spends, what the part discloses, the known runs) has the distribution in which the runs that
p spends are replaced by fresh uniform values. -/
def FreshAt (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (Bk : ProverCoinCounts) (ord : List Place)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) : Prop :=
  ∀ u ∈ σ.members, ∀ (p : Addr) sp ca m ds asks,
    drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
    u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid →
    (Prob.unif (Cs u.part.takes)).map (fun c =>
        (cutAll c (Bk.spentBy ⟨σ.block.place, u.number⟩ p), σ.shows φ u (c, sp, ca) m ds asks,
          cutAll c (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p))) =
      (Prob.unif (CsAll ((Bk.spentBy ⟨σ.block.place, u.number⟩ p).map Ahead.named) ×
          Cs u.part.takes)).map fun a =>
        (some a.1, σ.shows φ u (a.2, sp, ca) m ds asks,
          cutAll a.2 (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p))

-- An earlier state of this library had exactAt_of_good here (Good gives ExactAt). The field exact
-- of Good now has one premise more than ExactAt, so g.exact no longer gives ExactAt, and no law
-- here leads from Good pre to it. From Good pre to the field's form: members_of_good
-- (Johnson/Desc/ProofFile/Honest/Small/Field.lean).

/-- FreshAt is the field fresh of Good. -/
theorem freshAt_of_good {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    {φ : Face V W Pb} {σ : Side S Cl V W X Pb} {Bk : ProverCoinCounts} {ord : List Place}
    {chain firstTree : Nat} {A B : Coins Bk → S → Mid W X → Env → Prop}
    {On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop}
    {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop}
    (g : Good pre φ σ Bk ord chain firstTree A B On bud) : FreshAt φ σ Bk ord bud := g.fresh

/-- What the framework's function play reads of a round: the items that are not roots, and each
oracle message's log-length and number of words. -/
def shapeOf (r : Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle) :
    List Fmt.Item × List (Nat × Nat) :=
  (r.1.items.filter (· != .root), r.2.map fun o => (o.logLength, o.words))

/-- The side σ has the honest sender of the job J, alone, with its simulator as its row, and its
sub-protocol's rounds agree with the sender's. -/
structure Seated (σ : Side S Cl V W X Pb) (J : SendJob W X) : Prop where
  /-- the row is the honest sender, alone, with its simulator -/
  row : σ.row = [(sendPart J, sendSim J.P J.first J.ride ⟨σ.block.place, 0⟩)]
  /-- the framework's own test on a side: as many rounds as the row has moves, so two; as many lists
  of oracle messages; the simulator names its part's address -/
  fits : σ.fits = true
  /-- the sub-protocol's rounds agree with the sender's in what play reads of them -/
  shape : (σ.block.rounds.zip σ.block.oracles).map shapeOf = (roundsOf J.P).map shapeOf
  /-- a list of challenges that the rounds can sample consists of exactly the seeds, with no
  factor 0 -/
  draws : ∀ ds, drawsFit σ.block.rounds ds = true →
    seedsFit J.P ds = true ∧ ∀ s ∈ seedsAt J.P ds, readE s.2 ≠ 0

/-- ExactAt holds at every Seated side, with On := True and the bound budAt.
Statement only; proved as sendExactAt in Johnson/SendSim/At/ExactAt.lean. -/
def Spec.sendExactAt : Prop :=
  ∀ (S Cl V W X Pb : Type) (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : SendJob W X)
    (chain firstTree : Nat), Seated σ J →
    ExactAt φ σ chain firstTree (fun _ _ _ _ => True) fun _ _ asks => budAt J.P asks

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.freshAt_of_good
#print axioms OnBytes.SendSim.At.bare
#print axioms OnBytes.SendSim.At.standIn
#print axioms OnBytes.SendSim.At.roundsOf
#print axioms OnBytes.SendSim.At.sendSim
#print axioms OnBytes.SendSim.At.asked
#print axioms OnBytes.SendSim.At.budAt
#print axioms OnBytes.SendSim.At.shownR
#print axioms OnBytes.SendSim.At.Spec.rowsExact
#print axioms OnBytes.SendSim.At.ExactAt
#print axioms OnBytes.SendSim.At.FreshAt
#print axioms OnBytes.SendSim.At.shapeOf
#print axioms OnBytes.SendSim.At.Seated
#print axioms OnBytes.SendSim.At.Spec.sendExactAt
