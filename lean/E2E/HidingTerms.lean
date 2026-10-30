-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/HidingTerms.lean

Terms for the files of this folder and of AtFullSide/E2E/ on index privacy after hashing. This file
holds this comment and no code. The group's seven main files are E2E/ZetaAtCaps.lean,
E2E/StringsOpenInGame.lean, AtFullSide/E2E/AtWrittenFiles.lean, E2E/LinkLaidPrivacy.lean,
E2E/LinkLaidAllAtOnce.lean, AtFullSide/E2E/LinkLaidAtWrittenFiles.lean and
AtFullSide/E2E/LinkLaidAccepted.lean. Where the group stands on the way to index privacy of the
protocol: the header of E2E/ZetaAtCaps.lean. For other words of the library see lean/GLOSSARY.md.

Index privacy.
  Index: what the scheme commits to. In the release's use it is the model's weights, as a matrix of
    the index type; no statement in these seven files ties it to a weight file.
  Index privacy (ZKCP.Gen.PrivacyOn R A B Sim ζ ok, ZKCP/OnRange.lean) asks for a simulator that is
    given the index's public parameters, the number of batches and the requested instances, but not
    the index. PrivacyOn is PrivacyFor (ZKCP/Gen.lean) at every index of the range and every valid
    environment. What the simulator makes (the public key, the oracle's answers and all proofs) must
    be statistically close to what an adversarial verifier really sees.
  For every index i with ok i, every valid environment and every adversary with at most t oracle
    queries and N batches, the real and ideal views are within statistical distance ζ t N. A view is
    the key, the proofs released, the oracle queries with their answers, and the adversary's coins.
    The real experiment runs the scheme's committer and prover on i; the ideal experiment runs the
    simulator, whose oracle answers are consistent with probability 1.
  The environment names each batch of at most B instances from the adversary's whole view so far. It
    is chosen after the index and may know it; it is valid if every instance that it names is in the
    relation for i. So «without the index» is said of the simulator: the instances come from the
    environment in both experiments.
  In the statements of this folder and of AtFullSide/E2E/ the public parameters have the type Unit,
    B is 1, ok holds of every index, and the simulator simWholeKey encodes a fixed index i₀ in the
    true one's place. This is the library's form for batches, with the simulator named; the cited
    definition has no batches (lean/TERMS.md, «index privacy for batches»).
  For two indices with the same public parameters, under one environment that is valid at both, the
    real views are within twice the error (OnBytes.WholeKey.real_real). So the statement says
    something only where the error is well below 1/2. It says something about a protocol only
    together with completeness of the same provers: provers that send fixed messages can be
    simulated too.
  The protocol's own provers: the provers that send the protocol's messages, which they compute from
    the index and the tables' randomness. Placeholder provers send each round's fixed message
    instead. Lean has one of the three as an explicit term, the link's (explicitLinkProver b Z); that it is
    the protocol's link prover rests on the acceptance theorem, on two_plains and on inspection.
  What the key and the proofs hold with the placeholder provers: the tables' roots and OOD samples;
    and in each produced proof the fixed messages, the nonces, and opened columns of the index's
    tables with salts and paths. This list is not proved in Lean: it is by inspection of the
    definitions. The counts of opened positions are proved in E2E/StringsHoldClosed.lean.
  R, Ryes: R is any pair of relations `R.yes` ⊆ `R.no` between indices and instances
    (`ZKCP.Gen.RelPair r.Index r.Instance Unit Unit`: the types of witnesses and of public parameters are both
    `Unit`), and Ryes any relation that holds wherever `R.yes` does. Each statement holds for every
    such pair: nothing ties R to the model's computation.
  The model: Each use of the hash is an independent random oracle on structured inputs, and
    randomness is uniform. The provers, the committer and the simulator are Lean terms, tied to no
    program, and the simulator's running time is not modelled.

The public files and the parameters.
  Z: the three public files: the layout file, the scale file and the parameter file.
  Z is in scope (`VerifierAndGoals.InScope Z = true`, Ladder.lean): the library's reader accepts the three
    files; the layout file is the stored full-size example's; the parameter file is that example's,
    byte for byte, but for eight free numbers; and 2 ^ 8 ≤ theta. So only the scale file and these
    eight numbers are free. At files out of scope `VerifierAndGoals.verify` rejects.
  Acceptance policy: three of the eight free numbers, (C, theta, cap) in the library's names (this
    cap is not a search limit): a clip, a bound on the mean cost and a limit on the number of
    positions above the clip (lean/GLOSSARY.md, "first choice, exact match, acceptance policy").
    `VerifierAndGoals.storedPublicFiles` is the stored full-size example; `VerifierAndGoals.zGap` is the same three files with
    another policy (Ladder/Stored.lean).
  The description is live at Z: `protocolDataWellFormed (asDescriptionFiles Z) = true`. This is the test that the IOP as
    written in Lean (the description) runs on the public files; where it fails, the verifier rejects
    every proof.
  The verifier's parameters at Z: `(VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input Z c m`, which the
    top-level verifier `VerifierAndGoals.verify` gives to the compiled verifier.
  The digest c and the second public reading m: the verifier asks the hash function for the digest c
    of the three files (`readConfig Z`). Then it runs a further algorithm with access to the hash
    function on the files and c (`readMore Z c`); m is what that returns. Each theorem is stated for
    each c and m fixed before the oracles are sampled.
  `atSecondHashFunction`: with the byte format's second hash function (`OnBytes.secondHashFunction`), as in all but two of
    the library's goals.
  The value that the library builds: `descriptionOfDataOnBytes flashProveData`, which `atSecondHashFunction theDescription` equals
    (`theDescription_eq`, Johnson/Goal/Description/Description.lean).
  Structure of parameters: a value r of the type `InnerCompilerInput`, or the provers, coins and numbers that
    a statement takes beside it.

The scheme.
  The scheme: `wholeKeySchemeOverTypedOracles r`, the hashed argument whose public key holds the first table's proof and
    all link proofs. Its verifier is called the compiled verifier or the hashed verifier: one thing.
  First table, copy, place, session: the committer encodes the index once (the first table) and then
    M + 1 more times under fresh randomness (the copies). A copy's place is its number in the key's
    list. A link proof ties a copy to the first table. Each copy serves at most s1 proofs
    (sessions); a session's prover samples the place of the copy that it uses.
  Key file, a copy's file, proof file: the key file holds the first table's proof, a copy's file its
    link proof, and the proof file a session's proof. Their three interactive protocols are the key
    file's, the link's and the proof file's.
  Prover: "honest side" in the Lean names: a prover's coins and strategy. The scheme has three: for
    the first table's proof, for a link proof and for a session. A strategy takes as private input
    the index and, for each table that it concerns, the table's encoding randomness and OOD seed.
  The placeholder provers: `silentAtC` (E2E/FiveLeftSilentCaps.lean). Lean's names call them silent
    (`silentAt`, `silentAtC`, `silent_not_two_plains`).
  Plain messages: what a prover sends in the clear, as against its oracle messages (`plains` in
    Lean; "plain parts" in lean/GLOSSARY.md and in some files of this group).
  Proof-of-work test: in a round with a test the verifier's message has some test bits, and the
    prover's plain message ends in a nonce (`GrW`, OnBytes/TypedOracleCompiler/Iop/BatchWire.lean). A verifier
    message passes if all its test bits are 0 (`RoundsQueryLayout.pass`, the same file). After hashing, the
    verifier's message is the oracle's answer to a query that holds the nonce, and the prover tries
    the nonces 0, 1, 2, and so on, one query each, until the answer passes. So the interactive
    protocols have these bits in the verifier's messages already.
  Search limit (`cap` in the Lean names): a search with limit k tries the nonces 0 to k: k + 1
    tries. So a limit of 2 ^ 40 gives 2 ^ 40 + 1 tries. The premise 2 ^ 40 ≤ cap i + 1 says "at
    least 2 ^ 40 tries": a limit of at least 2 ^ 40 - 1.
  A proof is produced: the prover returns a proof and not a failure. Bad event: the event whose
    probability a bound limits, such as that some proof is not produced.
  OOD seed, OOD sample: for each table an out-of-domain seed (`L.OutOfDomainSeed`), which the scheme computes
    from the table's root by an oracle (`tabG`, Johnson/WholeKey/Complete.lean), and, with the
    answers to it, the table's OOD sample (`L.recOf`).
  External strings: the input oracles of an interactive protocol (`ExtSpec`, Iop/InteractiveOracleProof.lean). Here
    they are the encoded tables `L.encodeIndex i r`.
  Oracle name: the random oracles form a family indexed by names (`OracleName`,
    OnBytes/TypedOracleCompiler/Compile/Batch/Oracles.lean), such as one for leaves and one for each protocol's
    Fiat-Shamir queries. The table of oracle answers (`Table`): the answers that have been sampled
    so far in a run.
  Rounds' data: the lists that give each round's sizes, tree shapes and proof-of-work bits, from
    which a protocol and its wiring are built (`RD`, `RDT`, `WholeD`). A whole file's protocol has
    three chains of rounds and three single rounds: the front round, the joining round and the seam
    (`roundsW`, E2E/ZetaAtWiring.lean). One-time chain: the key file's chain `key.oneTime` in the
    planner's output.
  Free bits: the ℓ bits of a leaf's salt that are sampled uniformly. Listed coins: the coins that a
    prover's enumeration lists for a compiled run (`PathsFit`, Johnson/WholeKey/Work.lean).
    Formatted annotation: `RoundSplits.Fmt` (Iop/BatchFmt.lean): every round has a format.

With the explicit link prover.
  The explicit link prover: `explicitLinkProver b Z`, a Lean term; its simulator is `homeSim Z` (both in
    Johnson/LinkSim/AtHome/SpecHome.lean). The acceptance theorem: `homeSide_accepted`
    (Johnson/LinkSim/AtHome/HomeAccepted.lean); for `laidAt`, `laid_accepted`
    (AtFullSide/E2E/LinkLaidAccepted.lean).
  two_plains (Johnson/LinkSim/AtHome/TwoPlains.lean): take any index and add 1 to its cell (0, 0);
    keep both tables' encoding randomness and seeds, and the prover's coin. Then what the explicit
    link prover sends in the clear differs, at the one verifier message whose hash blocks and
    proof-of-work bits are all 0. That holds for every index, all instances and every coin, before
    hashing. It compares two runs at the same coin: about the two distributions over the coins it
    says nothing. silent_not_two_plains: for the placeholder link prover ("silent" in the Lean
    names) the same statement is false.
  `laidAt`: the placeholder provers with the explicit link prover substituted for the link's
    placeholder. `fixedAt`: the placeholder provers at these parameters (E2E/LinkLaidPrivacy.lean).
  `homeR b Z` (Johnson/Goal/Conditions/HomeAtWider.lean), the input at one fixed digest, also called
    the parameters with an all-zero digest: the verifier's parameters at Z for the all-zero digest
    `allZeroDigest` and one second public reading (the empty one, at the value that the library builds),
    with the field `coinBound`, a number of coins, set to b Z. The verifier does not read that field
    (`VerifierAndGoals.verify_reBound`, Johnson/Goal/Conditions/ReBound.lean; E2E/HomeInputTie.lean).

The files.
  The release's goal statements stand in lean/Ladder.lean and in the files under lean/Ladder/;
    lean/README.md says which file states what. No statement of this folder or of AtFullSide/E2E/ is
    among them. Whether one becomes a goal statement is a person's to say.
  Lean has checked every proof in each file; the lines at its
    end ask Lean which axioms each theorem rests on. This file itself holds no proof and no such
    lines.


-/
