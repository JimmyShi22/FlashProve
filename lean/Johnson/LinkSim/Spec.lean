-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/Spec.lean: what a simulator for the link proof must satisfy, and this folder's
terms.

What this folder is about. The scheme argW (Johnson/WholeKey/Defs.lean) commits once to a private
index. The committer makes a first table, which encodes the index, and M + 1 copies. The
verification key holds each table's Merkle root and OOD sample, one proof on the first table, and
one link proof per copy. The link proof proves that a copy, a further encoding of the index under
fresh randomness, encodes the same index as the first table. It is made once for each copy, by the
committer; the verifier checks it as part of every proof (lean/TERMS.md). Each later request is
proved on one copy. This folder is about the link proof's interactive oracle proof (IOP), before
hashing.
This folder proves that the link proof's interactive protocol, at the library's full-size parameter
set (dsFull), is perfect honest-verifier zero knowledge relative to the input oracles' symbols at
the queried positions. The honest prover and the simulator are explicit (homeExactAt,
AtHome/HomeExactAll.lean). It also proves the link's four clauses among the premises of index
privacy, with both error terms 0 (linkFieldsHome). And it proves that this prover and simulator can
replace the link's in any structure of parameters that satisfies these premises at homeR b Z
(premW_withLaid, AtHome/CompileFit.lean).
The main theorem, homeExactAt, is in Johnson/LinkSim/AtHome/HomeExactAll.lean.
Johnson/LinkSim/AtHome/Home.lean's head says what is proved, what the simulator is given, and what
is left; homeExact there is the form that the premises of index privacy take.
The folder's security statements are homeExactAt (AtHome/HomeExactAll.lean), homeExact
(AtHome/Home.lean), homeHVZK (AtHome/HomeHVZK.lean) and linkFieldsHome (stated in
AtHome/SpecHome.lean, proved in AtHome/Home.lean). Every other file holds definitions, lemmas,
guards and tests on the way there or from there, and states no security property by itself. No file
of this folder states or proves anything on soundness.
The release's goal statements are in lean/Ladder.lean and in the files under lean/Ladder/;
lean/README.md says which file states what. No statement of this folder is among them.


A reading order. First Johnson/LinkSim/AtHome/HomeExactAll.lean, the main theorem in one short head.
Then Johnson/LinkSim/AtHome/Home.lean, what it means and what is left, and
Johnson/LinkSim/AtHome/SpecHome.lean, the prover and the simulator.
Johnson/LinkSim/AtHome/HomeHVZK.lean states the result in the library's own predicate (Honest.HVZK),
and Johnson/LinkSim/AtHome/HomeDigest.lean proves that the input's protocol structure depends
neither on the digest nor on b. The files go in three steps: for any protocol (this file,
SpecForm.lean, Bridge.lean, SameView.lean, and SpecTests.lean, SpecFormTests.lean and
SpecStopTests.lean), for the prover's algorithm (AtText/), and at homeR b Z (AtHome/). The folder's
root also holds general lemmas of algebra and of probability on no protocol (Tail.lean, Shift.lean,
UpTo.lean and their kin), and two files on PremW and on the error zetaW (Swap.lean, SwapZeta.lean).
The terms at the end of this head, and Johnson/LinkSim/AtText/Defs.lean's, are for looking things
up.

What this file has (namespace OnBytes.LinkSim). Definitions for arbitrary parameters, two small
theorems, and two statements whose proofs are in Johnson/LinkSim/Bridge.lean.

  SimOf Q      (the library's: Compile/Life.lean) the type of a simulator of the interactive
               protocol Q, as in honest-verifier zero knowledge in the exact form (Honest.HVZK,
               Iop/InteractiveOracleProof.lean). Its arguments are the instance, all of the verifier's randomness
               ρ at once, and the input oracles' symbols at the positions that the verifier reads.
               It returns a distribution on "a disclosed view, or none"; none is the value that the
               honest output takes at an abort. (What keeps the private input out of a simulator:
               see «the guard on what a simulator may read» in the terms below.)
  ExactOff H valid S U   for all w and x with valid w x, and for every ρ that lies neither in U
               nor in H.Hid w x, the honest output H.output w x ρ is equal, as a distribution, to
               S x ρ (Q.extAns x ρ (H.ext w)). The equality holds at each single ρ: there is no
               distance and no error term. U is a set of values of ρ, so by its statement it does
               not depend on the private input.
  validLk L ok Gs w x   the link's private input is w = (i, (r, e), (r', e')): the index i, the
               encoding randomness r and OOD seed e of the first table, and r' and e' of the copy.
               validLk holds exactly when ok i, both seeds lie in the set Gs, and x is the pair of
               honest OOD samples (recOf i r e, recOf i r' e'). ok and Gs are free parameters.
  LinkFields a S W ok Gs zL hL   four of PremW's clauses on the link proof, term for term as
               PremW has them (by inspection): on the input oracles of its honest prover a.Hs.Lk, on
               its run values, on the simulator S, and on its aborts. zL and hL are the link's two
               error terms, for simulation and for aborts. The docstrings of the four fields say
               what each asks.
  Spec.fieldsZero   if S is exact for the link's honest prover at every ρ (ExactOff with U empty),
               if that prover has no abort that depends on the private input (Hid is empty), and
               if the clauses ext and runVals hold, then LinkFields holds with both error terms
               0. Statement only; proved as fieldsZero in Johnson/LinkSim/Bridge.lean. This is the
               form that Johnson/LinkSim/AtHome/ uses.
  Spec.fieldsOfExact   the general form. If S is exact outside a set U, the clause on the simulator
               holds for every zL that is at least the probability that ρ falls into U once its
               proof-of-work bits are set to 0. The clauses ext, runVals and stops are premises and
               are passed through unchanged. Statement only; proved as fieldsOfExact in Bridge.lean.
               It is used in one place only: in the proof of fieldsZero, with U empty and both error
               terms 0. For U not empty it would serve a simulator that is exact but for a set.
  linkFields_of_premW   PremW gives LinkFields, by four projections: a check that PremW implies
               each of LinkFields's four clauses. The folder uses the other direction: it builds
               PremW from LinkFields (Johnson/LinkSim/Swap.lean, Johnson/LinkSim/AtHome/).
  LinkBeside L qpar qch   part of what PremW asks of the link's protocol besides a simulator: two
               counts and locality (how many positions of each table its verifier reads, and that
               its verifier is local). linkBeside_of_premW: PremW gives it. The folder divides what
               PremW asks of the link in three: LinkFields (the prover and the simulator: four
               clauses), LinkBeside (the protocol itself: two counts and locality) and LinkCompile
               (Johnson/LinkSim/AtHome/CompileSpec.lean: compilation data, round annotations and
               randomness).

How it fits. The statement of index privacy for the scheme that publishes its whole key
(Johnson/WholeKey/Statement.lean) has one bundle of premises, PremW
(Johnson/WholeKey/Premises.lean). Four of PremW's clauses concern the link proof's interactive
protocol: on the honest prover's input oracles, on its run values, on a simulator, and on the honest
prover's aborts. This file writes these four out by themselves (LinkFields) and names the property
from which the third follows (ExactOff). Johnson/LinkSim/SpecForm.lean, the other half of the
first step, defines a simulator that runs a prover strategy of its own on data built from its
three arguments (simOfStrat), and states Spec.exactOfShift, proved in Bridge.lean.

How ExactOff differs from Honest.HVZK. There the simulator is bound by "there exists"; here it is a
variable bound before the private input. There one exceptional set is measured; here the public set
U and the private part of the abort set (Hid) are kept apart, as PremW keeps them.

What is not here. (Where each is: the second step: Johnson/LinkSim/AtText/; the third:
Johnson/LinkSim/AtHome/.)
  The honest prover: the prover's messages are terms under Johnson/Prover/Link/ (not imported
      here); its coins' finite type, and the map from (index, both tables' randomness and seeds) to
      the prover's data, are fixed at the third step (explicitLinkProver,
      Johnson/LinkSim/AtHome/SpecHome.lean).
  The simulator as an explicit Lean term (the second step), and the proof that ExactOff holds of
      the two.
  The four clauses at homeR b Z (the third step).

Limits.
  The main theorem is not a statement that the index is hidden; that limit, and those on the
      verifier, on hashing, on the three provers and on programs, are told once, in Home.lean's
      head.
  The statements here are about one link proof. No honest prover and no simulator is named here.
  A placeholder prover that sends fixed messages meets ExactOff with a simulator that sends the same
      messages. So ExactOff says something of a protocol only together with completeness of the same
      honest prover. For the folder's own prover see Johnson/LinkSim/AtHome/Home.lean's head.
  The clause on the simulator (LinkFields.good) measures the set of ρ at which the two distributions
      differ at all. It leaves no room for a statistical distance: two distributions that differ by
      however little at every ρ force zL to be at least 1, where Hid is empty.
  ExactOff excuses every ρ in Hid. A prover whose abort depends on a private bit can meet ExactOff
      with U empty, and only the premise "Hid is empty" of Spec.fieldsZero excludes it
      (Johnson/LinkSim/SpecStopTests.lean).
  In Spec.fieldsOfExact the premise on U measures not U itself but the set of ρ that fall into U
      once their proof-of-work bits are 0, so it is not a statement that U is small.
  LinkFields does not ask that the compilation data W is well formed. That setting the proof-of-work
      bits behaves as a proper update of ρ (GrW.OK, OnBytes/TypedOracleCompiler/Iop/BatchWire.lean) is among the
      well-formedness conditions of the compilation data, which only PremW's field wires asks.

Notes.
  In the error of index privacy the link's two terms are multiplied by the number of copies (zetaW,
      Johnson/WholeKey/Zeta.lean): up to 710,324 at the full-size parameter set
      (noProverSide_atFiles and, at one copy more, not_noProverSide_copy, E2E/PremisesAtFiles.lean).
      At the values 0 and 0 that are proved here (linkFieldsHome), that product is 0. That is why
      the folder proves exactness and not a small error.
  After hashing, the error of index privacy has further terms that grow with the number of copies
      and are not the interactive protocol's. SEEDS has one seed per table. HASH counts the hash
      queries of each table's Merkle tree and of each link proof's run, and grows with the square of
      their number. Nothing in this folder bounds them (zetaW, Johnson/WholeKey/Zeta.lean).
      E2E/ZetaAtCaps.lean bounds the whole error, for any number of copies, at numbers whose error
      terms for simulators, aborts and seeds are 0 (zetaSmallC_description).
  Exactness with U empty asks more than PremW does: PremW compares the two distributions only at ρ
      with the proof-of-work bits 0, and ExactOff with U empty compares them at every ρ; both pass
      by Hid.
  Why homeExact needs no premise on the honest run: home_claim
      (Johnson/LinkSim/AtHome/HomeTies.lean).
  Forms of index privacy. The property is that of the definition that the library follows
      (lean/TERMS.md, note 9). ZKCP.HasIndexPrivacy (ZKCP/Defs.lean) states a weaker form of it, in
      spite of its name. ZKCP.Gen.PrivacyOn is the form with the stronger environment, over typed
      oracles. wholeKeyPrivacy_overOne and wholeKeyPrivacy_strong (Main.lean) carry it, with the
      same error, to one hash function and to one request per call (ZKCP.StrongPrivacyOn).
      HasIndexPrivacy of that scheme restricted to ok follows by strongPrivacyOn_iff and
      HasStrongIndexPrivacyWith.toHasIndexPrivacyWith; these two steps are not stated at argW. The
      converse fails in general (leaky_private, leaky_not_strong, ZKCP/Separation.lean).

Sources. ExactOff and the type of a simulator follow the form of Compile/Life.lean (SimOf) and
Iop/InteractiveOracleProof.lean (Honest.HVZK). The statement of honest-verifier zero knowledge for the link's
interactive protocol (ExactOff, homeExactAt) and the type of a simulator here do not count as made
independently of the further work that this protocol builds on (lean/CREDITS.md, under that
heading). The same holds of the statements in the files of this folder whose heads point to this
note.

Terms of this folder. This list holds for this folder; Johnson/LinkSim/AtText/Defs.lean holds the
terms of the algorithms, and lean/GLOSSARY.md the library's. Lean names stay as they are; paths are
under lean/.
The scheme.
  index (I)           What the scheme commits to, once; one part of the link's private input w: in
                      general an element of a type I. At homeR b Z it is a matrix of 3,076,096 rows
                      by 2^18 columns over the field GE (Cells, Johnson/Flat/Claims.lean). Of each
                      cell, only its first coordinate, in GF, is written into a table
                      (Johnson/Flat/CodingCells.lean). The theorems hold for every index of the
                      type; no statement here says that it is a model's weights.
  table               The codeword encodeIndex i r of the index i under encoding randomness r (HolographicProtocol.encodeIndex,
                      Hiop/RecInterface.lean). After hashing it has a Merkle tree; before hashing,
                      where this folder stands, it is an input oracle. At the full-size parameters a
                      table has 2,048 rows and 2^32 positions. Each row's message has 402,653,184
                      entries (402,653,181 of data and 3 of pad), and its tail 44,040,191 more. Tail
                      and pad: Johnson/LinkSim/AtText/Defs.lean's terms.
  symbol              The value of a table at one position, together with that position: the pair of
                      the position and the column of its 2,048 rows' values there (SgX,
                      Run/PlanQX.lean).
  first table         The table whose root begins the verification key.
  copy                A further table of the same index, with fresh randomness. The key holds its
                      Merkle root, its OOD sample and its link proof. Each later proof runs on one
                      copy, chosen at random. There are M + 1 copies (AtRecs.M,
                      Johnson/WholeKey/Premises.lean).
  OOD samples, two kinds
                      The instance's OOD samples (Rec, recOf) come one per table. Each is a verifier
                      seed, drawn after the table is sent, with the prover's out-of-domain (OOD)
                      answers there: recOf L i r s = (s, L.honestOutOfDomainAnswer i r s). At the full-size parameters
                      the seed is a point of 29 coordinates with a non-zero scalar that multiplies
                      the pad, and there is one answer per row. The link proof's own OOD samples are
                      another thing: the verifier's samples on the prover's own oracle messages
                      inside the link proof (Johnson/LinkSim/AtText/Defs.lean's terms).
  link proof (L.link, Lk)
                      The sub-protocol for the equality relation on two encoded indices. Its input
                      oracles are the codewords of the first table and of a copy, and its instance
                      is their two OOD samples. Its soundness clause (sndL, Hiop/RecInterface.lean)
                      asks that the copy decode to the same index as the first table, but for two
                      exceptions stated there. Nothing in this folder is about its soundness.
  sub-protocols       Three, in HolographicProtocol (Hiop/RecInterface.lean). offline (T): one proof on the first
                      table, made once. link (Lk): the link proof, one per copy, made once. onlineBatch (B):
                      the proof for one request, on a copy.
  session             One run of onlineBatch: the proof for one request. s1 is the number of sessions per
                      copy for which the theorem's query budget is stated (NumsW.s1,
                      Johnson/WholeKey/Premises.lean). The prover itself does not count them.
  index privacy       Asks for a simulator that is given the index's public parameters, the number
                      of batches and the requested instances, but not the index. What it makes (the
                      public key, the oracle's answers and all proofs) must be statistically close
                      to what an adversarial verifier really sees. In Lean: ZKCP.Gen.PrivacyOn
                      (ZKCP/OnRange.lean); in full: E2E/HidingTerms.lean. wholeKeyPrivacy
                      (Johnson/WholeKey/Main.lean; stated in Statement.lean) is a conditional
                      theorem. If the relation's true instances lie in Ryes and PremW holds, argW
                      has this property at one request per proof, at the indices of a range ok, with
                      a named simulator and the error zetaW. Other forms: Notes, "Forms of index
                      privacy".
  PremW               The premises of that conditional theorem: one structure of 20 clauses on the
                      protocols, the compilation data, the three honest provers and their
                      simulators, the randomness and the numbers (Johnson/WholeKey/Premises.lean).
  structure of parameters (AtRecs)
                      The honest party's parameters, 32 fields: among them the three honest provers,
                      the bounds on proof-of-work attempts, the number of copies, the run values,
                      the window, and how randomness is enumerated. The verifier reads none of them.
                      (Johnson/WholeKey/Premises.lean)
  error terms zL, hL  The link's two error terms in PremW. zL bounds the probability, over verifier
                      messages with their proof-of-work bits set to 0, that the honest and the
                      simulated distributions differ outside Hid. hL bounds the probability of Hid.
                      How they count once per copy: see the notes above.
The interactive protocol.
  verifier message (ρ)
                      The verifier's randomness for a whole run, one part per round (Rho,
                      Iop/Shape.lean). It is fixed first, and the prover's strategy is run against
                      it.
  hash blocks         The verifier's random strings in each round, from which its challenges are
                      computed; after hashing they are hash outputs.
  input oracles       Strings that the verifier reads but the prover does not send. For the link,
                      the two tables' codewords. Lean calls them external strings (ext, extAns).
  plain part          What the prover sends in the clear in a round, beside its oracle message. The
                      verifier reads it in full.
  blinded             A predicate on the positions of the prover's own oracle messages
                      (InteractiveOracleProof.blinded, Iop/InteractiveOracleProof.lean). In the link every such position is blinded,
                      by definition. It says nothing of the input oracles.
  disclosed view (DView)
                      What the verifier sees of one run (InteractiveOracleProof.dview, Iop/InteractiveOracleProof.lean). It holds
                      three things: the plain parts; the symbols of the input oracles at the
                      positions read; and the symbols of the prover's own oracle messages at every
                      position that is read or not blinded. So in the link it holds the prover's own
                      symbols only at the positions read.
  the format's view (Fmt.View)
                      The data that the verifier's decision reads, in the format's own terms (View,
                      Fmt/View.lean): for each round, the items of the prover's message as read and
                      what the round samples; and the opened columns, each with its tree and
                      position. Roots, nonces, salts, given digests and chain values are not in it.
                      In this folder it is read off a transcript by rvSL, rhoSL and colAtS
                      (OnBytes/TypedOracleCompiler/Run/PlanQS.lean), and the stored tables' columns off the input
                      oracles (viewX, OnBytes/TypedOracleCompiler/Run/PlanQX.lean). It is not the disclosed view
                      (DView), which is what the theorems on distributions compare.
  honest prover (Honest)
                      A finite type of coins, the input oracles, a strategy, and an abort set
                      (Iop/InteractiveOracleProof.lean). The abort set has two parts: Bad depends on the verifier
                      message only, and Hid may depend on the private input.
  abort set (withheld)
                      Honest.withheld w x = Bad ∪ Hid w x: the verifier messages at which the honest
                      prover aborts. There its output is none; elsewhere it is the distribution,
                      over a uniform coin, of the disclosed view.
  explicit            Given as a Lean term, not under "there exists".
  the guard on what a simulator may read
                      What keeps a simulator from using the private input, and how far, is told in
                      Johnson/LinkSim/AtText/SpecExact.lean. homeSim Z is a closed term whose only
                      parameter is Z. So it holds nothing of a private input: in homeExactAt one
                      homeSim Z serves every private input.
  linkRec             A generic constructor of an honest link prover from a coin type, the input
                      oracles and a next-message function (Johnson/Prover/Link/LinkFrame.lean). It
                      sets both parts of the abort set to the empty set.
  Kc, coinsFull       Kc is the finite type of all random values that the link's honest prover draws
                      in one run at the full-size parameters. They are tails, pads, the coefficients
                      of each fold's hiding polynomial, the free entries of mask rows, and the
                      masking word of the last switch. By the count in
                      Johnson/Prover/Link/LinkCoin.lean (fr_linkN) there are 26,840 of them, each in
                      GE. coinsFull places them in the form that the prover's algorithm reads. The
                      tables' encoding randomness is not among them: it is part of the private
                      input.
  proof-of-work bits  In a round with a proof-of-work check, designated bits of the verifier's
                      challenge. The honest prover searches for a nonce that makes them all 0.
                      RoundsQueryLayout.zero (OnBytes/TypedOracleCompiler/Iop/BatchWire.lean) sets them to 0.
  bound on attempts (capL)
                      The proof-of-work search tries at most cap + 1 nonces. If all fail, the run
                      returns no proof.
  the algorithms (AtText/)
                      Johnson/LinkSim/AtText/Defs.lean's head explains the prover's algorithm
                      linkAll and the simulator's simAll. It also explains coins as variables and as
                      a finite type, the shift of the coins, and the words of the proximity test
                      (stage, switch, fold, pad, tail).
The concrete instance and the hashed argument.
  homeR b Z           The concrete instance at which AtHome/ states its theorems. It is one
                      structure (InnerCompilerInput, Johnson/Top/InnerCompiledVerifier.lean) that holds the three
                      sub-protocols, the compilation data and the honest party's algorithms. The
                      library's description builds it from the public files Z
                      (Johnson/Goal/Conditions/HomeAtWider.lean). Its type of indices and its
                      protocol structure L depend neither on the digest nor on b (homeR_I_at,
                      homeR_L_at, homeR_L_b, Johnson/LinkSim/AtHome/HomeDigest.lean). L holds the
                      encoder, the OOD samples and the link protocol HomeQ Z (homeR_link, there). By
                      inspection, not proved: the main theorem reads of homeR b Z only its type of
                      indices and L, and in the link protocol Z enters only through the verifier's
                      decision (see Johnson/LinkSim/AtHome/HomeExactAll.lean). b sets one field,
                      coinBound: the honest committer's randomness has coinBound + 1 values. Every statement
                      here holds for all b. verify runs the compiled verifier at an input whose
                      digests it reads off the hash function. homeR b Z is that input at the digest
                      allZeroDigest (all bits 0) and no further digests. That verify is ever called at this
                      digest is not proved. That bounds the statements after hashing
                      (AtHome/CompileFit.lean, E2E/LinkLaidPrivacy.lean), not homeExact, which reads
                      only the encoder, the OOD samples and the link protocol.
  compilation data (W)
                      For each round: the depths of its Merkle trees, where an oracle position
                      stands among a tree's leaves, how the verifier's message comes from hash
                      blocks, and the optional proof-of-work check. Lean: QueryLayout
                      (OnBytes/TypedOracleCompiler/Iop/BatchWire.lean).
  window (nR, nK, nJ) Three bounds, on rounds, on trees per round component and on leaves per tree
                      (Johnson/WholeKey/Defs.lean). Within them a hashed run's salts get random
                      bits; outside them a fixed public string (fill) stands in.
  run value (RV; rvL, pvL)
                      A public string that the prover also sends in the clear. The public prefixes
                      of one hashed run's leaf salts are made from it, so it matters only after
                      hashing. rvL reads it off the prover's coins, and pvL off the plain parts.
  public files Z (PublicFiles)
                      Three files as bytes: the parameter file, the layout file and the scale file.
                      Z may be any bytes.
  in scope            InScope Z = true, a Boolean function on Z (Ladder.lean). The library's reader
                      accepts the three files, and a condition holds on the request policy (2^8 ≤
                      theta). The layout file is the stored full-size example's, and the parameter
                      file is that example's byte for byte but for eight free numbers. Only the
                      scale file and these eight numbers are free, within what the reader accepts.
  live description    protocolDataWellFormed (asDescriptionFiles Z) = true, a second Boolean function on Z
                      (Johnson/Goal/Description/Live.lean). It is true when the library's
                      description can be built from Z and passes a test on its numbers. By itself
                      the value true does not show that the verifier accepts anything; acceptance is
                      proved for files in scope with a live description together (homeSide_accepted,
                      Johnson/LinkSim/AtHome/HomeAccepted.lean).
Parameters and numbers.
  full-size parameters
                      The library's one concrete parameter set for the link. frP (P15): the link's
                      public parameters as the verifier's description reads them: the field, the
                      codes, the link's shape and the five stages. frS (Sz): the same sizes in the
                      form that the mathematics reads. dsFull, also written dsF: one entry per round
                      after the trivial first one. An entry says what the round sends and samples
                      and which trees it opens. xsF: the openings of the input oracles. In round 3,
                      62 positions of the first table are read, then 62 of the copy. numsRef =
                      ⟨3076096, 7⟩: the index's shape, 3,076,096 rows and 2^(7 + 11) columns. That
                      numsRef's two numbers are those of the full-size parameter file is not proved
                      (Johnson/Flat/ThreeFull.lean).
  62 and 97           62 and 97 count positions of different oracles. 62: the link's verifier
                      queries at most 62 positions of each input oracle, the first table and the
                      copy (home_beside, AtHome/HomeTies.lean). 97, 49, 49, 50 and 40: the positions
                      that it samples in the prover's own oracle messages, at the five stages of the
                      link's proximity test (fr_cnts, AtText/SeamAtFull3.lean). 97 is the bare
                      number in linkNext frP frS 97.
  GF, GE              GF is the field of integers modulo p = 2^64 - 2^32 + 1. GE is its cubic
                      extension GF[x]/(x^3 - 2) (Cb/Gl/GlField.lean).
  41 and 42           dsFull has 41 rounds (fr_rounds41, Johnson/Prover/Link/GroupsFull.lean); the
                      link's protocol linkProtocolOfRoundData has 42, with the trivial first round in front
                      (length_full, Johnson/LinkSim/AtHome/CompileWire.lean). Both counts hold.
This folder's idioms.
  AtText/, AtHome/    Folder names. AtText/ holds the statements about the prover's and the
                      simulator's algorithms as single functions, mostly at any sizes; the files
                      whose names contain AtFull, and a few others, are at the full-size parameter
                      set. AtHome/ holds those at homeR b Z: at the public files and the protocol
                      structure of the concrete instance.
  Spec.x and x        A statement is written as a named proposition, def Spec.x : Prop, so that it
                      can be read apart from its proof. The theorem x proves it, sometimes in
                      another file.
  #print axioms lines Each asks Lean to list the axioms on which a theorem depends. The expected
                      output is a subset of propext, Classical.choice and Quot.sound, the standard
                      axioms of Lean and Mathlib: no placeholder for a missing proof and no axiom of
                      this library.
  maxRecDepth         Some concrete facts at the full-size parameters are proved under "set_option
                      maxRecDepth 100000 in", as the library's own are
                      (Johnson/Desc/K15/TypedV.lean). This raises a limit of Lean's elaboration; the
                      kernel still checks every term.



Outside this folder.
  verify              The library's verifier of the goals (lean/Ladder.lean). It tests that the
                      public files are in scope and parses the proof. It reads the hash function
                      twice, for the digest of the public files and for further digests. Then it
                      runs the compiled verifier at the input that these give.
  the programs        The release's C++ executables (committer, prover, verifier), outside lean/. No
                      statement in Lean is about them.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Premises

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.LinkSim
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Compile.Lifetime (SimOf)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## For any interactive protocol -/

section Generic
variable {X : Type} {E : ExtSpec}

/-- **Exact outside U**: for every valid pair (w, x) and every ρ outside U and outside H.Hid w x,
the honest output and the simulator's output are the same distribution. -/
def ExactOff {Q : InteractiveOracleProof X E} {Wt : Type} (H : Honest Q Wt) (valid : Wt → X → Prop) (S : SimOf Q)
    (U : Set (Rho Q.shape)) : Prop :=
  ∀ w x, valid w x → ∀ ρ, ρ ∉ U → ρ ∉ H.Hid w x →
    H.output w x ρ = S x ρ (Q.extAns x ρ (H.ext w))

end Generic

/-! ## At the link proof of a protocol structure (HolographicProtocol) -/

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- The link's valid inputs: the index satisfies ok, both OOD seeds lie in Gs, and the instance is
the pair of honest OOD samples of the first table and the copy. -/
def validLk (L : HolographicProtocol I X) (ok : I → Prop) (Gs : L.OutOfDomainSeed → Prop)
    (w : I × (L.EncodingRandomness × L.OutOfDomainSeed) × (L.EncodingRandomness × L.OutOfDomainSeed)) (x : L.Rec × L.Rec) : Prop :=
  ok w.1 ∧ Gs w.2.1.2 ∧ Gs w.2.2.2 ∧
    x = (L.recOf w.1 w.2.1.1 w.2.1.2, L.recOf w.1 w.2.2.1 w.2.2.2)

/-- **Four of PremW's clauses, at the link.** S: the link's simulator. zL, hL: the link's two error
terms, for simulation and for aborts. -/
structure LinkFields (a : AtRecs lam L Bd aT aL) (S : SimOf L.link)
    (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (ok : I → Prop) (Gs : L.OutOfDomainSeed → Prop) (zL hL : ℝ≥0∞) :
    Prop where
  /-- the input oracles are the two encodings of the index -/
  ext : ∀ i r e r' e', a.Hs.Lk.ext (i, (r, e), (r', e')) = (L.encodeIndex i r, L.encodeIndex i r')
  /-- for indices with ok i, at every ρ outside the abort set, the run value read off what the
  prover sends in the clear equals the one read off its coin (a run value is what the public
  prefixes of a hashed run's leaf salts are made from) -/
  runVals : ∀ i u u' κ ρ, ok i →
    ρ ∉ a.Hs.Lk.withheld (i, u, u') (L.recOf i u.1 u.2, L.recOf i u'.1 u'.2) →
    a.pvL ((a.Hs.Lk.strat (i, u, u') (L.recOf i u.1 u.2, L.recOf i u'.1 u'.2) κ).run ρ).1.plains =
      a.rvL κ
  /-- over uniform ρ, the probability of the following is at most zL: with its proof-of-work bits
  set to 0, ρ is not in Hid, and there the honest and simulated distributions differ -/
  good : ∀ i r e r' e', ok i → Gs e → Gs e' →
    pr (unif (Rho L.link.shape))
      {ρ | RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ ∉
          a.Hs.Lk.Hid (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e') ∧
        a.Hs.Lk.output (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e')
          (RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ) ≠
        S (L.recOf i r e, L.recOf i r' e') (RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ)
          (L.link.extAns (L.recOf i r e, L.recOf i r' e')
            (RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ) (L.encodeIndex i r, L.encodeIndex i r'))} ≤ zL
  /-- over uniform ρ, the probability that ρ with its proof-of-work bits set to 0 falls into Hid,
  the aborts that may depend on the private input, is at most hL -/
  stops : ∀ i r e r' e', ok i → Gs e → Gs e' →
    pr (unif (Rho L.link.shape))
      {ρ | RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ ∈
        a.Hs.Lk.Hid (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e')} ≤ hL

/-- PremW gives LinkFields for the link's simulator and error terms, by four projections. -/
theorem linkFields_of_premW {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {Sd : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
    {cA : L.OutOfDomainAnswer → List (Dig lam)} {p : Params} {a : AtRecs lam L Bd aT aL} {Sm : Sims L}
    {ok : I → Prop} {Gs : L.OutOfDomainSeed → Prop} {Ryes : I → X → Prop} {c : CoinNums Bd} {N : NumsW}
    (hP : PremW W Sd cA p a Sm ok Gs Ryes c N) : LinkFields a Sm.Lk W ok Gs N.zL N.hL :=
  ⟨hP.ext.Lk, hP.runVals.Lk, hP.good.Lk, hP.stops.Lk⟩

/-- **Part of what PremW asks of the link's protocol besides a simulator: two counts and locality.**
qpar, qch: how many positions of the first table, and of the copy, the link's verifier reads at
most; they enter PremW's query budgets budget₀ and budget₁. isLocal: its decision depends on the
input oracles and on the prover's oracle messages only at the positions read. A simulator is given
the instance (the two OOD samples), the verifier's messages and the symbols of the two encodings at
the positions read. What these inputs disclose of the index is the subject of the first limit in
Johnson/LinkSim/AtHome/Home.lean's head. -/
structure LinkBeside (L : HolographicProtocol I X) (qpar qch : ℕ) : Prop where
  cntLp : ∀ x ρ, ((L.link.extReads x ρ).filter (fun p => p.isLeft)).card ≤ qpar
  cntLc : ∀ x ρ, ((L.link.extReads x ρ).filter (fun p => p.isRight)).card ≤ qch
  isLocal : L.link.IsLocal

/-- PremW gives LinkBeside at its own read counts N.qpar and N.qch. -/
theorem linkBeside_of_premW {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {Sd : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL}
    {cA : L.OutOfDomainAnswer → List (Dig lam)} {p : Params} {a : AtRecs lam L Bd aT aL} {Sm : Sims L}
    {ok : I → Prop} {Gs : L.OutOfDomainSeed → Prop} {Ryes : I → X → Prop} {c : CoinNums Bd} {N : NumsW}
    (hP : PremW W Sd cA p a Sm ok Gs Ryes c N) : LinkBeside L N.qpar N.qch :=
  ⟨hP.reads.cntLp, hP.reads.cntLc, hP.isLocal.2.1⟩

/-- **From exactness outside a public set U to the clause on the simulator.** Statement only;
proved as fieldsOfExact in Johnson/LinkSim/Bridge.lean. -/
def Spec.fieldsOfExact : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (a : AtRecs lam L Bd aT aL) (S : SimOf L.link)
    (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (ok : I → Prop) (Gs : L.OutOfDomainSeed → Prop)
    (U : Set (Rho L.link.shape)) (zL hL : ℝ≥0∞),
    ExactOff a.Hs.Lk (validLk L ok Gs) S U →
    pr (unif (Rho L.link.shape)) {ρ | RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ ∈ U} ≤ zL →
    (∀ i r e r' e', a.Hs.Lk.ext (i, (r, e), (r', e')) = (L.encodeIndex i r, L.encodeIndex i r')) →
    (∀ i u u' κ ρ, ok i →
      ρ ∉ a.Hs.Lk.withheld (i, u, u') (L.recOf i u.1 u.2, L.recOf i u'.1 u'.2) →
      a.pvL ((a.Hs.Lk.strat (i, u, u') (L.recOf i u.1 u.2, L.recOf i u'.1 u'.2) κ).run
        ρ).1.plains = a.rvL κ) →
    (∀ i r e r' e', ok i → Gs e → Gs e' →
      pr (unif (Rho L.link.shape))
        {ρ | RoundsQueryLayout.zero L.link.shape aL (wLC W).sh ρ ∈
          a.Hs.Lk.Hid (i, (r, e), (r', e')) (L.recOf i r e, L.recOf i r' e')} ≤ hL) →
    LinkFields a S W ok Gs zL hL

/-- **Exact at every ρ, with no abort that depends on the private input: both error terms 0.**
Statement only; proved as fieldsZero in Johnson/LinkSim/Bridge.lean. Its four premises are
ExactOff with U empty, Hid empty, ext and runVals. The form used in Johnson/LinkSim/AtHome/. -/
def Spec.fieldsZero : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (a : AtRecs lam L Bd aT aL) (S : SimOf L.link)
    (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (ok : I → Prop) (Gs : L.OutOfDomainSeed → Prop),
    ExactOff a.Hs.Lk (validLk L ok Gs) S ∅ →
    (∀ w x, a.Hs.Lk.Hid w x = ∅) →
    (∀ i r e r' e', a.Hs.Lk.ext (i, (r, e), (r', e')) = (L.encodeIndex i r, L.encodeIndex i r')) →
    (∀ i u u' κ ρ, ok i →
      ρ ∉ a.Hs.Lk.withheld (i, u, u') (L.recOf i u.1 u.2, L.recOf i u'.1 u'.2) →
      a.pvL ((a.Hs.Lk.strat (i, u, u') (L.recOf i u.1 u.2, L.recOf i u'.1 u'.2) κ).run
        ρ).1.plains = a.rvL κ) →
    LinkFields a S W ok Gs 0 0

end OnBytes.LinkSim

#print axioms OnBytes.LinkSim.linkFields_of_premW
#print axioms OnBytes.LinkSim.linkBeside_of_premW
