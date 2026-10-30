-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WholeKey/Statement.lean: THE STATEMENT OF INDEX PRIVACY for the scheme with the whole key
published (argW, Johnson/WholeKey/Defs.lean), for ANY object with out-of-domain (OOD) samples, any
wires and any honest sides of its three protocols; with the simulator NAMED (simWholeKey,
Johnson/WholeKey/Wrap.lean) and the error WRITTEN OUT (zetaW, Johnson/WholeKey/Zeta.lean).

ONE THEOREM's TYPE, as the definition of a proposition, NOT PROVED IN THIS FILE (its proof:
wholeKeyPrivacy, Johnson/WholeKey/Main.lean), and one small theorem with its proof (the statement at
the range of all indices). A general statement. This file states no goal of the release.

  Spec.wholeKeyPrivacy   for all letters: under the premises PremW (Johnson/WholeKey/Premises.lean),
      and if every instance that the relation R calls true at an index is one at which the session's
      simulators are asked to be good (R.yes → Ryes): AT EVERY INDEX OF THE RANGE ok (a letter: a
      property of indices) the scheme argW at the honest side made of these meets the library's
      requirement of index privacy over typed oracles (ZKCP.Gen.PrivacyFor, ZKCP/Gen.lean: the
      environment that picks the instances sees the adversary's whole view and may decline), at one
      request a proof, with the simulator simWholeKey and the error zetaW. zetaW is a written term
      in named letters; its seven letters for errors each stand on the right of a "≤" in a premise
      of PremW.
  privacyAll_of_wholeKeyPrivacy   at the range of all indices that is the library's property
      ZKCP.Gen.HasIndexPrivacyWith.
Completeness, index binding, index privacy and the honest side's work AT ONE TERM:
Johnson/WholeKey/Bundle.lean (bundle_argW).

WHAT THE STATEMENT SAYS, in words. Fix the public letters: the object, the wires, the parameters,
the caps, the number of copies, the enumerations of coins, the honest sides, a set Gs of seeds, a
range ok of indices. For every index i of the range, every environment that names only instances
which are true at i, every adversary with at most t oracle queries and every number n of requests:
the adversary's view (THE WHOLE PUBLISHED KEY from the first step; each request with its proof; its
own queries with their answers; its coins) in the real experiment is within ζ(t, n) in statistical
distance of its view with the simulator; and the simulator never answers one query in two ways.

THE SIMULATOR is a reduction, which does the scheme's hash work and never holds an encoded index,
around a game of the interactive protocols alone, in which encodings of a fixed index i₀ are kept
and the interactive protocols' simulators answer (Johnson/WholeKey/Wrap.lean).

WHAT THE SIMULATOR IS HANDED: the public parameters, which are of the type with one member, and the
number of requests, which it does not read; each oracle query; for a request its instance. NOTHING
OF THE INDEX: that is so by the order of the quantifiers (all its letters are bound before the index
is named) and by its text (it is handed nothing else); it is no fact of a type alone. What is public
of an index lies in the letters in front of the statement.
AT A SEED OUTSIDE THE PUBLIC SET Gs the game refuses the table, and the simulator hands out a FIXED
KEY and serves nothing afterwards, while the real committer goes on. That is what ζ's term SEEDS
pays for.

ON WHAT THE STATEMENT LEANS, by the form of the scheme and of the experiment.
  * EVERY TABLE IS MADE BY THE COMMITTER, before the adversary moves: the first table and all
    copies. So the two queries of every table's seed are asked before the key is out.
  * EACH TABLE's SEED IS A FUNCTION OF ITS OWN ROOT, THE PUBLIC LETTERS AND THE ORACLE ALONE. It
    reads nothing of another table's answers or randomness. A scheme in which a seed hung on what
    was published of an earlier table, or in which a table were made after something was shown,
    would be another scheme, and would want more of the interactive protocol than is asked here.
  * ONE SEED A TABLE. Of two OOD samples on one table's encoding randomness nothing is said.
  * The seeds are asked, by the committer and by the simulator alike; nothing is programmed there.
  * THE COINS ARE IDEAL: uniform and independent (CoinsFit). Coins derived from a short key by a
    pseudo-random function are not covered.
  * ONE REQUEST A PROOF. Other clients' requests in one batch are not covered.
  * THE PROVER HAS NO STATE and draws its copy at random; the simulator counts, and stops a copy
    after s1 sessions; the price is ζ's first term, once.
  * ONE RUN OF THE COMMITTER.
  * A STOP OF THE HONEST SIDE IS A VALUE of the key or of a proof. Whether a run stops may hang on
    the index; that is paid by a term of ζ of its own (STOPS: hT, hL, hO), not inside zT, zL, zO.
    There is no premise "no stop".

WHAT MUST GO WITH ANY QUOTE OF IT.
  * IT IS A CONDITIONAL STATEMENT AT LETTERS. This file does not prove it; its proof is
    wholeKeyPrivacy, Johnson/WholeKey/Main.lean. Whether its premises hold at a given protocol is
    another matter.
  * THE RANGE ok, BY NAME. Nothing is said of an index outside it, and NO TERM OF ζ PAYS FOR IT: at
    a small range the premises are weak, ζ stays small and little is said. A quote says which range
    it is; that it holds two indices or more; and that every index with a true instance lies in it.
  * THE NUMBER OF ζ AT NAMED NUMBERS t OF QUERIES AND n OF REQUESTS. ζ + ζ < 1 IS WHERE THE
    STATEMENT BEGINS TO SPEAK, NOT WHERE IT HIDES. What follows of two real experiments: at two
    indices OF THE RANGE with the same public parameters, under ONE environment that is valid at
    both, the real views are within ζ + ζ (real_real, Johnson/WholeKey/Half.lean). An error
    "below 1" does not shut out a prover that sends a one-bit index in the clear; nor (argued, not
    typed) does ζ + ζ < 1 by itself, if that prover now and then hands no string (the head of
    Johnson/WholeKey/Half.lean). A quote gives the number, not "passes the bar".
  * COMPLETENESS OF THE SAME HONEST SIDES must stand beside it, WITH ITS NUMBER: "below 1" is no bar
    for it either (the head of Johnson/WholeKey/Bundle.lean).
  * IDEAL COINS, TYPED ORACLES, NO PROGRAM.
  * THE PREMISES ON THE SIMULATORS ARE ASKED EXACTLY AND POINTWISE: equality of laws, at every value
    of the encoding's randomness and every seed of Gs, but for a set of verifier messages.
  * THE GROUND. The scheme's own compiled prover (the chain, the searches, the trees, the coins) is
    defined in the files of OnBytes/Prover/ and Johnson/Prover/:
    what argW's prover IS, is decided there.
  * A BOUNDED NUMBER OF SESSIONS A KEY. ζ is 1 or more for n > (M + 1) · s1, and its first term is
    large long before.
  * ONE REQUEST A PROOF (batches of at most one slot). It bears weight: by a reading of the two
    texts (not proved in Lean), at batches of two the statement with this simulator is FALSE: at a
    batch of two with one slot of the adversary's own the real prover hands a notice, and the
    simulator, which is told of that one slot alone, a string. Nothing is said of what the client of
    one request learns of a batch's other requests, not even of their number. Batches of two or more
    are not covered; a statement on them is no corollary of this one.
  * NO WITNESS: the relation's witnesses are of the type with one member.
  * Gs IS A PUBLIC LETTER, bound before the relation, i₀ and the index. The statement says nothing
    unless (M + 2) · δ < 1; at the empty set δ is 1 or more and all premises on hiding are idle.
  * NOTHING IS ASKED ON THE SIMULATOR's WORK: it decides membership in Gs by the law of the excluded
    middle, and the interactive protocols' simulators are any families of laws.
  * IN THIS FOLDER NO BOUND ON ζ AT ANY SIZES but two toys', where all seven error letters (δ among
    them) are 0 and Gs is all seeds: so of ζ's terms those for the simulators' errors, for the stops
    and for the seeds are 0 there. At the full size (public files in scope), with placeholder
    provers and again the seven error letters 0, ζ at t queries and n ≤ s1 requests is at most a
    formula in t, n, the copies and the search limits (`zetaSmallC_description`, `boundZ`,
    E2E/ZetaAtCaps.lean).

WHAT IT DOES NOT SAY.
  * NOTHING OUTSIDE THE RANGE ok. An environment that names no instance is valid at every index, so
    the key alone must be simulated at every index of which the statement speaks. Outside the range
    nothing is concluded. ON THE RANGE ALONE are asked: that the simulators are good (Sims.Good),
    that the stops are rare (StopsSmall), that the run values stand in the plain parts (RunVals).
    AT EVERY INDEX are asked: that the honest sides speak of the encodings (ExtEnc), and the
    encoding's hiding (ReadsG). The simulator's fixed index i₀ need not lie in the range. The range
    is a letter: at the empty range, or at a range with one index, the statement is idle.
  * Nothing of any program. Committer and prover are Lean terms, tied to no program.
  * Nothing at a system whose verifier first reads its input off the hash function, and nothing over
    one hash function or on bytes: the oracles are typed, the input is fixed.
  * Nothing on what the public letters themselves tell of an index.
  * NOTHING OF A PROTOCOL UNLESS COMPLETENESS OF THE SAME HONEST SIDES, AT A SMALL ERROR, STANDS
    BESIDE IT. Index privacy alone is cheap: silent honest sides, which send fixed messages, meet
    the premises on provers with error 0 (proved: silent_good, Johnson/WholeKey/Foes.lean). What
    they are meant to fail is completeness. Johnson/WholeKey/Bundle.lean lays the clauses at ONE
    scheme; its head says what that guards and what not.
  * Nothing unless ζ is small: a bound of 1 or more is met by every scheme, and only where
    ζ + ζ < 1 does real_real (Johnson/WholeKey/Half.lean) say anything of two real views.
  * Nothing on how many queries committer and prover ask (their counts: Johnson/WholeKey/Work.lean).
    Caps and numbers of test bits are free letters: a prover that never reads the index and finds an
    accepted string by a long search is not shut out by bars on the three errors alone.
  * Whether the premises can be met at a given object is not said. At two toys they are met
    together: there ζ + ζ is at most 60/256 (about 0.23) at one query and one request, and at most
    about 0.50 at one query and three requests, so the second toy shows little
    (Johnson/WholeKey/Member.lean, Johnson/WholeKey/Member2.lean, Johnson/WholeKey/Main.lean).
    At Lean's form of the release's protocol they are met, for public files in scope, and within its
    bounds on the number of copies, the number of requests per copy and the sampled bits of a leaf's
    salt, with placeholders for two of the three provers, with the public files' digest set to
    zeros, where `verify` is not proved ever to be called (`premW_laid`, E2E/LinkLaidPrivacy.lean).
    Johnson/WholeKey/Foes.lean has tests that can fail.

Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Zeta
import Johnson.WholeKey.Wrap
import ZKCP.OnRange

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- **THE STATEMENT OF INDEX PRIVACY.** A theorem's type; not proved here. ok: the range of indices
of which it speaks. ZKCP.Gen.PrivacyOn (ZKCP/OnRange.lean): at every index of the range and every
environment that is valid there, the library's requirement for one index and one environment
(ZKCP.Gen.PrivacyFor, ZKCP/Gen.lean). -/
def Spec.wholeKeyPrivacy : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
    (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (p : Params) (a : AtRecs lam L Bd aT aL)
    (Sm : Sims L) (ok : I → Prop) (Gs : L.OutOfDomainSeed → Prop) (Ryes : I → X → Prop) (c : CoinNums Bd)
    (u : NumsW) (R : ZKCP.Gen.RelPair I X Unit Unit) (i₀ : I),
    (∀ i x w, R.yes i x w → Ryes i x) →
    PremW W S cA p a Sm ok Gs Ryes c u →
    ZKCP.Gen.PrivacyOn R (argW W S cA r₀ p a.side) 1
      (simWholeKey W S cA r₀ a.side Sm i₀ u.s1 Gs Unit) (zetaW W S p a c u) ok

/-- Where the range is all indices, the statement's conclusion is the library's property of index
privacy with the simulator named. -/
theorem privacyAll_of_wholeKeyPrivacy (h : Spec.wholeKeyPrivacy) (I X : Type) (lam : ℕ)
    (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape) (aL : RoundSplits L.link.shape)
    (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (p : Params) (a : AtRecs lam L Bd aT aL)
    (Sm : Sims L) (Gs : L.OutOfDomainSeed → Prop) (Ryes : I → X → Prop) (c : CoinNums Bd) (u : NumsW)
    (R : ZKCP.Gen.RelPair I X Unit Unit) (i₀ : I) (hR : ∀ i x w, R.yes i x w → Ryes i x)
    (hP : PremW W S cA p a Sm (fun _ => True) Gs Ryes c u) :
    ZKCP.Gen.HasIndexPrivacyWith R (argW W S cA r₀ p a.side) 1
      (simWholeKey W S cA r₀ a.side Sm i₀ u.s1 Gs Unit) (zetaW W S p a c u) :=
  fun i Z hZ =>
    h I X lam L Bd aT aL W S cA r₀ p a Sm (fun _ => True) Gs Ryes c u R i₀ hR hP i trivial Z hZ

end OnBytes.WholeKey

#print axioms OnBytes.WholeKey.privacyAll_of_wholeKeyPrivacy
