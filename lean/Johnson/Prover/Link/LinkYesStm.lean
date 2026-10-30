-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/LinkYesStm.lean: the statement that the link verifier's decision accepts the
view of the explicit honest link prover, for every input that satisfies Meant, at the library's
full-size parameter set. Definitions only (namespace Johnson.Prover.Link).

The link, and where these files stand. The library's protocol structure (HolographicProtocol,
Hiop/RecInterface.lean) has three interactive protocols. test is the offline protocol on one encoded
index (the key file's). link is the protocol for the equality relation on two encoded indices: a
first encoding and a further one, the copy (lean/GLOSSARY.md, "link"). onlineBatch is a session on requests
(the proof file's). An index (HolographicProtocol's type I) is what a table encodes. The link's instance is the two
tables' out-of-domain (OOD) samples, each a seed with its answers. Its two input oracles are the two
encodings.
These files are about completeness. completeOn_last (Johnson/Goal/Conditions/HomeLast.lean) is a
reduction. It proves CompleteOn, that is completeness with error at most α on the domain CanServe,
for the argument system with the library's verify() and a prover side given by parameters. Its one
hypothesis is LastFits, a structure of thirteen clauses. The clause "honest" is HonFit
(Johnson/Prover/All/OfHonest.lean): fourteen fields on the three protocols' provers (values of the
library's structure Honest). For the link an explicit honest prover is defined (linkNext), and
HonFit's four fields on the link (extL, whL, accL, prL) are proved for it by linkFits_at
(Johnson/Goal/Conditions/LinkFitsAt.lean), under linkFits_at's conditions: the public files pass the
tests InScope and protocolDataWellFormed, the link's prover is that one, and no further challenges are excepted. At
homeR b Z the other ten fields are proved at placeholder provers only, with the probability bounds
pT, pL and pO equal to 1, so they say nothing (honest_idle, Johnson/Goal/Conditions/HomeIdle.lean;
see HomeLast.lean, limit 1).

What this file has. LinkYes t₀ is the following proposition. Take any instance rr, any pair of input
oracles y and any row polynomials M₀, M₁ of the two tables that satisfy Meant. Then, for every value
C of the prover's free parameters (LCoins, Johnson/Prover/Link/LinkAll.lean) and all verifier
challenges ρ, the link's decision (one of four conditions of the accept: common limit 1) accepts the
view of the explicit honest prover (linkNext, LinkAll.lean). No challenge is excepted and there is
no error term.
Row polynomials are, for each row of a table, the coefficients of its polynomial (tail, then
message). The decision is the one that the protocol description generates (linkDescriptionAt,
Johnson/Desc/Link/LinkDesc.lean), at the two table keys made of rr (keysOf). The view is viewOf
(Johnson/Prover/Link/LinkFrame.lean): the decision's input, not the library's disclosed view.
The number t₀ is the first stage's number of sampled positions: 97 at the full-size parameter set
(frPar; fr_sg, OnBytes/Slice/FullRecSz.lean). It is the field t of the sizes Sz.sg
(OnBytes/Slice/BatSem.lean). linkNext passes it to smAt and mu0 in round 2's two answers, and these
rounds go on into lT. There it is only handed on (smAt to atJ, atJ to memRow) or stands in a type,
as the index of the sizes S.sg t: no body computes with it (by inspection). mu0_atJ
(Johnson/Prover/Link/FrontMsg.lean) shows that the summands do not depend on it. The prover's stages
take their numbers from the plan.
Meant rr y M₀ M₁ has seven clauses. The answers of each OOD sample are the sample map's values, at
the sample's seed, on its table's rows (rec0, rec1). Each input oracle is the table of these rows'
code words (tab0, tab1). The two tables' message parts agree, in every row, at the entries of the
layout (same; SameOn, Cb/Ld/LdLinkWords.lean). Every word of an oracle's symbol is below the field's
prime (words). Every symbol has 2048 words (wide): the tables have 2 ^ 11 rows (frPar,
OnBytes/Slice/FullRecSz.lean). The sample map is recZ at 29 coordinates and one answer for each row
(OnBytes/Slice/RecordRead.lean): a row's message has 402,653,184 entries (frPar), fewer than 2 ^ 29.

The link files, in reading order (Johnson/Prover/Link/ and Johnson/Goal/Conditions/).
  LinkAll.lean   the explicit honest prover: linkAll, linkNext.
  LinkFrame.lean   from a next-message function to a strategy, its view, and AccLaw from the
      decision's accept.
  LinkJoinF.lean   link_yes : LinkYes 97.
  LinkAccept.lean   link_accLaw: the whole accept of the link protocol's verifier at that decision,
      at the challenges that pass all proof-of-work checks, under Meant and one further premise.
  LinkMeant.lean   meant_home: the seven clauses of Meant at the honest prover's input in homeR b Z.
  LinkAcceptHome.lean   link_accLaw_home: the whole accept of that same verifier at that input, at
      the same challenges, with no further condition.
  LinkDecAt.lean   dec_at_D: for public files that pass InScope and protocolDataWellFormed, the link decision
      inside dataAtFiles flashProveData Z is the decision above.
  LinkFitsAt.lean   linkFits_at: HonFit's four fields on the link, under the four conditions named
      above.
The chain. link_yes gives link_accLaw. meant_home and a fact on the encodings' positions prove
link_accLaw's two premises at homeR b Z (accept_met_home,
Johnson/Goal/Conditions/LinkAcceptMet.lean): that gives link_accLaw_home. link_yes, meant_home,
dec_at_D and two facts on the openings and the positions (full_full, carries_home:
Johnson/Goal/Conditions/LinkFitsPaid.lean) give linkFits_at.
homeR b Z (Johnson/Goal/Conditions/HomeAtWider.lean) is the compiler's input (InnerCompilerInput) at the
public files Z, at which LastFits asks HonFit; b : PublicFiles → ℕ is a parameter of it (see HomeLast.lean).
The first five clauses of Meant are five premises of front_holds
(Johnson/Prover/Link/FrontWhole.lean).

Common limits of the link files. Seven of the other eight heads point here by number.
1. The decision is one of four conditions of the interactive verifier's accept (skeletonOverBothExternalStrings.accept,
OnBytes/TypedOracleCompiler/Run/PlanQX.lean: the proof-of-work checks, the openings' counts, the stored symbols'
positions, the decision). So LinkYes by itself does not say that the verifier accepts.
2. Every statement on the accept speaks of the challenges that pass all proof-of-work checks. Why,
and where the failure of the proof-of-work search is counted: Johnson/Prover/Link/LinkAccept.lean,
limit 1.
3. link_yes, link_accLaw, link_accLaw_home and linkFits_at are at the full-size parameter set only
(dsFull, frP, frS).
4. These four hold for every value C of the prover's free parameters, and speak of no distribution
on C. For completeness that is the strongest form. A statement on hiding would need a distribution
on C; these files make none.

Limits of this file. Meant has no clause on the stored symbols' positions. The accept's third
condition therefore needs a further premise (see LinkAccept.lean).
M₀, M₁ and C are parameters. The seven clauses are all that is asked of M₀ and M₁, and nothing is
asked of C.
This file holds no proof.
Nothing on soundness. No distribution is put on the prover's free parameters or on the challenges.
Nothing on what any value that is sent discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.LinkAtFull
import Johnson.Prover.Link.FrontWhole
import Johnson.Prover.Link.AtD

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb Cb.Ood Iop _root_.Run
open VerifiableInference.Desc
open _root_.Desc.K15 (frP linkDescriptionAt linkDeclaredRounds linkRoundsMatchPlan)
open OnBytes.Flat (dsFull RecFull)
open _root_.Run.PQ (SgX)
open TypedOracleCompiler.Run.PQ (drawnSL uL)

/-- The words of one input oracle's symbol at position x (b picks the oracle). From 2 ^ a on: the
empty list. -/
def yCol (a : ℕ) (y : (twoExternalStrings (2 ^ a) SgX).Str) (b : Bool) (x : ℕ) : List UInt64 :=
  if h : x < 2 ^ a then ((twoExternalStrings (2 ^ a) SgX).rd y (if b then .inr ⟨x, h⟩ else .inl ⟨x, h⟩)).2 else []

/-- The two table keys made of the instance: each holds its OOD sample's seed and answers. The
second has item := 1. -/
def keysOf (rr : RecFull × RecFull) : TableKey × TableKey :=
  (keyOf (fun β : NZ => β.val) rr.1, { keyOf (fun β : NZ => β.val) rr.2 with item := 1 })

/-- The honest prover's input: the two tables' row polynomials, the two oracles' symbols by
position, and the two keys. -/
def linOf (rr : RecFull × RecFull) (y : (twoExternalStrings (2 ^ frS.P.T.a) SgX).Str)
    (M₀ M₁ : (Fin frS.P.v → Bool) → frS.Co → GE) : LIn frS :=
  ⟨M₀, M₁, yCol frS.P.T.a y, keysOf rr⟩

/-- The relation between the instance, the input oracles and the row polynomials: seven clauses. M₀
and M₁ are parameters: these clauses are all that is asked of them. -/
structure Meant (r : (frS.lkR (recZ frS.P.T.l 29 1)).X0)
    (y : (frS.lkR (recZ frS.P.T.l 29 1)).E0.Str)
    (M₀ M₁ : (frS.ixR (recZ frS.P.T.l 29 1)).Row → frS.Co → GE) : Prop where
  rec0 : ∀ ρ s, r.1.2 (ρ, s) =
    ∑ j, (recZ frS.P.T.l 29 1).mat r.1.1 s j * M₀ ρ ((frS.ixR (recZ frS.P.T.l 29 1)).pl j)
  rec1 : ∀ ρ s, r.2.2 (ρ, s) =
    ∑ j, (recZ frS.P.T.l 29 1).mat r.2.1 s j * M₁ ρ ((frS.ixR (recZ frS.P.T.l 29 1)).pl j)
  tab0 : (frS.lkR (recZ frS.P.T.l 29 1)).tab y.1 =
    fun ρ => (frS.ixR (recZ frS.P.T.l 29 1)).G.mulVec (M₀ ρ)
  tab1 : (frS.lkR (recZ frS.P.T.l 29 1)).tab y.2 =
    fun ρ => (frS.ixR (recZ frS.P.T.l 29 1)).G.mulVec (M₁ ρ)
  same : (frS.lwR (recZ frS.P.T.l 29 1)).SameOn ((frS.ixR (recZ frS.P.T.l 29 1)).view M₀)
    ((frS.ixR (recZ frS.P.T.l 29 1)).view M₁)
  /-- every word of an oracle's symbol is below the prime -/
  words : ∀ p, (((twoExternalStrings (2 ^ frS.P.T.a) SgX).rd y p).2.all (· < fieldPrimeWord)) = true
  /-- an oracle's symbol has 2048 words -/
  wide : ∀ (w : Bool) (x : ℕ) (h : x < 2 ^ frS.P.T.a),
    ((twoExternalStrings (2 ^ frS.P.T.a) SgX).rd y (if w then .inr ⟨x, h⟩ else .inl ⟨x, h⟩)).2.length = 2048

/-- **The statement.** For all rr, y, M₀, M₁ with Meant rr y M₀ M₁, all C : LCoins and all ρ, the
description's decision at keysOf rr returns true on viewOf at linkNext. Nothing is asked of C.
Statement only; proved at t₀ = 97 as link_yes in Johnson/Prover/Link/LinkJoinF.lean. -/
def LinkYes (t₀ : ℕ) : Prop :=
  ∀ (rr : RecFull × RecFull) (y : (twoExternalStrings (2 ^ frS.P.T.a) SgX).Str)
    (M₀ M₁ : (Fin frS.P.v → Bool) → frS.Co → GE), Meant rr y M₀ M₁ →
  ∀ (C : LCoins) (ρ : Rho (uL (ckP .two) dsFull)),
    (linkDescriptionAt frP (linkDeclaredRounds frP) (linkRoundsMatchPlan frP recordPlan)).run (keysOf rr)
      (viewOf dsFull frS.P.T.a frD.xs (linkNext frP frS t₀ (linOf rr y M₀ M₁) C) y
        (drawnSL (ckP .two) dsFull ρ)) = true

end Johnson.Prover.Link
