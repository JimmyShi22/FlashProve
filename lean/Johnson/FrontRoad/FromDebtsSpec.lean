-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/FromDebtsSpec.lean: an implication. No parameters are known at which its premises
hold together: it may apply to nothing. If a named list of conditions on the public files and on the
provers holds at every value of the public reading, and the further premises below hold, then an
argument system made for this purpose has index privacy and zero knowledge, both on the requests
that can be served. It is no statement about a description: the randomness, the sampler, the
committer and the prover of shownSystem are made anew for each public files Z.
Terms of this folder: Johnson/FrontRoad/Front.lean and Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
Spec.roadPrivate_of_debts: a statement only; proved as roadPrivate_of_debts in
Johnson/FrontRoad/FromDebts.lean. It is an implication and proves nothing of any prover. Below, d is
a value of the public reading: what the verifier first reads off the hash function.
Its premises.
  (1) The library's reader returns a table pp at the public files Z.
  (2) PremWDebts (E2E/BridgeDebts.lean) holds at every d, at the relation yesAt b Z hr
      (Johnson/Goal/Conditions/HomeServed.lean). PremWDebts is the named list of conditions from
      which premW_of_debts derives the premises PremW of index privacy. It has conditions on the
      public files, the relation, two numbers, the key file's prover, the sessions' prover, and
      lengths and run values. It is asked at the parameters of the pair (allZeroDigest, []), which are those
      of homeR b Z, with the honest party's settings taken at d. That is enough: PremW reads the
      data for out-of-domain seeds and the encoding of answers, which depend on d, and
      premW_told_of_debts (E2E/BridgeDebtsTold.lean) proves that what PremW asks of them at homeR b
      Z's own data holds at every d.
  (3) Every index given by weights lies in the range ok.
  (4) Bounds on the honest party's numbers that hold for every d. The number of copies is M + 1. The
      bounds on proof-of-work attempts are at most CT, CL, CB. At least 256 bits of a leaf's salt
      are sampled. NC and NP bound the committer's and the prover's queries to the typed oracles.
      One number bound + 1 is a multiple of coinsRange.
So the settings are those that the library's reader takes from the public files, and the description
is asked to be live at Z (the field live of PremWDebts).
Its conclusion is RoadPrivate (Johnson/FrontRoad/FromPremisesSpec.lean) at the family debtSides, for
the relation «the request can be served (CanServe at the settings read off pp) and its output is the
model's». It has three clauses. The first is ThreeOfId for frontId, the scheme that publishes the
commitment ID alone: index privacy with the explicit simulator, bounds on its hash queries, and that
its verifier is that of Ladder.lean, which holds by definition. The second is index privacy of
shownSystem read as a scheme. The third is ZeroKnowledgeOn shownSystem on these requests. For an
adversary with at most t queries and N requests, N ≤ s1, the error is at most boundZ (9 + CT + CL +
CB) M (t + 1) N + zT + hT + N · hO (boundZ, E2E/ZetaAtCaps.lean). zT, hT and hO are variables of the
premises: no value is known for them at any prover of the key file or of the sessions. Beyond s1
requests the bound is ⊤ and bounds nothing.

  debtSides   the family of honest parties, simulators and numbers over the values d.

What may depend on d, and what does not. The settings may depend on d: the parameters c of the laws
on coins, among them pre₀, the public start of a table's leaf salt (a prover whose tables' salts
begin with the digest that is read has that digest there; the enumeration of salts is made from pre₀
and ℓ by canon, E2E/BridgeCoins.lean), the rest R₀ (RestOf, E2E/BridgeAtRecs.lean), the test okV on
run values, the link's run value v₀, and startT, startL, startB, the prefixes of the leaf salts of
the three hashed runs. Of R₀ the honest party atRecsAll reads the decisions of two abort sets, b₀,
the bounds on attempts, the number of copies (held the same at every d by premise (4)), the maps nm
and rtail, and the filler of a leaf's salt. Its windows and enumerations are overwritten by canon,
and its fields over run values by restKey (E2E/BridgePremWKey.lean). By this statement's choice the
following do not depend on d: the three variables of which the sessions' prover is made (the rows G,
the prover of parts H and the book B of E2E/BridgeDebts.lean); the key file's description Fx, book
BT, prover HT and map shT; the run values val₂, val₃, run₂, run₃; the description's parameters Zp,
Np, cF; the three simulators; the number s1; the simulator's fixed index i₀; the error numbers zT,
hT, hO. The relation and the range ok cannot depend on d, because PremAll takes one of each. All of
them are bound before the weights. The sessions' simulator simZ has H among its arguments and does
not read it (simZ_any, E2E/BridgeExact.lean).

How it fits. It joins premW_told_of_debts, at one value of d at a time, with roadPrivate_of_premAll
(Johnson/FrontRoad/FromPremises.lean). Three of that theorem's premises come from tieOn_yesAt
(Johnson/FrontRoad/TieServed.lean), zetaLe_withErrors (Johnson/FrontRoad/ZetaErr.lean) and
familyLaws_home (Johnson/FrontRoad/AtHomeT.lean). What it adds is that the named list is enough for
the conclusion, and that the types of the theorems that it joins fit together. Its conclusion
contains ZeroKnowledgeOn, which could be read as a goal of the release. It counts as none.

Limits.
  No parameters are known at which its premises hold together, not even with a sessions' prover that
      sends no session's proof. The conditions on the key file's and the sessions' provers are
      proved of no prover. Whether the protocol's own prover of the sessions can be written as a
      family debtSides, at some parameters, is shown by no theorem of this library.
  No proof of the field rows of PremWDebts is known at the description of the release at the whole
      relation RyesZ Z; at the narrower relation of served requests that form is concluded, where
      the reader returns, under the head AtHonest and the row debts RowDebtsP, of which these two
      files give no value (owed_atDescription, Johnson/T3/OwedOfKinds.lean; at the prover read
      through, under four premises more: owed_of_base, Johnson/T3/OnlineThru.lean). That is no fault
      of the field's form: it lies in a lemma below it. The theorems that have the field as their
      conclusion (file_owed_rows_mute, Johnson/Desc/ProofFile/Honest/Thread/RowsMute.lean, and those
      built on it) have a hypothesis of which their authors say, by inspection: «unprovable by what
      the invariant says; that it is false is shown by nobody», at the description's own invariants
      (that folder's structures Thread, one for each chain). Its plain form fails at one small
      example, at that example's three invariants alone (said here without a theorem). A weaker form
      of it (DoorBehindS, Johnson/Desc/ProofFile/Honest/Thread/FileD.lean) stands in other theorems.
      At the description it is concluded under hypotheses and letters alone: the head HeadAtReturn;
      the threads' parts FirstThreadParts (the honest prover's script among them), IndexReaders,
      SharedThreadParts and LastThreadParts; the fields of ThreadFieldsP; and a run that ready
      returns (doorAtTheTerm, AtFullSide/Honest/ThreadsAtTheTerm.lean, side library, whose head
      says: "All of this holds for nothing where a field can't be met: the fields are hypotheses.").
      The side library gives these fields a value at the record's threads, at the runs tied to the
      base relation (`theHalf`, AtFullSide/E2E/ZeroKnowledgeFromWhatIsLeftAtRecord.lean); no
      statement ends in DoorBehindS there. These files are not among this file's imports. The field
      is asked at the whole relation RyesZ Z, which does not read yesAt.
  The premises PremW of index privacy do not make a prover useful. Wherever the twenty premises of
      index privacy are met, they are met too, at no larger error, by an honest side whose sessions'
      prover sends nothing; it has no completeness error below 1. That last clause holds for every
      relation that holds of some index and instance, at one request or more (said here without a
      theorem). At shownSystem the like holds of the premises of roadPrivate_of_premAll, under a
      parser that undoes the encoder at the form of a proof without a session's proof, and a request
      in the set whose output is the model's
      (said here without a theorem). By one application this holds at the like family over
      debtSides, which is not shown to be a debtSides
      (said here without a theorem). Of PremWDebts this is by inspection, not proved: its conditions
      bound the part of the sessions' abort set that may depend on the private input, and none
      bounds the public part, so none is seen to shut out a sessions' prover that always aborts
      publicly (E2E/BridgeDebts.lean, Limits). No prover that tells something of the weights is
      shown to fail these premises at these parameters.
  Satisfying every condition would not give zero knowledge of the Lean verifier's own system. Left
      beyond the conclusion: completeness of the same honest party; the description's own sampler,
      committer and prover (one sampler for all public files; no choice in the fields that run);
      batches; coins derived from a seed.
  It is on the requests that can be served. Whether a request can be served depends on the weights
      and is then not hidden (Ladder/Package.lean). At weights at which no request can be served the
      statement speaks of the commitment alone.
  Index privacy and completeness together, at the same honest party, need more than this list: that
      all three interactive verifiers accept outside sets of small measure, that the honest party's
      enumerations hold lists of the right lengths (SideFit), and that the parser undoes the
      encoder. No statement for both is made here. The form in which both would stand at one family
      is Spec.both_of_premises (Johnson/FrontRoad/FromPremisesBothSpec.lean). No named list like
      PremWDebts exists for its further premises.
  The premises ask that the link's and the sessions' simulators give exactly the honest output, for
      each list of the verifier's messages, outside the aborts that may depend on the private input:
      the link's two error numbers and the sessions' simulation error are fixed at 0 (indexPrivacyNumbers s1 zT 0
      0 hT 0 hO). A link's or sessions' simulator that is only statistically close does not satisfy
      them. Only the key file's simulator may differ from the honest output, on verifier messages of
      measure at most zT.
  At zT ≥ 1 every key file's prover satisfies keyGood, and the same holds of keyStops at hT ≥ 1 and
      of sessionStops at hO ≥ 1, because each bounds a probability. The bound is then 1 or more (at
      hO, for one request or more) and says nothing. A bound ζ says nothing until ζ + ζ < 1
      (Johnson/WholeKey/Half.lean).
  The bounds on attempts are variables. At small bounds hardly any proof is produced. The error
      bound does not show that: it has no term for a search that runs out.
  The premises admit every number ℓ of sampled bits from 256 up to the length of a leaf's salt. By
      inspection, not proved, a hashed run of the protocol publishes the first 256 bits of a leaf's
      salt. So where ℓ exceeds the salt's length less 256 the statement counts as sampled bits that
      the protocol publishes (Johnson/FrontRoad/LaidIdSpec.lean, Limits; E2E/ZetaAtCaps.lean).
  The field below of PremWDebts, at the relation yesAt, is a theorem (below_yesAt,
      Johnson/FrontRoad/FromDebts.lean); it is asked again inside the list. The field laid holds of
      some Zp, Np, cF wherever the field live holds (laid_of_live, E2E/TiedAtFiles.lean).
  The description's parameters Zp, Np, cF are tied to Z by the field laid alone. They are not named
      as functions of Z, so the conclusion's simulator is an explicit term in these three
      variables, not in Z alone.
  By inspection, not proved, four places are tight for whoever would prove the conditions. No
      out-of-domain seed can be set aside: in debtSides the set of seeds is every seed and the
      number δ is 0, though roadPrivate_of_premAll has room for both, so the conditions on the key
      file's and the sessions' provers are asked at every seed. The field rows asks its condition on
      the input at the relaxed relation RyesZ Z. It asks its conditions on runs at all coins. It
      asks that a part's masks are fresh at every state m of that part, with no condition on how m
      was reached.
  The key file's simulator sT is a variable that stands beside the variable range ok, and keyGood is
      asked at ok alone. At a range with one index sT could be made for that index. Premise (3) bars
      that as far as the weights give two or more indices.
  The type of forms, the parser and the encoder are variables of which nothing is asked: an encoder
      that throws the proof away satisfies the statement. The numbers b Z and bound are two
      variables that nothing ties.
  Every premise is asked at every d of the type, whether or not a hash function gives that d. One
      multiple of coinsRange, one NC and one NP are asked for all d. If the sizes of an honest
      party's lists grow with d without a bound, there are none.
  There is one run of the committer, one request per proof, and no further tokens. The public files,
      the weights and the environment are fixed before the hash function is sampled. What Z itself
      tells is outside what is hidden, and Z holds the file of scales, which for a fitted model are
      made from its weights.
  The other limits of E2E/BridgeDebts.lean, E2E/BridgeOwedLink.lean and E2E/BridgeDebtsTold.lean
      hold here, except three that this statement removes. Here the conditions do read d, through
      the settings. The step from a fixed pair to the scheme that reads d off the hash function is
      taken (roadPrivate_of_premAll). At least 256 bits of a leaf's salt are sampled. The limits of
      Johnson/FrontRoad/TieServed.lean on yesAt and of Johnson/FrontRoad/ZetaErrAtInput.lean on the
      bound hold here. Of Johnson/FrontRoad/FromPremisesSpec.lean and
      Johnson/FrontRoad/LaidIdSpec.lean, the limits on the simulator, the coins, batches, the counts
      of hash calls, shownSystem and the built description hold here. Their limits on placeholder
      provers, free settings, a free map from weights to indices, an arbitrary description, a
      description that is not live, the relation relTaken and a free relation Yes or set domain do
      not apply.
-/
import E2E.BridgeDebtsTold
import Johnson.FrontRoad.FromPremisesSpec
import Johnson.FrontRoad.LaidSides
import Johnson.FrontRoad.LaidIdSpec
import Johnson.Goal.Conditions.HomeServed

set_option autoImplicit false
set_option maxRecDepth 100000

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off here, so that no
statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open OnBytes.WholeKey OnBytes.Prover AtPublicFiles.Premises AtPublicFiles.ZetaAt AtPublicFiles.AtFiles AtPublicFiles.Bridge AtPublicFiles.Along
open AtPublicFiles.Committed
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes (TableKey)
open VerifiableInference.Desc (FileDescription)
open ProofFile.Honest (Prover ProverCoinCounts Sides)
open VerifierAndGoals (PublicFiles readFiles settingsOfRead)
open FlashProve (homeR homeT backB yesAt flashProveDescription allZeroDigest)
open OnBytes.LinkSim.AtHome (homeSim)
open P5J

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) nonemptyPadZ_fromDebtsSpec : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_fromDebtsSpec {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

section Letters
variable (b : PublicFiles → ℕ) (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF :
                        VerifiableInference.Desc.Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)
  (Fx : FileDescription KeyInst) {TrT X₀T XT Q₂ Q₃ : Type} (BT : ProverCoinCounts) [Fintype Q₂] [Nonempty Q₂]
  [Fintype Q₃] [Inhabited Q₃]
  (HT : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst TableKey TrT X₀T XT)
  (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray) (shT : TableKey → Fx.S₂)
  (c : (homeT b Z).D → CoinNums (List Bool))
  (R₀ : (homeT b Z).D → RestOf 256 (List Bool) (filesAt Z).annT (filesAt Z).annL
    (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z))
  (okV : (homeT b Z).D → ByteArray × ByteArray → Prop)
  (v₀ : (homeT b Z).D → ByteArray × ByteArray)
  (startT startL startB :
    (homeT b Z).D → ByteArray × ByteArray → ℕ → Bool → Rom.Bits → Rom.Bits)
  (sT : AtPublicFiles.KeyBridge.SimT (homeR b Z).protocol) (s1 : ℕ) (zT hT hO : ℝ≥0∞) (i₀ : (homeR b Z).Index)

/-- The family of honest parties, simulators and numbers over the values d of the public reading.
The honest party at d has the key file's prover offlineProverWithEncodedTable, the link's prover and the sessions' family
famG, at the settings c d, R₀ d, okV d, v₀ d and the three prefixes at d, all at the pair (allZeroDigest,
[]). The simulators, the set of seeds (every seed), the numbers of the premises (u) and the
simulator's fixed index do not depend on d. -/
def debtSides : SidesAt (homeT b Z) where
  a := fun d => atRecsAll allZeroDigest [] b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT (c d) (R₀ d)
    (okV d) (v₀ d) (startT d) (startL d) (startB d)
  Sm := fun _ => ⟨sT, homeSim Z, fun n a ρ ans =>
    (simZ Z Zp Np cF run₂ run₃ B G H n (LPFD.Full.instanceAsPlainRecord a) ρ ans).map (Option.map (viewRe
                     LPFD.Full.instanceAsPlainRecord _))⟩
  Gs := fun _ _ => True
  c := c
  u := fun _ => indexPrivacyNumbers s1 zT 0 0 hT 0 hO
  i₀ := fun _ => i₀

end Letters

/-- An implication. No parameters are known at which its premises hold together: it may apply to
nothing. Statement only; proved as roadPrivate_of_debts in Johnson/FrontRoad/FromDebts.lean. If the
library's reader returns a table at Z, the conditions PremWDebts hold at every value d of the public
reading at the relation yesAt, every index given by weights lies in the range ok, and the honest
party's numbers are bounded uniformly in d, then the three clauses of RoadPrivate hold at debtSides,
on the requests that can be served. -/
def Spec.roadPrivate_of_debts : Prop :=
  ∀ (b : PublicFiles → ℕ) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl) (R₂ R₃ : Type) [Fintype R₂]
      [Nonempty R₂]
    [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray)
    (Tr X₀ Xh : Type) (B : ProverCoinCounts) (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
    (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh) (Fx : FileDescription KeyInst)
    (TrT X₀T XT Q₂ Q₃ : Type) (BT : ProverCoinCounts) [Fintype Q₂] [Nonempty Q₂] [Fintype Q₃] [Inhabited Q₃]
    (HT : Prover (Cz Z).I ((Cz Z).Pad × (Cz Z).Rnd) KeyInst TableKey TrT X₀T XT)
    (val₂ : Q₂ → ByteArray) (val₃ : Q₃ → ByteArray) (shT : TableKey → Fx.S₂)
    (c : (homeT b Z).D → CoinNums (List Bool))
    (R₀ : (homeT b Z).D → RestOf 256 (List Bool) (filesAt Z).annT (filesAt Z).annL
      (offlineProverWithEncodedTable Z Fx BT HT val₂ val₃ shT) (linkProverAtFiles b Z))
    (okV : (homeT b Z).D → ByteArray × ByteArray → Prop)
    (v₀ : (homeT b Z).D → ByteArray × ByteArray)
    (startT startL startB :
      (homeT b Z).D → ByteArray × ByteArray → ℕ → Bool → Rom.Bits → Rom.Bits)
    (sT : AtPublicFiles.KeyBridge.SimT (homeR b Z).protocol) (s1 : ℕ) (zT hT hO : ℝ≥0∞) (i₀ : (homeR b Z).Index)
    (ok : (homeR b Z).Index → Prop) (x₀ : (homeR b Z).Instance) (Form : Type)
    (parse : VerifierAndGoals.Parser (flashProveDescription.reBound b) Z Form)
    (encF : VerifierAndGoals.TypedProof ((flashProveDescription.reBound b).F Z) ((flashProveDescription.reBound b).P Z) → Form)
    (M CT CL CB NC NP bound : ℕ),
    (∀ d, PremWDebts allZeroDigest [] b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT (c d) (R₀ d)
      (okV d) (v₀ d) (startT d) (startL d) (startB d) (yesAt b Z hr) ok sT s1 zT hT hO) →
    (∀ w, ok (backB b Z (settingsOfRead pp) w)) →
    (∀ d, ((debtSides b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT startL
      startB sT s1 zT hT hO i₀).a d).M = M) →
    (∀ d i, ((debtSides b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
      startL startB sT s1 zT hT hO i₀).a d).capT i ≤ CT) →
    (∀ d i, ((debtSides b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
      startL startB sT s1 zT hT hO i₀).a d).capL i ≤ CL) →
    (∀ d i, ((debtSides b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT
      startL startB sT s1 zT hT hO i₀).a d).capB i ≤ CB) →
    (∀ d, 256 ≤ (c d).ℓ) →
    (∀ d, commitN (homeR b Z).queryLayout ((debtSides b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c
                R₀ okV v₀ startT startL startB sT s1 zT hT hO i₀).side d) ≤ NC) →
    (∀ d, proveN (homeR b Z).queryLayout ((debtSides b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀
                okV v₀ startT startL startB sT s1 zT hT hO i₀).side d) ≤ NP) →
    (∀ d, coinsRange ((debtSides b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀
      startT startL startB sT s1 zT hT hO i₀).side d) ∣ bound + 1) →
    RoadPrivate (flashProveDescription.reBound b) Z allZeroDigest [] (homeT b Z)
      (debtSides b Z Zp Np cF run₂ run₃ B G H Fx BT HT val₂ val₃ shT c R₀ okV v₀ startT startL
        startB sT s1 zT hT hO i₀)
      (settingsOfRead pp) (backB b Z (settingsOfRead pp)) x₀ (backTok b Z) Form parse encF
      (CanServe (settingsOfRead pp)) bound (8 + NC * ((homeR b Z).queryLayout.K + 1) + 1)
      (NP * ((homeR b Z).queryLayout.K + 1))
      (upTo s1 fun t n => boundZ (9 + CT + CL + CB) M t n + (zT + hT + (n : ℝ≥0∞) * hO))

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_fromDebtsSpec
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_fromDebtsSpec
#print axioms OnBytes.FrontRoad.debtSides
#print axioms OnBytes.FrontRoad.Spec.roadPrivate_of_debts
