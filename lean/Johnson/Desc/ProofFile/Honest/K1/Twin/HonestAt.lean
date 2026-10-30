-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Twin/HonestAt.lean: FOR THE TWINS OF THE LIBRARY's ARMS (the kind
K1; "the committed cell is its stated function", behind the tie): WHAT THE TWINS CALL IN THE STEAD
OF THE LIBRARY's LAWS AT ITS WIDER MEANING (mw1, Johnson/Desc/K1/Law/K01FiftyR.lean): THREE
EQUATIONS ON ProofFile's "honest" OVER THE COMPOSED MEANING mgAll, AND FIVE CLOSED FACTS AT ITS TABLE OF
NAMES mgMore. TYPED BY HAND. Eleven theorems; no definition. PUBLIC DATA ALONE.
IT STANDS IN THE LIBRARY's NAMESPACE VerifiableInference.Desc.K1 (the twins do, so that a
copied proof finds its callees without a sign turned): the names are ours.

  - honest_more_closed: the table of names of honest (mgAll Dm Mg₀) ans test is mgMore, where Mg₀'s
    is empty: mgAll_more_closed (Johnson/Desc/Sound/MgAllAt.lean); honest leaves "more".
  - honest_pub_all: its public items' Bools are pubAll Dm.pubD Mg₀.pub: by rfl (mgAll_pub,
    Johnson/Desc/Sound/MgAll.lean).
  - honest_pubP_all: what its public items say beside their Bools: by rfl (mgAll_pubP): the right
    side is the field pubP of the library's FillsK1, to the letter.
  - tie_mw1_is, tie_honest_is: the item "tie" is one at the wider meaning, at the composed one and
    at honest over it: by rfl.
  - plainIn_mg, freshIn_mg, leftOpen342_mg, open342_mg: the library's plainIn_mw (ArmAtReads.lean),
    freshIn_mw (HeardAtReads.lean), leftOpen342 (ArmHeadBare.lean), open342 (ArmHeadPromise.lean)
    WITH mwMore TURNED TO mgMore AND NOT A SIGN ELSE: the names that the arms read off the promise
    are open at the reads' borders at the narrower table too. ownIn_mg: ownInB 25 (ArmAttIn.lean),
    written out, with the same turn. THE LIKE OF sentIn_mw LIES IN THE LIBRARY ALREADY: sentIn_mg
    (Johnson/Desc/AtSeats/FirstSeatedAtReads.lean): the twins call it. Evaluations in Lean's kernel.
    The library's own negative tests stand beside its own facts; at mgMore: leftOpen342_mg_fails.

This letter is for the honest run's own forms alone: no statement on any other party may take it.
NEVER ON SOUNDNESS's ROAD: at the meaning "honest" the
clauses noColl, shown and decodes are True by definition: a law at that meaning may stand beneath
statements on completeness or zero knowledge only, never beneath a statement on soundness.

Drift. If a sealed fact or law named above turns, its like here is typed anew by hand and held
against it anew.

Limits. THE FULL SIZE ALONE. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Thread.First
import Johnson.Desc.K1.Law.ArmAttIn
import Johnson.Desc.K1.Law.ArmHeadBare
import Johnson.Desc.K1.Law.HeardAtReads
import Johnson.Desc.K1.Law.HpubAtPlus13
import Johnson.Desc.Sound.MgBase
import Johnson.Desc.AtSeats.FirstSeatedAtReads
import Johnson.Desc.K1.Law.K01FiftyR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription Link Claim named)
open VerifiableInference.Desc.First (S AttOwn ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll mgBase d13 rowQ linkNo runsAt seatTab)
open VerifiableInference.Desc.K13.Law (openAt plus13)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.K9 (readerOf statesOfLink readersOfLink holesAt formsInT)
open VerifiableInference.Desc.First.Att.P (plannedK inOf seatCO parCOf firstK runsN runN find_first named_some)
open VerifiableInference.OnPublicFiles (headLink)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open Iop Run OnBytes.Maker OnBytes.Flat
open Cb Johnson.Pack
open ProofFile (Cl)
open VerifiableInference.Desc.Sound (mgMore mgAll_more_closed)
open VerifiableInference.Desc.First (pubAll)
open VerifiableInference.Desc (Strs Wit)
open ProofFile.Honest.FirstThread (honest)
open IM (k1Ix)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR XV) (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
  (ans : ℕ → ℕ → P × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop) (test : ℕ → S → Option String)

/-- The table of names. -/
theorem honest_more_closed (h : Mg₀.more = {}) : (honest (mgAll Dm Mg₀) ans test).more = mgMore :=
  mgAll_more_closed Dm Mg₀ h

variable {Dm Mg₀ ans test} in
/-- The public items' Bools. -/
theorem honest_pub_all : (honest (mgAll Dm Mg₀) ans test).pub = pubAll Dm.pubD Mg₀.pub := rfl

/-- **The wider meaning's tie is the composed meaning's.** -/
theorem tie_mw1_is (dk : K12Data) :
    (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀)).tie = (mgAll Dm Mg₀).tie := rfl

/-- honest leaves the tie. -/
theorem tie_honest_is : (honest (mgAll Dm Mg₀) ans test).tie = (mgAll Dm Mg₀).tie := rfl

/-- What the public items say beside their Bools. -/
theorem honest_pubP_all : (honest (mgAll Dm Mg₀) ans test).pubP =
    (First.Look.fillK3 XV Dm.sent (First.FillP1.fillP1 Dm.d1 Dm.rw13 Dm.A1 Dm.cr1 Mg₀)).pubP := rfl

end

set_option maxRecDepth 1000000 in
theorem plainIn_mg : ((List.range 25).all fun l =>
    !((linksFull[l]?).getD .layers == .attention) ||
      openB mgMore linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2)
        (.more (some l) "K5.plain")) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem freshIn_mg : ((List.range 25).all fun l =>
    openB mgMore linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l false + 2)
      (.linkFresh l)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem ownIn_mg : ((List.range 25).all fun l =>
    !((linksFull[l]?).getD .layers == .attention) ||
      ((rowQ linksFull (flatPlacesOf linksFull true) (noL l false)).ins.contains (.formsT l 3 "own") &&
        (runsAt linksFull l 3 "own").contains (2, "first") &&
        openB mgMore linksFull (flatPlacesOf linksFull true) (noL l false)
          (.more (some l) "ledger.treesAre"))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem leftOpen342_mg :
    ((First.pubSets mgMore linksFull (flatPlacesOf linksFull true))[noL 24 false]?.getD []).contains
      (.leftOn 24) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem open342_mg :
    (openB mgMore linksFull (flatPlacesOf linksFull true) (noL 24 false) (.linkFresh 24) &&
      openB mgMore linksFull (flatPlacesOf linksFull true) (noL 24 false)
        (.more (some 24) "ledger.treesAre")) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The test can fail. -/
theorem leftOpen342_mg_fails :
    ((First.pubSets mgMore linksFull (flatPlacesOf linksFull true))[noL 24 false]?.getD []).contains
      (.leftOn 23) = false := by
  decide +kernel

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.honest_more_closed
#print axioms VerifiableInference.Desc.K1.honest_pub_all
#print axioms VerifiableInference.Desc.K1.tie_mw1_is
#print axioms VerifiableInference.Desc.K1.tie_honest_is
#print axioms VerifiableInference.Desc.K1.honest_pubP_all
#print axioms VerifiableInference.Desc.K1.plainIn_mg
#print axioms VerifiableInference.Desc.K1.freshIn_mg
#print axioms VerifiableInference.Desc.K1.ownIn_mg
#print axioms VerifiableInference.Desc.K1.leftOpen342_mg
#print axioms VerifiableInference.Desc.K1.open342_mg
#print axioms VerifiableInference.Desc.K1.leftOpen342_mg_fails
