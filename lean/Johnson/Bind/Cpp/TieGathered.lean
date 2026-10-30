-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/TieGathered.lean: THE STEP BEFORE Johnson/Bind/Cpp/TheTie.lean: the parts of the
tie between the written committer and the running committer (TieAt, TieKeyAt:
Johnson/Bind/Cpp/Defs.lean), gathered, and the headline forms that follow from it, UNDER TWO
EQUATIONS ON TYPED QUERIES AS HYPOTHESES (OwedAt: the leaf's and the OOD seed's, of the five of
Johnson/Bind/Cpp/Spells.lean), which this file does not prove: they are proved in
Johnson/Bind/Spell/Leaf.lean (where the frame's salts have 40 bytes) and
Johnson/Bind/Spell/Seed.lean, and laid in by Johnson/Bind/Cpp/TheTie.lean. Every proof here is a
call of theorems of other files.
NOTHING HERE SAYS THAT A COMMITMENT OF THE RELEASE'S COMMITTING PROGRAM CAN BE OPENED ONLY TO THE
EXTRACTOR'S WEIGHTS, OR THAT THE EXTRACTOR GIVES THE WEIGHTS THAT THE PROGRAM COMMITTED TO.
"The opening form" is BindsWith (VerifiableInference/MoreStatements.lean): nobody opens a
commitment, by naming weights and randomness from which the committer gives it, to weights that the
extractor does not give; at fixed randomness it yields that the extractor gives the committed
weights back (BindsWith.atRandomness).

Why. The tie's proof is cut into parts that are proved apart. Paid, and called here:
  the joint       join_at, tieCells_of_seven (Johnson/Bind/Cpp/Join.lean);
  three of five   spellsC, spellsNode, spellsId: the told part is the files' digest; a vertex's
                  typed answer is the format's vertex hash; the answer at a key's code is the
                  format's commitment ID (Johnson/Bind/Cpp/SpellsC.lean, SpellsNode.lean,
                  SpellsId.lean);
  the encoder     columnIs: the written encoder's symbols are the running committer's columns
                  (Johnson/Bind/Cpp/ColumnAt.lean);
  the answers     answersAre: the written OOD answers, spelled, are the running committer's
                  (Johnson/Bind/Cpp/AnswersAre.lean);
  the digits      entryIs: the running text of the table's entries is what the library's matrix of
                  digits spells (ColumnAt.lean); tieAt_of_cells (Johnson/Bind/Cpp/OfTie.lean);
  the frame       saltAt_of_live: in scope, where the tests on the public files pass (protocolDataWellFormed), the
                  frame's salts have 40 bytes (Johnson/Bind/Cpp/SaltAt.lean);
  the count       count_theTwin (Johnson/Bind/Cpp/AtTwin.lean);
  the forms       extractsCommitted_cpp (Johnson/Bind/Cpp/Extracts.lean), bindsAtZ_cpp (OfTie.lean):
                  from the tie and the count to the two headline forms. Every probability in them is
                  the written committer's own theorem's (bindsWith_plain_law,
                  Johnson/Goal/Conditions/BindsTold.lean): the tie carries it over, by equal values
                  at every hash function.

Main names (namespace Bind.Cpp).
  OwedAt Z: the hypothesis: at every hash function SpellsLeaf and SpellsSeed at Z. In scope it can
    hold only where the frame's salts have 40 bytes (argued).
  spells_of_owed: with the three that are paid, the five.
  tieKeyAt_of_owed, tieAt_of_owed: the tie at the key and at the ID, at a Z whose frame has salts of
    40 bytes.
  extractsCommitted_of_owed: correctness of extraction (ExtractsCommittedWeights,
    VerifiableInference/MoreStatements.lean) for the committer of theCpp (theTwin g), UNDER
    OwedAt Z, at one Z in scope that is read and at which the verifier's tests on the public files
    pass (protocolDataWellFormed).
  bindsAt_of_owed: the body of G9bits (Ladder/Bits.lean) at such a Z, UNDER OwedAt Z: the opening
    form (BindsWith), at bindingErrorInQueries.
Limits. Those of Johnson/Bind/Cpp/AtLive.lean and OfTie.lean travel whole. That OwedAt Z holds is
not shown here: where the frame's salts have 40 bytes it is owedAt (Johnson/Bind/Cpp/TheTie.lean).
THAT THEY HAVE 40 BYTES AT ANY Z IS NO THEOREM OF THE MAIN LIBRARY WITHOUT A PREMISE; that protocolDataWellFormed
passes at any files is no theorem of that library. At the full-size shape. The generator g and the
prover are letters: no theorem reads what they are.
Terms: lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Bind.Cpp.Join
import Johnson.Bind.Cpp.SpellsNode
import Johnson.Bind.Cpp.SpellsId
import Johnson.Bind.Cpp.ColumnAt
import Johnson.Bind.Cpp.AnswersAre
import Johnson.Bind.Cpp.AtLive

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

open scoped ENNReal

noncomputable section

namespace Bind.Cpp
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open Bind.Twin (Shape Table)

/- Lean compares these by their names. -/
attribute [local irreducible] Bind.Twin.twinID Bind.Twin.calls shapeFull twinBudget theTwin
  theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate theProofGate theLinkGate
  theProvers theNamed LPFD.Full.GF riDigits fieldRows descriptionOfDataOnBytes T₀ FlashProve.thePlan
  FlashProve.theItem LayoutsByPublicReading.commitAtCoins

/-- **What this file takes as a hypothesis of the tie at Z**: at every hash function the equations
on a leaf's query and on the OOD seed's two queries. This file does not prove it. The leaf's
equation speaks of salts of 40 bytes: where the planner rejects the files and the frame's salts have
no bytes it is false (argued, no theorem). So in scope OwedAt Z can hold only where SaltAt Z holds.
-/
def OwedAt (Z : PublicFiles) : Prop := ∀ hash : Hash, SpellsLeaf Z hash ∧ SpellsSeed Z hash

/-- With the three that are paid, the five. -/
theorem spells_of_owed {Z : PublicFiles} (h : OwedAt Z) (hash : Hash) : Spells Z hash :=
  ⟨spellsC Z hash, (h hash).1, spellsNode Z hash, (h hash).2, spellsId Z hash⟩

/-- **The tie at the key, under OwedAt Z**, where the frame's salts have 40 bytes. -/
theorem tieKeyAt_of_owed (Z : PublicFiles) (hs : SaltAt Z) (h : OwedAt Z) : TieKeyAt Z :=
  join_at Z hs (spells_of_owed h) (columnIs Z) (answersAre Z)

/-- **The tie, under OwedAt Z**, where the frame's salts have 40 bytes, at the running committer
of Johnson/Bind/Twin.lean (Bind.Twin.twinID). The statement does not read the generator g. -/
theorem tieAt_of_owed (Z : PublicFiles) (hs : SaltAt Z) (h : OwedAt Z)
    (g : Shape → Seed → Digest → Digest → Coins) : TieAt (theTwin g) Z :=
  tieAt_of_cells (theTwin g) Z entryIs
    (tieCells_of_seven Z hs (spells_of_owed h) (columnIs Z) (answersAre Z) g)

variable (prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm flashProveDescription.Form)

/-- **Correctness of extraction for the committer of theCpp (theTwin g), UNDER OwedAt Z AS A
HYPOTHESIS**, at one Z in scope that is read and at which protocolDataWellFormed passes. The generator is a letter:
no theorem reads what it is. No theorem of the main library says that protocolDataWellFormed passes at any files.
The error, bindingErrorInQueries (2^35 + 2), is about 2^-89. -/
theorem extractsCommitted_of_owed (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hs : InScope Z = true) (hr : readFiles Z = .ok pp)
    (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) (h : OwedAt Z) :
    ExtractsCommittedWeights
      (systemOfRecord (atSecondHashFunction (theCpp (theTwin g) prove)) Z (settingsOfRead pp))
      ((atSecondHashFunction (theCpp (theTwin g) prove)).extractor Z (settingsOfRead pp))
      (bindingErrorInQueries (twinBudget + 2)) :=
  extractsCommitted_cpp (theTwin g) prove Z pp hr
    (tieAt_of_owed Z (saltAt_of_live hs hl) h g) (count_theTwin g Z)

/-- **The body of G9bits, UNDER OwedAt Z AS A HYPOTHESIS**, at one such Z. The generator is a
letter. The files are fewer than the goal's ("in scope, read"): this is not G9bits. -/
theorem bindsAt_of_owed (g : Shape → Seed → Digest → Digest → Coins) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (hs : InScope Z = true) (hr : readFiles Z = .ok pp)
    (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) (h : OwedAt Z) :
    (∀ w ρ, ((atSecondHashFunction (theCpp (theTwin g) prove)).commit Z (settingsOfRead pp) w
        ρ).toRandomized.QueryBound honestBudget) ∧
      BindsWith (systemOfRecord (atSecondHashFunction (theCpp (theTwin g) prove)) Z (settingsOfRead pp))
        ((atSecondHashFunction (theCpp (theTwin g) prove)).extractor Z (settingsOfRead pp)) bindingErrorInQueries :=
  bindsAtZ_cpp (theTwin g) prove Z pp hr
    (tieAt_of_owed Z (saltAt_of_live hs hl) h g) (count_theTwin g Z)

end Bind.Cpp

end

#print axioms Bind.Cpp.spells_of_owed
#print axioms Bind.Cpp.tieKeyAt_of_owed
#print axioms Bind.Cpp.tieAt_of_owed
#print axioms Bind.Cpp.extractsCommitted_of_owed
#print axioms Bind.Cpp.bindsAt_of_owed
