-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/PvFrontNum.lean

-/
import Johnson.TypedOracleCompiler.RecCompile.CmsAns
import OnBytes.TypedOracleCompiler.Joined.Queries
import Johnson.Flat.TwoSizes
/-! num: THE TEST OF THE STORED COPY's NUMBER,
  WITH CODE: the number that stands in the plain part of
the proof file's front round (FrontMsg.copy) is the proof's. The law's own test
at rd := FrontMsg.copy. -/
set_option autoImplicit false
namespace PV.Front
open OnBytes OnBytes.Flat OnBytes.Slice OnBytes.Maker VerifiableInference.OnPublicFiles
open _root_.Iop _root_.Compile.Joined

/-- General in the rounds behind the front and in the front's fixed message. -/
def numCopy {t : FrontMsg (List OnBytes.E)} {s : Shape} :
    ℕ → Plains (plainRound (FrontMsg (List OnBytes.E)) t :: s) → Bool :=
  fun k π => decide (π.1.copy = k)

section
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X) (E : Coding A) (G : FilesParameters X RecSmall)
  (P : (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).Provers)
/-- DOES IT TYPE AT THE OBJECT's OWN SHAPE, AT THE SMALL SIZE? -/
def numAtSmall : ℕ → Plains ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P).onlineBatch.loc.shape → Bool := numCopy
end
section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X) (E : Coding A) (G : FilesParameters X RecFull)
  (P : (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).Provers)
def numAtFull : ℕ → Plains ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P).onlineBatch.loc.shape → Bool := numCopy
end

end PV.Front
