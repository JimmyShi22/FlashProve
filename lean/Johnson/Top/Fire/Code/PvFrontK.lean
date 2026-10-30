-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/PvFrontK.lean


-/
import Johnson.Top.ArmsAtFiles
import Johnson.Top.ArmsAtFilesSmall
import OnBytes.Flat.WireBlocks
/-! THREE LETTERS OF DvOf: K · r₀ · num. Definitions alone. -/
set_option autoImplicit false
namespace PV.Front
open OnBytes OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.K.ArmsAtFiles
open VerifiableInference VerifiableInference.OnPublicFiles

/-- K: kThree (OnBytes/Flat/WireBlocks.lean) at the two whole files' data and at the
  rounds
of the entry's description (srD.ds | frD.ds: with code; srD.ds = srRds is sr_ds_C, frD.ds
  =
frRds fr_ds_C). A function of the data alone: of no digest. -/
def KSmall (DK DP : WholeD) : ℕ := kThree .two DK srD.ds DP
def KFull (DK DP : WholeD) : ℕ := kThree .two DK frD.ds DP

/-- r₀: the record of zeros: (bigZSmall Z).rec₀ | (bigZFull Z).rec₀ at every Z. Any record serves,
  if the
same one stands in the coding's test "is r₀". -/
def r0Small : RecSmall := recZeroSmall
def r0Full : RecFull := recZeroFull

/-- num: NO TEST. (Johnson/TypedOracleCompiler/RecCompile/Cms.lean:61: "a letter under no law: no proof leans on its
test, which can only make VC refuse".) General in the type of plain parts. -/
def numNoTest {α : Type} : ℕ → α → Bool := fun _ _ => true

end PV.Front
