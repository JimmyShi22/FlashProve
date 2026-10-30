-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmTopTests.lean: the tie's three hypotheses for the entry file at the three files' own
object and wiring (`entryPart_topFull`, `entryPart_topSmall`, Johnson/Top/ArmTopFull.lean,
Johnson/Top/ArmTopSmall.lean), with the hypothesis on the number of blocks replaced by two tests
that can be run.

The two theorems ask that the one wiring's number of blocks, and one, is below 2 ^ 48. By
Johnson/Flat/BlocksAt.lean that holds just if no round of the key file's data and no round of the
proof file's data draws too many blocks (`KFullAt_lt_iff`), which `blocksFitB`
(OnBytes/Flat/BlocksBelow.lean) tests on the data of the dry runs. Here the tests stand in the
hypothesis's place.

Main theorems: `entryPart_topFull_tests`, `entryPart_topFull_at_tests`; the like at the small size.

Not claimed. That the two tests say yes at any G: at a G made of the planner's answer at given
public files they are two values of Bool, which an evaluation can give and no theorem here does. The
tests are this library's own, no tests of the programs. Where the makers' tests on a dry run fail,
that file's data are empty lists and its test here says yes for nothing. All that the heads of
Johnson/Top/ArmTopFull.lean and Johnson/Top/ArmTopSmall.lean do not claim. For proofs only; no
program imports this file.


-/
import Johnson.Top.ArmTopFull
import Johnson.Top.ArmTopSmall
import Johnson.Flat.BlocksAt

set_option autoImplicit false
set_option maxRecDepth 40000

noncomputable section

namespace OnBytes.K.Arm
open OnBytes.Flat OnBytes.Slice OnBytes.Tie Hiop Cb Cb.Ood OnBytes.K OnBytes.K.Left
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open VerifiableInference.OnPublicFiles
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X) (E : Coding A) (G : FilesParameters X RecFull)
  (P : (threeProtocolsFromDryRunAtFullSize A (Flat.relationsAndEncodingOfClaims A E) G).Provers) (Z : Pub) (sX : Ser X)
  (num : ℕ → Plains (restFullAt A E G P).bat.loc.shape → Bool)

/-- **The tie's three hypotheses for the entry file, at the three files' own object and wiring**,
with two tests that can be run in the place of the bound on the number of blocks. -/
theorem entryPart_topFull_tests (hZ : recordGround.SaysLines Z.pol)
    (hK : blocksFitB .two (dataKFull G) = true) (hP : blocksFitB .two (dataPFull G) = true) :
    EntryPart (armTopFull A E G P Z sX num).shape (readTopFull A E G P Z sX num) :=
  entryPart_topFull A E G P Z sX num hZ (KFullAt_lt_of_tests G hK hP)

/-- The same at every Z whose parameter file begins with the example's 32 lines. -/
theorem entryPart_topFull_at_tests (more lay KL : ByteArray)
    (hK : blocksFitB .two (dataKFull G) = true) (hP : blocksFitB .two (dataPFull G) = true) :
    EntryPart
      (armTopFull A E G P ⟨TestSaysLines.bytesOf TestSaysLines.full32 ++ more, lay, KL⟩ sX
        num).shape
      (readTopFull A E G P ⟨TestSaysLines.bytesOf TestSaysLines.full32 ++ more, lay, KL⟩ sX
        num) :=
  entryPart_topFull_at A E G P sX num more lay KL (KFullAt_lt_of_tests G hK hP)

end

section
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X) (E : Coding A) (G : FilesParameters X RecSmall)
  (P : (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).Provers) (Z : Pub) (sX : Ser X)
  (num : ℕ → Plains (restSmallAt A E G P).bat.loc.shape → Bool)

/-- **The tie's three hypotheses for the entry file, at the three files' own object and wiring**,
with two tests that can be run in the place of the bound on the number of blocks. -/
theorem entryPart_topSmall_tests (hZ : smallRecordGround.SaysLines Z.pol)
    (hK : blocksFitB .two (dataKSmall G) = true) (hP : blocksFitB .two (dataPSmall G) = true) :
    EntryPart (armTopSmall A E G P Z sX num).shape (readTopSmall A E G P Z sX num) :=
  entryPart_topSmall A E G P Z sX num hZ (KSmallAt_lt_of_tests G hK hP)

/-- The same at every Z whose parameter file begins with the example's 32 lines. -/
theorem entryPart_topSmall_at_tests (more lay KL : ByteArray)
    (hK : blocksFitB .two (dataKSmall G) = true) (hP : blocksFitB .two (dataPSmall G) = true) :
    EntryPart
      (armTopSmall A E G P ⟨TestSaysLines.bytesOf TestSaysLines.small32 ++ more, lay, KL⟩ sX
        num).shape
      (readTopSmall A E G P ⟨TestSaysLines.bytesOf TestSaysLines.small32 ++ more, lay, KL⟩ sX
        num) :=
  entryPart_topSmall_at A E G P sX num more lay KL (KSmallAt_lt_of_tests G hK hP)

end

end OnBytes.K.Arm
