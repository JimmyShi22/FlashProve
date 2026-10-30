-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ladder/Guards.lean: tests on the fixed terms of Ladder.lean and Ladder/Stored.lean. Lean's evaluator
runs them whenever this file is compiled. They are evaluations, not proofs checked by the kernel,
and they are no proof of `FilesRead`. An evaluation trusts Lean's evaluator and what Lean's compiler
makes of the definitions, the library's and Mathlib's, which no theorem ties to the kernel's reading
of them; the theorems of Ladder/Ties.lean trust neither.

The stored bytes: the three files' sizes; that `zGap` differs from `storedPublicFiles` in the parameter file
alone; and the digest of each set of three files under the format's real hash function against a
stored value, so that a changed byte in any of them fails a test. A further test holds that digest
against the real hash function at the bytes that `configString` spells.
In scope: the stored files and the same with the policy (25856, 512, 1), each with the policy that
the reader returns; four further policies; some other value of MF, some other value of KF, four
further settings of eps1, eps2 and epsF, one of them above 2^32 and one at 2^48 - 1; and a scale
file in whose records the thirteen numbers differ from one another. Out of scope: three empty files;
an empty layout file; an empty scale file; one line changed among the first 32 (two cases) or after
them (eleven cases, among them theta0, cs, wb_emb, a table's digest); one line more at the end; a
policy with theta below 2^8 (two cases), with C = 2^32, with theta above C, with cap above 1,024; a
free number written with a leading zero (two cases) or a sign; a free number that the reader refuses
(three cases); a scale file with a number that the reader refuses.
-/
import Ladder

namespace VerifierAndGoals

/-- The policy that the reader returns, as (C, theta, cap). -/
def policyRead (Z : PublicFiles) : Option (Nat × Nat × Nat) :=
  match readFiles Z with
  | .ok pp => some (pp.pol.C, pp.pol.theta, pp.pol.cap)
  | .error _ => none

/-- The 152 lines after the first 32, as the stored example has them. -/
def behindText : String :=
  behindA1 ++ "eps1_lo 53687\neps1_hi 0\neps2_lo 53687\neps2_hi 0\n" ++ behindA2 ++
    "MF 44\nKF 30\nepsF_lo 53687\nepsF_hi 0\n" ++ behindA3 ++ "C 256\ntheta 256\ncap 0\n" ++ behindB

/-- A scale file: for each of the 48 layers the twelve given numbers and the rotary flag of the
reference pattern; then 24 times the stored file's three numbers of a layer with experts. -/
def scaleFile (record : List Nat) : ByteArray :=
  OnBytes.Tie.Pv.Plan.wordsFile
    (((List.range 48).flatMap fun L => record ++ [if L % 4 = 3 then 0 else 1]) ++
      (List.range 24).flatMap fun _ => [17, 16, 20])

/-- The stored parameter file at another policy. -/
def atPolicy (C theta cap : Nat) : ByteArray :=
  policyFile { storedLines with C := C, theta := theta, cap := cap }

/-- The stored parameter file with one of its first 32 lines replaced. -/
def withLine (old new : String) : ByteArray :=
  OnBytes.Tie.Pv.Plan.textOf (lines32.map fun l => if l == old then new else l) ++ behindText.toUTF8

/-- The stored parameter file with one of the lines after the first 32 replaced. -/
def withLineBehind (old new : String) : ByteArray :=
  OnBytes.Tie.Pv.Plan.textOf lines32 ++
    (behindText.replace ("\n" ++ old ++ "\n") ("\n" ++ new ++ "\n")).toUTF8

#guard storedPublicFiles.pol.size == 2629 && storedPublicFiles.lay.size == 224975 && storedPublicFiles.KL.size == 2784
#guard zGap.pol.size == 2631 && zGap.pol != storedPublicFiles.pol
#guard zGap.lay == storedPublicFiles.lay && zGap.KL == storedPublicFiles.KL
#guard Fmt.configDigest [storedPublicFiles.pol, storedPublicFiles.lay, storedPublicFiles.KL] ==
  Fmt.unhex "cf8ebe88802355fc0921fbbd3cc6aa770d01579b5750d1a88ab2d50cd0a5b118"
#guard
  Fmt.oracle (Fmt.oStr 0 169 0 2 Fmt.zero32 (Fmt.configBytes [storedPublicFiles.pol, storedPublicFiles.lay, storedPublicFiles.KL])) ==
    Fmt.configDigest [storedPublicFiles.pol, storedPublicFiles.lay, storedPublicFiles.KL]
#guard Fmt.configDigest [zGap.pol, zGap.lay, zGap.KL] ==
  Fmt.unhex "0d8481554288897d81d52f6e17231e9bcc41f763e706e252fea61322f6004810"

#guard InScope storedPublicFiles && policyRead storedPublicFiles == some (256, 256, 0)
#guard InScope zGap && policyRead zGap == some (25856, 512, 1)
#guard OnBytes.Tie.Pv.Plan.textOf lines32 ++ behindText.toUTF8 == storedPublicFiles.pol
#guard InScope { storedPublicFiles with pol := atPolicy 2304 259 0 }
#guard InScope { storedPublicFiles with pol := atPolicy 256 256 1 }
#guard InScope { storedPublicFiles with pol := atPolicy 256 256 1024 }
#guard InScope { storedPublicFiles with pol := atPolicy (2 ^ 32 - 1) (2 ^ 32 - 1) 0 }

#guard (List.range 64).any fun M =>
  M != storedLines.MF && InScope { storedPublicFiles with pol := policyFile { storedLines with MF := M } }
#guard (List.range 64).any fun K =>
  K != storedLines.KF && InScope { storedPublicFiles with pol := policyFile { storedLines with KF := K } }
#guard InScope { storedPublicFiles with pol := policyFile { storedLines with eps1 := 53688 } }
#guard InScope { storedPublicFiles with pol := policyFile { storedLines with eps2 := 1, epsF := 2 } }
#guard InScope { storedPublicFiles with pol := policyFile { storedLines with eps1 := 2 ^ 32 + 5 } }
#guard InScope { storedPublicFiles with pol := policyFile { storedLines with epsF := 2 ^ 48 - 1 } }
#guard scaleFile [29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 8] == storedPublicFiles.KL
#guard InScope { storedPublicFiles with KL := scaleFile [29, 28, 17, 16, 15, 20, 19, 44, 30, 43, 31, 8] }

#guard !InScope ⟨ByteArray.empty, ByteArray.empty, ByteArray.empty⟩
#guard !InScope { storedPublicFiles with lay := ByteArray.empty }
#guard !InScope { storedPublicFiles with KL := ByteArray.empty }
#guard withLine "slots 64" "slots 1" != storedPublicFiles.pol
#guard !InScope { storedPublicFiles with pol := withLine "slots 64" "slots 1" }
#guard !InScope { storedPublicFiles with pol := withLine "work positions 20 28 32" "work positions 0 0 0" }
#guard withLineBehind "tau 128" "tau 64" != storedPublicFiles.pol
#guard !InScope { storedPublicFiles with pol := withLineBehind "tau 128" "tau 64" }
#guard !InScope { storedPublicFiles with pol := withLineBehind "tau 128" "tau 127" }
#guard !InScope { storedPublicFiles with pol := withLineBehind "nmin 20" "nmin 1" }
#guard !InScope { storedPublicFiles with pol := withLineBehind "D 2048" "D 1" }
#guard !InScope { storedPublicFiles with pol := withLineBehind "seed_lo 1" "seed_lo 2" }
#guard !InScope { storedPublicFiles with pol := withLineBehind "call FL FL F" "call FL FL F F" }
#guard !InScope { storedPublicFiles with pol := withLineBehind "s 15" "s 14" }
#guard !InScope { storedPublicFiles with pol := withLineBehind "theta0_lo 500000" "theta0_lo 500001" }
#guard !InScope { storedPublicFiles with pol := withLineBehind "cs 12" "cs 13" }
#guard !InScope { storedPublicFiles with pol := withLineBehind "wb_emb 21" "wb_emb 20" }
#guard !InScope { storedPublicFiles with pol := withLineBehind "tsilu0 2048398297" "tsilu0 2048398298" }
#guard !InScope { storedPublicFiles with pol := withLineBehind "MF 44" "MF 044" }
#guard !InScope { storedPublicFiles with pol := policyFile { storedLines with MF := 48 } }
#guard !InScope { storedPublicFiles with pol := policyFile { storedLines with eps2 := 0 } }
#guard !InScope { storedPublicFiles with pol := policyFile { storedLines with eps1 := 2 ^ 48 } }
#guard !InScope { storedPublicFiles with pol := withLineBehind "eps1_lo 53687" "eps1_lo +53687" }
#guard !InScope { storedPublicFiles with KL := scaleFile [29, 29, 17, 17, 16, 20, 19, 44, 30, 44, 30, 13] }
#guard !InScope { storedPublicFiles with pol := storedPublicFiles.pol ++ "x 1\n".toUTF8 }
#guard !InScope { storedPublicFiles with pol := atPolicy 256 255 0 }
#guard !InScope { storedPublicFiles with pol := atPolicy 256 0 0 }
#guard !InScope { storedPublicFiles with pol := atPolicy (2 ^ 32) 256 0 }
#guard !InScope { storedPublicFiles with pol := atPolicy 256 257 0 }
#guard !InScope { storedPublicFiles with pol := atPolicy 256 256 1025 }
#guard !InScope { storedPublicFiles with pol := withLineBehind "C 256" "C 0256" }

end VerifierAndGoals
