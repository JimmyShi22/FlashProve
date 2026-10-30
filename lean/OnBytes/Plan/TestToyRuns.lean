-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Plan/TestToyRuns.lean: tests of OnBytes/Plan/ToyRuns.lean. They run when this file
compiles.

The four texts are the public files of the runs "product" and "links", each at full and at tiny
size, as the C++ tool blocks/toy/handover.cpp writes them. What is expected are the parameter bytes
that the tool writes beside them, by their length and digest. The tiny runs have the target 10, so
they are called with 10 bits asked, and are refused at the default. A text in another spelling is
refused.

No module of the program imports this file. It holds no theorem.
-/
import OnBytes.Plan.ToyRuns
import OnBytes.Hash.H

namespace OnBytes.Plan.TestToyRuns

/-- The public file of the run "product" at tiny size. -/
def tinyProduct : String :=
  "run product, tiny edition: a test size that reaches no security level\n" ++
  "format H821\n" ++
  "target 10\n" ++
  "work-on-positions 6\n" ++
  "salt-bytes 40\n" ++
  "nonce-bytes 8\n" ++
  "position-bytes 0\n" ++
  "samples 1\n" ++
  "log-length 4\n" ++
  "log-n 7\n" ++
  "mask-log-n 7\n" ++
  "stage 1 1 8 8\n" ++
  "stage 0 0 9 9\n"

/-- The public file of the run "product". -/
def product : String :=
  "run product\n" ++
  "format H821\n" ++
  "target 128\n" ++
  "work-on-positions 20\n" ++
  "salt-bytes 40\n" ++
  "nonce-bytes 8\n" ++
  "position-bytes 0\n" ++
  "samples 1\n" ++
  "log-length 12\n" ++
  "log-n 15\n" ++
  "mask-log-n 15\n" ++
  "stage 1 1 14 14\n" ++
  "stage 0 0 14 14\n"

/-- The public file of the run "links" at tiny size. -/
def tinyLinks : String :=
  "run links, tiny edition: a test size that reaches no security level\n" ++
  "format H821\n" ++
  "target 10\n" ++
  "work-on-positions 6\n" ++
  "salt-bytes 40\n" ++
  "nonce-bytes 8\n" ++
  "position-bytes 0\n" ++
  "samples 1\n" ++
  "links 3\n" ++
  "log-length 6\n" ++
  "log-n 9\n" ++
  "mask-log-n 9\n" ++
  "stage 1 1 9 9\n" ++
  "stage 0 0 10 10\n"

/-- The public file of the run "links". -/
def links : String :=
  "run links\n" ++
  "format H821\n" ++
  "target 128\n" ++
  "work-on-positions 20\n" ++
  "salt-bytes 40\n" ++
  "nonce-bytes 8\n" ++
  "position-bytes 0\n" ++
  "samples 1\n" ++
  "links 3\n" ++
  "log-length 12\n" ++
  "log-n 15\n" ++
  "mask-log-n 15\n" ++
  "stage 1 1 14 14\n" ++
  "stage 0 0 14 14\n"

/-- The length and the digest of a run's parameter bytes. -/
def facts (r : Except String ToyRun) : Option (Nat × String) :=
  r.toOption.map fun x =>
    (x.params.size, Fmt.hex (Fmt.paramsDigestW (m := Id) formatHashFastForm x.params))

#guard facts (productRun tinyProduct.toUTF8 10) ==
  some (2949, "26d712eca24f846337fa037bfbe0cf44fb9e9922d3ace3dd4e0f37285835f76b")
#guard facts (productRun product.toUTF8) ==
  some (3765, "a0cecb8c51f49dd4fb30aa83c9ecbbd5a60d8ee2eadb517becff542160d050c7")
#guard facts (linksRun tinyLinks.toUTF8 10) ==
  some (6878, "59922437150dbd2232f5986d9c1b939e1639a1e7b145989202984f34a08c1161")
#guard facts (linksRun links.toUTF8) ==
  some (8744, "9b25d5f4e5adf08c456bf0cbd7ba184a7ce04c5b54e8ddb311a9c8fdbb365aab")
-- a file whose target is below what the caller asks
#guard (productRun tinyProduct.toUTF8).toOption.isNone
#guard (linksRun tinyLinks.toUTF8 11).toOption.isNone
#guard (match productRun tinyProduct.toUTF8 with | .error e => e | .ok _ => "") == "security-bits"
-- another run's file; a leading zero; a line too many; no line feed at the end
#guard (facts (productRun links.toUTF8)).isNone && (facts (linksRun product.toUTF8)).isNone
#guard (facts (productRun (product.replace "target 128" "target 0128").toUTF8)).isNone
#guard (facts (productRun (product ++ "samples 1\n").toUTF8)).isNone
#guard (facts (productRun ⟨product.toUTF8.toList.dropLast.toArray⟩)).isNone
-- very many lines, and a line of very many numbers: refused, at the cost of their length
#guard (facts (productRun
  (product ++ String.join (List.replicate 100000 "stage 0 0 14 14\n")).toUTF8)).isNone
#guard (facts (productRun
  ((product.dropEnd 1).toString ++ String.join (List.replicate 300000 " 7") ++ "\n").toUTF8)).isNone
-- a nonce of 0 or 9 bytes, a listed position of 9 bytes or of very many
#guard (facts (productRun (product.replace "nonce-bytes 8" "nonce-bytes 0").toUTF8)).isNone
#guard (facts (productRun (product.replace "nonce-bytes 8" "nonce-bytes 9").toUTF8)).isNone
#guard (facts (productRun (product.replace "position-bytes 0" "position-bytes 9").toUTF8)).isNone
#guard (facts (linksRun (links.replace "position-bytes 0" "position-bytes 999999").toUTF8)).isNone
-- a zero byte in the first line
#guard (facts (productRun (product.replace "run product" "run product\x00").toUTF8)).isNone
#guard (facts (linksRun (links.replace "run links" "run li\x00nks").toUTF8)).isNone
-- all four files ask for work before positions are drawn, and need it
#guard (productRun product.toUTF8).toOption.map (fun r => (r.needsWork, r.work)) == some (true, 20)
#guard (linksRun links.toUTF8).toOption.map (fun r => (r.needsWork, r.work)) == some (true, 20)
#guard (productRun tinyProduct.toUTF8 10).toOption.map (fun r => (r.needsWork, r.work)) ==
  some (true, 6)
#guard (linksRun tinyLinks.toUTF8 10).toOption.map (fun r => (r.needsWork, r.work)) ==
  some (true, 6)

end OnBytes.Plan.TestToyRuns
