-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Entry/TestRecordToySums.lean: the size and a checksum of each stored byte string of the toy:
the nine of OnBytes/Entry/RecordToyFiles.lean and the eight entry files of
Fmt/MustBeRefused/RecordToy.lean.

The checksum is BLAKE2b with 64 bytes of output, no key, no salt and no personalization: Fmt.blake2b
(Fmt/Blake2b.lean), which Fmt/Blake2bKnown.lean holds against known answers.

Where the expected values come from. Outside Lean: the programs ls, sha256sum and b2sum, in one run
over the 17 files from which the literals were made. The sha256 sums of that run are those that
stand in the two files' heads and docstrings. Sizes and BLAKE2b digests were copied from that run's
print into this file by a program.

So a literal that differs from its file in a byte, or in its length, turns a test red. This library
has no function for SHA-256, so the sums in the heads are not computed here.

Every test is checked when the file compiles. The program verify-on-bytes does not import this file.

Not claimed. No theorem. That the 17 files are what the programs, or the cheating prover of six of
the false entries, wrote is not shown here: the two files' heads say where they come from. The
altered copies that OnBytes/Entry/TestRecordToy.lean and OnBytes/Key/TestRecordToy.lean make by
recipes are not held against files. Nothing on soundness, completeness or hiding.
-/
import OnBytes.Entry.RecordToyFiles
import Fmt.MustBeRefused.RecordToy
import Fmt.Blake2b

namespace OnBytes.Entry.RecordToySums
open OnBytes.Entry.RecordToy Fmt.MustBeRefused.RecordToy

/-- Each stored byte string: its name, the bytes, the file's size and the file's BLAKE2b digest. -/
def stored : List (String × ByteArray × Nat × String) := [
  ("keyFile", keyFile, 503744,
    "398ca8f4c965a0ee419f2cba5d98fc0ec5d58c9a531d00a46dc54ccaece47717" ++
    "e47a4b415a46e5e800c3c100079cbd8faae7b186aa234715b7545addb26a5337"),
  ("entryFile", entryFile, 131432,
    "e90a04dfb6cf8d538e88896040034ee6003d61af2b5d529ab1966a5c1887eb7c" ++
    "d106eb8f958f8267591f7a1d39457ad3540e9287a69902d88d1b61475ae4c912"),
  ("entryParameters", entryParameters, 2648,
    "44aa82074c87e44c34a25125486faf3f369752f6dd6d4fabb579564187be8d80" ++
    "99afc6571f7d3c282c1940150f181c8ab0cc77172ec2991f05c2d126f5483669"),
  ("oneTimeParameters", oneTimeParameters, 76647,
    "b80b30e94f29f027c91acde697714a1b24eff74450a531075046a910b1c1acc7" ++
    "23e9eb8b2ccbef03a565faad93a015815a0bdc8d5d45178939ac8f07e1f0a0eb"),
  ("sharedParameters", sharedParameters, 4982,
    "e5acf1a235b82858a4f68c12af0b7a47d6a60f1bc1d08f3167f1141765869b63" ++
    "d988e183f8c8692762c35e5ea6812757fa62f6f7ee98cf71a35bd64979925691"),
  ("secondParameters", secondParameters, 1521,
    "8c1bda734750ea6e32783585f78f54da823bd11c7b5e9736b7646664032fa2a2" ++
    "87a6a95a3422812b18665b57e3f1ecc50f08dc5078c2cb020439e77fd2ec90fe"),
  ("publicFileOne", publicFileOne, 713,
    "9e6e2283b226fe3b3b58e777bf91bb09032bb7492106ff938491d668fc509e5b" ++
    "bad593997bd281a92b4b0772d6fd2997ac26ff20f7358b0a3e67ccdf4e94093f"),
  ("publicFileTwo", publicFileTwo, 47,
    "753e344961bb687fb5919eb7e8567595d21db12ba1b675e263944acc9eaafeb1" ++
    "64a8163e56358dc402b8f8bb18ff57d8e1ba9083087b07616240240932b4f50c"),
  ("entryStatement", entryStatement, 544,
    "8b09dc74a63c67203f59cfb02a04b88f22fa41e2459f9715569c99ff5314dd94" ++
    "e8f186ad726e0a835b4f0f34f2337d8fdc79637e0bb8af78abc2243ebe6be0ba"),
  ("bentSwap", bentSwap, 131432,
    "a7b08d5531021144707c61dfdb28c170b61bc90e5f90a1d8750c987b7a282c9c" ++
    "4ca21c5b074dc97f1ce91351314c2ba20790279fd6c7c2a302be3087b3c45cec"),
  ("linkOneCell", linkOneCell, 131792,
    "1d869372dae47d4d1f389bfc43995213fbcedc044ac2be081b7b5333aca5afe0" ++
    "3d18b15139bd6d920771552b169d7ff994977062db4838a0025b3d9383a1bbc5"),
  ("baseWrongWord", baseWrongWord, 131240,
    "dd1d681c6577a9dc8e2d9549862ac4ce4664554f548cb3733578e8590325d0a6" ++
    "6ba6a5dbe968ce5d0ae99e1388b9f7ec5b6a171df283b1e49466e952488a168f"),
  ("foldeqOtherRow", foldeqOtherRow, 131568,
    "2718524a671997d242404a66a02cf0fb445b4d20c05d2acbd110fad2ae7ab917" ++
    "a900a6c45b2079717850ad39b9fe62a8c66a2816b0288b5f78499e2924965c21"),
  ("linkFarTable", linkFarTable, 132040,
    "dedcc3d2a8cfdd0f274a72bedfd9b612db71c88dca1fcd3054c069531ab2c89e" ++
    "02f4bab6401c8272d6ed7c6e785d7f2fc3a6ca135600c0e062e17ec20c73f721"),
  ("linkOtherCopyRow", linkOtherCopyRow, 131176,
    "4d7a051bc5de9c5f4d4a67eb0f3783a3b8f0e9e51cf4d7d05481694e9c8472ac" ++
    "f29da4635ee56127be5c084cc78a9b618ae95e0669deda1b15d5fb00f6add9ea"),
  ("linkOtherCopyTail", linkOtherCopyTail, 131536,
    "95d49f64a5d41e2ef90aca4317beb574251163a98114a0e855af74c12b35f044" ++
    "5b52b584e94be085753e872e84ae5ea23014f1e8a87ad8cf2237d4e15528cce2"),
  ("linkShortCut", linkShortCut, 130864,
    "ada22f7eba5f3e10ecea7f58220399130813000a7e8228e6f0117aece6d503ca" ++
    "dbc3629e5b70de970cb0b425b10b2c795ba28b9a170b11e1544f4470f736b00c") ]

/-- The checksum, in hex. -/
def sumOf (b : ByteArray) : String := Fmt.hex (Fmt.blake2b 64 ByteArray.empty ByteArray.empty b)

-- the function is b2sum's: the digest of the three bytes "abc" (RFC 7693, appendix A)
#guard sumOf "abc".toUTF8 ==
  "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1" ++
  "7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923"
#guard stored.length == 17 && (stored.map (·.1)).eraseDups.length == 17
-- the sizes
#guard (stored.filter fun x => x.2.1.size != x.2.2.1).map (·.1) == []
-- the checksums
#guard (stored.filter fun x => sumOf x.2.1 != x.2.2.2).map (·.1) == []
-- the test of the test: with bit 0 of the last byte of the key file turned the checksum is another
#guard sumOf (keyFile.set! (keyFile.size - 1) (keyFile.get! (keyFile.size - 1) ^^^ 1)) !=
  sumOf keyFile

end OnBytes.Entry.RecordToySums
