-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M3ItemsKnown.lean: the parameter item "the link" and the format page's test vectors.

An entry file comes with a further stored copy of a committed table. The link is a protocol whose
purpose is to show that the copy holds the same table as the first one (given that the first one is
well formed, which is the key file's matter). An entry file holds the prover's messages,
proof-of-work nonces and Merkle openings of the link (Fmt/M3Entry.lean says more). The parameters of
an entry file's hash chain contain an item named "the link", which lists the sizes of the link
protocol (docs/format/FORMAT.md, R13.9). The format page (FORMAT.md, which comes with the programs;
here in an edition that is not the one that ships) has a list of test vectors, written by its own
program. One of them is this item.






1. What the file contains. No definition and no test.

2. What is checked when the file compiles. Nothing. That `linkBytes` (Fmt/M3Items.lean), this
library's spelling of the item, equals the page's test vector is tested nowhere in this library.



3. Theorems. None.

4. What is not claimed. In that edition the page has two more test vectors in the same
section, for items of a key file's chains. They are not covered here.
-/
import Fmt.M3Items
