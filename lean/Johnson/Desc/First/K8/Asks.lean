-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K8/Asks.lean: THE SMALLNESS TEST: THE FAMILIES OF TABLES IN A LINK's VECTOR OF
READS, AS NUMBERS OF THE PLACE: for each of the three sorts of link a function of the public shapes
alone. A family: the number of its first matrix in the link's list · of how many matrices in a row
it has a table · over how many rows one entry sums (Johnson/Desc/First/K8/Hear.lean: Par.asks).
DEFINITIONS, WITH CODE. NO THEOREM. NO SOUNDNESS IS CLAIMED.
WHERE THE LISTS COME FROM: each follows, in order and in numbers, the text by which that sort of
link makes its tables out of what it has heard: layers: OnBytes/Model/LayerForms.lean: tableAsks ·
attention: OnBytes/Model/AttentionTables.lean:218-272 · the head: OnBytes/Model/HeadTables.lean:
tablesOf. Here the weights are left out, and with them everything that a prover sent. THAT THE LISTS
AGREE WITH WHAT THE LINKS' KINDS MAKE IS ASKED AT EVERY RUN by the kind's test (t).

-/
import OnBytes.Model.VerifyPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Asks
open OnBytes OnBytes.Model

/-- A layers' link, of group g. The matrices' numbers: the parts of af from 0 · the parts of ad · ar
· b · qa · the stream that goes out · the stream that comes in. -/
def layers (y : Layer.Lay) (rd : Layer.Reads) (g : Nat) : List (Nat × Nat × Nat) :=
  let nAF := y.parts.getD 0 0
  let nAD := y.parts.getD 1 0
  let iAR := nAF + nAD
  let long := 2 ^ y.h.la
  List.replicate rd.rdAF.length (0, nAF, long) ++
  List.replicate rd.rdQA.length (iAR + 2, 1, long) ++
  List.replicate rd.rdXI.length (iAR + 4, 1, long) ++
  (if g == 0 then [(iAR + 4, 1, long)] else []) ++
  List.replicate rd.rdXO.length (iAR + 3, 1, long) ++
  List.replicate rd.rdAD.length (nAF, nAD, y.T) ++
  List.replicate rd.rdAR.length (iAR, 1, y.T) ++
  (if y.h.p4 then List.replicate rd.rdQS.length (iAR + 2, 1, y.T) else []) ++
  List.replicate 3 (iAR + 1, 1, 2 ^ y.h.lmb)

/-- An attention link. n: the units of the scores. The matrices' numbers: the parts of `as` from 0 ·
ah · ao · bA · qa. A unit: a lookup call of the kind KFD with one of the segments fm, fd that it
holds (OnBytes/Model/AttentionScores.lean: unitsOf, scores). -/
def attention (S : Attention.Shape) : List (Nat × Nat × Nat) :=
  let two := [Attention.Seg.fm, Attention.Seg.fd]
  let n := (S.calls.toList.filter fun c => c.kind == Attention.Table.kfd).foldl
    (fun a c => a + (two.filter fun s => c.segs.contains s).length) 0
  let N := S.cf.NAs
  List.replicate 3 (0, N, 2 ^ S.cf.lmS) ++
  List.replicate (n + 6) (N, 1, S.T) ++
  [(N + 1, 1, 2 ^ S.cf.la)] ++
  List.replicate (2 * n + 5) (N + 3, 1, 2 ^ S.cf.la) ++
  List.replicate 3 (N + 2, 1, 2 ^ S.cf.lmb)

/-- The head's link. The matrices' numbers: the parts of hf from 0 · hd · hr · bH · xbL. -/
def head (h : Head.Shape) : List (Nat × Nat × Nat) :=
  let N := h.NHf
  List.replicate 2 (0, N, 2 ^ h.la) ++
  List.replicate 2 (N + 3, 1, 2 ^ h.la) ++
  List.replicate 2 (N, 1, h.T) ++
  List.replicate 6 (N + 1, 1, h.T) ++
  List.replicate 3 (N + 2, 1, 2 ^ h.lmbH)

end VerifiableInference.Desc.First.K8.Asks
