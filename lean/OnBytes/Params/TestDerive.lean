-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/TestDerive.lean: tests of the derivation of sizes and plans from the parameter file.

The lines are those of prover/examples/target_small_f2_roomy/policy.txt. The numbers that are
expected were taken from the C++ verifier: the columns, positions and codes from its planning call
on that example (`-plan accounting`), and the parameter bytes' lengths and digests from a run on a
proof of that example of a copy of the verifier (not in this repository) that writes out what it
hashes. The order of the codes is held by the digests, which hash them. The rows of a link, the
rider's class, the first chain's rounds and its verdict are compared with no print. The sub-proofs'
numbers are written out by hand; the first chain's plan is made from them. Each test is checked when the file compiles. The file is no part of the
program.
-/
import OnBytes.Params.DeriveReq
import OnBytes.Params.SubRounds
import OnBytes.Hash.H
import OnBytes.Params.TestFile

namespace OnBytes.Params.TestDerive

/-- The lines of the small example. -/
def lines : Option Lines := TestFile.smallLines

/-- The digest of the small example's three public files. -/
def cfg : ByteArray := TestFile.smallCfg

/-- What follows for the link of the small example. -/
def link : Option (LinkSized × Codes) :=
  lines.bind fun l => (deriveTable (settingOf l) l).bind fun T => linkSized (settingOf l) l T {}

-- the columns of the two tables, the rows of a folded row's oracle message, the codes
#guard link.any fun x => x.1.shape.columnsFirst == 51 && x.1.shape.columnsFurther == 51 &&
  x.1.shape.rows == 18
-- the codes of the entry's chain
#guard link.any fun x =>
  x.2.base == #[⟨17, 32768, 97⟩, ⟨14, 2048, 66⟩] &&
  x.2.mask == #[⟨13, 64, 97⟩, ⟨12, 128, 66⟩, ⟨14, 512, 66⟩]
-- the parameter bytes of the entry's chain: their length and their digest
#guard (lines.bind fun l => (entryParams l cfg).toOption).any fun b => b.size == 3154 &&
  Fmt.hex (Fmt.paramsDigestW (m := Id) formatHashFastForm b) ==
    "024a450069cd46ebdeb048d9ec5c3860e8eb16cb4be3a42c0d72f3c33e7ce6d7"

/-- The digest of parameter bytes, in hexadecimal digits. -/
def digestOf (b : Option ByteArray) : Option String :=
  b.map fun x => Fmt.hex (Fmt.paramsDigestW (m := Id) formatHashFastForm x)

/-- The test on the table of the small example: the matrix has 59392 rows, and the message that
masks the claims has one mask row. `before` are the codes that stand in the list already. -/
def lin (oneTime : Bool) (before : Codes) : Option (Setting × LinSized × Codes) :=
  lines.bind fun l =>
    let s := settingOf l
    (deriveTable s l).bind fun T =>
      (linSized s (linLines l 59392 1 oneTime) T before).map fun x =>
        (s, x.1, x.2)

-- a key's test: the columns of the table, and the codes in the order in which they are entered
#guard (lin true {}).any fun x => x.2.1.shape.fold.columns == 51 &&
  x.2.2.base == #[⟨17, 32768, 97⟩, ⟨14, 2048, 66⟩, ⟨18, 16384, 98⟩, ⟨14, 1024, 49⟩, ⟨15, 1024, 39⟩] &&
  x.2.2.mask == #[⟨13, 64, 146⟩, ⟨12, 256, 66⟩, ⟨14, 1024, 66⟩, ⟨13, 128, 49⟩, ⟨15, 512, 39⟩,
                  ⟨13, 256, 49⟩]
-- the second chains of a key and of a proof
#guard digestOf ((lin true {}).bind fun x => (secondParams x.1 x.2.1 cfg).toOption) ==
  some "50b081d0b33589b3964f4a8d0d7227676d4495c676200a3a3d9da67f7d5fe474"
#guard digestOf ((lin false {}).bind fun x => (secondParams x.1 x.2.1 cfg).toOption) ==
  some "80c1a7c7d0f4c3304ef58d9d791c128152c28f423474873a3e787be0f6025cea"

/-- The codes that the ranges' proof adds to a key's list after the test's. -/
def withRanges (c : Codes) : Codes :=
  ⟨c.base ++ #[⟨22, 262144, 49⟩, ⟨19, 16384, 39⟩, ⟨17, 2048, 33⟩, ⟨20, 2048, 22⟩],
   c.mask ++ #[⟨16, 1024, 49⟩, ⟨17, 512, 39⟩, ⟨17, 256, 33⟩, ⟨20, 1024, 22⟩]⟩

/-- The codes of a request's links and of their last test, which stand first in a proof's list. -/
def ofTheLinks : Codes :=
  ⟨#[⟨18, 131072, 218⟩, ⟨17, 8192, 55⟩, ⟨16, 1024, 44⟩, ⟨15, 128, 44⟩, ⟨15, 128, 73⟩],
   #[⟨17, 8192, 218⟩, ⟨17, 4096, 55⟩, ⟨16, 2048, 44⟩, ⟨15, 1024, 44⟩, ⟨15, 4096, 73⟩]⟩

-- the shared chains of a key and of a proof, with the other blocks' codes taken as known
#guard digestOf ((lin true {}).bind fun x =>
    (sharedParams x.1 (withRanges x.2.2) x.2.1 cfg).toOption) ==
  some "1f65b490e5071b268d94a37af4bb23bb21227032982a0be756f8097d5e53817a"
#guard digestOf ((lin false ofTheLinks).bind fun x =>
    (sharedParams x.1 x.2.2 x.2.1 cfg).toOption) ==
  some "6e18903daad8dccc4414257bd8b7d66423a3a4bc8849915d46866b7c19860f6e"

/-- An oracle message of a link, from its main rows, their degree, its mask rows, its moment and
its life. -/
def msg (rows deg masks moment life : Nat) : ReqMessage :=
  ⟨{ mainRows := rows, mainDeg := deg, maskRows := masks }, 0, moment, life⟩

/-- The five links of the small example: two groups of layers, each followed by its attention,
and the head. The sub-proofs' own rounds are left out: the sizes do not read them. -/
def sub : Subproofs where
  links :=
    [⟨0, [msg 61 1 1 0 0, msg 3 1 0 0 1, msg 1 1 0 0 2, msg 2 3 0 1 0, msg 129 1 0 2 0]⟩,
     ⟨0, [msg 23 1 1 0 0, msg 1 3 0 1 0, msg 61 1 0 2 0]⟩,
     ⟨0, [msg 60 1 1 0 0, msg 3 1 0 0 1, msg 1 1 0 0 2, msg 2 3 0 1 0, msg 129 1 0 2 0]⟩,
     ⟨0, [msg 23 1 1 0 0, msg 1 3 0 1 0, msg 61 1 0 2 0]⟩,
     ⟨1, [msg 34 1 1 0 0, msg 1 3 0 1 0, msg 81 1 0 2 0]⟩]
  openRows := [1, 1, 1, 1, 1]
  plan := fun _ _ => pure ()
  pendingRows := 3
  matrixRows := 59392

-- the groups of the chain of links: their row variables (the C++ plan has so many rounds of a
-- fold after each link)
#guard (reqGroups (shapeOfLinks (fillLinks sub.links) 1)).toList.map (fun g => (g.k, g.h)) ==
  [(9, 0), (7, 0), (9, 0), (7, 0), (8, 0), (1, 0)]
-- a proof's sizes: the positions of a link's list, all codes in their order, the rider's class
#guard (lines.bind fun l => proofSized l sub).any fun z => z.link.t == 218 &&
  z.codes.base == ofTheLinks.base ++ #[⟨17, 32768, 101⟩, ⟨14, 2048, 68⟩, ⟨18, 16384, 3831⟩,
      ⟨14, 1024, 69⟩, ⟨15, 1024, 68⟩, ⟨14, 1024, 75⟩, ⟨15, 1024, 73⟩] &&
  z.codes.mask == ofTheLinks.mask ++ #[⟨13, 64, 156⟩, ⟨12, 256, 68⟩, ⟨14, 1024, 68⟩,
      ⟨13, 1024, 69⟩, ⟨15, 4096, 68⟩, ⟨13, 256, 59⟩, ⟨13, 1024, 75⟩] &&
  z.request.atStart.map (·.leafClass) == [1] && z.batch.shape.fold.columns == 53

/-- The numbers of the small example's layer sub-proofs. -/
def layers (first : Bool) : LayerRounds :=
  { lt := 6, ls := 2, lNI := 3, lPd := 9, ll := 2, lPf := 10, lfe := 9, lamS := 15, lkW := 11,
    NI := 8, NS := 9, NP := 7, NO := 4, withTerms := true, shownByTheTerms := 18, neverSent := 3,
    weightClaims := 32, firstGroup := first, routed := true }

/-- The numbers of its attention sub-proofs. -/
def attention : AttentionRounds :=
  { lt := 6, lgk := 1, pairs := 8, Lam := 4, planeMessages := 2, score := [(11, 8), (10, 8)],
    e := 7, valueM := 8, valueD := 7, attained := 14, bits := 11, rows := 2074535 }

/-- The numbers of its head sub-proof. -/
def head : HeadRounds :=
  { lt := 6, lPd := 9, lkW := 11, sums := 9, products := 7, rowValues := 4, rows := 2712833 }

/-- The small example's sub-proofs with their rounds. -/
def subWithRounds : Subproofs :=
  { sub with plan := fun link =>
      match link with
      | 0 => layerRounds ⟨24, 19, true⟩ (layers true) ⟨3099, 128, ⟨24, 11, true⟩⟩ 4347789
      | 2 => layerRounds ⟨24, 19, true⟩ (layers false) ⟨3099, 128, ⟨24, 11, true⟩⟩ 4343660
      | 4 => headRounds ⟨23, 19, true⟩ head ⟨1594, 128, ⟨24, 11, true⟩⟩
      | _ => attentionRounds ⟨22, 18, true⟩ attention ⟨1276, 128, ⟨23, 11, true⟩⟩ }

/-- The plan of the first chain of a proof of the small example. -/
def first : Option Planned :=
  lines.bind fun l => (proofSized l subWithRounds).bind fun z =>
    (firstPlan z subWithRounds).toOption

/-- A sum over bytes that is cheap to compute: the bytes as digits to the base 257, modulo
2 ^ 61 - 1. The format's own digest of so long a string would take this test minutes. -/
def cheapSum (b : ByteArray) : Nat := b.foldl (fun h x => (h * 257 + x.toNat) % (2 ^ 61 - 1)) 0

-- the first chain's plan: its rounds and its verdict
#guard first.any fun p => p.rounds.length == 8037 && p.holds && p.needsWork
/-- The same sub-proofs, but the head's smallness test works with 160 combinations. -/
def otherTau : Subproofs :=
  let plan := fun (link : Nat) =>
    if link == 4 then headRounds ⟨23, 19, true⟩ head ⟨1594, 160, ⟨24, 11, true⟩⟩
    else subWithRounds.plan link
  { subWithRounds with plan := plan }

/-- The name under which a plan is refused; the empty string if it is made. -/
def refusal (x : Except String Planned) : String :=
  match x with
  | .error e => e
  | .ok _ => ""

-- another number of combinations in a sub-proof than follows from the setting
#guard (lines.bind fun l => (proofSized l otherTau).map fun z => refusal (firstPlan z otherTau)) ==
  some "plan-tau"

end OnBytes.Params.TestDerive
