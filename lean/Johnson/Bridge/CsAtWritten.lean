-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bridge/CsAtWritten.lean: the code switches of the nine proximity tests of a key file, an
entry file and a proof file, at two sizes, as written numbers; and at each of the fifty-five: the
code switch is taken off, and both of its rounds' error counts are at most 2^-128 of the round's
written verifier messages.

The statement on codes is not used in this file's own proofs. Through its imports the file stands
above Cb/Bridge/CodeListRSProved.lean and the files under ThirdParty/: files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15).
Like the files of Cb/Bridge/, this file was written by AI systems that had seen ArkLib's source
(https://github.com/Verified-zkEVM/ArkLib, a copy marked as
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13; Copyright ArkLib Contributors, Apache-2.0), so it
does not count as written independently of it. It takes no text from ArkLib or from ThirdParty/ and
follows no file of theirs.

Definitions, and statements that are proved by evaluation on natural numbers and the theorems of
Johnson/Bridge/CsPriced.lean.

Main names:
  `switchFull` (34 places), `switchSmall` (21 places): one place between each stage of a test and
    the next, in the order: the key file's proof of the ranges, folded row, Omega, own test; the
    entry file's test; the proof file's last test behind the links, folded row, Omega, own test.
  `switch_good`, `switch_priced`: all fifty-five pass the two tests.
  `switchFull_key`: the key file's fourteen at full size are `keyCs`
    (Johnson/Top/H/KeyValues.lean), stages and radii.
  `SwitchPlacesPaid`, `switchPlacesPaid`: THE STATEMENT: `SwitchPlace.Paid` at each of the
    fifty-five.

Limits: THAT THESE NUMBERS ARE THOSE OF A FILE's PLAN IS NOT PROVED HERE, and that they are the
stages of the description of the protocol that a verifier runs is open. The numerals are tied to
nothing but typed numbers: at fourteen places stages and radii (not the bits of work) equal `keyCs`,
a definition which was itself read off a print (its head says so). Stages and radii are those of
Johnson/Bridge/FoldAtWritten.lean and Johnson/Bridge/BaseAtWritten.lean, read off the same prints;
no theorem here ties the three lists to each other (Johnson/Bridge/TestsAtWritten.lean does). The
bits of work (32 in the key and the entry file, 20 or 28 in the proof file) are those of the plans'
entries «CS», by a print of the same kind. Of the 128 bits of a second round these are proof of
work. The tightest second round has 128.10 bits at full size (the proof file's Omega, from stage 3)
and 128.11 at the small size; the first rounds have 169 bits or more. The code switches into a proof
file's links' groups (rounds «SEND seed» and «LOC») are not here. No sum over rounds. Nothing on a
verifier or a file.

-/
import Johnson.Bridge.CsPriced
import Johnson.Top.H.KeyValues

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Bridge
open OnBytes OnBytes.Slice Cb

/-- The code switches at full size. -/
def switchFull : List SwitchPlace := [
  -- key: proof of the ranges, from stage 1
  ⟨⟨⟨22, 262144, 49⟩, ⟨16, 4096, 49⟩, 4, 0, 49⟩,
    ⟨⟨19, 16384, 39⟩, ⟨17, 2048, 39⟩, 3, 1, 39⟩, 3131959, 431022, 32⟩,
  -- key: proof of the ranges, from stage 2
  ⟨⟨⟨19, 16384, 39⟩, ⟨17, 2048, 39⟩, 3, 1, 39⟩,
    ⟨⟨17, 2048, 33⟩, ⟨17, 1024, 33⟩, 3, 0, 33⟩, 431022, 114481, 32⟩,
  -- key: proof of the ranges, from stage 3
  ⟨⟨⟨17, 2048, 33⟩, ⟨17, 1024, 33⟩, 3, 0, 33⟩,
    ⟨⟨20, 2048, 25⟩, ⟨20, 4096, 25⟩, 0, 0, 25⟩, 114481, 982125, 32⟩,
  -- key: folded row, from stage 1
  ⟨⟨⟨24, 4194304, 97⟩, ⟨13, 64, 146⟩, 0, 7, 97⟩,
    ⟨⟨21, 131072, 52⟩, ⟨12, 256, 52⟩, 2, 3, 52⟩, 8342420, 1519572, 32⟩,
  -- key: folded row, from stage 2
  ⟨⟨⟨21, 131072, 52⟩, ⟨12, 256, 52⟩, 2, 3, 52⟩,
    ⟨⟨17, 8192, 52⟩, ⟨12, 256, 52⟩, 2, 2, 52⟩, 1519572, 95065, 32⟩,
  -- key: folded row, from stage 3
  ⟨⟨⟨17, 8192, 52⟩, ⟨12, 256, 52⟩, 2, 2, 52⟩,
    ⟨⟨13, 512, 52⟩, ⟨12, 256, 52⟩, 2, 2, 52⟩, 95065, 5944, 32⟩,
  -- key: folded row, from stage 4
  ⟨⟨⟨13, 512, 52⟩, ⟨12, 256, 52⟩, 2, 2, 52⟩,
    ⟨⟨14, 512, 49⟩, ⟨14, 1024, 49⟩, 0, 0, 49⟩, 5944, 12184, 32⟩,
  -- key: Omega, from stage 1
  ⟨⟨⟨22, 262144, 98⟩, ⟨13, 64, 146⟩, 0, 4, 49⟩,
    ⟨⟨18, 16384, 49⟩, ⟨14, 128, 49⟩, 3, 1, 49⟩, 3138896, 196275, 32⟩,
  -- key: Omega, from stage 2
  ⟨⟨⟨18, 16384, 49⟩, ⟨14, 128, 49⟩, 3, 1, 49⟩,
    ⟨⟨14, 1024, 49⟩, ⟨13, 64, 49⟩, 3, 1, 49⟩, 196275, 12184, 32⟩,
  -- key: Omega, from stage 3
  ⟨⟨⟨14, 1024, 49⟩, ⟨13, 64, 49⟩, 3, 1, 49⟩,
    ⟨⟨15, 1024, 39⟩, ⟨15, 512, 39⟩, 0, 0, 39⟩, 12184, 26851, 32⟩,
  -- key: own test, from stage 1
  ⟨⟨⟨22, 262144, 98⟩, ⟨13, 256, 49⟩, 1, 4, 49⟩,
    ⟨⟨18, 16384, 49⟩, ⟨15, 128, 49⟩, 3, 1, 49⟩, 3138896, 196275, 32⟩,
  -- key: own test, from stage 2
  ⟨⟨⟨18, 16384, 49⟩, ⟨15, 128, 49⟩, 3, 1, 49⟩,
    ⟨⟨15, 2048, 49⟩, ⟨14, 64, 49⟩, 3, 0, 49⟩, 196275, 24460, 32⟩,
  -- key: own test, from stage 3
  ⟨⟨⟨15, 2048, 49⟩, ⟨14, 64, 49⟩, 3, 0, 49⟩,
    ⟨⟨13, 256, 41⟩, ⟨13, 64, 41⟩, 3, 0, 41⟩, 24460, 6631, 32⟩,
  -- key: own test, from stage 4
  ⟨⟨⟨13, 256, 41⟩, ⟨13, 64, 41⟩, 3, 0, 41⟩,
    ⟨⟨15, 256, 29⟩, ⟨15, 256, 29⟩, 0, 0, 29⟩, 6631, 29702, 32⟩,
  -- entry: the entry's test, from stage 1
  ⟨⟨⟨24, 4194304, 97⟩, ⟨13, 64, 97⟩, 0, 8, 97⟩,
    ⟨⟨21, 131072, 49⟩, ⟨12, 128, 49⟩, 2, 3, 49⟩, 8342420, 1569886, 32⟩,
  -- entry: the entry's test, from stage 2
  ⟨⟨⟨21, 131072, 49⟩, ⟨12, 128, 49⟩, 2, 3, 49⟩,
    ⟨⟨17, 8192, 49⟩, ⟨12, 128, 49⟩, 2, 2, 49⟩, 1569886, 98104, 32⟩,
  -- entry: the entry's test, from stage 3
  ⟨⟨⟨17, 8192, 49⟩, ⟨12, 128, 49⟩, 2, 2, 49⟩,
    ⟨⟨13, 512, 50⟩, ⟨12, 128, 50⟩, 2, 2, 50⟩, 98104, 6044, 32⟩,
  -- entry: the entry's test, from stage 4
  ⟨⟨⟨13, 512, 50⟩, ⟨12, 128, 50⟩, 2, 2, 50⟩,
    ⟨⟨14, 512, 40⟩, ⟨14, 512, 40⟩, 0, 0, 40⟩, 6044, 13370, 32⟩,
  -- proof: last test behind the links, from stage 1
  ⟨⟨⟨23, 4194304, 219⟩, ⟨17, 8192, 219⟩, 0, 1, 219⟩,
    ⟨⟨22, 262144, 55⟩, ⟨17, 4096, 55⟩, 3, 1, 55⟩, 2433820, 3138982, 20⟩,
  -- proof: last test behind the links, from stage 2
  ⟨⟨⟨22, 262144, 55⟩, ⟨17, 4096, 55⟩, 3, 1, 55⟩,
    ⟨⟨19, 32768, 55⟩, ⟨16, 2048, 55⟩, 3, 0, 55⟩, 3138982, 392563, 20⟩,
  -- proof: last test behind the links, from stage 3
  ⟨⟨⟨19, 32768, 55⟩, ⟨16, 2048, 55⟩, 3, 0, 55⟩,
    ⟨⟨16, 4096, 55⟩, ⟨15, 1024, 55⟩, 3, 0, 55⟩, 392563, 48999, 20⟩,
  -- proof: last test behind the links, from stage 4
  ⟨⟨⟨16, 4096, 55⟩, ⟨15, 1024, 55⟩, 3, 0, 55⟩,
    ⟨⟨13, 256, 46⟩, ⟨13, 256, 46⟩, 4, 0, 46⟩, 48999, 6617, 20⟩,
  -- proof: last test behind the links, from stage 5
  ⟨⟨⟨13, 256, 46⟩, ⟨13, 256, 46⟩, 4, 0, 46⟩,
    ⟨⟨15, 256, 44⟩, ⟨15, 1024, 44⟩, 0, 0, 44⟩, 6617, 26837, 20⟩,
  -- proof: folded row, from stage 1
  ⟨⟨⟨24, 4194304, 101⟩, ⟨13, 64, 152⟩, 0, 7, 101⟩,
    ⟨⟨21, 131072, 54⟩, ⟨12, 256, 54⟩, 2, 3, 54⟩, 8342416, 1517714, 28⟩,
  -- proof: folded row, from stage 2
  ⟨⟨⟨21, 131072, 54⟩, ⟨12, 256, 54⟩, 2, 3, 54⟩,
    ⟨⟨17, 8192, 54⟩, ⟨12, 256, 54⟩, 2, 2, 54⟩, 1517714, 94948, 28⟩,
  -- proof: folded row, from stage 3
  ⟨⟨⟨17, 8192, 54⟩, ⟨12, 256, 54⟩, 2, 2, 54⟩,
    ⟨⟨13, 512, 54⟩, ⟨12, 256, 54⟩, 2, 2, 54⟩, 94948, 5937, 28⟩,
  -- proof: folded row, from stage 4
  ⟨⟨⟨13, 512, 54⟩, ⟨12, 256, 54⟩, 2, 2, 54⟩,
    ⟨⟨14, 512, 51⟩, ⟨14, 1024, 51⟩, 0, 0, 51⟩, 5937, 12180, 28⟩,
  -- proof: Omega, from stage 1
  ⟨⟨⟨22, 262144, 3571⟩, ⟨13, 64, 152⟩, 0, 4, 51⟩,
    ⟨⟨18, 16384, 51⟩, ⟨14, 512, 51⟩, 3, 1, 51⟩, 3131972, 196271, 28⟩,
  -- proof: Omega, from stage 2
  ⟨⟨⟨18, 16384, 51⟩, ⟨14, 512, 51⟩, 3, 1, 51⟩,
    ⟨⟨14, 1024, 51⟩, ⟨13, 256, 51⟩, 3, 1, 51⟩, 196271, 12180, 28⟩,
  -- proof: Omega, from stage 3
  ⟨⟨⟨14, 1024, 51⟩, ⟨13, 256, 51⟩, 3, 1, 51⟩,
    ⟨⟨15, 1024, 41⟩, ⟨15, 1024, 41⟩, 0, 0, 41⟩, 12180, 26843, 28⟩,
  -- proof: own test, from stage 1
  ⟨⟨⟨22, 262144, 3571⟩, ⟨13, 256, 55⟩, 1, 4, 55⟩,
    ⟨⟨18, 16384, 55⟩, ⟨15, 1024, 55⟩, 3, 1, 55⟩, 3131972, 196263, 20⟩,
  -- proof: own test, from stage 2
  ⟨⟨⟨18, 16384, 55⟩, ⟨15, 1024, 55⟩, 3, 1, 55⟩,
    ⟨⟨15, 2048, 55⟩, ⟨14, 512, 55⟩, 3, 0, 55⟩, 196263, 24449, 20⟩,
  -- proof: own test, from stage 3
  ⟨⟨⟨15, 2048, 55⟩, ⟨14, 512, 55⟩, 3, 0, 55⟩,
    ⟨⟨13, 256, 46⟩, ⟨13, 256, 46⟩, 3, 0, 46⟩, 24449, 6617, 20⟩,
  -- proof: own test, from stage 4
  ⟨⟨⟨13, 256, 46⟩, ⟨13, 256, 46⟩, 3, 0, 46⟩,
    ⟨⟨15, 256, 44⟩, ⟨15, 1024, 44⟩, 0, 0, 44⟩, 6617, 26837, 20⟩]

/-- The code switches at the small size. -/
def switchSmall : List SwitchPlace := [
  -- key: proof of the ranges, from stage 1
  ⟨⟨⟨22, 262144, 49⟩, ⟨16, 1024, 49⟩, 3, 0, 49⟩,
    ⟨⟨19, 16384, 39⟩, ⟨17, 512, 39⟩, 3, 1, 39⟩, 3138994, 431022, 32⟩,
  -- key: proof of the ranges, from stage 2
  ⟨⟨⟨19, 16384, 39⟩, ⟨17, 512, 39⟩, 3, 1, 39⟩,
    ⟨⟨17, 2048, 33⟩, ⟨17, 256, 33⟩, 3, 0, 33⟩, 431022, 114481, 32⟩,
  -- key: proof of the ranges, from stage 3
  ⟨⟨⟨17, 2048, 33⟩, ⟨17, 256, 33⟩, 3, 0, 33⟩,
    ⟨⟨20, 2048, 22⟩, ⟨20, 1024, 22⟩, 0, 0, 22⟩, 114481, 1001368, 32⟩,
  -- key: folded row, from stage 1
  ⟨⟨⟨17, 32768, 97⟩, ⟨13, 64, 146⟩, 0, 5, 97⟩,
    ⟨⟨14, 2048, 66⟩, ⟨12, 256, 66⟩, 2, 2, 66⟩, 65304, 10490, 32⟩,
  -- key: folded row, from stage 2
  ⟨⟨⟨14, 2048, 66⟩, ⟨12, 256, 66⟩, 2, 2, 66⟩,
    ⟨⟨14, 2048, 66⟩, ⟨14, 1024, 66⟩, 0, 0, 66⟩, 10490, 10490, 32⟩,
  -- key: Omega, from stage 1
  ⟨⟨⟨18, 16384, 98⟩, ⟨13, 64, 146⟩, 0, 2, 49⟩,
    ⟨⟨14, 1024, 49⟩, ⟨13, 128, 49⟩, 3, 1, 49⟩, 196176, 12184, 32⟩,
  -- key: Omega, from stage 2
  ⟨⟨⟨14, 1024, 49⟩, ⟨13, 128, 49⟩, 3, 1, 49⟩,
    ⟨⟨15, 1024, 39⟩, ⟨15, 512, 39⟩, 0, 0, 39⟩, 12184, 26851, 32⟩,
  -- key: own test, from stage 1
  ⟨⟨⟨18, 16384, 98⟩, ⟨13, 256, 49⟩, 0, 3, 49⟩,
    ⟨⟨14, 1024, 49⟩, ⟨13, 128, 49⟩, 3, 1, 49⟩, 196176, 12184, 32⟩,
  -- key: own test, from stage 2
  ⟨⟨⟨14, 1024, 49⟩, ⟨13, 128, 49⟩, 3, 1, 49⟩,
    ⟨⟨15, 1024, 39⟩, ⟨15, 512, 39⟩, 0, 0, 39⟩, 12184, 26851, 32⟩,
  -- entry: the entry's test, from stage 1
  ⟨⟨⟨17, 32768, 97⟩, ⟨13, 64, 97⟩, 0, 6, 97⟩,
    ⟨⟨14, 2048, 66⟩, ⟨12, 128, 66⟩, 2, 2, 66⟩, 65304, 10490, 32⟩,
  -- entry: the entry's test, from stage 2
  ⟨⟨⟨14, 2048, 66⟩, ⟨12, 128, 66⟩, 2, 2, 66⟩,
    ⟨⟨14, 2048, 66⟩, ⟨14, 512, 66⟩, 0, 0, 66⟩, 10490, 10490, 32⟩,
  -- proof: last test behind the links, from stage 1
  ⟨⟨⟨18, 131072, 218⟩, ⟨17, 8192, 218⟩, 0, 1, 218⟩,
    ⟨⟨17, 8192, 55⟩, ⟨17, 4096, 55⟩, 3, 1, 55⟩, 76267, 98093, 20⟩,
  -- proof: last test behind the links, from stage 2
  ⟨⟨⟨17, 8192, 55⟩, ⟨17, 4096, 55⟩, 3, 1, 55⟩,
    ⟨⟨16, 1024, 44⟩, ⟨16, 2048, 44⟩, 3, 0, 44⟩, 98093, 53784, 20⟩,
  -- proof: last test behind the links, from stage 3
  ⟨⟨⟨16, 1024, 44⟩, ⟨16, 2048, 44⟩, 3, 0, 44⟩,
    ⟨⟨15, 128, 44⟩, ⟨15, 1024, 44⟩, 3, 0, 44⟩, 53784, 26835, 20⟩,
  -- proof: last test behind the links, from stage 4
  ⟨⟨⟨15, 128, 44⟩, ⟨15, 1024, 44⟩, 3, 0, 44⟩,
    ⟨⟨15, 128, 73⟩, ⟨15, 4096, 73⟩, 0, 0, 73⟩, 26835, 21058, 20⟩,
  -- proof: folded row, from stage 1
  ⟨⟨⟨17, 32768, 101⟩, ⟨13, 64, 156⟩, 0, 5, 101⟩,
    ⟨⟨14, 2048, 68⟩, ⟨12, 256, 68⟩, 2, 2, 68⟩, 65300, 10487, 28⟩,
  -- proof: folded row, from stage 2
  ⟨⟨⟨14, 2048, 68⟩, ⟨12, 256, 68⟩, 2, 2, 68⟩,
    ⟨⟨14, 2048, 68⟩, ⟨14, 1024, 68⟩, 0, 0, 68⟩, 10487, 10487, 28⟩,
  -- proof: Omega, from stage 1
  ⟨⟨⟨18, 16384, 3831⟩, ⟨13, 64, 156⟩, 0, 2, 55⟩,
    ⟨⟨14, 1024, 69⟩, ⟨13, 1024, 69⟩, 3, 1, 69⟩, 189103, 10390, 28⟩,
  -- proof: Omega, from stage 2
  ⟨⟨⟨14, 1024, 69⟩, ⟨13, 1024, 69⟩, 3, 1, 69⟩,
    ⟨⟨15, 1024, 68⟩, ⟨15, 4096, 68⟩, 0, 0, 68⟩, 10390, 21065, 28⟩,
  -- proof: own test, from stage 1
  ⟨⟨⟨18, 16384, 3831⟩, ⟨13, 256, 59⟩, 0, 3, 59⟩,
    ⟨⟨14, 1024, 75⟩, ⟨13, 1024, 75⟩, 3, 1, 75⟩, 189103, 10374, 20⟩,
  -- proof: own test, from stage 2
  ⟨⟨⟨14, 1024, 75⟩, ⟨13, 1024, 75⟩, 3, 1, 75⟩,
    ⟨⟨15, 1024, 73⟩, ⟨15, 4096, 73⟩, 0, 0, 73⟩, 10374, 21058, 20⟩]

theorem switch_good : ((switchFull ++ switchSmall).all fun x => x.good) = true := by decide +kernel

theorem switch_priced : ((switchFull ++ switchSmall).all fun x => x.priced) = true := by
  decide +kernel

/-- The key file's fourteen at full size are the list `keyCs`. -/
theorem switchFull_key :
    (switchFull.take 14).map (fun x => (⟨x.s, x.s', x.e, x.e'⟩ : Johnson.Top.H.CsPlace)) =
      Johnson.Top.H.keyCs := rfl

/-- **The code switches taken off, and their rounds' counts against 2^-128, at the written
stages.** -/
def SwitchPlacesPaid : Prop := ∀ x ∈ switchFull ++ switchSmall, x.Paid

theorem switchPlacesPaid : SwitchPlacesPaid := fun x hx =>
  SwitchPlace.paid (List.all_eq_true.1 switch_good x hx) (List.all_eq_true.1 switch_priced x hx)

end Johnson.Bridge

#print axioms Johnson.Bridge.switch_good
#print axioms Johnson.Bridge.switch_priced
#print axioms Johnson.Bridge.switchPlacesPaid
