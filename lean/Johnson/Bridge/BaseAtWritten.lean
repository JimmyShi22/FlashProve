-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bridge/BaseAtWritten.lean: the last stage of each of the nine proximity tests of a proof
file, a key file and an entry file, at two sizes, as written numbers; and at each of the eighteen:
what the base case asks of its codes holds, with no hypothesis on codes, at letters that are small
enough.

This file rests on Cb/Bridge/CodeListRSProved.lean, and so on the files under ThirdParty/:
files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15).
Like the files of Cb/Bridge/, this file was written by AI systems that had seen ArkLib's source
(https://github.com/Verified-zkEVM/ArkLib, a copy marked as
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13; Copyright ArkLib Contributors, Apache-2.0), so it
does not count as written independently of it. It takes no text from ArkLib or from ThirdParty/ and
follows no file of theirs.

Definitions, and statements that are proved by evaluation on natural numbers and the theorems of
Johnson/Bridge/BaseCodesAt.lean and Johnson/Bridge/BasePriced.lean.

Main names:
  `lastFull`, `lastSmall`: nine places each (`LastPlace`), in the order: the proof file's last test
    behind the links, folded row, Omega, own test; the key file's proof of the ranges, folded row,
    Omega, own test; the entry file's test. A place is: the main code and the mask code (logarithm
    of the length, entries of a message, random entries), the number of drawn positions, the radius,
    the bits of work of the second round, and two brackets of `Cb.bchksBound`.
  `last_good`, `last_priced`: all eighteen pass the two tests.
  `last_far`: at none of them is twice the radius below the stage's distance.
  `lastFull_key`, `lastFull_entry`, `lastSmall_entry`: six of the eighteen stand in other files: the
    key file's four at full size are `keyLast` (Johnson/Top/H/KeyValues.lean), the entry file's two
    are `frSg5` and `srSg3` at their radii (OnBytes/Slice/FullRecCodes.lean, SmallRecCodes.lean).
  `LastPlacesPaid`, `lastPlacesPaid`: THE STATEMENT: at each of the eighteen places: `BaseCodes` at
    the place's two numbers; so, at written rounds that are the format's own «BASE lambda» and
    «BASE», the base case is taken off (`BaseHolds`) with the library's error counts at these
    numbers; and each of the two counts is at most 2^-128 of its round's written verifier messages.

Limits: THAT THESE NUMBERS ARE THOSE OF A FILE's PLAN IS NOT PROVED HERE, and that they are the
stages of the description of the protocol that a verifier runs is open. The numerals are tied to
nothing but typed numbers: at six places stage and radius (not the bits of work, not the brackets)
equal definitions in other files, which were themselves read off a print (their heads say so).
They were read off a print
made by evaluating this library's port of the planner (`Model.Verify.planned`; `stageOf` and
`radiusOf` of Johnson/Top/H/StageJ.lean) at the three public files of two stored example sets
(name, size, sha256):
 full size (prover/examples/target_full_f2, the same files as examples/full-size/config):
  policy.txt (2,629 bytes) ce9e126bb3ba7179319a31981a3fc36ca505d738348971f379dfc795f94a3fae
  layout.txt (224,975 bytes) a99b964bbd3648d6e3b4007fc9370b5c70c7e9668848daa039820bc9e03e8f80
  KL.bin (2,784 bytes) 1c3191164c5113fd04d5108a469d7b3d17f4ccb3256e8a676d15bdc94435b919
 small (prover/examples/target_small_f2_roomy, the same files as examples/accepted-proof/config):
  policy.txt (2,479 bytes) 8d9ae1dda2e503550cafade93c54c1b8ecc8eb4b6dab3b843c72a478bb892d2f
  layout.txt (27,038 bytes) a0cce649d992c6f17d1e27c68ac4b900b828ff6ef0bfe8da7c2491fed9f02225
  KL.bin (464 bytes) b8fb55ed7c70c4cdc7bac01e804dd0dc79349022ba7972957c7e50a29dc974a2
The brackets were reckoned outside Lean in exact integers, and Lean's kernel checks them here. The
program that printed is not in this repository. Of the 128 bits of a second round, 20, 28 or 32 are
proof of work. The tightest first round has 128.01 bits (the small key file's proof of the ranges).
Nothing on a verifier or a file: `BaseHolds` (OnBytes/Slice/BlockHolds.lean) speaks of the two
written rounds alone, of a claim without a witness at the radius, and of columns that show fixed
words; who applies it owes these. No sum over rounds.

-/
import Johnson.Bridge.BasePriced
import OnBytes.Slice.BlocksJohnson
import OnBytes.Slice.ManyJohnson
import OnBytes.Slice.FullRecCodes
import OnBytes.Slice.SmallRecCodes
import Johnson.Top.H.KeyValues

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Bridge
open OnBytes OnBytes.Slice Cb Iop _root_.Run
open scoped ENNReal

/-- The nine last stages at full size. -/
def lastFull : List LastPlace := [
  -- proof: last
  ⟨⟨⟨15, 256, 44⟩, ⟨15, 1024, 44⟩, 0, 0, 44⟩, 26837, 20,
    ⟨3, 1762099180353883179, 1762099180353883180, 13164351193⟩,
    ⟨329, 3328717695466727643, 3328717695466727644, 14439895285771832507⟩⟩,
  -- proof: folded
  ⟨⟨⟨14, 512, 51⟩, ⟨14, 1024, 51⟩, 0, 0, 51⟩, 12180, 28,
    ⟨3, 3416472352878959345, 3416472352878959346, 903243890⟩,
    ⟨457, 4722934183774491208, 4722934183774491209, 13043905961530100492⟩⟩,
  -- proof: omega
  ⟨⟨⟨15, 1024, 41⟩, ⟨15, 1024, 41⟩, 0, 0, 41⟩, 26843, 28,
    ⟨291, 3324034854655124279, 3324034854655124280, 7858034512149105983⟩,
    ⟨291, 3324034854655124279, 3324034854655124280, 7858034512149105983⟩⟩,
  -- proof: own
  ⟨⟨⟨15, 256, 44⟩, ⟨15, 1024, 44⟩, 0, 0, 44⟩, 26837, 20,
    ⟨3, 1762099180353883179, 1762099180353883180, 13164351193⟩,
    ⟨329, 3328717695466727643, 3328717695466727644, 14439895285771832507⟩⟩,
  -- key: ranges
  ⟨⟨⟨20, 2048, 25⟩, ⟨20, 4096, 25⟩, 0, 0, 25⟩, 982125, 32,
    ⟨3, 820001489742707832, 820001489742707833, 4179960268669⟩,
    ⟨91, 1156294270967697095, 1156294270967697096, 18204056319852731468⟩⟩,
  -- key: folded
  ⟨⟨⟨14, 512, 49⟩, ⟨14, 1024, 49⟩, 0, 0, 49⟩, 12184, 32,
    ⟨3, 3410387802452679117, 3410387802452679118, 908086267⟩,
    ⟨461, 4718534616742505246, 4718534616742505247, 13662335249885330219⟩⟩,
  -- key: omega
  ⟨⟨⟨15, 1024, 39⟩, ⟨15, 512, 39⟩, 0, 0, 39⟩, 26851, 32,
    ⟨330, 3320909292276435225, 3320909292276435226, 14764002917195837190⟩,
    ⟨3, 2389880027195572508, 2389880027195572509, 5277028883⟩⟩,
  -- key: own
  ⟨⟨⟨15, 256, 29⟩, ⟨15, 256, 29⟩, 0, 0, 29⟩, 29702, 32,
    ⟨198, 1717330665785649474, 1717330665785649475, 8343698909693454954⟩,
    ⟨198, 1717330665785649474, 1717330665785649475, 8343698909693454954⟩⟩,
  -- entry: linked
  ⟨⟨⟨14, 512, 40⟩, ⟨14, 512, 40⟩, 0, 0, 40⟩, 13370, 32,
    ⟨320, 3382871897694436802, 3382871897694436803, 5989235087195079573⟩,
    ⟨320, 3382871897694436802, 3382871897694436803, 5989235087195079573⟩⟩]

/-- The nine last stages at the small size. -/
def lastSmall : List LastPlace := [
  -- proof: last
  ⟨⟨⟨15, 128, 73⟩, ⟨15, 4096, 73⟩, 0, 0, 73⟩, 21058, 20,
    ⟨3, 1441151880758558720, 1441151880758558720, 24062781892⟩,
    ⟨500, 6578980666694979968, 6578980666694979969, 15123852112153090666⟩⟩,
  -- proof: folded
  ⟨⟨⟨14, 2048, 68⟩, ⟨14, 1024, 68⟩, 0, 0, 68⟩, 10487, 28,
    ⟨567, 6627731996935651722, 6627731996935651723, 13861887214509903538⟩,
    ⟨3, 4760166330144986411, 4760166330144986412, 334000174⟩⟩,
  -- proof: omega
  ⟨⟨⟨15, 1024, 68⟩, ⟨15, 4096, 68⟩, 0, 0, 68⟩, 21065, 28,
    ⟨3, 3365945891621401849, 3365945891621401850, 1888989677⟩,
    ⟨500, 6575033356885801749, 6575033356885801750, 15151107202872580756⟩⟩,
  -- proof: own
  ⟨⟨⟨15, 1024, 73⟩, ⟨15, 4096, 73⟩, 0, 0, 73⟩, 21058, 20,
    ⟨3, 3373650058009624412, 3373650058009624413, 1876079656⟩,
    ⟨500, 6578980666694979968, 6578980666694979969, 15123852112153090666⟩⟩,
  -- key: ranges
  ⟨⟨⟨20, 2048, 22⟩, ⟨20, 1024, 22⟩, 0, 0, 22⟩, 1001368, 32,
    ⟨74, 819407644289022298, 819407644289022299, 18304132543402839982⟩,
    ⟨3, 582341728346042474, 582341728346042475, 11670203838897⟩⟩,
  -- key: folded
  ⟨⟨⟨14, 2048, 66⟩, ⟨14, 1024, 66⟩, 0, 0, 66⟩, 10490, 32,
    ⟨579, 6624597576331438045, 6624597576331438046, 15412622631318445410⟩,
    ⟨3, 4755801206503243776, 4755801206503243776, 334920486⟩⟩,
  -- key: omega
  ⟨⟨⟨15, 1024, 39⟩, ⟨15, 512, 39⟩, 0, 0, 39⟩, 26851, 32,
    ⟨330, 3320909292276435225, 3320909292276435226, 14764002917195837190⟩,
    ⟨3, 2389880027195572508, 2389880027195572509, 5277028883⟩⟩,
  -- key: own
  ⟨⟨⟨15, 1024, 39⟩, ⟨15, 512, 39⟩, 0, 0, 39⟩, 26851, 32,
    ⟨330, 3320909292276435225, 3320909292276435226, 14764002917195837190⟩,
    ⟨3, 2389880027195572508, 2389880027195572509, 5277028883⟩⟩,
  -- entry: linked
  ⟨⟨⟨14, 2048, 66⟩, ⟨14, 512, 66⟩, 0, 0, 66⟩, 10490, 32,
    ⟨579, 6624597576331438045, 6624597576331438046, 15412622631318445410⟩,
    ⟨3, 3461765611577187957, 3461765611577187958, 868226374⟩⟩]

theorem last_good : ((lastFull ++ lastSmall).all fun x => x.good) = true := by decide +kernel

theorem last_priced : ((lastFull ++ lastSmall).all fun x => x.priced) = true := by decide +kernel

/-- Twice the radius is at least the stage's distance: no theorem on radii below half a distance
applies at any of the eighteen. -/
theorem last_far : ((lastFull ++ lastSmall).all fun x => decide (x.s.d ≤ 2 * x.e)) = true := by
  decide +kernel

/-- The key file's four at full size are the list `keyLast`. -/
theorem lastFull_key :
    ((lastFull.drop 4).take 4).map (fun x => (x.s, x.e)) = Johnson.Top.H.keyLast := rfl

/-- The entry file's at full size is the last stage `frSg5`, at the radius of `frSg5_J`. -/
theorem lastFull_entry : (lastFull.drop 8).map (fun x => (x.s, x.e)) = [(frSg5, 13370)] := rfl

/-- The entry file's at the small size is the last stage `srSg3`, at the radius of `srSg3_J`. -/
theorem lastSmall_entry : (lastSmall.drop 8).map (fun x => (x.s, x.e)) = [(srSg3, 10490)] := rfl

/-- What is said of one place. dL, dB: any written rounds that are the format's own «BASE lambda»
and «BASE» at the place's stage and bits of work. -/
structure LastPlace.Paid (x : LastPlace) : Prop where
  /-- what the base case asks of its codes, at the place's two numbers -/
  codes : BaseCodes x.s x.e x.exc x.lst
  /-- so the base case is taken off, with the library's error counts at these two numbers -/
  holds : ∀ (dL dB : PQ.RD) (tree : ℕ), IsRd dL Fmt.M1.rLambda →
    IsRd dB (Fmt.M1.rBase x.work x.s.st tree) →
    BaseHolds x.s x.e dL dB (baseErr x.s x.e x.exc x.lst dL dB)
  /-- both of these error counts are at most 2^-128 of their rounds' written verifier messages -/
  below : ∀ (dL dB : PQ.RD) (tree : ℕ), IsRd dL Fmt.M1.rLambda →
    IsRd dB (Fmt.M1.rBase x.work x.s.st tree) →
    Err.Below (baseErr x.s x.e x.exc x.lst dL dB) ((2 : ℝ≥0∞)⁻¹ ^ 128)
  /-- the first round's count -/
  lambda : ∀ dL : PQ.RD, IsRd dL Fmt.M1.rLambda →
    RoundBelow (x.exc + x.lst) dL ((2 : ℝ≥0∞)⁻¹ ^ 128)
  /-- the second round's count likewise, the bits of work among the 128 -/
  base : ∀ (dB : PQ.RD) (tree : ℕ), IsRd dB (Fmt.M1.rBase x.work x.s.st tree) →
    RoundBelow ((2 ^ x.s.C.a - x.e - 1) ^ x.s.t) dB ((2 : ℝ≥0∞)⁻¹ ^ 128)

theorem LastPlace.paid {x : LastPlace} (hg : x.good = true) (hp : x.priced = true) : x.Paid :=
  have hs := (LastPlace.stageJ hg).sized
  have h64 : x.s.C.a ≤ 64 := le_trans hs.small (by decide)
  ⟨LastPlace.baseCodes hg,
    fun dL dB _ hL hB G col mk last hlast hno bad hpp H =>
      base_block x.s (LastPlace.oneRow hg).1 (LastPlace.oneRow hg).2 x.e x.exc x.lst dL dB
        (LastPlace.baseCodes hg) (rLambda_sd hL) (rBase_sd (s := x.s.st) hB h64) G col mk last hlast
        hno bad hpp H,
    fun dL dB _ hL hB => base_below_joh x.s x.e x.exc x.lst dL dB _
      (LastPlace.below_rLambda hp hL) (LastPlace.below_rBase hp h64 hB),
    fun _ hL => LastPlace.below_rLambda hp hL,
    fun _ _ hB => LastPlace.below_rBase hp h64 hB⟩

/-- **The premise on codes that the library's base block takes, at the written last stages.** -/
def LastPlacesPaid : Prop := ∀ x ∈ lastFull ++ lastSmall, x.Paid

theorem lastPlacesPaid : LastPlacesPaid := fun x hx =>
  LastPlace.paid (List.all_eq_true.1 last_good x hx) (List.all_eq_true.1 last_priced x hx)

end Johnson.Bridge

#print axioms Johnson.Bridge.last_good
#print axioms Johnson.Bridge.last_priced
#print axioms Johnson.Bridge.lastPlacesPaid
