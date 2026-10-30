-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/KeyRows.lean: the group of one sampled message of a sending of the programs, over
the signatures of Johnson/Pack/, as a value of `Rows`; and at full size the whole proximity test
in the proof of the ranges of a key file.

The signature of a sending is `sigOf` (Johnson/Pack/PortF.lean): a function of a chain's codes and
of the sampled messages' shapes, each with its radius. A message with main rows is read in its
test at the positions of its main code. The first stage's two codes are the shape's own (`sg1`),
so nothing has to be evaluated for the types to meet. The closed values are written out; the tests
on numbers are proved by evaluation. Definitions, statements and proofs.
Main names:
  `sg1 cs sh h g t`: the stage with a shape's two codes.
  `S1 N₁ cs sh em`: earlier messages beside the sending of the one shape sh at the radius em.
  `mbOne`, `famOne`, `rowsOne`: what is held of the member (`membPort`,
    Johnson/Top/H/MemberOf.lean); the family of that one message (Johnson/Top/H/Families.lean);
    the value of `Rows` (Johnson/Top/H/GroupRows.lean). Its rows begin at the corner 0.
  `famOne_ok`, `rowsOne_good`: `Fam.Ok` and `Rows.Good`, from `Sg.Sized` and four inequalities.
    `rowsOne_fits`: the joint radius implies the member's own, from two inequalities.
  `csKey`, `shIdx`, `shMul`: the codes of a key file's first chain; the shapes of the message of
    masks for the index and of the message with the multiplicities.
  `nIdx`, `nMul`, `meetIdx`, `meetMul`: the two signatures; the test of Johnson/Pack/Check.lean is
    true at both.
  `rRng`, `tRngP`, `rngTestP`, `rngTestP_know`: the group; the data of the test, all four stages;
    the arrangement and the test; it is knowledge sound under `CountsAt`
    (Johnson/Top/H/StageJ.lean) at its four stages.
Limits: as typed here the batched form is 0 on the rows of a block that no member sent, and by a
reading of the programs' text theirs is not: so these are not yet the tests that the programs run.
«Knowledge sound» is said with errors that are terms: nothing says that the errors are small. The
stages at any form are in Johnson/Top/H/FirstAt.lean. That these numbers are those of a key file
is not proved here: codes, shapes and radii were read off prints of the planner's own functions at
the example of full size. The prints were made by evaluating this library's port of the planner at
the three public files of the example set prover/examples/target_full_f2, held as constants by the
programs that printed (name, size, sha256):
  policy.txt (2,629 bytes) ce9e126bb3ba7179319a31981a3fc36ca505d738348971f379dfc795f94a3fae
  layout.txt (224,975 bytes) a99b964bbd3648d6e3b4007fc9370b5c70c7e9668848daa039820bc9e03e8f80
  KL.bin (2,784 bytes) 1c3191164c5113fd04d5108a469d7b3d17f4ccb3256e8a676d15bdc94435b919
These programs and the program that cut the numbers out of the prints are not in this repository.
The messages' radii (6130 and 3131959) are the upper ends of the planner's distances times the
codes' lengths, rounded down, as `Params.upperRadius` (OnBytes/Params/JohnsonLaws.lean) has them;
the test's radius at the first stage is 3131959. The condition on counts is not proved here. The
three other tests of a key file's chains stand on groups of several messages and are not laid here.
The main rows of the message with the multiplicities stand over the base field and are read here
under a code over the extension field (Johnson/Top/H/StageJ.lean): what is extracted is a message
over the extension field. That the first fold's mask was sent earlier is typed after a public flag
of the programs (`masksRide`, OnBytes/Iop/Wf.lean), which is not read here. `csKey` holds the codes
of all three chains of a key file, not of the first alone.

-/
import Johnson.Pack.Check
import Johnson.Pack.PortS
import Johnson.Top.H.Families
import Johnson.Top.H.FirstRows
import Johnson.Top.H.KeyTowers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes.Slice Cb Cb.Pv.Tower Johnson.Pack

section One
variable (N₁ : Sig GE) (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) (em h g t e : ℕ)

/-- The stage with a shape's two codes. -/
abbrev sg1 : Sg := ⟨cMain cs sh, cMask cs sh, h, g, t⟩

/-- Earlier messages beside the sending of the one shape. -/
noncomputable abbrev S1 : Sig GE := N₁.sum (sigOf cs [(sh, em)])

/-- What is held of the member. -/
noncomputable def mbOne : ∀ o : (S1 N₁ cs sh em).O, o.isRight = true →
    MembAt ((S1 N₁ cs sh em).om o) (sg1 cs sh h g t)
  | .inr ⟨0, _⟩, _ => membPort cs sh em (sg1 cs sh h g t) 0 0 (fun _ => rfl) (fun _ => rfl)
  | .inr ⟨_ + 1, k⟩, _ => absurd k (by simp)
  | .inl _, k => absurd k Bool.false_ne_true

/-- The family of that one message. -/
noncomputable def famOne : Fam (S1 N₁ cs sh em) (sg1 cs sh h g t) :=
  ⟨fun o => o.isRight = true, mbOne N₁ cs sh em h g t⟩

/-- The group of that one message. -/
noncomputable abbrev rowsOne : Rows (S1 N₁ cs sh em) := (famOne N₁ cs sh em h g t).rows e

theorem one_mem : ∀ a b : {o : (S1 N₁ cs sh em).O // o.isRight = true}, a = b
  | ⟨.inr ⟨0, _⟩, _⟩, ⟨.inr ⟨0, _⟩, _⟩ => rfl
  | ⟨.inr ⟨_ + 1, k⟩, _⟩, _ => absurd k (by simp)
  | _, ⟨.inr ⟨_ + 1, k⟩, _⟩ => absurd k (by simp)
  | ⟨.inl _, k⟩, _ => absurd k Bool.false_ne_true
  | _, ⟨.inl _, k⟩ => absurd k Bool.false_ne_true

theorem mbOne_laws (hA : aOf cs sh ≤ (cMain cs sh).a) :
    ∀ o k, (mbOne N₁ cs sh em h g t o k).view.Laws
  | .inr ⟨0, _⟩, _ => membPort_laws _ _ _ _ _ _ _ _ hA
  | .inr ⟨_ + 1, k⟩, _ => absurd k (by simp)
  | .inl _, k => absurd k Bool.false_ne_true

theorem mbOne_fitM (hM : sh.mainRows ≤ 2 ^ (h + g)) :
    ∀ o k, (mbOne N₁ cs sh em h g t o k).oM + (mbOne N₁ cs sh em h g t o k).nM ≤ 2 ^ (h + g)
  | .inr ⟨0, _⟩, _ => (Nat.zero_add sh.mainRows).le.trans hM
  | .inr ⟨_ + 1, k⟩, _ => absurd k (by simp)
  | .inl _, k => absurd k Bool.false_ne_true

theorem mbOne_fitZ (hZ : sh.maskRows ≤ 2 ^ h) :
    ∀ o k, (mbOne N₁ cs sh em h g t o k).oZ + (mbOne N₁ cs sh em h g t o k).nZ ≤ 2 ^ h
  | .inr ⟨0, _⟩, _ => (Nat.zero_add sh.maskRows).le.trans hZ
  | .inr ⟨_ + 1, k⟩, _ => absurd k (by simp)
  | .inl _, k => absurd k Bool.false_ne_true

theorem famOne_ok (hA : aOf cs sh ≤ (cMain cs sh).a) (hM : sh.mainRows ≤ 2 ^ (h + g))
    (hZ : sh.maskRows ≤ 2 ^ h) : (famOne N₁ cs sh em h g t).Ok where
  laws := mbOne_laws N₁ cs sh em h g t hA
  fitM := mbOne_fitM N₁ cs sh em h g t hM
  apartM := fun o k o' k' n =>
    absurd (congrArg Subtype.val (one_mem N₁ cs sh em ⟨o, k⟩ ⟨o', k'⟩)) n
  fitZ := mbOne_fitZ N₁ cs sh em h g t hZ
  apartZ := fun o k o' k' n =>
    absurd (congrArg Subtype.val (one_mem N₁ cs sh em ⟨o, k⟩ ⟨o', k'⟩)) n

theorem rowsOne_good (hs : (sg1 cs sh h g t).Sized) (hA : aOf cs sh ≤ (cMain cs sh).a)
    (hM : sh.mainRows ≤ 2 ^ (h + g)) (hZ : sh.maskRows ≤ 2 ^ h) (h1 : 1 ≤ h + g) :
    (rowsOne N₁ cs sh em h g t e).Good :=
  Fam.good e hs h1 (famOne_ok N₁ cs sh em h g t hA hM hZ)

/-- The joint radius implies the member's own. -/
theorem rowsOne_fits (hA : aOf cs sh ≤ (cMain cs sh).a)
    (he : e ≤ 2 ^ ((cMain cs sh).a - aOf cs sh) * em + (2 ^ ((cMain cs sh).a - aOf cs sh) - 1)) :
    (rowsOne N₁ cs sh em h g t e).G.Fits :=
  Fam.fits (F := famOne N₁ cs sh em h g t) fun o k =>
    match o, k with
    | .inr ⟨0, _⟩, _ => membPort_fits _ _ _ _ _ _ _ _ e hA he
    | .inr ⟨_ + 1, k⟩, _ => absurd k (by simp)
    | .inl _, k => absurd k Bool.false_ne_true

end One

/-! ### a key file's first chain at full size -/

/-- The codes of the chain: main rows' and mask rows', as (logarithm of the length, entries of a
message, random entries). -/
def csKey : OnBytes.Codes where
  base := #[⟨24, 4194304, 97⟩, ⟨21, 131072, 52⟩, ⟨17, 8192, 52⟩, ⟨13, 512, 52⟩, ⟨14, 512, 49⟩,
    ⟨22, 262144, 98⟩, ⟨18, 16384, 49⟩, ⟨14, 1024, 49⟩, ⟨15, 1024, 39⟩, ⟨15, 2048, 49⟩,
    ⟨13, 256, 41⟩, ⟨15, 256, 29⟩, ⟨22, 262144, 49⟩, ⟨19, 16384, 39⟩, ⟨17, 2048, 33⟩,
    ⟨20, 2048, 25⟩]
  mask := #[⟨13, 64, 146⟩, ⟨12, 256, 52⟩, ⟨14, 1024, 49⟩, ⟨14, 128, 49⟩, ⟨13, 64, 49⟩,
    ⟨15, 512, 39⟩, ⟨13, 256, 49⟩, ⟨15, 128, 49⟩, ⟨14, 64, 49⟩, ⟨13, 64, 41⟩, ⟨15, 256, 29⟩,
    ⟨16, 4096, 49⟩, ⟨17, 2048, 39⟩, ⟨17, 1024, 33⟩, ⟨20, 4096, 25⟩]

/-- The message of masks for the index: one mask row under mask code 6. -/
def shIdx : OnBytes.OracleShape :=
  { code := OnBytes.noId, mainRows := 0, mainDeg := 1, maskRows := 1, maskCode := 6, answers := 1 }

/-- The multiplicities: two main rows over the base field under code 12, nine mask rows under mask
code 11. -/
def shMul : OnBytes.OracleShape :=
  { code := 12, mainRows := 2, mainDeg := 1, maskRows := 9, maskCode := 11, answers := 1 }

noncomputable abbrev nIdx : Sig GE := sigOf csKey [(shIdx, 6130)]
noncomputable abbrev nMul : Sig GE := sigOf csKey [(shMul, 3131959)]

theorem meetIdx : allMeet csKey [(shIdx, 6130)] = true := by decide +kernel
theorem meetMul : allMeet csKey [(shMul, 3131959)] = true := by decide +kernel

/-- The first stage of the test in the proof of the ranges, with the shape's own codes. -/
abbrev sRngP : Sg := sg1 csKey shMul 4 0 49

theorem gRngP : (sizedB sRngP && inJB sRngP eRng1) = true := by decide +kernel
theorem fRngP : CsFit sRngP sRng2 := by decide +kernel

/-- The group of the message with the multiplicities. -/
noncomputable abbrev rRng : Rows (S1 nIdx csKey shMul 3131959) :=
  rowsOne nIdx csKey shMul 3131959 4 0 49 eRng1

theorem rRng_good : rRng.Good :=
  rowsOne_good nIdx csKey shMul 3131959 4 0 49 eRng1 (szd gRngP) (by decide +kernel) (by decide)
    (by decide) (by decide)

theorem rRng_fits : rRng.G.Fits :=
  rowsOne_fits nIdx csKey shMul 3131959 4 0 49 eRng1 (by decide +kernel) (by decide +kernel)

theorem rRng_list : rRng.G.C.ListAt rRng.G.e (lstJ sRngP eRng1) := rRng.list rRng_good (inj gRngP)

variable (bC bZ : Sg → ℕ → ℕ) {B : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) rRng.G.C.J) (Z : Evader GE (rRng.G.Row B))

/-- The data of the test: all four stages. -/
noncomputable def tRngP :
    TowR (wholeJ rRng.Sh.par (rRng.Sh.form Sb sl Z) rRng.G.e) rRng.Sh.par.Cw.nat :=
  rRng.step Sb sl Z fRngP eRng2 (bC sRngP eRng1) (bZ sRngP eRng1)
    (tRng2 bC bZ ((rRng.sw Sb sl Z fRngP).D rRng.G.e).sl')

theorem tRngP_hypK (h1 : CountsAt sRngP eRng1 (bC sRngP eRng1) (bZ sRngP eRng1))
    (hc : cRng bC bZ) : (tRngP bC bZ Sb sl Z).HypK :=
  rRng.step_hypK Sb sl Z fRngP _ rRng_good (szd gRng2) (inj gRngP) (inj gRng2) h1
    (tRng2_hypK bC bZ hc _)

theorem tRngP_reads : (tRngP bC bZ Sb sl Z).Reads :=
  rRng.step_reads Sb sl Z fRngP _ _ _ _ (szd gRng2) (tRng2_reads bC bZ _)

/-- The arrangement and the test, from the joint at which the round before the test ends. -/
noncomputable def rngTestP : EndR (rRng.G.joint Sb sl Z) rRng.Sh.par.Cw.nat :=
  rRng.test Sb sl Z (tRngP bC bZ Sb sl Z)

/-- It is knowledge sound under the two conditions on counts. -/
theorem rngTestP_know (h1 : CountsAt sRngP eRng1 (bC sRngP eRng1) (bZ sRngP eRng1))
    (hc : cRng bC bZ) : (rngTestP bC bZ Sb sl Z).Know :=
  rRng.test_know Sb sl Z _ rRng_good (tRngP_hypK bC bZ Sb sl Z h1 hc)

end Johnson.Top.H

#print axioms Johnson.Top.H.rowsOne_good
#print axioms Johnson.Top.H.rowsOne_fits
#print axioms Johnson.Top.H.rngTestP_know
