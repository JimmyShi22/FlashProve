-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/KeyFamilies.lean: the groups of the three proximity tests that close the test on a
key file's stored table, at full size, as families over one signature; and each whole test,
knowledge sound under one condition on counts.

The signature holds what the proof of the ranges keeps, then the sendings of W, of the folded row,
and of Omega with the split's mask message (`sigOf`, Johnson/Pack/PortF.lean). The tests run in
the order: the folded row's, Omega's, the own test. A later test stands over the messages that the
earlier ones keep (`Fam.sub`, Johnson/Top/H/Families.lean). The first stage of each test has the
members' own codes. The stages behind the first are those of Johnson/Top/H/KeyTowers.lean. The
tests on numbers are proved by evaluation. Definitions, statements and proofs.
Main names:
  `shW`, `shU`, `shO`, `shSp`; `nW`, `nU`, `nO`; `meetW`, `meetU`, `meetO`: the shapes; the three
    sendings' signatures; the test of Johnson/Pack/Check.lean is true at each.
  `saK`, `sK`: what the proof of the ranges keeps; the whole signature.
  `sRowP`, `sOmgP`, `sOwnP`: the three first stages.
  `fRow`, `fOmg`, `fOwn`: the families: the folded row and the split's mask message; Omega and the
    split's mask message; the message of masks for the index, W and Omega. The first corners of
    the blocks: rows by decreasing size of block, ties in the order named.
  `tot`, `apart_tot`: that the blocks of two members do not overlap, as a test over all names.
  `fRow_ok`, `fRow_fits` and the like: `Fam.Ok` and `Fam.FitsAt`.
  `keepRow`, `keepOmg`, `kp₁`, `kp₂`: the first test keeps the split's mask message, the second
    keeps Omega; the messages behind each.
  `rRow`, `rOmg`, `rOwn`: the three groups' data.
  `Rows.stepOwn`, `Rows.testOwn`, `Rows.testOwn_know`: a first stage whose fold sends its own
    mask, and the whole test, for any group.
  `rowTestP_know`, `omgTestP_know`, `ownTestP_know`: each whole test is knowledge sound under
    `CountsAt` (Johnson/Top/H/StageJ.lean) at all its stages.
Limits: as typed here the batched form is 0 on the rows of a block that no member sent, and by a
reading of the programs' text theirs is not: so these are not yet the tests that the programs run.
«Knowledge sound» is said with errors that are terms: nothing says that the errors are small. The
stages at any form are in Johnson/Top/H/FirstAt.lean. That these numbers, the members of each
group, the order of the tests and what each keeps are those of a key file is not proved here: they
were read off prints of the planner's own functions at the example of full size and off the text
of the verifier that is written after the programs. The first corners were worked out by hand
after the rule of that text. The prints were made by evaluating this library's port of the planner
at the three public files of the example set prover/examples/target_full_f2, held as constants by
the programs that printed (name, size, sha256):
  policy.txt (2,629 bytes) ce9e126bb3ba7179319a31981a3fc36ca505d738348971f379dfc795f94a3fae
  layout.txt (224,975 bytes) a99b964bbd3648d6e3b4007fc9370b5c70c7e9668848daa039820bc9e03e8f80
  KL.bin (2,784 bytes) 1c3191164c5113fd04d5108a469d7b3d17f4ccb3256e8a676d15bdc94435b919
These programs and the program that cut the numbers out of the prints are not in this repository.
The condition on counts is not proved here. How this signature meets the signature of a description
of a key file's protocol is not treated. `Fam.sub` cuts a family down without a word where a member
is not kept: that no member is lost here, and that no message is left behind the third test, is not
shown here. Which test's first fold sends its own mask is typed after public flags of the programs
(`masksRide`, OnBytes/Iop/Wf.lean; `masksAhead`, OnBytes/Iop/Lin.lean), which are not read here.
One signature holds the messages of three hash chains; Omega, sent in the second, is taken into
the third test's group. «Keeps» (`keepRow`, `keepOmg`) means here: the message is read again
behind the test; it is not the layout's mark `kept`. The names `shW`, `shU`, `shO` stand for other
values in Johnson/Pack/Check.lean; here they are this file's.

-/
import Johnson.Top.H.Families
import Johnson.Top.H.KeyRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes.Slice Cb Cb.Pv.Tower Johnson.Pack

/-! ### a first stage whose fold sends its own mask -/

namespace Rows
variable {S : Sig GE} (R : Rows S) {s' : Sg} {B : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B))

/-- The first stage, its fold sending its own mask, then the remainder. -/
noncomputable def stepOwn (hf : CsFit R.s s') (e' bC bZ : ℕ)
    (rest : TowR (((R.sw Sb sl Z hf).D R.G.e).jOut e') (s'.par s'.Z.l).Cw.nat) :
    EndO (wholeJ R.Sh.par (R.Sh.form Sb sl Z) R.G.e) :=
  ownStep R.Sh.par (R.Sh.form Sb sl Z) R.G.e (1, 1) (R.sw Sb sl Z hf) (s'.par s'.Z.l).Cw s'.Ps
    (Sum.elim id id) id R.s.d (fun _ => lstJ R.s R.e) (fun _ => bC) (fun _ => bZ) (fun _ => bZ)
    e' (lstJ s' e') rest

/-- The arrangement and the whole test. -/
noncomputable def testOwn (hf : CsFit R.s s') (e' bC bZ : ℕ)
    (rest : TowR (((R.sw Sb sl Z hf).D R.G.e).jOut e') (s'.par s'.Z.l).Cw.nat) :
    EndO (R.G.joint Sb sl Z) :=
  Cb.Pv.Tower.testOwn R.Sh Sb sl Z (R.stepOwn Sb sl Z hf e' bC bZ rest)

theorem testOwn_know (hf : CsFit R.s s') {e' bC bZ : ℕ}
    (rest : TowR (((R.sw Sb sl Z hf).D R.G.e).jOut e') (s'.par s'.Z.l).Cw.nat)
    (h : R.Good) (hs' : s'.Sized) (hj : InJ R.s R.e) (hj' : InJ s' e')
    (hc : CountsAt R.s R.e bC bZ) (hr : rest.HypK) :
    (R.testOwn Sb sl Z hf e' bC bZ rest).Know :=
  Cb.Pv.Tower.testOwn_know R.Sh Sb sl Z _ (R.sh_ok h)
    (ownStep_know _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rest (R.hypK Sb sl Z h hj hc)
      (R.sw_hypK Sb sl Z hf _ h.sized hs' hj') hr)

end Rows

/-! ### blocks that do not overlap, as a test over the names -/

/-- A number that is held of each member, as a function of all names: 0 at a name that is none. -/
def tot {X : Type} (mem : X → Prop) [DecidablePred mem] (f : ∀ x, mem x → ℕ) (x : X) : ℕ :=
  if k : mem x then f x k else 0

/-- The blocks of two different members do not overlap, from the same on the total functions. -/
theorem apart_tot {X : Type} (mem : X → Prop) [DecidablePred mem] (o n : ∀ x, mem x → ℕ)
    (h : ∀ x y, mem x → mem y → x ≠ y →
      tot mem o x + tot mem n x ≤ tot mem o y ∨ tot mem o y + tot mem n y ≤ tot mem o x) :
    ∀ x k y k', x ≠ y → o x k + n x k ≤ o y k' ∨ o y k' + n y k' ≤ o x k := by
  intro x k y k' hne
  have g := h x y k k' hne
  simp only [tot, dif_pos k, dif_pos k'] at g
  exact g

/-! ### the shapes and the signature -/

/-- W: one main row under code 5, one mask row under mask code 6. -/
def shW : OnBytes.OracleShape :=
  { code := 5, mainRows := 1, mainDeg := 3, maskRows := 1, maskCode := 6, answers := 1 }

/-- The folded row: 107 main rows under code 0. -/
def shU : OnBytes.OracleShape :=
  { code := 0, mainRows := 107, mainDeg := 3, maskRows := 0, maskCode := OnBytes.noId,
    answers := 1 }

/-- Omega: twelve main rows under code 5. -/
def shO : OnBytes.OracleShape :=
  { code := 5, mainRows := 12, mainDeg := 3, maskRows := 0, maskCode := OnBytes.noId,
    answers := 1 }

/-- The split's mask message: one mask row under mask code 0. -/
def shSp : OnBytes.OracleShape :=
  { code := OnBytes.noId, mainRows := 0, mainDeg := 1, maskRows := 1, maskCode := 0, answers := 1 }

noncomputable abbrev nW : Sig GE := sigOf csKey [(shW, 3138896)]
noncomputable abbrev nU : Sig GE := sigOf csKey [(shU, 8342420)]
noncomputable abbrev nO : Sig GE := sigOf csKey [(shO, 3138896), (shSp, 6130)]

theorem meetW : allMeet csKey [(shW, 3138896)] = true := by decide +kernel
theorem meetU : allMeet csKey [(shU, 8342420)] = true := by decide +kernel
theorem meetO : allMeet csKey [(shO, 3138896), (shSp, 6130)] = true := by decide +kernel

/-- What the proof of the ranges keeps: the messages that are no members of its group. -/
noncomputable abbrev saK : Sig GE :=
  (S1 nIdx csKey shMul 3131959).sub fun o => ¬ rRng.G.mem o ∨ False

/-- The whole signature. -/
noncomputable abbrev sK : Sig GE := ((saK.sum nW).sum nU).sum nO

/-- Whether two names are one can be evaluated by the kernel: found once, so that a test over pairs
of names finds it at once. -/
noncomputable instance decK : DecidableEq sK.O := inferInstance

/-- The three first stages, with the members' own codes. -/
abbrev sRowP : Sg := ⟨cMain csKey shU, cMask csKey shSp, 0, 7, 97⟩
abbrev sOmgP : Sg := ⟨cMain csKey shO, cMask csKey shSp, 0, 4, 49⟩
abbrev sOwnP : Sg := ⟨cMain csKey shW, cMask csKey shW, 1, 4, 49⟩

theorem gRowP : (sizedB sRowP && inJB sRowP eRow1) = true := by decide +kernel
theorem gOmgP : (sizedB sOmgP && inJB sOmgP eOmg1) = true := by decide +kernel
theorem gOwnP : (sizedB sOwnP && inJB sOwnP eOwn1) = true := by decide +kernel
theorem fRowP : CsFit sRowP sRow2 := by decide +kernel
theorem fOmgP : CsFit sOmgP sOmg2 := by decide +kernel
theorem fOwnP : CsFit sOwnP sOwn2 := by decide +kernel

/-! ### the folded row's test -/

def memRow : sK.O → Bool
  | .inl (.inr _) => true
  | .inr ⟨1, _⟩ => true
  | .inr ⟨0, _⟩ => false
  | .inr ⟨_ + 2, _⟩ => false
  | .inl (.inl _) => false

noncomputable def mbRow : ∀ o, memRow o = true → MembAt (sK.om o) sRowP
  | .inl (.inr ⟨0, _⟩), _ =>
    membPort csKey shU 8342420 sRowP 0 0 (fun _ => rfl) (fun h => absurd rfl h)
  | .inl (.inr ⟨_ + 1, k⟩), _ => absurd k (by simp)
  | .inr ⟨1, _⟩, _ => membPort csKey shSp 6130 sRowP 0 0 (fun h => absurd rfl h) (fun _ => rfl)
  | .inr ⟨0, _⟩, k => absurd k Bool.false_ne_true
  | .inr ⟨_ + 2, k⟩, _ => absurd k (by simp)
  | .inl (.inl _), k => absurd k Bool.false_ne_true

/-- The folded row and the split's mask message. -/
noncomputable def fRow : Fam sK sRowP := ⟨fun o => memRow o = true, mbRow⟩

theorem fRow_laws : ∀ o k, (mbRow o k).view.Laws
  | .inl (.inr ⟨0, _⟩), _ => membPort_laws _ _ _ _ _ _ _ _ (by decide +kernel)
  | .inl (.inr ⟨_ + 1, k⟩), _ => absurd k (by simp)
  | .inr ⟨1, _⟩, _ => membPort_laws _ _ _ _ _ _ _ _ (by decide +kernel)
  | .inr ⟨0, _⟩, k => absurd k Bool.false_ne_true
  | .inr ⟨_ + 2, k⟩, _ => absurd k (by simp)
  | .inl (.inl _), k => absurd k Bool.false_ne_true

theorem fRow_ok : fRow.Ok where
  laws := fRow_laws
  fitM := by decide +kernel
  apartM := apart_tot (fun o => memRow o = true) (fun o k => (mbRow o k).oM)
    (fun o k => (mbRow o k).nM) (by decide +kernel)
  fitZ := by decide +kernel
  apartZ := apart_tot (fun o => memRow o = true) (fun o k => (mbRow o k).oZ)
    (fun o k => (mbRow o k).nZ) (by decide +kernel)

theorem fRow_fits : fRow.FitsAt eRow1
  | .inl (.inr ⟨0, _⟩), _ => membPort_fits _ _ _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel)
  | .inl (.inr ⟨_ + 1, k⟩), _ => absurd k (by simp)
  | .inr ⟨1, _⟩, _ => membPort_fits _ _ _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel)
  | .inr ⟨0, _⟩, k => absurd k Bool.false_ne_true
  | .inr ⟨_ + 2, k⟩, _ => absurd k (by simp)
  | .inl (.inl _), k => absurd k Bool.false_ne_true

/-! ### Omega's test -/

def memOmg : sK.O → Bool
  | .inr _ => true
  | .inl _ => false

noncomputable def mbOmg : ∀ o, memOmg o = true → MembAt (sK.om o) sOmgP
  | .inr ⟨0, _⟩, _ =>
    membPort csKey shO 3138896 sOmgP 0 0 (fun _ => rfl) (fun h => absurd rfl h)
  | .inr ⟨1, _⟩, _ => membPort csKey shSp 6130 sOmgP 0 0 (fun h => absurd rfl h) (fun _ => rfl)
  | .inr ⟨_ + 2, k⟩, _ => absurd k (by simp)
  | .inl _, k => absurd k Bool.false_ne_true

/-- Omega and the split's mask message. -/
noncomputable def fOmg : Fam sK sOmgP := ⟨fun o => memOmg o = true, mbOmg⟩

theorem fOmg_laws : ∀ o k, (mbOmg o k).view.Laws
  | .inr ⟨0, _⟩, _ => membPort_laws _ _ _ _ _ _ _ _ (by decide +kernel)
  | .inr ⟨1, _⟩, _ => membPort_laws _ _ _ _ _ _ _ _ (by decide +kernel)
  | .inr ⟨_ + 2, k⟩, _ => absurd k (by simp)
  | .inl _, k => absurd k Bool.false_ne_true

theorem fOmg_ok : fOmg.Ok where
  laws := fOmg_laws
  fitM := by decide +kernel
  apartM := apart_tot (fun o => memOmg o = true) (fun o k => (mbOmg o k).oM)
    (fun o k => (mbOmg o k).nM) (by decide +kernel)
  fitZ := by decide +kernel
  apartZ := apart_tot (fun o => memOmg o = true) (fun o k => (mbOmg o k).oZ)
    (fun o k => (mbOmg o k).nZ) (by decide +kernel)

theorem fOmg_fits : fOmg.FitsAt eOmg1
  | .inr ⟨0, _⟩, _ => membPort_fits _ _ _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel)
  | .inr ⟨1, _⟩, _ => membPort_fits _ _ _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel)
  | .inr ⟨_ + 2, k⟩, _ => absurd k (by simp)
  | .inl _, k => absurd k Bool.false_ne_true

/-! ### the own test -/

def memOwn : sK.O → Bool
  | .inl (.inl (.inl a)) => a.1.isLeft
  | .inl (.inl (.inr _)) => true
  | .inl (.inr _) => false
  | .inr ⟨0, _⟩ => true
  | .inr ⟨_ + 1, _⟩ => false

noncomputable def mbOwn : ∀ o, memOwn o = true → MembAt (sK.om o) sOwnP
  | .inl (.inl (.inl ⟨.inl ⟨0, _⟩, _⟩)), _ =>
    membPort csKey shIdx 6130 sOwnP 0 0 (fun h => absurd rfl h) (fun _ => rfl)
  | .inl (.inl (.inl ⟨.inl ⟨_ + 1, k⟩, _⟩)), _ => absurd k (by simp)
  | .inl (.inl (.inl ⟨.inr _, _⟩)), k => absurd k Bool.false_ne_true
  | .inl (.inl (.inr ⟨0, _⟩)), _ =>
    membPort csKey shW 3138896 sOwnP 16 1 (fun _ => rfl) (fun _ => rfl)
  | .inl (.inl (.inr ⟨_ + 1, k⟩)), _ => absurd k (by simp)
  | .inl (.inr _), k => absurd k Bool.false_ne_true
  | .inr ⟨0, _⟩, _ =>
    membPort csKey shO 3138896 sOwnP 0 0 (fun _ => rfl) (fun h => absurd rfl h)
  | .inr ⟨_ + 1, _⟩, k => absurd k Bool.false_ne_true

/-- The message of masks for the index, W and Omega. -/
noncomputable def fOwn : Fam sK sOwnP := ⟨fun o => memOwn o = true, mbOwn⟩

theorem fOwn_laws : ∀ o k, (mbOwn o k).view.Laws
  | .inl (.inl (.inl ⟨.inl ⟨0, _⟩, _⟩)), _ => membPort_laws _ _ _ _ _ _ _ _ (by decide +kernel)
  | .inl (.inl (.inl ⟨.inl ⟨_ + 1, k⟩, _⟩)), _ => absurd k (by simp)
  | .inl (.inl (.inl ⟨.inr _, _⟩)), k => absurd k Bool.false_ne_true
  | .inl (.inl (.inr ⟨0, _⟩)), _ => membPort_laws _ _ _ _ _ _ _ _ (by decide +kernel)
  | .inl (.inl (.inr ⟨_ + 1, k⟩)), _ => absurd k (by simp)
  | .inl (.inr _), k => absurd k Bool.false_ne_true
  | .inr ⟨0, _⟩, _ => membPort_laws _ _ _ _ _ _ _ _ (by decide +kernel)
  | .inr ⟨_ + 1, _⟩, k => absurd k Bool.false_ne_true

theorem fOwn_ok : fOwn.Ok where
  laws := fOwn_laws
  fitM := by decide +kernel
  apartM := apart_tot (fun o => memOwn o = true) (fun o k => (mbOwn o k).oM)
    (fun o k => (mbOwn o k).nM) (by decide +kernel)
  fitZ := by decide +kernel
  apartZ := apart_tot (fun o => memOwn o = true) (fun o k => (mbOwn o k).oZ)
    (fun o k => (mbOwn o k).nZ) (by decide +kernel)

theorem fOwn_fits : fOwn.FitsAt eOwn1
  | .inl (.inl (.inl ⟨.inl ⟨0, _⟩, _⟩)), _ =>
    membPort_fits _ _ _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel)
  | .inl (.inl (.inl ⟨.inl ⟨_ + 1, k⟩, _⟩)), _ => absurd k (by simp)
  | .inl (.inl (.inl ⟨.inr _, _⟩)), k => absurd k Bool.false_ne_true
  | .inl (.inl (.inr ⟨0, _⟩)), _ =>
    membPort_fits _ _ _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel)
  | .inl (.inl (.inr ⟨_ + 1, k⟩)), _ => absurd k (by simp)
  | .inl (.inr _), k => absurd k Bool.false_ne_true
  | .inr ⟨0, _⟩, _ => membPort_fits _ _ _ _ _ _ _ _ _ (by decide +kernel) (by decide +kernel)
  | .inr ⟨_ + 1, _⟩, k => absurd k Bool.false_ne_true

/-! ### the three groups, each over what the earlier tests keep -/

/-- The folded row's group. -/
noncomputable abbrev rRow : Rows sK := fRow.rows eRow1

/-- The first test keeps the split's mask message. -/
def keepRow : sK.O → Bool
  | .inr ⟨1, _⟩ => true
  | .inr ⟨0, _⟩ => false
  | .inr ⟨_ + 2, _⟩ => false
  | .inl _ => false

/-- The messages behind the first test. -/
abbrev kp₁ : sK.O → Prop := fun o => ¬ rRow.G.mem o ∨ keepRow o = true

/-- Omega's group. -/
noncomputable abbrev rOmg : Rows (sK.sub kp₁) := (fOmg.sub kp₁).rows eOmg1

/-- The second test keeps Omega. -/
def keepOmg : (sK.sub kp₁).O → Bool
  | ⟨.inr ⟨0, _⟩, _⟩ => true
  | ⟨.inr ⟨_ + 1, _⟩, _⟩ => false
  | ⟨.inl _, _⟩ => false

/-- The messages behind the second test. -/
abbrev kp₂ : (sK.sub kp₁).O → Prop := fun a => ¬ rOmg.G.mem a ∨ keepOmg a = true

/-- The own test's group. -/
noncomputable abbrev rOwn : Rows ((sK.sub kp₁).sub kp₂) := ((fOwn.sub kp₁).sub kp₂).rows eOwn1

theorem rRow_good : rRow.Good := Fam.good eRow1 (szd gRowP) (by decide) fRow_ok
theorem rOmg_good : rOmg.Good := Fam.good eOmg1 (szd gOmgP) (by decide) (fOmg_ok.sub kp₁)
theorem rOwn_good : rOwn.Good :=
  Fam.good eOwn1 (szd gOwnP) (by decide) ((fOwn_ok.sub kp₁).sub kp₂)

theorem rRow_fits : rRow.G.Fits := Fam.fits fRow_fits
theorem rOmg_fits : rOmg.G.Fits := Fam.fits (fOmg_fits.sub kp₁)
theorem rOwn_fits : rOwn.G.Fits := Fam.fits ((fOwn_fits.sub kp₁).sub kp₂)

/-! ### the three whole tests -/

section Tests
variable (bC bZ : Sg → ℕ → ℕ) {B : Type} [Fintype B] (Sb : B → Type)

/-- The folded row's test: the first fold's mask was sent earlier. -/
noncomputable def rowTestP (sl : ∀ b, Slf GE (Sb b) rRow.G.C.J) (Z : Evader GE (rRow.G.Row B)) :
    EndR (rRow.G.joint Sb sl Z) rRow.Sh.par.Cw.nat :=
  rRow.test Sb sl Z (rRow.step Sb sl Z fRowP eRow2 (bC sRowP eRow1) (bZ sRowP eRow1)
    (tRow2 bC bZ ((rRow.sw Sb sl Z fRowP).D rRow.G.e).sl'))

theorem rowTestP_know (sl : ∀ b, Slf GE (Sb b) rRow.G.C.J) (Z : Evader GE (rRow.G.Row B))
    (h1 : CountsAt sRowP eRow1 (bC sRowP eRow1) (bZ sRowP eRow1)) (hc : cRow bC bZ) :
    (rowTestP bC bZ Sb sl Z).Know :=
  rRow.test_know Sb sl Z _ rRow_good
    (rRow.step_hypK Sb sl Z fRowP _ rRow_good (szd gRow2) (inj gRowP) (inj gRow2) h1
      (tRow2_hypK bC bZ hc _))

/-- Omega's test: the first fold sends its own mask. -/
noncomputable def omgTestP (sl : ∀ b, Slf GE (Sb b) rOmg.G.C.J) (Z : Evader GE (rOmg.G.Row B)) :
    EndO (rOmg.G.joint Sb sl Z) :=
  rOmg.testOwn Sb sl Z fOmgP eOmg2 (bC sOmgP eOmg1) (bZ sOmgP eOmg1)
    (tOmg2 bC bZ ((rOmg.sw Sb sl Z fOmgP).D rOmg.G.e).sl')

theorem omgTestP_know (sl : ∀ b, Slf GE (Sb b) rOmg.G.C.J) (Z : Evader GE (rOmg.G.Row B))
    (h1 : CountsAt sOmgP eOmg1 (bC sOmgP eOmg1) (bZ sOmgP eOmg1)) (hc : cOmg bC bZ) :
    (omgTestP bC bZ Sb sl Z).Know :=
  rOmg.testOwn_know Sb sl Z fOmgP _ rOmg_good (szd gOmg2) (inj gOmgP) (inj gOmg2) h1
    (tOmg2_hypK bC bZ hc _)

/-- The own test: the first fold's mask was sent earlier. -/
noncomputable def ownTestP (sl : ∀ b, Slf GE (Sb b) rOwn.G.C.J) (Z : Evader GE (rOwn.G.Row B)) :
    EndR (rOwn.G.joint Sb sl Z) rOwn.Sh.par.Cw.nat :=
  rOwn.test Sb sl Z (rOwn.step Sb sl Z fOwnP eOwn2 (bC sOwnP eOwn1) (bZ sOwnP eOwn1)
    (tOwn2 bC bZ ((rOwn.sw Sb sl Z fOwnP).D rOwn.G.e).sl'))

theorem ownTestP_know (sl : ∀ b, Slf GE (Sb b) rOwn.G.C.J) (Z : Evader GE (rOwn.G.Row B))
    (h1 : CountsAt sOwnP eOwn1 (bC sOwnP eOwn1) (bZ sOwnP eOwn1)) (hc : cOwn bC bZ) :
    (ownTestP bC bZ Sb sl Z).Know :=
  rOwn.test_know Sb sl Z _ rOwn_good
    (rOwn.step_hypK Sb sl Z fOwnP _ rOwn_good (szd gOwn2) (inj gOwnP) (inj gOwn2) h1
      (tOwn2_hypK bC bZ hc _))

end Tests

end Johnson.Top.H

#print axioms Johnson.Top.H.rowTestP_know
#print axioms Johnson.Top.H.omgTestP_know
#print axioms Johnson.Top.H.ownTestP_know
