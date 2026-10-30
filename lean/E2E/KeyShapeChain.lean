--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeChain.lean: THE LETTERS OF THE CUT "STRUCTURE | VALUES" FOR THE KEY FILE's THIRD CHAIN,
LAID TOGETHER: one value `Z₃` of Johnson/Desc/ProofFile/Honest/Thread/Shape.lean's type `Shape` over
the chain's four sub-protocols, with (B1) `Carries` and (B2) `Returns` at three of them shown AT THE
DESCRIPTION's OWN FLAT LIST, and at the fourth (the own proximity test) from the two forms for one
run, as premises. With evaluations in Lean's kernel at the full size's shapes and codes.
Definitions, statements and proofs. NOTHING IS SHOWN OF ANY PROVER: no completeness.

  **`Z₃ S rounds gOwn vOwn`**: the shape `Sh₃`, the reader `sh₃ S`; g: number 0 `gSecond S` · 1
    `gSources rounds` · 2 gOwn · 3 `gEnd`; the named tests on values: number 0 `vSecond S` ("no
    coefficient on a pad") · 2 vOwn · none at 1 and 3. gOwn, vOwn: letters: the own proximity
    test's.
  `Z₃At X P gOwn vOwn`: at the description's own public values.
  **`carries₀`**, **`carries₁`**, **`carries₃`**, **`returns₀`**, **`returns₁`**, **`returns₃`**: at
    the flat list of `(keyFileDescription X N P).second`. `carries₂`, `returns₂`: from the two forms at the own
    test's decision.
  **`carries_all`**: (B1) at every number.

EVALUATIONS, at the written values of the full size (`SF`, `CF`; the own test's written rounds),
from the shape of E2E/KeySecondMember.lean's synthetic state:
  `aF`: that state's shape, WRITTEN OUT, not read off the state. `aF_is`: it is the reader's value
    at `sF`: by the kernel.
  **`yes_two`**: the shape's own run over the first two sub-protocols returns: by the kernel.
  **`no_mark`**, **`no_border`**, **`no_tree`**: three negative tests: without the mark on the row
    weights; without the two ends; with another number at W's tree: the run rejects.

Limits.
- The own proximity test's g is a letter. So the named public premise (`Shape.yes`) over
  all four sub-protocols is not evaluated.
- The first shape is a synthetic state's: three messages in place of a run's eleven; row weights
  without a written-out factor, where the key file's have one.
- That a run's first shape has the marks is not shown.


-/
import E2E.KeyShapeSecond
import E2E.KeyShapeDoor
import E2E.KeySources

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.AtFiles
open OnBytes
open OnBytes.Params (LinShape)
open ProofFile.Honest (Shape Carries Returns CarriesR ReturnsR carries_seat returns_seat)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Third (S₃)

/-- **The letters of the cut, for the third chain.** -/
def Z₃ (S : LinShape) (rounds : List Fmt.DeclaredRound) (gOwn : Sh₃ → Except String Sh₃)
    (vOwn : S₃ → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) : Shape S₃ where
  Sh := Sh₃
  sh := sh₃ S
  g := fun b => match b with
    | 0 => gSecond S
    | 1 => gSources rounds
    | 2 => gOwn
    | _ => gEnd
  vals := fun b s rs gs => match b with
    | 0 => vSecond S s
    | 2 => vOwn s rs gs
    | _ => true

section At
variable (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (P : VerifiableInference.Desc.Key.LaterPlaces) (gOwn : Sh₃ → Except String Sh₃)
  (vOwn : S₃ → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) (ft : Nat)

/-- At the description's own public values. -/
abbrev Z₃At : Shape S₃ :=
  Z₃ X.chains.made.sized.key.once.shape (VerifiableInference.Desc.Key.ownTest P).rounds gOwn vOwn

theorem carries₀ : Carries (keyFileDescription X N P).second.blocksInOrder ft (Z₃At X P gOwn vOwn) 0 := by
  obtain ⟨blk, e, hd⟩ : ∃ blk, (keyFileDescription X N P).second.blocksInOrder[0]? = some blk ∧
      blk.decide = (VerifiableInference.Desc.Third.batchLinearConstraintsSecondPart (Cl := Unit)
        (VerifiableInference.Desc.Key.thirdPar X.chains)).decide := ⟨_, rfl, rfl⟩
  refine carries_seat e fun _ _ _ => ?_
  rw [hd]
  exact second_carries (Cl := Unit) (VerifiableInference.Desc.Key.thirdPar X.chains) _ _

theorem returns₀ : Returns (keyFileDescription X N P).second.blocksInOrder ft (Z₃At X P gOwn vOwn) 0 := by
  obtain ⟨blk, e, hd⟩ : ∃ blk, (keyFileDescription X N P).second.blocksInOrder[0]? = some blk ∧
      blk.decide = (VerifiableInference.Desc.Third.batchLinearConstraintsSecondPart (Cl := Unit)
        (VerifiableInference.Desc.Key.thirdPar X.chains)).decide := ⟨_, rfl, rfl⟩
  refine returns_seat e fun _ _ _ => ?_
  rw [hd]
  exact second_returns (Cl := Unit) (VerifiableInference.Desc.Key.thirdPar X.chains) _ _

theorem carries₁ : Carries (keyFileDescription X N P).second.blocksInOrder ft (Z₃At X P gOwn vOwn) 1 := by
  obtain ⟨blk, e, hd⟩ : ∃ blk, (keyFileDescription X N P).second.blocksInOrder[1]? = some blk ∧
      blk.decide = (VerifiableInference.Desc.Third.takenSources
        (VerifiableInference.Desc.Key.ownTest P)).decide := ⟨_, rfl, rfl⟩
  refine carries_seat e fun _ _ _ => ?_
  rw [hd]
  exact sources_carries _ (VerifiableInference.Desc.Key.ownTest P) _ _

theorem returns₁ : Returns (keyFileDescription X N P).second.blocksInOrder ft (Z₃At X P gOwn vOwn) 1 := by
  obtain ⟨blk, e, hd⟩ : ∃ blk, (keyFileDescription X N P).second.blocksInOrder[1]? = some blk ∧
      blk.decide = (VerifiableInference.Desc.Third.takenSources
        (VerifiableInference.Desc.Key.ownTest P)).decide := ⟨_, rfl, rfl⟩
  refine returns_seat e fun _ _ _ => ?_
  rw [hd]
  exact sources_returns _ (VerifiableInference.Desc.Key.ownTest P) _ _

theorem carries₂
    (h : ∀ rs gs, CarriesR (sh₃ X.chains.made.sized.key.once.shape)
      (fun s => (VerifiableInference.Desc.Key.ownTest P).decide s rs gs) gOwn) :
    Carries (keyFileDescription X N P).second.blocksInOrder ft (Z₃At X P gOwn vOwn) 2 := by
  obtain ⟨blk, e, hd⟩ : ∃ blk, (keyFileDescription X N P).second.blocksInOrder[2]? = some blk ∧
      blk.decide = (VerifiableInference.Desc.Key.ownTest P).decide := ⟨_, rfl, rfl⟩
  refine carries_seat e fun _ _ _ => ?_
  rw [hd]
  exact h _ _

theorem returns₂
    (h : ∀ rs gs, ReturnsR (sh₃ X.chains.made.sized.key.once.shape)
      (fun s => (VerifiableInference.Desc.Key.ownTest P).decide s rs gs) gOwn
      (fun s => vOwn s rs gs)) : Returns (keyFileDescription X N P).second.blocksInOrder ft (Z₃At X P gOwn vOwn) 2 := by
  obtain ⟨blk, e, hd⟩ : ∃ blk, (keyFileDescription X N P).second.blocksInOrder[2]? = some blk ∧
      blk.decide = (VerifiableInference.Desc.Key.ownTest P).decide := ⟨_, rfl, rfl⟩
  refine returns_seat e fun _ _ _ => ?_
  rw [hd]
  exact h _ _

theorem carries₃ : Carries (keyFileDescription X N P).second.blocksInOrder ft (Z₃At X P gOwn vOwn) 3 := by
  obtain ⟨blk, e, hd⟩ : ∃ blk, (keyFileDescription X N P).second.blocksInOrder[3]? = some blk ∧
      blk.decide = (VerifiableInference.Desc.Third.end₃ (Cl := Unit) []).decide := ⟨_, rfl, rfl⟩
  refine carries_seat e fun _ _ _ => ?_
  rw [hd]
  exact end_carries (Cl := Unit) _ [] _ _

theorem returns₃ : Returns (keyFileDescription X N P).second.blocksInOrder ft (Z₃At X P gOwn vOwn) 3 := by
  obtain ⟨blk, e, hd⟩ : ∃ blk, (keyFileDescription X N P).second.blocksInOrder[3]? = some blk ∧
      blk.decide = (VerifiableInference.Desc.Third.end₃ (Cl := Unit) []).decide := ⟨_, rfl, rfl⟩
  refine returns_seat e fun _ _ _ => ?_
  rw [hd]
  exact end_returns (Cl := Unit) _ [] _ _

/-- **(B1) at every number.** -/
theorem carries_all
    (h : ∀ rs gs, CarriesR (sh₃ X.chains.made.sized.key.once.shape)
      (fun s => (VerifiableInference.Desc.Key.ownTest P).decide s rs gs) gOwn) (j : Nat) :
    Carries (keyFileDescription X N P).second.blocksInOrder ft (Z₃At X P gOwn vOwn) j := by
  match j with
  | 0 => exact carries₀ X N P gOwn vOwn ft
  | 1 => exact carries₁ X N P gOwn vOwn ft
  | 2 => exact carries₂ X N P gOwn vOwn ft h
  | 3 => exact carries₃ X N P gOwn vOwn ft
  | n + 4 =>
    intro blk hb
    cases hb

end At

/-! ## Evaluations at the full size's shapes and codes -/

open Lk6.AtPlan (keyFull) in
/-- The shape of E2E/KeySecondMember.lean's synthetic state, written out. -/
def aF : Sh₃ :=
  (⟨⟨CF,
      [⟨keyFull.once.input.shape, true, 0, padF keyFull.once.input.shape, [0], none, false⟩,
        ⟨SF.w, true, 0, padF SF.w, [0], none, false⟩,
        ⟨{ code := noId, mainRows := 0, maskRows := 1, maskCode := SF.ownMaskCode, answers := 0 },
          false, 0, [], [], none, false⟩],
      [⟨SF.w.code, SF.ownMaskCode, [0, 1], [false, false], [.plain], false⟩]⟩,
    ⟨[⟨{}, 0, .own 0, [0], false, 0⟩, ⟨{}, 5, .own 0, [1, 2], false, 0⟩],
      [(0, 0), (1, 0), (1, 1)]⟩, 0⟩,
   ⟨true, 1, 0, some 2,
    some ⟨true, true,
      ⟨CF, [⟨SF.omega, true, 0, padF SF.omega, [0], none, false⟩],
        [⟨SF.omega.code, 0, [0], [false], [], true⟩]⟩,
      ⟨[⟨{}, 1, .own 0, [0], false, 0⟩], [(0, 0)]⟩, SF.kCol, 0⟩,
    noId, 3⟩)

/-- It is the reader's value at that state: by the kernel. -/
theorem aF_is : sh₃ SF sF = aF := by decide +kernel

/-- The letters at the written values; the own test's are not run here. -/
def ZF : Shape S₃ :=
  Z₃ SF (H2K.Member.dsOf H2K.Member.piKWFull) (fun a => .ok a) fun _ _ _ => true

/-- **The shape's own run over the first two sub-protocols returns**: by the kernel. -/
theorem yes_two : ZF.yes aF 2 = true := by decide +kernel

/-- **A negative test**: without the mark on the row weights the run rejects. -/
theorem no_mark : ZF.yes (aF.1, { aF.2 with
    border := aF.2.border.map fun x => { x with weights := false } }) 1 = false := by
  decide +kernel

/-- **A negative test**: without the two ends. -/
theorem no_border : ZF.yes (aF.1, { aF.2 with border := none }) 1 = false := by decide +kernel

/-- **A negative test**: with another number at W's tree the first sub-protocol's guards return and
the second's reject. -/
theorem no_tree :
    ZF.yes ({ aF.1 with book := { aF.1.book with
      trees := [⟨{}, 0, .own 0, [0], false, 0⟩, ⟨{}, 4, .own 0, [1, 2], false, 0⟩] } }, aF.2) 1 =
        true ∧
    ZF.yes ({ aF.1 with book := { aF.1.book with
      trees := [⟨{}, 0, .own 0, [0], false, 0⟩, ⟨{}, 4, .own 0, [1, 2], false, 0⟩] } }, aF.2) 2 =
        false := by decide +kernel

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.carries₀
#print axioms AtPublicFiles.AtFiles.returns₀
#print axioms AtPublicFiles.AtFiles.carries₁
#print axioms AtPublicFiles.AtFiles.returns₁
#print axioms AtPublicFiles.AtFiles.carries₂
#print axioms AtPublicFiles.AtFiles.returns₂
#print axioms AtPublicFiles.AtFiles.carries₃
#print axioms AtPublicFiles.AtFiles.returns₃
#print axioms AtPublicFiles.AtFiles.carries_all
#print axioms AtPublicFiles.AtFiles.aF_is
#print axioms AtPublicFiles.AtFiles.yes_two
#print axioms AtPublicFiles.AtFiles.no_mark
#print axioms AtPublicFiles.AtFiles.no_border
#print axioms AtPublicFiles.AtFiles.no_tree
