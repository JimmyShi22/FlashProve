-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/AllThereP.lean: THE TEST `allThere` (Johnson/Desc/First/AllThere.lean) READS OF
ITS SIX OPTIONS ONLY WHETHER EACH IS THERE: so it is a function of five yes-or-no answers, the
head's segment's number and two lists of sorts; AND IT IS MONOTONE IN THE FIVE. So a closed fact
at a written PATTERN of answers, with "each option is there wherever the pattern says so", gives
the test at real data. Definitions with code and four theorems. No Mathlib.
  `dataThereP ns nx f5 a5 pl hd links links5`, `allThereP`; `dataThereBy_P`, `allThereBy_P`: the
    twin of Johnson/Desc/First/AllThereBy.lean IS this one at the options' `isSome`.
    `dataThereP_mono`, `allThereP_mono`.
Limits: those of Johnson/Desc/First/AllThereBy.lean. Nothing on soundness.

-/
import Johnson.Desc.First.AllThereBy
import Johnson.Desc.First.AllFilledBy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First.Look (k3SortAt placeAt)
open VerifiableInference.Desc.First.FillK4 (isLay)
open H2K5.Door (K5Data)

/-- The test at an item, of five answers "is the option there". -/
def dataThereP (ns nx f5 a5 : Nat → Bool) (pl : Nat → Bool → Bool) (hd : Nat)
    (links links5 : List ModelPart) : Pub → Bool
  | .freeAbove m => ns m
  | .callerIn m =>
    if isLay links m then nx m
    else if links5[m]? == some .attention then f5 m
    else true
  | .lookIn m pc => (k3SortBy hd m pc).all fun dg => pl m dg
  | .lookOut m pc => (k3SortBy hd m pc).all fun dg => pl m dg
  | .more (some m) name =>
    if (links5[m]? == some .attention) && (name == "K5.okAt" || name == "K5.plain") then a5 m
    else true
  | _ => true

def allThereP (ns nx f5 a5 : Nat → Bool) (pl : Nat → Bool → Bool) (hd : Nat)
    (linksD links5 : List ModelPart) (M : More) (links : List ModelPart) (ps : List Place) : Bool :=
  (askedAt M links ps).all fun Q => Q.all (dataThereP ns nx f5 a5 pl hd linksD links5)

theorem dataThereBy_P (nsOf nextOf : Nat → Option Nat) (links : List ModelPart) (d5 : K5Data)
    (X : OnBytes.Model.Verify.Public) (q : Pub) :
    dataThereBy nsOf nextOf links d5 X q =
      dataThereP (fun m => (nsOf m).isSome) (fun m => (nextOf m).isSome)
        (fun m => (d5.first? m).isSome) (fun m => (d5.W.A[m / 2]?).isSome)
        (fun m dg => (placeAt X m dg).any fun p => p.shape.isSome) (hdOf X) links d5.links q := by
  cases q with
  | more sg name => cases sg <;> rfl
  | _ => rfl

theorem allThereBy_P (nsOf nextOf : Nat → Option Nat) (linksD : List ModelPart) (d5 : K5Data)
    (X : OnBytes.Model.Verify.Public) (M : More) (links : List ModelPart) (ps : List Place) :
    allThereBy nsOf nextOf linksD d5 X M links ps =
      allThereP (fun m => (nsOf m).isSome) (fun m => (nextOf m).isSome)
        (fun m => (d5.first? m).isSome) (fun m => (d5.W.A[m / 2]?).isSome)
        (fun m dg => (placeAt X m dg).any fun p => p.shape.isSome) (hdOf X) linksD d5.links M links
        ps := by
  unfold allThereBy allThereP
  rw [show dataThereBy nsOf nextOf linksD d5 X = _ from
    funext (dataThereBy_P nsOf nextOf linksD d5 X)]

/-- More options there: the test still says yes. -/
theorem dataThereP_mono {ns nx f5 a5 ns' nx' f5' a5' : Nat → Bool} {pl pl' : Nat → Bool → Bool}
    (h1 : ∀ m, ns m = true → ns' m = true) (h2 : ∀ m, nx m = true → nx' m = true)
    (h3 : ∀ m, f5 m = true → f5' m = true) (h4 : ∀ m, a5 m = true → a5' m = true)
    (h5 : ∀ m dg, pl m dg = true → pl' m dg = true) (hd : Nat) (links links5 : List ModelPart) (q : Pub)
    (h : dataThereP ns nx f5 a5 pl hd links links5 q = true) :
    dataThereP ns' nx' f5' a5' pl' hd links links5 q = true := by
  cases q with
  | freeAbove m => exact h1 m h
  | callerIn m =>
    have h' : (if isLay links m then nx m
      else if links5[m]? == some .attention then f5 m else true) = true := h
    show (if isLay links m then nx' m
      else if links5[m]? == some .attention then f5' m else true) = true
    by_cases e : isLay links m = true
    · rw [if_pos e] at h' ⊢
      exact h2 m h'
    · rw [if_neg e] at h' ⊢
      by_cases e' : (links5[m]? == some ModelPart.attention) = true
      · rw [if_pos e'] at h' ⊢
        exact h3 m h'
      · rw [if_neg e']
  | lookIn m pc =>
    have h' : ((k3SortBy hd m pc).all fun dg => pl m dg) = true := h
    show ((k3SortBy hd m pc).all fun dg => pl' m dg) = true
    cases hk : k3SortBy hd m pc with
    | none => rfl
    | some dg =>
      rw [hk] at h'
      exact h5 m dg h'
  | lookOut m pc =>
    have h' : ((k3SortBy hd m pc).all fun dg => pl m dg) = true := h
    show ((k3SortBy hd m pc).all fun dg => pl' m dg) = true
    cases hk : k3SortBy hd m pc with
    | none => rfl
    | some dg =>
      rw [hk] at h'
      exact h5 m dg h'
  | more sg name =>
    cases sg with
    | none => rfl
    | some m =>
      have h' : (if (links5[m]? == some .attention) &&
        (name == "K5.okAt" || name == "K5.plain") then a5 m else true) = true := h
      show (if (links5[m]? == some .attention) &&
        (name == "K5.okAt" || name == "K5.plain") then a5' m else true) = true
      by_cases e : ((links5[m]? == some ModelPart.attention) &&
          (name == "K5.okAt" || name == "K5.plain")) = true
      · rw [if_pos e] at h' ⊢
        exact h4 m h'
      · rw [if_neg e]
  | _ => rfl

theorem allThereP_mono {ns nx f5 a5 ns' nx' f5' a5' : Nat → Bool} {pl pl' : Nat → Bool → Bool}
    (h1 : ∀ m, ns m = true → ns' m = true) (h2 : ∀ m, nx m = true → nx' m = true)
    (h3 : ∀ m, f5 m = true → f5' m = true) (h4 : ∀ m, a5 m = true → a5' m = true)
    (h5 : ∀ m dg, pl m dg = true → pl' m dg = true) (hd : Nat) (linksD links5 : List ModelPart)
    (M : More) (links : List ModelPart) (ps : List Place)
    (h : allThereP ns nx f5 a5 pl hd linksD links5 M links ps = true) :
    allThereP ns' nx' f5' a5' pl' hd linksD links5 M links ps = true := by
  unfold allThereP at h ⊢
  refine List.all_eq_true.2 fun Q hQ => List.all_eq_true.2 fun q hq => ?_
  exact dataThereP_mono h1 h2 h3 h4 h5 hd linksD links5 q
    (List.all_eq_true.1 (List.all_eq_true.1 h Q hQ) q hq)

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.dataThereBy_P
#print axioms VerifiableInference.Desc.First.allThereBy_P
#print axioms VerifiableInference.Desc.First.dataThereP_mono
#print axioms VerifiableInference.Desc.First.allThereP_mono
