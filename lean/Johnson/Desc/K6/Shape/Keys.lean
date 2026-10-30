-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Shape/Keys.lean: the shapes of the output head's nine keys, of the six calls' key
vectors and of the one form of the run "join", as code on shapes, with the laws that tie the code
to the texts.

What it is not. No law on a value, a coefficient or a constant. The letters are letters, as in
Forms.lean beside it: of each leaf the shape alone is asked (LeavesAre, a premise). Nothing on any
property of the protocol. It stands on Johnson/Desc/First/Shape/Parts.lean.

  `keyNSh`, `keySh`   the normalization's four keys (Johnson/Desc/Kinds/HeadNorm.lean: key); the
                head's five (Head.lean: key)
  `keyVectorSh`  a call's key vector (HeadFrame.lean: keyVector): its keys one behind the other
  `keysSh`       the six calls' (HeadIn.lean: callList), in order
  `joinSh`       the form of "join" (Johnson/Desc/Kinds/Law/JoinValue.lean: joinForm): the key
                vectors one behind the other, then the form in which the lookup's key side ended
  `keyN_sh`, `key_sh`, `keyVector_sh`, `calls_keys_all`, `joinForm_sh`   the laws

-/
import Johnson.Desc.K6.Shape.Forms
import Johnson.Desc.Kinds.Law.KeysHave
import Johnson.Desc.Kinds.Law.FromGiven

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Shape
open OnBytes (E zeroE)
open OnBytes.Model (Aff)
open Norm (lt ls d lPd T S2)
open VerifiableInference.Desc.First.Shape (AffSh affSh affSh_addMul affSh_add affSh_sub)

local infixl:65 " ⋆ " => AffSh.append

section Code
variable [Sizes] (L : LeafSh)

/-- FinalNorm.wideAt. -/
def wideAtNSh (f0 : Nat) : AffSh :=
  sumSh (d / S2) fun i => sumSh 2 fun l => L.wide ((f0 + l * d) / S2 + i)

/-- The normalization's four keys. -/
def keyNSh (more : Nat) : FinalNorm.Key → AffSh
  | .remLow => L.nmClaimed ⋆ wideAtNSh L 0 ⋆ wideAtNSh L (2 * d)
  | .remHigh => wideAtNSh L (2 * d)
  | .clamp => wideAtNSh L 0 ⋆ sumSh d fun k => actAtSh (L.entryN .actAtKeys) k
  | .digits => sumSh (NR + more) fun j => L.entryN .rowAtKeys j

/-- wideAt. -/
def wideAtSh (k : Key) (f0 nl stride : Nat) : AffSh :=
  sumSh (len k / S2) fun i => sumSh nl fun l => L.entryH .wideAtKeys ((f0 + l * stride) / S2 + i)

/-- mid. -/
def midSh (k : Key) (v0 : Nat) : AffSh := wideAtSh L k (4 * d + v0) 2 JV
/-- low. -/
def lowSh (k : Key) : AffSh := wideAtSh L k (4 * d + 2 * JV) 1 JV
/-- tableValue. -/
def tableValueSh (k : Key) (v0 : Nat) : AffSh := wideAtSh L k (4 * d + 3 * JV + v0) 3 JV

/-- top. -/
def topSh : AffSh :=
  L.lgClaimed ⋆ (atCostsSh L .paid ⋆ atCostsSh L .over) ⋆ midSh L .marginTop 0 ⋆ lowSh L .marginTop

/-- The head's five keys. -/
def keySh : Key → AffSh
  | .marginTop => topSh L
  | .marginMid => midSh L .marginMid 0
  | .marginLow => lowSh L .marginLow
  | .tableA => midSh L .tableA 0 ⋆ tableValueSh L .tableA 0
  | .tableB => midSh L .tableB JVa ⋆ tableValueSh L .tableB JVa

/-- A key of the place. -/
def placeKeySh : PlaceKey → AffSh
  | .inl k => keyNSh L 21 k
  | .inr k => keySh L k

/-- A call's key vector: its keys, one behind the other; the padding's term is a constant. -/
def keyVectorSh (keys : List PlaceKey) : AffSh := catSh (keys.map (placeKeySh L))

/-- The six calls' key vectors, in order. -/
def keysSh : List AffSh := callList.map (keyVectorSh L)

end Code

/-- The form of "join": the calls' key vectors, one behind the other, then the form in which the
lookup's key side ended. -/
def joinSh (KF : List AffSh) (cEnd : AffSh) : AffSh := catSh KF ⋆ cEnd

section Law
variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] [Norm.Heard] [FinalNorm.Heard]
  [Heard] [FinalNorm.Reads] [Reads] (L : LeafSh) (h : LeavesAre L)
include h

theorem keyN_sh (more : Nat) (k : FinalNorm.Key) :
    affSh (FinalNorm.key more k) = keyNSh L more k := by
  have hw : ∀ k f0, affSh (FinalNorm.wideAt k f0) = wideAtNSh L f0 := by
    intro k f0
    unfold FinalNorm.wideAt wideAtNSh
    simp only [affSh_sumTo, affSh_smulE, h.wide]
  cases k
  · simp only [FinalNorm.key, keyNSh, affSh_sub, affSh_addE, affSh_smulN, h.nmClaimed, hw]
  · simp only [FinalNorm.key, keyNSh, affSh_smulN, affSh_Eadd, hw]
  · simp only [FinalNorm.key, keyNSh, actAtSh, FinalNorm.actAt, affSh_addE, affSh_add,
      affSh_smulN, affSh_smulE, affSh_sumTo, h.entryN, hw]
  · simp only [FinalNorm.key, keyNSh, affSh_sumTo, affSh_smulE, affSh_add, affSh_natCast,
      append_noTerm, h.entryN]

theorem key_sh (k : Key) : affSh (key k) = keySh L k := by
  have hw : ∀ k f0 nl stride, affSh (wideAt k f0 nl stride) = wideAtSh L k f0 nl stride := by
    intro k f0 nl stride
    unfold wideAt wideAtSh
    simp only [affSh_sumTo, affSh_smulE, h.entryH]
  have hm : ∀ k v0, affSh (mid k v0) = midSh L k v0 := by
    intro k v0
    unfold mid midSh
    rw [affSh_Eadd, hw]
  have hlo : ∀ k, affSh (low k) = lowSh L k := by
    intro k
    unfold low lowSh
    rw [affSh_Eadd, hw]
  have ht : ∀ k v0, affSh (tableValue k v0) = tableValueSh L k v0 := by
    intro k v0
    unfold tableValue tableValueSh
    rw [affSh_Eadd, hw]
  cases k
  · simp only [key, top, keySh, topSh, affSh_smulE, affSh_smulN, affSh_sub, affSh_const,
      append_noTerm, affSh_add, h.lgClaimed, atCosts_sh L h, hm, hlo]
  · exact hm _ _
  · exact hlo _
  · simp only [key, keySh, affSh_add, affSh_smulN, hm, ht]
  · simp only [key, keySh, affSh_add, affSh_smulN, hm, ht]

/-- **A call's key vector.** -/
theorem keyVector_sh (padding : E) (keys : List PlaceKey) :
    affSh (keyVector key padding keys) = keyVectorSh L keys := by
  unfold keyVector keyVectorSh catSh
  rw [affSh_foldl_add, List.map_map, affSh_const]
  refine congrArg (List.foldl (· ⋆ ·) noTerm) (List.map_congr_left fun k _ => ?_)
  cases k with
  | inl k => exact keyN_sh L h 21 k
  | inr k => exact key_sh L h k

end Law

/-- The calls that come in from the lookup have the keys of the list of calls, whatever the points
are. -/
theorem calls_keys_all [Sizes] (floor : Nat) (zx : Point) (zk : Nat → Point) :
    (fromLookup floor zx zk).calls.map (·.2) = callList := by
  rfl

/-- **The form of "join"**, at any key vectors. -/
theorem joinForm_sh (g : OnBytes.Model.Forest.Heard) (KF : Array Aff) :
    affSh (Law.Came.joinForm g KF) = joinSh (KF.toList.map affSh) (affSh g.cEnd) := by
  have step : ∀ (l : List Nat) (a : Aff), affSh (l.foldl (Law.Came.joinStep g KF) a) =
      (l.map fun c => affSh (KF.getD c (Aff.ofConst zeroE))).foldl (· ⋆ ·) (affSh a) := by
    intro l
    induction l with
    | nil =>
      intro a
      rfl
    | cons x xs ih =>
      intro a
      simp only [List.foldl_cons, List.map_cons]
      rw [ih]
      unfold Law.Came.joinStep
      rw [affSh_addMul, affSh_sub, affSh_const, noTerm_append]
  have e : (List.range KF.size).map (fun c => affSh (KF.getD c (Aff.ofConst zeroE))) =
      KF.toList.map affSh := by
    refine List.ext_getElem (by simp) fun i h1 _ => ?_
    have hi : i < KF.size := by simpa using h1
    simp [Array.getD_eq_getD_getElem?, hi]
  unfold Law.Came.joinForm joinSh catSh
  rw [affSh_sub, affSh_add, affSh_const, append_noTerm, step, affSh_const, e]

end VerifiableInference.Desc.Kinds.Head.Shape

#print axioms VerifiableInference.Desc.Kinds.Head.Shape.keyN_sh
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.key_sh
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.keyVector_sh
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.calls_keys_all
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.joinForm_sh
