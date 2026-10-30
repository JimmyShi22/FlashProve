-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupKeyFormsAreTheLibrarysKeysAtTheHeadB.lean: helper B of
LookupKeyFormsAreTheLibrarysKeysAtTheHead.lean: CALLS, COLUMNS, PADDING KEYS. A WORKING FILE.

One statement, on public data alone: in the goals' scope, at a call below the shape's number of calls: the output
head's kind's table of a call (callTable: Johnson/Desc/Kinds/HeadCallLaw.lean) over any values G of the nine keys, with the
kind's padding key, at column i / 1024 and position i % 1024, is the library's key vector of that call (H.kvOf:
OnBytes/Tie/Pv/Lookup/Ends/H.lean) over any values f of the nine segments that agree with G below the keys' lengths.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupKeyFormsAreTheLibrarysKeysAtTheHeadB0
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupKeyFormsAreTheLibrarysKeysAtTheHeadB1
import Johnson.Desc.ProofFile.Honest.K3.Tab.HeadMade
import Johnson.Desc.Kinds.Law.Columns
import Johnson.Desc.Kinds.Law.LibJoin
import Johnson.Desc.Kinds.Law.LibLetters
import Johnson.Desc.ProofFile.Honest.K3.WitHead
import Johnson.Road.FormsKeysPos
import Johnson.Goal.HonestTrace.LookAtRunInScope
import Johnson.Goal.HonestTrace.FullPlanesInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc.Kinds.Head (Sizes PlaceKey lenOf padKey)
open VerifiableInference.Desc.Kinds.Head.Law (callTable)
open VerifiableInference.OnPublicFiles

/-- **A call's table over the kind's columns is the library's key vector over the layout's.** -/
theorem callTableIsTheLibrarysKeyVector {K : Type} [Field K] [sizes : Sizes]
    {publicFiles : VerifierAndGoals.PublicFiles} {parameters : Inst.Model.ScalesAndPolicy} {layoutFile : Option ByteArray}
    {publicPart : OnBytes.Model.Verify.Public}
    (inScope : VerifierAndGoals.InScope publicFiles = true)
    (filesRead : VerifierAndGoals.readFiles publicFiles = .ok parameters)
    (publicPartMade : OnBytes.Model.Verify.publicOf publicFiles.pol publicFiles.KL layoutFile =
      .ok publicPart)
    (sizesAreThePublicParts : sizes = k3SizesAt publicPart)
    (coveredPositions : OnBytes.Model.Head.Covered) (checkedTokens : Array Nat)
    (kindsValues : PlaceKey → Nat → Nat → K) (librarysValues : String → Nat → Nat → K)
    (valuesAgree : ∀ key x t, x < lenOf key → t < 1024 →
      kindsValues key x t = librarysValues (segmentName key) x t)
    (call : Nat) (callIsThere : call < publicPart.HLy.fs.NC) (i : Nat) :
    callTable call kindsValues ((padKey call : Nat) : K) (i / 1024) (i % 1024) =
      OnBytes.Ends.H.kvOf (headPub publicPart coveredPositions checkedTokens) librarysValues call i := by
  have thePad := fun (h6 : call < 6) =>
    paddingKeyIsTheTablesRow inScope filesRead publicPartMade sizesAreThePublicParts h6
  subst sizesAreThePublicParts
  letI : Sizes := k3SizesAt publicPart
  have core := OnBytes.Road.Hd.public_of_core publicPartMade
    (OnBytes.Road.Hd.core_of_scope inScope filesRead publicPartMade)
  have theCalls := headCallsAreTheDefaultLines inScope filesRead publicPartMade
  have wide := VerifiableInference.Desc.Kinds.Head.Law.Came.wide_at publicPart.hS core.full
    (Meaning.HeadS.famF_in_scope inScope filesRead publicPartMade)
  have positions : publicPart.hS.T = 1024 :=
    OnBytes.HonestTrace.headT_in_scope inScope filesRead publicPartMade
  have size : publicPart.HLy.calls.size = 6 := by
    rw [theCalls]
    rfl
  have h6 : call < 6 := by
    rw [← size, ← OnBytes.Road.Hd.fsNC_of_layout core.head]
    exact callIsThere
  have admitted := OnBytes.Road.Hd.admittedH_of_layout core.head
  have layoutJV : publicPart.HLy.JV = 202048 :=
    (OnBytes.HonestTrace.lookPub_in_scope inScope filesRead publicPartMade).JV.trans core.full.V
  have layoutJVa : publicPart.HLy.JVa = 131072 := by
    rw [admitted.JVa, layoutJV]
    rfl
  have dKind : VerifiableInference.Desc.Kinds.Norm.d = 5120 := wide.d
  have jvKind : VerifiableInference.Desc.Kinds.Head.JV = 202048 := wide.JV
  have kindsJVa : VerifiableInference.Desc.Kinds.Head.JVa = 131072 := by
    unfold VerifiableInference.Desc.Kinds.Head.JVa
    rw [jvKind]
    rfl
  have oneColumnAnEntry : ∀ g ∈ (publicPart.HLy.calls.getD call default).segs, g.pos.size = g.n :=
    fun g hg => ProofFile.Honest.K3.AtInt.posSize_made core.head (by rw [size]; exact h6) hg
  have tBelow : i % 1024 < 1024 := Nat.mod_lt _ (by norm_num)
  have agreeAt : ∀ key x, x < lenOf key →
      kindsValues key x (i % 1024) = librarysValues (segmentName key) x (i % 1024) :=
    fun key x hx => valuesAgree key x (i % 1024) hx tBelow
  have theEnd : OnBytes.Ends.H.kvOf (headPub publicPart coveredPositions checkedTokens) librarysValues call i =
      match OnBytes.Ends.H.colH publicPart.HLy call (i / 1024) with
      | some (sn, x) => librarysValues sn x (i % 1024)
      | none => ((padKey call : Nat) : K) := by
    unfold OnBytes.Ends.H.kvOf
    show (match OnBytes.Ends.H.colH publicPart.HLy call (i / publicPart.hS.T) with
      | some (sn, x) => librarysValues sn x (i % publicPart.hS.T)
      | none => ((OnBytes.Ends.tauN publicPart.HLy.fs call (OnBytes.Ends.t0N publicPart.HLy.fs call) : Nat) : K)) = _
    rw [positions, ← thePad h6]
  rw [theEnd]
  have placedAt : ∀ q, publicPart.HLy.calls.getD q default =
      (defaultCallsOf publicPart.hS publicPart.HLy).toArray.getD q default := fun q => by rw [theCalls]
  have dLayout : publicPart.hS.d = 5120 := core.full.d
  have rowLayout : OnBytes.Model.ledNRH publicPart.hS.XL = 120 := by
    rw [core.full.XL]
    rfl
  interval_cases call
  · refine callTableAtAPlacedCall publicPart.HLy 0 _ _ _ _ (placedAt 0) ?_ ?_ oneColumnAnEntry _ _ _ agreeAt _ _
    · show [("NF", VerifiableInference.Desc.Kinds.Norm.d), ("NFH", VerifiableInference.Desc.Kinds.Norm.d),
        ("HD0", VerifiableInference.Desc.Kinds.Head.JV)] =
        [("NF", publicPart.hS.d), ("NFH", publicPart.hS.d), ("HD0", publicPart.HLy.JV)]
      rw [dKind, jvKind, dLayout, layoutJV]
    · intro n hn
      have hn' : n ∈ [publicPart.hS.d, publicPart.hS.d, publicPart.HLy.JV] := hn
      rw [dLayout, layoutJV] at hn'
      simp at hn'
      omega
  · refine callTableAtAPlacedCall publicPart.HLy 1 _ _ _ _ (placedAt 1) ?_ ?_ oneColumnAnEntry _ _ _ agreeAt _ _
    · show [("HD1", VerifiableInference.Desc.Kinds.Head.JV)] = [("HD1", publicPart.HLy.JV)]
      rw [jvKind, layoutJV]
    · intro n hn
      have hn' : n ∈ [publicPart.HLy.JV] := hn
      rw [layoutJV] at hn'
      simp at hn'
      omega
  · refine callTableAtAPlacedCall publicPart.HLy 2 _ _ _ _ (placedAt 2) ?_ ?_ oneColumnAnEntry _ _ _ agreeAt _ _
    · show [("ROW", lenOf (.inl .digits : PlaceKey)), ("HD2", VerifiableInference.Desc.Kinds.Head.JV)] =
        [("ROW", OnBytes.Model.ledNRH publicPart.hS.XL), ("HD2", publicPart.HLy.JV)]
      rw [jvKind, layoutJV, rowLayout]
      rfl
    · intro n hn
      have hn' : n ∈ [OnBytes.Model.ledNRH publicPart.hS.XL, publicPart.HLy.JV] := hn
      rw [rowLayout, layoutJV] at hn'
      simp at hn'
      omega
  · refine callTableAtAPlacedCall publicPart.HLy 3 _ _ _ _ (placedAt 3) ?_ ?_ oneColumnAnEntry _ _ _ agreeAt _ _
    · show [("HE0", VerifiableInference.Desc.Kinds.Head.JVa)] = [("HE0", publicPart.HLy.JVa)]
      rw [kindsJVa, layoutJVa]
    · intro n hn
      have hn' : n ∈ [publicPart.HLy.JVa] := hn
      rw [layoutJVa] at hn'
      simp at hn'
      omega
  · refine callTableAtAPlacedCall publicPart.HLy 4 _ _ _ _ (placedAt 4) ?_ ?_ oneColumnAnEntry _ _ _ agreeAt _ _
    · show [("HE1", VerifiableInference.Desc.Kinds.Head.JV - VerifiableInference.Desc.Kinds.Head.JVa)] =
        [("HE1", publicPart.HLy.JV - publicPart.HLy.JVa)]
      rw [jvKind, kindsJVa, layoutJV, layoutJVa]
    · intro n hn
      have hn' : n ∈ [publicPart.HLy.JV - publicPart.HLy.JVa] := hn
      rw [layoutJV, layoutJVa] at hn'
      simp at hn'
      omega
  · refine callTableAtAPlacedCall publicPart.HLy 5 _ _ _ _ (placedAt 5) ?_ ?_ oneColumnAnEntry _ _ _ agreeAt _ _
    · show [("CNF", VerifiableInference.Desc.Kinds.Norm.d)] = [("CNF", publicPart.hS.d)]
      rw [dKind, dLayout]
    · intro n hn
      have hn' : n ∈ [publicPart.hS.d] := hn
      rw [dLayout] at hn'
      simp at hn'
      omega

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.callTableIsTheLibrarysKeyVector
