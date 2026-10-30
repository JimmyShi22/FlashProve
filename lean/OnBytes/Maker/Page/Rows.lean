-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/Rows.lean: the nine fields of the tie of a file's three chains that speak of the
typed oracle functions or of the instance in a query (`GRows`,
OnBytes/Maker/Page/RunsTools.lean), in that record's own numbers, for oracle functions that answer
by the calls of a file's page.

Statements and proofs. OnBytes/Maker/Page/Chains.lean has the seven laws on the oracle functions at
the page's own numbers of rounds: 1, .., J, J + 1, .., J3, J3 + 1, ... The record writes these
numbers by the lengths of the file's three lists of rounds. Here the two are laid together.

Main names:
  `HeadFits O S o lab pd st rnd run`: what one chain's first query needs: the head as the reader
    computed it (`HeadIs`, OnBytes/Maker/Page/FirstCalls.lean), its run's value, the parameters'
    digest.
  `ChainsFit F Q C ds₁ ds₂ ds₃ embP`: the page's data count the three stretches' rounds and fit
    them (`FitsEnd`, `FitsShE`).
  `gRows_of`: `GRows`.
No letter stands under "there is".
Limits: every premise of Chains.lean is a premise here. The two fields on the instance in a query
(`late₁`, `late₃`) are premises. That the premises can be met at any interface is not shown here.
These oracle functions are no encoding in the sense of the soundness theorem (the head of
OnBytes/Maker/Page/Frame.lean). Nothing on soundness.


-/
import OnBytes.Maker.Page.Chains
import OnBytes.Maker.Page.RunsTools

set_option autoImplicit false

namespace OnBytes.Maker.Page

open Rom TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Joined.K TypedOracleCompiler.Compile.Batch
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Compile.Joined
open _root_.Run.PQ (CK)
open TypedOracleCompiler.Run.Twin TypedOracleCompiler.Run.Thin TypedOracleCompiler.Run.PQ
open _root_.Run.Twin (RS up allLo allLo_eq)
open _root_.Fmt (Chain RoundOut ChainOut)

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {Y : Type} {E : ExtSpec} {C : CK} {K : ℕ} {rF rJ r3 : RS}
  {aJ : RAnn rJ.up} {ds₁ ds₂ ds₃ : List RD} {t : Tag}
  {D : Desc (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃) Y E}

/-- The page's data count the three stretches' rounds and fit them. -/
structure ChainsFit (F : FileJ L t) (Q : FbIn 256 L t → Prop)
    (embP : PlainPart (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).sh (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).ann →
      PBt L t) : Prop where
  n₁ : F.n₁ = ds₁.length
  n₂ : F.n₂ = ds₂.length
  n₃ : F.n₃ = ds₃.length
  f₁ : FitsEnd F Q C ds₁ (fun z => embL₁ embP (Sum.inr z)) (0 + 1)
  f₂ : FitsShE F Q C ds₂ (fun z => embL₂ embP (Sum.inr z)) (F.J + 1)
  f₃ : FitsEnd F Q C ds₃ (fun z => embL₃ embP (Sum.inr z)) (F.J3 + 1)

/-- What one chain's first query needs of the reading. lab, pd: the page's label and parameters'
digest of the chain; rnd: the chain's random bytes. -/
structure HeadFits (O : ByteArray → ByteArray) (S : Fmt.SpecX) (o : ChainOut) (lab : ℕ)
    (pd st rnd run : ByteArray) : Prop where
  head : HeadIs (Fmt.HO O) S o lab st rnd
  run_eq : o.run = some run
  pd_eq : pd = pdOf (Fmt.HO O) S

/-- **The nine fields.** -/
theorem gRows_of {g : Fam (typedOracleFamily 256 (K + 1) L)} {F : FileJ L t} {O : ByteArray → ByteArray}
    {Q : FbIn 256 L t → Prop} (hO : ∀ s, (O s).size = 32) (S : Speaks g t F O Q)
    (embP : PlainPart (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).sh (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).ann →
      PBt L t)
    (A : ChainsFit (C := C) (rF := rF) (rJ := rJ) (r3 := r3) (aJ := aJ) (ds₁ := ds₁) (ds₂ := ds₂)
      (ds₃ := ds₃) F Q embP)
    (xin : Y → Option X) (cms : List (Dig 256)) (x : Y) (π : OneProtocolProof 256 D.batch)
    (rtF rt3 : List (Dig 256)) (S₁ S₂ S₃ : Fmt.SpecX) (o₁ o₂ o₃ : ChainOut)
    (rs₁ : List Fmt.Round) (hrs : rs₁.length = ds₁.length) (some₂ : ds₂ ≠ [])
    {st₁ st₂ st₃ rnd₁ rnd₂ rnd₃ run₁ run₂ run₃ : ByteArray}
    (H₁ : HeadFits O S₁ o₁ F.lab₁ F.pd₁ st₁ rnd₁ run₁)
    (H₂ : HeadFits O S₂ o₂ F.lab₂ F.pd₂ st₂ rnd₂ run₂)
    (H₃ : HeadFits O S₃ o₃ F.lab₃ F.pd₃ st₃ rnd₃ run₃) (hsalt : π.salt = bytesToBits run₁)
    (q₁ : Q ⟨0, .f1 cms ((xin x).map L.early) (bytesToBits run₁), rtF,
      embL₁ embP (Sum.inl (Sum.inr (pls₁ D π).1))⟩)
    (t₁ : F.stm₁ cms ((xin x).map L.early) (embL₁ embP (Sum.inl (Sum.inr (pls₁ D π).1))) = st₁)
    (q₂ : Q ⟨F.J, .f4 cms (List.ofFn π.rtreq), [],
      embL₂ embP (Sum.inl (Sum.inl (aJ.plain (pls₂ D π).1).1))⟩)
    (t₂ : F.stm₂ cms (List.ofFn π.rtreq)
      (embL₂ embP (Sum.inl (Sum.inl (aJ.plain (pls₂ D π).1).1))) = st₂)
    (u₂ : F.run₂ (embL₂ embP (Sum.inl (Sum.inl (aJ.plain (pls₂ D π).1).1))) = bytesToBits run₂)
    (q₃ : Q ⟨F.J3,
      .f3 (List.ofFn (bytesToDig (sealRead o₂))) (List.ofFn (bytesToDig (sealRead o₁))), rt3,
      embL₃ embP (Sum.inl (Sum.inr (pls₃ D π).1))⟩)
    (t₃ : F.stm₃ (List.ofFn (bytesToDig (sealRead o₂))) (List.ofFn (bytesToDig (sealRead o₁)))
      (embL₃ embP (Sum.inl (Sum.inr (pls₃ D π).1))) = st₃)
    (u₃ : F.run₃ (embL₃ embP (Sum.inl (Sum.inr (pls₃ D π).1))) = bytesToBits run₃)
    (late₁ : xin x = none ∨ ∀ k, k < ds₁.length → L.late ≠ some (0 + 1 + k))
    (late₃ : xin x = none ∨ ∀ k, k < ds₃.length →
      L.late ≠ some (0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length +
        (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₂.length + 1 + k)) :
    GRows (D := D) embP xin cms x π g O rtF rt3 S₁ S₂ S₃ o₁ o₂ o₃ rs₁ := by
  have eJ : 0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length = F.J := by
    rw [len_c₁]
    unfold FileJ.J
    rw [A.n₁]
    omega
  have eJ3 : 0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length +
      (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₂.length = F.J3 := by
    rw [len_c₁₂]
    unfold FileJ.J3
    rw [A.n₁, A.n₂]
    omega
  have eG : 0 + rs₁.length + 1 = F.J := by
    unfold FileJ.J
    rw [A.n₁, hrs]
    omega
  have l2 : 1 ≤ ds₂.length := List.length_pos_iff.2 some₂
  exact
    { row₁ := by
        rw [H₁.head.label_eq]
        exact rowEnd₁ hO S C ds₁ _ (0 + 1) A.f₁ (by omega) (by rw [A.n₁]; omega)
      row₂ := by
        rw [H₂.head.label_eq, eJ]
        exact rowShE₂ hO S C ds₂ _ 1 A.f₂ (by omega) (by rw [A.n₂]; omega)
      row₃ := by
        rw [H₃.head.label_eq, eJ3]
        exact rowEnd₃ hO S C ds₃ _ 1 A.f₃ (by omega) (by rw [A.n₃]; omega)
      s0 := by
        rw [hsalt]
        exact s0_of hO S H₁.head H₁.run_eq H₁.pd_eq cms _ rtF _ q₁ t₁
      sG := by
        rw [H₁.head.label_eq, eJ, eG]
        exact gAt_of hO S _
      s4 := by
        rw [eJ]
        exact s4_of hO S H₂.head H₂.run_eq H₂.pd_eq cms _ [] _ q₂ t₂ u₂
      s3 := by
        rw [eJ3]
        exact s3_of hO S H₃.head H₃.run_eq H₃.pd_eq _ _ rt3 _ q₃ t₃ u₃
      late₁ := late₁
      late₃ := late₃ }

end OnBytes.Maker.Page
