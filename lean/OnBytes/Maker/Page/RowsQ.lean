-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/RowsQ.lean: the nine fields on typed oracle functions (`GRows`,
OnBytes/Maker/Page/RunsTools.lean) for a family that answers by a page's data only at queries that
meet two conditions.

OnBytes/Maker/Page/Rows.lean has `GRows` from `Speaks` and `ChainsFit`. A family that is read
through a one-to-one code meets `Speaks.slot` only where O has one answer at two strings, and
`ChainsFit` asks the chain queries' condition of queries that no run makes (the head of
OnBytes/Maker/Page/ChainsQ.lean). Here the records of that file, which ask less, stand in their
place. The text follows OnBytes/Maker/Page/Rows.lean closely.

Main definitions.
  `OursEnd Q C ds embP i`, `OursShE`: along a stretch of local rounds, or of shared rounds, from the
    typed round i on: Q holds of the query at the round's own number, with a chaining value of 256
    bits, as many roots as the round sends trees, and a plain part of that round whose nonce is
    below 2 ^ 64.
  `ChainsFitQ`: `ChainsFit` with `FitsEndQ` and `FitsShEQ`.
Main theorems.
  `SpeaksQ.congrO`: `SpeaksQ` passes between two functions on strings that agree at calls' strings.
  `fitsEndQ_of`, `fitsShEQ_of`: `FitsEndQ` and `FitsShEQ` at Q, from the fit at the condition that
    every query meets and `OursEnd`, `OursShE` at Q.
  `oursEnd_of_all`, `oursShE_of_all`: from Q at every query with the stretch's form of head.
  `gRowsQ_of`: seven of the nine fields of `GRows`, from `SpeaksQ`, `ChainsFitQ`, answers of O of 32
    bytes, three records `HeadFits`, the typed string's salt, Q at the three first queries, Qg at
    the sealing call's queries, five equations on the page's data, the count of the first chain's
    rounds, and a second stretch that is not empty; the two fields on the instance in a query
    (`late₁`, `late₃`) are hypotheses handed through.
No letter stands under "there is".
No other file calls `SpeaksQ.congrO`.

What is not claimed. None of the hypotheses. That any family meets `SpeaksQ`. Whether a family that
meets `SpeaksQ` is an encoding in the sense of the soundness theorem is not said. Nothing on
soundness.


-/
import OnBytes.Maker.Page.ChainsQ
import OnBytes.Maker.Page.Rows

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

/-! ## The function on strings -/

/-- `SpeaksQ` reads the function on strings at calls' strings alone. -/
theorem SpeaksQ.congrO {g : Fam (typedOracleFamily 256 (K + 1) L)} {F : FileJ L t} {O O' : ByteArray → ByteArray}
    {Q : FbIn 256 L t → Prop} {Qg : JoiningRoundQuery 256 L t → Prop} (S : SpeaksQ g t F O Q Qg)
    (h : ∀ c : Fmt.OQ, O (strOf c) = O' (strOf c)) : SpeaksQ g t F O' Q Qg :=
  ⟨fun q k c hq hc => (S.blk q k c hq hc).trans (by rw [h c]),
    fun q c hq hc => (S.tail q c hq hc).trans (by rw [h c]),
    fun q c hq hc => (S.slot q c hq hc).trans (by rw [h c])⟩

/-! ## The condition on a stretch's own queries -/

/-- Q holds of the own queries of a stretch of local rounds, from the typed round i on. -/
def OursEnd (Q : FbIn 256 L t → Prop) (C : CK) : (ds : List RD) →
    (PlainPart (uL C ds) (allLo (SL C ds)) → PBt L t) → ℕ → Prop
  | [], _, _ => True
  | d :: ds, embP, i =>
    (∀ (ρ : Bits) (rt : List (Dig 256)) (pl : (roundS C d).Plain), ρ.length = 256 →
      rt.length = d.trees.length → GPlain.nonce (b := d.entry.work) pl < 2 ^ 64 →
      Q ⟨i, .f2 none ρ, rt, embP (.inl (.inr pl))⟩) ∧
      OursEnd Q C ds (fun z => embP (.inr z)) (i + 1)

/-- Q holds of the own queries of a stretch of shared rounds, from the typed round i on. -/
def OursShE (Q : FbIn 256 L t → Prop) (C : CK) : (ds : List RD) →
    (PlainPart (uL C ds) (annShE C ds) → PBt L t) → ℕ → Prop
  | [], _, _ => True
  | d :: ds, embP, i =>
    (∀ (ρ : Bits) (rt : List (Dig 256)) (pl : (roundS C d).Plain), ρ.length = 256 →
      rt.length = d.trees.length → GPlain.nonce (b := d.entry.work) pl < 2 ^ 64 →
      Q ⟨i, .f5 ρ, rt, embP (.inl (.inl pl))⟩) ∧
      OursShE Q C ds (fun z => embP (.inr z)) (i + 1)

theorem fitsEndQ_of {F : FileJ L t} {Q : FbIn 256 L t → Prop} {C : CK} : ∀ {ds : List RD}
    {embP : PlainPart (uL C ds) (allLo (SL C ds)) → PBt L t} {i : ℕ},
    FitsEnd F (fun _ => True) C ds embP i → OursEnd Q C ds embP i → FitsEndQ F Q C ds embP i
  | [], _, _, _, _ => trivial
  | _ :: _, _, _, h, o =>
    ⟨⟨o.1, h.1.kind, h.1.work, h.1.msg, h.1.nonce⟩, fitsEndQ_of h.2 o.2⟩

theorem fitsShEQ_of {F : FileJ L t} {Q : FbIn 256 L t → Prop} {C : CK} : ∀ {ds : List RD}
    {embP : PlainPart (uL C ds) (annShE C ds) → PBt L t} {i : ℕ},
    FitsShE F (fun _ => True) C ds embP i → OursShE Q C ds embP i → FitsShEQ F Q C ds embP i
  | [], _, _, _, _ => trivial
  | _ :: _, _, _, h, o =>
    ⟨⟨o.1, h.1.kind, h.1.work, h.1.msg, h.1.nonce⟩, fitsShEQ_of h.2 o.2⟩

/-- Where Q holds of every query with the stretch's form of head, it holds of the stretch's own. -/
theorem oursEnd_of_all {Q : FbIn 256 L t → Prop} {C : CK} : ∀ {ds : List RD}
    {embP : PlainPart (uL C ds) (allLo (SL C ds)) → PBt L t} {i : ℕ},
    (∀ i ρ rt z, Q ⟨i, .f2 none ρ, rt, embP z⟩) → OursEnd Q C ds embP i
  | [], _, _, _ => trivial
  | _ :: _, _, _, h =>
    ⟨fun ρ rt _ _ _ _ => h _ ρ rt _, oursEnd_of_all fun i ρ rt _ => h i ρ rt _⟩

theorem oursShE_of_all {Q : FbIn 256 L t → Prop} {C : CK} : ∀ {ds : List RD}
    {embP : PlainPart (uL C ds) (annShE C ds) → PBt L t} {i : ℕ},
    (∀ i ρ rt z, Q ⟨i, .f5 ρ, rt, embP z⟩) → OursShE Q C ds embP i
  | [], _, _, _ => trivial
  | _ :: _, _, _, h =>
    ⟨fun ρ rt _ _ _ _ => h _ ρ rt _, oursShE_of_all fun i ρ rt _ => h i ρ rt _⟩

/-! ## The nine fields -/

/-- The page's data count the three stretches' rounds and fit them, the chain queries' condition
asked under the row laws' own three premises. -/
structure ChainsFitQ (F : FileJ L t) (Q : FbIn 256 L t → Prop)
    (embP : PlainPart (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).sh (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).ann →
      PBt L t) : Prop where
  n₁ : F.n₁ = ds₁.length
  n₂ : F.n₂ = ds₂.length
  n₃ : F.n₃ = ds₃.length
  f₁ : FitsEndQ F Q C ds₁ (fun z => embL₁ embP (Sum.inr z)) (0 + 1)
  f₂ : FitsShEQ F Q C ds₂ (fun z => embL₂ embP (Sum.inr z)) (F.J + 1)
  f₃ : FitsEndQ F Q C ds₃ (fun z => embL₃ embP (Sum.inr z)) (F.J3 + 1)

/-- **The nine fields**, for a family that speaks by the page's data at the queries that meet Q and
Qg. qG: the queries of the sealing call of which the field `sG` speaks meet Qg. -/
theorem gRowsQ_of {g : Fam (typedOracleFamily 256 (K + 1) L)} {F : FileJ L t} {O : ByteArray → ByteArray}
    {Q : FbIn 256 L t → Prop} {Qg : JoiningRoundQuery 256 L t → Prop} (hO : ∀ s, (O s).size = 32)
    (S : SpeaksQ g t F O Q Qg)
    (embP : PlainPart (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).sh (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).ann →
      PBt L t)
    (A : ChainsFitQ (C := C) (rF := rF) (rJ := rJ) (r3 := r3) (aJ := aJ) (ds₁ := ds₁) (ds₂ := ds₂)
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
    (qG : ∀ ρ : Bits, ρ.length = 256 →
      Qg ⟨F.J, ρ, [], embL₂ embP (Sum.inl (Sum.inr (aJ.plain (pls₂ D π).1).2))⟩)
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
        exact rowEndQ₁ hO S C ds₁ _ (0 + 1) A.f₁ (by omega) (by rw [A.n₁]; omega)
      row₂ := by
        rw [H₂.head.label_eq, eJ]
        exact rowShEQ₂ hO S C ds₂ _ 1 A.f₂ (by omega) (by rw [A.n₂]; omega)
      row₃ := by
        rw [H₃.head.label_eq, eJ3]
        exact rowEndQ₃ hO S C ds₃ _ 1 A.f₃ (by omega) (by rw [A.n₃]; omega)
      s0 := by
        rw [hsalt]
        exact s0Q_of hO S H₁.head H₁.run_eq H₁.pd_eq cms _ rtF _ q₁ t₁
      sG := by
        rw [H₁.head.label_eq, eJ, eG]
        exact S.gAt hO _ qG
      s4 := by
        rw [eJ]
        exact s4Q_of hO S H₂.head H₂.run_eq H₂.pd_eq cms _ [] _ q₂ t₂ u₂
      s3 := by
        rw [eJ3]
        exact s3Q_of hO S H₃.head H₃.run_eq H₃.pd_eq _ _ rt3 _ q₃ t₃ u₃
      late₁ := late₁
      late₃ := late₃ }

end OnBytes.Maker.Page
