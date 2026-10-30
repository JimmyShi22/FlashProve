-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/RowsAtQ.lean: the nine fields `GRows` (OnBytes/Maker/Page/RunsTools.lean) at the
rounds of a whole file and the page's data as OnBytes/Maker/Page/Fill.lean lays them (`fillJ`), for
a family that speaks by these data only at queries that meet two conditions.

OnBytes/Maker/Page/RowsAt.lean has this from `Speaks` and `QuietAt`, which asks the chain queries'
condition of every query with a stretch's form of head. Here it comes from `SpeaksQ`
(OnBytes/Maker/Page/ChainsQ.lean) and a record that asks the two conditions of the file's own
queries alone. The text follows OnBytes/Maker/Page/RowsAt.lean closely.

Main definition.
  `QuietAtQ Q Qg ..`: seven fields. `one`, `two`, `three`: Q holds of the three stretches' own
    queries (`OursEnd`, `OursShE`, OnBytes/Maker/Page/RowsQ.lean). `first₁`, `first₂`, `first₃`: Q
    holds of the three chains' first queries, with no roots. `slot`: Qg holds of the sealing call's
    query at the joining round's number, a chaining value of 256 bits, no roots, and the local part
    of the joining round's message.
Main theorems.
  `chainsFitQ_fill`: `ChainsFitQ` at `fillJ`.
  `QuietAt.toQ`: from `QuietAt`, at a second condition that every query meets. At such a condition
    `SpeaksQ.slot` is `Speaks.slot` again.
  `rowsQ_fill`: `GRows` at `fillJ`. Two of the nine fields, those on the round in which an instance
is written (`late₁`, `late₃`), are hypotheses handed through: seven are shown. No letter stands
under "there is".

What is not claimed. None of the hypotheses: those of `rows_fill` (the head of
OnBytes/Maker/Page/RowsAt.lean lists them), with `SpeaksQ` and `QuietAtQ` in the place of `Speaks`
and `QuietAt`. Whether a family that meets `SpeaksQ` is an encoding in the sense of the soundness
theorem is not said. Nothing on soundness.


-/
import OnBytes.Maker.Page.RowsQ
import OnBytes.Maker.Page.RowsAt

set_option autoImplicit false

namespace OnBytes.Maker.Page

open Rom TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Joined.K TypedOracleCompiler.Compile.Batch
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ _root_.Compile.Joined
open TypedOracleCompiler.Run.PQ (sealRead)

section
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {t : Tag} (C : CK) (Dw : WholeD) {TF TJ T3 : Type} (tF : TF)
  (tJ : TJ) (t3 : T3)
  (rd : PBt L t → Option (PlainPart (chainsOf C Dw tF tJ t3).sh (chainsOf C Dw tF tJ t3).ann))
  (Sl : SilentJ X TF TJ T3) (Q : FbIn 256 L t → Prop) (Qg : JoiningRoundQuery 256 L t → Prop)
  (embP : PlainPart (chainsOf C Dw tF tJ t3).sh (chainsOf C Dw tF tJ t3).ann → PBt L t)
  (hrd : ∀ w, rd (embP w) = some w)
include hrd

omit Qg in
/-- **The page's data as laid fit the three stretches of a whole file**, the condition Q asked of
the stretches' own queries alone. -/
theorem chainsFitQ_fill
    (o₁ : OursEnd Q C (toRDs Dw.ds₁) (fun z => e₁ C Dw tF tJ t3 embP (Sum.inr z)) (0 + 1))
    (o₂ : OursShE Q C (toRDs Dw.ds₂) (fun z => e₂ C Dw tF tJ t3 embP (Sum.inr z))
      ((fillJ C Dw tF tJ t3 rd Sl).J + 1))
    (o₃ : OursEnd Q C (toRDs Dw.ds₃) (fun z => e₃ C Dw tF tJ t3 embP (Sum.inr z))
      ((fillJ C Dw tF tJ t3 rd Sl).J3 + 1)) :
    ChainsFitQ (C := C) (rF := plainRS TF tF) (rJ := plainRS TJ tJ) (r3 := plainRS T3 t3)
      (aJ := RAnn.ofShared .sh _) (ds₁ := toRDs Dw.ds₁) (ds₂ := toRDs Dw.ds₂)
      (ds₃ := toRDs Dw.ds₃) (fillJ C Dw tF tJ t3 rd Sl) Q embP where
  n₁ := (List.length_map _).symm
  n₂ := (List.length_map _).symm
  n₃ := (List.length_map _).symm
  f₁ := fitsEndQ_of
    (fitsEnd₁ C Dw tF tJ t3 rd Sl (fun _ => True) embP hrd fun _ _ _ _ => trivial) o₁
  f₂ := fitsShEQ_of
    (fitsShE₂ C Dw tF tJ t3 rd Sl (fun _ => True) embP hrd fun _ _ _ _ => trivial) o₂
  f₃ := fitsEndQ_of
    (fitsEnd₃ C Dw tF tJ t3 rd Sl (fun _ => True) embP hrd fun _ _ _ _ => trivial) o₃

omit hrd in
/-- The conditions Q and Qg hold of the file's own queries. -/
structure QuietAtQ (cms : List (Dig 256)) (x : Option X) (salt rtreq ρ0 c : Bits) (pF : TF)
    (pJ : TJ) (p3 : T3) : Prop where
  one : OursEnd Q C (toRDs Dw.ds₁) (fun z => e₁ C Dw tF tJ t3 embP (Sum.inr z)) (0 + 1)
  two : OursShE Q C (toRDs Dw.ds₂) (fun z => e₂ C Dw tF tJ t3 embP (Sum.inr z))
    ((fillJ C Dw tF tJ t3 rd Sl).J + 1)
  three : OursEnd Q C (toRDs Dw.ds₃) (fun z => e₃ C Dw tF tJ t3 embP (Sum.inr z))
    ((fillJ C Dw tF tJ t3 rd Sl).J3 + 1)
  first₁ : Q ⟨0, .f1 cms x salt, [], e₁ C Dw tF tJ t3 embP (Sum.inl (Sum.inr pF))⟩
  first₂ : Q ⟨(fillJ C Dw tF tJ t3 rd Sl).J, .f4 cms rtreq, [],
    e₂ C Dw tF tJ t3 embP (Sum.inl (Sum.inl pJ))⟩
  first₃ : Q ⟨(fillJ C Dw tF tJ t3 rd Sl).J3, .f3 ρ0 c, [],
    e₃ C Dw tF tJ t3 embP (Sum.inl (Sum.inr p3))⟩
  slot : ∀ ρ : Bits, ρ.length = 256 → Qg ⟨(fillJ C Dw tF tJ t3 rd Sl).J, ρ, [],
    e₂ C Dw tF tJ t3 embP
      (Sum.inl (Sum.inr ((RAnn.ofShared .sh (plainRS TJ tJ).up).plain pJ).2))⟩

omit hrd in
/-- The record of OnBytes/Maker/Page/RowsAt.lean gives this one, at a second condition that every
query meets. -/
theorem QuietAt.toQ {cms : List (Dig 256)} {x : Option X} {salt rtreq ρ0 c : Bits} {pF : TF}
    {pJ : TJ} {p3 : T3} (A : QuietAt C Dw tF tJ t3 rd Sl Q embP cms x salt rtreq ρ0 c pF pJ p3)
    (hg : ∀ q, Qg q) : QuietAtQ C Dw tF tJ t3 rd Sl Q Qg embP cms x salt rtreq ρ0 c pF pJ p3 :=
  ⟨oursEnd_of_all A.one, oursShE_of_all A.two, oursEnd_of_all A.three, A.first₁, A.first₂, A.first₃,
    fun _ _ => hg _⟩

variable {K : ℕ} {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool)
  (run : Xi → View → View → View → Bool)

/-- **The nine fields, at the rounds of a whole file and the page's data as laid**, for a family
that speaks by them at the queries that meet Q and Qg. -/
theorem rowsQ_fill {g : Fam (typedOracleFamily 256 (K + 1) L)} {O : ByteArray → ByteArray}
    (hO : ∀ s, (O s).size = 32) (S : SpeaksQ g t (fillJ C Dw tF tJ t3 rd Sl) O Q Qg)
    (xin : Xi → Option X) (cms : List (Dig 256)) (x : Xi)
    (π : OneProtocolProof 256 (wholeDesc C Dw tF tJ t3 silent run).batch) (S₁ S₂ S₃ : Fmt.SpecX)
    (o₁ o₂ o₃ : Fmt.ChainOut) (rs₁ : List Fmt.Round) (hrs : rs₁.length = Dw.ds₁.length)
    (some₂ : Dw.ds₂ ≠ []) {st₁ st₂ st₃ rnd₁ rnd₂ rnd₃ run₁ run₂ run₃ : ByteArray}
    (H₁ : HeadFits O S₁ o₁ Sl.lab₁ Sl.pd₁ st₁ rnd₁ run₁)
    (H₂ : HeadFits O S₂ o₂ Sl.lab₂ Sl.pd₂ st₂ rnd₂ run₂)
    (H₃ : HeadFits O S₃ o₃ Sl.lab₃ Sl.pd₃ st₃ rnd₃ run₃) (pF : TF) (pJ : TJ) (p3 : T3)
    (hsalt : π.salt = bytesToBits run₁)
    (hF : (pls₁ (wholeDesc C Dw tF tJ t3 silent run) π).1 = pF)
    (hJ : (pls₂ (wholeDesc C Dw tF tJ t3 silent run) π).1 = pJ)
    (h3 : (pls₃ (wholeDesc C Dw tF tJ t3 silent run) π).1 = p3)
    (Qa : QuietAtQ C Dw tF tJ t3 rd Sl Q Qg embP cms ((xin x).map L.early) (bytesToBits run₁)
      (List.ofFn π.rtreq) (List.ofFn (bytesToDig (sealRead o₂)))
      (List.ofFn (bytesToDig (sealRead o₁))) pF pJ p3)
    (t₁ : Sl.stm₁ cms ((xin x).map L.early) pF = st₁)
    (t₂ : Sl.stm₂ cms (List.ofFn π.rtreq) pJ = st₂) (u₂ : Sl.run₂ pJ = bytesToBits run₂)
    (t₃ : Sl.stm₃ (List.ofFn (bytesToDig (sealRead o₂))) (List.ofFn (bytesToDig (sealRead o₁))) p3 =
      st₃) (u₃ : Sl.run₃ p3 = bytesToBits run₃)
    (late₁ : xin x = none ∨ ∀ k, k < (toRDs Dw.ds₁).length → L.late ≠ some (0 + 1 + k))
    (late₃ : xin x = none ∨ ∀ k, k < (toRDs Dw.ds₃).length →
      L.late ≠ some (0 + (chainsOf C Dw tF tJ t3).c₁.length +
        (chainsOf C Dw tF tJ t3).c₂.length + 1 + k)) :
    GRows (L := L) (t := t) (C := C) (K := K) (rF := plainRS TF tF) (rJ := plainRS TJ tJ)
      (r3 := plainRS T3 t3) (aJ := RAnn.ofShared .sh _) (ds₁ := toRDs Dw.ds₁)
      (ds₂ := toRDs Dw.ds₂) (ds₃ := toRDs Dw.ds₃) (D := wholeDesc C Dw tF tJ t3 silent run) embP
      xin cms x π g O [] [] S₁ S₂ S₃ o₁ o₂ o₃ rs₁ := by
  subst hF hJ h3
  exact gRowsQ_of (C := C) (rF := plainRS TF tF) (rJ := plainRS TJ tJ) (r3 := plainRS T3 t3)
    (aJ := RAnn.ofShared .sh _) (ds₁ := toRDs Dw.ds₁) (ds₂ := toRDs Dw.ds₂) (ds₃ := toRDs Dw.ds₃)
    (D := wholeDesc C Dw tF tJ t3 silent run) hO S embP
    (chainsFitQ_fill C Dw tF tJ t3 rd Sl Q embP hrd Qa.one Qa.two Qa.three) xin cms x π [] [] S₁ S₂
    S₃ o₁ o₂ o₃ rs₁ (hrs.trans (List.length_map _).symm)
    (fun e => some₂ (List.map_eq_nil_iff.1 e)) H₁ H₂ H₃ hsalt Qa.first₁
    ((fill_stm₁ C Dw tF tJ t3 rd Sl embP hrd cms _ _).trans t₁) Qa.first₂
    ((fill_stm₂ C Dw tF tJ t3 rd Sl embP hrd cms _ _).trans t₂)
    ((fill_run₂ C Dw tF tJ t3 rd Sl embP hrd _).trans u₂) Qa.first₃
    ((fill_stm₃ C Dw tF tJ t3 rd Sl embP hrd _ _ _).trans t₃)
    ((fill_run₃ C Dw tF tJ t3 rd Sl embP hrd _).trans u₃) Qa.slot late₁ late₃

end

end OnBytes.Maker.Page
