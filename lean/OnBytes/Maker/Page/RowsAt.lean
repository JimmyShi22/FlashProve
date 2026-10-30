-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/RowsAt.lean: the nine fields of the tie of a file's three chains that speak of
the typed oracle functions (`GRows`, OnBytes/Maker/Page/RunsTools.lean), at the rounds of a whole
file and at the page's data as OnBytes/Maker/Page/Fill.lean lays them (`fillJ`).

Statements and proofs. OnBytes/Maker/Page/Rows.lean has `GRows` for any data of a page that fit.
OnBytes/Maker/Page/FillLine.lean shows that `fillJ` fits the three stretches, and what it reads off
the three silent rounds' messages as embedded. Here the two are laid together, so that what is left
to ask speaks of the silent rounds' data (`SilentJ`) at the three messages themselves.

Main names:
  `chainsFit_fill`: `ChainsFit` at `fillJ`.
  `fill_stm₁`, `fill_stm₂`, `fill_run₂`, `fill_stm₃`, `fill_run₃`: what `fillJ` reads off a silent
    round's message as embedded is what the silent rounds' data give at that message.
  `QuietAt Q ..`: the condition Q on chain queries holds of every query with a stretch's form of
    head and a plain part of that stretch as embedded, and of the three first queries.
  `rows_fill`: `GRows` at `fillJ`, for a family that speaks by it.
No letter stands under "there is".
Limits: premises, none shown here: that the read-back undoes the embedding; `QuietAt`; the three
chains' heads (`HeadFits`); that the typed string's salt is the first chain's run's value and its
three silent rounds' messages are pF, pJ, p3; that the silent rounds' data give the three statements
and the two later run's values there; the two fields on the instance in a query. These oracle
functions are no encoding in the sense of the soundness theorem (the head of
OnBytes/Maker/Page/Frame.lean). Nothing on soundness.


-/
import OnBytes.Maker.Page.Rows
import OnBytes.Maker.Page.FillLine

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
  (Sl : SilentJ X TF TJ T3) (Q : FbIn 256 L t → Prop)
  (embP : PlainPart (chainsOf C Dw tF tJ t3).sh (chainsOf C Dw tF tJ t3).ann → PBt L t)
  (hrd : ∀ w, rd (embP w) = some w)
include hrd

/-- **The page's data as laid fit the three stretches of a whole file.** -/
theorem chainsFit_fill
    (h₁ : ∀ i ρ rt z, Q ⟨i, .f2 none ρ, rt, e₁ C Dw tF tJ t3 embP (Sum.inr z)⟩)
    (h₂ : ∀ i ρ rt z, Q ⟨i, .f5 ρ, rt, e₂ C Dw tF tJ t3 embP (Sum.inr z)⟩)
    (h₃ : ∀ i ρ rt z, Q ⟨i, .f2 none ρ, rt, e₃ C Dw tF tJ t3 embP (Sum.inr z)⟩) :
    ChainsFit (C := C) (rF := plainRS TF tF) (rJ := plainRS TJ tJ) (r3 := plainRS T3 t3)
      (aJ := RAnn.ofShared .sh _) (ds₁ := toRDs Dw.ds₁) (ds₂ := toRDs Dw.ds₂)
      (ds₃ := toRDs Dw.ds₃) (fillJ C Dw tF tJ t3 rd Sl) Q embP where
  n₁ := (List.length_map _).symm
  n₂ := (List.length_map _).symm
  n₃ := (List.length_map _).symm
  f₁ := fitsEnd₁ C Dw tF tJ t3 rd Sl Q embP hrd h₁
  f₂ := fitsShE₂ C Dw tF tJ t3 rd Sl Q embP hrd h₂
  f₃ := fitsEnd₃ C Dw tF tJ t3 rd Sl Q embP hrd h₃

/-! ## The silent rounds' messages -/

theorem fill_stm₁ (cms : List (Dig 256)) (x : Option X) (p : TF) :
    (fillJ C Dw tF tJ t3 rd Sl).stm₁ cms x (e₁ C Dw tF tJ t3 embP (Sum.inl (Sum.inr p))) =
      Sl.stm₁ cms x p := by
  show (match partAt C Dw tF tJ t3 rd (e₁ C Dw tF tJ t3 embP (Sum.inl (Sum.inr p))) with
    | .front p => Sl.stm₁ cms x p
    | _ => ByteArray.empty) = _
  rw [partAt_front C Dw tF tJ t3 rd embP hrd p]

theorem fill_stm₂ (cms : List (Dig 256)) (rtreq : Bits) (p : TJ) :
    (fillJ C Dw tF tJ t3 rd Sl).stm₂ cms rtreq (e₂ C Dw tF tJ t3 embP (Sum.inl (Sum.inl p))) =
      Sl.stm₂ cms rtreq p := by
  show (match partAt C Dw tF tJ t3 rd (e₂ C Dw tF tJ t3 embP (Sum.inl (Sum.inl p))) with
    | .join p => Sl.stm₂ cms rtreq p
    | _ => ByteArray.empty) = _
  rw [partAt_join C Dw tF tJ t3 rd embP hrd p]

theorem fill_run₂ (p : TJ) :
    (fillJ C Dw tF tJ t3 rd Sl).run₂ (e₂ C Dw tF tJ t3 embP (Sum.inl (Sum.inl p))) =
      Sl.run₂ p := by
  show (match partAt C Dw tF tJ t3 rd (e₂ C Dw tF tJ t3 embP (Sum.inl (Sum.inl p))) with
    | .join p => Sl.run₂ p
    | _ => []) = _
  rw [partAt_join C Dw tF tJ t3 rd embP hrd p]

theorem fill_stm₃ (ρ0 c : Bits) (p : T3) :
    (fillJ C Dw tF tJ t3 rd Sl).stm₃ ρ0 c (e₃ C Dw tF tJ t3 embP (Sum.inl (Sum.inr p))) =
      Sl.stm₃ ρ0 c p := by
  show (match partAt C Dw tF tJ t3 rd (e₃ C Dw tF tJ t3 embP (Sum.inl (Sum.inr p))) with
    | .seam p => Sl.stm₃ ρ0 c p
    | _ => ByteArray.empty) = _
  rw [partAt_seam C Dw tF tJ t3 rd embP hrd p]

theorem fill_run₃ (p : T3) :
    (fillJ C Dw tF tJ t3 rd Sl).run₃ (e₃ C Dw tF tJ t3 embP (Sum.inl (Sum.inr p))) =
      Sl.run₃ p := by
  show (match partAt C Dw tF tJ t3 rd (e₃ C Dw tF tJ t3 embP (Sum.inl (Sum.inr p))) with
    | .seam p => Sl.run₃ p
    | _ => []) = _
  rw [partAt_seam C Dw tF tJ t3 rd embP hrd p]

omit hrd in
/-- The condition Q holds of every chain query of these forms. -/
structure QuietAt (cms : List (Dig 256)) (x : Option X) (salt rtreq ρ0 c : Bits) (pF : TF)
    (pJ : TJ) (p3 : T3) : Prop where
  one : ∀ i ρ rt z, Q ⟨i, .f2 none ρ, rt, e₁ C Dw tF tJ t3 embP (Sum.inr z)⟩
  two : ∀ i ρ rt z, Q ⟨i, .f5 ρ, rt, e₂ C Dw tF tJ t3 embP (Sum.inr z)⟩
  three : ∀ i ρ rt z, Q ⟨i, .f2 none ρ, rt, e₃ C Dw tF tJ t3 embP (Sum.inr z)⟩
  first₁ : Q ⟨0, .f1 cms x salt, [], e₁ C Dw tF tJ t3 embP (Sum.inl (Sum.inr pF))⟩
  first₂ : Q ⟨(fillJ C Dw tF tJ t3 rd Sl).J, .f4 cms rtreq, [],
    e₂ C Dw tF tJ t3 embP (Sum.inl (Sum.inl pJ))⟩
  first₃ : Q ⟨(fillJ C Dw tF tJ t3 rd Sl).J3, .f3 ρ0 c, [],
    e₃ C Dw tF tJ t3 embP (Sum.inl (Sum.inr p3))⟩

variable {K : ℕ} {Xi : Type} (silent : Xi → TF → TJ → T3 → Bool)
  (run : Xi → View → View → View → Bool)

/-- **The nine fields, at the rounds of a whole file and the page's data as laid.** -/
theorem rows_fill {g : Fam (typedOracleFamily 256 (K + 1) L)} {O : ByteArray → ByteArray}
    (hO : ∀ s, (O s).size = 32) (S : Speaks g t (fillJ C Dw tF tJ t3 rd Sl) O Q)
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
    (Qa : QuietAt C Dw tF tJ t3 rd Sl Q embP cms ((xin x).map L.early) (bytesToBits run₁)
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
  exact gRows_of (C := C) (rF := plainRS TF tF) (rJ := plainRS TJ tJ) (r3 := plainRS T3 t3)
    (aJ := RAnn.ofShared .sh _) (ds₁ := toRDs Dw.ds₁) (ds₂ := toRDs Dw.ds₂) (ds₃ := toRDs Dw.ds₃)
    (D := wholeDesc C Dw tF tJ t3 silent run) hO S embP
    (chainsFit_fill C Dw tF tJ t3 rd Sl Q embP hrd Qa.one Qa.two Qa.three) xin cms x π [] [] S₁ S₂
    S₃ o₁ o₂ o₃ rs₁ (hrs.trans (List.length_map _).symm)
    (fun e => some₂ (List.map_eq_nil_iff.1 e)) H₁ H₂ H₃ hsalt Qa.first₁
    ((fill_stm₁ C Dw tF tJ t3 rd Sl embP hrd cms _ _).trans t₁) Qa.first₂
    ((fill_stm₂ C Dw tF tJ t3 rd Sl embP hrd cms _ _).trans t₂)
    ((fill_run₂ C Dw tF tJ t3 rd Sl embP hrd _).trans u₂) Qa.first₃
    ((fill_stm₃ C Dw tF tJ t3 rd Sl embP hrd _ _ _).trans t₃)
    ((fill_run₃ C Dw tF tJ t3 rd Sl embP hrd _).trans u₃) late₁ late₃

end

end OnBytes.Maker.Page
