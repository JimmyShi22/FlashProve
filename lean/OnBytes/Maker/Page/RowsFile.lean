-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/RowsFile.lean: the nine fields of the tie of a file's three chains that speak of
the typed oracle functions (`GRows`, OnBytes/Maker/Page/RunsTools.lean), for a key file and for a
proof file: at the record of the verifier program's own reading, at a value of the typing, at the
page's data for such a file, and at the realised oracle.

Statements and proofs. OnBytes/Maker/Page/RowsAt.lean has `GRows` at the page's data as laid, under
premises on the three chains' heads, on the typed string and on the silent rounds' data. Here these
are paid: the heads by OnBytes/Maker/Page/AtOracle.lean, the typed string's fields by
OnBytes/Maker/Page/AtValue.lean, the silent rounds' data by OnBytes/Maker/Page/Silent.lean.

Main names:
  `join_run`: what the joining round's message of a file as read is.
  `rows_key`: a key file. `rows_proof`: a proof file.
What is left to ask: the record of the reading (`ThreeRead`) with the first chain's description; the
bounds that the hash's domain asks (`SmallThree`); that the family speaks by the page's data
(`Speaks`) at a condition Q that every query of these forms meets, whatever its outer roots,
instance, salt, request root, seals and silent message (`QuietAt`); that the read-back undoes the
embedding; a value of the typing at the three silent rounds' messages of the file as read; that the
first of the outer roots is the table's root; that this root, the binding tree's root and the two
seals have 32 bytes; for a proof file that the instance in the first query gives the request's
two strings; the count of the first chain's rounds; the two fields on the instance in a query.
No letter stands under "there is".
In the premise on the request's two strings req is the caller's free letter: nothing asks that it
spell the instance, be one to one, or that its two strings say one request, and the constant
function with the value (request, words) meets it where an instance stands. It ties the first
query's string to the pair, not to the typed instance.
Limits: none of these premises is shown here. All is said at the realised oracle `Fmt.oracle`. These
oracle functions are no encoding in the sense of the soundness theorem (the head of
OnBytes/Maker/Page/Frame.lean). Nothing on soundness.


-/
import OnBytes.Maker.Page.RowsAt
import OnBytes.Maker.Page.Silent
import OnBytes.Maker.Page.AtValue

set_option autoImplicit false

namespace OnBytes.Maker.Page

open Rom TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Joined.K TypedOracleCompiler.Compile.Batch
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ _root_.Compile.Joined
open OnBytes.Maker (FrontMsg frontOf joinOf seamOf)
open OnBytes.Params (Rounds)

/-- What the joining round's message of a file as read is. -/
theorem join_run {A : Type} {answers : A} {r : Proof.TailRead} {pJ : JoinMsg A ByteArray}
    (h : joinOf answers r = some pJ) : r.shared.out.run = some pJ.run ∧ pJ.answers = answers := by
  unfold joinOf at h
  cases hr : r.shared.out.run with
  | none => rw [hr] at h; cases h
  | some x =>
    rw [hr] at h
    obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl⟩

section
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {t : Tag} (C : CK) (Dw : WholeD)
  (tF : FrontMsg (List E)) (tJ : JoinMsg (List E) ByteArray) (t3 : ByteArray)
  (rd : PBt L t → Option (PlainPart (chainsOf C Dw tF tJ t3).sh (chainsOf C Dw tF tJ t3).ann))
  (Q : FbIn 256 L t → Prop)
  (embP : PlainPart (chainsOf C Dw tF tJ t3).sh (chainsOf C Dw tF tJ t3).ann → PBt L t)
  (hrd : ∀ w, rd (embP w) = some w) {K : ℕ} {Xi : Type}
  (silent : Xi → FrontMsg (List E) → JoinMsg (List E) ByteArray → ByteArray → Bool)
  (run : Xi → View → View → View → Bool) {g : Fam (typedOracleFamily 256 (K + 1) L)}
  {file : ByteArray} {R₁ : Rounds} {dry : Proof.FirstEnd} {S₁ : Fmt.SpecX} {r : Proof.TailRead}
  {seal1 seal2 : ByteArray} {R₂ : Rounds} {dry2 : Proof.SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds}
  {S₃ : Fmt.SpecX} (table : Params.TableName)
include hrd

/-- **A key file.** -/
theorem rows_key (k : Params.KeyChains) {j : ℕ}
    (T : ThreeRead (Key.tailPublic k table) (Key.oneTime k.oneTime) (Key.startOf k.oneTime) file j
      R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : k.oneTime.describe table R₁ = some S₁) (hsm : SmallThree S₁ S₂ S₃ file)
    (S : Speaks g t (fillJ C Dw tF tJ t3 rd (silentKey (Fmt.HO Fmt.oracle) k X)) Fmt.oracle Q)
    (Qa : ∀ cms x salt rtreq ρ0 c pF pJ p3, QuietAt C Dw tF tJ t3 rd
      (silentKey (Fmt.HO Fmt.oracle) k X) Q embP cms x salt rtreq ρ0 c pF pJ p3)
    (xin : Xi → Option X) (rest : List (Dig 256)) (x : Xi)
    (π : OneProtocolProof 256 (wholeDesc C Dw tF tJ t3 silent run).batch) (copy : ℕ)
    (pJ : JoinMsg (List E) ByteArray) (p3 : ByteArray) (hJ : joinOf table.answers r = some pJ)
    (h3 : seamOf r = some p3) (tabs : List (ℕ × List (ℕ × Row3)))
    (ext : (oneExternalString (2 ^ Dw.a) SgX).Pos → Option (Opening 256 SgX)) (salt : ByteArray)
    (path : List ByteArray)
    (hπ : toBPrfW C Dw tF tJ t3 silent run (frontOf table.answers copy) pJ p3 tabs ext salt path r =
      some π)
    (z₁ : table.root.size = 32) (z₂ : r.place.root.size = 32) (z₃ : seal1.size = 32)
    (z₄ : seal2.size = 32) (rs₁ : List Fmt.Round) (hrs : rs₁.length = Dw.ds₁.length)
    (some₂ : Dw.ds₂ ≠ [])
    (late₁ : xin x = none ∨ ∀ n, n < (toRDs Dw.ds₁).length → L.late ≠ some (0 + 1 + n))
    (late₃ : xin x = none ∨ ∀ n, n < (toRDs Dw.ds₃).length →
      L.late ≠ some (0 + (chainsOf C Dw tF tJ t3).c₁.length +
        (chainsOf C Dw tF tJ t3).c₂.length + 1 + n)) :
    GRows (L := L) (t := t) (C := C) (K := K) (rF := plainRS _ tF) (rJ := plainRS _ tJ)
      (r3 := plainRS _ t3) (aJ := RAnn.ofShared .sh _) (ds₁ := toRDs Dw.ds₁)
      (ds₂ := toRDs Dw.ds₂) (ds₃ := toRDs Dw.ds₃) (D := wholeDesc C Dw tF tJ t3 silent run) embP
      xin (bytesToDig table.root :: rest) x π g Fmt.oracle [] [] S₁ S₂ S₃ r.first.out r.shared.out
      r.second.out rs₁ := by
  have hS₁' : Params.describeWith k.oneTime.given Params.labelOneTime
      (Params.OneTime.statement table) .inFile R₁ 0 = some S₁ := hS₁
  obtain ⟨⟨rnd₁, -, A₁⟩, A₂, rnd₃, -, A₃⟩ := three_firstO T hS₁' hsm
  obtain ⟨run₁, hr₁, hsalt⟩ := value_salt C Dw tF tJ t3 silent run _ pJ p3 tabs ext salt path r π hπ
  obtain ⟨hr₂, ha₂⟩ := join_run hJ
  obtain ⟨d₁, d₂, d₃⟩ := key_pd (Fmt.HO Fmt.oracle) k X hS₁ T.shared_spec T.second_spec
  obtain ⟨e₁, e₂⟩ := seals_read T
  have eq : π.rtreq = bytesToDig r.place.root :=
    value_rtreq C Dw tF tJ t3 silent run _ pJ p3 tabs ext salt path r π hπ
  have hpJ : pJ = ⟨table.answers, pJ.run⟩ := by
    rw [← ha₂]
  exact rows_fill C Dw tF tJ t3 rd (silentKey (Fmt.HO Fmt.oracle) k X) Q embP hrd silent run
    oracle_32 S xin _ x π S₁ S₂ S₃ _ _ _ rs₁ hrs some₂ ⟨A₁, hr₁, d₁⟩ ⟨A₂, hr₂, d₂⟩ ⟨A₃, h3, d₃⟩
    (frontOf table.answers copy) pJ p3 hsalt
    (value_front C Dw tF tJ t3 silent run _ pJ p3 tabs ext salt path r π hπ)
    (value_join C Dw tF tJ t3 silent run _ pJ p3 tabs ext salt path r π hπ)
    (value_seam C Dw tF tJ t3 silent run _ pJ p3 tabs ext salt path r π hπ) (Qa _ _ _ _ _ _ _ _ _)
    (key_stm₁ _ table z₁ rest k _ copy)
    (by rw [eq, hpJ]; exact key_stm₂ _ table z₁ rest k X r.place.root pJ.run z₂) rfl
    (by rw [e₁, e₂]; exact key_stm₃ _ k X seal1 seal2 p3 z₃ z₄) rfl late₁ late₃

/-- **A proof file.** block: the first chain's block; req: from the instance, the value of the item
"request" and the request file's bytes. -/
theorem rows_proof (c : Params.ProofChains) (copy : ℕ) (request words : ByteArray)
    (block : Blk Proof.FirstEnd) (req : X → ByteArray × ByteArray) {i : ℕ}
    (T : ThreeRead (Proof.tailPublic c table) block (Proof.firstStart c.first) file i R₁ dry S₁ r
      seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : c.first.describe table copy request words R₁ = some S₁) (hsm : SmallThree S₁ S₂ S₃ file)
    (S : Speaks g t (fillJ C Dw tF tJ t3 rd (silentProof (Fmt.HO Fmt.oracle) c req)) Fmt.oracle Q)
    (Qa : ∀ cms x salt rtreq ρ0 c' pF pJ p3, QuietAt C Dw tF tJ t3 rd
      (silentProof (Fmt.HO Fmt.oracle) c req) Q embP cms x salt rtreq ρ0 c' pF pJ p3)
    (xin : Xi → Option X) (rest : List (Dig 256)) (x : Xi)
    (hreq : (((xin x).map L.early).map req).getD default = (request, words))
    (π : OneProtocolProof 256 (wholeDesc C Dw tF tJ t3 silent run).batch)
    (pJ : JoinMsg (List E) ByteArray) (p3 : ByteArray) (hJ : joinOf table.answers r = some pJ)
    (h3 : seamOf r = some p3) (tabs : List (ℕ × List (ℕ × Row3)))
    (ext : (oneExternalString (2 ^ Dw.a) SgX).Pos → Option (Opening 256 SgX)) (salt : ByteArray)
    (path : List ByteArray)
    (hπ : toBPrfW C Dw tF tJ t3 silent run (frontOf table.answers copy) pJ p3 tabs ext salt path r =
      some π)
    (z₁ : table.root.size = 32) (z₂ : r.place.root.size = 32) (z₃ : seal1.size = 32)
    (z₄ : seal2.size = 32) (rs₁ : List Fmt.Round) (hrs : rs₁.length = Dw.ds₁.length)
    (some₂ : Dw.ds₂ ≠ [])
    (late₁ : xin x = none ∨ ∀ n, n < (toRDs Dw.ds₁).length → L.late ≠ some (0 + 1 + n))
    (late₃ : xin x = none ∨ ∀ n, n < (toRDs Dw.ds₃).length →
      L.late ≠ some (0 + (chainsOf C Dw tF tJ t3).c₁.length +
        (chainsOf C Dw tF tJ t3).c₂.length + 1 + n)) :
    GRows (L := L) (t := t) (C := C) (K := K) (rF := plainRS _ tF) (rJ := plainRS _ tJ)
      (r3 := plainRS _ t3) (aJ := RAnn.ofShared .sh _) (ds₁ := toRDs Dw.ds₁)
      (ds₂ := toRDs Dw.ds₂) (ds₃ := toRDs Dw.ds₃) (D := wholeDesc C Dw tF tJ t3 silent run) embP
      xin (bytesToDig table.root :: rest) x π g Fmt.oracle [] [] S₁ S₂ S₃ r.first.out r.shared.out
      r.second.out rs₁ := by
  have hS₁' : Params.describeWith c.first.given Params.labelFirst
      (Params.First.statement table copy request words) .inFile R₁ 0 = some S₁ := hS₁
  obtain ⟨⟨rnd₁, -, A₁⟩, A₂, rnd₃, -, A₃⟩ := three_firstO T hS₁' hsm
  obtain ⟨run₁, hr₁, hsalt⟩ := value_salt C Dw tF tJ t3 silent run _ pJ p3 tabs ext salt path r π hπ
  obtain ⟨hr₂, ha₂⟩ := join_run hJ
  obtain ⟨d₁, d₂, d₃⟩ := proof_pd (Fmt.HO Fmt.oracle) c req hS₁ T.shared_spec T.second_spec
  obtain ⟨e₁, e₂⟩ := seals_read T
  have eq : π.rtreq = bytesToDig r.place.root :=
    value_rtreq C Dw tF tJ t3 silent run _ pJ p3 tabs ext salt path r π hπ
  have hpJ : pJ = ⟨table.answers, pJ.run⟩ := by
    rw [← ha₂]
  have t₁ : (silentProof (Fmt.HO Fmt.oracle) c req).stm₁ (bytesToDig table.root :: rest)
      ((xin x).map L.early) (frontOf table.answers copy) =
      Params.First.statement table copy request words := by
    show Params.First.statement (tableOf _ table.answers) copy _ _ = _
    rw [tableOf_eq table z₁, hreq]
  exact rows_fill C Dw tF tJ t3 rd (silentProof (Fmt.HO Fmt.oracle) c req) Q embP hrd silent run
    oracle_32 S xin _ x π S₁ S₂ S₃ _ _ _ rs₁ hrs some₂ ⟨A₁, hr₁, d₁⟩ ⟨A₂, hr₂, d₂⟩ ⟨A₃, h3, d₃⟩
    (frontOf table.answers copy) pJ p3 hsalt
    (value_front C Dw tF tJ t3 silent run _ pJ p3 tabs ext salt path r π hπ)
    (value_join C Dw tF tJ t3 silent run _ pJ p3 tabs ext salt path r π hπ)
    (value_seam C Dw tF tJ t3 silent run _ pJ p3 tabs ext salt path r π hπ) (Qa _ _ _ _ _ _ _ _ _)
    t₁ (by rw [eq, hpJ]; exact proof_stm₂ _ table z₁ rest c req r.place.root pJ.run z₂) rfl
    (by rw [e₁, e₂]; exact proof_stm₃ _ c req seal1 seal2 p3 z₃ z₄) rfl late₁ late₃

end

end OnBytes.Maker.Page
