-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/AtFiles.lean: the nine fields on typed oracle functions (`GRows`,
OnBytes/Maker/Page/RunsTools.lean) for a key file and for a proof file, at data that are made of
three lists of rounds and at a value of the typing of a whole file.

OnBytes/Maker/Page/RowsFile.lean and Sizes.lean give `GRows` for a key file and for a proof file
(`rows_key'`, `rows_proof'`), general in the data and in the first chain's rounds, at a value of
`toBPrfW`. This file lays in the rounds at which OnBytes/Maker/Page/Runs.lean takes `GRows`, at data
that are a letter W with the equation W = `Three.Whole.of` R₁ R₂ R₃, and pays two counts.

Main theorems.
  `ds₁_length`: the first stretch's data are as many as the first chain's rounds without the last.
  `ds₂_ne`: the second stretch has a round, where the test `Three.Whole.fits` passes.
  `rows_key_value`, `rows_proof_value`: `GRows`, in the form that `readL_of_read`, `draws_of_read`,
    `sealAt_of_read` (OnBytes/Maker/Page/Runs.lean) and `accept_of_read`
    (OnBytes/Maker/Page/Accept.lean) take, with the outer roots beginning with the table's root.
No letter stands under "there is" in these statements.

The third list R₃ in W is the caller's letter: no hypothesis of these two statements ties it to the
reading, whose third chain was read under its own rounds; OnBytes/Maker/Page/Runs.lean ties it.

What is not claimed. None of the hypotheses. They are: the record of the reading, and the first
chain's description; the test `Three.Whole.fits`; the bounds that the hash's domain asks for, a test
on each file; that the reading back of a plain part undoes the embedding; that g speaks by the
page's data as laid (`Speaks`); the condition Q of every query with a stretch's form of head and of
the three first queries at all values (`QuietAt`, under "for all" over nine letters: more than the
file's own queries); the joining round's and the seam's messages; that the typing returns π; that
the table's root has 32 bytes; the two conditions on the round in which an instance is written; for
a proof file, the hypothesis on the request's two strings. No law is asked of req in it: the
constant function at (request, words) meets it, and nothing asks that the two say one request. So it
ties the first query's string to the pair, not to the typed instance; where there is no instance it
says that both strings are empty.
Two of the nine fields, those on the round in which an instance is written (`late₁`,
`late₃`), are hypotheses handed through: seven are shown.
A family that is read through a one-to-one code meets `Speaks.slot` only where O has one answer at
two strings (the head of OnBytes/Maker/Page/ChainsQ.lean): that these oracle functions are an
encoding in the sense of the soundness theorem is not said. Nothing on soundness.


-/
import OnBytes.Maker.Page.Sizes
import OnBytes.Maker.Page.Runs

set_option autoImplicit false

namespace OnBytes.Maker.Page

open Rom TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Joined.K TypedOracleCompiler.Compile.Batch
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ _root_.Compile.Joined
open OnBytes.Maker (FrontMsg frontOf joinOf seamOf)
open OnBytes.Params (Rounds)
open OnBytes.Proof (FirstEnd SharedEnd TailRead)

/-- The first stretch's data are as many as the first chain's rounds without the last. -/
theorem ds₁_length (a : ℕ) (R₁ R₂ R₃ : Rounds) :
    ((R₁.map (·.1)).dropLast).length = (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).ds₁.length := by
  have e := congrArg List.length (stored_ds₁ R₁ R₂ R₃)
  rw [List.length_map, List.length_map] at e
  show _ = ((Three.Whole.of R₁ R₂ R₃).ds₁.dropLast.map rdtOf).length
  rw [List.length_map, List.length_dropLast, List.length_dropLast, List.length_map, e]

/-- The second stretch has a round, where the test passes. -/
theorem ds₂_ne (a : ℕ) (R₁ R₂ R₃ : Rounds) (h : Three.Whole.fits R₁ R₂ R₃ 2 = true) :
    (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).ds₂ ≠ [] := by
  obtain ⟨-, r₂, w₂, -⟩ := seals_of_fits R₁ R₂ R₃ h
  intro e
  have e1 := congrArg List.length (stored_ds₂ R₁ R₂ R₃)
  have e2 : ((Three.Whole.of R₁ R₂ R₃).ds₂.map rdtOf).length = 0 := by
    have e' : (Three.Whole.of R₁ R₂ R₃).ds₂.map rdtOf = [] := e
    rw [e']
    rfl
  rw [List.length_map] at e2
  rw [List.length_map, List.length_map, e2] at e1
  rw [List.eq_nil_of_length_eq_zero e1.symm] at w₂
  cases w₂

variable {file : ByteArray} {i : ℕ} {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead}
  {seal1 seal2 : ByteArray} {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds}
  {S₃ : Fmt.SpecX} {R₃ : Rounds} {I X : Type} {L : BatchProtocolWithLeafBody I X} {t : Tag} (C : CK) {K : ℕ} (a : ℕ)
  (tF : FrontMsg (List E)) (tJ : JoinMsg (List E) ByteArray) (t3 : ByteArray) {Xi : Type}
  (silent : Xi → FrontMsg (List E) → JoinMsg (List E) ByteArray → ByteArray → Bool) (run : Xi → View
    → View → View → Bool)

/-- **A key file.** -/
theorem rows_key_value (W : Three.Whole) (hW : W = Three.Whole.of R₁ R₂ R₃) (k : Params.KeyChains)
    (table : Params.TableName) (hfit : Three.Whole.fits R₁ R₂ R₃ 2 = true)
    (T : ThreeRead (Key.tailPublic k table) (Key.oneTime k.oneTime) (Key.startOf k.oneTime) file i
      R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃) (hS₁ : k.oneTime.describe table R₁ = some S₁)
    (hsm : SmallThree S₁ S₂ S₃ file)
    (rd : PBt L t → Option
      (PlainPart (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ t3).ann))
    (Q : FbIn 256 L t → Prop)
    (embP : PlainPart (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ t3).ann →
      PBt L t) (hrd : ∀ w, rd (embP w) = some w) (g : Fam (typedOracleFamily 256 (K + 1) L))
    (S : Speaks g t (fillJ C (WholeD.of a W) tF tJ t3 rd (silentKey (Fmt.HO Fmt.oracle) k X))
      Fmt.oracle Q)
    (Qa : ∀ cms x salt rtreq ρ0 c' pF pJ p3, QuietAt C (WholeD.of a W) tF tJ t3 rd
      (silentKey (Fmt.HO Fmt.oracle) k X) Q embP cms x salt rtreq ρ0 c' pF pJ p3)
    (xin : Xi → Option X) (rest : List (Dig 256)) (x : Xi)
    (π : OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch) (copy : ℕ)
    (pJ : JoinMsg (List E) ByteArray) (p3 : ByteArray) (hJ : joinOf table.answers r = some pJ)
    (h3 : seamOf r = some p3) (sb : ℕ) (cfg salt : ByteArray) (path : List ByteArray)
    (hπ : typeFile C a W tF tJ t3 silent run sb cfg (frontOf table.answers copy) pJ p3 salt path r =
      some π) (z₁ : table.root.size = 32)
    (late₁ : xin x = none ∨ ∀ n, n < (toRDs (WholeD.of a W).ds₁).length → L.late ≠ some (0 + 1 + n))
    (late₃ : xin x = none ∨ ∀ n, n < (toRDs (WholeD.of a W).ds₃).length → L.late ≠ some (0 +
      (chainsOf C (WholeD.of a W) tF tJ t3).c₁.length + (chainsOf C (WholeD.of a W) tF tJ
      t3).c₂.length + 1 + n)) :
    GRows (L := L) (t := t) (C := C) (K := K) (rF := plainRS _ tF) (rJ := plainRS _ tJ)
      (r3 := plainRS _ t3) (aJ := RAnn.ofShared .sh _) (ds₁ := toRDs (WholeD.of a W).ds₁)
      (ds₂ := toRDs (WholeD.of a W).ds₂) (ds₃ := toRDs (WholeD.of a W).ds₃)
      (D := wholeDesc C (WholeD.of a W) tF tJ t3 silent run) embP xin
      (bytesToDig table.root :: rest) x π g Fmt.oracle [] [] S₁ S₂ S₃ r.first.out r.shared.out
      r.second.out (R₁.map (·.1)).dropLast := by
  subst hW
  obtain ⟨tabs, ext, -, -, hπ'⟩ := typeFile_some C a (Three.Whole.of R₁ R₂ R₃) tF tJ t3 silent run
    sb cfg _ pJ p3 salt path r π hπ
  exact rows_key' C _ tF tJ t3 rd Q embP hrd silent run table k T hS₁ hsm S Qa xin rest x π copy pJ
    p3 hJ h3 tabs ext salt path hπ' z₁ _ (ds₁_length a R₁ R₂ R₃) (ds₂_ne a R₁ R₂ R₃ hfit) late₁
      late₃

/-- **A proof file.** block: the first chain's block; req: a function from instances to two strings
of bytes, a letter. -/
theorem rows_proof_value (W : Three.Whole) (hW : W = Three.Whole.of R₁ R₂ R₃)
    (c : Params.ProofChains) (table : Params.TableName) (copy : ℕ) (request words : ByteArray)
    (block : Blk FirstEnd) (req : X → ByteArray × ByteArray) (hfit : Three.Whole.fits R₁ R₂ R₃ 2 =
        true)
    (T : ThreeRead (Proof.tailPublic c table) block (Proof.firstStart c.first) file i R₁ dry S₁ r
      seal1 seal2 R₂ dry2 S₂ R₃' S₃) (hS₁ : c.first.describe table copy request words R₁ = some S₁)
    (hsm : SmallThree S₁ S₂ S₃ file)
    (rd : PBt L t → Option
      (PlainPart (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ t3).ann))
    (Q : FbIn 256 L t → Prop)
    (embP : PlainPart (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ t3).ann →
      PBt L t) (hrd : ∀ w, rd (embP w) = some w) (g : Fam (typedOracleFamily 256 (K + 1) L))
    (S : Speaks g t (fillJ C (WholeD.of a W) tF tJ t3 rd (silentProof (Fmt.HO Fmt.oracle) c req))
      Fmt.oracle Q)
    (Qa : ∀ cms x salt rtreq ρ0 c' pF pJ p3, QuietAt C (WholeD.of a W) tF tJ t3 rd
      (silentProof (Fmt.HO Fmt.oracle) c req) Q embP cms x salt rtreq ρ0 c' pF pJ p3)
    (xin : Xi → Option X) (rest : List (Dig 256)) (x : Xi)
    (hreq : (((xin x).map L.early).map req).getD default = (request, words))
    (π : OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch)
    (pJ : JoinMsg (List E) ByteArray) (p3 : ByteArray) (hJ : joinOf table.answers r = some pJ)
    (h3 : seamOf r = some p3) (sb : ℕ) (cfg salt : ByteArray) (path : List ByteArray)
    (hπ : typeFile C a W tF tJ t3 silent run sb cfg (frontOf table.answers copy) pJ p3 salt path r =
      some π) (z₁ : table.root.size = 32)
    (late₁ : xin x = none ∨ ∀ n, n < (toRDs (WholeD.of a W).ds₁).length → L.late ≠ some (0 + 1 + n))
    (late₃ : xin x = none ∨ ∀ n, n < (toRDs (WholeD.of a W).ds₃).length → L.late ≠ some (0 +
      (chainsOf C (WholeD.of a W) tF tJ t3).c₁.length + (chainsOf C (WholeD.of a W) tF tJ
      t3).c₂.length + 1 + n)) :
    GRows (L := L) (t := t) (C := C) (K := K) (rF := plainRS _ tF) (rJ := plainRS _ tJ)
      (r3 := plainRS _ t3) (aJ := RAnn.ofShared .sh _) (ds₁ := toRDs (WholeD.of a W).ds₁)
      (ds₂ := toRDs (WholeD.of a W).ds₂) (ds₃ := toRDs (WholeD.of a W).ds₃)
      (D := wholeDesc C (WholeD.of a W) tF tJ t3 silent run) embP xin
      (bytesToDig table.root :: rest) x π g Fmt.oracle [] [] S₁ S₂ S₃ r.first.out r.shared.out
      r.second.out (R₁.map (·.1)).dropLast := by
  subst hW
  obtain ⟨tabs, ext, -, -, hπ'⟩ := typeFile_some C a (Three.Whole.of R₁ R₂ R₃) tF tJ t3 silent run
    sb cfg _ pJ p3 salt path r π hπ
  exact rows_proof' C _ tF tJ t3 rd Q embP hrd silent run table c copy request words block req T hS₁
      hsm S
    Qa xin rest x hreq π pJ p3 hJ h3 tabs ext salt path hπ' z₁ _ (ds₁_length a R₁ R₂ R₃) (ds₂_ne a
      R₁ R₂ R₃ hfit) late₁ late₃

end OnBytes.Maker.Page
