-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/Sizes.lean: the binding tree's root and the two seals of a file as the verifier
program's reader has read it have 32 bytes each; so has the root of a table that the program has
read out of a key file.

Statements and proofs. OnBytes/Maker/Page/RowsFile.lean asks these four sizes. The laws are there:
a seal of what the program's reader has read has 32 bytes (`OnBytes.TieK.seal_size`,
OnBytes/TieK/SealSize.lean); the binding tree's root takes the place of the shared chain's random
bytes, of which the head of a chain asks 32 (`HeadIs.size`, OnBytes/Maker/Page/FirstCalls.lean); the
root of a table that `Key.readTable` has read (`OnBytes.Tie.keyTable_root`,
OnBytes/Tie/LeafCall.lean). Here they are called at the record of the reading.

Main names:
  `sizes_of_read`: the binding tree's root and the two seals, from `ThreeRead`.
  `table_root_32`: the table's root, from the equation of `Key.readTable`.
  `rows_key'`, `rows_proof'`: `rows_key` and `rows_proof` without the three sizes that the reading
    gives.
No letter stands under "there is".
Limits: that the table's root has 32 bytes stays a premise of both (z₁). At a key file
`table_root_32` pays it for whoever holds the equation of `Key.readTable`; at a proof file the table
is the caller's. All other premises of `rows_key` and `rows_proof` (OnBytes/Maker/Page/RowsFile.lean
lists them) stay premises here. These oracle functions are no encoding in the sense of the soundness
theorem (the head of OnBytes/Maker/Page/Frame.lean). Nothing on soundness.


-/
import OnBytes.Maker.Page.RowsFile
import OnBytes.TieK.SealSize
import OnBytes.Tie.LeafCall

set_option autoImplicit false

namespace OnBytes.Maker.Page

open Rom TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Joined.K TypedOracleCompiler.Compile.Batch
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ _root_.Compile.Joined
open OnBytes.Maker (FrontMsg frontOf joinOf seamOf)
open OnBytes.Params (Rounds)

/-- **The binding tree's root and the two seals have 32 bytes.** -/
theorem sizes_of_read {p : Proof.TailPublic} {block1 : Blk Proof.FirstEnd} {start1 : Start}
    {file : ByteArray} {i : ℕ} {R₁ : Rounds} {dry : Proof.FirstEnd} {S₁ : Fmt.SpecX}
    {r : Proof.TailRead} {seal1 seal2 : ByteArray} {R₂ : Rounds} {dry2 : Proof.SharedEnd}
    {S₂ : Fmt.SpecX} {R₃ : Rounds} {S₃ : Fmt.SpecX}
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃ S₃) :
    r.place.root.size = 32 ∧ seal1.size = 32 ∧ seal2.size = 32 := by
  have hS₂ : Params.describeWith p.shared.given p.lab₂
      (Params.Shared.statement p.table r.place.root) (.given r.place.root) R₂ 0 = some S₂ :=
    T.shared_spec
  obtain ⟨n2, a2, b2⟩ := head_of hS₂ (fun e => by cases e) _ _ _ _ _ T.shared_read
  unfold RandIs at a2
  rw [describeWith_rand hS₂] at a2
  have a2' : r.place.root = n2 := a2
  exact ⟨a2' ▸ b2.size, TieK.seal_size _ _ _ _ _ _ T.first_read T.first_seal,
    TieK.seal_size _ _ _ _ _ _ T.shared_read T.shared_seal⟩

/-- The root of a table that the program has read out of a key file has 32 bytes. -/
theorem table_root_32 {s : Params.IndexShape} {cfg file : ByteArray} {t : Params.TableName} {j : ℕ}
    (h : Key.readTable s cfg file = .ok (t, j)) : t.root.size = 32 := Tie.keyTable_root h

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

/-- **A key file**, with the sizes that the reading gives paid. -/
theorem rows_key' (k : Params.KeyChains) {j : ℕ}
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
    (z₁ : table.root.size = 32) (rs₁ : List Fmt.Round) (hrs : rs₁.length = Dw.ds₁.length)
    (some₂ : Dw.ds₂ ≠ [])
    (late₁ : xin x = none ∨ ∀ n, n < (toRDs Dw.ds₁).length → L.late ≠ some (0 + 1 + n))
    (late₃ : xin x = none ∨ ∀ n, n < (toRDs Dw.ds₃).length →
      L.late ≠ some (0 + (chainsOf C Dw tF tJ t3).c₁.length +
        (chainsOf C Dw tF tJ t3).c₂.length + 1 + n)) :
    GRows (L := L) (t := t) (C := C) (K := K) (rF := plainRS _ tF) (rJ := plainRS _ tJ)
      (r3 := plainRS _ t3) (aJ := RAnn.ofShared .sh _) (ds₁ := toRDs Dw.ds₁)
      (ds₂ := toRDs Dw.ds₂) (ds₃ := toRDs Dw.ds₃) (D := wholeDesc C Dw tF tJ t3 silent run) embP
      xin (bytesToDig table.root :: rest) x π g Fmt.oracle [] [] S₁ S₂ S₃ r.first.out r.shared.out
      r.second.out rs₁ :=
  rows_key C Dw tF tJ t3 rd Q embP hrd silent run table k T hS₁ hsm S Qa xin rest x π copy pJ p3 hJ
    h3 tabs ext salt path hπ z₁ (sizes_of_read T).1 (sizes_of_read T).2.1 (sizes_of_read T).2.2 rs₁
    hrs some₂ late₁ late₃

/-- **A proof file**, with the sizes that the reading gives paid. -/
theorem rows_proof' (c : Params.ProofChains) (copy : ℕ) (request words : ByteArray)
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
    (z₁ : table.root.size = 32) (rs₁ : List Fmt.Round) (hrs : rs₁.length = Dw.ds₁.length)
    (some₂ : Dw.ds₂ ≠ [])
    (late₁ : xin x = none ∨ ∀ n, n < (toRDs Dw.ds₁).length → L.late ≠ some (0 + 1 + n))
    (late₃ : xin x = none ∨ ∀ n, n < (toRDs Dw.ds₃).length →
      L.late ≠ some (0 + (chainsOf C Dw tF tJ t3).c₁.length +
        (chainsOf C Dw tF tJ t3).c₂.length + 1 + n)) :
    GRows (L := L) (t := t) (C := C) (K := K) (rF := plainRS _ tF) (rJ := plainRS _ tJ)
      (r3 := plainRS _ t3) (aJ := RAnn.ofShared .sh _) (ds₁ := toRDs Dw.ds₁)
      (ds₂ := toRDs Dw.ds₂) (ds₃ := toRDs Dw.ds₃) (D := wholeDesc C Dw tF tJ t3 silent run) embP
      xin (bytesToDig table.root :: rest) x π g Fmt.oracle [] [] S₁ S₂ S₃ r.first.out r.shared.out
      r.second.out rs₁ :=
  rows_proof C Dw tF tJ t3 rd Q embP hrd silent run table c copy request words block req T hS₁ hsm S
      Qa
    xin rest x hreq π pJ p3 hJ h3 tabs ext salt path hπ z₁ (sizes_of_read T).1
    (sizes_of_read T).2.1 (sizes_of_read T).2.2 rs₁ hrs some₂ late₁ late₃

end

end OnBytes.Maker.Page
