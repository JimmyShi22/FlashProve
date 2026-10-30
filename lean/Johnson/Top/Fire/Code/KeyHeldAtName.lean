-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/KeyHeldAtName.lean: at the full size: THE LAST FIELD OF THE KEY FILE's FIRST BORDER, `HeldAtName` (KeyAtName.lean), PAID IN SCOPE AT THE NAME's OWN CLAIMS, AT A WRITTEN `tab`: the base word of each entry of a decoded table.
Main names.
  `baseW x`: the word of the base field's element that x is, where it is one; else 0 · `rdF_baseW`.
  `tabN u r i`: the base word of the entry i of row number r of the table u.
  `TabSays tab u`: the matrix that `tab u` says (`matAt`, at the written key's shape), read in the field, IS the matrix that the name's claims read of u (`cellsOf DN numsRef u`) · `says_of_base`: where every entry of u lies in the base field, `tabN` says u.
  `held_of_says`: in scope, at ANY tab: TabSays tab u and both lookups' sentences ⟹ the configuration holds an index at u.
  `looks_full` | `kCol_full` | `kLo_full`: three facts on the written key [the kernel].
  `held_at_name`: THE THEOREM: in scope: `HeldAtName (claimsReqAt DN numsRef pp) E X tabN`, at every table pp of scales and policy and every coding E: by `dcd_base_full` (Johnson/Desc/K14/Law/BaseValued.lean: a call of `Cb.ldFc_overF` at this decoder) and `inRange_of_ranges` (KeyHeldMeans.lean).
OBJECT: `HeldAtName` · USER: Johnson/Goal/Conditions/KeyAtTheSeat.lean · LETTERS: pp · E.
Limits. AT THE CLAIMS `claimsReqAt DN numsRef pp` ALONE (the name's are these). `tab` is now a written term: each of the 21 laws that reads the stored table's matrix is owed at it. (Where
this and lean/THEOREM.md differ, the page holds.) The full size alone. NO LAW IS PAID. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.KeyAtName
import Johnson.Top.Fire.Code.KeyHeldMeans
import Johnson.Desc.K14.Law.BaseValued
import Johnson.Top.H.TargetAtPolicy
import Johnson.Flat.ThreeFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace LPFD
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.KeyRows23 (BaseSt AtFk Fk fr₁ fr₂ fr₃ On₁ Cl₁ On₂ Cl₂ On₃ Cl₃ oneAt St₂ St₃ seam₁_at_fk seam₂_at_fk ends_at_fk)
open Johnson.RunOne.KeyRows1 (FirstLetters firstOn_of firstClaim_of CollCell ReadsL open₁)
open Johnson.RunOne.KeyRows23 (CellOnly inFront₂ front₂ seat open₃)
open Johnson.RunOne.KeyRows23 (p14At shared_flat names_blocks fileOk_all bareB)
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope shared_lin_in_scope)

open VerifiableInference.Desc.Key.Fill (six OmAt)
open Johnson.RunOne.KeyRows23 (atSix)
open Johnson.Pack (lk0Full lk1Full)
open Inst.Model.Layout (kRef hRef)
open VerifiableInference.OnPublicFiles (numsRef)

open Classical in
/-- The word of the base field's element that x is, where it is one. -/
def baseW (x : GE) : OnBytes.F := if h : ∃ b : GF, x = algebraMap GF GE b then OnBytes.Slice.ofF (Classical.choose h) else 0

theorem rdF_baseW (x : GE) (h : ∃ b : GF, x = algebraMap GF GE b) : rdF (baseW x) = x := by
  unfold baseW rdF
  rw [dif_pos h, readE_ofF, toF_ofF]
  exact (Classical.choose_spec h).symm

/-- **The written `tab`**: the base word of the entry i of row number r. -/
def tabN (u : MsgN) (r i : ℕ) : OnBytes.F := if h : i < DN.T.l then baseW (u (rowAt DN.v r, ⟨i, h⟩)) else 0

/-- **The F-valued table says the decoded table's matrix**: at every row and column of the committed matrix's shape the word that `tab u` lays there (`matAt`, at the written key's shape), read in the field, is the cell that the name's claims read of u. -/
def TabSays (tab : MsgN → ℕ → ℕ → OnBytes.F) (u : MsgN) : Prop :=
  ∀ (y : Fin numsRef.rows) (c : Fin (2 ^ (numsRef.kLo + DN.v))),
    readE (OnBytes.ofF (matAt keyFull.once.shape (tab u) y.val c.val)) = cellsOf DN numsRef u y c

theorem kLo_full : keyFull.once.shape.kLo = 7 := by decide +kernel

/-- **Where every entry of u lies in the base field, `tabN` says u.** -/
theorem says_of_base (u : MsgN) (hu : ∀ n, ∃ b : GF, u n = algebraMap GF GE b) : TabSays tabN u := by
  intro y c
  have hy : y.val < 3076096 := y.isLt
  have hc : c.val % 2 ^ 7 < 2 ^ 7 := Nat.mod_lt _ (by decide)
  have hi : c.val % 2 ^ 7 + 2 ^ 7 * y.val < 402653181 := by omega
  have hl : c.val % 2 ^ 7 + 2 ^ 7 * y.val < DN.T.l := by
    show _ < 402653184
    omega
  show rdF (matAt keyFull.once.shape (tabN u) y.val c.val) = _
  unfold matAt tabN cellsOf
  rw [kLo_full]
  rw [dif_pos (show c.val % 2 ^ numsRef.kLo + 2 ^ numsRef.kLo * y.val < DN.T.l ∧ c.val % 2 ^ numsRef.kLo + 2 ^ numsRef.kLo * y.val < DN.cut from ⟨hl, hi⟩),
    dif_pos hl, rdF_baseW _ (hu _)]
  rfl

set_option maxRecDepth 1000000 in
theorem looks_full : keyFull.ranges.x.lookups = [lk0Full, lk1Full] := by decide +kernel

theorem kCol_full : (OnBytes.Wf.matrixOf keyFull.once.shape).kCol = kRef := by decide +kernel

section
variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
variable {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {X₀ : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol X₀) {cfg : ByteArray}
  {m : Johnson.G.OfPlan.Made} (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
include hZ hP hm hX hp

/-- **«THE KEY FILE's LOOKUPS ENFORCE InRange», AT THE NAME's CONFIGURATION**: in scope: where tab says u and both lookups' sentences hold of the matrix that `tab u` says, the configuration holds an index at u. -/
theorem held_of_says (pp : Inst.Model.ScalesAndPolicy) (E : Coding (claimsReqAt DN numsRef pp)) (tab : MsgN → ℕ → ℕ → OnBytes.F) (u : MsgN) (hT : TabSays tab u)
    (hl : ∀ l, l < Johnson.RunOne.KeyRows1.n₁ (oneAt X) → ∃ L, (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)).lookups[l]? = some L ∧
      InRange (readAt tab).same (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)).m L (matAt (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)).lin (tab u))) :
    ((lettersAt (claimsReqAt DN numsRef pp) (relationsAndEncodingOfClaims (claimsReqAt DN numsRef pp) E)).conf.held u).isSome := by
  classical
  obtain ⟨e1, e2, -⟩ := one_full hZ hP hm hX hp
  obtain ⟨x₀, x₁, h2⟩ := hl_in_scope hZ hP hm hX hp
  have hn : Johnson.RunOne.KeyRows1.n₁ (oneAt X) = 2 := by
    unfold Johnson.RunOne.KeyRows1.n₁
    rw [h2]
    rfl
  have hlk : (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)).lookups = [lk0Full, lk1Full] := by
    show (oneAt X).ranges.lookups = _
    rw [e1]
    exact looks_full
  have hlin : (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)).lin = keyFull.once.shape := e2
  have hk : (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)).m.kCol = kRef := by
    show (OnBytes.Wf.matrixOf (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)).lin).kCol = kRef
    rw [hlin]
    exact kCol_full
  obtain ⟨L0, hL0, r0⟩ := hl 0 (by omega)
  obtain ⟨L1, hL1, r1⟩ := hl 1 (by omega)
  rw [hlk] at hL0 hL1
  obtain rfl : lk0Full = L0 := Option.some.inj hL0
  obtain rfl : lk1Full = L1 := Option.some.inj hL1
  rw [hlin] at r0 r1
  have hin : VerifiableInference.OnPublicFiles.Flat.InRange (cellsOf DN numsRef u) :=
    inRange_of_ranges (readAt tab).same (fun _ _ h => h) _ hk _ (cellsOf DN numsRef u) (fun y c => (hT y c).symm) r0 r1
  show (if VerifiableInference.OnPublicFiles.Flat.InRange (cellsOf DN numsRef u) then some (cellsOf DN numsRef u) else none).isSome = true
  rw [if_pos hin]
  rfl

/-- **THE LAST FIELD OF THE FIRST BORDER, PAID IN SCOPE AT THE NAME's CLAIMS.** -/
theorem held_at_name (pp : Inst.Model.ScalesAndPolicy) (E : Coding (claimsReqAt DN numsRef pp)) : HeldAtName (claimsReqAt DN numsRef pp) E X tabN :=
  fun r y u hu hl => held_of_says hZ hP hm hX hp pp E tabN u (says_of_base u (_root_.Desc.K14.Law.dcd_base_full frZ 402653181 y r u hu)) hl

end

end LPFD

#print axioms LPFD.rdF_baseW
#print axioms LPFD.says_of_base
#print axioms LPFD.looks_full
#print axioms LPFD.held_of_says
#print axioms LPFD.held_at_name
