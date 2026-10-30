-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupKeyFormsAreTheLibrarysKeysAtTheHeadA1.lean: helper A1 of
LookupKeyFormsAreTheLibrarysKeysAtTheHead.lean: THE VALUES OF THE HEAD's FIVE KEYS. A WORKING FILE.

Part 1, at letters, under Wide and More: the kind's key at an entry and a position ("keyG",
Johnson/Desc/Kinds/Law/General.lean) is the cast of the kind's integer ("midZ", "lowZ", "tvZ", "topNum",
Law/Ints.lean). Part 2: by Law/LibJoin.lean these integers are the specification's; by helper A0 the
library's H.segH is the cast of the specification's key. Nothing is claimed on soundness, completeness or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupKeyFormsAreTheLibrarysKeysAtTheHeadA0

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc.Kinds.Head (Sizes Policy Request Token PlaceKey lenOf Key len V JV JVa
  checked costed win sh)
open VerifiableInference.Desc.Kinds.Norm (d S2 T)
open VerifiableInference.Desc.Kinds.Head.Law (cornerKey rd wideG midG lowG tvG topG keyG midZ
  lowZ tvZ topNum first)
open VerifiableInference.Desc.Kinds.HeadJoin (Same Wide More)
open VerifiableInference.OnPublicFiles
open OnBytes.Road (Hd.TiesH Hd.readH Hd.cellsH Hd.npOf)

/-- The kind's field. -/
local notation "FieldK" => VerifiableInference.Desc.Kinds.Head.Law.K

/-! ## 1 At letters: the kind's keys are casts of the kind's integers -/

section Letters
variable [Sizes] [Policy] [Request] [Token] {Y : Inst.Model.Head.Req} (c : VerifiableInference.Desc.Kinds.Head.Law.Cells)

theorem wideG_plain (k : Key) (f0 nl stride x t : Nat) (hx : x < len k) (hl : S2 ∣ len k)
    (hf : S2 ∣ f0) (hs : S2 ∣ stride) :
    wideG c k f0 nl stride x t = (Finset.range nl).sum fun l =>
      (256 : FieldK) ^ l * ((c.cell .wide (f0 + l * stride + x) t : Int) : FieldK) := by
  unfold wideG
  rw [if_pos (by rw [Nat.div_mul_cancel hl]; exact hx)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Nat.mul_div_cancel' (dvd_add hf (Dvd.dvd.mul_left hs l))]

variable (Wd : Wide) (M : More Y)
include Wd

theorem blocks_JV : S2 ∣ JV := by
  rw [Wd.JV]
  exact Wd.blocks.trans (by norm_num)

theorem blocks_d (n : Nat) : S2 ∣ n * d := by
  rw [Wd.d]
  exact Dvd.dvd.mul_left (Wd.blocks.trans (by norm_num)) n

include M

theorem blocks_JVa : S2 ∣ JVa := by
  rw [M.JVa]
  exact Wd.blocks.trans (by norm_num)

theorem blocks_len (k : Key) : S2 ∣ len k := by
  cases k
  · exact blocks_JV Wd
  · exact blocks_JV Wd
  · exact blocks_JV Wd
  · exact blocks_JVa Wd M
  · show S2 ∣ JV - JVa
    rw [Wd.JV, M.JVa]
    exact Wd.blocks.trans (by norm_num)

theorem blocks_first (k : Key) : S2 ∣ first k := by
  cases k
  · exact dvd_zero _
  · exact dvd_zero _
  · exact dvd_zero _
  · exact dvd_zero _
  · exact blocks_JVa Wd M

theorem midG_cast (k : Key) {x : Nat} (t : Nat) (hx : x < len k) :
    midG c k (first k) x t = ((midZ c (first k + x) t : Int) : FieldK) := by
  unfold midG midZ
  rw [wideG_plain c k _ 2 JV x t hx (blocks_len Wd M k)
    (dvd_add (blocks_d Wd 4) (blocks_first Wd M k)) (blocks_JV Wd),
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    show 4 * d + first k + 0 * JV + x = 4 * d + (first k + x) by ring,
    show 4 * d + first k + 1 * JV + x = 4 * d + JV + (first k + x) by ring]
  push_cast
  ring

theorem lowG_cast (k : Key) (h0 : first k = 0) {x : Nat} (t : Nat) (hx : x < len k) :
    lowG c k x t = ((lowZ c x t : Int) : FieldK) := by
  unfold lowG lowZ
  rw [wideG_plain c k _ 1 JV x t hx (blocks_len Wd M k)
    (dvd_add (blocks_d Wd 4) (Dvd.dvd.mul_left (blocks_JV Wd) 2)) (blocks_JV Wd),
    Finset.sum_range_one, h0, Nat.zero_add,
    show 4 * d + 2 * JV + 0 * JV + x = 4 * d + 2 * JV + x by ring]
  push_cast
  ring

theorem tvG_cast (k : Key) {x : Nat} (t : Nat) (hx : x < len k) :
    tvG c k (first k) x t = ((tvZ c (first k + x) t : Int) : FieldK) := by
  unfold tvG tvZ
  rw [wideG_plain c k _ 3 JV x t hx (blocks_len Wd M k)
    (dvd_add (dvd_add (blocks_d Wd 4) (Dvd.dvd.mul_left (blocks_JV Wd) 3)) (blocks_first Wd M k))
    (blocks_JV Wd)]
  push_cast
  refine congrArg _ (Finset.sum_congr rfl fun l _ => ?_)
  rw [show 4 * d + 3 * JV + first k + l * JV + x = 4 * d + (3 + l) * JV + (first k + x) by ring]

theorem topG_cast {x : Nat} (t : Nat) (hx : x < JV) : topG c x t = ((topNum c x t : Int) : FieldK) := by
  unfold topG topNum
  have e1 := midG_cast c Wd M .marginTop t hx
  have e2 := lowG_cast c Wd M .marginTop rfl t hx
  have e1' : midG c .marginTop 0 x t = ((midZ c x t : Int) : FieldK) := by
    have h : first Key.marginTop + x = x := Nat.zero_add x
    rw [h] at e1
    exact e1
  rw [e1', e2, Int.cast_sub, Int.cast_sub, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_pow]
  norm_num

end Letters

/-! ## 2 The five keys -/

/-- Which family of the specification a key of the head is. -/
def familyOfKey : Key → Inst.Model.Head.Fam
  | .marginTop => .HD0
  | .marginMid => .HD1
  | .marginLow => .HD2
  | .tableA => .HE0
  | .tableB => .HE1

/-- **Each of the head's five keys, at a corner, read, is the library's key of its segment.** -/
theorem headsCornerKeyIsTheLibrarysSegmentKey
    [sizes : Sizes] [policy : Policy] [request : Request]
    {publicFiles : VerifierAndGoals.PublicFiles} {parameters : Inst.Model.ScalesAndPolicy} {layoutFile : Option ByteArray}
    {publicPart : OnBytes.Model.Verify.Public}
    (inScope : VerifierAndGoals.InScope publicFiles = true)
    (filesRead : VerifierAndGoals.readFiles publicFiles = .ok parameters)
    (publicPartMade : OnBytes.Model.Verify.publicOf publicFiles.pol publicFiles.KL layoutFile =
      .ok publicPart)
    (sizesAreThePublicParts : sizes = k3SizesAt publicPart)
    (requestIsOk : VerifiableInference.Desc.Kinds.Head.Request.ok = true)
    (replyToken : Nat) (replyTokenIsInTheVocabulary : replyToken <
      VerifiableInference.Desc.Kinds.Head.V)
    (coveredPositions : OnBytes.Model.Head.Covered) (checkedTokens : Array Nat)
    (coveredPositionsAreTheRequests : ∀ t, t < 1024 →
      coveredPositions.hOn.getD t false = VerifiableInference.Desc.Kinds.Head.checked t)
    (positionsWithCostAreTheRequests : ∀ t, t < 1024 →
      coveredPositions.hOnC.getD t false = VerifiableInference.Desc.Kinds.Head.costed t)
    (checkedTokensAreTheRequests : ∀ t, t + 1 < 1024 →
      VerifiableInference.Desc.Kinds.Head.checked t = true →
      checkedTokens.getD t 0 = VerifiableInference.Desc.Kinds.Head.tok (t + 1))
    (replyTokenIsTheCheckedOne : VerifiableInference.Desc.Kinds.Head.checked 1023 = true →
      checkedTokens.getD 1023 0 = replyToken)
    (matrices : OnBytes.Road.Mats ℤ) (index : Cm.Idx)
    (key : Key) (x t : Nat) (entryIsThere : x < len key) (positionIsThere : t < 1024) :
    letI : Token := ⟨replyToken⟩
    rd (cornerKey (P5J.listCells publicPart.hS publicPart.HLy
        (OnBytes.Model.Verify.borderOf publicPart.y) matrices index.mat) (.inr key) x t) =
      OnBytes.Ends.H.segH (headPub publicPart coveredPositions checkedTokens)
        (OnBytes.Road.Hd.readH matrices index.mat) (OnBytes.Road.Hd.nameOf (familyOfKey key)) x t := by
  obtain ⟨S, Wd, M⟩ := lettersAtTheHead inScope filesRead publicPartMade sizesAreThePublicParts
    replyToken
  have B := OnBytes.Road.Hd.public_of_core publicPartMade
    (OnBytes.Road.Hd.core_of_scope inScope filesRead publicPartMade)
  letI : Token := ⟨replyToken⟩
  have hlen : x < Inst.Model.Head.len (familyOfKey key) := by
    have hJV : JV = 202048 := Wd.JV
    have hJVa : JVa = 131072 := M.JVa
    cases key
    · have h : x < JV := entryIsThere
      rw [hJV] at h
      exact h
    · have h : x < JV := entryIsThere
      rw [hJV] at h
      exact h
    · have h : x < JV := entryIsThere
      rw [hJV] at h
      exact h
    · have h : x < JVa := entryIsThere
      rw [hJVa] at h
      exact h
    · have h : x < JV - JVa := entryIsThere
      rw [hJV, hJVa] at h
      exact h
  have L := librarysSegmentKeyIsACast inScope filesRead publicPartMade sizesAreThePublicParts
    requestIsOk replyToken replyTokenIsInTheVocabulary coveredPositions checkedTokens
    coveredPositionsAreTheRequests positionsWithCostAreTheRequests checkedTokensAreTheRequests
    replyTokenIsTheCheckedOne matrices index.mat (familyOfKey key) x t hlen positionIsThere
  rw [L]
  generalize hC : P5J.listCells publicPart.hS publicPart.HLy
    (OnBytes.Model.Verify.borderOf publicPart.y) matrices index.mat = C
  have hcells : Hd.cellsH publicPart.hS publicPart.HLy (OnBytes.Model.Verify.borderOf publicPart.y)
      matrices = VerifiableInference.Desc.Kinds.HeadJoin.cellsOf C.toCells C.stream := by
    rw [← hC]
    rfl
  have hW : (Inst.Model.Layout.weightsOf Inst.Model.ppref Inst.Model.Layout.kRef index.mat).H =
      C.Wh := by
    rw [← hC]
    rfl
  rw [hcells, hW]
  have hk : rd (cornerKey C (.inr key) x t) = keyG C.toCells key x t :=
    VerifiableInference.Desc.Kinds.Head.Law.rd_keyAt_corner C.toCells requestIsOk
      replyTokenIsInTheVocabulary key entryIsThere (by rw [S.T]; exact positionIsThere)
  rw [hk]
  cases key with
  | marginTop =>
    have hv : x < 202048 := hlen
    have e := topG_cast C.toCells Wd M t entryIsThere
    have hsh : (headPub publicPart coveredPositions checkedTokens).h.digSh = sh := by
      rw [M.sh]
      exact B.sh
    show ((2 : FieldK) ^ (sh + 15))⁻¹ * topG C.toCells x t =
      ((2 : FieldK) ^ ((headPub publicPart coveredPositions checkedTokens).h.digSh + 15))⁻¹ *
        ((Inst.Model.Head.mg _ C.Wh requestRecord x t -
          2 ^ 8 * Inst.Model.Head.K1 _ requestRecord x t -
          Inst.Model.Head.K2 _ requestRecord x t : ℤ) : FieldK)
    rw [VerifiableInference.Desc.Kinds.HeadJoin.top_eq S Wd M hv t, e, hsh]
  | marginMid =>
    have hv : x < 202048 := hlen
    have e := midG_cast C.toCells Wd M .marginMid t entryIsThere
    rw [show first Key.marginMid + x = x from Nat.zero_add x] at e
    show midG C.toCells .marginMid 0 x t =
      1 * ((Inst.Model.Head.K1 _ requestRecord x t : ℤ) : FieldK)
    rw [one_mul, VerifiableInference.Desc.Kinds.HeadJoin.K1_eq S Wd hv t]
    exact e
  | marginLow =>
    have hv : x < 202048 := hlen
    have e := lowG_cast C.toCells Wd M .marginLow rfl t entryIsThere
    show lowG C.toCells .marginLow x t =
      1 * ((Inst.Model.Head.K2 _ requestRecord x t : ℤ) : FieldK)
    rw [one_mul, VerifiableInference.Desc.Kinds.HeadJoin.K2_eq S Wd hv t]
    exact e
  | tableA =>
    have hx0 : x < 131072 := hlen
    have hv : x < 202048 := by omega
    have e1 := midG_cast C.toCells Wd M .tableA t entryIsThere
    have e2 := tvG_cast C.toCells Wd M .tableA t entryIsThere
    rw [show first Key.tableA + x = x from Nat.zero_add x] at e1 e2
    show midG C.toCells .tableA 0 x t + (2 : FieldK) ^ 16 * tvG C.toCells .tableA 0 x t =
      1 * ((Inst.Model.Head.K1 _ requestRecord x t +
        2 ^ 16 * Inst.Model.Head.ex _ x t : ℤ) : FieldK)
    rw [one_mul, VerifiableInference.Desc.Kinds.HeadJoin.K1_eq S Wd hv t,
      VerifiableInference.Desc.Kinds.HeadJoin.ex_eq Wd x t]
    have e1' : midG C.toCells .tableA 0 x t = _ := e1
    have e2' : tvG C.toCells .tableA 0 x t = _ := e2
    rw [e1', e2']
    push_cast
    ring
  | tableB =>
    have hx0 : x < 70976 := hlen
    have hv : 131072 + x < 202048 := by omega
    have e1 := midG_cast C.toCells Wd M .tableB t entryIsThere
    have e2 := tvG_cast C.toCells Wd M .tableB t entryIsThere
    rw [show first Key.tableB + x = 131072 + x by
      show JVa + x = _
      rw [M.JVa]] at e1 e2
    show midG C.toCells .tableB JVa x t + (2 : FieldK) ^ 16 * tvG C.toCells .tableB JVa x t =
      1 * ((Inst.Model.Head.K1 _ requestRecord (131072 + x) t +
        2 ^ 16 * Inst.Model.Head.ex _ (131072 + x) t : ℤ) : FieldK)
    rw [one_mul, VerifiableInference.Desc.Kinds.HeadJoin.K1_eq S Wd hv t,
      VerifiableInference.Desc.Kinds.HeadJoin.ex_eq Wd (131072 + x) t]
    have e1' : midG C.toCells .tableB JVa x t = _ := e1
    have e2' : tvG C.toCells .tableB JVa x t = _ := e2
    rw [e1', e2']
    push_cast
    ring

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.headsCornerKeyIsTheLibrarysSegmentKey
#print axioms ProofFile.Honest.K3.Term.midG_cast
#print axioms ProofFile.Honest.K3.Term.lowG_cast
#print axioms ProofFile.Honest.K3.Term.tvG_cast
#print axioms ProofFile.Honest.K3.Term.topG_cast
