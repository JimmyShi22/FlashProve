-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/KeyPublicAtSeat.lean: at the full size: SIX OF THE FACTS THAT STAND BESIDE THE 21 LAWS ARE PAID, IN SCOPE, AT ANY DIGEST, AND SIX FIELDS OF TWO MORE (AtFk's form · lin · codes; FirstLetters' start · order · fits); and the statement of what is owed with the six HANDED to the payer and the six fields STRUCK.
Main names.
  `head_flat`: AT EVERY CHAIN: the flat list begins with a block (Block.lean: Chain.blocksInOrder): the three heads.
  `one_full`: in scope, at any digest: the source's ranges and its two shapes of the test on the table ARE the written key's (keyFull): BY five_in_scope · shared_lin_in_scope (Johnson/RunOne/Law/KeyInScope.lean): called, not typed again.
  `shape_full`: so the tables' letter S (`shapeAt X`) is the written key's shape.
  `hl_in_scope`: the key has two lookups · `hw_in_scope`: the block that sends W is made (linMessageW at the written shape: one fact of the kernel's) · `hO_in_scope`: the plan has a place for Omega's test (the description's own clause "stages.O" with the written shape's four stages) · `hin_in_scope`: ten blocks between the shared chain's front and its end (the eight of K14, since the fallback block fails its test on the plan; the two tests).
  `front_of_planOk` · `atFk_in_scope`: `AtFk` from its four fields on letters (orc · arr · reads · off): by `atFk_of` · `start_in_scope` (`start_shape`) · `fits_in_scope` (`keyOf_fits`, OnBytes/Slice/KeyOfRec.lean; three numbers by the kernel) · `FirstLeft`: what is left of `FirstLetters`: recAt · arr · reads · coll · dec · held.
  `The21Handed A E X N P DK`: FOR ALL c_j k_j x₀ x₁ bw WITH THE SIX FACTS: THERE ARE the other letters, at one set of which hold: the 21 laws · AtFk's four fields on letters · FirstLeft · two facts on the letters · four on bases; the pieces' rests are `capRest`: their errors ARE the cap, by rfl (`atCap_capRest`).
  `letters_of_handed`: in scope: it gives `The21Letters` (The21AtD.lean).
OBJECT: `Key.descriptionFromSource X N P` as the maker makes it in scope · USER: Johnson/Goal/Conditions/KeyAtTheSeat.lean · LETTERS: A · E.
Limits. PUBLIC FACTS ALONE: NO LAW IS PAID. The full size alone. Nothing on soundness.

-/
import Johnson.RunOne.Law.KeyInScope
import Johnson.Top.Fire.Code.PublicOfFileOkD
import Johnson.RunOne.KeyAtFkMore
import Johnson.Top.Fire.Code.The21AtD

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

/-- **The three heads, at every chain**: the flat list begins with a block. -/
theorem head_flat {S Cl : Type} (c : Chain S Cl) : ∃ b l, c.blocksInOrder = b :: l := ⟨_, _, rfl⟩

theorem w_full : (OnBytes.linMessageW keyFull.once.shape).isSome = true := by decide +kernel

theorem omega_full : keyFull.once.shape.testOmega.isEmpty = false := by decide +kernel

theorem id_full : keyFull.ranges.x.messageId = 1 := by decide +kernel

theorem index_full : keyFull.once.shape.fold.index.v = frS.P.v ∧ keyFull.once.shape.fold.index.answers = 1 ∧ keyFull.once.shape.fold.index.cubeBits = 29 := by decide +kernel

/-- A test that such a comparison can fail. -/
theorem index_full_no : ¬ keyFull.once.shape.fold.index.cubeBits = 28 := by decide +kernel

/-- The shared chain's blocks pass their own tests on the plan. -/
theorem shared_blocksOk (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (hp : (Fk X N P).planOk = true) : blocksOk (Fk X N P).shared.blocksInOrder = true := by
  have h := hp
  simp only [FileDescription.planOk, FileDescription.planOkCore, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.1.1.1.2

/-- **Under the tests on the plan K14's eight blocks are said**: where they are not, the description lays one block whose test on the plan is false. -/
theorem blocks_said (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (hp : (Fk X N P).planOk = true) : ∃ l, _root_.Desc.K14.blocks (p14At X P) = some l := by
  cases hB : _root_.Desc.K14.blocks (p14At X P) with
  | some l => exact ⟨l, rfl⟩
  | none =>
    exfalso
    have e : ∃ bad : Block _root_.Desc.K14.St Unit, inFront₂ X P = bad :: sharedTests P ∧ bad.planOk = false := by
      unfold inFront₂ _root_.Desc.K14.blocksOr
      rw [hB]
      exact ⟨_, rfl, rfl⟩
    obtain ⟨bad, e, hbad⟩ := e
    have hb := shared_blocksOk X N P hp
    rw [shared_flat, e] at hb
    have h2 := List.all_eq_true.1 hb (seat bad) (List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_append_left _ List.mem_cons_self)))
    have h3 : ((bad.planOk && bad.claims.isEmpty) && (Block.retype bad : Block _root_.Desc.K14.St Claim).hasNoClaimsAndNothingAfter) = true := (Bool.and_eq_true_iff.1 h2).1
    rw [hbad] at h3
    cases h3

/-- The shared chain's front's six clauses hold: it is the shared chain's first block's own test on the plan. -/
theorem front_of_planOk (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (hp : (Fk X N P).planOk = true) : sharedFrontOk X.chains = true := by
  have hb := shared_blocksOk X N P hp
  rw [shared_flat] at hb
  have h2 := List.all_eq_true.1 hb (front₂ X) List.mem_cons_self
  have h3 : (front₂ X).planOk = true := (Bool.and_eq_true_iff.1 h2).1
  have h4 : (((sharedFrontOk X.chains && (sharedFront X.chains).claims.isEmpty) && true) && _) = true := h3
  simp only [Bool.and_eq_true] at h4
  exact h4.1.1.1

section
variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
variable {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {X₀ : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol X₀) {cfg : ByteArray}
  {m : Johnson.G.OfPlan.Made} (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
include hZ hP hm hX hp

/-- **In scope, at any digest: the source's ranges and its two shapes are the written key's.** -/
theorem one_full : (oneAt X).ranges = keyFull.ranges.x ∧ (oneAt X).lin = keyFull.once.shape ∧ X.Y.k.shared.lin = keyFull.once.shape :=
  ⟨(five_in_scope hZ hP hm hX hp).2.1, (five_in_scope hZ hP hm hX hp).2.2.1, shared_lin_in_scope hZ hP hm hX hp⟩

/-- **The tables' letter S at the seat**: the sized key's shape, off which our tables of chains 2 and 3 are made, is the written key's. -/
theorem shape_full : Johnson.RunOne.KeyRows23.shapeAt X = keyFull.once.shape :=
  (Johnson.RunOne.KeyRows23.lin_of_fileOk X N P (fileOk_of_planOk' _ hp)).symm.trans (one_full hZ hP hm hX hp).2.1

/-- **hl: the key has two lookups.** -/
theorem hl_in_scope : ∃ x₀ x₁, lookupsOf (oneAt X) = [x₀, x₁] := by
  obtain ⟨e1, e2, _⟩ := one_full hZ hP hm hX hp
  unfold lookupsOf
  rw [e1, e2]
  exact ⟨_, _, rfl⟩

/-- **hw: the block that sends W is made.** -/
theorem hw_in_scope (Np : Pieces) (sent : ℕ) (groups : List (List ℕ)) :
    ∃ bw : Block FirstState Claim, sendW (oneAt X) Np sent groups = some bw := by
  obtain ⟨_, e2, _⟩ := one_full hZ hP hm hX hp
  obtain ⟨msg, hmsg⟩ := Option.isSome_iff_exists.1 w_full
  unfold sendW
  rw [e2, hmsg]
  exact ⟨_, rfl⟩

/-- **The plan has a place for Omega's test**: the description's own clause "stages.O". -/
theorem hO_in_scope : ∃ nO, P.O = some nO := by
  obtain ⟨_, _, e3⟩ := one_full hZ hP hm hX hp
  cases hO : P.O with
  | some nO => exact ⟨nO, rfl⟩
  | none =>
    exfalso
    obtain ⟨r₁, r₂, r₃, ha⟩ := fileOk_all X N P (fileOk_of_planOk' _ hp)
    have hc := List.all_eq_true.1 ha _ (List.mem_append.2 (Or.inr (List.mem_of_getElem? (i := 6) rfl)))
    rw [hO] at hc
    have hc' : X.Y.k.shared.lin.testOmega.isEmpty = true := hc
    rw [e3, omega_full] at hc'
    cases hc'

/-- **hin: ten blocks between the shared chain's front and its end.** -/
theorem hin_in_scope : (inFront₂ X P).length = 10 := by
  obtain ⟨nO, hO⟩ := hO_in_scope hZ hP hm hX hp
  have ht : (sharedTests P).length = 2 := by
    unfold sharedTests
    rw [hO]
    rfl
  obtain ⟨l, hB⟩ := blocks_said X N P hp
  have h8 : l.length = 8 := by
    have := congrArg List.length (names_blocks _ l hB)
    rw [List.length_map] at this
    exact this
  unfold inFront₂ _root_.Desc.K14.blocksOr
  rw [hB, List.length_append, ht]
  show l.length + 2 = 10
  rw [h8]

omit hZ hP hm in
/-- **AtFk from its four fields on letters**: form · lin · codes are paid. -/
theorem atFk_in_scope {Cells M Smp Rec : Type} (B : BaseSt Cells M Smp Rec) (at_ : Where) (R : KRead Cells M) (off₃ : ℕ → ℕ)
    (orc : B.orc₁ = (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)).orc) (arr : ArrOk B.h₂ at_ [0, 2, 3, 4, 5]) (reads : ReadsPinned B.h₂ at_ R [3, 4, 5])
    (off : ∀ k ∈ [0, 2], off₃ (at_ k).1 = (at_ k).1) : AtFk X B at_ R off₃ := by
  obtain ⟨e1, e2⟩ := Johnson.RunOne.KeyRows23.pubsOf_k m X hX
  exact Johnson.RunOne.KeyRows23.atFk_of X N P B at_ R off₃ (by rw [e2, e1]) (front_of_planOk X N P hp) (fileOk_of_planOk' _ hp) orc arr reads off

/-- **FirstLetters.start**: at the first chain's first state the book-keeping's test at border 0 says yes. -/
theorem start_in_scope (x : Xi) : shape₁ (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)) (Johnson.RunOne.KeyRows1.readers₁ (oneAt X)) (Johnson.RunOne.KeyRows1.book₁ (oneAt X))
    (Johnson.RunOne.KeyRows1.n₁ (oneAt X)) (Johnson.RunOne.KeyRows1.slots₁ (oneAt X)) 0 ((Fk X N P).start₁ x) = true := by
  obtain ⟨x₀, x₁, hl⟩ := hl_in_scope hZ hP hm hX hp
  have h2 : (lookupsOf (oneAt X)).length = 2 := by rw [hl]; rfl
  have hid : (oneAt X).ranges.messageId = 1 := by rw [(one_full hZ hP hm hX hp).1]; exact id_full
  have e : Johnson.RunOne.KeyRows1.n₁ (oneAt X) = 2 := h2
  rw [e]
  exact Johnson.RunOne.KeyRows1.start_shape (oneAt X) h2 hid

/-- **FirstLetters.fits**: at every typed record the key written of it fits the table's shape. -/
theorem fits_in_scope (r : RecFull) : (VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample r).key.fits (oneAt X).lin.fold.index = true := by
  rw [(one_full hZ hP hm hX hp).2.1]
  exact OnBytes.Slice.keyOf_fits _ r _ index_full.1 index_full.2.1 index_full.2.2

end

section
variable {Cells M Smp Rec : Type} (Fr : Frame) (G : Reading (Xi × FirstState) Cells M Smp Rec) (at_ : Where)
  (one : OnBytes.Params.OneTime) (R : KRead Cells M) (coll : Strs → Rec → Prop)
  {RecT Y U I : Type} (inst : RecT → Xi) (s₀ : Xi → FirstState) (str : Y → Fr.E.Str) (ρ : RecT → Rec)
  (collT : Y → RecT → Prop) (dcdT : Y → RecT → Option U) (heldT : U → Option I) (cellsOf : U → Cells)

/-- **What is left of `FirstLetters`** (Johnson/RunOne/KeyFirst.lean) when its three public fields (start · order · fits) are paid: six fields, word for word. -/
structure FirstLeft : Prop where
  recAt : ∀ r, G.recOf (inst r, s₀ (inst r)) = some (ρ r)
  arr : ArrOk G at_ [0, 1, 2]
  reads : ReadsPinned G at_ R [0, 1, 2]
  coll : ∀ r y, coll (strsOf Fr (str y)) (ρ r) → collT y r
  dec : ∀ r y c, G.decT (strsOf Fr (str y)).cell (ρ r) = some c → ∃ u, dcdT y r = some u ∧ cellsOf u = c
  held : ∀ r y u, dcdT y r = some u → (∀ l, l < Johnson.RunOne.KeyRows1.n₁ one → ∃ L, (Johnson.RunOne.KeyRows1.plan₁ one).lookups[l]? = some L ∧ InRange R.same (Johnson.RunOne.KeyRows1.plan₁ one).m L (matAt (Johnson.RunOne.KeyRows1.plan₁ one).lin (R.tab (cellsOf u)))) → (heldT u).isSome

end

/-- **The rest of a piece, written**: the extractor hands the witness back; the errors ARE the cap. What a law in the plain form reads of a piece holds neither its extractor nor its errors (`ior_pieceOf`, PieceSame.lean), and a law at smaller errors goes up to the cap (`keeps_same_cap`): so nothing is lost by writing them. -/
def capRest {C : CK} {F : Frame} {S W : Type} (_ : ℕ) (ds : List RDT) : Rest C F S W ds := ⟨fun _ _ w => w, Err.cap 128 (uLT C ds)⟩

theorem atCap_capRest {C : CK} {F : Frame} {S W : Type} : AtCap (capRest (C := C) (F := F) (S := S) (W := W)) := fun _ _ => rfl

/-- **WHAT IS OWED, WITH THE SIX PUBLIC FACTS HANDED TO THE PAYER, WITHOUT SIX FIELDS THAT ARE PAID, AND AT THE WRITTEN RESTS**: the pieces' rests, the witnesses' type and its two values are no letters any more. -/
def The21Handed {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD) : Prop :=
  ∀ (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
    (x₀ x₁ : Lookup) (bw : Block FirstState Claim),
    (Fk X N P).first.blocksInOrder = c₁ :: k₁ → (Fk X N P).shared.blocksInOrder = c₂ :: k₂ → (Fk X N P).second.blocksInOrder = c₃ :: k₃ →
    lookupsOf (oneAt X) = [x₀, x₁] →
    sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw →
    (inFront₂ X P).length = 10 →
    ∃ (Cells M Smp Rec : Type) (_ : Inhabited Cells) (_ : Inhabited M)
      (B : BaseSt Cells M Smp Rec) (at_ : Where) (R : KRead Cells M) (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ)
      (coll : Strs → Rec → Prop) (off₂ off₃ : ℕ → ℕ)
      (ρ : RecFull → Rec) (cellsOf : (lettersAt A (relationsAndEncodingOfClaims A E)).conf.Msg → Cells)
      (_ : ((Fk X N P).XiPub × (Fk X N P).S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str),
      The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () () B at_ R enc rad coll off₂ off₃ ∧
      B.orc₁ = (Johnson.RunOne.KeyRows1.plan₁ (oneAt X)).orc ∧ ArrOk B.h₂ at_ [0, 2, 3, 4, 5] ∧ ReadsPinned B.h₂ at_ R [3, 4, 5] ∧ (∀ k ∈ [0, 2], off₃ (at_ k).1 = (at_ k).1) ∧
      FirstLeft (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R coll VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample (Fk X N P).start₁
        (fun y : (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str => ((y, fun _ => []) : (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str)) ρ
        (fun y r => (lettersAt A (relationsAndEncodingOfClaims A E)).conf.coll y r.1) (fun y r => (lettersAt A (relationsAndEncodingOfClaims A E)).conf.dcd y r) (lettersAt A (relationsAndEncodingOfClaims A E)).conf.held cellsOf ∧
      CellOnly coll ∧
      ReadsL B.h₁ ∧
      (∀ n p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₁)[n]? = some p → ∀ j ∈ pinned (open₁ 2 n), (at_ j).1 < p.base) ∧
      (∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂)[0]? = some p → ∀ j ∈ pinned seam, (at_ j).1 < p.base) ∧
      (∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₂)[11]? = some p → ∀ j ∈ pinned end₂, (at_ j).1 < p.base) ∧
      (∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ capRest capRest capRest () ())).l₃)[1]? = some p → ∀ j ∈ pinned (open₃ 1), (at_ j).1 < p.base)

/-- **In scope the six are paid: what is owed with them handed gives what is owed with them asked.** -/
theorem letters_of_handed {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} (DK : WholeD)
    {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {X₀ : OnBytes.Model.Verify.Public} (hP : ReadOf Zp.pol X₀) {cfg : ByteArray}
    {m : Johnson.G.OfPlan.Made} (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (h : The21Handed A E X N P DK) : The21Letters A E X N P DK := by
  obtain ⟨c₁, k₁, q₁⟩ := head_flat (Fk X N P).first
  obtain ⟨c₂, k₂, q₂⟩ := head_flat (Fk X N P).shared
  obtain ⟨c₃, k₃, q₃⟩ := head_flat (Fk X N P).second
  obtain ⟨x₀, x₁, hl⟩ := hl_in_scope hZ hP hm hX hp
  obtain ⟨bw, hw⟩ := hw_in_scope hZ hP hm hX hp pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
    (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1)))
  have hin := hin_in_scope hZ hP hm hX hp
  obtain ⟨Cells, M, Smp, Rec, iC, iM, B, at_, R, enc, rad, coll, off₂, off₃, ρ, cellsOf, dS,
    H, orc, arr, reads, off, fl, hc, hG, hb₁, hb₂₀, hb₂₁₁, hb₃₁⟩ := h c₁ k₁ c₂ k₂ c₃ k₃ x₀ x₁ bw q₁ q₂ q₃ hl hw hin
  have atFk := atFk_in_scope hX hp B at_ R off₃ orc arr reads off
  have first : FirstLetters (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R coll VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample (Fk X N P).start₁
      (fun y : (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str => ((y, fun _ => []) : (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str)) ρ
      (fun y r => (lettersAt A (relationsAndEncodingOfClaims A E)).conf.coll y r.1) (fun y r => (lettersAt A (relationsAndEncodingOfClaims A E)).conf.dcd y r) (lettersAt A (relationsAndEncodingOfClaims A E)).conf.held cellsOf :=
    ⟨start_in_scope hZ hP hm hX hp, fl.recAt, fl.arr, fl.reads, fun _ => Johnson.RunOne.KeyRows1.start_order _, fits_in_scope hZ hP hm hX hp, fl.coll, fl.dec, fl.held⟩
  exact ⟨Cells, M, Smp, Rec, Unit, iC, iM, c₁, k₁, c₂, k₂, c₃, k₃, capRest, capRest, capRest, (), (), B, at_, R, enc, rad, coll, off₂, off₃, ρ, cellsOf, dS, x₀, x₁, bw,
    H, atFk, first, q₁, q₂, q₃, hl, hw, hin, hc, hG, hb₁, hb₂₀, hb₂₁₁, hb₃₁, atCap_capRest, atCap_capRest, atCap_capRest⟩

end LPFD

#print axioms LPFD.head_flat
#print axioms LPFD.one_full
#print axioms LPFD.shape_full
#print axioms LPFD.hl_in_scope
#print axioms LPFD.hw_in_scope
#print axioms LPFD.hO_in_scope
#print axioms LPFD.hin_in_scope
#print axioms LPFD.front_of_planOk
#print axioms LPFD.atFk_in_scope
#print axioms LPFD.start_in_scope
#print axioms LPFD.fits_in_scope
#print axioms LPFD.FirstLeft
#print axioms LPFD.atCap_capRest
#print axioms LPFD.The21Handed
#print axioms LPFD.letters_of_handed
