-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/KeyASideAll.lean: THE KEY FILE, CHAIN 1, IN SCOPE: THE STATE's SIDE OF THE TABLES' PROMISE AT EVERY BORDER, FROM THE HISTORY: NO GAP LEFT. aSide_of_hist's seven named steps (Gaps) are filled: five by gaps_of (RunOne/Law/StepSideGaps.lean), two by astep16_scope | astep17_scope (Top/Fire/Code/RowAStepsScope.lean); every public premise is paid by a call in scope.
OBJECT: ASide (oneAt X) atSix k a.2 at Hist₁ (Fk X N P) D k a, k ≤ 19 · USER: row 3.2's guard (Johnson/RunOne/Law/BookAt32.lean) · the shared chain's start (KeyASide2Start.lean) · LETTERS: none but the scope's (Zp X₀ cfg m X N P D).
  gaps_in_scope     PROVED: Gaps X N P atSix (H₀ X) (H₁ X)
  aSide_at_all    PROVED: q₁ · the five in scope · hft ⟹ ∀ k ≤ 19, Hist₁ (Fk X N P) D k a → ASide (oneAt X) atSix k a.2
  E18 · e18_at_end  PROVED: at the borders 18 | 19 also: the row (Eval) is the claim's · the last group's open rows lie on their own tables · W's test's first mask lies in W's tree, the next part (free₁'s three conjuncts from 18 on): by astep17E_scope and the last block's «the same state»
  bookAtEnd_scope   PROVED: KeyGuard32.lean's BookAtEnd
  guard_32_scope  PROVED: guard_32 with no premise on a verifier's state
  aSide_at_made | e18_at_made | guard_32_made   PROVED: the same three at the maker's own numbers: hft gone
hft : N.nums.firstTree = 0: A PREMISE THAT NO TEST OF Key.descriptionFromSource ASKS: PAID WHERE N IS THE MAKER's: firstTree_of_rangesNumbers (Desc/Key/RangesFirstTree.lean): the forms aSide_at_made | e18_at_made | guard_32_made take «rangesNumbers m = .ok N» in its place (at the seat that equation is one of the facts in OpenLawAtZ's hypotheses, Johnson/Goal/Conditions/KeySoundOfOpenAt.lean).
IMPLICATIONS: EMPTY WHERE NOTHING IS REACHED. Nothing on soundness.
-/
import Johnson.Top.Fire.Code.KeyGuard32
import Johnson.Top.Fire.Code.RowAStepsE
import Johnson.Top.Fire.Code.KeyMemberAtSeat
import Johnson.Top.Fire.Code.Row11Eight
import Johnson.RunOne.Law.StepSideGaps
import Johnson.Desc.Key.RangesFirstTree

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

open OnBytes.Params (OneTime Setting)
open Johnson.RunOne.KeyRows1
open Johnson.RunOne.KeyRows23 (CellOnly)

open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open Johnson.RunOne.Law.KeyInScope (five_in_scope)
open Johnson.RunOne.KeyRows23 (atSix)

open Johnson.RunOne.Law.StepSideGaps (gaps_of)
open Johnson.RunOne.Law.StepSideAtFk (H₀ H₁)

/-- What free₁ asks of the verifier's state from border 18 on, beside ASide. -/
def E18 (one : OneTime) (s : FirstState) : Prop :=
  Johnson.RunOne.KeyRows23.EvalIs one.lin s ∧ Johnson.RunOne.KeyRows23.OpenIn s.d.st (s.d.st.groups.size - 1) ∧
    ∀ o, (plan₁ one).orc 2 = some o → MaskWith (fun i => s.d.book.place[i]?) o (o + 1)

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
variable {Zp : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {cfg : ByteArray} {m : Johnson.G.OfPlan.Made}

theorem gaps_in_scope (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hft : N.nums.firstTree = 0) : Gaps X N P atSix (H₀ X) (H₁ X) := by
  obtain ⟨x₀, x₁, hl⟩ := hl_in_scope hZ hP hm hX hp
  exact gaps_of X N P atSix hp (by rw [show lookupsOf X.Y.k.oneTime = [x₀, x₁] from hl]; rfl) hft
    (fun b hb => astep16_scope X N P c₁ k₁ q₁ hZ hP hm hX hp b (q₁ ▸ hb))
    (fun b hb => astep17_scope X N P c₁ k₁ q₁ hZ hP hm hX hp b (q₁ ▸ hb))

variable (D : WholeD)

/-- **Every border of the first chain.** -/
theorem aSide_at_all (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hft : N.nums.firstTree = 0) (k : ℕ) (a : Xi × FirstState) (hk : k ≤ 19) (hist : Hist₁ (Fk X N P) D k a) : ASide (oneAt X) atSix k a.2 := by
  obtain ⟨x₀, x₁, hl⟩ := hl_in_scope hZ hP hm hX hp
  obtain ⟨bw, hw⟩ := hw_in_scope hZ hP hm hX hp pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
    (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1)))
  have h5s := five_in_scope hZ hP hm hX hp
  obtain ⟨pub1⟩ := public11_full (oneAt X) pieces (g11 X) h5s.2.1 h5s.2.2.2.2 (plan11_of hp)
  have hid : (oneAt X).ranges.messageId = 1 := by rw [h5s.2.1]; exact id_full
  have hst : 1 ≤ (oneAt X).ranges.stages.length := by
    rw [h5s.2.1, Johnson.RunOne.KeyLetters.stages_full]
    decide
  exact aSide_of_hist X N P atSix D x₀ x₁ (H₀ X) (H₁ X) hl hid (public10_in_scope hZ hP hm hX hp c₁ k₁ q₁) pub1 hst rfl rfl bw hw
    (gaps_in_scope X N P c₁ k₁ q₁ hZ hP hm hX hp hft) k a hk hist

/-- **At the borders 18 and 19: free₁'s three more.** -/
theorem e18_at_end (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hft : N.nums.firstTree = 0) : (∀ a : Xi × FirstState, Hist₁ (Fk X N P) D 18 a → E18 (oneAt X) a.2) ∧ ∀ a : Xi × FirstState, Hist₁ (Fk X N P) D 19 a → E18 (oneAt X) a.2 := by
  have h18 : ∀ a : Xi × FirstState, Hist₁ (Fk X N P) D 18 a → E18 (oneAt X) a.2 := by
    intro a h
    obtain ⟨a', b, rs, cols, hr, hb, hd, hf⟩ := Reached.last h
    rw [List.getElem?_map] at hb
    obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
    exact (astep17E_scope X N P c₁ k₁ q₁ hZ hP hm hX hp b₀ (q₁ ▸ hb₀) a'.2 a.2 rs _ hf (held_decide b₀ a' _ _ a hd).2
      (aSide_at_all X N P c₁ k₁ D q₁ hZ hP hm hX hp hft 17 a' (by decide) hr)).2
  refine ⟨h18, fun a h => ?_⟩
  obtain ⟨x₀, x₁, hl⟩ := hl_in_scope hZ hP hm hX hp
  obtain ⟨bw, hw⟩ := hw_in_scope hZ hP hm hX hp pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
    (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1)))
  obtain ⟨a', b, rs, cols, hr, hb, hd, hf⟩ := Reached.last h
  rw [List.getElem?_map] at hb
  obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
  have hy := (held_decide b₀ a' _ _ a hd).2
  obtain ⟨asks, ha⟩ := dec_seal (oneAt X) X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl bw hw b₀ hb₀
  rw [ha] at hy
  have e : a'.2 = a.2 := by
    cases hq : ChainEnd.refuse (asks a'.2) with
    | error e => rw [hq] at hy; cases hy
    | ok u => rw [hq] at hy; exact Except.ok.inj hy
  rw [← e]
  exact h18 a' hr

theorem bookAtEnd_scope (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hft : N.nums.firstTree = 0) : BookAtEnd X N P D := by
  obtain ⟨x₀, x₁, hl⟩ := hl_in_scope hZ hP hm hX hp
  obtain ⟨bw, hw⟩ := hw_in_scope hZ hP hm hX hp pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
    (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1)))
  exact bookAtEnd_of_aSide X N P D atSix (flat_length (oneAt X) X.Y.D.1 X.Y.told.1 X.set N x₀ x₁ hl bw hw)
    (fun a ha => aSide_at_all X N P c₁ k₁ D q₁ hZ hP hm hX hp hft 19 a (by decide) ha)

/-- **Row 3.2's guard, in scope: no premise on a verifier's state.** -/
theorem guard_32_scope (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hft : N.nums.firstTree = 0) (a : (Xi × FirstState × St₂) × St₃) (h : Hist₃ (Fk X N P) D 2 a) (t : VerifiableInference.Desc.K12.T12)
    (ht : VerifiableInference.Desc.K12.Seat.enterOwn a.2 = .ok t) :
    ∃ (q : Nat × Nat) (tO : OnBytes.Tree), a.1.2.2.book.place[a.1.2.2.loc.oOmega]? = some q ∧ a.1.2.2.book.trees[q.1]? = some tO ∧
      H2K.First.BookOrdW a.1.2.1.d.roots tO.number t.book ∧ t.book.trees.size = a.1.2.1.d.roots + 1 ∧ t.roots = 0 :=
  guard_32 X N P D (bookAtEnd_scope X N P c₁ k₁ D q₁ hZ hP hm hX hp hft) a h t ht

/-! ## At the maker's own numbers -/

theorem aSide_at_made (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hN : rangesNumbers m = .ok N) (k : ℕ) (a : Xi × FirstState) (hk : k ≤ 19) (hist : Hist₁ (Fk X N P) D k a) : ASide (oneAt X) atSix k a.2 :=
  aSide_at_all X N P c₁ k₁ D q₁ hZ hP hm hX hp (firstTree_of_rangesNumbers hN) k a hk hist

theorem e18_at_made (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hN : rangesNumbers m = .ok N) : (∀ a : Xi × FirstState, Hist₁ (Fk X N P) D 18 a → E18 (oneAt X) a.2) ∧ ∀ a : Xi × FirstState, Hist₁ (Fk X N P) D 19 a → E18 (oneAt X) a.2 :=
  e18_at_end X N P c₁ k₁ D q₁ hZ hP hm hX hp (firstTree_of_rangesNumbers hN)

theorem guard_32_made (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁)
    (hZ : VerifierAndGoals.InScope Zp = true) (hP : ReadOf Zp.pol X₀) (hm : madeAt X₀ Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X) (hp : (Fk X N P).planOk = true)
    (hN : rangesNumbers m = .ok N) (a : (Xi × FirstState × St₂) × St₃) (h : Hist₃ (Fk X N P) D 2 a) (t : VerifiableInference.Desc.K12.T12)
    (ht : VerifiableInference.Desc.K12.Seat.enterOwn a.2 = .ok t) :
    ∃ (q : Nat × Nat) (tO : OnBytes.Tree), a.1.2.2.book.place[a.1.2.2.loc.oOmega]? = some q ∧ a.1.2.2.book.trees[q.1]? = some tO ∧
      H2K.First.BookOrdW a.1.2.1.d.roots tO.number t.book ∧ t.book.trees.size = a.1.2.1.d.roots + 1 ∧ t.roots = 0 :=
  guard_32_scope X N P c₁ k₁ D q₁ hZ hP hm hX hp (firstTree_of_rangesNumbers hN) a h t ht

end

end LPFD

#print axioms LPFD.gaps_in_scope
#print axioms LPFD.aSide_at_all
#print axioms LPFD.e18_at_end
#print axioms LPFD.bookAtEnd_scope
#print axioms LPFD.guard_32_scope
#print axioms LPFD.aSide_at_made
#print axioms LPFD.e18_at_made
#print axioms LPFD.guard_32_made
