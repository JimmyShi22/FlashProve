-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/KeyAtGathered.lean: THE KEY FILE'S RULE, HAD AT GATHERED BLOCKS, SERVES THE
DESCRIPTION'S OWN DECISION: so one proved typed block may stand against several blocks of the fold.

The setting. `keyCoreAtDesc` (Johnson/Desc/Sound/KeyAtDesc.lean) asks a seat, with a proved typed
block, for EACH block of the description's three flat lists. A typed block of the library may span
several of them. By Johnson/Desc/Sound/Gather.lean the fold's yes gives the gathered fold's yes
with the same record; by `keyCoreAnti` the hypothesis goes over to a decision that says yes less
often.

What is said. `OfGathered F g₁ g₂ g₃ T`: the pieces of T hold the blocks of three lists g₁, g₂, g₃
(each with the test below the prime, lifted), at the numbers that `FileDescription.runEnd` hands its three
folds: as `OfDesc` (Johnson/Desc/Sound/DescThree.lean), with the three lists free.
`runGivesRowGathered`: where these lists are the description's own flat lists with neighbours laid
together (`Gathers`), the decision's yes gives the yes of the three runs of `atDesc F T`.
`KeyCoreAtGathered`, `keyCoreAtGathered`: so, under the premises of `KeyCoreOfDecides` at seats for
the GATHERED blocks: `KeyCore` AT THE DECISION `F.run`.

Limits. A rule. A gathered block's one law is then a law on `Block.andThen`'s `decide`: the first
block's, then the second's at what the first returns: how it is had from laws on the parts is not
said here. Those of KeyAtDesc.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.KeyAtDesc
import Johnson.Desc.Sound.Gather

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run (ckP)
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)

variable {C : CK} {D : WholeD} {all : List LeftT} {Xi X₁ X₂ W : Type}

/-- **The pieces hold the blocks of three lists**, at the description's records and numbers. -/
structure OfGathered (F : FileDescription Xi) (g₁ : List (Block F.S₁ F.Cl)) (g₂ : List (Block F.S₂ F.Cl))
    (g₃ : List (Block F.S₃ F.Cl)) (T : ThreeAt C D all F X₁ X₂ W) : Prop where
  ft₁ : T.ft₁ = 0
  ft₂ : T.ft₂ = 0
  ft₃ : T.ft₃ = F.lastChainFirstTreeNumber
  b₁ : (T.p₁ :: T.l₁).map (·.b) = (g₁.map below).map (Block.lift Prod.snd fun t s => (t.1, s))
  b₂ : (T.p₂ :: T.l₂).map (·.b) = (g₂.map below).map (Block.lift Prod.snd fun t s => (t.1, s))
  b₃ : (T.p₃ :: T.l₃).map (·.b) = (g₃.map below).map (Block.lift Prod.snd fun t s => (t.1, s))
  back₁ : rowBack T.p₁ T.l₁ = [sealRound]
  back₂ : rowBack T.p₂ T.l₂ = []
  back₃ : rowBack T.p₃ T.l₃ = []

/-- Three runs in a row say yes wherever three runs that return less often do. -/
theorem runRow_mono {Y A B : Type} (r₁ r₁' : Y → Fmt.View → Option A)
    (r₂ r₂' : A → Fmt.View → Option B) (r₃ r₃' : B → Fmt.View → Bool)
    (h₁ : ∀ x v a, r₁ x v = some a → r₁' x v = some a)
    (h₂ : ∀ x v a, r₂ x v = some a → r₂' x v = some a)
    (h₃ : ∀ x v, r₃ x v = true → r₃' x v = true) (x : Y) (v₁ v₂ v₃ : Fmt.View)
    (h : runRow r₁ r₂ r₃ x v₁ v₂ v₃ = true) : runRow r₁' r₂' r₃' x v₁ v₂ v₃ = true := by
  unfold runRow at h ⊢
  cases e₁ : r₁ x v₁ with
  | none =>
    rw [e₁] at h
    cases h
  | some a =>
    rw [e₁] at h
    rw [h₁ x v₁ a e₁]
    dsimp only at h ⊢
    cases e₂ : r₂ a v₂ with
    | none =>
      rw [e₂] at h
      cases h
    | some b =>
      rw [e₂] at h
      rw [h₂ a v₂ b e₂]
      exact h₃ b v₃ h

/-- **The decision's yes gives the yes of the three runs at the gathered blocks.** -/
theorem runGivesRowGathered (F : FileDescription Xi) (g₁ : List (Block F.S₁ F.Cl))
    (g₂ : List (Block F.S₂ F.Cl)) (g₃ : List (Block F.S₃ F.Cl)) (T : ThreeAt C D all F X₁ X₂ W)
    (hO : OfGathered F g₁ g₂ g₃ T) (G₁ : Gathers F.first.blocksInOrder g₁) (G₂ : Gathers F.shared.blocksInOrder g₂)
    (G₃ : Gathers F.second.blocksInOrder g₃) (x : Xi) (v₁ v₂ v₃ : Fmt.View)
    (h : F.run x v₁ v₂ v₃ = true) :
    runRow (atDesc F T).run₁ (atDesc F T).run₂ (atDesc F T).run₃ x v₁ v₂ v₃ = true := by
  have e₁ := runOfStarts₁ C D all Xi F.S₁ F.S₂ F.S₃ X₁ X₂ F.Cl W F.XiPub F.pub F.start₁ F.start₂
    (fun p a b => (F.start₃ p a b).toOption) T g₁ [sealRound] hO.b₁ hO.back₁ rfl
  have e₂ := runOfStarts C D all Xi F.S₁ F.S₂ F.S₃ X₁ X₂ F.Cl W F.XiPub F.pub F.start₁ F.start₂
    (fun p a b => (F.start₃ p a b).toOption) T g₂ hO.b₂ hO.back₂
  have e₃ := runOfStarts₃ C D all Xi F.S₁ F.S₂ F.S₃ X₁ X₂ F.Cl W F.XiPub F.pub F.start₁ F.start₂
    (fun p a b => (F.start₃ p a b).toOption) T g₃ hO.b₃ hO.back₃
  have e₁' : (atDesc F T).run₁ = _ := e₁
  have e₂' : (atDesc F T).run₂ = _ := e₂
  have e₃' : (atDesc F T).run₃ = _ := e₃
  rw [e₁', e₂', e₃']
  refine runRow_mono (descRun₁ F) _ (descRun₂ F) _ (descRun₃ F) _ ?_ ?_ ?_ x v₁ v₂ v₃
    (runGivesRow Xi F x v₁ v₂ v₃ h)
  · intro x v a ha
    unfold descRun₁ at ha
    by_cases hw : viewWordsBelowPrime v = true
    · rw [if_pos hw] at ha
      obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 ha
      show (if viewWordsBelowPrime v then _ else none) = _
      rw [if_pos hw, foldRun_at _ _ "the first chain" 0 hO.ft₁]
      have := gathers_chainAt "the first chain" "the first chain" 0 G₁ _ s (withEmptySealRound v) hs
      have this' : (chainAt "the first chain" 0 g₁ (F.start₁ (F.pub x))
        ⟨v.rounds ++ [sealRound], v.opened⟩).toOption = some s := this
      rw [this']
      rfl
    · rw [if_neg hw] at ha
      cases ha
  · intro a v b hb
    unfold descRun₂ at hb
    by_cases hw : viewWordsBelowPrime v = true
    · rw [if_pos hw] at hb
      obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 hb
      show (if viewWordsBelowPrime v then _ else none) = _
      rw [if_pos hw, foldRun_at _ _ "the shared chain" 0 hO.ft₂, view_nil,
        gathers_chainAt "the shared chain" "the shared chain" 0 G₂ _ s v hs]
      rfl
    · rw [if_neg hw] at hb
      cases hb
  · intro a v hb
    unfold descRun₃ at hb
    obtain ⟨hw, hs⟩ := Bool.and_eq_true_iff.1 hb
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 hs
    obtain ⟨s, h1, h2⟩ := Option.bind_eq_some_iff.1 he
    show (viewWordsBelowPrime v && ((F.start₃ a.1 a.2.1 a.2.2).toOption.bind fun s =>
                  foldRun (frameAt D all D.key₃ T.ft₃) T.n₃ g₃ [] s v).isSome) = true
    rw [hw, h1]
    show (foldRun (frameAt D all D.key₃ T.ft₃) T.n₃ g₃ [] s v).isSome = true
    rw [foldRun_at _ _ "the second chain" F.lastChainFirstTreeNumber hO.ft₃, view_nil,
      gathers_chainAt "the second chain" "the second chain" F.lastChainFirstTreeNumber G₃ _ e v h2]
    rfl

/-- **`KeyCore` at a description's own decision, from one law for each GATHERED block.** -/
def KeyCoreAtGathered : Prop :=
  ∀ (a : ℕ) (Kc : ConfLetters a) (DK : WholeD) (TFk TJk T3k : Type) (tFk : TFk)
    (tJk : TJk) (t3k : T3k) (silK : Kc.conf.Rec → TFk → TJk → T3k → Bool)
    (all : List LeftT) (X₁ X₂ W : Type) (F : FileDescription Kc.conf.Rec)
    (g₁ : List (Block F.S₁ F.Cl)) (g₂ : List (Block F.S₂ F.Cl)) (g₃ : List (Block F.S₃ F.Cl))
    (T : ThreeAt (ckP .two) (DK.at a) all F X₁ X₂ W) (J₁ J₂ Z : JK)
    (L₁ : SL (F.XiPub × F.S₁) F.Cl (frameAt (DK.at a) all (DK.at a).key₁ T.ft₁) (jWf Kc.conf) J₁)
    (L₂ : SL ((F.XiPub × F.S₁) × F.S₂) F.Cl (frameAt (DK.at a) all (DK.at a).key₂ T.ft₂) J₁ J₂)
    (L₃ : SL ((F.XiPub × F.S₁ × F.S₂) × F.S₃) F.Cl
      (frameAt (DK.at a) all (DK.at a).key₃ T.ft₃) J₂ Z) (εs : ℝ≥0∞),
    Gathers F.first.blocksInOrder g₁ → Gathers F.shared.blocksInOrder g₂ → Gathers F.second.blocksInOrder g₃ →
    OfGathered F g₁ g₂ g₃ T →
    T.p₁ :: T.l₁ = L₁.pieces W → T.p₂ :: T.l₂ = L₂.pieces W → T.p₃ :: T.l₃ = L₃.pieces W →
    (atDesc F T).Fits → L₁.Laws → L₂.Laws → L₃.Laws →
    (∀ rec y, L₁.rd0 ((F.pub rec, F.start₁ (F.pub rec)), (y, fun _ => [])) = (rec, y) ∧
      L₁.inv0 ((F.pub rec, F.start₁ (F.pub rec)), (y, fun _ => []))) →
    (∀ b, L₂.rd0 ((b.1, F.start₂ b.1.1), b.2) = L₁.rdZ b ∧
      (L₁.invZ b → L₂.inv0 ((b.1, F.start₂ b.1.1), b.2))) →
    (∀ b s, F.start₃ b.1.1.1 b.1.1.2 b.1.2 = .ok s →
      L₃.rd0 (((b.1.1.1, b.1.1.2, b.1.2), s), b.2) = L₂.rdZ b ∧
      (L₂.invZ b → L₃.inv0 (((b.1.1.1, b.1.1.2, b.1.2), s), b.2))) →
    (∀ b, Z.on (L₃.rdZ b) → L₃.invZ b → ∃ w, Z.relR (L₃.rdZ b) w) →
    RowFit (DK.at a) all all →
    L₁.Held εs → L₂.Held εs → L₃.Held εs →
    KeyCore Kc DK tFk tJk t3k silK F.run 1 εs

theorem keyCoreAtGathered : KeyCoreAtGathered := by
  intro a Kc DK TFk TJk T3k tFk tJk t3k silK all X₁ X₂ W F g₁ g₂ g₃ T J₁ J₂ Z L₁ L₂ L₃ εs G₁ G₂ G₃
    hO e₁ e₂ e₃ hf w₁ w₂ w₃ hfirst hs₁ hs₂ hlast hfit d₁ d₂ d₃
  refine keyCoreAnti a Kc DK TFk TJk T3k tFk tJk t3k silK silK
    (runRow (atDesc F T).run₁ (atDesc F T).run₂ (atDesc F T).run₃) F.run 1 εs
    (fun _ _ _ _ h => h) (runGivesRowGathered F g₁ g₂ g₃ T hO G₁ G₂ G₃) ?_
  exact keyCoreOfDecides a Kc DK TFk TJk T3k tFk tJk t3k silK all _ _ _ _ _ F.Cl W (atDesc F T)
    J₁ J₂ Z L₁ L₂ L₃ εs e₁ e₂ e₃ hf w₁ w₂ w₃ hfirst (fun _ b => hs₁ b)
    (fun _ b s h => by
      obtain ⟨s₃, h1, h2⟩ := Option.map_eq_some_iff.1 h
      have h3 : F.start₃ b.1.1.1 b.1.1.2 b.1.2 = .ok s₃ := by
        cases hh : F.start₃ b.1.1.1 b.1.1.2 b.1.2 with
        | error e =>
          have h1' : (F.start₃ b.1.1.1 b.1.1.2 b.1.2).toOption = some s₃ := h1
          rw [hh] at h1'
          cases h1'
        | ok t =>
          have h1' : (F.start₃ b.1.1.1 b.1.1.2 b.1.2).toOption = some s₃ := h1
          rw [hh] at h1'
          exact congrArg Except.ok (Option.some.inj h1')
      rw [← h2]
      exact hs₂ b s₃ h3)
    (fun _ b _ => hlast b) hfit d₁ d₂ d₃

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.runGivesRowGathered
#print axioms VerifiableInference.Desc.Sound.keyCoreAtGathered
