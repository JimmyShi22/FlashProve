-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/DescThreeProofs.lean: the proofs of the statements of
Johnson/Desc/Sound/DescThree.lean.

Limits: those of Johnson/Desc/Sound/DescThree.lean.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.DescThree
import Johnson.Desc.Sound.DescRunsProofs
import Johnson.Desc.Sound.FileBatchProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open TypedOracleCompiler.Joined (LinkJ Links)
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString)
open _root_.Compile.Joined (plainRound)

/-- The chain's decision is blind to the chain's name, and reads of the frame the number ft alone.
-/
theorem foldRun_at {S Cl : Type} (Fr : Frame) (n n' : String) (ft : ℕ) (hft : Fr.ft = ft)
    (bs : List (Block S Cl)) (back : List Fmt.RoundView) (s : S) (v : Fmt.View) :
    foldRun Fr n bs back s v = (chainAt n' ft bs s ⟨v.rounds ++ back, v.opened⟩).toOption := by
  unfold foldRun
  rw [hft, chainAt_toOption, chainAt_toOption]

theorem view_nil (v : Fmt.View) : (⟨v.rounds ++ [], v.opened⟩ : Fmt.View) = v := by
  rw [List.append_nil]

theorem runsAtDesc : RunsAtDesc := by
  intro C D all Xi X₁ X₂ W F T h
  refine ⟨?_, ?_, ?_⟩
  · refine (runOfStarts₁ C D all Xi F.S₁ F.S₂ F.S₃ X₁ X₂ F.Cl W F.XiPub F.pub F.start₁ F.start₂
      (fun p a b => (F.start₃ p a b).toOption) T F.first.blocksInOrder [sealRound] h.b₁ h.back₁ rfl).trans ?_
    funext x v
    rw [foldRun_at _ _ "the first chain" 0 h.ft₁]
    rfl
  · refine (runOfStarts C D all Xi F.S₁ F.S₂ F.S₃ X₁ X₂ F.Cl W F.XiPub F.pub F.start₁ F.start₂
      (fun p a b => (F.start₃ p a b).toOption) T F.shared.blocksInOrder h.b₂ h.back₂).trans ?_
    funext a v
    rw [foldRun_at _ _ "the shared chain" 0 h.ft₂, view_nil]
    rfl
  · refine (runOfStarts₃ C D all Xi F.S₁ F.S₂ F.S₃ X₁ X₂ F.Cl W F.XiPub F.pub F.start₁ F.start₂
      (fun p a b => (F.start₃ p a b).toOption) T F.second.blocksInOrder h.b₃ h.back₃).trans ?_
    funext a v
    have e : (fun s => foldRun (frameAt D all D.key₃ T.ft₃) T.n₃ F.second.blocksInOrder [] s v) =
        fun s => (chainAt "the second chain" F.lastChainFirstTreeNumber F.second.blocksInOrder s v).toOption := by
      funext s
      rw [foldRun_at _ _ "the second chain" F.lastChainFirstTreeNumber h.ft₃, view_nil]
    show (viewWordsBelowPrime v && ((F.start₃ a.1 a.2.1 a.2.2).toOption.bind fun s =>
                  foldRun (frameAt D all D.key₃ T.ft₃) T.n₃ F.second.blocksInOrder [] s v).isSome) = _
    rw [e]
    rfl

theorem runGivesRowAt : RunGivesRowAt := by
  intro C D all Xi X₁ X₂ W F T h x v₁ v₂ v₃ hy
  obtain ⟨e₁, e₂, e₃⟩ := runsAtDesc C D all Xi X₁ X₂ W F T h
  rw [e₁, e₂, e₃]
  exact runGivesRow Xi F x v₁ v₂ v₃ hy

theorem liftedAtDesc : LiftedAtDesc := by
  intro C D all Xi X₁ X₂ W F T h
  refine ⟨fun _ _ => rfl, fun _ _ _ => rfl, fun q hq => ?_⟩
  have hq' : q ∈ T.p₂ :: T.l₂ := hq
  have hm : q.b ∈ (T.p₂ :: T.l₂).map (·.b) := List.mem_map.2 ⟨q, hq', rfl⟩
  rw [h.b₂] at hm
  obtain ⟨b₀, -, e⟩ := List.mem_map.1 hm
  exact ⟨b₀, e.symm⟩

/-- What the row's first stage puts out is what the first run puts out at some view. -/
theorem row_out₁ {C : CK} {D : WholeD} {all : List LeftT} {Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 : Type}
    (tF : TF) (tJ : TJ) (t3 : T3) (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (okF : Y → TF → Bool)
    (okJ : X₁ → TJ → Bool) (ok3 : X₂ → T3 → Bool) (x : Y) (y : (oneExternalString (2 ^ D.a) SgX).Str)
    (τ : Iop.Tr (plainRound TF tF :: uLT C D.ds₁)) (xo : X₁)
    (h : (T.row tF tJ t3 okF okJ ok3).S₁.out x y τ = some xo) : ∃ v, T.run₁ x v = some xo := by
  have h' : (if okF x τ.1.2 then
      (if sTests C (D.st₁ all) (y, fun p => p.1.elim0) τ.2.2 then
        T.run₁ x (sView C (D.st₁ all) (y, fun p => p.1.elim0) τ.2.2) else none) else none) =
      some xo := h
  split at h'
  · split at h'
    · exact ⟨_, h'⟩
    · cases h'
  · cases h'

theorem descRun₁_pub {Xi : Type} (F : FileDescription Xi) (x : Xi) (v : Fmt.View) (xo : F.XiPub × F.S₁)
    (h : descRun₁ F x v = some xo) : xo.1 = F.pub x := by
  unfold descRun₁ at h
  split at h
  · obtain ⟨s, -, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  · cases h

theorem firstKeyAtDesc : FirstKeyAtDesc := by
  intro C D all Xi X₁ X₂ W TF TJ T3 tF tJ t3 F T Q okF okJ ok3 h₁ h₂ h₃ hO a τ b hb
  have hb' : (((atDesc F T).row tF tJ t3 okF okJ ok3).S₁.out a.1 a.2 τ).map (fun xo =>
      (xo, ((atDesc F T).row tF tJ t3 okF okJ ok3).S₁.imp a.2 τ)) = some b := hb
  obtain ⟨xo, hx, rfl⟩ := Option.map_eq_some_iff.1 hb'
  obtain ⟨v, hv⟩ := row_out₁ tF tJ t3 (atDesc F T) okF okJ ok3 a.1 a.2 τ xo hx
  rw [(runsAtDesc C D all Xi X₁ X₂ W F T hO).1] at hv
  have hp := descRun₁_pub F a.1 v xo hv
  show (F.start₂ xo.1, a.2) = (F.start₂ (F.pub a.1), a.2)
  rw [hp]

end VerifiableInference.Desc.Sound
