-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/DescFin.lean: THE RULE OF COMPOSITION's FILLING AT A DESCRIPTION, WITH THE ENDS'
PART OF THE LAST TEST IN THE ROW. Definitions, statements written as `def … : Prop`, and their
proofs.

Why. The filling that is meant (`atDesc F T`, Johnson/Desc/Sound/DescThree.lean) lays no last test
into the row (`Three.fin` says yes always). The description's decision has one (`FileDescription.fin`). So
the row is laxer than the decision, and the blocks' laws are owed of the three folds alone: where a
description's soundness leans on a clause of its last test, the last block's law "into true" cannot
be met. One part of the last test cannot stand in the row: what reads the instance beyond its public
part (the asked reply: the row is read at the early part). THE REST CAN: a test g on the public part
and the three ends.

What is laid.
  `atDescFin F g T`: `atDesc F T` with the last test "g at the third chain's last record: at its own
    copy of the public part and of the two earlier ends, and at the chain's own last record". At g
    := "yes always" it IS `atDesc F T` (`atDescFin_true`: by rfl).
  `FinGives F g`: the description's last test's yes gives g's. THE ONE NEW PREMISE. Free at g :=
    "yes always".
  `RunGivesRowAtFin`, `runGivesRowAtFin`: the decision's yes gives the yes of the three runs of that
    filling.
  `FirstKeyAtDescFin`, `firstKeyAtDescFin`: the first key, as at `atDesc`.
  `FoldSlotsFin`, `foldSlotsFin`: the rule of composition for N slots behind one key
    (Johnson/Desc/Sound/FoldSlots.lean) at that filling: its premise `Glued` now asks, at the third
    chain's end: WHERE g SAYS YES the last relation holds of the last statement (`Three.Ends`): so
    the last relation need not be "true".

Every "there is", walked. None of its own.

Limits. Those of DescThree.lean and FoldSlots.lean. g is a letter: which clauses of a real last test
it holds is said where a description is laid. In `Three.Ends` what was handed to the third chain and
the chain's last statement are two variables: so g is handed THE LAST STATEMENT's OWN COPY of the
public part and of the earlier ends (a lifted block cannot turn that copy: in a run it is what was
handed to the chain): thus `Ends` can be met by a last relation that speaks of that copy. Terms:
lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.FoldSlotsProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open TypedOracleCompiler.Joined (LinkJ Links shA)
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString BTr Doomed)

variable {C : CK} {D : WholeD} {all : List LeftT} {Xi X₁ X₂ W : Type}

/-- **The filling that is meant, with the ends' part of the last test.** -/
def atDescFin (F : FileDescription Xi) (g : F.XiPub → F.S₁ → F.S₂ → F.S₃ → Bool)
    (T : ThreeAt C D all F X₁ X₂ W) :
    ThreeAt C D all F (F.XiPub × F.S₁) (F.XiPub × F.S₁ × F.S₂) W :=
  { atDesc F T with fin := fun _ s => g s.1.1 s.1.2.1 s.1.2.2 s.2 }

theorem atDescFin_true (F : FileDescription Xi) (T : ThreeAt C D all F X₁ X₂ W) :
    atDescFin F (fun _ _ _ _ => true) T = atDesc F T := rfl

/-- The description's last test's yes gives g's, at the instance's public part, AT AN INSTANCE THAT
PASSES THE TEST ON THE INSTANCE (under the decision's yes it has passed: so g may hold what the last
test gives only with that test). -/
def FinGives (F : FileDescription Xi) (g : F.XiPub → F.S₁ → F.S₂ → F.S₃ → Bool) : Prop :=
  ∀ x e₁ e₂ e₃, F.okStart x = true → F.fin x e₁ e₂ e₃ = true → g (F.pub x) e₁ e₂ e₃ = true

/-- **The decision's yes gives the yes of the three runs of the filling with g.** -/
def RunGivesRowAtFin : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Xi X₁ X₂ W : Type) (F : FileDescription Xi)
    (g : F.XiPub → F.S₁ → F.S₂ → F.S₃ → Bool) (T : ThreeAt C D all F X₁ X₂ W), OfDesc F T →
    FinGives F g →
    ∀ (x : Xi) (v₁ v₂ v₃ : Fmt.View), F.run x v₁ v₂ v₃ = true →
      runRow (atDescFin F g T).run₁ (atDescFin F g T).run₂ (atDescFin F g T).run₃ x v₁ v₂ v₃ = true

theorem runGivesRowAtFin : RunGivesRowAtFin := by
  intro C D all Xi X₁ X₂ W F g T hO hg x v₁ v₂ v₃ hy
  obtain ⟨r₁, r₂, -⟩ := runsAtDesc C D all Xi X₁ X₂ W F T hO
  have hr : (F.runEnd x v₁ v₂ v₃).isOk = true := hy
  revert hr
  cases he : F.runEnd x v₁ v₂ v₃ with
  | error e => exact fun hr => nomatch hr
  | ok ends =>
    intro _
    obtain ⟨e₁, e₂, e₃⟩ := ends
    obtain ⟨-, ks, k₁, k₂, k₃, ⟨s₃, hs, hc⟩, kf⟩ := (runEndIs Xi F x v₁ v₂ v₃ e₁ e₂ e₃).1 he
    have q₁ : (atDescFin F g T).run₁ x v₁ = some (F.pub x, e₁) := by
      show (atDesc F T).run₁ x v₁ = _
      rw [r₁]
      exact k₁
    have q₂ : (atDescFin F g T).run₂ (F.pub x, e₁) v₂ = some (F.pub x, e₁, e₂) := by
      show (atDesc F T).run₂ (F.pub x, e₁) v₂ = _
      rw [r₂]
      exact k₂
    have q₃ : (atDescFin F g T).run₃ (F.pub x, e₁, e₂) v₃ = true := by
      rw [run₃_eq]
      show (((((F.start₃ (F.pub x) e₁ e₂).toOption).map fun s =>
          (((F.pub x, e₁, e₂), s) : (F.XiPub × F.S₁ × F.S₂) × F.S₃)).bind fun s =>
        foldRun (frameAt D all D.key₃ T.ft₃) T.n₃ ((T.p₃ :: T.l₃).map (·.b)) (rowBack T.p₃ T.l₃) s
          v₃).map fun s => g s.1.1 s.1.2.1 s.1.2.2 s.2).getD false = true
      rw [hO.b₃, hO.back₃, hs]
      show ((foldRun (frameAt D all D.key₃ T.ft₃) T.n₃
        ((F.second.blocksInOrder.map below).map
          (Block.lift Prod.snd fun (t : (F.XiPub × F.S₁ × F.S₂) × F.S₃) s => (t.1, s)))
        [] ((F.pub x, e₁, e₂), s₃) v₃).map fun s => g s.1.1 s.1.2.1 s.1.2.2 s.2).getD false = true
      rw [fold_pair foldBelow _ _ _ _ rfl, if_pos k₃,
        foldRun_at _ _ "the second chain" F.lastChainFirstTreeNumber hO.ft₃, view_nil, hc]
      exact hg x e₁ e₂ e₃ ks kf
    unfold runRow
    simp only [q₁, q₂, q₃]

/-- **What the first key is**, as at `atDesc`. -/
def FirstKeyAtDescFin : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Xi X₁ X₂ W TF TJ T3 : Type) (tF : TF) (tJ : TJ)
    (t3 : T3) (F : FileDescription Xi) (g : F.XiPub → F.S₁ → F.S₂ → F.S₃ → Bool)
    (T : ThreeAt C D all F X₁ X₂ W) (Q : PlacesAt D all F W)
    (okF : Xi → TF → Bool) (okJ : F.XiPub × F.S₁ → TJ → Bool)
    (ok3 : F.XiPub × F.S₁ × F.S₂ → T3 → Bool)
    (h₁ : (rowIOR (atDescFin F g T).p₁ (atDescFin F g T).l₁).shape = uLT C D.ds₁)
    (h₂ : (rowIOR (atDescFin F g T).p₂ (atDescFin F g T).l₂).shape = uLT C D.ds₂)
    (h₃ : (rowIOR (atDescFin F g T).p₃ (atDescFin F g T).l₃).shape = uLT C D.ds₃),
    OfDesc F T →
    ∀ a τ b, (((atDescFin F g T).row tF tJ t3 okF okJ ok3).links
      ((atDescFin F g T).snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃)).K₁.out a τ = some b →
      (Prod.snd ((atDescFin F g T).in₂ b.1), b.2.1) = (F.start₂ (F.pub a.1), a.2)

theorem firstKeyAtDescFin : FirstKeyAtDescFin := by
  intro C D all Xi X₁ X₂ W TF TJ T3 tF tJ t3 F g T Q okF okJ ok3 h₁ h₂ h₃ hO a τ b hb
  have hb' : (((atDescFin F g T).row tF tJ t3 okF okJ ok3).S₁.out a.1 a.2 τ).map (fun xo =>
      (xo, ((atDescFin F g T).row tF tJ t3 okF okJ ok3).S₁.imp a.2 τ)) = some b := hb
  obtain ⟨xo, hx, rfl⟩ := Option.map_eq_some_iff.1 hb'
  obtain ⟨v, hv⟩ := row_out₁ tF tJ t3 (atDescFin F g T) okF okJ ok3 a.1 a.2 τ xo hx
  have hv' : (atDesc F T).run₁ a.1 v = some xo := hv
  rw [(runsAtDesc C D all Xi X₁ X₂ W F T hO).1] at hv'
  have hp := descRun₁_pub F a.1 v xo hv'
  show (F.start₂ xo.1, a.2) = (F.start₂ (F.pub a.1), a.2)
  rw [hp]

/-- **The rule of composition for N slots behind one key, at the filling with g.** The premises and
the conclusion of `FoldSlots` (Johnson/Desc/Sound/FoldSlots.lean), read at `atDescFin F g T`. -/
def FoldSlotsFin : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (X Rec X₁ X₂ W TF TJ T3 : Type) (tF : TF) (tJ : TJ)
    (t3 : T3) (F : FileDescription (X × Rec)) (g : F.XiPub → F.S₁ → F.S₂ → F.S₃ → Bool)
    (T : ThreeAt C D all F X₁ X₂ W) (Q : PlacesAt D all F W)
    (okF : X × Rec → TF → Bool) (okJ : F.XiPub × F.S₁ → TJ → Bool)
    (ok3 : F.XiPub × F.S₁ × F.S₂ → T3 → Bool)
    (h₁ : (rowIOR (atDescFin F g T).p₁ (atDescFin F g T).l₁).shape = uLT C D.ds₁)
    (h₂ : (rowIOR (atDescFin F g T).p₂ (atDescFin F g T).l₂).shape = uLT C D.ds₂)
    (h₃ : (rowIOR (atDescFin F g T).p₃ (atDescFin F g T).l₃).shape = uLT C D.ds₃) (N : ℕ)
    (s₂ : Rec → F.S₂),
    OfDesc F T → (atDescFin F g T).Fits →
    EachGood Q.on₁ Q.R₁ 0 ((atDescFin F g T).p₁ :: (atDescFin F g T).l₁) →
    EachLostBoth N Q.on₂ Q.R₂ (actsOf Prod.snd D.t₁ (atDescFin F g T).p₂ (atDescFin F g T).l₂) 0
      ((atDescFin F g T).p₂ :: (atDescFin F g T).l₂) →
    EachGood Q.on₃ Q.R₃ 0 ((atDescFin F g T).p₃ :: (atDescFin F g T).l₃) →
    (atDescFin F g T).Glued Q →
    (∀ d ∈ D.ds₂, ∀ j ∈ d.opens, D.t₁ ≤ j) →
    (∀ x rec, F.start₂ (F.pub (x, rec)) = s₂ rec) →
    ∀ rec : Rec,
      ((((atDescFin F g T).row tF tJ t3 okF okJ ok3).links
        ((atDescFin F g T).snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃)).comap
          fun x : X => (x, rec)).KnowsJ N
        (fun a : (F.XiPub × F.S₁) × (EAll D all).Str => (F.start₂ a.1.1, a.2.1)) (fun _ => ())

open _root_.CompileK.Joined (allKind_const) in
theorem foldSlotsFin : FoldSlotsFin := by
  intro C D all X Rec X₁ X₂ W TF TJ T3 tF tJ t3 F g T Q okF okJ ok3 h₁ h₂ h₃ N s₂ hO hF g₁ hL g₃ hG
    ho one rec
  obtain ⟨e1, e2, hb⟩ := liftedAtDesc C D all (X × Rec) X₁ X₂ W F T hO
  have hh := each_hands Prod.snd (fun (t : (F.XiPub × F.S₁) × F.S₂) (s : F.S₂) => (t.1, s)) e1 e2
    D.t₁ (atDescFin F g T).l₂ (atDescFin F g T).p₂ 0
    (actsOf Prod.snd D.t₁ (atDescFin F g T).p₂ (atDescFin F g T).l₂)
    (fun k => by rw [Nat.zero_add]; rfl) hF.tiled₂ hb
    (fun q hq d hd =>
      ho d (hF.data₂ ▸ mem_rowData (atDescFin F g T).p₂ (atDescFin F g T).l₂ q hq d hd))
  have hkk := keyed_back_both N Q.on₂ Q.R₂
    (actsOf Prod.snd D.t₁ (atDescFin F g T).p₂ (atDescFin F g T).l₂)
    (actsOf Prod.snd D.t₁ (atDescFin F g T).p₂ (atDescFin F g T).l₂
      (0 + ((atDescFin F g T).p₂ :: (atDescFin F g T).l₂).length)) (atDescFin F g T).l₂
    (atDescFin F g T).p₂ 0 hL
  obtain ⟨gh, hgh⟩ := headOfActs _ F.Cl W C _
    (actsOf Prod.snd D.t₁ (atDescFin F g T).p₂ (atDescFin F g T).l₂) 0
    ((atDescFin F g T).p₂ :: (atDescFin F g T).l₂) hh
  refine ⟨?_, ?_, ?_, fun _ _ _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩
  · exact LinkJ.ofLocal (allKind_const (fun _ => rfl) _) N
      (fun a ha => file_know₁ tF tJ t3 (atDescFin F g T) Q okF okJ ok3 h₁ h₂ h₃ hF g₁ hG.glue₁
        ((a.1, rec), a.2) ha)
      (fun y => (s₂ rec, y)) fun a τ b hb' => by
        have k := firstKeyAtDescFin C D all (X × Rec) X₁ X₂ W TF TJ T3 tF tJ t3 F g T Q okF okJ ok3
          h₁ h₂ h₃ hO ((a.1, rec), a.2) τ b hb'
        rw [one] at k
        exact k
  · refine seamLink C D all (X × Rec) _ _ _ _ _ F.Cl W TF TJ T3 _ _ tF tJ t3 (atDescFin F g T) Q okF
      okJ ok3 h₁ h₂ h₃ N _ _ _ _ hF hkk hG.glue₂
      ⟨fun k => gh (k.1, k.2, fun _ _ => none), fun a => ?_⟩ ⟨fun _ _ => (), fun _ _ => rfl⟩
    rw [hgh]
    refine congrArg gh ?_
    show (F.start₂ a.1.1, a.2.1,
      fun j x => if D.t₁ ≤ j ∧ j < (atDescFin F g T).p₂.base then _ else none) = _
    refine congrArg (fun f => (F.start₂ a.1.1, a.2.1, f)) (funext fun j => funext fun x => ?_)
    rw [if_neg]
    rw [hF.base₂]
    omega
  · exact LinkJ.ofLocal (allKind_const (fun _ => rfl) _) N
      (file_know₃ tF tJ t3 (atDescFin F g T) Q okF okJ ok3 h₁ h₂ h₃ hF g₃ hG.ends) (fun _ => ())
      (fun _ _ _ _ => rfl)

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.runGivesRowAtFin
#print axioms VerifiableInference.Desc.Sound.firstKeyAtDescFin
#print axioms VerifiableInference.Desc.Sound.foldSlotsFin
