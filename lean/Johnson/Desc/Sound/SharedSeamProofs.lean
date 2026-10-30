-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SharedSeamProofs.lean: the proofs of the statements of
Johnson/Desc/Sound/SharedSeam.lean: `SeamLink` and `SeamOfGood` outright; `FoldBelow`
(ChainRule.lean) ENTERS AS A HYPOTHESIS INTO FOUR THEOREMS: `fold_pair`, `runOfStarts₁_of`,
`runOfStarts_of` and `runOfStarts₃_of`; the last three are closed in
Johnson/Desc/Sound/FileBatchProofs.lean.

Limits: those of Johnson/Desc/Sound/SharedSeam.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.SharedSeam
import Johnson.Desc.Sound.SharedOwnProofs
import Johnson.Desc.Sound.LinkMoves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open TypedOracleCompiler.Joined (LinkJ Links shA)
open _root_.Compile.Joined (plainRound)
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString RAnn)

/-- A stage at equal data. -/
theorem stage_at {S : Type} (C : CK) (F : Frame) (run : S → Fmt.View → Option S) (b b' : ℕ)
    (ds ds' : List RDT) (eb : b = b') (ed : ds = ds') (a : S × F.E.Str)
    (σ : Iop.Tr (uLT C ds')) :
    (stageIOR C ⟨F.a, b, F.all, ds, F.key, F.all⟩ run).red.out a
        (cast (congrArg (fun x => Iop.Tr (uLT C x)) ed.symm) σ) =
      (stageIOR C ⟨F.a, b', F.all, ds', F.key, F.all⟩ run).red.out a σ := by
  subst eb
  subst ed
  rfl

theorem seamLink : SeamLink := by
  rintro C D all Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 κ₁ κ₂ tF tJ t3 T Q okF okJ ok3 h₁ h₂ h₃ N kA kZ k₁
    k₂ hF hk hG ⟨g, hg⟩ ⟨G, hGk⟩
  have hrow : (rowIOR T.p₂ T.l₂).shape = uLT C (rowData T.p₂ T.l₂) :=
    shapeIsChain _ _ _ _ _ _ _
  have c0 := chainLink S₂ Cl W C (frameAt D all D.key₂ T.ft₂) T.n₂ N Q.on₂ Q.R₂ T.d T.p₂ T.l₂ hrow
    kA kZ hF.tiled₂ hk
  have c1 := linkJ_castShape _ (uLT C D.ds₂) h₂ c0
  have c2 := linkJ_glued (linkJ_offOn c1)
    (fun a : X₁ × (EAll D all).Str => (T.in₂ a.1, a.2))
    (fun (a : X₁ × (EAll D all).Str) (b : S₂ × (EAll D all).Str) => (T.out₂ a.1 b.1, b.2)) k₁ k₂
    (T.mid₂ Q) g hg G hGk (fun a b w hw => hG a.1 b w hw)
  have c3 := linkJ_front c2 (plainRound TJ tJ) (RAnn.ofShared .sh _) rfl
    (fun x m => okJ x.1 m.2) T.d
  refine linkJ_sub c3
    ((T.row tF tJ t3 okF okJ ok3).links (T.snd tF tJ t3 Q okF okJ ok3 h₁ h₂ h₃)).K₂.out ?_
  rintro ⟨x₁, y⟩ τ b hb
  have hb' : (if okJ x₁ τ.1.2 then (stageIOR C (D.st₂ all all) T.run₂).out x₁ y τ.2.2
      else none).map (fun xo => (xo, (stageIOR C (D.st₂ all all) T.run₂).imp y τ.2.2)) =
      some b := hb
  by_cases ht : okJ x₁ τ.1.2 = true
  · rw [if_pos ht] at hb'
    show (if okJ x₁ τ.1.2 = true then _ else none) = some b
    rw [if_pos ht, ← hb']
    show ((chainIOR C (frameAt D all D.key₂ T.ft₂) T.n₂ ((T.p₂ :: T.l₂).map (·.b)) T.p₂.base
        (rowData T.p₂ T.l₂) (rowBack T.p₂ T.l₂)).red.out (T.in₂ x₁, y)
        (cast (congrArg Iop.Tr hrow) (cast (congrArg Iop.Tr h₂.symm) τ.2.2))).map
        (fun b : S₂ × (EAll D all).Str => (T.out₂ x₁ b.1, b.2)) = _
    have ec : cast (congrArg Iop.Tr hrow) (cast (congrArg Iop.Tr h₂.symm) τ.2.2) =
        cast (congrArg (fun x => Iop.Tr (uLT C x)) hF.data₂.symm) τ.2.2 := by
      rw [cast_cast]
    rw [ec]
    have es := stage_at C (frameAt D all D.key₂ T.ft₂)
      (foldRun (frameAt D all D.key₂ T.ft₂) T.n₂ ((T.p₂ :: T.l₂).map (·.b)) (rowBack T.p₂ T.l₂))
      T.p₂.base D.t₁ (rowData T.p₂ T.l₂) D.ds₂ hF.base₂ hF.data₂ (T.in₂ x₁, y) τ.2.2
    rw [show (chainIOR C (frameAt D all D.key₂ T.ft₂) T.n₂ ((T.p₂ :: T.l₂).map (·.b)) T.p₂.base
        (rowData T.p₂ T.l₂) (rowBack T.p₂ T.l₂)).red.out (T.in₂ x₁, y)
        (cast (congrArg (fun x => Iop.Tr (uLT C x)) hF.data₂.symm) τ.2.2) = _ from es]
    show ((if sTests C (D.st₂ all all) y τ.2.2 then
        foldRun (frameAt D all D.key₂ T.ft₂) T.n₂ ((T.p₂ :: T.l₂).map (·.b)) (rowBack T.p₂ T.l₂)
          (T.in₂ x₁) (sView C (D.st₂ all all) y τ.2.2) else none).map
        (fun xo => (xo, (y.1, sLeft C (D.st₂ all all) y τ.2.2)))).map
        (fun b : S₂ × (EAll D all).Str => (T.out₂ x₁ b.1, b.2)) =
      (if sTests C (D.st₂ all all) y τ.2.2 then
        (foldRun (frameAt D all D.key₂ T.ft₂) T.n₂ ((T.p₂ :: T.l₂).map (·.b)) (rowBack T.p₂ T.l₂)
          (T.in₂ x₁) (sView C (D.st₂ all all) y τ.2.2)).map (T.out₂ x₁) else none).map
        (fun xo => (xo, (y.1, sLeft C (D.st₂ all all) y τ.2.2)))
    by_cases hs : sTests C (D.st₂ all all) y τ.2.2 = true
    · rw [if_pos hs, if_pos hs]
      generalize foldRun (frameAt D all D.key₂ T.ft₂) T.n₂ ((T.p₂ :: T.l₂).map (·.b))
        (rowBack T.p₂ T.l₂) (T.in₂ x₁) (sView C (D.st₂ all all) y τ.2.2) = o
      cases o <;> rfl
    · rw [if_neg hs, if_neg hs]
      rfl
  · rw [if_neg ht] at hb'
    cases hb'

/-- Every piece's data lie in the row's. -/
theorem mem_rowData {S Cl W : Type} {C : CK} {F : Frame} (p : Piece C F S Cl W)
    (l : List (Piece C F S Cl W)) (q : Piece C F S Cl W) (hq : q ∈ p :: l) (d : RDT)
    (hd : d ∈ q.ds) : d ∈ rowData p l :=
  List.mem_flatMap.2 ⟨q, hq, hd⟩

theorem seamOfGood : SeamOfGood := by
  intro C D all Y S₁ S₂ S₀ S₃ X₁ X₂ Cl W TF TJ T3 tF tJ t3 T Q okF okJ ok3 h₁ h₂ h₃ N get set Ra Rc
    hF hQ hg hr hk g1 g2 hb ho hG
  obtain ⟨e1, e2⟩ := each_own Q.on₂ Ra Rc get set g1 g2 D.t₁ T.l₂ T.p₂ 0
    (actsOf get D.t₁ T.p₂ T.l₂) (fun k => by rw [Nat.zero_add]; rfl) hF.tiled₂ hg hr hk hb
    (fun q hq d hd => ho d (hF.data₂ ▸ mem_rowData T.p₂ T.l₂ q hq d hd))
  rw [← hQ] at e1
  have hkk := keyed_back N Q.on₂ Q.R₂ (actsOf get D.t₁ T.p₂ T.l₂)
    (actsOf get D.t₁ T.p₂ T.l₂ (0 + (T.p₂ :: T.l₂).length)) T.l₂ T.p₂ 0 e1
  obtain ⟨gh, hgh⟩ := headOfActs S₂ Cl W C _ (actsOf get D.t₁ T.p₂ T.l₂) 0 (T.p₂ :: T.l₂) e2
  refine seamLink C D all Y S₁ S₂ S₃ X₁ X₂ Cl W TF TJ T3 _ _ tF tJ t3 T Q okF okJ ok3 h₁ h₂ h₃ N _ _
    _ _ hF hkk hG ⟨fun k => gh (k.1, k.2, fun _ _ => none), fun a => ?_⟩
    ⟨fun _ _ => (), fun _ _ => rfl⟩
  rw [hgh]
  refine congrArg gh ?_
  show (get (T.in₂ a.1), a.2.1, fun j x => if D.t₁ ≤ j ∧ j < T.p₂.base then _ else none) = _
  refine congrArg (fun f => (get (T.in₂ a.1), a.2.1, f)) (funext fun j => funext fun x => ?_)
  rw [if_neg]
  rw [hF.base₂]
  omega

/-- The fold of blocks with the test below the prime, lifted to a pair, from (a, s). -/
theorem fold_pair (hB : FoldBelow) {A S₀ Cl : Type} (F : Frame) (n : String)
    (bs : List (Block S₀ Cl)) (back : List Fmt.RoundView) (hk : viewWordsBelowPrime ⟨back, []⟩ = true) (a : A)
    (s : S₀) (v : Fmt.View) :
    foldRun F n ((bs.map below).map (Block.lift Prod.snd fun (t : A × S₀) s => (t.1, s))) back
        (a, s) v =
      if viewWordsBelowPrime v = true then (foldRun F n bs back s v).map fun z => (a, z) else none := by
  rw [foldLift _ _ _ _ _ _ _ Prod.snd (fun (t : A × S₀) s => (t.1, s)) (fun _ _ => rfl)
    (fun _ _ _ => rfl), hB _ _ _ _ _ _ hk]
  show (if viewWordsBelowPrime v = true then foldRun F n bs back s v else none).map _ = _
  by_cases h : viewWordsBelowPrime v = true
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    rfl

theorem runOfStarts₁_of (hB : FoldBelow) : RunOfStarts₁ := by
  intro C D all Y S₁' S₂' S₃' X₁ X₂ Cl W P pub start₁ start₂ start₃ T bs back hb h0 hk
  funext x v
  show (foldRun (frameAt D all D.key₁ T.ft₁) T.n₁ ((T.p₁ :: T.l₁).map (·.b)) (rowBack T.p₁ T.l₁)
    (pub x, start₁ (pub x)) v).map (fun s : P × S₁' => s) = _
  rw [hb, h0, fold_pair hB _ _ _ _ hk]
  by_cases h : viewWordsBelowPrime v = true
  · rw [if_pos h]
    generalize foldRun (frameAt D all D.key₁ T.ft₁) T.n₁ bs back (start₁ (pub x)) v = o
    cases o <;> rfl
  · rw [if_neg h]
    rfl

theorem runOfStarts_of (hB : FoldBelow) : RunOfStarts := by
  intro C D all Y S₁' S₂' S₃' X₁ X₂ Cl W P pub start₁ start₂ start₃ T bs hb h0
  funext a v
  show (foldRun (frameAt D all D.key₂ T.ft₂) T.n₂ ((T.p₂ :: T.l₂).map (·.b)) (rowBack T.p₂ T.l₂)
    (a, start₂ a.1) v).map (fun s : (P × S₁') × S₂' => (s.1.1, s.1.2, s.2)) = _
  rw [hb, h0, fold_pair hB _ _ _ _ rfl]
  by_cases h : viewWordsBelowPrime v = true
  · rw [if_pos h, if_pos h]
    generalize foldRun (frameAt D all D.key₂ T.ft₂) T.n₂ bs [] (start₂ a.1) v = o
    cases o <;> rfl
  · rw [if_neg h, if_neg h]
    rfl

/-- The third chain's run, without a case distinction. -/
theorem run₃_eq {C : CK} {D : WholeD} {all : List LeftT} {Y S₁ S₂ S₃ X₁ X₂ Cl W : Type}
    (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (a : X₂) (v : Fmt.View) :
    T.run₃ a v = (((T.in₃ a).bind fun s =>
      foldRun (frameAt D all D.key₃ T.ft₃) T.n₃ ((T.p₃ :: T.l₃).map (·.b)) (rowBack T.p₃ T.l₃) s
        v).map (T.fin a)).getD false := by
  unfold Three.run₃
  cases ((T.in₃ a).bind fun s =>
    foldRun (frameAt D all D.key₃ T.ft₃) T.n₃ ((T.p₃ :: T.l₃).map (·.b)) (rowBack T.p₃ T.l₃) s
      v) <;> rfl

theorem runOfStarts₃_of (hB : FoldBelow) : RunOfStarts₃ := by
  intro C D all Y S₁' S₂' S₃' X₁ X₂ Cl W P pub start₁ start₂ start₃ T bs hb h0
  funext a v
  rw [run₃_eq]
  show ((((start₃ a.1 a.2.1 a.2.2).map fun s => (a, s)).bind fun s =>
      foldRun (frameAt D all D.key₃ T.ft₃) T.n₃ ((T.p₃ :: T.l₃).map (·.b)) (rowBack T.p₃ T.l₃) s
        v).map fun _ => true).getD false = _
  rw [hb, h0]
  cases start₃ a.1 a.2.1 a.2.2 with
  | none =>
    show false = (viewWordsBelowPrime v && false)
    rw [Bool.and_false]
  | some s =>
    show ((foldRun (frameAt D all D.key₃ T.ft₃) T.n₃
        ((bs.map below).map (Block.lift Prod.snd fun (t : (P × S₁' × S₂') × S₃') s => (t.1, s)))
        [] (a, s) v).map fun _ => true).getD false =
      (viewWordsBelowPrime v && (foldRun (frameAt D all D.key₃ T.ft₃) T.n₃ bs [] s v).isSome)
    rw [fold_pair hB _ _ _ _ rfl]
    by_cases h : viewWordsBelowPrime v = true
    · rw [if_pos h, h, Bool.true_and]
      generalize foldRun (frameAt D all D.key₃ T.ft₃) T.n₃ bs [] s v = o
      cases o <;> rfl
    · rw [if_neg h, Bool.eq_false_iff.2 h, Bool.false_and]
      rfl

end VerifiableInference.Desc.Sound
