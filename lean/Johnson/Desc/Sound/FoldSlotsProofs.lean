-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/FoldSlotsProofs.lean: the proofs of the statements of
Johnson/Desc/Sound/FoldSlots.lean. Theorems with their proofs; each has the statement's name with a
small first letter. What is said, under which premises, and the limits: that file's head.

How. `jWithin_both`: in a shared round in which only the shared part speaks, the union over the
slots of "one common bad set or the slot's own" has at most eK + N · eO members; by induction on the
rounds, after the manner of `jWithin_of_same` (Blocks/Batch/Kit.lean) and `jWithin_times`
(Ior/BatchSeq.lean). `knowB_of_lost_both`: the bad sets are the two families made from "the prover
has lost" (`lostFam`, Ior/OnlineK.lean), laid together. `paidBoth`: that rule at the block's own
reduction, with `admBack`. `chainLinkBoth`: `chainLink` at the keys made backwards, then
`headOfActs`: as `chainLinkActs_of`. `foldSlots`: l₁ and l₃ by `LinkJ.ofLocal` from `file_know₁` and
`file_know₃` (read at (·, rec)), the law on the first key by `firstKeyAtDesc` and premise 8; l₂ by
`seamLink` at the keys made backwards, as `seamOfGood`.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FoldSlots
import Johnson.Desc.Sound.DescThreeProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Iop
open Prob IOR

/-- A transcript without a bad challenge of the two families together has none of either. -/
theorem BadFam.clean_both : ∀ {s : Shape} (B B' : BadFam s) (τ : Tr s),
    (B.both B').Clean τ → B.Clean τ ∧ B'.Clean τ
  | [], _, _, _, _ => ⟨trivial, trivial⟩
  | _ :: _, (B, k), (B', k'), (m, c, τ), h => by
      have h' : c ∉ {c | c ∈ B m ∨ c ∈ B' m} ∧ ((k m c).both (k' m c)).Clean τ := h
      obtain ⟨h1, h2⟩ := BadFam.clean_both (k m c) (k' m c) τ h'.2
      exact ⟨⟨fun hc => h'.1 (Or.inl hc), h1⟩, ⟨fun hc => h'.1 (Or.inr hc), h2⟩⟩

/-- Shared rounds in which only the shared part is sent: if each slot's bad sets are one common
family B₀, within εK, laid together with a family of the slot's own, within εO, then jointly they
are within εK + N · εO. -/
theorem jWithin_both (N : ℕ) :
    ∀ (s : Shape) (εK εO : Err s) (B₀ : BadFam s) (Bo : Fin N → BadFam s)
      (G : Fin N → Option (Bool × BadFam s)), B₀.Within εK → (∀ j, (Bo j).Within εO) →
      (∀ j p, G j = some p → p.2 = B₀.both (Bo j)) →
      JWithin N s (RoundSplits.const (RAnn.ofShared .sh) s) (Err.add εK (Err.times N εO)) G
  | [], _, _, _, _, _, _, _, _ => trivial
  | r :: s, (eK, εK), (eO, εO), B₀, Bo, G, hK, hO, h => by
      show JWithin N (r :: s) (RAnn.ofShared .sh r, RoundSplits.const (RAnn.ofShared .sh) s)
        (eK + N * eO, Err.add εK (Err.times N εO)) G
      intro m0 m
      refine ⟨?_, fun v => jWithin_both N s εK εO (B₀.2 m0 v) (fun j => (Bo j).2 m0 v) _
        (hK.2 m0 v) (fun j => (hO j).2 m0 v) fun j p hp => ?_⟩
      · have h1 := cnt_exists_le_mul (fun (j : Fin N) (c : r.Chal) => c ∈ (Bo j).1 m0) eO
          fun j => (hO j).1 m0
        rw [Fintype.card_fin] at h1
        refine le_trans (cnt_le_add (Q := fun c => c ∈ B₀.1 m0)
          (R := fun c => ∃ j : Fin N, c ∈ (Bo j).1 m0) ?_) (Nat.add_le_add (hK.1 m0) h1)
        rintro c ⟨j, p, hp, _, hc⟩
        rw [h j p hp] at hc
        rcases (hc : c ∈ B₀.1 m0 ∨ c ∈ (Bo j).1 m0) with hc | hc
        · exact Or.inl hc
        · exact Or.inr ⟨j, hc⟩
      · obtain ⟨p', hp', rfl⟩ := Option.map_eq_some_iff.mp hp
        show p'.2.2 m0 v = (B₀.2 m0 v).both ((Bo j).2 m0 v)
        rw [h j p' hp']
        rfl

theorem knowB_of_lost_both : Spec.knowB_of_lost_both := by
  intro Xi Xo κ Ei Eo Wi Wo R N key lostK lostO on RA RB ext εK εO hK hO hback
  refine ⟨fun a => (lostFam R.shape εK (lostK (key a))).both (lostFam R.shape εO (lostO a)),
    fun a τ b w ha hτ hb hw => ?_, fun a ha => ?_⟩
  · obtain ⟨h1, h2⟩ := BadFam.clean_both _ _ τ hτ
    exact hback a τ b w ha (lostFam_clean (hK a ha) h1) (lostFam_clean (hO a ha) h2) hb hw
  · by_cases hne : ∃ j aj, a j = some aj
    · obtain ⟨j₀, a₀, h₀⟩ := hne
      refine jWithin_both N R.shape εK εO (lostFam R.shape εK (lostK (key a₀)))
        (fun j => ((a j).map fun aj => lostFam R.shape εO (lostO aj)).getD (BadFam.empty _)) _
        (lostFam_within _ _ _) (fun j => ?_) fun j p hp => ?_
      · beta_reduce
        cases a j with
        | none => exact BadFam.empty_within _ _
        | some aj => exact lostFam_within _ _ _
      · obtain ⟨aj, haj, rfl⟩ := Option.map_eq_some_iff.mp hp
        show (lostFam R.shape εK (lostK (key aj))).both (lostFam R.shape εO (lostO aj)) = _
        beta_reduce
        rw [ha j j₀ aj a₀ haj h₀, haj]
        rfl
    · refine jWithin_both N R.shape εK εO (BadFam.empty _) (fun _ => BadFam.empty _) _
        (BadFam.empty_within _ _) (fun _ => BadFam.empty_within _ _) fun j p hp => ?_
      obtain ⟨aj, haj, rfl⟩ := Option.map_eq_some_iff.mp hp
      exact absurd ⟨j, aj, haj⟩ hne

end Iop

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open TypedOracleCompiler.Joined (LinkJ Links shA)
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString BTr Doomed)

theorem paidBoth : PaidBoth := by
  rintro S Cl W C F p on on' R R' act kB N ⟨εK, εO, hle, lostK, lostO, hK, hO, hb⟩
  refine ⟨?_, admBack S Cl W C F p act kB N⟩
  obtain ⟨bad, c, J⟩ := Iop.knowB_of_lost_both S S act.1 F.E F.E W W p.ior N act.2 lostK lostO on R
    (Reduction.orOff on' R') p.ext εK εO hK hO
    (fun a τ b w ha hk ho hout hw =>
      (hb a τ b ha hk ho hout).2 w (hw.elim id fun n => absurd (hb a τ b ha hk ho hout).1 n))
  exact ⟨bad, c, fun a ha => Iop.JWithin.mono N _ _ _ hle
    (J a fun j j' aj aj' hj hj' => congrArg Prod.fst (ha j j' aj aj' hj hj'))⟩

theorem lostBothOfLostBy : LostBothOfLostBy := by
  rintro S Cl W C F p on on' R R' act N ⟨lost, hD, hb⟩
  refine ⟨p.err, Err.zero _, ?_, lost, fun _ _ => True, hD,
    fun _ _ => Doomed.of_forall _ _ fun _ => trivial, fun a τ b ha hl _ ho => hb a τ b ha hl ho⟩
  have e : ∀ (s : Shape), Err.times N (Err.zero s) = Err.zero s := by
    intro s
    induction s with
    | nil => rfl
    | cons r s ih =>
      show (N * 0, Err.times N (Err.zero s)) = (0, Err.zero s)
      rw [ih, Nat.mul_zero]
  rw [e, Err.add_zero]
  exact Err.le_refl _

theorem lostBothOfOwn : LostBothOfOwn := by
  intro S Cl W C F p on on' R R' act N εO hle hD
  refine ⟨Err.zero _, εO, ?_, fun _ _ => True,
    fun a τ => ∀ b, p.ior.red.out a τ = some b → on' b ∧ ∀ w, R' b w → R a (p.ext a τ w),
    fun _ _ => Doomed.of_forall _ _ fun _ => trivial, hD, fun a τ b _ _ hl ho => hl b ho⟩
  rw [Err.zero_add]
  exact hle

theorem lostBothBeside : LostBothBeside := by
  rintro S Cl W C F p on on' R R' Rc act N ⟨εK, εO, hle, lostK, lostO, hK, hO, hb⟩ hc
  refine ⟨εK, εO, hle, lostK, lostO, hK, hO, fun a τ b ha hk ho hout => ?_⟩
  obtain ⟨h1, h2⟩ := hb a τ b ha hk ho hout
  exact ⟨h1, fun w hw => ⟨h2 w hw.1, hc a τ b w ha hout h1 hw.2⟩⟩

/-- The premise of `ChainLink` at the keys made backwards. -/
theorem keyed_back_both {S Cl W : Type} {C : CK} {F : Frame} (N : ℕ)
    (on : ℕ → S × F.E.Str → Prop) (R : ℕ → S × F.E.Str → W → Prop) (act : ℕ → BKey F S)
    (kZ : BKey F S) :
    ∀ (l : List (Piece C F S Cl W)) (p : Piece C F S Cl W) (i : ℕ),
      EachLostBoth N on R act i (p :: l) → Keyed N on R i p l (keysBack act kZ i (p :: l)) kZ
  | [], p, i, h => paidBoth S Cl W C F p _ _ _ _ (act i) kZ N h.1
  | q :: l, p, i, h =>
    ⟨keysBack act kZ (i + 1) (q :: l), paidBoth S Cl W C F p _ _ _ _ (act i) _ N h.1,
      keyed_back_both N on R act kZ l q (i + 1) h.2⟩

theorem chainLinkBoth : ChainLinkBoth := by
  intro S Cl W C F name N on R d p l h act ht hl hh
  have k := chainLink S Cl W C F name N on R d p l h _ (act (1 + l.length)) ht
    (keyed_back_both N on R act (act (1 + l.length)) l p 0 hl)
  have hd := headOfActs S Cl W C F act 0 (p :: l) hh
  have e : 0 + (p :: l).length = 1 + l.length := by
    simp only [List.length_cons]
    omega
  rw [e] at hd
  obtain ⟨g, hg⟩ := hd
  exact k.conseq (act 0).2 g hg id (fun _ h => h) (fun _ _ _ h => h) (fun _ _ h => h)

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- Lifted blocks that open no tree below lo hand the acting parts that are meant on, along a row.
(The half of `each_own`, SharedOwnProofs.lean, that asks no law of a block.) -/
theorem each_hands {S₀ : Type} (get : S → S₀) (set : S → S₀ → S)
    (g1 : ∀ t s, get (set t s) = s) (g2 : ∀ t s s', set (set t s) s' = set t s') (lo : ℕ) :
    ∀ (l : List (Piece C F S Cl W)) (p : Piece C F S Cl W) (i : ℕ) (act : ℕ → BKey F S),
      (∀ k, act (i + k) = actAt F get lo (hiAt k p l)) → Tiled p l →
      (∀ q ∈ p :: l, ∃ b₀ : Block S₀ Cl, q.b = b₀.lift get set) →
      (∀ q ∈ p :: l, ∀ d ∈ q.ds, ∀ j ∈ d.opens, lo ≤ j) →
      EachHands act i (p :: l)
  | [], p, i, act, ha, _, hb, ho => by
    have h0 : act i = actAt F get lo p.base := ha 0
    have h1 : act (i + 1) = actAt F get lo (p.base + p.trees) := ha 1
    obtain ⟨b₀, hb₀⟩ := hb p (List.mem_cons_self ..)
    have hh : p.HandsAct (act i) (act (i + 1)) := by
      rw [h0, h1]
      exact liftHands S S₀ Cl W C F get set b₀ p lo hb₀ g1 g2 (ho p (List.mem_cons_self ..))
    exact ⟨hh, trivial⟩
  | q :: l, p, i, act, ha, ht, hb, ho => by
    have h0 : act i = actAt F get lo p.base := ha 0
    have h1 : act (i + 1) = actAt F get lo (p.base + p.trees) := by
      rw [ha 1]
      show actAt F get lo q.base = _
      rw [ht.2.2.2.1]
    obtain ⟨b₀, hb₀⟩ := hb p (List.mem_cons_self ..)
    have hh : p.HandsAct (act i) (act (i + 1)) := by
      rw [h0, h1]
      exact liftHands S S₀ Cl W C F get set b₀ p lo hb₀ g1 g2 (ho p (List.mem_cons_self ..))
    exact ⟨hh, each_hands get set g1 g2 lo l q (i + 1) act
      (fun k => by
        rw [show i + 1 + k = i + (k + 1) by omega]
        exact ha (k + 1))
      ht.2.2.2.2 (fun q' hq' => hb q' (List.mem_cons_of_mem _ hq'))
      (fun q' hq' => ho q' (List.mem_cons_of_mem _ hq'))⟩

open _root_.CompileK.Joined (allKind_const) in
theorem foldSlots : FoldSlots := by
  intro C D all X Rec X₁ X₂ W TF TJ T3 tF tJ t3 F T Q okF okJ ok3 h₁ h₂ h₃ N s₂ hO hF g₁ hL g₃ hG ho
    one rec
  obtain ⟨e1, e2, hb⟩ := liftedAtDesc C D all (X × Rec) X₁ X₂ W F T hO
  have hh := each_hands Prod.snd (fun (t : (F.XiPub × F.S₁) × F.S₂) (s : F.S₂) => (t.1, s)) e1 e2
    D.t₁ (atDesc F T).l₂ (atDesc F T).p₂ 0
    (actsOf Prod.snd D.t₁ (atDesc F T).p₂ (atDesc F T).l₂) (fun k => by rw [Nat.zero_add]; rfl)
    hF.tiled₂ hb
    (fun q hq d hd => ho d (hF.data₂ ▸ mem_rowData (atDesc F T).p₂ (atDesc F T).l₂ q hq d hd))
  have hkk := keyed_back_both N Q.on₂ Q.R₂ (actsOf Prod.snd D.t₁ (atDesc F T).p₂ (atDesc F T).l₂)
    (actsOf Prod.snd D.t₁ (atDesc F T).p₂ (atDesc F T).l₂
      (0 + ((atDesc F T).p₂ :: (atDesc F T).l₂).length)) (atDesc F T).l₂ (atDesc F T).p₂ 0 hL
  obtain ⟨gh, hgh⟩ := headOfActs _ F.Cl W C _
    (actsOf Prod.snd D.t₁ (atDesc F T).p₂ (atDesc F T).l₂) 0
    ((atDesc F T).p₂ :: (atDesc F T).l₂) hh
  refine ⟨?_, ?_, ?_, fun _ _ _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩
  · exact LinkJ.ofLocal (allKind_const (fun _ => rfl) _) N
      (fun a ha => file_know₁ tF tJ t3 (atDesc F T) Q okF okJ ok3 h₁ h₂ h₃ hF g₁ hG.glue₁
        ((a.1, rec), a.2) ha)
      (fun y => (s₂ rec, y)) fun a τ b hb' => by
        have k := firstKeyAtDesc C D all (X × Rec) X₁ X₂ W TF TJ T3 tF tJ t3 F T Q okF okJ ok3 h₁ h₂
          h₃ hO ((a.1, rec), a.2) τ b hb'
        rw [one] at k
        exact k
  · refine seamLink C D all (X × Rec) _ _ _ _ _ F.Cl W TF TJ T3 _ _ tF tJ t3 (atDesc F T) Q okF okJ
      ok3 h₁ h₂ h₃ N _ _ _ _ hF hkk hG.glue₂
      ⟨fun k => gh (k.1, k.2, fun _ _ => none), fun a => ?_⟩ ⟨fun _ _ => (), fun _ _ => rfl⟩
    rw [hgh]
    refine congrArg gh ?_
    show (F.start₂ a.1.1, a.2.1,
      fun j x => if D.t₁ ≤ j ∧ j < (atDesc F T).p₂.base then _ else none) = _
    refine congrArg (fun f => (F.start₂ a.1.1, a.2.1, f)) (funext fun j => funext fun x => ?_)
    rw [if_neg]
    rw [hF.base₂]
    omega
  · exact LinkJ.ofLocal (allKind_const (fun _ => rfl) _) N
      (file_know₃ tF tJ t3 (atDesc F T) Q okF okJ ok3 h₁ h₂ h₃ hF g₃ hG.ends) (fun _ => ())
      (fun _ _ _ _ => rfl)

end VerifiableInference.Desc.Sound

#print axioms Iop.jWithin_both
#print axioms Iop.knowB_of_lost_both
#print axioms VerifiableInference.Desc.Sound.paidBoth
#print axioms VerifiableInference.Desc.Sound.lostBothOfLostBy
#print axioms VerifiableInference.Desc.Sound.lostBothOfOwn
#print axioms VerifiableInference.Desc.Sound.lostBothBeside
#print axioms VerifiableInference.Desc.Sound.chainLinkBoth
#print axioms VerifiableInference.Desc.Sound.foldSlots
