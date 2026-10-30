-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SharedRuleProofs.lean: proofs of eleven of the fourteen statements of
Johnson/Desc/Sound/SharedRule.lean. Six outright: `RowLink`, `AdmBack`, `PaidOnce`, `HeadOfActs`,
`LostOfGoodIn`, `LostBeside`. FIVE UNDER A HYPOTHESIS: `ChainLink` and `SlotOne` under `FoldIsRow`;
`ChainLinkAt` and `ChainLinkBack` under `ChainLink`; `ChainLinkActs` under `ChainLinkBack`: these
five are closed in Johnson/Desc/Sound/SharedRuleClosed.lean. The other three are proved elsewhere:
`FoldLift` in FoldLiftProof.lean, `LiftHands` and `ChainLinkOwn` in SharedOwnProofs.lean.

Limits: those of Johnson/Desc/Sound/SharedRule.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.SharedRule
import OnBytes.TypedOracleCompiler.Joined.LinkJKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open TypedOracleCompiler.Joined (LinkJ shA)
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString BTr Doomed)

theorem rowLink : RowLink := by
  intro S Cl W C F N on R d i p l
  induction l generalizing p i with
  | nil =>
    intro kA kZ h
    exact h
  | cons q l ih =>
    intro kA kZ h
    obtain ⟨kB, h1, h2⟩ : ∃ kB : BKey F S,
      (p.bk (on i) (on (i + 1)) (R i) (R (i + 1))).LinkSh N (kkAt kA) (kkAt kB) ∧
        Keyed N on R (i + 1) q l kB kZ := h
    have k := BK.linkSh_seq (p.bk (on i) (on (i + 1)) (R i) (R (i + 1))) _ d h1
      (ih (i + 1) q kB kZ h2)
    have e : i + 1 + 1 + l.length = i + 1 + (q :: l).length := by
      simp only [List.length_cons]
      omega
    rw [e] at k
    exact k

theorem chainLink_of (hf : FoldIsRow) : ChainLink := by
  intro S Cl W C F name N on R d p l h kA kZ ht hk
  have k := (rowLink S Cl W C F N on R d 0 p l kA kZ hk).linkJ
  rw [Nat.zero_add] at k
  have e : ∀ a τ, (foldRed name ((p :: l).map (·.b)) p l h).out a τ = (rowIOR p l).red.out a τ :=
    hf S Cl W C F name p l h ht
  obtain ⟨⟨bad, c, J⟩, adm⟩ := k
  refine ⟨⟨bad, fun a τ b w ha hτ hb hw => c a τ b w ha hτ ((e a τ).symm.trans hb) hw, J⟩,
    fun a ha τ => ?_⟩
  refine cast (congrArg (IOR.SameKey kZ.2) (funext fun j => ?_)) (adm a ha τ)
  exact congrArg (a j).bind (funext fun aj => (e aj _).symm)

theorem chainLinkAt_of (hc : ChainLink) : ChainLinkAt := by
  intro S Cl W C F name N on R d c p l h kA kZ e ht hk
  rw [← e]
  exact hc S Cl W C F name N on R d p l h kA kZ ht hk

theorem slotOne_of (hf : FoldIsRow) : SlotOne := by
  intro S Cl W C F name N on R d p l h kA kZ hN ht hk
  have k := (rowLink S Cl W C F N on R d 0 p l kA kZ hk).know
  rw [Nat.zero_add] at k
  have k1 := Iop.know_of_knowB _ _ _ _ _ _ (rowIOR p l) _ N _ _ _ _ _ _ ⟨0, hN⟩ k
    (fun a _ j j' aj aj' hj hj' => by
      unfold IOR.alone at hj hj'
      split at hj <;> split at hj' <;> simp_all)
  intro a ha
  refine Doomed.mono _ _ ?_ (k1 a ha)
  intro τ hτ b w hb hw
  exact hτ b w ((hf S Cl W C F name p l h ht a τ).symm.trans hb) hw

theorem admBack : AdmBack := by
  intro S Cl W C F p act kB N a ha τ j j' b b' hb hb'
  obtain ⟨aj, haj, hbj⟩ := Option.bind_eq_some_iff.mp hb
  obtain ⟨aj', haj', hbj'⟩ := Option.bind_eq_some_iff.mp hb'
  have e2 : (p.ior.red.out aj (τ.slot j')).map kB.2 = (p.ior.red.out aj' (τ.slot j')).map kB.2 :=
    congrFun (congrArg Prod.snd (ha j j' aj aj' haj haj')) (τ.slot j')
  rw [Iop.slot_shared N p.ior.shape τ j j'] at hbj
  rw [hbj, hbj'] at e2
  exact Option.some.inj e2

theorem paidOnce : PaidOnce := by
  rintro S Cl W C F p on on' R R' act kB N ⟨lost, hD, hb⟩
  refine ⟨?_, admBack S Cl W C F p act kB N⟩
  have k := Iop.knowB_of_lost S S act.1 F.E F.E W W p.ior N act.2 lost on R
    (Reduction.orOff on' R') p.ext p.err hD
    (fun a τ b w ha hl ho hw =>
      (hb a τ b ha hl ho).2 w (hw.elim id fun n => absurd (hb a τ b ha hl ho).1 n))
  exact Iop.knowB_conseq _ _ _ _ _ _ p.ior _ N _ _ _ _ _ _ _ _ _ _ k
    (fun a ha j j' aj aj' hj hj' => congrArg Prod.fst (ha j j' aj aj' hj hj')) (fun _ h => h)
    (fun _ _ _ h => h) (fun _ _ h => h)

theorem keyed_back {S Cl W : Type} {C : CK} {F : Frame} (N : ℕ) (on : ℕ → S × F.E.Str → Prop)
    (R : ℕ → S × F.E.Str → W → Prop) (act : ℕ → BKey F S) (kZ : BKey F S) :
    ∀ (l : List (Piece C F S Cl W)) (p : Piece C F S Cl W) (i : ℕ),
      EachLost on R act i (p :: l) → Keyed N on R i p l (keysBack act kZ i (p :: l)) kZ
  | [], p, i, h => paidOnce S Cl W C F p _ _ _ _ (act i) kZ N h.1
  | q :: l, p, i, h =>
    ⟨keysBack act kZ (i + 1) (q :: l), paidOnce S Cl W C F p _ _ _ _ (act i) _ N h.1,
      keyed_back N on R act kZ l q (i + 1) h.2⟩

theorem chainLinkBack_of (hc : ChainLink) : ChainLinkBack := by
  intro S Cl W C F name N on R d p l h act kZ ht hl
  exact hc S Cl W C F name N on R d p l h _ kZ ht (keyed_back N on R act kZ l p 0 hl)

theorem headOfActs : HeadOfActs := by
  intro S Cl W C F act i l
  induction l generalizing i with
  | nil =>
    intro _
    exact ⟨fun x => x, fun _ => rfl⟩
  | cons p l ih =>
    intro h
    have e : i + (p :: l).length = i + 1 + l.length := by
      simp only [List.length_cons]
      omega
    rw [e]
    obtain ⟨G, hG⟩ := h.1
    obtain ⟨g', hg'⟩ := ih (i + 1) h.2
    refine ⟨fun k => (k, fun τ => (G k τ).map g'), fun a => ?_⟩
    show ((act i).2 a, fun τ => (p.ior.red.out a τ).map
      (keysBack act (act (i + 1 + l.length)) (i + 1) l).2) = _
    refine congrArg (Prod.mk ((act i).2 a)) (funext fun τ => ?_)
    rw [← hG a τ]
    generalize p.ior.red.out a τ = o
    cases o with
    | none => rfl
    | some b => exact congrArg some (hg' b)

theorem chainLinkActs_of (hb : ChainLinkBack) : ChainLinkActs := by
  intro S Cl W C F name N on R d p l h act ht hl hh
  have k := hb S Cl W C F name N on R d p l h act (act (1 + l.length)) ht hl
  have hd := headOfActs S Cl W C F act 0 (p :: l) hh
  have e : 0 + (p :: l).length = 1 + l.length := by
    simp only [List.length_cons]
    omega
  rw [e] at hd
  obtain ⟨g, hg⟩ := hd
  exact k.conseq (act 0).2 g hg id (fun _ h => h) (fun _ _ _ h => h) (fun _ _ h => h)

theorem lostOfGoodIn : LostOfGoodIn := by
  intro S Cl W C F p on on' R R' act act' hG hR
  obtain ⟨G, hGa⟩ := hR.hands
  refine ⟨fun k τ => ∀ a, on a → act.2 a = k → ∀ b, p.ior.red.out a τ = some b →
    on' b ∧ ∀ w, R' b w → R a (p.ext a τ w), fun a ha => ?_,
    fun a τ b ha hl hb => hl a ha rfl b hb⟩
  refine Doomed.mono _ _ ?_ (hG a ha)
  intro τ hτ a' ha' e b' hb'
  have h1 : (p.ior.red.out a τ).map act'.2 = some (act'.2 b') := by
    rw [hGa a τ, ← e, ← hGa a' τ, hb']
    rfl
  obtain ⟨b, hb, hbb⟩ := Option.map_eq_some_iff.mp h1
  obtain ⟨ho, hk⟩ := hτ b hb
  refine ⟨hR.rels.cond b b' hbb ho, fun w hw => ?_⟩
  rw [hR.rels.ext a' a τ w e]
  exact hR.rels.front a a' _ e.symm (hk w (hR.rels.behind b' b w hbb.symm hw))

theorem lostBeside : LostBeside := by
  rintro S Cl W C F p on on' R R' Rc act ⟨lost, hD, hb⟩ hc
  refine ⟨lost, hD, fun a τ b ha hl ho => ?_⟩
  obtain ⟨h1, h2⟩ := hb a τ b ha hl ho
  exact ⟨h1, fun w hw => ⟨h2 w hw.1, hc a τ b w ha ho h1 hw.2⟩⟩

end VerifiableInference.Desc.Sound
