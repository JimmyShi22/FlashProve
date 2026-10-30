-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.Plain.KeyAlone
import Johnson.Desc.Sound.PaidAtDesc
/-
Johnson/Desc/K12/Law/HeldKey.lean: A PIECE WHOSE BLOCK IS A HELD BLOCK
(Johnson/Desc/Sound/PaidAtDesc.lean: held: what a description's pieces hold) AND WHOSE DATA OPEN NO
TREE BELOW lo IS KEY-ALONE: liftHands | leadsK_of_lift
(Johnson/Desc/Sound/SharedOwnProofs.lean · Plain/KeyAlone.lean) AT held b = (below b).lift Prod.snd
…: their four premises hb · h1 · h2 · ho come down to two: p.b = held B · ho. AND THE THIRD CLAUSE
THAT THE SHARED CHAIN's RULE ASKS OF EACH PIECE (Plain/FoldChainK.lean: EachLeadsK): KeyLaw, from
HandsAct. GENERAL: no kind is named. NO SOUNDNESS IS
CLAIMED. NOTHING ON HIDING. NO NEW MATHEMATICS.
  hands_of_held        p.HandsAct (actAt F Prod.snd lo p.base) (actAt F Prod.snd lo (p.base +
      p.trees)).
  keyLaw_of_held       p.ior.red.KeyLaw of these two keys. (The two keys have one type; where the
      block refuses, the function hands the key in front back: nothing hangs on that value.)
  leadsK_of_held       Leads at a relation that reads the two keys alone ⇒ LeadsK at the key in
      front.
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open OnBytes.Maker
open _root_.Run.PQ (CK)

variable {P S Cl W : Type} {C : CK} {F : Frame}

theorem hands_of_held (p : Piece C F (P × S) Cl W) (B : Block S Cl) (lo : ℕ)
    (hb : p.b = held (P := P) B) (ho : ∀ d ∈ p.ds, ∀ j ∈ d.opens, lo ≤ j) :
    p.HandsAct (actAt F (Prod.snd : P × S → S) lo p.base)
      (actAt F (Prod.snd : P × S → S) lo (p.base + p.trees)) :=
  liftHands (P × S) S Cl W C F Prod.snd (fun t s => (t.1, s)) (below B) p lo hb
    (fun _ _ => rfl) (fun _ _ _ => rfl) ho

theorem keyLaw_of_held (p : Piece C F (P × S) Cl W) (B : Block S Cl) (lo : ℕ)
    (hb : p.b = held (P := P) B) (ho : ∀ d ∈ p.ds, ∀ j ∈ d.opens, lo ≤ j) :
    p.ior.red.KeyLaw (actAt F (Prod.snd : P × S → S) lo p.base).2
      (actAt F (Prod.snd : P × S → S) lo (p.base + p.trees)).2 := by
  obtain ⟨G, hG⟩ := hands_of_held p B lo hb ho
  refine ⟨fun k τ => (G k τ).getD k, fun a τ b hab => ?_⟩
  have h := hG a τ
  rw [hab] at h
  show _ = (G _ τ).getD _
  rw [← h]
  rfl

theorem leadsK_of_held (p : Piece C F (P × S) Cl W) (B : Block S Cl) (lo : ℕ)
    (hb : p.b = held (P := P) B) (ho : ∀ d ∈ p.ds, ∀ j ∈ d.opens, lo ≤ j)
    (on : (P × S) × F.E.Str → Prop)
    (Q₀ : (actAt F (Prod.snd : P × S → S) lo p.base).1 →
      (actAt F (Prod.snd : P × S → S) lo (p.base + p.trees)).1 → Prop)
    (h : p.ior.red.Leads on
      (fun a b => Q₀ ((actAt F (Prod.snd : P × S → S) lo p.base).2 a)
        ((actAt F (Prod.snd : P × S → S) lo (p.base + p.trees)).2 b)) p.err) :
    p.ior.red.LeadsK (actAt F (Prod.snd : P × S → S) lo p.base).2 on
      (fun a b => Q₀ ((actAt F (Prod.snd : P × S → S) lo p.base).2 a)
        ((actAt F (Prod.snd : P × S → S) lo (p.base + p.trees)).2 b)) p.err :=
  leadsK_of_lift Prod.snd (fun t s => (t.1, s)) (below B) p lo hb (fun _ _ => rfl)
    (fun _ _ _ => rfl) ho on Q₀ h

end H2K.JointK

#print axioms H2K.JointK.hands_of_held
#print axioms H2K.JointK.keyLaw_of_held
#print axioms H2K.JointK.leadsK_of_held
