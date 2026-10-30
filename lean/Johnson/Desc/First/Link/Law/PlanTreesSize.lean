-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/PlanTreesSize.lean: IN WHAT EACH OF THE THREE ROUTINES THAT LAY OUT A
SUB-PROOF's ARRAYS RETURNS (`Layer.planG`, `Attention.Seam.plan`, `Head.planH2`) THE LEDGER `Fp`
HAS AS MANY ARRAYS AS THE LIST `Tp` HAS ENTRIES: a law of these routines' own text. Six theorems.
The cuts of the three routines are those of OnBytes/Tie/Pv/Lookup/Ends/FoPlanSize.lean, line by
line, with one hypothesis kept that is thrown away there. No text already in the library turns.
Why. All three routines end their list with `let Tp ← t2Plan Fp Tp` (OnBytes/Model/LayerPlan.lean,
AttentionPlan.lean, HeadPlan.lean), and `t2Plan F T` returns only where `t2Open F T` holds, whose
last clause is `F.trees.size == T.nt.size` (OnBytes/Model/Trees.lean).
  `t2Plan_size`: **`t2Plan F T = .ok T'` gives `F.trees.size = T'.nt.size`.** `trimL_size`:
  `Fork.trimL` keeps the number of arrays (the layers' routine returns `Fp.trimL`; the public
  parameters hold the head's ledger so too).
  `planG_trees`, `seamPlan_trees`, `planH2_trees`: at the three routines' returns.
  `public_trees`: **so at every member of X.G, at every member of X.A's seam, and at X.H, where
  `Verify.publicOf` returns X.** By `Fo.Pub.public_G`, `Fo.Pub.public_H`,
  `Fo.PubA.public_A_seam`.
Limits. A number alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoPlanSize
import OnBytes.Tie.Pv.Lookup.Ends.FoPublic
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicAPlFor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open Fo (pureE_ok)
open Fo.BatRows (bindE_ok ite_ok)

/-- **The three routines' last test on their list.** -/
theorem t2Plan_size {F : Fork} {T T' : Tail2} (h : t2Plan F T = .ok T') :
    F.trees.size = T'.nt.size := by
  unfold t2Plan at h
  split at h
  · cases h
  · rename_i hn
    obtain rfl := Except.ok.inj h
    have ho : t2Open F T = true := by simpa using hn
    unfold t2Open at ho
    simp only [Bool.and_eq_true, beq_iff_eq] at ho
    exact ho.2

theorem trimL_size (F : Fork) : F.trimL.trees.size = F.trees.size := by
  show (F.trees.map _).size = _
  rw [Array.size_map]

theorem planG_trees (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : hp.Fp.trees.size = hp.Tp.nt.size := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, _, h⟩ := bindE_ok h
  obtain ⟨tl, _, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, _, h⟩ := bindE_ok h
  obtain ⟨Tp1, hT, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have k : Fp.trimL.trees.size = Tp1.nt.size := (trimL_size Fp).trans (t2Plan_size hT)
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨y, _, h⟩ := bindE_ok h
    obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    exact k
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      exact k
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

set_option hygiene false in
/-- Closes a goal whose hypothesis e says that a routine which throws has returned. -/
local macro "dead" : tactic => `(tactic| first
  | (obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done)
  | (obtain ⟨_, _, e⟩ := bindE_ok e; obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done))

set_option hygiene false in
/-- Takes the branch of a test in which nothing is thrown. -/
local macro "alive" : tactic => `(tactic|
  (rcases ite_ok e with ⟨_, e⟩ | ⟨_, e⟩; (· dead); obtain ⟨_, _, e⟩ := bindE_ok e))

theorem seamPlan_trees {s s' : Attention.Seam} {nU3 hb hbLine : Nat}
    (e : s.plan nU3 hb hbLine = .ok s') : s'.Fp.trees.size = s'.Tp.nt.size := by
  unfold Attention.Seam.plan at e
  dsimp only at e
  obtain ⟨⟨tl, Fp, T⟩, _, e⟩ := bindE_ok e
  alive
  obtain ⟨Tp, hT, e⟩ := bindE_ok e
  cases e
  exact t2Plan_size hT

theorem planH2_trees (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) : hp.Fp.trees.size = hp.Tp.nt.size := by
  unfold Head.planH2 at e
  repeat obtain ⟨_, _, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨⟨tl1, Fp, Tp⟩, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨Tp1, hT, e⟩ := bindE_ok e
    obtain ⟨tl2, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    cases e
    exact t2Plan_size hT
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

/-- **At the public parameters.** -/
theorem public_trees {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) :
    (∀ (g : Nat) (hp : Layer.HPlan2), X.G[g]? = some hp → hp.Fp.trees.size = hp.Tp.nt.size) ∧
      (∀ (g : Nat) (a : Attention.Plan), X.A[g]? = some a →
        a.seam.Fp.trees.size = a.seam.Tp.nt.size) ∧
      X.H.Fp.trees.size = X.H.Tp.nt.size := by
  refine ⟨fun g hp hg => planG_trees _ _ _ hp (Fo.Pub.public_G h g hp hg), fun g a hg => ?_, ?_⟩
  · obtain ⟨seam0, s1, h1, e⟩ := Fo.PubA.public_A_seam h g a hg
    have k : s1.Fp.trees.size = s1.Tp.nt.size := seamPlan_trees h1
    rw [e]
    exact k
  · obtain ⟨H0, h1, e⟩ := Fo.Pub.public_H h
    have k : H0.Fp.trimL.trees.size = H0.Tp.nt.size :=
      (trimL_size H0.Fp).trans (planH2_trees _ _ _ _ _ _ _ H0 h1)
    rw [e]
    exact k

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.t2Plan_size
#print axioms VerifiableInference.Desc.LinkJoin.trimL_size
#print axioms VerifiableInference.Desc.LinkJoin.planG_trees
#print axioms VerifiableInference.Desc.LinkJoin.seamPlan_trees
#print axioms VerifiableInference.Desc.LinkJoin.planH2_trees
#print axioms VerifiableInference.Desc.LinkJoin.public_trees
