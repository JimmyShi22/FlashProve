-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/PlanBare.lean: IN THE PLAN OF EVERY SUB-PROOF EACH VIRTUAL ROW OF EACH ARRAY IS THE EMPTY ROW:
no weight, no product form, no list of factors: from the return of `Verify.publicOf` alone, by the planners' own text.

  `Bare F`        every virtual row of every array of the ledger is the empty row
  `addN_bare`, `addP_bare`, **`addTreesF_bare`**   the making of the list of arrays, from the empty ledger
  `bare_trimL`    striking the weights on the columns keeps it
  `planG_bare`, `seamPlan_bare`, `planA_bare`, `planH2_bare`   at the three planners' returns
  **`public_bare`**   at the public parameters' own members

How. As Honest/K9/PlanFresh.lean: the cuts of the routines' texts are the library's: `addTreesF_walk`
(Johnson/Desc/Kinds/Law/AddTreesLooks.lean) and the theorems `planG_two` to `public_A_two`
(Johnson/Desc/First/Link/Law/StaticOfMade.lean).

Limits. Nothing on the arrays' sizes. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.PlanFresh

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open _root_.Fo (SameP SameRec pureE_ok)
open _root_.Fo.BatRows _root_.Fo.Pub _root_.Fo.ZPlan
open OnBytes.Road (ok_of_bind ok_of_jp forIn_keeps)

/-- Every virtual row of every array of the ledger is the empty row. -/
def Bare (F : Fork) : Prop := ∀ X ∈ F.trees, ∀ r ∈ X.rows, r = ({} : HRow)

theorem bare_empty : Bare ({} : Fork) := fun X hX => absurd hX (by simp)

theorem bare_push {F : Fork} (h : Bare F) (Y : HTree) (hY : ∀ r ∈ Y.rows, r = ({} : HRow)) :
    Bare { F with trees := F.trees.push Y } := by
  intro X hX
  have hX' : X ∈ F.trees.push Y := hX
  rcases Array.mem_push.1 hX' with k | rfl
  · exact h X k
  · exact hY

theorem addN_bare {F : Fork} {T : Tail2} {name : String} {R K ec a : Nat} {foreign : Bool}
    {nv got : Nat} {F' : Fork} {T' : Tail2}
    (h : t2AddN F T name R K ec a foreign nv = .ok (got, F', T')) (g : Bare F) : Bare F' := by
  unfold t2AddN at h
  split at h
  · cases h
  · have e := Except.ok.inj h
    obtain ⟨_, e2⟩ := Prod.mk.inj e
    obtain ⟨e3, _⟩ := Prod.mk.inj e2
    rw [← e3]
    exact bare_push g _ fun r hr => (Array.mem_replicate.1 hr).2

theorem addP_bare {F : Fork} {T : Tail2} {name : String} {m k w a : Nat} {foreign : Bool}
    {got : Nat} {F' : Fork} {T' : Tail2}
    (h : t2AddP F T name m k w a foreign = .ok (got, F', T')) (g : Bare F) : Bare F' := by
  unfold t2AddP at h
  split at h
  · cases h
  · split at h
    · cases h
    · have e := Except.ok.inj h
      obtain ⟨_, e2⟩ := Prod.mk.inj e
      obtain ⟨e3, _⟩ := Prod.mk.inj e2
      rw [← e3]
      exact bare_push g _ fun r hr => (Array.mem_replicate.1 hr).2

/-- **The making of the list of arrays, from the empty ledger.** -/
theorem addTreesF_bare {tl tl' : HTailF2} {G : Fork} {T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF {} {} nU aTX hb hbLine = .ok (tl', G, T')) : Bare G := by
  unfold addTreesF at h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨⟨F1, T1⟩, h1, h⟩ := ok_of_bind h
  obtain ⟨⟨F2, T2⟩, h2, h⟩ := ok_of_bind h
  obtain ⟨⟨F3, T3⟩, h3, h⟩ := ok_of_bind h
  obtain ⟨⟨gotZ, FZ, TZ⟩, hZ, h⟩ := ok_of_bind h
  obtain ⟨nZ, h⟩ := ok_of_jp h
  obtain ⟨⟨gotB, FB, TB⟩, hB, h⟩ := ok_of_bind h
  obtain ⟨nB, h⟩ := ok_of_jp h
  obtain ⟨⟨F4, T4⟩, h4, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  have e := Except.ok.inj h
  obtain ⟨-, e2⟩ := Prod.mk.inj e
  obtain ⟨e3, -⟩ := Prod.mk.inj e2
  have K1 : Bare F1 := forIn_keeps _ (List.range 3)
    (fun _ (s : MProd Fork Tail2) => Bare s.1)
    (fun pre a rest hl s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      dsimp only at hs
      split at hs
      · obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
        obtain ⟨ne, hs⟩ := ok_of_jp hs
        exact ⟨_, (Except.ok.inj hs).symm, addN_bare hP hI⟩
      · exact ⟨_, (Except.ok.inj hs).symm, hI⟩)
    (List.range 3) [] _ _ rfl bare_empty h1
  have K2 : Bare F2 := forIn_keeps _ (List.range tl.pkMat.size)
    (fun _ (s : MProd Fork Tail2) => Bare s.1)
    (fun _ a _ _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨ne, hs⟩ := ok_of_jp hs
      exact ⟨_, (Except.ok.inj hs).symm, addP_bare hP hI⟩)
    (List.range tl.pkMat.size) [] _ _ rfl K1 h2
  have K3 : Bare F3 := forIn_keeps _ (List.range tl.pxMat.size)
    (fun _ (s : MProd Fork Tail2) => Bare s.1)
    (fun _ a _ _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨ne, hs⟩ := ok_of_jp hs
      exact ⟨_, (Except.ok.inj hs).symm, addP_bare hP hI⟩)
    (List.range tl.pxMat.size) [] _ _ rfl K2 h3
  have KB : Bare FB := addN_bare hB (addN_bare hZ K3)
  have K4 : Bare F4 := forIn_keeps _ (List.range tl.ft.size)
    (fun _ (s : MProd Fork Tail2) => Bare s.1)
    (fun _ a _ _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨ne, hs⟩ := ok_of_jp hs
      exact ⟨_, (Except.ok.inj hs).symm, addP_bare hP hI⟩)
    (List.range tl.ft.size) [] _ _ rfl KB h4
  rw [← e3]
  exact K4

/-- Striking the weights on the columns. -/
theorem bare_trimL {F : Fork} (h : Bare F) : Bare F.trimL := by
  intro X hX r hr
  have hX' : X ∈ F.trees.map fun X => { X with rows := X.rows.map fun r => { r with L := #[] } } := hX
  obtain ⟨X0, h0, rfl⟩ := Array.mem_map.1 hX'
  obtain ⟨r0, h1, rfl⟩ := Array.mem_map.1 hr
  rw [h X0 h0 r0 h1]

/-! ## The three planners -/

theorem planG_bare (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : Bare hp.Fp := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, _, h⟩ := bindE_ok h
  obtain ⟨tl, hS, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, hA, h⟩ := bindE_ok h
  obtain ⟨Tp1, hT, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have hP : Bare Fp.trimL := bare_trimL (addTreesF_bare hA)
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨y, hy, h⟩ := bindE_ok h
    obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    exact hP
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      exact hP
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

theorem seamPlan_bare {s s' : Attention.Seam} {nU3 hb hbLine : Nat}
    (e : s.plan nU3 hb hbLine = .ok s') : Bare s'.Fp := by
  unfold Attention.Seam.plan at e
  dsimp only at e
  obtain ⟨⟨tl, Fp, T⟩, hr, e⟩ := bindE_ok e
  rcases ite_ok e with ⟨_, e⟩ | ⟨_, e⟩
  · obtain ⟨_, e1, _⟩ := bindE_ok e
    cases e1
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨Tp, hT, e⟩ := bindE_ok e
    cases e
    exact addTreesF_bare hr

theorem planA_bare (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (e : Attention.plan settings i cf = .ok P) : Bare P.seam.Fp := by
  obtain ⟨seam0, h0, h1, -⟩ := planA_rows0 settings i cf P e
  exact seamPlan_bare h1

theorem planH2_bare (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) : Bare hp.Fp := by
  unfold Head.planH2 at e
  repeat obtain ⟨_, _, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl, hS, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨⟨tl1, Fp, Tp⟩, hA, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨Tp1, hT, e⟩ := bindE_ok e
    obtain ⟨tl2, hO, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    cases e
    exact addTreesF_bare hA
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

/-- **At the public parameters.** -/
theorem public_bare {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) :
    (∀ (g : Nat) (hp : Layer.HPlan2), X.G[g]? = some hp → Bare hp.Fp) ∧
      (∀ (g : Nat) (a : Attention.Plan), X.A[g]? = some a → Bare a.seam.Fp) ∧ Bare X.H.Fp := by
  refine ⟨fun g hp hg => planG_bare X.layers g _ hp (public_G h g hp hg), fun g a hg => ?_, ?_⟩
  · obtain ⟨_, _, _, _, _, sc, A0, seen, k2, k3, k6, k7⟩ := publicOf_cut pol KL layout X h
    rw [k7] at hg
    have hz : ∃ a0 s, A0[g]? = some a0 ∧ seen[g]? = some s ∧
        a = { a0 with seam := { a0.seam with tl := s.tl } } := by
      rw [← Array.getElem?_toList, Array.toList_zipWith] at hg
      obtain ⟨a0, s, e1, e2, e3⟩ := List.getElem?_zipWith_eq_some.1 hg
      exact ⟨a0, s, by simpa using e1, by simpa using e2, e3.symm⟩
    obtain ⟨a0, s, e1, e2, e3⟩ := hz
    rcases k3 with ⟨_, c, k9, rfl⟩ | ⟨_, rfl⟩
    · obtain ⟨lines, l1, l2⟩ := config_at k9
      obtain ⟨cf, m1, m2⟩ := group_plan (l2 g a0 e1)
      subst e3
      exact planA_bare _ _ _ a0 m2
    · simp at e1
  · obtain ⟨H0, h0, e⟩ := public_H h
    have k : Bare H0.Fp.trimL := bare_trimL (planH2_bare _ _ _ _ _ _ _ H0 h0)
    rw [e]
    exact k

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.bare_empty
#print axioms VerifiableInference.Desc.LinkJoin.bare_push
#print axioms VerifiableInference.Desc.LinkJoin.addN_bare
#print axioms VerifiableInference.Desc.LinkJoin.addP_bare
#print axioms VerifiableInference.Desc.LinkJoin.addTreesF_bare
#print axioms VerifiableInference.Desc.LinkJoin.bare_trimL
#print axioms VerifiableInference.Desc.LinkJoin.planG_bare
#print axioms VerifiableInference.Desc.LinkJoin.seamPlan_bare
#print axioms VerifiableInference.Desc.LinkJoin.planA_bare
#print axioms VerifiableInference.Desc.LinkJoin.planH2_bare
#print axioms VerifiableInference.Desc.LinkJoin.public_bare
