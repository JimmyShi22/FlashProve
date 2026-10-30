-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/PlanFresh.lean: THE PLAN OF EVERY SUB-PROOF HANDS THE VERIFIER A CLOSED LIST OF ARRAYS AND A
LEDGER TO WHICH NOTHING HAS HAPPENED: from the return of `Verify.publicOf` alone, by the planners' own text. What it is for: a
segment's opening lays the plan's list as the segment's list, and makes the segment's ledger out of the plan's (`startFork`,
Johnson/Desc/First/Walk/FirstQuiet.lean), which keeps four of its fields as the plan has them.

  `Plain F`       of a ledger: the batching element is not drawn, no claim is counted, the one equation has not been made, and
                  the constant is 0: as in the empty ledger
  `Closed T`      of a list of arrays: it is a segment's list, and it is closed
  `addN_plain`, `addP_plain`, **`addTreesF_plain`**   adding arrays to the list turns none of the four
  `t2Plan_closed`   the closing of the list gives `Closed`
  `planG_fresh`, `seamPlan_fresh`, `planA_fresh`, `planH2_closed`   at the three planners' returns
  **`public_G_fresh`**, **`public_A_fresh`**, **`public_H_closed`**   at the public parameters' own members

How. The cuts of the routines' texts are the library's: `addTreesF_walk` (Johnson/Desc/Kinds/Law/AddTreesLooks.lean) and the
theorems `planG_two` to `public_A_two` (Johnson/Desc/First/Link/Law/StaticOfMade.lean), with these two sentences in the place of
theirs.

Limits. At the head's plan the ledger is not treated: the head's opening makes its ledger of the plan's arrays alone. Nothing on
what the plans' numbers are. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.First.Link.Law.StaticOfMade
import Johnson.Desc.Kinds.Law.AddTreesLooks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open _root_.Fo (SameP SameRec pureE_ok)
open _root_.Fo.BatRows _root_.Fo.Pub _root_.Fo.ZPlan
open OnBytes.Road (ok_of_bind ok_of_jp forIn_keeps)

/-- Of a ledger: four fields are as in the empty ledger. -/
structure Plain (F : Fork) : Prop where
  drawn : F.thetaDrawnF = false
  count : F.nClaim = 0
  door : F.doorShutF = false
  const : F.c0 = zeroE

/-- Of a list of arrays: it is a segment's list, and it is closed. -/
structure Closed (T : Tail2) : Prop where
  link : T.link = true
  planned : T.planned = true

theorem plain_empty : Plain ({} : Fork) := ⟨rfl, rfl, rfl, rfl⟩

theorem plain_trees {F : Fork} (h : Plain F) (tr : Array HTree) : Plain { F with trees := tr } :=
  ⟨h.drawn, h.count, h.door, h.const⟩

theorem addN_plain {F : Fork} {T : Tail2} {name : String} {R K ec a : Nat} {foreign : Bool}
    {nv got : Nat} {F' : Fork} {T' : Tail2}
    (h : t2AddN F T name R K ec a foreign nv = .ok (got, F', T')) (g : Plain F) : Plain F' := by
  unfold t2AddN at h
  split at h
  · cases h
  · have e := Except.ok.inj h
    obtain ⟨_, e2⟩ := Prod.mk.inj e
    obtain ⟨e3, _⟩ := Prod.mk.inj e2
    rw [← e3]
    exact plain_trees g _

theorem addP_plain {F : Fork} {T : Tail2} {name : String} {m k w a : Nat} {foreign : Bool}
    {got : Nat} {F' : Fork} {T' : Tail2}
    (h : t2AddP F T name m k w a foreign = .ok (got, F', T')) (g : Plain F) : Plain F' := by
  unfold t2AddP at h
  split at h
  · cases h
  · split at h
    · cases h
    · have e := Except.ok.inj h
      obtain ⟨_, e2⟩ := Prod.mk.inj e
      obtain ⟨e3, _⟩ := Prod.mk.inj e2
      rw [← e3]
      exact plain_trees g _

/-- **The making of the list of arrays, from the empty ledger.** -/
theorem addTreesF_plain {tl tl' : HTailF2} {G : Fork} {T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF {} {} nU aTX hb hbLine = .ok (tl', G, T')) : Plain G := by
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
  have K1 : Plain F1 := forIn_keeps _ (List.range 3)
    (fun _ (s : MProd Fork Tail2) => Plain s.1)
    (fun pre a rest hl s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      dsimp only at hs
      split at hs
      · obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
        obtain ⟨ne, hs⟩ := ok_of_jp hs
        exact ⟨_, (Except.ok.inj hs).symm, addN_plain hP hI⟩
      · exact ⟨_, (Except.ok.inj hs).symm, hI⟩)
    (List.range 3) [] _ _ rfl plain_empty h1
  have K2 : Plain F2 := forIn_keeps _ (List.range tl.pkMat.size)
    (fun _ (s : MProd Fork Tail2) => Plain s.1)
    (fun _ a _ _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨ne, hs⟩ := ok_of_jp hs
      exact ⟨_, (Except.ok.inj hs).symm, addP_plain hP hI⟩)
    (List.range tl.pkMat.size) [] _ _ rfl K1 h2
  have K3 : Plain F3 := forIn_keeps _ (List.range tl.pxMat.size)
    (fun _ (s : MProd Fork Tail2) => Plain s.1)
    (fun _ a _ _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨ne, hs⟩ := ok_of_jp hs
      exact ⟨_, (Except.ok.inj hs).symm, addP_plain hP hI⟩)
    (List.range tl.pxMat.size) [] _ _ rfl K2 h3
  have KB : Plain FB := addN_plain hB (addN_plain hZ K3)
  have K4 : Plain F4 := forIn_keeps _ (List.range tl.ft.size)
    (fun _ (s : MProd Fork Tail2) => Plain s.1)
    (fun _ a _ _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨ne, hs⟩ := ok_of_jp hs
      exact ⟨_, (Except.ok.inj hs).symm, addP_plain hP hI⟩)
    (List.range tl.ft.size) [] _ _ rfl KB h4
  rw [← e3]
  exact K4

/-- The closing of the list. -/
theorem t2Plan_closed {F : Fork} {T T' : Tail2} (h : t2Plan F T = .ok T') : Closed T' := by
  unfold t2Plan at h
  split at h
  · cases h
  · rename_i ho
    have e := Except.ok.inj h
    have ho' : t2Open F T = true := by simpa using ho
    unfold t2Open at ho'
    simp only [Bool.and_eq_true] at ho'
    rw [← e]
    exact ⟨ho'.1.1, rfl⟩

/-! ## The three planners -/

theorem planG_fresh (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : Closed hp.Tp ∧ Plain hp.Fp := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, _, h⟩ := bindE_ok h
  obtain ⟨tl, hS, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, hA, h⟩ := bindE_ok h
  obtain ⟨Tp1, hT, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have hP : Plain Fp.trimL := plain_trees (addTreesF_plain hA) _
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨y, hy, h⟩ := bindE_ok h
    obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    exact ⟨t2Plan_closed hT, hP⟩
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      exact ⟨t2Plan_closed hT, hP⟩
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

theorem seamPlan_fresh {s s' : Attention.Seam} {nU3 hb hbLine : Nat}
    (e : s.plan nU3 hb hbLine = .ok s') : Closed s'.Tp ∧ Plain s'.Fp := by
  unfold Attention.Seam.plan at e
  dsimp only at e
  obtain ⟨⟨tl, Fp, T⟩, hr, e⟩ := bindE_ok e
  rcases ite_ok e with ⟨_, e⟩ | ⟨_, e⟩
  · obtain ⟨_, e1, _⟩ := bindE_ok e
    cases e1
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨Tp, hT, e⟩ := bindE_ok e
    cases e
    exact ⟨t2Plan_closed hT, addTreesF_plain hr⟩

theorem planA_fresh (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (e : Attention.plan settings i cf = .ok P) :
    Closed P.seam.Tp ∧ Plain P.seam.Fp := by
  obtain ⟨seam0, h0, h1, -⟩ := planA_rows0 settings i cf P e
  exact seamPlan_fresh h1

theorem planH2_closed (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) : Closed hp.Tp := by
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
    exact t2Plan_closed hT
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

/-! ## The public parameters -/

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

theorem public_G_fresh (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) : Closed hp.Tp ∧ Plain hp.Fp :=
  planG_fresh X.layers g _ hp (public_G h g hp hg)

theorem public_H_closed (h : Verify.publicOf pol KL layout = .ok X) : Closed X.H.Tp := by
  obtain ⟨H0, h0, e⟩ := public_H h
  have k : Closed H0.Tp := planH2_closed _ _ _ _ _ _ _ H0 h0
  rw [e]
  exact k

theorem public_A_fresh (h : Verify.publicOf pol KL layout = .ok X) (g : Nat)
    (a : Attention.Plan) (hg : X.A[g]? = some a) : Closed a.seam.Tp ∧ Plain a.seam.Fp := by
  obtain ⟨_, _, _, _, _, sc, A0, seen, k2, k3, k6, k7⟩ := publicOf_cut pol KL layout X h
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
    exact planA_fresh _ _ _ a0 m2
  · simp at e1

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.plain_empty
#print axioms VerifiableInference.Desc.LinkJoin.plain_trees
#print axioms VerifiableInference.Desc.LinkJoin.addN_plain
#print axioms VerifiableInference.Desc.LinkJoin.addP_plain
#print axioms VerifiableInference.Desc.LinkJoin.addTreesF_plain
#print axioms VerifiableInference.Desc.LinkJoin.t2Plan_closed
#print axioms VerifiableInference.Desc.LinkJoin.planG_fresh
#print axioms VerifiableInference.Desc.LinkJoin.seamPlan_fresh
#print axioms VerifiableInference.Desc.LinkJoin.planA_fresh
#print axioms VerifiableInference.Desc.LinkJoin.planH2_closed
#print axioms VerifiableInference.Desc.LinkJoin.public_G_fresh
#print axioms VerifiableInference.Desc.LinkJoin.public_H_closed
#print axioms VerifiableInference.Desc.LinkJoin.public_A_fresh
