-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Claims/PlanU3.lean: kind K5: in the ledger that Attention.plan plans, the
array of the vector of reads has one row and just as many columns as the vector has entries; and the
three tables on the lookup's matrix are the last three of that vector.

IS IT EMPTY HERE? Each theorem has one premise, a return (of addTreesF, shapeF, Attention.plan,
tablesP). That any of these returns is not shown in this file or in what it imports.

Main names:
  `U3Is F t n`: in the ledger F array number t is there, with one row, n columns and one virtual
    row.
  `addN_K`: the array that t2AddN (OnBytes/Model/Trees.lean) lays has the number of columns handed
    in.
  `U3Is.keep`: a ledger whose list of arrays begins with F's (Fo.Ext,
    OnBytes/Tie/Pv/Lookup/Ends/FoAddTrees.lean) keeps it.
  `addTreesF_u3all`: behind HTailF2.addTreesF (OnBytes/Model/Tail.lean), where the record names t as
    the array of the third vector: U3Is G t (nU.getD 2 0). The first loop lays the array; every
    later step lengthens the list of arrays and leaves the earlier ones.
  `shapeF_U`: a record that shapeF shapes with the third vector alone names array number 0 for it,
    and none for the other three.
  `plan_U`: so does the plan's record.
  `plan_u3_tree`: **Attention.plan settings j cf = .ok A → A.iU3 = 0 ∧ there is T with
    A.seam.Fp.trees[A.iU3]? = some T, T.R = 1, T.K = A.nW, T.rows.size = 1.**
  `plan_nm`: the plan's record has NAs + 4 matrices.
  `planes_end`: tablesP g mats nW lk p = some t → t.tBit0 + 3 kbA = nW ∧ t.tBit1 + 2 kbA = nW ∧
    t.tPin + kbA = nW. By tablesP_lays (Johnson/Desc/First/Att/Claims/ReadsOfIs.lean).
After: the walk through addTreesF's loops follows a proof of another file
(Johnson/Goal/Meaning/PlanPort.lean: addTreesF_u3, t2AddN_K), which
keeps the number of columns alone; here the rows and the virtual rows are kept too. shapeF_U's walk
is that of shapeF_u (OnBytes/Tie/Pv/Lookup/Ends/FoHasU.lean), which keeps "one of the four is
there". Limits: THE PLANNED LEDGER A.seam.Fp ALONE. That the ledger of a state that a chain reaches
has that array so is not shown here (Johnson/Desc/First/Att/Claims/Widths.lean: the numbers of
columns stay under every verb of the ledger).
Used of OnBytes: the planner's pure functions into Except. No routine that runs in a context is
named.

Nothing is claimed on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoHasU
import Johnson.Road.FormsKeysForest
import Johnson.Road.Lane5AttPlan
import Johnson.Desc.First.Att.Claims.ReadsOfIs

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 Fo Fo.Pub Fo.ZPlan
open OnBytes.Road (ok_of_bind ok_of_jp forIn_keeps)
open Fo.BatRows (bindE_ok ite_ok)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo TablesP LookIn Pts)

/-- In the ledger F array number t is there, with one row, n columns and one virtual row. -/
def U3Is (F : Fork) (t n : ℕ) : Prop :=
  t < F.trees.size ∧ (F.trees.getD t {}).R = 1 ∧ (F.trees.getD t {}).K = n ∧
    (F.trees.getD t {}).rows.size = 1

/-- The array that t2AddN lays has the number of columns handed in. -/
theorem addN_K {F : Fork} {T : Tail2} {name : String} {R K ec a : ℕ} {foreign : Bool}
    {nv got : ℕ} {F' : Fork} {T' : Tail2}
    (h : t2AddN F T name R K ec a foreign nv = .ok (got, F', T')) :
    (F'.trees.getD got {}).K = K := by
  unfold t2AddN at h
  split at h
  · cases h
  · have e := Except.ok.inj h
    obtain ⟨e1, e2⟩ := Prod.mk.inj e
    obtain ⟨e2, _⟩ := Prod.mk.inj e2
    subst e1 e2
    show ((F.trees.push _).getD F.trees.size {}).K = K
    rw [getD_push_last]

/-- A ledger whose list of arrays begins with F's keeps the array. -/
theorem U3Is.keep {F G : Fork} (h : Fo.Ext F G) {t n : ℕ} (k : U3Is F t n) : U3Is G t n := by
  unfold U3Is
  rw [h.2 t k.1]
  exact ⟨Nat.lt_of_lt_of_le k.1 h.1, k.2⟩

/-- **Behind addTreesF the array of the third vector has one row, nU[2] columns and one virtual
row.** -/
theorem addTreesF_u3all {tl tl' : HTailF2} {F G : Fork} {T T' : Tail2} {nU aTX : Array ℕ}
    {hb hbLine : ℕ} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T')) {t : ℕ}
    (hu : tl.ix.U.getD 2 none = some t) : U3Is G t (nU.getD 2 0) := by
  unfold addTreesF at h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨⟨F1, T1⟩, h1, h⟩ := ok_of_bind h
  obtain ⟨⟨F2, T2⟩, h2, h⟩ := ok_of_bind h
  obtain ⟨⟨F3, T3⟩, h3, h⟩ := ok_of_bind h
  obtain ⟨⟨gotZ, FZ, TZ⟩, hZ, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨⟨gotB, FB, TB⟩, hB, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  obtain ⟨⟨F4, T4⟩, h4, h⟩ := ok_of_bind h
  obtain ⟨_, h⟩ := ok_of_jp h
  have e := Except.ok.inj h
  obtain ⟨-, e2⟩ := Prod.mk.inj e
  obtain ⟨e2, -⟩ := Prod.mk.inj e2
  subst e2
  have K1 := forIn_keeps _ (List.range 3)
    (fun pre (s : MProd Fork Tail2) => 2 ∈ pre → U3Is s.1 t (nU.getD 2 0))
    (fun pre a rest _ s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      dsimp only at hs
      split at hs
      · rename_i want hw
        obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
        obtain ⟨hgw, hs⟩ := ok_of_jp hs
        refine ⟨_, (Except.ok.inj hs).symm, fun hm => ?_⟩
        obtain ⟨g1, g2, g3, g4, g5⟩ := t2AddN_ok hP
        rcases List.mem_append.1 hm with hm | hm
        · exact U3Is.keep g2 (hI hm)
        · have ea : a = 2 := (List.mem_singleton.1 hm).symm
          subst ea
          have ew : want = t := Option.some.inj (hw.symm.trans hu)
          have eg : got = t := by
            have : got = want := by simpa using hgw
            rw [this, ew]
          subst eg
          exact ⟨by show got < F'.trees.size; omega, g4, addN_K hP, g5⟩
      · rename_i hw
        refine ⟨_, (Except.ok.inj hs).symm, fun hm => ?_⟩
        rcases List.mem_append.1 hm with hm | hm
        · exact hI hm
        · have ea : a = 2 := (List.mem_singleton.1 hm).symm
          subst ea
          exact absurd hu (hw t))
    (List.range 3) [] _ _ rfl (fun hm => by cases hm) h1
  have k1 := K1 (by decide)
  have addP : ∀ (Fa : Fork) (l : List ℕ) (body : ℕ → MProd Fork Tail2 →
      Except String (ForInStep (MProd Fork Tail2))) (s r : MProd Fork Tail2),
      (∀ a s s', Fo.Ext Fa s.1 → body a s = .ok s' → ∃ u, s' = .yield u ∧ Fo.Ext Fa u.1) →
      Fo.Ext Fa s.1 → forIn l s body = .ok r → Fo.Ext Fa r.1 := by
    intro Fa l body s r hstep hs hr
    exact forIn_keeps body l (fun _ s => Fo.Ext Fa s.1)
      (fun _ a _ _ s s' hI hb => hstep a s s' hI hb) l [] s r rfl hs hr
  have E2 : Fo.Ext F1 F2 := addP F1 _ _ _ _ (fun a s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      exact ⟨_, (Except.ok.inj hs).symm, hI.trans (t2AddP_ok hP)⟩) (Fo.Ext.refl F1) h2
  have E3 : Fo.Ext F2 F3 := addP F2 _ _ _ _ (fun a s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      exact ⟨_, (Except.ok.inj hs).symm, hI.trans (t2AddP_ok hP)⟩) (Fo.Ext.refl F2) h3
  have E4 : Fo.Ext FB F4 := addP FB _ _ _ _ (fun a s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := ok_of_bind hs
      obtain ⟨_, hs⟩ := ok_of_jp hs
      exact ⟨_, (Except.ok.inj hs).symm, hI.trans (t2AddP_ok hP)⟩) (Fo.Ext.refl FB) h4
  exact U3Is.keep ((((E2.trans E3).trans (t2AddN_ok hZ).2.1).trans (t2AddN_ok hB).2.1).trans E4) k1

/-- A record that is shaped with the third vector alone names array number 0 for it. -/
theorem shapeF_U {tl tl' : HTailF2} {m : Array TMat} {txOf : Array (Option ℕ)}
    {f : Array T2Foreign} {tau : ℕ}
    (e : tl.shapeF m txOf f #[false, false, true, false] tau = .ok tl') :
    tl'.ix.U = #[none, none, some 0, none] := by
  unfold HTailF2.shapeF at e
  dsimp only at e
  rcases ite_ok e with ⟨_, e⟩ | ⟨_, e⟩
  · obtain ⟨_, e1, _⟩ := bindE_ok e
    cases e1
  obtain ⟨_, _, e⟩ := bindE_ok e
  rcases ite_ok e with ⟨_, e⟩ | ⟨_, e⟩
  · obtain ⟨_, e1, _⟩ := bindE_ok e
    cases e1
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  rcases ite_ok e with ⟨_, e⟩ | ⟨_, e⟩
  · obtain ⟨_, e1, _⟩ := bindE_ok e
    cases e1
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨r2, h2, e⟩ := bindE_ok e
  obtain rfl := Except.ok.inj h2
  obtain ⟨_, _, e⟩ := bindE_ok e
  rcases ite_ok e with ⟨_, e⟩ | ⟨_, e⟩
  · obtain ⟨_, e1, _⟩ := bindE_ok e
    cases e1
  obtain ⟨_, _, e⟩ := bindE_ok e
  rcases ite_ok e with ⟨_, e⟩ | ⟨_, e⟩
  · obtain ⟨_, e1, _⟩ := bindE_ok e
    cases e1
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, _, hi, _⟩ := Fo.PiecesF.piecesF_pieceOK_walk e
  rw [hi]
  rfl

/-- The plan's record names array number 0 for the third vector, and none for the other three. -/
theorem plan_U {settings : Settings} {j : Attention.In} {cf : Attention.Cfg} {A : Attention.Plan}
    (h : Attention.plan settings j cf = .ok A) : A.seam.tl.ix.U = #[none, none, some 0, none] := by
  obtain ⟨seam0, h0, h1, -⟩ := BatRows.planA_rows0 settings j cf A h
  obtain ⟨tl₀, m1, txOf, f, hS⟩ := seamShape_lit h0
  obtain ⟨T, hA⟩ := seamPlan_cut h1
  rw [(addTreesF_sameP hA).same.ix]
  exact shapeF_U hS

/-- **In the planned ledger the array of the vector of reads is number 0, with one row, as many
columns as the vector has entries, and one virtual row.** -/
theorem plan_u3_tree {settings : Settings} {j : Attention.In} {cf : Attention.Cfg} {A : Attention.Plan}
    (h : Attention.plan settings j cf = .ok A) :
    A.iU3 = 0 ∧ ∃ T : HTree, A.seam.Fp.trees[A.iU3]? = some T ∧ T.R = 1 ∧ T.K = A.nW ∧
      T.rows.size = 1 := by
  obtain ⟨seam0, h0, h1, -⟩ := BatRows.planA_rows0 settings j cf A h
  obtain ⟨tl₀, m1, txOf, f, hS⟩ := seamShape_lit h0
  obtain ⟨T, hA⟩ := seamPlan_cut h1
  have hU := shapeF_U hS
  have hu : seam0.tl.ix.U.getD 2 none = some 0 := by rw [hU]; rfl
  have e0 : A.iU3 = 0 := by
    show (A.seam.tl.ix.U.getD 2 none).getD 0 = 0
    rw [(addTreesF_sameP hA).same.ix, hu]
    rfl
  obtain ⟨k1, k2, k3, k4⟩ := addTreesF_u3all hA hu
  have e : A.seam.Fp.trees.getD 0 {} = A.seam.Fp.trees[0] := by simp [Array.getD, k1]
  rw [e] at k2 k3 k4
  refine ⟨e0, A.seam.Fp.trees[0], ?_, k2, k3, k4⟩
  rw [e0, Array.getElem?_eq_getElem k1]

/-- The plan's record has NAs + 4 matrices: the planner's own test. -/
theorem plan_nm {settings : Settings} {j : Attention.In} {cf : Attention.Cfg} {A : Attention.Plan}
    (h : Attention.plan settings j cf = .ok A) : A.seam.tl.NM = A.S.cf.NAs + 4 := by
  unfold Attention.plan at h
  obtain ⟨-, h⟩ := OnBytes.Road.L5.jp_ok h
  obtain ⟨-, h⟩ := OnBytes.Road.L5.jp_ok h
  obtain ⟨-, h⟩ := OnBytes.Road.L5.jp_ok h
  obtain ⟨r, hr, h⟩ := OnBytes.Road.L5.bind_ok h
  obtain ⟨S, fs⟩ := r
  obtain ⟨-, h⟩ := OnBytes.Road.L5.jp_ok h
  obtain ⟨seam0, -, h⟩ := OnBytes.Road.L5.bind_ok h
  obtain ⟨hn, h⟩ := OnBytes.Road.L5.jp_ok h
  obtain ⟨-, h⟩ := OnBytes.Road.L5.jp_ok h
  obtain ⟨seam, h1, h⟩ := OnBytes.Road.L5.bind_ok h
  have e := Except.ok.inj h
  subst e
  obtain ⟨T, hA⟩ := seamPlan_cut h1
  show seam.tl.NM = S.cf.NAs + 4
  rw [(addTreesF_sameP hA).same.NM]
  simpa using hn

/-- **The three tables on the lookup's matrix are the last three of the vector of reads**: each has
kbA entries, and the third ends where the vector ends. -/
theorem planes_end {g : Geo} {mats : Array (ℕ × ℕ)} {nW : ℕ} {lk : LookIn} {p : Pts} {t : TablesP}
    (h : P.tablesP g mats nW lk p = some t) :
    t.tBit0 + 3 * g.kbA = nW ∧ t.tBit1 + 2 * g.kbA = nW ∧ t.tPin + g.kbA = nW := by
  obtain ⟨-, q, e⟩ := tablesP_lays h
  have m : ∀ r, r = P.Read.bitsAtLeaves ∨ r = P.Read.bitsAtBits ∨ r = P.Read.counts →
      r ∈ P.reads p.scores.size := by
    intro r hr
    unfold P.reads
    rcases hr with rfl | rfl | rfl <;> simp
  have a0 : t.tBit0 = _ := q _ (m _ (Or.inl rfl))
  have a1 : t.tBit1 = _ := q _ (m _ (Or.inr (Or.inl rfl)))
  have a2 : t.tPin = _ := q _ (m _ (Or.inr (Or.inr rfl)))
  simp only [P.Read.start, P.Geo.nPlanes] at a0 a1 a2 e
  refine ⟨?_, ?_, ?_⟩ <;> omega

end K5Law

#print axioms K5Law.addN_K
#print axioms K5Law.U3Is.keep
#print axioms K5Law.addTreesF_u3all
#print axioms K5Law.shapeF_U
#print axioms K5Law.plan_U
#print axioms K5Law.plan_u3_tree
#print axioms K5Law.plan_nm
#print axioms K5Law.planes_end
