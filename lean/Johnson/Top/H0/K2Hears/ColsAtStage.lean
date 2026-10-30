-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/ColsAtStage.lean: the code switch: EVERY COLUMN THAT THE KIND's TEXT
IS SHOWN AT A STRETCH OF A CHAIN IS THE ORACLES' OWN, AT ITS KEY AND POSITION: LongCols.lean's
ColsOf, a premise of the switch's law (TiePaid.lean's YesAt.cols), at a reading of the oracles that
is MADE here, wherever Block.step's own tests pass.

The text lays its groups flat again, each column under its tree's key out of the plan (Kind.lean's
flat). Block.step has tested that the view's next columns have, in key, position and width, what the
declared rounds read (StepLaws.lean's Fits). So a flat column IS one of the view's columns. A
stretch's view (OnBytes/Maker/Stage.lean's sView) makes its columns out of its wants: a tree that
was sent in front of the stretch is read off the oracles in front.
  regroup_keyed  the i-th group that regroup lays holds columns of the list whose key, position and
                 width stand in the i-th group of wants: general
  groups_k2      what the kind's two declared rounds read: a group a tree of the plan's list «read»
  flat_key       a flat column's key is a tree's number out of «read»
  flat_sub       UNDER Fits: every flat column is one of the columns that the step was handed
  orcS           THE READING, MADE: to a key and a position: the column, at that position, of the
                 first tree at hand whose key it is; the empty column where there is none
  opened_is      a column of a stretch's view is a stored table's, or a tree's at a want
  posL_mem       a position in the trees at hand names a tree of the list
  orcS_old       the column of a tree at hand is orcS's, if the keys of the trees at hand are apart
  colsOf_stage   THE STATEMENT: ColsOf (orcS S y) (flat p (b.shown ft rs (sView C S y τ).opened))
LIMITS. FIVE PREMISES: Fits (Block.step's own tests: had at a yes of the step, not of the decision
alone) · ft is the plan's firstTree · hK: two trees at hand with one key have one number · h16: the
numbers in «read» are below 2 ^ 16 (so none is a stored table's key) · hNew: no tree that is sent in
the stretch or behind it has a key out of «read». The last three are facts on public numbers: NOT
SHOWN HERE AT ANY PLAN. orcS reads the oracles in front alone, not the transcript: so it is fixed
before the stretch's draws. No soundness is claimed.
-/
import Johnson.Top.H0.K2Hears.LongCols
import Johnson.Top.H0.StepLaws.StepLaws
import OnBytes.Maker.Stage

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open VerifiableInference.Desc (Block groupsOf regroup roundsFit roundsFit_length)
open OnBytes.Maker _root_.Run _root_.Run.PQ

theorem regroup_keyed : ∀ (G : List (List (Nat × Nat × Nat)))
    (got : List (Nat × Nat × List UInt64)),
    got.map (fun c => (c.1, c.2.1, c.2.2.length)) = G.flatMap id →
    ∀ (i : Nat) (g : List (Nat × Nat × Nat)) (h : List (Nat × List UInt64)),
      G[i]? = some g → (regroup (G.map (·.length)) got)[i]? = some h →
      ∀ x ∈ h, ∃ c ∈ got, x = (c.2.1, c.2.2) ∧ (c.1, c.2.1, c.2.2.length) ∈ g
  | [], _, _, i, g, h, hg, _ => by simp at hg
  | g0 :: G, got, e, i, g, h, hg, hh => by
    have e' : got.map (fun c => (c.1, c.2.1, c.2.2.length)) = g0 ++ G.flatMap id := by
      simpa using e
    have e1 : (got.take g0.length).map (fun c => (c.1, c.2.1, c.2.2.length)) = g0 := by
      rw [List.map_take, e', List.take_left']
      rfl
    have e2 : (got.drop g0.length).map (fun c => (c.1, c.2.1, c.2.2.length)) = G.flatMap id := by
      rw [List.map_drop, e', List.drop_left']
      rfl
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
      subst hg
      have hh' : (got.take g0.length).map (fun c => (c.2.1, c.2.2)) = h := by
        simpa [regroup] using hh
      intro x hx
      rw [← hh'] at hx
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
      have hm : (c.1, c.2.1, c.2.2.length) ∈
          (got.take g0.length).map (fun c => (c.1, c.2.1, c.2.2.length)) :=
        List.mem_map.2 ⟨c, hc, rfl⟩
      rw [e1] at hm
      exact ⟨c, List.mem_of_mem_take hc, rfl, hm⟩
    | succ i =>
      have hg' : G[i]? = some g := by simpa using hg
      have hh' : (regroup (G.map (·.length)) (got.drop g0.length))[i]? = some h := by
        simpa [regroup] using hh
      intro x hx
      obtain ⟨c, hc, h1, h2⟩ := regroup_keyed G _ e2 i g h hg' hh' x hx
      exact ⟨c, List.mem_of_mem_drop hc, h1, h2⟩

/-- What the kind's two declared rounds read. -/
theorem groups_k2 (p : P2) (ft : Nat) (R1 R2 : Fmt.Drawn) :
    groupsOf ft (rounds p) [R1, R2] = p.read.map fun r =>
      (Fmt.listOf (R2.poss.map (· % 2 ^ r.2.1))).map fun x =>
        (p.firstTree + r.1 - ft, x, r.2.2) := by
  simp [groupsOf, rounds, List.map_map, Function.comp_def]

theorem flat_at (p : P2) (gs : List (List (Nat × List UInt64))) (c : Nat × Nat × List UInt64)
    (hc : c ∈ flat p gs) : ∃ (i : Nat) (r : Nat × Nat × Nat) (g : List (Nat × List UInt64)),
      p.read[i]? = some r ∧ gs[i]? = some g ∧ ∃ x ∈ g, c = (r.1, x.1, x.2) := by
  unfold flat at hc
  obtain ⟨⟨r, g⟩, hz, hc⟩ := List.mem_flatMap.1 hc
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hz
  rw [List.getElem?_zip_eq_some] at hi
  exact ⟨i, r, g, hi.1, hi.2, x, hx, rfl⟩

/-- A flat column's key is a tree's number out of the plan's list. -/
theorem flat_key (p : P2) (gs : List (List (Nat × List UInt64))) (c : Nat × Nat × List UInt64)
    (hc : c ∈ flat p gs) : ∃ r ∈ p.read, c.1 = r.1 := by
  obtain ⟨i, r, g, h1, -, x, -, rfl⟩ := flat_at p gs c hc
  exact ⟨r, List.mem_of_getElem? h1, rfl⟩

/-- **Under Block.step's own tests every flat column is one of the columns handed over.** -/
theorem flat_sub {S Cl : Type} (b : Block S Cl) (p : P2) (hr : b.rounds = rounds p)
    (rs : List Fmt.RoundView) (cols : List (Nat × Nat × List UInt64))
    (hF : b.Fits p.firstTree rs cols) :
    ∀ c ∈ flat p (b.shown p.firstTree rs cols), c ∈ cols := by
  obtain ⟨hf, hw⟩ := hF
  have hl := roundsFit_length _ _ hf
  rw [hr] at hl
  obtain ⟨r1, r2, rfl⟩ : ∃ r1 r2, rs = [r1, r2] := by
    match rs, hl with
    | [r1, r2], _ => exact ⟨r1, r2, rfl⟩
  intro c hc
  obtain ⟨i, r, g, h1, h2, x, hx, rfl⟩ := flat_at p _ c hc
  have hw' := eq_of_beq hw
  unfold Block.shown at h2
  unfold Block.want at hw' h2
  rw [hr] at hw' h2
  simp only [List.map_cons, List.map_nil] at hw' h2
  rw [groups_k2] at hw' h2
  obtain ⟨c', hc', e1, e2⟩ := regroup_keyed _ _ hw' i _ g
    (by rw [List.getElem?_map, h1]; rfl) h2 x hx
  obtain ⟨z, -, ez⟩ := List.mem_map.1 e2
  have hk : c'.1 = r.1 := by
    have := congrArg Prod.fst ez
    simp only at this
    omega
  have : (r.1, x.1, x.2) = c' := by
    rw [e1, ← hk]
  rw [this]
  exact List.mem_of_mem_take hc'

section
variable (C : CK) (S : StageD)

/-- **The reading of the oracles in front, made.** -/
def orcS (y : S.Ei.Str) (k x : Nat) : List UInt64 :=
  match S.Lin.find? (fun L => S.key L.no == k) with
  | some L => ((posL S.Lin L.no x).map y.2).getD []
  | none => []

/-- A column of a stretch's view. -/
theorem opened_is (y : S.Ei.Str) (τ : Iop.Tr (uLT C S.ds)) (c : Nat × Nat × List UInt64)
    (hc : c ∈ (sView C S y τ).opened) :
    (∃ item, c.1 = Fmt.storedKey item) ∨
      ∃ j, c.1 = S.key j ∧ sCol C S y τ (.tree j c.2.1) = some c.2.2 := by
  unfold sView at hc
  obtain ⟨w, -, hw⟩ := List.mem_filterMap.1 hc
  obtain ⟨col, h1, rfl⟩ := Option.map_eq_some_iff.1 hw
  cases w with
  | table item x => exact Or.inl ⟨item, rfl⟩
  | tree j x => exact Or.inr ⟨j, rfl, h1⟩

theorem posL_mem (L : List LeftT) (j x : Nat) (q : PosL L) (h : posL L j x = some q) :
    ∃ T ∈ L, T.no = j := by
  unfold posL at h
  obtain ⟨i, -, hi⟩ := List.exists_of_findSome?_eq_some h
  by_cases e : (L.get i).no = j
  · exact ⟨L.get i, List.get_mem L i, e⟩
  · rw [if_neg e] at hi
    cases hi

/-- The column of a tree at hand is orcS's. -/
theorem orcS_old (hK : ∀ T ∈ S.Lin, ∀ T' ∈ S.Lin, S.key T.no = S.key T'.no → T.no = T'.no)
    (y : S.Ei.Str) (j x : Nat) (col : List UInt64) (h : (posL S.Lin j x).map y.2 = some col) :
    col = orcS S y (S.key j) x := by
  obtain ⟨q, hq, -⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨T, hT, rfl⟩ := posL_mem _ _ _ _ hq
  unfold orcS
  cases hf : S.Lin.find? (fun L => S.key L.no == S.key T.no) with
  | none =>
    have := List.find?_eq_none.1 hf T hT
    simp at this
  | some T' =>
    have h1 : S.key T'.no = S.key T.no := by simpa using List.find?_some hf
    have h2 := hK T' (List.mem_of_find?_eq_some hf) T hT h1
    simp only [h2, h, Option.getD_some]

/-- **Every column that the text is shown is the oracles' own.** -/
theorem colsOf_stage {St Cl : Type} (b : Block St Cl) (p : P2) (hr : b.rounds = rounds p)
    (hK : ∀ T ∈ S.Lin, ∀ T' ∈ S.Lin, S.key T.no = S.key T'.no → T.no = T'.no)
    (h16 : ∀ r ∈ p.read, r.1 < 2 ^ 16)
    (hNew : ∀ j, S.base ≤ j → ∀ r ∈ p.read, S.key j ≠ r.1)
    (y : S.Ei.Str) (τ : Iop.Tr (uLT C S.ds)) (rs : List Fmt.RoundView)
    (hF : b.Fits p.firstTree rs (sView C S y τ).opened) :
    ColsOf (orcS S y) (flat p (b.shown p.firstTree rs (sView C S y τ).opened)) := by
  intro c hc
  obtain ⟨r, hrm, hk⟩ := flat_key p _ c hc
  rcases opened_is C S y τ c (flat_sub b p hr rs _ hF c hc) with ⟨item, e⟩ | ⟨j, e, hcol⟩
  · have := h16 r hrm
    rw [← hk, e] at this
    unfold Fmt.storedKey at this
    omega
  · by_cases hj : j < S.base
    · have h' : (posL S.Lin j c.2.1).map y.2 = some c.2.2 := by
        have h0 : (if j < S.base then (posL S.Lin j c.2.1).map y.2
            else colAtST C S.ds τ (j - S.base) c.2.1) = some c.2.2 := hcol
        rwa [if_pos hj] at h0
      rw [e]
      exact orcS_old S hK y j c.2.1 c.2.2 h'
    · exact absurd (e.symm.trans hk) (hNew j (Nat.le_of_not_lt hj) r hrm)

end

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.flat_sub
#print axioms VerifiableInference.Desc.First.K2.colsOf_stage
