-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.Sits
/-
Johnson/Desc/K12/Law/AtCutWith.lean: AtCut (Johnson/Desc/K12/Law/Sits.lean) WITH A FACT AT THE RUN's
OWN RECORDS, INSIDE ITS OWN «THERE IS». WHY: AtCut says «there are m, t0, … with: the blocks in
front lead from the chain's start to m · the door lets m in as t0 · the kind's block's own step says
yes at t0 · …». A further sentence «there are m, t0 with … and Φ m t0» beside it opens the letters a
second time: read alone it speaks of SOME record. Here Φ stands under the same letters. (The letters
are pinned: each is a function's return: so the two readings agree: AtCutWith.and is that remark as
a
theorem.) NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. NO
NEW MATHEMATICS.
  AtCutWith … Φ        AtCut's nine conjuncts under its eight letters ∧ Φ m t0. Φ may read m (the
      chain's record in front of the seat) and t0 (the record that the door hands to the kind's
      block).
  AtCutWith.toAtCut · atCut_iff_true     it gives AtCut; AtCut is AtCutWith at the idle fact.
  atCutWith_of         AtCut, and Φ at every m, t0 that the run's own equations pin ⇒ AtCutWith Φ.
  AtCutWith.mono · AtCutWith.and     a weaker fact; two facts at ONE pair of records.
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (Letters)

/-- AtCut with a fact Φ at the record in front of the seat and at the record behind the door. -/
def AtCutWith (X : Letters) (p : P12) (ft : ℕ) {S Cl : Type} (pre : List (Block S Cl))
    (B : Block S Cl) (l : List (Block S Cl)) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (s s' : S) (v : Fmt.View) (Φ : S → T12 → Prop) : Prop :=
  ∃ (m : S) (t0 : T12) (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView) (cols : List OpenedColumn) (tE : T12) (n : ℕ)
    (t : S),
    foldBlocks ft pre s v.rounds v.opened = .ok (m, behindOf pre v.rounds, cols) ∧
    (∃ j, cols = v.opened.drop j) ∧
    enter m = .ok t0 ∧ (behindOf pre v.rounds).take B.rounds.length = r0 :: rs' ∧
    (proximityTestKind guardedProximityTestParts p : Blk').step ft t0 (r0 :: rs') cols = .ok (tE, n) ∧ leave m tE = .ok t ∧
    foldBlocks ft l t ((behindOf pre v.rounds).drop B.rounds.length) (cols.drop n) =
      .ok (s', [], []) ∧
    YesAll X p ft t0 r0 rs' cols ∧ GivenAt p ft t0 r0 rs' cols ∧ Φ m t0

section
variable {X : Letters} {p : P12} {ft : ℕ} {S Cl : Type} {pre : List (Block S Cl)}
  {B : Block S Cl} {l : List (Block S Cl)} {enter : S → Except String T12}
  {leave : S → T12 → Except String S} {s s' : S} {v : Fmt.View}

theorem AtCutWith.toAtCut {Φ : S → T12 → Prop}
    (h : AtCutWith X p ft pre B l enter leave s s' v Φ) :
    AtCut X p ft pre B l enter leave s s' v := by
  obtain ⟨m, t0, r0, rs', cols, tE, n, t, h1, h2, h3, h4, h5, h6, h7, h8, h9, _⟩ := h
  exact ⟨m, t0, r0, rs', cols, tE, n, t, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- From AtCut: Φ need only hold at what the run's own equations pin. -/
theorem atCutWith_of {Φ : S → T12 → Prop} (h : AtCut X p ft pre B l enter leave s s' v)
    (hΦ : ∀ (m : S) (t0 : T12) (r0 : Fmt.RoundView) (rs' : List Fmt.RoundView) (cols : List OpenedColumn) (tE : T12)
      (n : ℕ),
      foldBlocks ft pre s v.rounds v.opened = .ok (m, behindOf pre v.rounds, cols) →
      enter m = .ok t0 → (behindOf pre v.rounds).take B.rounds.length = r0 :: rs' →
      (proximityTestKind guardedProximityTestParts p : Blk').step ft t0 (r0 :: rs') cols = .ok (tE, n) → Φ m t0) :
    AtCutWith X p ft pre B l enter leave s s' v Φ := by
  obtain ⟨m, t0, r0, rs', cols, tE, n, t, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨m, t0, r0, rs', cols, tE, n, t, h1, h2, h3, h4, h5, h6, h7, h8, h9,
    hΦ m t0 r0 rs' cols tE n h1 h3 h4 h5⟩

theorem atCut_iff_true :
    AtCut X p ft pre B l enter leave s s' v ↔
      AtCutWith X p ft pre B l enter leave s s' v fun _ _ => True :=
  ⟨fun h => atCutWith_of h fun _ _ _ _ _ _ _ _ _ _ _ => trivial, AtCutWith.toAtCut⟩

theorem AtCutWith.mono {Φ Ψ : S → T12 → Prop}
    (h : AtCutWith X p ft pre B l enter leave s s' v Φ) (hm : ∀ m t0, Φ m t0 → Ψ m t0) :
    AtCutWith X p ft pre B l enter leave s s' v Ψ := by
  obtain ⟨m, t0, r0, rs', cols, tE, n, t, h1, h2, h3, h4, h5, h6, h7, h8, h9, hf⟩ := h
  exact ⟨m, t0, r0, rs', cols, tE, n, t, h1, h2, h3, h4, h5, h6, h7, h8, h9, hm m t0 hf⟩

/-- Two facts stand at ONE pair of records: the letters are the run's own. -/
theorem AtCutWith.and {Φ Ψ : S → T12 → Prop}
    (h : AtCutWith X p ft pre B l enter leave s s' v Φ)
    (h' : AtCutWith X p ft pre B l enter leave s s' v Ψ) :
    AtCutWith X p ft pre B l enter leave s s' v fun m t0 => Φ m t0 ∧ Ψ m t0 := by
  obtain ⟨m, t0, r0, rs', cols, tE, n, t, h1, h2, h3, h4, h5, h6, h7, h8, h9, hf⟩ := h
  obtain ⟨m', t0', _, _, _, _, _, _, g1, _, g3, _, _, _, _, _, _, gf⟩ := h'
  have em : m' = m := by
    have e := Except.ok.inj (g1.symm.trans h1)
    exact congrArg Prod.fst e
  subst em
  have et : t0' = t0 := Except.ok.inj (g3.symm.trans h3)
  subst et
  exact ⟨m', t0', r0, rs', cols, tE, n, t, h1, h2, h3, h4, h5, h6, h7, h8, h9, hf, gf⟩

end

end H2K.JointK

#print axioms H2K.JointK.atCutWith_of
#print axioms H2K.JointK.atCut_iff_true
#print axioms H2K.JointK.AtCutWith.mono
#print axioms H2K.JointK.AtCutWith.and
