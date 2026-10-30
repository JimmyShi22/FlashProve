-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/Says.lean: what K14's second part has laid on the last chain's statement,
exactly. Definitions of Prop and theorems.

Main names:
  `Says p s s'`: of the record s in front of the block and s' behind it. One new message, Omega, at
    the next free number, with the shape, the sample rows (renamed) and the pad that it has in the
    shared chain's last statement, where it is sampled; its one group is the own group. The own
    group bore no mark; Omega is its new member, not kept; its open rows are those in front with
    (Dot) as the last; (Dot) is `linDotRow` at the shape, the claim's row weights, the shared point,
    Omega and W, and is no sample row. THE FRAME: every older message and every other group is as it
    was; there are as many groups; the codes are the same.
  `Law₁₄`: Keeps and Says.
  `says_k14Second`, `law_k14Second`.
  `idle₃_not_law`, `deaf₃_law`: the block that says yes to all fails the law; the block that says no
    to all meets it, as it meets every law of the form "a yes only if".

Limits. What the row (Dot) says of committed values is not stated here. The book of trees:
Johnson/Desc/Third/Law/Book.lean. Nothing on soundness or on hiding.
-/
import Johnson.Desc.Third.Law.Keeps
import OnBytes.Slice.BlkStLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes OnBytes.Slice
open Desc.Plain (DState)
open VerifiableInference.Desc.Later
open VerifiableInference.Desc.Ground (adoptP elsewhereP elsewhereL joinP addRowP)

namespace VerifiableInference.Desc.Third.Law

/-- **What K14's second part has laid.** s: the record in front; s': the record behind. -/
def Says (p : P₁₄) (s s' : S₃) : Prop :=
  ∃ (x : Border) (y : OnBytes.Oracle) (G : OnBytes.Group) (dot : OnBytes.Row),
    s.loc.border = some x ∧
    s'.loc = { s.loc with border := none, omega := s.st.oracles.size } ∧
    x.shared.st.oracles[x.shared.omega]? = some y ∧ y.sampled = true ∧
    s'.st.oracles.size = s.st.oracles.size + 1 ∧
    s'.st.oracles[s.st.oracles.size]? = some
      { shape := y.shape, sampled := true
        sampleRows := y.sampleRows.map (·.renamed s.st.oracles.size), pad := y.pad
        groups := [s.loc.own] } ∧
    s.st.groups[s.loc.own]? = some G ∧ G.inRun = false ∧
    linDotRow p.S x.g x.shared.psi s.st.oracles.size (linLayOmega s.st.codes p.S) s.loc.w
      (linLayW s.st.codes p.S) = some dot ∧ (dot.kind != .sample) = true ∧
    s'.st.groups[s.loc.own]? = some { G with
      members := G.members.insertIdxIfInBounds (G.members.filter (· < s.st.oracles.size)).size
        s.st.oracles.size
      kept := G.kept.insertIdxIfInBounds (G.members.filter (· < s.st.oracles.size)).size false
      rows := G.rows.push dot } ∧
    -- the frame
    s'.st.codes = s.st.codes ∧
    (∀ i : Nat, i < s.st.oracles.size → s'.st.oracles[i]? = s.st.oracles[i]?) ∧
    (∀ i : Nat, i ≠ s.loc.own → s'.st.groups[i]? = s.st.groups[i]?) ∧
    s'.st.groups.size = s.st.groups.size

/-- **The law of K14's part on the third chain, as a property of a block.** -/
def Law₁₄ {Cl : Type} (p : P₁₄) (b : Block S₃ Cl) : Prop :=
  Keeps (fun s : S₃ => s.st) b ∧ ∀ s rs gs s', b.decide s rs gs = .ok s' → Says p s s'

/-! ## Small steps -/

theorem modify_same {α : Type} (xs : Array α) (i : Nat) (f : α → α) (x : α) (h : xs[i]? = some x) :
    (xs.modify i f)[i]? = some (f x) := by
  simp [Array.getElem?_modify, h]

/-- The one number that adoptP returns for one message is the next free one. -/
theorem adopt_one {L : Type} (d : DState L) (n : OracleNotice) (given : Array (Nat × Fmt.Src))
    (a : Array Nat × DState L) (mine : Nat) (h : adoptP d #[n] given = some a)
    (hm : a.1[0]? = some mine) : mine = d.st.oracles.size := by
  rw [(adoptP_inv d #[n] given a h).2] at hm
  simp at hm
  omega

/-! ## The taking-over, as a statement written out -/

/-- The statement behind the taking-over, at Omega's number and at the own group. -/
theorem takeOver_says (S : Params.LinShape) (own : Nat) (o : SharedOut) (d : DState Loc₃)
    (r : Nat × DState Loc₃) (h : takeOver S own o d = .ok r) :
    ∃ (y : OnBytes.Oracle) (G : OnBytes.Group), r.1 = d.st.oracles.size ∧
      o.st.oracles[o.omega]? = some y ∧ y.sampled = true ∧
      r.2.st.oracles.size = d.st.oracles.size + 1 ∧
      r.2.st.oracles[d.st.oracles.size]? = some
        { shape := y.shape, sampled := true
          sampleRows := y.sampleRows.map (·.renamed d.st.oracles.size), pad := y.pad
          groups := [own] } ∧
      d.st.groups[own]? = some G ∧ G.inRun = false ∧
      r.2.st.groups[own]? = some { G with
        members := G.members.insertIdxIfInBounds (G.members.filter (· < d.st.oracles.size)).size
          d.st.oracles.size
        kept := G.kept.insertIdxIfInBounds (G.members.filter (· < d.st.oracles.size)).size false } ∧
      (∀ i : Nat, i < d.st.oracles.size → r.2.st.oracles[i]? = d.st.oracles[i]?) ∧
      (∀ i : Nat, i ≠ own → r.2.st.groups[i]? = d.st.groups[i]?) ∧
      r.2.st.groups.size = d.st.groups.size := by
  obtain ⟨q, t, y, a, d₁, _, _, hy, ha, hm, h1, h2⟩ := takeOver_inv S own o d r h
  obtain ⟨mine, d₂⟩ := r
  have hmine : mine = d.st.oracles.size := adopt_one d _ _ a mine ha hm
  subst hmine
  have e0 : a.2.st = stSent d.st #[{ shape := y.shape, leafClass := S.omegaLeafClass }] :=
    (adoptP_inv d _ _ a ha).1
  obtain ⟨y', hy', e1, hok1⟩ := elsewhereP_inv a.2 d₁ _ o.st o.omega h1
  have ey : y = y' := Option.some.inj (hy.symm.trans hy')
  subst ey
  obtain ⟨G, hG, hr, e2⟩ := joinP_inv d₁ d₂ own _ false h2
  -- sampled there
  have ts := ok_mem hok1 _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  rw [hy] at ts
  have hs : y.sampled = true := ts
  -- the group in front is the first record's
  have hG0 : d.st.groups[own]? = some G := by
    rw [e1, e0] at hG
    exact hG
  -- Omega, step by step
  have o0 : a.2.st.oracles[d.st.oracles.size]? = some { shape := y.shape } := by
    rw [e0]
    have t0 := stSent_new d.st #[{ shape := y.shape, leafClass := S.omegaLeafClass }] 0
    simpa using t0
  have o1 : d₁.st.oracles[d.st.oracles.size]? = some
      { shape := y.shape, sampled := true
        sampleRows := y.sampleRows.map (·.renamed d.st.oracles.size), pad := y.pad } := by
    rw [e1]
    exact modify_same _ _ _ _ o0
  have o2 : d₂.st.oracles[d.st.oracles.size]? = some
      { shape := y.shape, sampled := true
        sampleRows := y.sampleRows.map (·.renamed d.st.oracles.size), pad := y.pad
        groups := [own] } := by
    rw [e2]
    exact joined_same _ _ _ _ _ _ o1
  have g2 : d₂.st.groups[own]? = some { G with
      members := G.members.insertIdxIfInBounds (G.members.filter (· < d.st.oracles.size)).size
        d.st.oracles.size
      kept := G.kept.insertIdxIfInBounds (G.members.filter (· < d.st.oracles.size)).size
        false } := by
    rw [e2]
    exact joined_group _ _ _ _ _ hG
  have z2 : d₂.st.oracles.size = d.st.oracles.size + 1 := by
    rw [e2, e1, e0]
    simp [withMessageInGroup, stSent]
  -- the frame
  have fo : ∀ i : Nat, i < d.st.oracles.size → d₂.st.oracles[i]? = d.st.oracles[i]? := by
    intro i hi
    have hne : d.st.oracles.size ≠ i := Nat.ne_of_gt hi
    have f0 : a.2.st.oracles[i]? = d.st.oracles[i]? := by
      rw [e0]
      exact stSent_old d.st _ i hi
    have f1 : d₁.st.oracles[i]? = a.2.st.oracles[i]? := by
      rw [e1]
      simp [Array.getElem?_modify, hne]
    have f2 : d₂.st.oracles[i]? = d₁.st.oracles[i]? := by
      rw [e2]
      exact joined_other _ _ _ _ _ i hne
    exact f2.trans (f1.trans f0)
  have fg : ∀ i : Nat, i ≠ own → d₂.st.groups[i]? = d.st.groups[i]? := by
    intro i hi
    have hne : own ≠ i := Ne.symm hi
    have f1 : d₁.st.groups[i]? = d.st.groups[i]? := by
      rw [e1, e0]
      rfl
    have f2 : d₂.st.groups[i]? = d₁.st.groups[i]? := by
      rw [e2]
      simp [withMessageInGroup, Array.getElem?_modify, hne]
    exact f2.trans f1
  have zg : d₂.st.groups.size = d.st.groups.size := by
    rw [e2, e1, e0]
    simp [withMessageInGroup, stSent]
  exact ⟨y, G, rfl, hy, hs, z2, o2, hG0, hr, g2, fo, fg, zg⟩

/-! ## The block -/

/-- **What K14's second part returns, it has laid so.** -/
theorem says_k14Second {Cl : Type} (p : P₁₄) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s') :
    Says p s s' := by
  obtain ⟨x, a, dot, b, hx, ha, hd, hb, e⟩ := k14Second_inv p s s' rs gs h
  subst e
  obtain ⟨y, G, hm, hy, hs, z2, o2, hG0, hr, g2, fo, fg, zg⟩ := takeOver_says _ _ _ _ _ ha
  have hm' : a.1 = s.st.oracles.size := hm
  have hc : a.2.st.codes = s.st.codes := (carries_takeOver _ _ _ _ _ ha).1.1.codes
  obtain ⟨_, hk, eb⟩ := addRowP_inv _ _ _ _ hb
  rw [hc, hm'] at hd
  refine ⟨x, y, G, dot, hx, ?_, hy, hs, ?_, ?_, hG0, hr, hd, hk, ?_, ?_, ?_, ?_, ?_⟩
  · show ({ s.loc with border := none, omega := a.1 } : Loc₃) = _
    rw [hm']
  · show b.st.oracles.size = _
    rw [eb]
    exact z2
  · show b.st.oracles[s.st.oracles.size]? = _
    rw [eb]
    exact o2
  · show b.st.groups[s.loc.own]? = _
    rw [eb]
    exact withRow_group _ _ _ _ g2
  · show b.st.codes = _
    rw [eb]
    exact hc
  · intro i hi
    show b.st.oracles[i]? = _
    rw [eb]
    exact fo i hi
  · intro i hi
    show b.st.groups[i]? = _
    rw [eb]
    have hne : s.loc.own ≠ i := Ne.symm hi
    have f3 : (withRow a.2.st s.loc.own dot).groups[i]? = a.2.st.groups[i]? := by
      simp [withRow, Array.getElem?_modify, hne]
    exact f3.trans (fg i hi)
  · show b.st.groups.size = _
    rw [eb]
    have f4 : (withRow a.2.st s.loc.own dot).groups.size = a.2.st.groups.size := by
      simp [withRow]
    exact f4.trans zg

/-- **K14's second part meets the law.** -/
theorem law_k14Second {Cl : Type} (p : P₁₄) : Law₁₄ p (batchLinearConstraintsSecondPart (Cl := Cl) p) :=
  ⟨keeps_k14Second p, fun s rs gs s' h => says_k14Second p s s' rs gs h⟩

/-! ## The statement at the two silly members -/

/-- Says holds of no record and itself: the border is there in front and gone behind. -/
theorem says_irrefl (p : P₁₄) (s : S₃) : ¬ Says p s s := by
  intro h
  obtain ⟨x, _, _, _, hx, hl, _⟩ := h
  have t : s.loc.border = none := congrArg Loc₃.border hl
  rw [hx] at t
  cases t

/-- It says yes to all and hands the record on. -/
def idle₃ : Block S₃ Unit := roundlessBlock "idle" 3 none 0 fun s => .ok s
/-- It says no to all. -/
def deaf₃ : Block S₃ Unit := roundlessBlock "deaf" 3 none 0 fun _ => .error "no"

theorem idle₃_not_law (p : P₁₄) (s : S₃) : ¬ Law₁₄ p idle₃ :=
  fun h => says_irrefl p s (h.2 s [] [] s rfl)

theorem deaf₃_law (p : P₁₄) : Law₁₄ p deaf₃ :=
  ⟨fun _ _ _ _ h => (by cases h), fun _ _ _ _ h => (by cases h)⟩

end VerifiableInference.Desc.Third.Law

#print axioms VerifiableInference.Desc.Third.Law.takeOver_says
#print axioms VerifiableInference.Desc.Third.Law.says_k14Second
#print axioms VerifiableInference.Desc.Third.Law.law_k14Second
#print axioms VerifiableInference.Desc.Third.Law.says_irrefl
#print axioms VerifiableInference.Desc.Third.Law.idle₃_not_law
#print axioms VerifiableInference.Desc.Third.Law.deaf₃_law
