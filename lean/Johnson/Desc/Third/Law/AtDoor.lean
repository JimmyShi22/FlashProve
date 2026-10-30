-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/AtDoor.lean: all that holds of the record that the last chain's own proximity
test is handed, in one statement. A structure of Prop and theorems.

Main names:
  `numbersOk_inv`, `firstOutFrom_inv`, `start₃_inv`, `start₃E_inv`: a yes of the start, taken apart.
  `AtDoor`: the codes are the plan's, at this record and at both ends; `Carries` from the first
    chain's last statement; Omega is the one new message, as in the shared chain's last statement; W
    has the plan's shape and is a member of the own group; the own group has the plan's codes, bore
    no mark, and its open rows are those that were pending at the first chain's end, and (Dot),
    which is no sample row; the sources are tied.
  `at_door`: the start's, K14's second part's and the sources' block's yes, in a row, give AtDoor.

Limits. What the pending rows, g and psi mean is the promise that this chain takes from the two
earlier ones: not stated here. Nothing on soundness or on hiding.
-/
import Johnson.Desc.Third.Law.Says
import Johnson.Desc.Third.Law.Sources
import Johnson.Desc.Third.Law.Start

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes OnBytes.Slice
open VerifiableInference.Desc.Later

namespace VerifiableInference.Desc.Third.Law

/-! ## The start, read back -/

theorem numbersOk_inv (S : Params.LinShape) (f : FirstOut) (h : numbersOk S f = true) :
    ∃ x G, f.st.oracles[f.w]? = some x ∧ f.st.groups[f.own]? = some G ∧ x.shape = S.w ∧
      G.members.contains f.w = true ∧ G.code = S.w.code ∧ G.maskCode = S.ownMaskCode ∧
      G.inRun = false := by
  unfold numbersOk at h
  split at h
  · rename_i x G hx hG
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, _⟩ := h
    refine ⟨x, G, hx, hG, of_decide_eq_true h1, h2, eq_of_beq h3, eq_of_beq h4, ?_⟩
    cases hq : G.inRun with
    | false => rfl
    | true =>
      rw [hq] at h5
      cases h5
  · cases h

theorem firstOutFrom_inv (S : Params.LinShape) (st : Statement) (book : TreeBook)
    (roots w own : Nat) (mask : Option Nat) (pile : List TensorRow) (f : FirstOut)
    (h : firstOutFrom S st book roots w own mask pile = some f) :
    numbersOk S f = true ∧ f.st = st ∧ f.w = w ∧ f.own = own ∧ f.mask = mask ∧
      ∃ r, pile = [r] ∧ f.g = r.g := by
  unfold firstOutFrom at h
  split at h
  · rename_i r
    try dsimp only at h
    repeat' (split at h)
    all_goals first
      | (cases h; exact ⟨by assumption, rfl, rfl, rfl, rfl, r, rfl, rfl⟩)
      | (cases h)
  · cases h

theorem start₃_inv (codes : Codes) (f : FirstOut) (o : SharedOut) (s₀ : S₃)
    (h : start₃ codes f o = some s₀) :
    f.st.codes = codes ∧ o.st.codes = codes ∧
      s₀ = { st := f.st, book := f.book, roots := 0
             loc := { w := f.w, own := f.own, mask := f.mask,
                      border := some { g := f.g, shared := o }
                      omega := noId, firstTree := f.roots + 1 } } := by
  unfold start₃ at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true] at hc
    exact ⟨of_decide_eq_true hc.1.1, of_decide_eq_true hc.1.2, (Option.some.inj h).symm⟩
  · cases h

theorem start₃E_inv (codes : Codes) (S : Params.LinShape) (st₁ : Statement) (book₁ : TreeBook)
    (roots₁ w₁ own₁ : Nat) (mask₁ : Option Nat) (pile₁ : List TensorRow) (o : SharedOut) (s₀ : S₃)
    (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀) :
    ∃ f, firstOutFrom S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ = some f ∧
      start₃ codes f o = some s₀ := by
  unfold start₃E at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i f hf
      split at h
      · cases h
      · rename_i t ht
        have e : t = s₀ := Except.ok.inj h
        subst e
        exact ⟨f, hf, ht⟩

/-! ## At the door -/

/-- **What holds of the record that the own test's block is handed.** -/
structure AtDoor {Cl : Type} (p : P₁₄) (own : Block S₃ Cl) (st₁ : Statement) (o : SharedOut)
    (g : List Tensor) (s : S₃) : Prop where
  codes : s.st.codes = p.codes ∧ st₁.codes = p.codes ∧ o.st.codes = p.codes
  carries : Carries st₁ s.st
  omegaIs : s.loc.omega = st₁.oracles.size ∧ s.st.oracles.size = st₁.oracles.size + 1
  omega : ∃ y, o.st.oracles[o.omega]? = some y ∧ y.sampled = true ∧
    s.st.oracles[st₁.oracles.size]? = some
      { shape := y.shape, sampled := true
        sampleRows := y.sampleRows.map (·.renamed st₁.oracles.size), pad := y.pad
        groups := [s.loc.own] }
  group : ∃ (x : OnBytes.Oracle) (G : OnBytes.Group) (dot : OnBytes.Row),
    st₁.oracles[s.loc.w]? = some x ∧ x.shape = p.S.w ∧ G.members.contains s.loc.w = true ∧
    st₁.groups[s.loc.own]? = some G ∧ G.code = p.S.w.code ∧ G.maskCode = p.S.ownMaskCode ∧
    G.inRun = false ∧
    linDotRow p.S g o.psi st₁.oracles.size (linLayOmega p.codes p.S) s.loc.w
      (linLayW p.codes p.S) = some dot ∧ (dot.kind != .sample) = true ∧
    s.st.groups[s.loc.own]? = some { G with
      members := G.members.insertIdxIfInBounds (G.members.filter (· < st₁.oracles.size)).size
        st₁.oracles.size
      kept := G.kept.insertIdxIfInBounds (G.members.filter (· < st₁.oracles.size)).size false
      rows := G.rows.push dot }
  tied : Tied own s

/-- **The start's, K14's second part's and the sources' block's yes, in a row, give AtDoor.** -/
theorem at_door {Cl : Type} (p : P₁₄) (own : Block S₃ Cl) (st₁ : Statement) (book₁ : TreeBook)
    (roots₁ w₁ own₁ : Nat) (mask₁ : Option Nat) (pile₁ : List TensorRow) (o : SharedOut)
    (s₀ s₁ s₂ : S₃)
    (r₀ r₁ : List Fmt.RoundView) (g₀ g₁ : List (List (Nat × List UInt64)))
    (hs : start₃E p.codes p.S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀)
    (h₀ : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s₀ r₀ g₀ = .ok s₁)
    (h₁ : (takenSources own).decide s₁ r₁ g₁ = .ok s₂) :
    (∃ r, pile₁ = [r] ∧ AtDoor p own st₁ o r.g s₂) ∧
      s₂.loc.w = w₁ ∧ s₂.loc.own = own₁ ∧ s₂.loc.mask = mask₁ := by
  obtain ⟨f, hf, hst⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ hs
  obtain ⟨hn, ef, ew, eo, em, r, hp, eg⟩ := firstOutFrom_inv _ _ _ _ _ _ _ _ _ hf
  obtain ⟨c1, c2, e0⟩ := start₃_inv _ _ _ _ hst
  obtain ⟨x, G, hx, hG, x1, x2, x3, x4, x5⟩ := numbersOk_inv _ _ hn
  obtain ⟨e2, ht⟩ := (takenSources_exact own s₁ r₁ g₁ s₂).1 h₁
  have hk := keeps_k14Second p s₀ r₀ g₀ s₁ h₀
  obtain ⟨b, y, G', dot, hb, hl, hy, hys, hz, ho, hG', _, hd, hkd, hg, _⟩ :=
    says_k14Second p s₀ s₁ r₀ g₀ h₀
  rw [e2]
  subst e0
  subst ef
  -- the border that K14's second part found is the one that the start laid
  have eb : ({ g := f.g, shared := o } : Border) = b := Option.some.inj hb
  subst eb
  -- the own group in front is the one that the start has looked at
  have eG : G = G' := Option.some.inj (hG.symm.trans hG')
  subst eG
  have lw : s₁.loc.w = f.w := congrArg Loc₃.w hl
  have lo : s₁.loc.own = f.own := congrArg Loc₃.own hl
  have lm : s₁.loc.omega = f.st.oracles.size := congrArg Loc₃.omega hl
  have lk : s₁.loc.mask = f.mask := congrArg Loc₃.mask hl
  have cs : s₁.st.codes = p.codes := (hk.1.1.codes).trans c1
  refine ⟨⟨r, hp, ⟨cs, c1, c2⟩, hk, ⟨lm, hz⟩, ⟨y, hy, hys, ?_⟩,
    ⟨x, G, dot, ?_, x1, ?_, ?_, x3, x4, x5, ?_, hkd, ?_⟩, ht⟩,
    lw.trans ew, lo.trans eo, lk.trans em⟩
  · rw [lo]
    exact ho
  · rw [lw]
    exact hx
  · rw [lw]
    exact x2
  · rw [lo]
    exact hG
  · rw [lw, ← eg, ← c1]
    exact hd
  · rw [lo]
    exact hg

end VerifiableInference.Desc.Third.Law

#print axioms VerifiableInference.Desc.Third.Law.numbersOk_inv
#print axioms VerifiableInference.Desc.Third.Law.firstOutFrom_inv
#print axioms VerifiableInference.Desc.Third.Law.start₃_inv
#print axioms VerifiableInference.Desc.Third.Law.at_door
