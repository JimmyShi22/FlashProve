-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Whole.lean: one whole masked sumcheck as the kind "lookup" calls it
(wholeStandIn, Johnson/Desc/First/Prod/Level.lean), where it returns: what it has read off the tape,
what it has done to the ledger, and what it hands back, on machine words.

Main names:
  Adv F G k: G is a later ledger than F and has taken k slots more.
  loop2_fl: the rounds of the variables.
  shownLoop: the end values are read back off the ledger.
  whole_fl: the whole.

Limits. Nothing is said where it returns nothing.

-/
import Johnson.Desc.First.Look.KeyLaw.Kit
import Johnson.Desc.First.Prod.Level

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc RoundName RoundForm)
open OnBytes.PscRun (took Later Sized Filled Ran)
open First.Prod (wholeStandIn Whole)

/-- G is later than F and has taken k slots more. -/
structure Adv (F G : Fork) (k : Nat) : Prop where
  next : G.next = F.next + k
  later : Later F G

theorem Adv.refl (F : Fork) : Adv F F 0 := ⟨rfl, Later.refl F⟩

theorem Adv.trans {F G H : Fork} {a b : Nat} (h : Adv F G a) (h' : Adv G H b) : Adv F H (a + b) :=
  ⟨by rw [h'.next, h.next, Nat.add_assoc], h.later.trans h'.later⟩

theorem Adv.cast {F G : Fork} {a b : Nat} (h : Adv F G a) (e : a = b) : Adv F G b := e ▸ h

theorem adv_took (F : Fork) (n : Nat) : Adv F (took F n) n := ⟨rfl, PscRun.took_later F n⟩

theorem adv_hide {F G : Fork} {first : Nat} {v : Array E} {factor : E} (hF : Sized F)
    (h : F.hideRun first v factor = some G) : Adv F G 0 :=
  ⟨(PscRun.hideRun_ok F G first v factor hF h).1.next, PscRun.hideRun_later hF h⟩

/-- The rounds of the variables of a sumcheck under equality weights, three coefficients each. -/
theorem loop2_fl {first : Nat} {mu eps : E} (zs : List E) : ∀ (p p' : Psc) (F G : Fork) (t u : Tape)
    (zd : List (E × Nat)) (rs : List (List E × E)),
    (zs.foldlM (m := Fl) (fun (p : Psc) z => do
      let x ← Fl.roundIn .eq2 p z
      pure x.2) p) F t = some (p', G, u) →
    Ran p first mu eps zd rs →
    ∃ rs' : List (List E × E), rs'.length = zs.length ∧
      rs'.map (fun r => r.1.length) = List.replicate zs.length 2 ∧
      Ran p' first mu eps (zd ++ zs.map (·, 3)) (rs ++ rs') ∧
      t.map key = (rs'.map fun r => kr .pscRound 0 r.1 [r.2]) ++ u.map key ∧
      Adv F G (2 * zs.length) ∧ p'.start = p.start ∧ p'.target = p.target := by
  induction zs with
  | nil =>
    intro p p' F G t u zd rs h hR
    cases pure_some h
    exact ⟨[], rfl, rfl, by simpa using hR, rfl, Adv.refl _, rfl, rfl⟩
  | cons z zs ih =>
    intro p p' F G t u zd rs h hR
    rw [List.foldlM_cons] at h
    replace h := bind_some h
    obtain ⟨p1, G1, u1, h1, h⟩ := h
    replace h1 := bind_some h1
    obtain ⟨⟨x, q⟩, G2, u2, h2, h1⟩ := h1
    cases pure_some h1
    obtain ⟨w, sent, hw, e1, e2, hG, hq⟩ := round_fl h2
    obtain rfl : OnBytes.Psc.Weight.equality z 3 = w :=
      Option.some.inj ((PscRun.weight_eq2 z 0).symm.trans hw)
    have hr := PscRun.ran_push hR z 3 sent x e2 q (by rw [hq]) (by rw [hq]) (by rw [hq])
      (by rw [hq]) (by rw [hq]) (by rw [hq])
    obtain ⟨rs', l, l2, hR', e3, a, e5, e6⟩ := ih q p' _ G _ u _ _ h hr
    refine ⟨(sent.toList, x) :: rs', by simp [l], ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.map_cons, l2, List.length_cons, List.replicate_succ]
      congr 1
      show sent.toList.length = 2
      have : sent.size + 1 = 3 := e2
      rw [Array.length_toList]; omega
    · simpa [List.append_assoc] using hR'
    · rw [e1, e3]; rfl
    · rw [hG] at a
      exact ((adv_took F 2).trans a).cast (by rw [List.length_cons]; omega)
    · rw [e5, hq]
    · rw [e6, hq]

/-- Values are read off the ledger, slot by slot. -/
theorem shownLoop (e : Nat) : ∀ (l : List Nat) (acc r : List E) (F G : Fork) (t u : Tape),
    List.mapM.loop (fun i => Fl.shown (e + i)) l acc F t = some (r, G, u) →
    G = F ∧ u = t ∧ r = acc.reverse ++ l.map fun i => F.vp.getD (e + i) zeroE
  | [], acc, r, F, G, t, u, h => by
    cases pure_some h
    exact ⟨rfl, rfl, by simp⟩
  | i :: l, acc, r, F, G, t, u, h => by
    unfold List.mapM.loop at h
    replace h := bind_some h
    obtain ⟨y, G1, u1, h1, h⟩ := h
    replace h1 := ask_some h1
    obtain ⟨h1, rfl, rfl⟩ := h1
    obtain ⟨-, -, rfl⟩ := (PscRun.shown_iff _ _ _).1 h1
    obtain ⟨rfl, rfl, rfl⟩ := shownLoop e l _ r _ G _ u h
    exact ⟨rfl, rfl, by simp⟩

theorem list_of_getD (v : Array E) : (List.range v.size).map (fun i => v.getD i zeroE) = v.toList :=
    by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    have : i < v.size := by simpa using h2
    simp [Array.getD, this]

/-- **One whole masked sumcheck.** -/
theorem whole_fl {C : Aff} {zs : List E} {dY n : Nat} {endTerm : List E → E} {F G : Fork}
    {t u : Tape} {w : Whole} (hF : Sized F)
    (h : wholeStandIn C zs dY n endTerm F t = some (w, G, u)) :
    ∃ (τ mu eps : E) (rs : List (List E × E)) (ry : List E × E) (v : Array E) (p : Psc)
      (G1 G2 : Fork),
      F.publicPart C = some τ ∧ rs.length = zs.length ∧
      rs.map (fun r => r.1.length) = List.replicate zs.length 2 ∧ ry.1.length = dY ∧
      t.map key = pscKeys mu eps rs (some (ry, v.toList)) ++ u.map key ∧
      Ran p F.next mu eps (zs.map (·, 3) ++ [(zeroE, dY + 1)]) (rs ++ [ry]) ∧
      p.start = C ∧ p.target = τ ∧ v.size = n ∧ w.challenges = (rs ++ [ry]).map (·.2) ∧
      w.sEnd = F.next + (1 + 2 * zs.length + dY) ∧ w.row = p.rowForm (endTerm v.toList) {} ∧
      Adv F G1 (1 + 2 * zs.length + dY + n) ∧ G1.hideRun w.sEnd v ry.2 = some G2 ∧
      G2.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G := by
  unfold wholeStandIn at h
  replace h := bind_some h
  obtain ⟨p0, G0, u0, h0, h⟩ := h
  obtain ⟨τ, mu, eps, hτ, k0, rfl, rfl⟩ := begin_fl h0
  replace h := bind_some h
  obtain ⟨p1, G1, u1, h1, h⟩ := h
  obtain ⟨rs, hl, hl2, hR, k1, a1, s1, t1⟩ := loop2_fl zs _ p1 _ G1 _ u1 [] [] h1
    (PscRun.ran_begin C τ mu eps F.next)
  replace h := bind_some h
  obtain ⟨⟨sEnd, p2⟩, G2, u2, h2, h⟩ := h
  obtain ⟨sent, v, beta, k2, hs, hv, rfl, hh, rfl⟩ := ends_fl h2
  replace h := bind_some h
  obtain ⟨ends, G3, u3, h3, h⟩ := h
  obtain ⟨rfl, rfl, rfl⟩ := shownLoop _ _ [] ends _ G3 _ u3 h3
  replace h := bind_some h
  obtain ⟨⟨row, p3⟩, G4, u4, h4, h⟩ := h
  obtain ⟨hr, rfl, rfl⟩ := row_fl h4
  cases pure_some h
  have a0 : Adv F (took (took G1 dY) n) (1 + 2 * zs.length + dY + n) :=
    (((adv_took F 1).trans a1).trans (adv_took G1 dY)).trans (adv_took _ n)
  have hS : Sized (took (took G1 dY) n) := a0.later.sized hF
  obtain ⟨-, -, f3, -⟩ := PscRun.hideRun_ok _ _ _ _ _ hS hh
  have hR2 := PscRun.ran_push hR zeroE (dY + 1) sent beta (by omega)
    { p1 with
      claim := OnBytes.Psc.polyAt
        ((OnBytes.Psc.Weight.equality zeroE (dY + 1)).complete sent.toList p1.claim) beta,
      vars := p1.vars.push (OnBytes.Psc.Weight.equality zeroE (dY + 1)),
      r := p1.r.push beta, ended := true } rfl rfl rfl rfl rfl rfl
  have hends : ([] : List E).reverse ++
      (List.range n).map (fun i => G3.vp.getD (G1.next + dY + i) zeroE) = v.toList := by
    rw [List.reverse_nil, List.nil_append, ← list_of_getD v, hv]
    exact List.map_congr_left fun i hi => (f3 i (by rw [hv]; exact List.mem_range.1 hi)).2.2.2.1
  have hn1 : G1.next = F.next + (1 + 2 * zs.length) := by
    rw [a1.next]; show F.next + 1 + _ = _; omega
  refine ⟨τ, mu, eps, rs, (sent.toList, beta), v,
    { p1 with
      claim := OnBytes.Psc.polyAt
        ((OnBytes.Psc.Weight.equality zeroE (dY + 1)).complete sent.toList p1.claim) beta,
      vars := p1.vars.push (OnBytes.Psc.Weight.equality zeroE (dY + 1)),
      r := p1.r.push beta, ended := true }, took (took G1 dY) n, G3, hτ, hl, hl2,
    (by rw [Array.length_toList]; exact hs), ?_, ?_, s1, t1, hv,
    ?_, ?_, ?_, a0, hh, hr⟩
  · rw [k0, k1, k2]
    simp [pscKeys]
  · simpa using hR2
  · show (p1.r.push beta).toList = _
    rw [Array.toList_push, hR.r_eq]
    simp
  · show G1.next + dY = _
    rw [hn1]; omega
  · show Psc.rowForm _ (endTerm _) {} = _
    rw [hends]

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.whole_fl
