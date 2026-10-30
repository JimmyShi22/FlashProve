-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoR5.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoR5.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  R5Is, r5
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  Closed, Filled, FitsA, Later, R5D.cls, Same, Sized, Stretch, bits2, bits_walk_len, closed_evs,
  filled_two, firstB_eq, flEv, hideRun_later, hideRun_ok, inRounds_place, leaves_r, leaves_vars,
  lsOf, others_two, placeOf, r5_h4, r5_h5, r5_zb0, r5_zb1, ran_bits2, ran_leaves, rds_evs, sBit,
  sBit_eq, shown_of_hideRun, sizes_evs, took, took_later, took_sized, zdL_map
The comments on the declarations are the library's, under the same swap: where they say "run" or
"view", read: on a tape.

Limits. What is proved here is proved of the flat functions alone, and a flat function tests less of
the plan than the program's routine (the paragraph "Not claimed" in the head of
OnBytes/K/Kc/Flat.lean). Nothing is said where a function refuses. A tie: it has no error term. If
the source file turns, this copy does not follow by itself. In the list of names a use by dot
notation on a hypothesis is not seen, and a short name may stand once too often. That no routine
in a context is reached from a statement or a proof here is meant, and is not shown in this
library.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoR5
import Johnson.Top.H.FlPort.Kit
import Johnson.Top.H.FlPort.FoR5Run
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun
import Johnson.Top.H.FlPort.FoTieRun
import Johnson.Top.H.FlPort.FoRds
import Johnson.Top.H.FlPort.FoHeard
import Johnson.Top.H.FlPort.PscRounds

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- What follows from the eight lines. -/
structure R5Is {P : Type} (N : Nums P K) (m d : ℕ) (rho : Array E) (C : Aff) (pt : List K)
    (F F8 : Fork) (c c8 : Tape) (lv : Psc) (zb0 zb1 : Array E) (sBit : ℕ) (row : Aff)
    (D : R5D) : Prop where
  evs : Evs (D.evs m d rho) c c8
  rds : Rds (D.evs m d rho)
  closed : Closed ρ (D.evs m d rho)
  sizes : (flEv ρ (D.evs m d rho)).map (fun r => (r.1.length, r.2.length)) =
    (1, 1) :: ((zdL m d rho).map fun p => (p.2 - 1, 1)) ++ ((0, m) :: (1, 1) ::
      ((zdB D.ptZ).map fun p => (p.2 - 1, 1)) ++ [(2, 1), (1, 0)])
  target : F.publicPart C = some D.tgL
  fitsL : FitsA (zdL m d rho) D.rsL
  fitsB : FitsA (zdB D.ptZ) D.rsB
  sizeY : D.sentY.size = 2
  sizeV : D.v.size = 1
  sizeZ : D.ptZ.size = m
  h4 : ∀ l, takeSc (flEv ρ (D.evs m d rho ++ l)) (ρ.val D.tgL) (inRounds N.oE pt) false =
    (D.cls ρ m d rho C F.next, ([], rdA ρ D.ptZ) ::
      (flH ρ D.muB D.epsB D.rsB' (some D.v.toList) ++ flEv ρ l))
  h5 : ∀ rest, takeSc (flH ρ D.muB D.epsB D.rsB' (some D.v.toList) ++ rest) 0
    (inRounds N.oB (rdA ρ D.ptZ) ++ [0]) true = (D.bitsSc ρ m d rho F.next, rest)
  lvEps : ρ.val lv.eps = (D.cls ρ m d rho C F.next).eps
  lvFin : ρ.val lv.claim = (D.cls ρ m d rho C F.next).fin
  lvXs : rdA ρ lv.r = (D.cls ρ m d rho C F.next).xs
  lvTarget : lv.target = D.tgL
  lvStart : lv.start = C
  lvFirst : lv.first = F.next
  lvVars : lv.vars.toList = (zdL m d rho).map fun p => OnBytes.Psc.Weight.equality p.1 p.2
  lvFlags : lv.started = true ∧ lv.ended = false ∧ lv.rowMade = false
  lvZs : ((zdL m d rho).map fun p => ρ.val p.1) = inRounds N.oE pt
  ranL : Ran lv F.next D.muL D.epsL (zdL m d rho) (lsOf D.rsL)
  ranB : Ran (D.bits2 m d rho F.next) (F.next + (1 + (m + d))) D.muB D.epsB D.zdB' D.rsB'
  zb0Is : rdA ρ zb0 = (byVar N.oE (D.cls ρ m d rho C F.next).xs).reverse
  zb1Is : rdA ρ zb1 = (byVar N.oB (D.bitsSc ρ m d rho F.next).xs).reverse
  sBitIs : sBit = F.next + (1 + (m + d)) + (1 + (2 * m + 2))
  next : F8.next = F.next + (1 + (m + d)) + (1 + (2 * m + 2) + 1)
  later : Later F F8
  sized : Sized F8
  same : Same (took F (1 + (m + d) + (1 + (2 * m + 2) + 1))) F8
  filled : ∀ j, Filled F8 j ↔ Filled F j ∨
    (F.next + (1 + (m + d)) ≤ j ∧ j < F.next + (1 + (m + d)) + (1 + (2 * m + 2) + 1))
  others : ∀ j, (j < F.next + (1 + (m + d)) ∨
      F.next + (1 + (m + d)) + (1 + (2 * m + 2) + 1) ≤ j) →
    F8.vp.getD j zeroE = F.vp.getD j zeroE ∧ F8.mf.getD j zeroE = F.mf.getD j zeroE
  stretch : Stretch (took F (1 + (m + d))) F8 (1 + (2 * m + 2) + 1)
  under : Filled F8 sBit ∧ F8.vp.getD sBit zeroE = D.v.getD 0 zeroE ∧
    F8.mf.getD sBit zeroE = D.beta
  rowIs : row = (D.bits2 m d rho F.next).rowForm
    (subE (mulE (D.v.getD 0 zeroE) (D.v.getD 0 zeroE)) (D.v.getD 0 zeroE)) {}
  fill : ∃ F6, (took F (1 + (m + d) + (1 + (2 * m + 2) + 1))).hideRun sBit D.v D.beta = some F6 ∧
    F6.shown sBit = some (D.v.getD 0 zeroE) ∧
    F6.hideRun (F.next + (1 + (m + d)))
      (Array.replicate (D.bits2 m d rho F.next).walk.1.length zeroE) (subE zeroE oneE) = some F8

/-- The eight lines, each as a run that returns. -/
theorem r5 {P : Type} (N : Nums P K) (m d : ℕ) (rho : Array E) (C : Aff) (pt : List K)
    (hE : N.oE = (List.range m).map (FoNums.placeOf m))
    (hO : N.oB = (List.range m).map (FoNums.placeOf m))
    (hpt : rdA ρ rho = pt.reverse) (hs : rho.size = m) (hd : d ≤ m)
    (F F1 F2 F3 F4 F5 F6 F7 F8 : Fork) (c c1 c2 c3 c4 c5 c6 c7 c8 : Tape)
    (lv0 lv b0 b1 b2 b3 : Psc) (zb0 zb1 z : Array E) (sBit : ℕ) (vBit : E) (row : Aff)
    (hF : Sized F) (hz : z.size = m)
    (h1 : Fl.pscBegin C F c = .ok ((lv0, F1), c1))
    (h2 : Fl.roundsIn .eq lv0
      ((List.range m).map fun j => (rho.getD j zeroE, if j < d then 2 else 1)) F1 c1 =
        .ok (((zb0, lv), F2), c2))
    (h3 : Fl.point .zero m F2 c2 = .ok ((z, F3), c3))
    (h4 : Fl.pscBegin (Aff.ofConst zeroE) F3 c3 = .ok ((b0, F4), c4))
    (h5 : Fl.roundsIn .eq2 b0 (z.reverse.toList.map fun z => (z, 0)) F4 c4 =
      .ok (((zb1, b1), F5), c5))
    (h6 : Fl.pscEnds b1 2 1 F5 c5 = .ok (((sBit, b2), F6), c6))
    (h7 : Fl.shown sBit F6 c6 = .ok ((vBit, F7), c7))
    (h8 : Fl.pscRow b2 (subE (mulE vBit vBit) vBit) {} F7 c7 = .ok (((row, b3), F8), c8)) :
    ∃ D : R5D, D.ptZ = z ∧ R5Is ρ N m d rho C pt F F8 c c8 lv zb0 zb1 sBit row D := by
  obtain ⟨D, a1, a2, a3, a4, a5, rfl, a7, rfl, rfl, rfl, a11, rfl, a13, a14, a15, rfl⟩ :=
    leavesBits_ok m d rho C F F1 F2 F3 F4 F5 F6 F7 F8 c c1 c2 c3 c4 c5 c6 c7 c8 lv0 lv b0 b1 b2 b3
      zb0 zb1 z sBit vBit row h1 h2 h3 h4 h5 h6 h7 h8
  clear h1 h2 h3 h4 h5 h6 h7 h8
  have hsB := sBit_eq D m d rho F.next hd hz
  have hn : D.sBit m d rho F.next + 1 - F.next = 1 + (m + d) + (1 + (2 * m + 2) + 1) := by omega
  rw [hn] at a13
  have hT : Sized (took F (1 + (m + d) + (1 + (2 * m + 2) + 1))) := took_sized _ hF
  obtain ⟨s1, z1, in1, _⟩ := hideRun_ok _ _ _ _ _ hT a13
  obtain ⟨s2, z2, _, _⟩ := hideRun_ok _ _ _ _ _ z1 a15
  obtain rfl := shown_of_hideRun hT a13 (by omega) a14
  have hfB : (D.bits2 m d rho F.next).first = F.next + (1 + (m + d)) :=
    firstB_eq m d rho F.next hd
  rw [hfB] at a15
  have hwl := bits_walk_len ρ D m d rho F.next hz a3 a4
  have hsB' : sBit = F.next + (1 + (m + d)) + (1 + (2 * m + 2)) := a11.trans hsB
  have hfl := fun j => filled_two (a := F.next + (1 + (m + d))) (L := 1 + (2 * m + 2)) hF a5
    (by rw [Array.size_replicate, hwl]) (hsB' ▸ a13) a15 j
  refine ⟨D, rfl, ?_⟩
  exact
    { evs := a7
      rds := rds_evs D m d rho
      closed := closed_evs ρ D m d rho
      sizes := sizes_evs ρ D m d rho a2 a3 a4 a5 hz
      target := a1
      fitsL := a2
      fitsB := a3
      sizeY := a4
      sizeV := a5
      sizeZ := hz
      h4 := fun l => r5_h4 ρ D m d rho N hE pt hpt hs a2 a3 C F.next l
      h5 := fun rest => r5_h5 ρ D m d rho N hO hz a3 a4 F.next rest
      lvEps := rfl
      lvFin := rfl
      lvXs := by
        rw [leaves_r]
        simp [rdA, R5D.cls]
      lvTarget := rfl
      lvStart := rfl
      lvFirst := rfl
      lvVars := leaves_vars D m d rho C F.next
      lvFlags := ⟨rfl, rfl, rfl⟩
      lvZs := by
        have hl : pt.length = m := by
          have := congrArg List.length hpt
          simpa [rdA, hs] using this.symm
        rw [hE, inRounds_place m pt hl, ← hpt, zdL_map ρ m d rho hs]
      ranL := ran_leaves D m d rho C F.next a2
      ranB := hfB ▸ ran_bits2 D m d rho F.next a3 a4
      zb0Is := by rw [hE]; exact r5_zb0 ρ D m d rho a2 C F.next
      zb1Is := by rw [hO]; exact r5_zb1 ρ D m d rho hz a3 F.next
      sBitIs := hsB'
      next := by
        rw [s2.next, s1.next]
        show F.next + _ = _
        omega
      later := (took_later F _).trans ((hideRun_later hT a13).trans (hideRun_later z1 a15))
      sized := z2
      same := s1.trans s2
      filled := fun j => by
        rw [hfl j]
        constructor <;> rintro (h | h)
        · exact Or.inl h
        · exact Or.inr ⟨h.1, by omega⟩
        · exact Or.inl h
        · exact Or.inr ⟨h.1, by omega⟩
      others := fun j hj => others_two (a := F.next + (1 + (m + d))) (L := 1 + (2 * m + 2)) hF a5
        (by rw [Array.size_replicate, hwl]) (hsB' ▸ a13) a15 j (by omega)
      stretch :=
        { same := by
            have e : took (took F (1 + (m + d))) (1 + (2 * m + 2) + 1) =
                took F (1 + (m + d) + (1 + (2 * m + 2) + 1)) := by
              simp [took, Nat.add_assoc]
            rw [e]
            exact s1.trans s2
          filled := fun j => by
            rw [hfl j]
            constructor <;> rintro (h | h)
            · exact Or.inl h
            · exact Or.inr ⟨h.1, by show j < F.next + _ + _; omega⟩
            · exact Or.inl h
            · exact Or.inr ⟨h.1, by have : j < F.next + (1 + (m + d)) + _ := h.2; omega⟩
          out := fun j hj => others_two (a := F.next + (1 + (m + d))) (L := 1 + (2 * m + 2)) hF a5
            (by rw [Array.size_replicate, hwl]) (hsB' ▸ a13) a15 j (by
              have : j < F.next + (1 + (m + d)) ∨
                F.next + (1 + (m + d)) + (1 + (2 * m + 2) + 1) ≤ j := hj
              omega) }
      under := by
        have h0 := in1 0 (by omega)
        rw [Nat.add_zero] at h0
        have k := (hideRun_later z1 a15).keep sBit h0.2.2.1
        exact ⟨k.1, k.2.1.trans h0.2.2.2.1, k.2.2.trans h0.2.2.2.2⟩
      rowIs := rfl
      fill := ⟨F6, a13, a14, a15⟩ }

end

end Fo.Tp
