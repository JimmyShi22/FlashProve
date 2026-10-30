-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoR5.lean.
The layer of the table's leaves and the test on bits in the byte-level lookup routine: one statement
for every run that returns.

The eight lines of OnBytes.Model.Forest.pad that run the sumcheck over the leaves of the table's
side, draw a fresh point and run the test that the planes hold bits, are taken here each as a run
that returns. `r5` gathers what follows, for every reading ρ of the byte-level field in a
commutative ring and every record N of the flat function's public numbers whose two last orders are
the byte-level routine's:

 * the calls of the channel's routines that were made; that they are a row of rounds and leave no
   message open; how many elements each round sends and draws;
 * the two last stages of the flat function's trace on these calls read as rounds, in the form in
   which the trace is put together (`takeSc ... = (cls, ([], zero) :: ...)` and `takeSc ... = (bits,
   ...)`), with whatever calls follow;
 * the state of the leaves' sumcheck that the routine returns, field by field: its factor, last
   claim and challenges read are those of `cls`; its target, start, first slot, weights and flags;
 * the two arrays of challenges: the two points by coordinate, reversed;
 * the slot of the shown value, and what lies under it: it is filled, what was shown is the value
   that was sent, and the factor of its mask entry is the further variable's challenge;
 * the state of the sub-proof: which slots were taken; that it is a later state in which all arrays
   keep their sizes; that it differs from the state before, with these slots taken, at most in what
   lies under the slots; which slots exactly are filled: those that were, and all slots of the
   bits' sumcheck; none of the leaves' sumcheck; what lies under every other slot stays;
 * the claim of the bits' sumcheck as the form that the routine makes of the state written out (its
   value is read elsewhere).

Premises beside the eight runs: the arrays of the state before have their sizes; the array of the
table's point has m places and is the point by coordinate reversed; the fresh point has m
coordinates (a run on a view gives that); d ≤ m.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoR5Ends
import OnBytes.Tie.Pv.Lookup.Forest.FoRds
import OnBytes.Tie.Pv.Lookup.Forest.FoWalk
import OnBytes.Tie.Pv.Psc.PscWhole
import OnBytes.Tie.Pv.Lookup.Forest.FoStretch

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie

section
variable {K : Type} [CommRing K] (ρ : Reading K)

private theorem open_vars : ∀ (zd : List (E × ℕ)) (rs : List (Array E × E)) (l : List Ev),
    openAfter ρ [] (evVars zd rs ++ l) = openAfter ρ [] l
  | [], [], _ => rfl
  | _ :: zd, _ :: rs, l => open_vars zd rs l
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl

/-- The calls of the stretch leave no message open. -/
theorem closed_evs (D : R5D) (m d : ℕ) (rho : Array E) : Closed ρ (D.evs m d rho) := by
  unfold Closed R5D.evs
  simp only [List.cons_append, List.nil_append, openAfter]
  rw [open_vars]
  simp only [openAfter]
  rw [open_vars]
  rfl

/-- How many elements each round of the variables sends and draws. -/
private theorem sizes_vars : ∀ (zd : List (E × ℕ)) (rs : List (Array E × E)), FitsA zd rs →
    (flR ρ (lsOf rs)).map (fun r => (r.1.length, r.2.length)) = zd.map fun p => (p.2 - 1, 1)
  | [], [], _ => rfl
  | p :: zd, r :: rs, h => by
    have e : (r.1.toList.map ρ.val).length = p.2 - 1 := by
      rw [List.length_map, Array.length_toList]
      have := h.1
      omega
    show ((r.1.toList.map ρ.val).length, 1) :: _ = (p.2 - 1, 1) :: _
    rw [e]
    exact congrArg ((p.2 - 1, 1) :: ·) (sizes_vars zd rs h.2)
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- How many elements each round of the stretch sends and draws. -/
theorem sizes_evs (D : R5D) (m d : ℕ) (rho : Array E) (hL : FitsA (zdL m d rho) D.rsL)
    (hB : FitsA (zdB D.ptZ) D.rsB) (hY : D.sentY.size = 2) (hV : D.v.size = 1)
    (hZ : D.ptZ.size = m) :
    (flEv ρ (D.evs m d rho)).map (fun r => (r.1.length, r.2.length)) =
      (1, 1) :: ((zdL m d rho).map fun p => (p.2 - 1, 1)) ++ ((0, m) :: (1, 1) ::
        ((zdB D.ptZ).map fun p => (p.2 - 1, 1)) ++ [(2, 1), (1, 0)]) := by
  have e := flEv_evs ρ D m d rho hL hB []
  rw [List.append_nil] at e
  rw [e]
  simp only [flH, R5D.rsB', flR, List.map_append, List.map_cons, List.map_nil, List.append_nil,
    List.cons_append, List.length_cons, List.length_nil, List.length_map, Array.length_toList,
    rdA, hY, hV, hZ]
  have a := sizes_vars ρ _ _ hL
  have b := sizes_vars ρ _ _ hB
  simp only [flR, List.map_map] at a b
  simp only [List.map_map, flEv, flGo]
  rw [a, b]
  simp

/-- What a slot shows right behind its filling. -/
theorem shown_of_hideRun {F G : Fork} {first : ℕ} {v : Array E} {f x : E} (hF : Sized F)
    (h : F.hideRun first v f = some G) (hv : 0 < v.size) (hx : G.shown first = some x) :
    x = v.getD 0 zeroE := by
  obtain ⟨_, _, hin, _⟩ := hideRun_ok F G first v f hF h
  have h0 := (hin 0 hv).2.2.2.1
  rw [Nat.add_zero] at h0
  unfold Fork.shown at hx
  split at hx
  · rw [← h0]
    exact (Option.some.inj hx).symm
  · exact absurd hx (by simp)

private theorem rds_vars : ∀ (zd : List (E × ℕ)) (rs : List (Array E × E)) {l : List Ev}, Rds l →
    Rds (evVars zd rs ++ l)
  | [], [], _, h => h
  | _ :: zd, _ :: rs, _, h => .read _ _ _ _ (rds_vars zd rs h)
  | [], _ :: _, _, h => h
  | _ :: _, [], _, h => h

/-- The calls of the stretch are a row of rounds. -/
theorem rds_evs (D : R5D) (m d : ℕ) (rho : Array E) : Rds (D.evs m d rho) :=
  .sum _ _ _ (rds_vars _ _ (.point _ _ _ (.sum _ _ _ (rds_vars _ _
    (.readNZ _ _ _ _ (.values _ _ _ .nil))))))

/-- The state of the leaves' sumcheck, in the words for a sumcheck that has run so far. -/
theorem ran_leaves (D : R5D) (m d : ℕ) (rho : Array E) (C : Aff) (first : ℕ)
    (hL : FitsA (zdL m d rho) D.rsL) :
    Ran (D.leaves m d rho C first) first D.muL D.epsL (zdL m d rho) (lsOf D.rsL) where
  first_eq := rfl
  eps_eq := rfl
  vars_eq := by simp [R5D.leaves, after]
  r_eq := by simp [R5D.leaves, after, lsOf]
  claim_eq := rfl
  fits := fits_of _ _ hL

/-- The state of the bits' sumcheck behind the round in the further variable. -/
theorem ran_bits2 (D : R5D) (m d : ℕ) (rho : Array E) (first : ℕ)
    (hB : FitsA (zdB D.ptZ) D.rsB) (hY : D.sentY.size = 2) :
    Ran (D.bits2 m d rho first) (firstB m d rho first) D.muB D.epsB D.zdB' D.rsB' where
  first_eq := rfl
  eps_eq := rfl
  vars_eq := by
    simp [R5D.bits2, R5D.bits1, after, R5D.zdB', eqW, OnBytes.Psc.Weight.atZero]
  r_eq := by simp [R5D.bits2, R5D.bits1, after, R5D.rsB', lsOf]
  claim_eq := by
    show _ = OnBytes.Psc.claimAfter (eqW D.zdB') D.rsB' (addE D.muB (mulE D.epsB zeroE))
    exact (Fo.claimAfter_snoc (zdB D.ptZ) (lsOf D.rsB) (zeroE, 3) (D.sentY.toList, D.beta) _
      (fits_of _ _ hB)).symm
  fits := Fo.fits_snoc (zdB D.ptZ) (lsOf D.rsB) (zeroE, 3) (D.sentY.toList, D.beta)
    (fits_of _ _ hB) (by
      show D.sentY.toList.length + 1 = 3
      rw [Array.length_toList, hY])

theorem zdB_snd (ptZ : Array E) : (zdB ptZ).map (·.2) = List.replicate ptZ.size 3 := by
  refine List.ext_getElem (by simp [zdB, zdOf]) fun i h1 h2 => ?_
  simp [zdB, zdOf, roundValues]

include ρ in
/-- The hiding polynomial of the bits' sumcheck has 1 + (2 m + 2) coefficients. -/
theorem bits_walk_len (D : R5D) (m d : ℕ) (rho : Array E) (first : ℕ) (hZ : D.ptZ.size = m)
    (hB : FitsA (zdB D.ptZ) D.rsB) (hY : D.sentY.size = 2) :
    (D.bits2 m d rho first).walk.1.length = 1 + (2 * m + 2) := by
  have h := congrArg List.length (ran_walk ρ (ran_bits2 D m d rho first hB hY)).1
  rw [List.length_map] at h
  have e : ((D.zdB'.zip D.rsB').map fun x => (x.1.2, ρ.val x.2.2)) =
      Cb.Fo.Walk.pairs (List.replicate m 2 ++ [2]) (D.rsB'.map fun r => ρ.val r.2) := by
    have e2 : (List.replicate m 2 ++ [2]).map (· + 1) = D.zdB'.map (·.2) := by
      simp [R5D.zdB', zdB_snd, hZ]
    unfold Cb.Fo.Walk.pairs
    rw [e2, List.zip_map]
    rfl
  rw [h, e, Cb.Fo.Walk.walk_length _ _ (by simp) (by
    simp [R5D.rsB', lsOf, fitsA_length hB, zdB_length, hZ])]
  simp
  omega

/-- Which slots two fillings in a row fill: a run of L slots from a on, and the slot behind it. -/
theorem filled_two {F F6 F8 : Fork} {a L n : ℕ} {v w : Array E} {f g : E} (hF : Sized F)
    (hv : v.size = 1) (hw : w.size = L)
    (h1 : (took F n).hideRun (a + L) v f = some F6) (h2 : F6.hideRun a w g = some F8) (j : ℕ) :
    Filled F8 j ↔ Filled F j ∨ (a ≤ j ∧ j < a + L + 1) := by
  obtain ⟨_, z1, in1, out1⟩ := hideRun_ok _ _ _ _ _ (took_sized n hF) h1
  obtain ⟨_, _, in2, out2⟩ := hideRun_ok _ _ _ _ _ z1 h2
  by_cases c1 : a ≤ j ∧ j < a + L
  · have := (in2 (j - a) (by omega)).2.2.1
    rw [show a + (j - a) = j by omega] at this
    exact ⟨fun _ => Or.inr ⟨c1.1, by omega⟩, fun _ => this⟩
  · rw [(out2 j (by omega)).2.2]
    by_cases c2 : j = a + L
    · subst c2
      have := (in1 0 (by omega)).2.2.1
      rw [Nat.add_zero] at this
      exact ⟨fun _ => Or.inr ⟨by omega, by omega⟩, fun _ => this⟩
    · rw [(out1 j (by omega)).2.2]
      exact ⟨fun h => Or.inl h, fun h => h.elim id fun h' => absurd h' (by omega)⟩

/-- What lies under every other slot, free or filled, stays. -/
theorem others_two {F F6 F8 : Fork} {a L n : ℕ} {v w : Array E} {f g : E} (hF : Sized F)
    (hv : v.size = 1) (hw : w.size = L)
    (h1 : (took F n).hideRun (a + L) v f = some F6) (h2 : F6.hideRun a w g = some F8) (j : ℕ)
    (hj : j < a ∨ a + L + 1 ≤ j) :
    F8.vp.getD j zeroE = F.vp.getD j zeroE ∧ F8.mf.getD j zeroE = F.mf.getD j zeroE := by
  obtain ⟨_, z1, _, out1⟩ := hideRun_ok _ _ _ _ _ (took_sized n hF) h1
  obtain ⟨_, _, _, out2⟩ := hideRun_ok _ _ _ _ _ z1 h2
  have o1 := out1 j (by omega)
  have o2 := out2 j (by omega)
  exact ⟨o2.1.trans o1.1, o2.2.1.trans o1.2.1⟩

/-- What follows from the eight lines. -/
structure R5Is {P : Type} (N : Nums P K) (m d : ℕ) (rho : Array E) (C : Aff) (pt : List K)
    (F F8 : Fork) (c c8 : Ctx) (lv : Psc) (zb0 zb1 : Array E) (sBit : ℕ) (row : Aff)
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
    (F F1 F2 F3 F4 F5 F6 F7 F8 : Fork) (c c1 c2 c3 c4 c5 c6 c7 c8 : Ctx)
    (lv0 lv b0 b1 b2 b3 : Psc) (zb0 zb1 z : Array E) (sBit : ℕ) (vBit : E) (row : Aff)
    (hF : Sized F) (hz : z.size = m)
    (h1 : pscBegin C F c = .ok ((lv0, F1), c1))
    (h2 : roundsIn .eq lv0
      ((List.range m).map fun j => (rho.getD j zeroE, if j < d then 2 else 1)) F1 c1 =
        .ok (((zb0, lv), F2), c2))
    (h3 : SubM.point .zero m F2 c2 = .ok ((z, F3), c3))
    (h4 : pscBegin (Aff.ofConst zeroE) F3 c3 = .ok ((b0, F4), c4))
    (h5 : roundsIn .eq2 b0 (z.reverse.toList.map fun z => (z, 0)) F4 c4 =
      .ok (((zb1, b1), F5), c5))
    (h6 : pscEnds b1 2 1 F5 c5 = .ok (((sBit, b2), F6), c6))
    (h7 : SubM.shown sBit F6 c6 = .ok ((vBit, F7), c7))
    (h8 : pscRow b2 (subE (mulE vBit vBit) vBit) {} F7 c7 = .ok (((row, b3), F8), c8)) :
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
end Fo
