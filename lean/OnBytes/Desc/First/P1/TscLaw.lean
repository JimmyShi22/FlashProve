-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/P1/TscLaw.lean: a token sumcheck, round by round, over `Fl.tscIn`
(OnBytes/K/Kc/Flat.lean), at a summand that is a sum of products of two extensions under
coefficients fixed before the run, the further variable with three coefficients (degreeInY = 2),
with everything read off the tape by functions. Statements and proofs.

  `tscLoop_tape`, `tscIn_tape`: the facts of `tscLoop_spec` and `tscIn_spec` (TscKit.lean), and the
    tape written out round by round. The claimed sum cl and the sum mu0 of the hiding polynomial
    are sent in ONE round, cl first, and eps is drawn behind both.
  `tapeCl`, `tapeMu2`: the first and the second element that the tape's first round sent.
  `tapeT`: the sumcheck's target as the function computes it from cl: 0 + 1 * cl in the program's
    own arithmetic. It reads as cl reads.
  `tsc_law`. FIXED FIRST: the point P and the number lt of its coordinates that are summed over; n
    tables over these variables, the first bit for the first coordinate; the terms; all mask
    entries; the ledger F in front. THEN there are: for each claimed sum as shown and each mu0 at
    most one bad eps; for each round fewer than three bad challenges; such that, wherever the
    function returns on a tape t: for every later ledger H AND ALL ENTRIES OF THE READS, which so
    come behind the sets, if in H's world the sumcheck's own slots hold their mask entries: if the
    row (the record's `rowForm` at an end term S0) is 0, S0 is the summand on what was shown, the
    hidden end values are the tables' extensions at the challenges, and no bad element was drawn,
    then the hidden claimed sum is the sum over the cube, under the equality weights of P, of the
    terms' products of the tables.

There is no "there is" behind the return: the claimed sum, mu0, eps and the rounds are read off the
tape by functions. The law also says what is left of the tape. The claimed sum is sent in the
message in front of eps, so the bad eps may hang on what was shown for it: it is a letter of
`badE`. The row is made later than the hearing (in a run of claims): that the sumcheck's own slots
then hold their mask entries (0 shown, the factor -1) is a premise here.

A test of the statement: the cheap choice ({0} as the set of bad eps, no bad challenge) fails for
the reason given in the head of LevelLaw.lean. The tape is under "for all", eps is what its first
round drew, and a tape whose drawn element is a place where a wrong polynomial agrees with the true
one is shut out only by a set that holds that place. This is an argument in words, not a theorem.

What is not shown. One direction: from a return. That the tables, the terms and the mask were fixed
before the tape's elements were drawn is the order of the letters, not time. That
the conditions can be met together is not shown. Counts, no probabilities.
-/
import OnBytes.Desc.First.P1.TscKit
import OnBytes.Desc.First.P1.LevelLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Desc.First.P1
open OnBytes OnBytes.Model OnBytes.K.Kc Polynomial
open OnBytes.PscRun (Sized Filled hideRun_ok)

variable {K : Type} [Field K] (ρ : Reading K)

/-! ### Small things -/

theorem array_one {v : Array E} (h : v.size = 1) : ∃ c : E, v = #[c] := by
  obtain ⟨l⟩ := v
  cases l with
  | nil =>
    have h' : 0 = 1 := h
    omega
  | cons c l =>
    cases l with
    | nil => exact ⟨c, rfl⟩
    | cons d l =>
      have h' : l.length + 1 + 1 = 1 := h
      omega

theorem getD_one (c : E) : (#[c] : Array E).getD 0 zeroE = c := rfl

/-- The public part of a slot's form, as the program computes it. -/
theorem publicPart_slot_eq {G : Fork} {j : ℕ} {T : E} (h : G.publicPart (Aff.slot j) = some T) :
    T = addE zeroE (mulE oneE (G.vp.getD j zeroE)) := by
  have h' : (G.shown j).map (fun y => addE zeroE (mulE oneE y)) = some T := by
    simpa [Fork.publicPart, Aff.slot] using h
  cases hq : G.shown j with
  | none => simp [hq] at h'
  | some y =>
    rw [hq, Option.map_some] at h'
    have hy := shown_some hq
    rw [← Option.some.inj h', hy.2.2]

theorem msOf_tsc_cons (z : E) (zs : List E) (nm : Option String) (z' k : Nat) (sent : List E)
    (c : E) (rs : List FlatRound) :
    msOf (tscWs (z :: zs)) (⟨nm, z', k, sent, [c]⟩ :: rs) =
      (OnBytes.Psc.Weight.equality z 3, sent, c) :: msOf (tscWs zs) rs := rfl

theorem drop_tsc {α : Type} (r0 : α) (rs : List α) (a b : α) (u : List α) :
    (r0 :: (rs ++ a :: b :: u)).drop (rs.length + 3) = u :=
  drop_cons_append r0 rs (a :: b :: u) 2

/-! ### The functions, with the tape -/

theorem tscLoop_tape : ∀ {zs : List E} {r r' : Array E} {p p' : Psc} {F G : Fork} {t u : Tape},
    Fl.tscLoop zs r p F t = some ((r', p'), G, u) →
    ∃ rs : List FlatRound, t = rs ++ u ∧ rs.length = zs.length ∧
      (∀ x ∈ rs, x.name = some Model.RoundName.pscRound.name ∧ x.nz = 0 ∧ x.drawn.length = 1) ∧
      (msOf (tscWs zs) rs).map (·.1) = tscWs zs ∧ (∀ m ∈ msOf (tscWs zs) rs, Held m.1) ∧
      (∀ m ∈ msOf (tscWs zs) rs, m.2.1.length + 1 = m.1.d) ∧ p' = runP p (msOf (tscWs zs) rs) ∧
      r'.toList = r.toList ++ (msOf (tscWs zs) rs).map (·.2.2) ∧
      G = { F with next := F.next + 2 * zs.length }
  | [], r, r', p, p', F, G, t, u, h => by
    unfold Fl.tscLoop at h
    obtain ⟨he, rfl, rfl⟩ := pure_some.mp h
    injection he with e1 e2
    have e0 : msOf (tscWs []) [] = [] := rfl
    refine ⟨[], rfl, rfl, by simp, ?_⟩
    rw [e0]
    exact ⟨rfl, by simp, by simp, e2.symm, by simp [e1], rfl⟩
  | z :: zs, r, r', p, p', F, G, t, u, h => by
    unfold Fl.tscLoop at h
    obtain ⟨x, G2, u2, h2, k1⟩ := bind_some.mp h
    obtain ⟨c, q⟩ := x
    obtain ⟨hh, sent, k, hl, rfl, rfl, ht⟩ := roundIn_eq2_tape h2
    obtain ⟨rs, b0, b1, b2, a1, a2, a3, a4, a5, a6⟩ := tscLoop_tape k1
    have et := ht.trans (congrArg
      (List.cons (⟨some Model.RoundName.pscRound.name, 0, k, sent, [c]⟩ : FlatRound)) b0)
    refine ⟨⟨some Model.RoundName.pscRound.name, 0, k, sent, [c]⟩ :: rs, et, ?_, ?_, ?_⟩
    · rw [List.length_cons, List.length_cons, b1]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨rfl, rfl, rfl⟩
      · exact b2 x hx
    rw [msOf_tsc_cons]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [List.map_cons, a1]
      rfl
    · intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hh
      · exact a2 m hm
    · intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · show sent.length + 1 = 3
        omega
      · exact a3 m hm
    · rw [runP_cons]
      exact a4
    · rw [a5, List.map_cons]
      simp
    · rw [a6]
      show ({ F with next := F.next + 2 + 2 * zs.length } : Fork) = _
      have : F.next + 2 + 2 * zs.length = F.next + 2 * (z :: zs).length := by
        rw [List.length_cons]
        omega
      rw [this]

/-- **Where a token sumcheck returns, with the tape.** -/
theorem tscIn_tape {P : Array E} {lt n dY : Nat} {F G : Fork} {t u : Tape} {o : Tsc}
    (h : Fl.tscIn P lt n dY F t = some (o, G, u)) :
    lt ≤ P.size ∧ ∃ (T cl mu0 eps : E) (rs : List FlatRound) (sentY : List E) (beta : E)
      (w0 wY wV : Nat) (ms : List Rnd) (y : Rnd) (v1 v : Array E) (G0 : Fork),
      t = ⟨some Model.RoundName.pscEpsilon.name, 0, w0, [cl, mu0], [eps]⟩ ::
        (rs ++ ⟨some Model.RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
          ⟨some Model.RoundName.pscValues.name, 0, wV, v.toList, []⟩ :: u) ∧
      rs.length = (P.toList.take lt).length ∧
      (∀ x ∈ rs, x.name = some Model.RoundName.pscRound.name ∧ x.nz = 0 ∧ x.drawn.length = 1) ∧
      ms = msOf (tscWs (P.toList.take lt)) rs ∧
      y = (OnBytes.Psc.Weight.atZero (dY + 1), sentY, beta) ∧ v1 = #[cl] ∧
      o.sCl = F.next ∧ v1.size = 1 ∧
      ({ F with next := F.next + 1 } : Fork).hideRun F.next v1 oneE = some G0 ∧
      G0.publicPart (Aff.slot F.next) = some T ∧
      ms.map (·.1) = tscWs (P.toList.take lt) ∧ y.1 = OnBytes.Psc.Weight.atZero (dY + 1) ∧
      (∀ m ∈ ms ++ [y], Held m.1) ∧ (∀ m ∈ ms ++ [y], m.2.1.length + 1 = m.1.d) ∧
      o.p.vars.toList = tscWs (P.toList.take lt) ++ [OnBytes.Psc.Weight.atZero (dY + 1)] ∧
      o.p.r.toList = (ms ++ [y]).map (·.2.2) ∧
      o.p.claim = claimAfter (ms ++ [y]) (addE mu0 (mulE eps T)) ∧
      o.p.target = T ∧ o.p.eps = eps ∧ o.p.start = Aff.slot F.next ∧ o.p.first = G0.next ∧
      o.r.toList = ms.map (·.2.2) ∧
      o.sEnd = G0.next + 1 + 2 * (P.toList.take lt).length + dY ∧ v.size = n ∧
      ({ G0 with next := G0.next + 1 + 2 * (P.toList.take lt).length + dY + n } : Fork).hideRun
        o.sEnd v y.2.2 = some G := by
  unfold Fl.tscIn at h
  obtain ⟨o1, G1, u1, h1, k1⟩ := bind_some.mp h
  obtain ⟨x, G2, u2, h2, k2⟩ := bind_some.mp k1
  obtain ⟨sEnd, p2⟩ := x
  obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k2
  unfold Fl.tscRounds at h1
  obtain ⟨_, G3, u3, h3, k3⟩ := bind_some.mp h1
  obtain ⟨hlt, rfl, rfl⟩ := must_some.mp h3
  obtain ⟨sCl, G4, u4, h4, k4⟩ := bind_some.mp k3
  obtain ⟨rfl, v1, hv1, ht4, _, hG0⟩ := claimsIn_spec h4
  obtain ⟨p0, G5, u5, h5, k5⟩ := bind_some.mp k4
  obtain ⟨T, mu0, eps, w0, hT, rfl, rfl, ht5⟩ := pscBegin_tape h5
  obtain ⟨x, G6, u6, h6, k6⟩ := bind_some.mp k5
  obtain ⟨r, p1⟩ := x
  obtain ⟨rs, c0, c1, c2, a1, a2, a3, rfl, a5, rfl⟩ := tscLoop_tape h6
  obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k6
  obtain ⟨hY, sentY, beta, v, wY, wV, b1, b2, rfl, rfl, hG, ht2⟩ := pscEnds_tape h2
  obtain ⟨cl, hcl⟩ := array_one hv1
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := endP_spec
    { target := T, first := G4.next, eps := eps, claim := addE mu0 (mulE eps T),
      start := Aff.slot F.next, started := true } (msOf (tscWs (P.toList.take lt)) rs)
    (OnBytes.Psc.Weight.atZero (dY + 1), sentY, beta)
  refine ⟨by simpa using hlt, T, cl, mu0, eps, rs, sentY, beta, w0, wY, wV,
    msOf (tscWs (P.toList.take lt)) rs, (OnBytes.Psc.Weight.atZero (dY + 1), sentY, beta),
    v1, v, G4, ?_, c1, c2, rfl, rfl, hcl, rfl, hv1, hG0, hT, a1, rfl, ?_, ?_, ?_, e2, e3, e5, e6,
    e4, e7, ?_, rfl, b2, hG⟩
  · rw [ht4, ht5, c0, ht2, hcl]
    rfl
  · intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact a2 m hm
    · rw [List.mem_singleton] at hm
      rw [hm]
      exact hY
  · intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact a3 m hm
    · rw [List.mem_singleton] at hm
      rw [hm]
      show sentY.length + 1 = dY + 1
      omega
  · exact e1.trans (by
      rw [List.map_append, a1]
      rfl)
  · rw [a5]
    rfl

/-! ### What is read off a tape -/

/-- The first element that the tape's first round has to send; 0 if there is none. -/
def tapeCl (t : Tape) : E := (t.head?.map fun r => r.sent.headD zeroE).getD zeroE

/-- The second element that the tape's first round has to send; 0 if there is none. -/
def tapeMu2 (t : Tape) : E := (t.head?.map fun r => r.sent.tail.headD zeroE).getD zeroE

/-- The sumcheck's target, as the function computes it from the claimed sum that was sent. -/
def tapeT (t : Tape) : E := addE zeroE (mulE oneE (tapeCl t))

theorem tapeCl_cons (nm : Option String) (z w : Nat) (c : E) (s d : List E) (u : Tape) :
    tapeCl (⟨nm, z, w, c :: s, d⟩ :: u) = c := rfl

theorem tapeMu2_cons (nm : Option String) (z w : Nat) (c m : E) (s d : List E) (u : Tape) :
    tapeMu2 (⟨nm, z, w, c :: m :: s, d⟩ :: u) = m := rfl

theorem tapeT_val (t : Tape) : ρ.val (tapeT t) = ρ.val (tapeCl t) := by
  rw [tapeT, ρ.add, ρ.mul, ρ.zero, ρ.one]
  ring

/-! ### The law -/

/-- **A token sumcheck at a sum of products, over `Fl.tscIn`, read off the tape.** -/
theorem tsc_law (P : Array E) (lt n : Nat) (A : ℕ → List Bool → K) (ts : List (Term K))
    (mask : ℕ → K) (F : Fork) (hF : Sized F) :
    ∃ (badE : K → K → Finset K) (bad : K → K → K → List (K[X] × K) → K[X] → Finset K),
      (∀ c m0, (badE c m0).card ≤ 1) ∧
      (∀ c m0 eps pre g, (bad c m0 eps pre g).card <
        dAt ((tscWs (P.toList.take lt) ++ [OnBytes.Psc.Weight.atZero 3]).map (wtOf ρ))
          pre.length) ∧
      ∀ (t u : Tape) (o : Tsc) (G : Fork), Fl.tscIn P lt n 2 F t = some (o, G, u) →
        u = t.drop ((P.toList.take lt).length + 3) ∧
        o.sCl = F.next ∧ o.p.first = F.next + 1 ∧
        o.r.toList = (msOf (tscWs (P.toList.take lt)) (t.drop 1)).map (·.2.2) ∧
        o.sEnd = F.next + 1 + 1 + 2 * (P.toList.take lt).length + 2 ∧
        Fo.Later F G ∧ Sized G ∧
        ∀ (H : Fork) (S0 : E) (entry : ℕ → ℕ → ℕ → K), Fo.Later G H →
          (∀ i, i < OnBytes.Psc.hidingEntries
              (tscWs (P.toList.take lt) ++ [OnBytes.Psc.Weight.atZero 3]) →
            (H.worldOf ρ mask entry).slot (o.p.first + i) = mask (F.next + 1 + i)) →
          (o.p.rowForm S0 {}).value ρ (H.worldOf ρ mask entry) = 0 →
          ρ.val S0 = sumTerms ts (fun i => ρ.val (H.vp.getD (o.sEnd + i) zeroE)) →
          (∀ i, i < n → (H.worldOf ρ mask entry).slot (o.sEnd + i) =
            mle (P.toList.take lt).length (A i)
              ((msOf (tscWs (P.toList.take lt)) (t.drop 1)).map fun m => ρ.val m.2.2)) →
          (∀ x ∈ ts, x.2.1 < n ∧ x.2.2 < n) →
          ρ.val (tapeEps t) ∉ badE (ρ.val (tapeCl t)) (ρ.val (tapeMu2 t)) →
          (haveI := Classical.decEq K
           NoBad (bad (ρ.val (tapeCl t)) (ρ.val (tapeMu2 t)) (ρ.val (tapeEps t)))
            (movesP ρ
              (msOf (tscWs (P.toList.take lt) ++ [OnBytes.Psc.Weight.atZero 3]) (t.drop 1))
              (addE (tapeMu2 t) (mulE (tapeEps t) (tapeT t))))) →
          (H.worldOf ρ mask entry).slot o.sCl =
            tot (tscXs ρ (P.toList.take lt)) fun b => sumTerms ts fun i => A i b := by
  choose badE bad hE hB hrun using fun c : K => products_sound ρ (tscWs (P.toList.take lt))
    (held_tsc _) (tscXs ρ (P.toList.take lt)) (twos_tsc ρ _) A
    (fun i => mask (F.next + 1 + 1 + 2 * (P.toList.take lt).length + 2 + i)) ts
    (fun i => mask (F.next + 1 + i)) c (c - mask F.next) (held_atZero 3 (by omega))
  refine ⟨badE, bad, hE, hB, ?_⟩
  intro t u o G h
  obtain ⟨_, T, cl, mu0, eps, rs, sentY, beta, w0, wY, wV, ms, y, v1, v, G0, ht, hrs, _, hms, hyy,
    hv1c, hsCl, hv1, hG0, hT, a1, hy, hheld, hlens, hvars, hr, hclaim, htar, heps, hstart, hfirst,
    hor, hsEnd, hvn, hG⟩ := tscIn_tape h
  have hF' : Sized ({ F with next := F.next + 1 } : Fork) := hF
  have l0 : Fo.Later F ({ F with next := F.next + 1 } : Fork) :=
    ⟨by show F.next ≤ F.next + 1; omega, rfl, fun _ hj => ⟨hj, rfl, rfl⟩⟩
  obtain ⟨hSame0, hS0, hin0, _⟩ := hideRun_ok _ G0 F.next v1 oneE hF' hG0
  have l1 := Fo.hideRun_later hF' hG0
  have hnext : G0.next = F.next + 1 := hSame0.next
  have hS0' : Sized ({ G0 with next := G0.next + 1 + 2 * (P.toList.take lt).length + 2 + n } :
      Fork) := hS0
  have l2 : Fo.Later G0 ({ G0 with next := G0.next + 1 + 2 * (P.toList.take lt).length + 2 + n } :
      Fork) :=
    ⟨by show G0.next ≤ G0.next + 1 + 2 * (P.toList.take lt).length + 2 + n; omega, rfl,
      fun _ hj => ⟨hj, rfl, rfl⟩⟩
  obtain ⟨_, hS1, hin1, _⟩ := hideRun_ok _ G o.sEnd v y.2.2 hS0' hG
  have l3 := Fo.hideRun_later hS0' hG
  -- what the functions read off the tape
  have c9 := (hin0 0 (by omega)).2.2.2.1
  rw [Nat.add_zero, hv1c, getD_one] at c9
  have hTe : T = addE zeroE (mulE oneE cl) := by rw [publicPart_slot_eq hT, c9]
  have hwr : (tscWs (P.toList.take lt)).length = rs.length := by
    rw [tscWs, List.length_map, hrs]
  have q1 : msOf (tscWs (P.toList.take lt)) (t.drop 1) = ms := by
    rw [ht, drop_one_cons, msOf_append_same _ _ _ hwr, hms]
  have q2 : msOf (tscWs (P.toList.take lt) ++ [OnBytes.Psc.Weight.atZero 3]) (t.drop 1) =
      ms ++ [y] := by
    rw [ht, drop_one_cons, msOf_append_lit _ _ _ _ _ _ _ _ _ hwr, hms, hyy]
  have q3 : tapeMu2 t = mu0 := by rw [ht, tapeMu2_cons]
  have q4 : tapeEps t = eps := by rw [ht, tapeEps_cons]
  have q6 : tapeCl t = cl := by rw [ht, tapeCl_cons]
  have q7 : tapeT t = T := by rw [tapeT, q6, hTe]
  have q8 : ρ.val (tapeCl t) = ρ.val T := by rw [← tapeT_val, q7]
  have hu : u = t.drop ((P.toList.take lt).length + 3) := by rw [ht, ← hrs, drop_tsc]
  rw [q1, q2, q8, q7, q3, q4]
  refine ⟨hu, hsCl, by rw [hfirst, hnext], hor, by rw [hsEnd, hnext],
    ((l0.trans l1).trans l2).trans l3, hS1, ?_⟩
  intro H S0 entry lH hslots hzero hS0v hends hts hne hnb
  -- the claimed sum
  have c0 := hin0 0 (by omega)
  rw [Nat.add_zero] at c0
  have kc := (lH.keep F.next ((l2.trans l3).keep F.next c0.2.2.1).1)
  have kc' := (l2.trans l3).keep F.next c0.2.2.1
  have hTv := (publicPart_slot ρ hT).1
  have hCl : (H.worldOf ρ mask entry).slot F.next = ρ.val T - mask F.next := by
    rw [slot_worldOf, kc.2.1, kc'.2.1, kc.2.2, kc'.2.2, c0.2.2.2.2, hTv, ρ.one]
    ring
  -- what was shown for the end values
  have hshown : ∀ i, i < n → ρ.val (H.vp.getD (o.sEnd + i) zeroE) =
      mle (P.toList.take lt).length (A i) (ms.map fun m => ρ.val m.2.2) +
        ρ.val y.2.2 * mask (o.sEnd + i) := by
    intro i hi
    have q := hin1 i (by omega)
    have r := lH.keep (o.sEnd + i) q.2.2.1
    have hs := hends i hi
    rw [slot_worldOf, r.2.2, q.2.2.2.2] at hs
    rw [← hs]
    ring
  have hlen : (tscWs (P.toList.take lt)).length = (P.toList.take lt).length := by
    rw [tscWs, List.length_map]
  have hfin := hrun (ρ.val T) (H.worldOf ρ mask entry) o.p mu0 ms y S0
    (fun i => mle (tscWs (P.toList.take lt)).length (A i) (ms.map fun x => ρ.val x.2.2) +
      ρ.val y.2.2 * mask (F.next + 1 + 1 + 2 * (P.toList.take lt).length + 2 + i))
    a1 hy hlens hvars hr (by rw [hclaim, heps, htar]) (by rw [htar])
    (by rw [hstart, Aff.value_slot, hCl]) hslots hzero ?_ (fun _ => rfl)
    (by rw [heps]; exact hne) (by rw [heps, htar]; exact hnb)
  · rw [hsCl, hCl]
    exact hfin
  · rw [hS0v, hlen]
    unfold sumTerms
    refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
    have e : o.sEnd = F.next + 1 + 1 + 2 * (P.toList.take lt).length + 2 := by rw [hsEnd, hnext]
    beta_reduce
    rw [hshown x.2.1 (hts x hx).1, hshown x.2.2 (hts x hx).2, e]

end OnBytes.Desc.First.P1
