-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoTailJoin.lean.
The smallness test's claim on the key vectors of its lookup, written out by hand: the run.

The byte-level routine linJoin9 (OnBytes/Model/Tail.lean) does not call Forest.join. It gathers a
constant and a list of runs in loops, makes some tests of public numbers, and adds one claim: a form
and the runs. This file cuts a run of linJoin9 that returns into its steps.

* forIn_quiet: a loop whose every step, if it returns, leaves the state and the context as they were
  and goes on: the whole loop does so, and an invariant of the steps holds at its end.
* joinRun tl g q p: the run of piece p of call q. joinRuns tl g: all runs, call by call, piece by
  piece. joinConst tl g: the constant.
* linJoin9_cut: a run that returns is: the record is there; both calls' padding keys are 0; one call
  of t2Lin, from the state and context of the start, on the form (the constant less the hidden value
  at the end of the key side) and these runs; the mark that the claim is added. Of the routine's
  other tests (the pieces' indices, the count of the places read, Forest.paddingLaid) the statement
  keeps nothing.

Not claimed: anything on completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoRds
import OnBytes.Model.Tail

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun

/-- A loop of quiet steps. -/
theorem forIn_quiet {α β : Type} (f : α → β → SubM (ForInStep β)) (Inv : List α → β → Prop)
    (hstep : ∀ (done : List α) (a : α) (b : β) (F : Fork) (c : Ctx)
      (r : (ForInStep β × Fork) × Ctx), Inv done b → f a b F c = .ok r →
      ∃ b', r = ((ForInStep.yield b', F), c) ∧ Inv (done ++ [a]) b') :
    ∀ (l done : List α) (b : β) (F : Fork) (c : Ctx) (r : (β × Fork) × Ctx), Inv done b →
      (forIn l b f) F c = .ok r → ∃ b', r = ((b', F), c) ∧ Inv (done ++ l) b'
  | [], done, b, F, c, r, hI, h => by
    rw [List.forIn_nil] at h
    exact ⟨b, (pure_ok _ _ _ _).1 h, by rwa [List.append_nil]⟩
  | a :: l, done, b, F, c, r, hI, h => by
    rw [List.forIn_cons] at h
    obtain ⟨s, F1, c1, h1, h2⟩ := (bind_ok _ _ F c _).1 h
    obtain ⟨b', e, hI'⟩ := hstep done a b F c _ hI h1
    have x1 : s = ForInStep.yield b' := congrArg (fun x : (ForInStep β × Fork) × Ctx => x.1.1) e
    have x2 : F1 = F := congrArg (fun x : (ForInStep β × Fork) × Ctx => x.1.2) e
    have x3 : c1 = c := congrArg (fun x : (ForInStep β × Fork) × Ctx => x.2) e
    rw [x1, x2, x3] at h2
    obtain ⟨b'', e2, hI''⟩ := forIn_quiet f Inv hstep l (done ++ [a]) b' F c r hI' h2
    exact ⟨b'', e2, by rwa [List.append_assoc] at hI''⟩

/-- The run of piece p of call q, under given weights on the columns. -/
def joinRunW (tl : HTailF2) (g : Heard) (q : ℕ) (p : Piece) (w : Array E) : Run2 :=
  { tree := p.tree, row := p.row, first := p.c0,
    coef := subE zeroE (mulE (g.e.getD q zeroE)
      (eqOne ((g.zk.getD q #[]).extract 0 ((tl.zOf q).call.n - p.b)) (p.off / 2 ^ p.b))),
    w := w, n := p.Cp }

/-- The coordinates of a call's point that belong to the columns of piece p. -/
def joinZc (tl : HTailF2) (g : Heard) (q : ℕ) (p : Piece) : Array E :=
  (g.zk.getD q #[]).extract ((tl.zOf q).call.n - p.b + p.a)
    ((tl.zOf q).call.n - p.b + p.a + clog2 p.CP)

/-- The run of piece p of call q. -/
def joinRun (tl : HTailF2) (g : Heard) (q : ℕ) (p : Piece) : Run2 :=
  joinRunW tl g q p (eqTab (joinZc tl g q p))

/-- The loop over the rows of a piece turns the count of places alone. -/
theorem rowsLoop_ok (h : Shape) (q : ℕ) (p : Piece) (read : Array Nat) (F : Fork) (c : Ctx)
    (r : (Array Nat × Fork) × Ctx)
    (hr : (forIn (List.range p.Rp) read fun rr (r : Array Nat) => (do
      let r ← SubM.get
        (HTailF2.placesRead h.dT (h.iota.getD q 0) (h.first.getD q 0) (2 ^ h.iota.getD q 0 + 1) r
          (p.off + rr * p.CP) p.Cp)
      pure PUnit.unit
      pure (ForInStep.yield r) : SubM (ForInStep (Array Nat)))) F c = .ok r) :
    ∃ read', r = ((read', F), c) := by
  obtain ⟨b', e, _⟩ := forIn_quiet _ (fun _ _ => True) (fun done a b F c r _ hs => by
    obtain ⟨x, F1, c1, h1, h2⟩ := (bind_ok _ _ F c _).1 hs
    obtain ⟨x', _, e1⟩ := (get_ok _ F c _).1 h1
    have y2 : F1 = F := congrArg (fun x : (Array Nat × Fork) × Ctx => x.1.2) e1
    have y3 : c1 = c := congrArg (fun x : (Array Nat × Fork) × Ctx => x.2) e1
    rw [y2, y3] at h2
    obtain ⟨_, F2, c2, h3, h4⟩ := (bind_ok _ _ F c _).1 h2
    have e3 := (pure_ok _ F c _).1 h3
    have z2 : F2 = F := congrArg (fun x : (PUnit × Fork) × Ctx => x.1.2) e3
    have z3 : c2 = c := congrArg (fun x : (PUnit × Fork) × Ctx => x.2) e3
    rw [z2, z3] at h4
    exact ⟨x, (pure_ok _ F c _).1 h4, trivial⟩) (List.range p.Rp) [] read F c r trivial hr
  exact ⟨b', e⟩

/-- All runs: call by call, piece by piece. -/
def joinRuns (tl : HTailF2) (g : Heard) : List Run2 :=
  [0, 1].flatMap fun q => (tl.zOf q).pieces.toList.map (joinRun tl g q)

/-- The calls' share of the constant. -/
def joinConst0 (g : Heard) (l : List ℕ) : E :=
  l.foldl (fun s q => addE s (mulE (g.e.getD q zeroE) (subE g.alpha (scaleNat g.theta q)))) zeroE

/-- The constant: the calls' share, then the trees of padding alone. -/
def joinConst (tl : HTailF2) (g : Heard) : E :=
  (List.range (2 ^ tl.f9.rK - tl.f9.NT)).foldl
    (fun s y => addE s (mulE ((eqTab g.zy).getD (tl.f9.NT + y) zeroE) (subE g.alpha (g.padKey 0))))
    (joinConst0 g [0, 1])

/-- The end of one step of the loop over the pieces of call q, behind the push of the piece's run:
if it returns, it turns the count of places alone and goes on. -/
theorem piecesStep_ok (tl : HTailF2) (q : ℕ) (p : Piece)
    (s : MProd (Array E) (MProd (Array Nat) (MProd (Array Run2) (Array E))))
    (x : SubM (ForInStep (MProd (Array E) (MProd (Array Nat) (MProd (Array Run2) (Array E))))))
    (F : Fork) (c : Ctx)
    (r : (ForInStep (MProd (Array E) (MProd (Array Nat) (MProd (Array Run2) (Array E)))) × Fork) ×
      Ctx)
    (hx : x = (do
      let r ← forIn (List.range p.Rp) s.snd.fst fun rr (r : Array Nat) => (do
        let r ← SubM.get
          (HTailF2.placesRead tl.f9.dT (tl.f9.iota.getD q 0) (tl.f9.first.getD q 0)
            (2 ^ tl.f9.iota.getD q 0 + 1) r (p.off + rr * p.CP) p.Cp)
        pure PUnit.unit
        pure (ForInStep.yield r) : SubM (ForInStep (Array Nat)))
      pure PUnit.unit
      pure (ForInStep.yield ⟨s.fst, r, s.snd.snd.fst, s.snd.snd.snd⟩)))
    (h : x F c = .ok r) :
    ∃ read', r = ((ForInStep.yield ⟨s.fst, read', s.snd.snd.fst, s.snd.snd.snd⟩, F), c) := by
  subst hx
  obtain ⟨rd, F1, c1, h1, h2⟩ := (bind_ok _ _ F c _).1 h
  obtain ⟨read', e1⟩ := rowsLoop_ok tl.f9 q p _ F c _ h1
  have y1 : rd = read' := congrArg (fun x : (Array Nat × Fork) × Ctx => x.1.1) e1
  have y2 : F1 = F := congrArg (fun x : (Array Nat × Fork) × Ctx => x.1.2) e1
  have y3 : c1 = c := congrArg (fun x : (Array Nat × Fork) × Ctx => x.2) e1
  rw [y1, y2, y3] at h2
  obtain ⟨_, F2, c2, h3, h4⟩ := (bind_ok _ _ F c _).1 h2
  have e3 := (pure_ok _ F c _).1 h3
  have z2 : F2 = F := congrArg (fun x : (PUnit × Fork) × Ctx => x.1.2) e3
  have z3 : c2 = c := congrArg (fun x : (PUnit × Fork) × Ctx => x.2) e3
  rw [z2, z3] at h4
  exact ⟨read', (pure_ok _ F c _).1 h4⟩

/-- A run of linJoin9 that returns, step by step. -/
theorem linJoin9_cut (tl tl' : HTailF2) (F G : Fork) (c c' : Ctx)
    (h : tl.linJoin9 F c = .ok ((tl', G), c')) :
    ∃ (g : Heard) (runs : Array Run2) (F1 : Fork) (c1 : Ctx),
      tl.heard = some g ∧
      ([0, 1].all fun q => (tl.zOf q).call.tauAt (tl.zOf q).call.t0 == 0) = true ∧
      runs.toList = joinRuns tl g ∧
      t2Lin (Aff.ofConst (joinConst tl g) - g.cEnd) runs F c = .ok (((), F1), c1) ∧
      Forest.joinAdded g F1 c1 = .ok (((), G), c') ∧
      tl' = { tl with joinObj9 := some F.nClaim } := by
  unfold HTailF2.linJoin9 at h
  obtain ⟨g, A1, a1, r1, k1⟩ := (bind_ok _ _ F c _).1 h
  obtain ⟨g', s1, e1⟩ := (get_ok _ F c _).1 r1
  have x1 : g = g' := congrArg (fun x : (Heard × Fork) × Ctx => x.1.1) e1
  have x2 : A1 = F := congrArg (fun x : (Heard × Fork) × Ctx => x.1.2) e1
  have x3 : a1 = c := congrArg (fun x : (Heard × Fork) × Ctx => x.2) e1
  rw [← x1] at s1
  rw [x2, x3] at k1
  obtain ⟨_, A2, a2, r2, k2⟩ := (bind_ok _ _ F c _).1 k1
  obtain ⟨t1, e2⟩ := (mustAs_ok _ _ F c _).1 r2
  have y2 : A2 = F := congrArg (fun x : (Unit × Fork) × Ctx => x.1.2) e2
  have y3 : a2 = c := congrArg (fun x : (Unit × Fork) × Ctx => x.2) e2
  rw [y2, y3] at k2
  -- the loop over the two calls
  obtain ⟨s, A3, a3, r3, k3⟩ := (bind_ok _ _ F c _).1 k2
  have L3 := fun hstep => forIn_quiet _
    (fun (done : List ℕ)
        (s : MProd E (MProd (Array E) (MProd (Array Nat) (MProd (Array Run2) (Array E))))) =>
      s.snd.snd.snd.snd = eqTab s.snd.fst ∧
      s.snd.snd.snd.fst.toList =
        done.flatMap (fun q => (tl.zOf q).pieces.toList.map (joinRun tl g q)) ∧
      s.fst = joinConst0 g done) hstep [0, 1] [] _ F c _ ⟨rfl, rfl, rfl⟩ r3
  obtain ⟨s', e3, hT, hR, hC⟩ := L3 (fun done q b F c r hI hs => by
      obtain ⟨iT, iR, iC⟩ := hI
      obtain ⟨u, B1, b1, q1, q2⟩ := (bind_ok _ _ F c _).1 hs
      rw [← Array.forIn_toList] at q1
      -- the loop over the call's pieces
      have L4 := fun hstep => forIn_quiet _
        (fun (dn : List Piece)
            (s : MProd (Array E) (MProd (Array Nat) (MProd (Array Run2) (Array E)))) =>
          s.snd.snd.snd = eqTab s.fst ∧
          s.snd.snd.fst.toList = b.snd.snd.snd.fst.toList ++ dn.map (joinRun tl g q)) hstep
        (tl.zOf q).pieces.toList [] _ F c _ ⟨iT, by simp⟩ q1
      obtain ⟨u', f1, jT, jR⟩ := L4 (fun dn p w F c r hJ ht => by
          obtain ⟨lT, lR⟩ := hJ
          obtain ⟨_, C1, d1, m1, m2⟩ := (bind_ok _ _ F c _).1 ht
          obtain ⟨_, e5⟩ := (mustAs_ok _ _ F c _).1 m1
          have n2 : C1 = F := congrArg (fun x : (Unit × Fork) × Ctx => x.1.2) e5
          have n3 : d1 = c := congrArg (fun x : (Unit × Fork) × Ctx => x.2) e5
          rw [n2, n3] at m2
          by_cases hz : (joinZc tl g q p != w.fst) = true
          · have m3 := m2
            rw [show (if ((g.zk.getD q #[]).extract ((tl.zOf q).call.n - p.b + p.a)
              ((tl.zOf q).call.n - p.b + p.a + clog2 p.CP) != w.fst) = true then _ else _) = _ from
              if_pos hz] at m3
            obtain ⟨_, C2, d2, m4, m5⟩ := (bind_ok _ _ F c _).1 m3
            have e6 := (pure_ok _ F c _).1 m4
            have o2 : C2 = F := congrArg (fun x : (PUnit × Fork) × Ctx => x.1.2) e6
            have o3 : d2 = c := congrArg (fun x : (PUnit × Fork) × Ctx => x.2) e6
            rw [o2, o3] at m5
            obtain ⟨rd, e7⟩ := piecesStep_ok tl q p
              ⟨joinZc tl g q p, w.snd.fst, w.snd.snd.fst.push (joinRun tl g q p),
                eqTab (joinZc tl g q p)⟩ _ F c r rfl m5
            refine ⟨_, e7, rfl, ?_⟩
            show (w.snd.snd.fst.push (joinRun tl g q p)).toList = _
            rw [Array.toList_push, lR, List.map_append, List.append_assoc]
            rfl
          · have hz' : joinZc tl g q p = w.fst := by simpa using hz
            have m3 := m2
            rw [show (if ((g.zk.getD q #[]).extract ((tl.zOf q).call.n - p.b + p.a)
              ((tl.zOf q).call.n - p.b + p.a + clog2 p.CP) != w.fst) = true then _ else _) = _ from
              if_neg hz] at m3
            obtain ⟨_, C2, d2, m4, m5⟩ := (bind_ok _ _ F c _).1 m3
            have e6 := (pure_ok _ F c _).1 m4
            have o2 : C2 = F := congrArg (fun x : (PUnit × Fork) × Ctx => x.1.2) e6
            have o3 : d2 = c := congrArg (fun x : (PUnit × Fork) × Ctx => x.2) e6
            rw [o2, o3] at m5
            have hrun : joinRunW tl g q p w.snd.snd.snd = joinRun tl g q p := by
              unfold joinRun
              rw [lT, hz']
            obtain ⟨rd, e7⟩ := piecesStep_ok tl q p
              ⟨w.fst, w.snd.fst, w.snd.snd.fst.push (joinRunW tl g q p w.snd.snd.snd),
                w.snd.snd.snd⟩ _ F c r rfl m5
            refine ⟨_, e7, lT, ?_⟩
            show (w.snd.snd.fst.push _).toList = _
            rw [hrun, Array.toList_push, lR, List.map_append, List.append_assoc]
            rfl)
      have v1 : u = u' := congrArg (fun x : (_ × Fork) × Ctx => x.1.1) f1
      have v2 : B1 = F := congrArg (fun x : (_ × Fork) × Ctx => x.1.2) f1
      have v3 : b1 = c := congrArg (fun x : (_ × Fork) × Ctx => x.2) f1
      rw [v1, v2, v3] at q2
      obtain ⟨_, B2, b2, q3, q4⟩ := (bind_ok _ _ F c _).1 q2
      have e8 := (pure_ok _ F c _).1 q3
      have w2 : B2 = F := congrArg (fun x : (PUnit × Fork) × Ctx => x.1.2) e8
      have w3 : b2 = c := congrArg (fun x : (PUnit × Fork) × Ctx => x.2) e8
      rw [w2, w3] at q4
      refine ⟨_, (pure_ok _ F c _).1 q4, jT, ?_, ?_⟩
      · show u'.snd.snd.fst.toList = _
        rw [jR, iR, List.nil_append, List.flatMap_append]
        simp
      · show addE b.fst _ = _
        rw [iC]
        unfold joinConst0
        rw [List.foldl_append]
        rfl)
  have z1 : s = s' := congrArg (fun x : (_ × Fork) × Ctx => x.1.1) e3
  have z2 : A3 = F := congrArg (fun x : (_ × Fork) × Ctx => x.1.2) e3
  have z3 : a3 = c := congrArg (fun x : (_ × Fork) × Ctx => x.2) e3
  rw [z1, z2, z3] at k3
  -- the loop over the trees of padding alone
  obtain ⟨cst, A4, a4, r4, k4⟩ := (bind_ok _ _ F c _).1 k3
  have L5 := fun hstep => forIn_quiet _
    (fun (done : List ℕ) (x : E) => x = done.foldl
      (fun s y => addE s (mulE ((eqTab g.zy).getD (tl.f9.NT + y) zeroE)
        (subE g.alpha (g.padKey 0)))) s'.fst) hstep
    (List.range (2 ^ tl.f9.rK - tl.f9.NT)) [] _ F c _ rfl r4
  obtain ⟨cst', e4, hK⟩ := L5 (fun done y b F c r hI hs => by
      obtain ⟨_, B2, b2, q3, q4⟩ := (bind_ok _ _ F c _).1 hs
      have e8 := (pure_ok _ F c _).1 q3
      have w2 : B2 = F := congrArg (fun x : (PUnit × Fork) × Ctx => x.1.2) e8
      have w3 : b2 = c := congrArg (fun x : (PUnit × Fork) × Ctx => x.2) e8
      rw [w2, w3] at q4
      refine ⟨_, (pure_ok _ F c _).1 q4, ?_⟩
      have hI' : b = done.foldl (fun s y => addE s (mulE ((eqTab g.zy).getD (tl.f9.NT + y) zeroE)
        (subE g.alpha (g.padKey 0)))) s'.fst := hI
      show addE b _ = (done ++ [y]).foldl (fun s y => addE s
        (mulE ((eqTab g.zy).getD (tl.f9.NT + y) zeroE) (subE g.alpha (g.padKey 0)))) s'.fst
      rw [List.foldl_append, ← hI']
      rfl)
  have u1 : cst = cst' := congrArg (fun x : (E × Fork) × Ctx => x.1.1) e4
  have u2 : A4 = F := congrArg (fun x : (E × Fork) × Ctx => x.1.2) e4
  have u3 : a4 = c := congrArg (fun x : (E × Fork) × Ctx => x.2) e4
  rw [u1, u2, u3] at k4
  -- two tests, the number of claims, the claim, the mark
  obtain ⟨_, A5, a5, r5, k5⟩ := (bind_ok _ _ F c _).1 k4
  obtain ⟨_, e5⟩ := (mustAs_ok _ _ F c _).1 r5
  have p2 : A5 = F := congrArg (fun x : (Unit × Fork) × Ctx => x.1.2) e5
  have p3 : a5 = c := congrArg (fun x : (Unit × Fork) × Ctx => x.2) e5
  rw [p2, p3] at k5
  obtain ⟨_, A6, a6, r6, k6⟩ := (bind_ok _ _ F c _).1 k5
  unfold Forest.paddingLaid at r6
  obtain ⟨_, e6⟩ := (mustAs_ok _ _ F c _).1 r6
  have p4 : A6 = F := congrArg (fun x : (Unit × Fork) × Ctx => x.1.2) e6
  have p5 : a6 = c := congrArg (fun x : (Unit × Fork) × Ctx => x.2) e6
  rw [p4, p5] at k6
  obtain ⟨num, A7, a7, r7, k7⟩ := (bind_ok _ _ F c _).1 k6
  unfold SubM.claims at r7
  obtain ⟨num', hn, e7⟩ := (ask_ok _ F c _).1 r7
  have p6 : num = num' := congrArg (fun x : (ℕ × Fork) × Ctx => x.1.1) e7
  have p7 : A7 = F := congrArg (fun x : (ℕ × Fork) × Ctx => x.1.2) e7
  have p8 : a7 = c := congrArg (fun x : (ℕ × Fork) × Ctx => x.2) e7
  rw [p6, ← Option.some.inj hn, p7, p8] at k7
  obtain ⟨_, F1, c1, r8, k8⟩ := (bind_ok _ _ F c _).1 k7
  obtain ⟨_, F2, c2, r9, k9⟩ := (bind_ok _ _ F1 c1 _).1 k8
  have e9 := (pure_ok _ F2 c2 _).1 k9
  have g1 : tl' = _ := congrArg (fun x : (HTailF2 × Fork) × Ctx => x.1.1) e9
  have g2 : G = F2 := congrArg (fun x : (HTailF2 × Fork) × Ctx => x.1.2) e9
  have g3 : c' = c2 := congrArg (fun x : (HTailF2 × Fork) × Ctx => x.2) e9
  rw [← g2, ← g3] at r9
  have hcst : cst' = joinConst tl g := by
    rw [hK, hC]
    rfl
  rw [hcst] at r8
  exact ⟨g, s'.snd.snd.snd.fst, F1, c1, s1, t1, hR, r8, r9, g1⟩

end Fo
