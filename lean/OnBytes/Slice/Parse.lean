-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/Parse.lean: the format's decision on a link, read as a list of parses.

The decision of Fmt/M3Dec.lean (decBy), with the proximity tests below it (Fmt/M2Last.lean: lastAt;
Fmt/M1Dec.lean: iopp), is a tower of matches. Each match takes one or more rounds off the list of
rounds, or asks a block's function for its result. This file says the same in another form: the
decision is yes if and only if every parse succeeds with some values and the blocks' functions give
the stated results on these values.

Main theorems.
 nextN_app, takeRounds_app, seedOf_app   a parse that succeeds on a list of rounds succeeds on the
                                         list with more rounds after it, with the same values
 iopp_base_iff    the proximity test at its last stage
 iopp_step_iff    the proximity test at a stage that is not the last
 lastAt_iff       the proximity test on a group, at its first stage
 decBy_iff        the decision
 iopp_step_some, iopp_step_none, lastAt_some, lastAt_none, iopp_base_eq, decBy_some, decBy_none
                  the same on a block's own rounds with more rounds after them: equations, but for
                  decBy_some, which is an implication

Not claimed. Nothing is said of what the decision shows.
-/
import Fmt.M3Dec

set_option autoImplicit false

namespace OnBytes.Slice
open Fmt.M1

/-- The next round, with more rounds after the list. -/
theorem nextN_app (ns ne np : Nat) (rs t : Rs) (v : RV) (rs' : Rs)
    (h : nextN ns ne np rs = some (v, rs')) : nextN ns ne np (rs ++ t) = some (v, rs' ++ t) := by
  cases rs with
  | nil => simp [nextN] at h
  | cons a rs0 =>
    simp only [nextN] at h
    simp only [List.cons_append, nextN]
    split at h
    · next hc =>
      rw [if_pos hc]
      cases h
      rfl
    · cases h

/-- Rounds of two elements sent and one drawn, with more rounds after the list. -/
theorem takeRounds_app : ∀ (n : Nat) (rs t : Rs) (qs : List (E × E)) (g : List E) (rs' : Rs),
    takeRounds n rs = some (qs, g, rs') → takeRounds n (rs ++ t) = some (qs, g, rs' ++ t)
  | 0, rs, t, qs, g, rs', h => by
    simp only [takeRounds, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  | n + 1, rs, t, qs, g, rs', h => by
    simp only [takeRounds] at h
    split at h
    · next a b g0 ps r1 h1 =>
      cases h2 : takeRounds n r1 with
      | none => simp [h2] at h
      | some x =>
        obtain ⟨q1, g1, r2⟩ := x
        simp only [h2, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp only [takeRounds, nextN_app 2 1 0 rs t _ _ h1, takeRounds_app n r1 t q1 g1 r2 h2,
          Option.map_some]
    · cases h

/-- A seed, with more rounds after the list. -/
theorem seedOf_app (na : Nat) (rs t : Rs) (z : List E) (beta : E) (rs' : Rs)
    (h : seedOf na rs = some (z, beta, rs')) : seedOf na (rs ++ t) = some (z, beta, rs' ++ t) := by
  simp only [seedOf] at h
  split at h
  · next v r1 h1 =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    simp only [seedOf, nextN_app 0 (na + 1) 0 rs t _ _ h1]
  · cases h

/-- The proximity test at its last stage says yes if and only if the two rounds of the base case
parse, no round is left, and the base case's function says yes. -/
theorem iopp_base_iff (B : Blocks) (f : Fmt.Fld) (V : View) (s : Stage) (tree mF mE : Nat)
    (G : GRow) (rs : Rs) :
    iopp B f V [s] tree mF mE G rs = true ↔
      ∃ tauS lam ps rs1 v, nextN 1 1 0 rs = some (⟨[tauS], [lam], ps⟩, rs1) ∧
        nextN (s.C.l + s.Z.l + s.C.r + s.Z.r) 0 s.t rs1 = some (v, []) ∧
        B.base f s.C s.Z G.c G.d G.t tauS lam (v.sent.take s.C.l)
          ((v.sent.drop s.C.l).take s.Z.l) ((v.sent.drop (s.C.l + s.Z.l)).take s.C.r)
          (v.sent.drop (s.C.l + s.Z.l + s.C.r)) v.poss (lastCol V tree) = true := by
  constructor
  · intro h
    simp only [iopp] at h
    split at h
    · next tauS lam ps rs1 h1 =>
      split at h
      · next v h2 => exact ⟨tauS, lam, ps, rs1, v, h1, h2, h⟩
      · cases h
    · cases h
  · rintro ⟨tauS, lam, ps, rs1, v, h1, h2, h3⟩
    simp only [iopp, h1, h2]
    exact h3

/-- The proximity test at a stage that is not the last says yes if and only if the rounds of the
fold, the seed and the code switch parse, the code switch's function gives a row, and the test says
yes at the next stage on that row. -/
theorem iopp_step_iff (B : Blocks) (f : Fmt.Fld) (V : View) (s s' : Stage) (more : List Stage)
    (tree mF mE : Nat) (G : GRow) (rs : Rs) :
    iopp B f V (s :: s' :: more) tree mF mE G rs = true ↔
      ∃ sigma eps ps rs1 qs g rs2 z beta rs3 alpha theta xs rs4 G',
        nextN 1 1 0 rs = some (⟨[sigma], [eps], ps⟩, rs1) ∧
        takeRounds s.k rs1 = some (qs, g, rs2) ∧ seedOf s'.na rs2 = some (z, beta, rs3) ∧
        nextN 1 1 s.t rs3 = some (⟨[alpha], [theta], xs⟩, rs4) ∧
        B.cs f s s' (B.fold f s.k s.h G sigma eps qs g) (B.sample f s'.Am s'.Az z beta alpha) xs
          theta (fun x => (colAt V tree x).bind (stageCol s mF mE)) = some G' ∧
        iopp B f V (s' :: more) (tree + 1) 0 (2 ^ s'.k) G' rs4 = true := by
  constructor
  · intro h
    simp only [iopp] at h
    split at h
    · next sigma eps ps rs1 h1 =>
      split at h
      · next qs g rs2 h2 =>
        split at h
        · next z beta rs3 h3 =>
          split at h
          · next alpha theta xs rs4 h4 =>
            split at h
            · next G' h5 =>
              exact ⟨sigma, eps, ps, rs1, qs, g, rs2, z, beta, rs3, alpha, theta, xs, rs4, G',
                h1, h2, h3, h4, h5, h⟩
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · rintro ⟨sigma, eps, ps, rs1, qs, g, rs2, z, beta, rs3, alpha, theta, xs, rs4, G',
      h1, h2, h3, h4, h5, h6⟩
    simp only [iopp, h1, h2, h3, h4, h5]
    exact h6

/-- The proximity test on a group says yes if and only if the rounds of the fold, the seed and the
code switch parse, the code switch's function gives a row on the group's columns, and the test says
yes at the next stage on that row. -/
theorem lastAt_iff (B : Blocks) (f : Fmt.Fld) (s s' : Stage) (more : List Stage)
    (ms : List Fmt.M2.Mem) (fresh tree : Nat) (V : View) (G : GRow) (rs : Rs) :
    Fmt.M2.lastAt B f (s :: s' :: more) ms fresh tree V G rs = true ↔
      ∃ sigma eps ps rs1 qs g rs2 z beta rs3 alpha theta xs rs4 G',
        nextN 1 1 0 rs = some (⟨[sigma], [eps], ps⟩, rs1) ∧
        takeRounds s.k rs1 = some (qs, g, rs2) ∧ seedOf s'.na rs2 = some (z, beta, rs3) ∧
        nextN 1 1 s.t rs3 = some (⟨[alpha], [theta], xs⟩, rs4) ∧
        B.cs f s s' (B.fold f s.k s.h G sigma eps qs g) (B.sample f s'.Am s'.Az z beta alpha) xs
          theta (fun x => ((colAt V tree x).bind (Fmt.M2.groupCol ms fresh)).map (·.col)) =
            some G' ∧
        iopp B f V (s' :: more) (tree + 1) 0 (2 ^ s'.k) G' rs4 = true := by
  constructor
  · intro h
    simp only [Fmt.M2.lastAt] at h
    split at h
    · next sigma eps ps rs1 h1 =>
      split at h
      · next qs g rs2 h2 =>
        split at h
        · next z beta rs3 h3 =>
          split at h
          · next alpha theta xs rs4 h4 =>
            split at h
            · next G' h5 =>
              exact ⟨sigma, eps, ps, rs1, qs, g, rs2, z, beta, rs3, alpha, theta, xs, rs4, G',
                h1, h2, h3, h4, h5, h⟩
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · rintro ⟨sigma, eps, ps, rs1, qs, g, rs2, z, beta, rs3, alpha, theta, xs, rs4, G',
      h1, h2, h3, h4, h5, h6⟩
    simp only [Fmt.M2.lastAt, h1, h2, h3, h4, h5]
    exact h6

/-- The decision says yes if and only if the sizes fit, the link's six rounds parse, the batching
gives a row, and the proximity test on the group says yes on that row. -/
theorem decBy_iff (B : Blocks) (P : Fmt.M3.Par) (V : Fmt.M3.View) (bt : Fmt.M3.Batch) :
    Fmt.M3.decBy B P V bt = true ↔ Fmt.M3.sizesOK B P = true ∧
      ∃ vg rs1 z beta rs2 y0 yj e3 p3 rs3 vx rs4 vp rs5 s6 theta p6 rs6 R,
        nextN 0 P.v 0 V.rounds = some (vg, rs1) ∧
        seedOf (Fmt.M2.seedLen (lg P.C.l) (lg P.Z.l) P.mems) rs1 = some (z, beta, rs2) ∧
        nextN 2 0 0 rs2 = some (⟨[y0, yj], e3, p3⟩, rs3) ∧
        nextN 0 0 (P.nu0 + P.nuj) rs3 = some (vx, rs4) ∧ nextN 0 P.aPhi 0 rs4 = some (vp, rs5) ∧
        nextN 0 1 0 rs5 = some (⟨s6, [theta], p6⟩, rs6) ∧
        bt vg.els z beta y0 yj vx.poss vp.els theta = some R ∧
        Fmt.M2.lastAt B P.fld P.stages P.mems 1 0 V.own R.toG rs6 = true := by
  constructor
  · intro h
    simp only [Fmt.M3.decBy, Bool.and_eq_true] at h
    obtain ⟨h0, h⟩ := h
    refine ⟨h0, ?_⟩
    split at h
    · next vg rs1 h1 =>
      split at h
      · next z beta rs2 h2 =>
        split at h
        · next y0 yj e3 p3 rs3 h3 =>
          split at h
          · next vx rs4 h4 =>
            split at h
            · next vp rs5 h5 =>
              split at h
              · next s6 theta p6 rs6 h6 =>
                split at h
                · next R h7 =>
                  exact ⟨vg, rs1, z, beta, rs2, y0, yj, e3, p3, rs3, vx, rs4, vp, rs5, s6, theta,
                    p6, rs6, R, h1, h2, h3, h4, h5, h6, h7, h⟩
                · cases h
              · cases h
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · rintro ⟨h0, vg, rs1, z, beta, rs2, y0, yj, e3, p3, rs3, vx, rs4, vp, rs5, s6, theta, p6, rs6,
      R, h1, h2, h3, h4, h5, h6, h7, h8⟩
    simp only [Fmt.M3.decBy, h0, h1, h2, h3, h4, h5, h6, h7, Bool.true_and]
    exact h8

/-! ## Equations in the shape of the blocks

A block hands on parses of its own rounds with no round left. The statements below say what the
decision is on these rounds with more rounds after them. All are equations but decBy_some. That one
is an implication, since the numbers of what the six rounds send and draw are not given. -/

/-- A stage that is not the last: if its rounds parse and the code switch gives a row, the test is
the test at the next stage on the rounds that are left. -/
theorem iopp_step_some (B : Blocks) (f : Fmt.Fld) (V : View) (s s' : Stage) (more : List Stage)
    (tree mF mE : Nat) (G : GRow) (ra rb rest : Rs) (sigma eps : E) (ps : List Nat) (rs1 : Rs)
    (qs : List (E × E)) (g z : List E) (beta : E) (rs3 : Rs) (alpha theta : E) (xs : List Nat)
    (G' : GRow) (h1 : nextN 1 1 0 ra = some (⟨[sigma], [eps], ps⟩, rs1))
    (h2 : takeRounds s.k rs1 = some (qs, g, [])) (h3 : seedOf s'.na rb = some (z, beta, rs3))
    (h4 : nextN 1 1 s.t rs3 = some (⟨[alpha], [theta], xs⟩, []))
    (h5 : B.cs f s s' (B.fold f s.k s.h G sigma eps qs g) (B.sample f s'.Am s'.Az z beta alpha) xs
      theta (fun x => (colAt V tree x).bind (stageCol s mF mE)) = some G') :
    iopp B f V (s :: s' :: more) tree mF mE G (ra ++ (rb ++ rest)) =
      iopp B f V (s' :: more) (tree + 1) 0 (2 ^ s'.k) G' rest := by
  have e1 := nextN_app 1 1 0 ra (rb ++ rest) _ _ h1
  have e2 := takeRounds_app s.k rs1 (rb ++ rest) _ _ _ h2
  have e3 := seedOf_app s'.na rb rest _ _ _ h3
  have e4 := nextN_app 1 1 s.t rs3 rest _ _ h4
  simp only [List.nil_append] at e2 e4
  simp only [iopp, e1, e2, e3, e4, h5]

/-- A stage that is not the last: if its rounds parse and the code switch gives no row, the test
says no. -/
theorem iopp_step_none (B : Blocks) (f : Fmt.Fld) (V : View) (s s' : Stage) (more : List Stage)
    (tree mF mE : Nat) (G : GRow) (ra rb rest : Rs) (sigma eps : E) (ps : List Nat) (rs1 : Rs)
    (qs : List (E × E)) (g z : List E) (beta : E) (rs3 : Rs) (alpha theta : E) (xs : List Nat)
    (h1 : nextN 1 1 0 ra = some (⟨[sigma], [eps], ps⟩, rs1))
    (h2 : takeRounds s.k rs1 = some (qs, g, [])) (h3 : seedOf s'.na rb = some (z, beta, rs3))
    (h4 : nextN 1 1 s.t rs3 = some (⟨[alpha], [theta], xs⟩, []))
    (h5 : B.cs f s s' (B.fold f s.k s.h G sigma eps qs g) (B.sample f s'.Am s'.Az z beta alpha) xs
      theta (fun x => (colAt V tree x).bind (stageCol s mF mE)) = none) :
    iopp B f V (s :: s' :: more) tree mF mE G (ra ++ (rb ++ rest)) = false := by
  have e1 := nextN_app 1 1 0 ra (rb ++ rest) _ _ h1
  have e2 := takeRounds_app s.k rs1 (rb ++ rest) _ _ _ h2
  have e3 := seedOf_app s'.na rb rest _ _ _ h3
  have e4 := nextN_app 1 1 s.t rs3 rest _ _ h4
  simp only [List.nil_append] at e2 e4
  simp only [iopp, e1, e2, e3, e4, h5]

/-- The first stage on a group: if its rounds parse and the code switch gives a row, the test is the
test at the next stage on the rounds that are left. -/
theorem lastAt_some (B : Blocks) (f : Fmt.Fld) (s s' : Stage) (more : List Stage)
    (ms : List Fmt.M2.Mem) (fresh tree : Nat) (V : View) (G : GRow) (ra rb rest : Rs)
    (sigma eps : E) (ps : List Nat) (rs1 : Rs) (qs : List (E × E)) (g z : List E) (beta : E)
    (rs3 : Rs) (alpha theta : E) (xs : List Nat) (G' : GRow)
    (h1 : nextN 1 1 0 ra = some (⟨[sigma], [eps], ps⟩, rs1))
    (h2 : takeRounds s.k rs1 = some (qs, g, [])) (h3 : seedOf s'.na rb = some (z, beta, rs3))
    (h4 : nextN 1 1 s.t rs3 = some (⟨[alpha], [theta], xs⟩, []))
    (h5 : B.cs f s s' (B.fold f s.k s.h G sigma eps qs g) (B.sample f s'.Am s'.Az z beta alpha) xs
      theta (fun x => ((colAt V tree x).bind (Fmt.M2.groupCol ms fresh)).map (·.col)) = some G') :
    Fmt.M2.lastAt B f (s :: s' :: more) ms fresh tree V G (ra ++ (rb ++ rest)) =
      iopp B f V (s' :: more) (tree + 1) 0 (2 ^ s'.k) G' rest := by
  have e1 := nextN_app 1 1 0 ra (rb ++ rest) _ _ h1
  have e2 := takeRounds_app s.k rs1 (rb ++ rest) _ _ _ h2
  have e3 := seedOf_app s'.na rb rest _ _ _ h3
  have e4 := nextN_app 1 1 s.t rs3 rest _ _ h4
  simp only [List.nil_append] at e2 e4
  simp only [Fmt.M2.lastAt, e1, e2, e3, e4, h5]

/-- The first stage on a group: if its rounds parse and the code switch gives no row, the test says
no. -/
theorem lastAt_none (B : Blocks) (f : Fmt.Fld) (s s' : Stage) (more : List Stage)
    (ms : List Fmt.M2.Mem) (fresh tree : Nat) (V : View) (G : GRow) (ra rb rest : Rs)
    (sigma eps : E) (ps : List Nat) (rs1 : Rs) (qs : List (E × E)) (g z : List E) (beta : E)
    (rs3 : Rs) (alpha theta : E) (xs : List Nat)
    (h1 : nextN 1 1 0 ra = some (⟨[sigma], [eps], ps⟩, rs1))
    (h2 : takeRounds s.k rs1 = some (qs, g, [])) (h3 : seedOf s'.na rb = some (z, beta, rs3))
    (h4 : nextN 1 1 s.t rs3 = some (⟨[alpha], [theta], xs⟩, []))
    (h5 : B.cs f s s' (B.fold f s.k s.h G sigma eps qs g) (B.sample f s'.Am s'.Az z beta alpha) xs
      theta (fun x => ((colAt V tree x).bind (Fmt.M2.groupCol ms fresh)).map (·.col)) = none) :
    Fmt.M2.lastAt B f (s :: s' :: more) ms fresh tree V G (ra ++ (rb ++ rest)) = false := by
  have e1 := nextN_app 1 1 0 ra (rb ++ rest) _ _ h1
  have e2 := takeRounds_app s.k rs1 (rb ++ rest) _ _ _ h2
  have e3 := seedOf_app s'.na rb rest _ _ _ h3
  have e4 := nextN_app 1 1 s.t rs3 rest _ _ h4
  simp only [List.nil_append] at e2 e4
  simp only [Fmt.M2.lastAt, e1, e2, e3, e4, h5]

/-- The last stage: if its two rounds parse and no round is left, the test is the base case's
function. -/
theorem iopp_base_eq (B : Blocks) (f : Fmt.Fld) (V : View) (s : Stage) (tree mF mE : Nat)
    (G : GRow) (rs : Rs) (tauS lam : E) (ps : List Nat) (rs1 : Rs) (v : RV)
    (h1 : nextN 1 1 0 rs = some (⟨[tauS], [lam], ps⟩, rs1))
    (h2 : nextN (s.C.l + s.Z.l + s.C.r + s.Z.r) 0 s.t rs1 = some (v, [])) :
    iopp B f V [s] tree mF mE G rs =
      B.base f s.C s.Z G.c G.d G.t tauS lam (v.sent.take s.C.l) ((v.sent.drop s.C.l).take s.Z.l)
        ((v.sent.drop (s.C.l + s.Z.l)).take s.C.r) (v.sent.drop (s.C.l + s.Z.l + s.C.r)) v.poss
        (lastCol V tree) := by
  simp only [iopp, h1, h2]

/-- The next round of a list that begins with r is r. -/
private theorem nextN_cons {ns ne np : Nat} {r v : RV} {t rs' : Rs}
    (h : nextN ns ne np (r :: t) = some (v, rs')) : v = r ∧ rs' = t := by
  simp only [nextN] at h
  split at h
  · cases h
    exact ⟨rfl, rfl⟩
  · cases h

/-- The seed of a list that begins with r is read off r. -/
private theorem seedOf_cons {na : Nat} {r : RV} {t : Rs} {z : List E} {beta : E} {rs' : Rs}
    (h : seedOf na (r :: t) = some (z, beta, rs')) :
    z = r.els.take na ∧ beta = r.els.getD na Fmt.Fld.zeroE ∧ rs' = t := by
  simp only [seedOf] at h
  split at h
  · next v r1 h1 =>
    obtain ⟨rfl, rfl⟩ := nextN_cons h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩
  · cases h

/-- If the decision says yes on a list that begins with six rounds, the batching gives a row on what
these rounds hold, and the proximity test says yes on that row and the rounds that are left. -/
private theorem decBy_six (B : Blocks) (P : Fmt.M3.Par) (V : Fmt.M3.View) (bt : Fmt.M3.Batch)
    (r1 r2 r3 r4 r5 r6 : RV) (rest : Rs) (theta : E)
    (hV : V.rounds = r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: rest) (h6 : r6.els = [theta])
    (h : Fmt.M3.decBy B P V bt = true) :
    ∃ R, bt r1.els (r2.els.take (Fmt.M2.seedLen (lg P.C.l) (lg P.Z.l) P.mems))
        (r2.els.getD (Fmt.M2.seedLen (lg P.C.l) (lg P.Z.l) P.mems) Fmt.Fld.zeroE)
        (r3.sent.getD 0 Fmt.Fld.zeroE) (r3.sent.getD 1 Fmt.Fld.zeroE) r4.poss r5.els theta =
          some R ∧
      Fmt.M2.lastAt B P.fld P.stages P.mems 1 0 V.own R.toG rest = true := by
  obtain ⟨_, vg, rs1, z, beta, rs2, y0, yj, e3, p3, rs3, vx, rs4, vp, rs5, s6, th, p6, rs6, R,
    a1, a2, a3, a4, a5, a6, a7, a8⟩ := (decBy_iff B P V bt).1 h
  rw [hV] at a1
  obtain ⟨rfl, rfl⟩ := nextN_cons a1
  obtain ⟨rfl, rfl, rfl⟩ := seedOf_cons a2
  obtain ⟨b3, rfl⟩ := nextN_cons a3
  obtain ⟨rfl, rfl⟩ := nextN_cons a4
  obtain ⟨rfl, rfl⟩ := nextN_cons a5
  obtain ⟨b6, rfl⟩ := nextN_cons a6
  subst b3
  subst b6
  have ht : th = theta := by simpa using h6
  subst ht
  exact ⟨R, a7, a8⟩

/-- The decision on a list that begins with six rounds: if it says yes and the batching gives the
row R on what these rounds hold, the proximity test says yes on R and the rounds that are left. -/
theorem decBy_some (B : Blocks) (P : Fmt.M3.Par) (V : Fmt.M3.View) (bt : Fmt.M3.Batch)
    (r1 r2 r3 r4 r5 r6 : RV) (rest : Rs) (theta : E) (R : Fmt.M2.KRow)
    (hV : V.rounds = r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: rest) (h6 : r6.els = [theta])
    (hb : bt r1.els (r2.els.take (Fmt.M2.seedLen (lg P.C.l) (lg P.Z.l) P.mems))
      (r2.els.getD (Fmt.M2.seedLen (lg P.C.l) (lg P.Z.l) P.mems) Fmt.Fld.zeroE)
      (r3.sent.getD 0 Fmt.Fld.zeroE) (r3.sent.getD 1 Fmt.Fld.zeroE) r4.poss r5.els theta =
        some R) :
    Fmt.M3.decBy B P V bt = true →
      Fmt.M2.lastAt B P.fld P.stages P.mems 1 0 V.own R.toG rest = true := by
  intro h
  obtain ⟨R', c1, c2⟩ := decBy_six B P V bt r1 r2 r3 r4 r5 r6 rest theta hV h6 h
  rw [hb] at c1
  cases c1
  exact c2

/-- The decision on a list that begins with six rounds: if the batching gives no row on what these
rounds hold, it says no. -/
theorem decBy_none (B : Blocks) (P : Fmt.M3.Par) (V : Fmt.M3.View) (bt : Fmt.M3.Batch)
    (r1 r2 r3 r4 r5 r6 : RV) (rest : Rs) (theta : E)
    (hV : V.rounds = r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: rest) (h6 : r6.els = [theta])
    (hb : bt r1.els (r2.els.take (Fmt.M2.seedLen (lg P.C.l) (lg P.Z.l) P.mems))
      (r2.els.getD (Fmt.M2.seedLen (lg P.C.l) (lg P.Z.l) P.mems) Fmt.Fld.zeroE)
      (r3.sent.getD 0 Fmt.Fld.zeroE) (r3.sent.getD 1 Fmt.Fld.zeroE) r4.poss r5.els theta = none) :
    Fmt.M3.decBy B P V bt = false := by
  cases h : Fmt.M3.decBy B P V bt with
  | false => rfl
  | true =>
    obtain ⟨R', c1, _⟩ := decBy_six B P V bt r1 r2 r3 r4 r5 r6 rest theta hV h6 h
    rw [hb] at c1
    cases c1

end OnBytes.Slice

#print axioms OnBytes.Slice.nextN_app
#print axioms OnBytes.Slice.takeRounds_app
#print axioms OnBytes.Slice.seedOf_app
#print axioms OnBytes.Slice.iopp_base_iff
#print axioms OnBytes.Slice.iopp_step_iff
#print axioms OnBytes.Slice.lastAt_iff
#print axioms OnBytes.Slice.decBy_iff
#print axioms OnBytes.Slice.iopp_step_some
#print axioms OnBytes.Slice.iopp_step_none
#print axioms OnBytes.Slice.lastAt_some
#print axioms OnBytes.Slice.lastAt_none
#print axioms OnBytes.Slice.iopp_base_eq
#print axioms OnBytes.Slice.decBy_some
#print axioms OnBytes.Slice.decBy_none
