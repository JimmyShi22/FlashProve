-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/G4/AnyCourse.lean: the steps of the program's lookup verifier above a single sumcheck, at
any caller that meets the laws of OnBytes/G4/AnyCaller.lean, each as an equation with every value
named: a line, a level and the levels of a product tree, a sumcheck without a variable, the tie's
later steps, the parts' steps, and the key trees of all parts.

Each value is a function on stands (Caller.Stand: the rounds left, the two ledgers, the rows added):
`levelVal`, `chainVal`, `tieVal`, `partVal`, `treesVal`. Beside each equation stand the facts that
the next step needs: the rounds that are left fit the entries that are left, what the two ledgers
have left, and the lengths of the points.

Main definitions: chainOwn, chainKey, Caller.Stand.levelVal, Caller.Stand.chainVal,
Caller.Stand.tieVal, Caller.Stand.partVal, Caller.Stand.treesVal, partEntries, treesEntries,
treesOwn, treesKey.
Main theorems: Caller.Laws.line_val, Caller.Laws.level_val, Caller.Laws.chain_val,
Caller.Laws.value_val, Caller.Laws.tie_val, Caller.Laws.part_val, Caller.Laws.trees_val,
Caller.Laws.drawOne_val, Caller.Laws.draws_val.
Not claimed: as in OnBytes/G4/AnyCaller.lean.


-/
import OnBytes.G4.AnyCaller

set_option autoImplicit false

namespace OnBytes.G4

open Blk

variable {C : Caller}

/-! ## Rounds in which nothing is sent -/

/-- A round in which one element is drawn and nothing is sent. -/
theorem Caller.Laws.drawOne_val (L : C.Laws) (work : Nat) (name : String) (es' : List Fmt.Entry)
    (s : C.Stand) (last) (hq : NoRows last)
    (hfit : FitsAll s.rounds ((rDraw name work 1).entry :: es')) :
    FitsAll s.next.rounds es' ∧
      (Lkp.drawOne name) (s.ctx ((rDraw name work 1).entry :: es') last) =
        .ok (s.draw, s.next.ctx es' (some (rDraw name work 1).entry)) := by
  obtain ⟨rounds, led, rows⟩ := s
  cases rounds with
  | nil => simp [FitsAll] at hfit
  | cons r rs =>
    obtain ⟨hr, hrest⟩ := hfit
    have hm : Meets r (rDraw name work 1).entry name 0 1 0 := meets_of_fits hr rfl rfl rfl rfl rfl
        rfl rfl
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.1 hm.drawn
    refine ⟨hrest, ?_⟩
    unfold Lkp.drawOne Caller.Stand.ctx
    rw [show rvs (r :: rs) = r.rv :: rvs rs from rfl,
      bind_ok (L.hearDraw_val _ es' (rvs rs) last led rows r name 1 hm hq), hx]
    simp [Caller.Stand.draw, Caller.Stand.next, hx]
    rfl

/-- A round in which n elements are drawn and nothing is sent. -/
theorem Caller.Laws.draws_val (L : C.Laws) (work n : Nat) (name : String) (es' : List Fmt.Entry)
    (s : C.Stand) (last) (hq : NoRows last)
    (hfit : FitsAll s.rounds ((rDraw name work n).entry :: es')) :
    FitsAll s.next.rounds es' ∧ s.draws.length = n ∧
      (hearDraw name n) (s.ctx ((rDraw name work n).entry :: es') last) =
        .ok (s.draws, s.next.ctx es' (some (rDraw name work n).entry)) := by
  obtain ⟨rounds, led, rows⟩ := s
  cases rounds with
  | nil => simp [FitsAll] at hfit
  | cons r rs =>
    obtain ⟨hr, hrest⟩ := hfit
    have hm : Meets r (rDraw name work n).entry name 0 n 0 := meets_of_fits hr rfl rfl rfl rfl rfl
        rfl rfl
    exact ⟨hrest, hm.drawn, L.hearDraw_val _ es' (rvs rs) last led rows r name n hm hq⟩

/-- Two claims at one point become one. -/
theorem Caller.Laws.line_val (L : C.Laws) (work : Nat) (es' : List Fmt.Entry) (s : C.Stand) (last)
    (a b : PointClaim) (hp : a.point = b.point) (hq : NoRows last)
    (hfit : FitsAll s.rounds ((rDraw "LINE" work 1).entry :: es')) :
    FitsAll s.next.rounds es' ∧
      (line a b) (s.ctx ((rDraw "LINE" work 1).entry :: es') last) =
        .ok (lineAt s.draw a b, s.next.ctx es' (some (rDraw "LINE" work 1).entry)) := by
  obtain ⟨rounds, led, rows⟩ := s
  cases rounds with
  | nil => simp [FitsAll] at hfit
  | cons r rs =>
    obtain ⟨hr, hrest⟩ := hfit
    have hm : Meets r (rDraw "LINE" work 1).entry "LINE" 0 1 0 :=
      meets_of_fits hr rfl rfl rfl rfl rfl rfl rfl
    obtain ⟨rho, hrho⟩ := List.length_eq_one_iff.1 hm.drawn
    refine ⟨hrest, ?_⟩
    unfold line Caller.Stand.ctx
    rw [bind_ok (must_ok (by simp [hp]) _), bind_ok (test_ok (by simp [hp]) _),
      show rvs (r :: rs) = r.rv :: rvs rs from rfl,
      bind_ok (L.hearDraw_val _ es' (rvs rs) last led rows r "LINE" 1 hm hq), hrho]
    simp [Caller.Stand.draw, Caller.Stand.next, hrho]
    rfl

/-! ## The levels of a product tree -/

/-- One level of a product tree: the claim on the next level, and the stand after it. -/
def Caller.Stand.levelVal (s : C.Stand) (order : List Nat) (keys : Bool) (c : PointClaim) :
    PointClaim × C.Stand :=
  let place := fun p => Lkp.byVariable p order
  let o := s.pscOut (levelSum c order) Lkp.summandProduct keys place
  let s1 := s.afterPsc (levelSum c order) Lkp.summandProduct keys [] place
  (lineAt s1.draw (o.ends.getD 0 default) (o.ends.getD 1 default), s1.next)

/-- One level of a product tree, with every value named. -/
theorem Caller.Laws.level_val (L : C.Laws) (work : Nat) (order : List Nat) (keys : Bool)
    (es' : List Fmt.Entry) (s : C.Stand) (last) (c : PointClaim) (hc : C.ClaimOK order.length c)
    (hq : NoRows last)
    (hfit : FitsAll s.rounds (pscEntries work { degree := List.replicate order.length 3 } ++
      (rDraw "LINE" work 1).entry :: es'))
    (h1 : ownOf (2 * order.length + 5) keys ≤ C.left s.led) (h2 : keyOf keys ≤ C.keyLeft s.led) :
    FitsAll (s.levelVal order keys c).2.rounds es' ∧
      C.left (s.levelVal order keys c).2.led = C.left s.led - ownOf (2 * order.length + 5) keys ∧
      C.keyLeft (s.levelVal order keys c).2.led = C.keyLeft s.led - keyOf keys ∧
      (s.levelVal order keys c).1.point.length = order.length + 1 ∧
      (keys = false → C.SlotsOK (s.levelVal order keys c).1.masks) ∧
      ((Lkp.psc C.env (levelSum c order) Lkp.summandProduct keys []
          fun p => Lkp.byVariable p order) >>= fun o =>
        match o.ends with
        | [e0, e1] => line e0 e1
        | _ => Blk.fail)
        (s.ctx (pscEntries work { degree := List.replicate order.length 3 } ++
          (rDraw "LINE" work 1).entry :: es') last) =
        .ok ((s.levelVal order keys c).1,
          (s.levelVal order keys c).2.ctx es' (some (rDraw "LINE" work 1).entry)) := by
  have hsz := levelSum_size c order
  have hmk := levelSum_masks c order
  have hvars : (levelSum c order).vars.length = order.length := by simp [levelSum]
  obtain ⟨last1, hf1, hq1, hrun, hpt, hends, hall, hl, hk⟩ :=
    L.psc_val work (levelSum c order) Lkp.summandProduct keys []
      (fun p => Lkp.byVariable p order) ((rDraw "LINE" work 1).entry :: es') s last hq
      (by rw [hsz]; exact hfit)
      (by simp [Psc.formOK, Lkp.summandProduct, levelSum, Psc.Weight.fits, Psc.Weight.equality])
      (by intro p y; rfl)
      (by
        intro x hx
        simp only [Psc.varsOf, Lkp.summandProduct, levelSum] at hx
        simp at hx
        rcases hx with ⟨t, _, rfl⟩ | rfl <;> simp [Psc.Weight.equality, Psc.Weight.atZero])
      (by simp [Psc.varsOf, Lkp.summandProduct])
      (by simp [Psc.varsOf, Lkp.summandProduct])
      (by rw [hmk]; exact h1) h2 (by intro _; rw [hmk]; omega)
      (by unfold keyOf; cases keys <;> simp [Lkp.summandProduct]) hc.2 rfl
      (by intro m hm; simp at hm) (fun p => byVariable_length p order)
  obtain ⟨e0, e1, he⟩ : ∃ e0 e1, (s.pscOut (levelSum c order) Lkp.summandProduct keys
      (fun p => Lkp.byVariable p order)).ends = [e0, e1] := by
    have h3 : (s.pscOut (levelSum c order) Lkp.summandProduct keys
      (fun p => Lkp.byVariable p order)).ends.length = 2 := hends
    match (s.pscOut (levelSum c order) Lkp.summandProduct keys
      (fun p => Lkp.byVariable p order)).ends, h3 with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  have h0 := hall e0 (by simp [he])
  have h1' := hall e1 (by simp [he])
  obtain ⟨hf2, hline⟩ := L.line_val work es'
    (s.afterPsc (levelSum c order) Lkp.summandProduct keys [] fun p => Lkp.byVariable p order) last1
    e0 e1 (h0.1.trans h1'.1.symm) hq1 hf1
  rw [hmk] at hl
  refine ⟨hf2, hl, hk, ?_, ?_, ?_⟩
  · simp only [Caller.Stand.levelVal, he, List.getD_cons_zero, List.getD_cons_succ]
    simp [lineAt, h0.1, hpt, hvars]
  · intro hkeys
    simp only [Caller.Stand.levelVal, he, List.getD_cons_zero, List.getD_cons_succ]
    exact Caller.slotsOK_append (Caller.slotsOK_scale _ (h0.2 hkeys))
      (Caller.slotsOK_scale _ (h1'.2 hkeys))
  · rw [← hsz]
    refine (bind_ok hrun).trans ?_
    rw [he]
    simp only [Caller.Stand.levelVal, he, List.getD_cons_zero, List.getD_cons_succ]
    exact hline

/-- The entries of the first ledger that the levels l, l + 1, .. of a tree take, n of them. keys:
the tree is a key tree, whose last level takes two entries from the second ledger. -/
def chainOwn (keys : Bool) (more : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | l, n + 1 => ownOf (2 * (l + more) + 5) (keys && n == 0) + chainOwn keys more (l + 1) n

/-- The entries of the second ledger that the last n levels of a tree take. -/
def chainKey (keys : Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => keyOf (keys && n == 0) + chainKey keys n

/-- The last n levels of a product tree. -/
def Caller.Stand.chainVal (keys : Bool) (levels more : Nat) :
    Nat → PointClaim → C.Stand → PointClaim × C.Stand
  | 0, c, s => (c, s)
  | n + 1, c, s =>
    let x := s.levelVal (orderAt C.S keys levels more (levels - (n + 1))) (keys && n == 0) c
    Caller.Stand.chainVal keys levels more n x.1 x.2

/-- The levels of a product tree, with every value named. -/
theorem Caller.Laws.chain_val (L : C.Laws) (work : Nat) (keys : Bool) (levels more : Nat)
    (hord : ∀ l, l < levels → (orderAt C.S keys levels more l).length = more + l)
    (es' : List Fmt.Entry) :
    ∀ (n : Nat) (c : PointClaim) (s : C.Stand) (last : Option Fmt.Entry), n ≤ levels →
      c.point.length = more + (levels - n) → ((0 < n ∨ keys = false) → C.SlotsOK c.masks) →
      NoRows last → FitsAll s.rounds (chainEntries work more (levels - n) n ++ es') →
      chainOwn keys more (levels - n) n ≤ C.left s.led → chainKey keys n ≤ C.keyLeft s.led →
      ∃ last', NoRows last' ∧ FitsAll (Caller.Stand.chainVal keys levels more n c s).2.rounds es' ∧
        C.left (Caller.Stand.chainVal keys levels more n c s).2.led =
          C.left s.led - chainOwn keys more (levels - n) n ∧
        C.keyLeft (Caller.Stand.chainVal keys levels more n c s).2.led =
          C.keyLeft s.led - chainKey keys n ∧
        (Caller.Stand.chainVal keys levels more n c s).1.point.length = more + levels ∧
        (keys = false → C.SlotsOK (Caller.Stand.chainVal keys levels more n c s).1.masks) ∧
        (Lkp.levelChain C.env keys levels more n c)
          (s.ctx (chainEntries work more (levels - n) n ++ es') last) =
          .ok ((Caller.Stand.chainVal keys levels more n c s).1,
            (Caller.Stand.chainVal keys levels more n c s).2.ctx es' last')
  | 0, c, s, last, _, hc, hm, hq, hfit, _, _ =>
    ⟨last, hq, hfit, rfl, rfl, by simpa using hc, fun hk => hm (Or.inr hk), rfl⟩
  | n + 1, c, s, last, hn, hc, hm, hq, hfit, h1, h2 => by
    have hl : levels - (n + 1) < levels := by omega
    have ho := hord _ hl
    have hnext : levels - (n + 1) + 1 = levels - n := by omega
    have hlen : levels - (n + 1) + more =
        (orderAt C.S keys levels more (levels - (n + 1))).length := by
      rw [ho]; omega
    have hflag : (keys && levels - (n + 1) + 1 == levels) = (keys && n == 0) := by
      have hb : (levels - (n + 1) + 1 == levels) = (n == 0) := by
        by_cases h0 : n = 0
        · subst h0
          have h3 : levels - (0 + 1) + 1 = levels := by omega
          rw [h3]
          simp
        · have h3 : levels - (n + 1) + 1 ≠ levels := by omega
          rw [beq_eq_false_iff_ne.2 h3, beq_eq_false_iff_ne.2 h0]
      rw [hb]
    simp only [chainEntries, chainOwn, chainKey, List.append_assoc, List.cons_append, hnext,
      hlen] at hfit h1 h2 ⊢
    obtain ⟨hf1, hl1, hk1, hc1, hm1, hrun1⟩ :=
      L.level_val work (orderAt C.S keys levels more (levels - (n + 1))) (keys && n == 0)
        (chainEntries work more (levels - n) n ++ es') s last c
        ⟨by rw [ho]; exact hc, hm (Or.inl (Nat.succ_pos n))⟩ hq hfit (by omega) (by omega)
    obtain ⟨last', hq', hf', hl', hk', hc', hm', hrun'⟩ :=
      Caller.Laws.chain_val L work keys levels more hord es' n
        (s.levelVal (orderAt C.S keys levels more (levels - (n + 1))) (keys && n == 0) c).1
        (s.levelVal (orderAt C.S keys levels more (levels - (n + 1))) (keys && n == 0) c).2 _
            (by omega)
        (by rw [ho] at hc1; rw [← hnext, ← Nat.add_assoc]; exact hc1)
        (by
          intro hor
          apply hm1
          rcases hor with h0 | h0
          · have : (n == 0) = false := beq_eq_false_iff_ne.2 (by omega)
            simp [this]
          · simp [h0])
        (noRows_rDraw "LINE" work 1) hf1
        (by rw [hl1]; omega) (by rw [hk1]; omega)
    have hv : Caller.Stand.chainVal keys levels more (n + 1) c s =
        Caller.Stand.chainVal keys levels more n
          (s.levelVal (orderAt C.S keys levels more (levels - (n + 1))) (keys && n == 0) c).1
          (s.levelVal (orderAt C.S keys levels more (levels - (n + 1))) (keys && n == 0) c).2 := rfl
    rw [hv]
    refine ⟨last', hq', hf', by rw [hl', hl1]; omega, by rw [hk', hk1]; omega, hc', hm', ?_⟩
    show ((Blk.must ((orderAt C.S keys levels more (levels - (n + 1))).length ==
          more + (levels - (n + 1)) &&
        c.point.length == more + (levels - (n + 1)))) >>= fun _ =>
      (Lkp.psc C.env (levelSum c (orderAt C.S keys levels more (levels - (n + 1))))
          Lkp.summandProduct
        (keys && levels - (n + 1) + 1 == levels) []
        fun p => Lkp.byVariable p (orderAt C.S keys levels more (levels - (n + 1)))) >>= fun o =>
      match o.ends with
      | [e0, e1] => line e0 e1 >>= fun next => Lkp.levelChain C.env keys levels more n next
      | _ => Blk.fail) _ = _
    rw [bind_ok (must_ok (by simp [ho, hc]) _), hflag]
    refine (congrFun (level_assoc _ _) _).trans ?_
    refine (bind_ok hrun1).trans ?_
    exact hrun'

/-! ## Sumchecks without a variable: the tie and the parts -/

/-- A sumcheck without a variable, with every value named. -/
theorem Caller.Laws.value_val (L : C.Laws) (work : Nat) (cl : Psc.Claim) (hcl : cl.vars = [])
    (Sm : Psc.Summand) (hs : 0 < Sm.shown) (hdg : 0 < Sm.degree) (hk0 : Sm.kept = 0)
    (ha : ∀ p y, (Sm.coeffs p y).length = 1 + Sm.kept) (es' : List Fmt.Entry) (s : C.Stand) (last)
    (hq : NoRows last)
    (hfit : FitsAll s.rounds (pscEntries work
      { degree := [], withY := true, degreeY := Sm.degree, values := Sm.shown } ++ es'))
    (hk : 1 + Sm.degree + Sm.shown ≤ C.left s.led) (hm : C.SlotsOK cl.masks) :
    ∃ last', NoRows last' ∧ FitsAll (s.afterPsc cl Sm false [] id).rounds es' ∧
      C.left (s.afterPsc cl Sm false [] id).led = C.left s.led - (1 + Sm.degree + Sm.shown) ∧
      C.keyLeft (s.afterPsc cl Sm false [] id).led = C.keyLeft s.led ∧
      (s.pscOut cl Sm false id).ends.length = Sm.shown ∧
      (∀ e ∈ (s.pscOut cl Sm false id).ends, C.ClaimOK 0 e) ∧
      (Lkp.psc C.env cl Sm)
          (s.ctx (pscEntries work
            { degree := [], withY := true, degreeY := Sm.degree, values := Sm.shown } ++ es') last)
                =
        .ok (s.pscOut cl Sm false id, (s.afterPsc cl Sm false [] id).ctx es' last') := by
  have hne0 : Sm.shown ≠ 0 := Nat.pos_iff_ne_zero.1 hs
  have hdne : Sm.degree ≠ 0 := Nat.pos_iff_ne_zero.1 hdg
  have hsz : Psc.sizeOf cl Sm =
      { degree := [], withY := true, degreeY := Sm.degree, values := Sm.shown } := by
    simp [Psc.sizeOf, hcl, hs]
  have hvo : Psc.varsOf cl Sm = [Psc.Weight.atZero (Sm.degree + 1)] := by
    simp [Psc.varsOf, hcl, hne0]
  have hmk : Psc.masksOf cl Sm = 1 + Sm.degree + Sm.shown := by
    simp [Psc.masksOf, hvo, Psc.hidingEntries, Psc.Weight.atZero, Psc.Weight.equality]
  obtain ⟨last', hf', hq', hrun, hpt, hends, hall, hl, hkl⟩ :=
    L.psc_val work cl Sm false [] id es' s last hq (by rw [hsz]; exact hfit)
      (by
        have b1 : (Sm.shown == 0) = false := by simp [hne0]
        have b2 : (Sm.degree == 0) = false := by simp [hdne]
        simp [Psc.formOK, hcl, hs, b1, b2]) ha
      (by rw [hvo]; intro x hx; simp at hx; subst hx; simp [Psc.Weight.atZero, Psc.Weight.equality])
      (by rw [hvo]; simp) (by simp [hcl]) (by rw [hmk]; exact hk) (Nat.zero_le _)
      (by intro h; cases h) (Nat.zero_le _) hm (by simp [hk0]) (by intro m hm'; simp at hm')
          (fun _ => rfl)
  rw [hmk] at hl
  refine ⟨last', hq', hf', hl, hkl, hends, ?_, ?_⟩
  · intro e he
    obtain ⟨h1, h2⟩ := hall e he
    exact ⟨by rw [h1, hpt, hcl]; rfl, h2 rfl⟩
  · rw [← hsz]
    exact hrun

/-- The last n steps of the tie: the claims on the planes' roots and on the last power, and the
stand after them. -/
def Caller.Stand.tieVal : Nat → PointClaim → C.Stand → List PointClaim × C.Stand
  | 0, c, s => ([c], s)
  | n + 1, c, s =>
    let o := s.pscOut (valueSum c) Lkp.summandTie false id
    let x := Caller.Stand.tieVal n (o.ends.getD 0 default)
      (s.afterPsc (valueSum c) Lkp.summandTie false [] id)
    (o.ends.getD 1 default :: x.1, x.2)

/-- A claim on a value as a sum without variables. -/
theorem Caller.onValue_val (c : PointClaim) (hc : C.ClaimOK 0 c) (x : Ctx) :
    (Lkp.onValue c) x = .ok (valueSum c, x) := by
  have hp : c.point = [] := List.length_eq_zero_iff.1 hc.1
  simp [Lkp.onValue, Psc.Claim.atPoint, hp, get_ok, valueSum]

/-- The later steps of the tie, with every value named. -/
theorem Caller.Laws.tie_val (L : C.Laws) (work : Nat) (es' : List Fmt.Entry) :
    ∀ (n : Nat) (c : PointClaim) (s : C.Stand) (last : Option Fmt.Entry), C.ClaimOK 0 c →
      NoRows last → FitsAll s.rounds (tieEntries work n ++ es') → 6 * n ≤ C.left s.led →
      ∃ last', NoRows last' ∧ FitsAll (Caller.Stand.tieVal n c s).2.rounds es' ∧
        C.left (Caller.Stand.tieVal n c s).2.led = C.left s.led - 6 * n ∧
        C.keyLeft (Caller.Stand.tieVal n c s).2.led = C.keyLeft s.led ∧
        (∀ x ∈ (Caller.Stand.tieVal n c s).1, C.ClaimOK 0 x) ∧
        (Lkp.tieSteps C.env n c) (s.ctx (tieEntries work n ++ es') last) =
          .ok ((Caller.Stand.tieVal n c s).1, (Caller.Stand.tieVal n c s).2.ctx es' last')
  | 0, c, s, last, hc, hq, hfit, _ =>
    ⟨last, hq, hfit, rfl, rfl,
      by intro x hx; simp [Caller.Stand.tieVal] at hx; subst hx; exact hc, rfl⟩
  | n + 1, c, s, last, hc, hq, hfit, hk => by
    simp only [tieEntries, List.append_assoc] at hfit ⊢
    obtain ⟨last1, hq1, hf1, hl1, hk1, hends, hall, hrun1⟩ :=
      L.value_val work (valueSum c) rfl Lkp.summandTie (by decide) (by decide) rfl (fun _ _ => rfl)
        (tieEntries work n ++ es') s last hq hfit (by show 1 + 3 + 2 ≤ _; omega) hc.2
    obtain ⟨power, plane, he⟩ : ∃ a b, (s.pscOut (valueSum c) Lkp.summandTie false id).ends =
        [a, b] := by
      have h2 : (s.pscOut (valueSum c) Lkp.summandTie false id).ends.length = 2 := hends
      match (s.pscOut (valueSum c) Lkp.summandTie false id).ends, h2 with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    have hl1' : C.left (s.afterPsc (valueSum c) Lkp.summandTie false [] id).led = C.left s.led -
        6 := hl1
    obtain ⟨last', hq', hf', hl', hk', hl, hrun'⟩ :=
      Caller.Laws.tie_val L work es' n power (s.afterPsc (valueSum c) Lkp.summandTie false [] id)
          last1
        (hall power (by simp [he])) hq1 hf1 (by rw [hl1']; omega)
    have hv : Caller.Stand.tieVal (n + 1) c s =
        (plane :: (Caller.Stand.tieVal n power
            (s.afterPsc (valueSum c) Lkp.summandTie false [] id)).1,
          (Caller.Stand.tieVal n power
              (s.afterPsc (valueSum c) Lkp.summandTie false [] id)).2) := by
      simp [Caller.Stand.tieVal, he]
    rw [hv]
    refine ⟨last', hq', hf', by rw [hl', hl1']; omega, by rw [hk', hk1], ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hall _ (by simp [he])
      · exact hl x hx
    · show ((Lkp.onValue c) >>= fun cl => (Lkp.psc C.env cl Lkp.summandTie) >>= fun o =>
        match o.ends with
        | [power, plane] => (Lkp.tieSteps C.env n power) >>= fun rest => pure (plane :: rest)
        | _ => Blk.fail) _ = _
      rw [bind_ok (Caller.onValue_val c hc _)]
      refine (bind_ok hrun1).trans ?_
      rw [he]
      show ((Lkp.tieSteps C.env n power) >>= fun rest => pure (plane :: rest)) _ = _
      refine (bind_ok hrun').trans ?_
      rfl

/-- The entries of n steps from the product of the parts' roots to each root. -/
def partEntries (work : Nat) : Nat → List Fmt.Entry
  | 0 => []
  | n + 1 => pscEntries work { degree := [], degreeY := 2, values := 2 } ++ partEntries work n

/-- The last n steps from the product of the parts' roots to each root: the claims on the roots, and
the stand after them. -/
def Caller.Stand.partVal : Nat → PointClaim → C.Stand → List PointClaim × C.Stand
  | 0, c, s => ([c], s)
  | n + 1, c, s =>
    let o := s.pscOut (valueSum c) Lkp.summandProduct false id
    let x := Caller.Stand.partVal n (o.ends.getD 1 default)
      (s.afterPsc (valueSum c) Lkp.summandProduct false [] id)
    (o.ends.getD 0 default :: x.1, x.2)

/-- The parts' steps, with every value named. -/
theorem Caller.Laws.part_val (L : C.Laws) (work : Nat) (es' : List Fmt.Entry) :
    ∀ (n : Nat) (c : PointClaim) (s : C.Stand) (last : Option Fmt.Entry), C.ClaimOK 0 c →
      NoRows last → FitsAll s.rounds (partEntries work n ++ es') → 5 * n ≤ C.left s.led →
      ∃ last', NoRows last' ∧ FitsAll (Caller.Stand.partVal n c s).2.rounds es' ∧
        C.left (Caller.Stand.partVal n c s).2.led = C.left s.led - 5 * n ∧
        C.keyLeft (Caller.Stand.partVal n c s).2.led = C.keyLeft s.led ∧
        (Caller.Stand.partVal n c s).1.length = n + 1 ∧
        (∀ x ∈ (Caller.Stand.partVal n c s).1, C.ClaimOK 0 x) ∧
        (Lkp.partSteps C.env n c) (s.ctx (partEntries work n ++ es') last) =
          .ok ((Caller.Stand.partVal n c s).1, (Caller.Stand.partVal n c s).2.ctx es' last')
  | 0, c, s, last, hc, hq, hfit, _ =>
    ⟨last, hq, hfit, rfl, rfl, rfl,
      by intro x hx; simp [Caller.Stand.partVal] at hx; subst hx; exact hc, rfl⟩
  | n + 1, c, s, last, hc, hq, hfit, hk => by
    simp only [partEntries, List.append_assoc] at hfit ⊢
    obtain ⟨last1, hq1, hf1, hl1, hk1, hends, hall, hrun1⟩ :=
      L.value_val work (valueSum c) rfl Lkp.summandProduct (by decide) (by decide) rfl
        (fun _ _ => rfl) (partEntries work n ++ es') s last hq hfit (by show 1 + 2 + 2 ≤ _; omega)
            hc.2
    obtain ⟨root, rest, he⟩ : ∃ a b,
        (s.pscOut (valueSum c) Lkp.summandProduct false id).ends = [a, b] := by
      have h2 : (s.pscOut (valueSum c) Lkp.summandProduct false id).ends.length = 2 := hends
      match (s.pscOut (valueSum c) Lkp.summandProduct false id).ends, h2 with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    have hl1' : C.left (s.afterPsc (valueSum c) Lkp.summandProduct false [] id).led =
        C.left s.led - 5 := hl1
    obtain ⟨last', hq', hf', hl', hk', hlen, hl, hrun'⟩ :=
      Caller.Laws.part_val L work es' n rest
          (s.afterPsc (valueSum c) Lkp.summandProduct false [] id)
        last1 (hall rest (by simp [he])) hq1 hf1 (by rw [hl1']; omega)
    have hv : Caller.Stand.partVal (n + 1) c s =
        (root :: (Caller.Stand.partVal n rest
            (s.afterPsc (valueSum c) Lkp.summandProduct false [] id)).1,
          (Caller.Stand.partVal n rest
              (s.afterPsc (valueSum c) Lkp.summandProduct false [] id)).2) := by
      simp [Caller.Stand.partVal, he]
    rw [hv]
    refine ⟨last', hq', hf', by rw [hl', hl1']; omega, by rw [hk', hk1], by simp [hlen], ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hall _ (by simp [he])
      · exact hl x hx
    · show ((Lkp.onValue c) >>= fun cl => (Lkp.psc C.env cl Lkp.summandProduct) >>= fun o =>
        match o.ends with
        | [root, rest] => (Lkp.partSteps C.env n rest) >>= fun more => pure (root :: more)
        | _ => Blk.fail) _ = _
      rw [bind_ok (Caller.onValue_val c hc _)]
      refine (bind_ok hrun1).trans ?_
      rw [he]
      show ((Lkp.partSteps C.env n rest) >>= fun more => pure (root :: more)) _ = _
      refine (bind_ok hrun').trans ?_
      rfl

/-! ## The key trees of all parts -/

/-- The entries of the key trees of parts of the given sizes in bits. -/
def treesEntries (work : Nat) : List Nat → List Fmt.Entry
  | [] => []
  | v :: vs => chainEntries work 0 (v - v) v ++ treesEntries work vs

/-- The entries of the first ledger that these trees take. -/
def treesOwn : List Nat → Nat
  | [] => 0
  | v :: vs => chainOwn true 0 (v - v) v + treesOwn vs

/-- The entries of the second ledger that these trees take. -/
def treesKey : List Nat → Nat
  | [] => 0
  | v :: vs => chainKey true v + treesKey vs

/-- The key trees of all parts: the claims on their leaves, and the stand after them. -/
def Caller.Stand.treesVal : List Nat → List PointClaim → C.Stand → List PointClaim × C.Stand
  | v :: vs, c :: cs, s =>
    let x := Caller.Stand.chainVal true v 0 v c s
    let rest := Caller.Stand.treesVal vs cs x.2
    (x.1 :: rest.1, rest.2)
  | _, _, s => ([], s)

/-- The claims are at points of the given numbers of coordinates, one by one, and there are as many.
-/
def PointsAt : List Nat → List PointClaim → Prop
  | [], [] => True
  | v :: vs, c :: cs => c.point.length = v ∧ PointsAt vs cs
  | _, _ => False

/-- The key trees of all parts, with every value named. -/
theorem Caller.Laws.trees_val (L : C.Laws) (work : Nat) (es' : List Fmt.Entry) :
    ∀ (vs : List Nat) (cs : List PointClaim) (s : C.Stand) (last : Option Fmt.Entry),
      cs.length = vs.length → (∀ c ∈ cs, C.ClaimOK 0 c) →
      (∀ v ∈ vs, (Lkp.orderBeginning C.S.lastKeyLevelOrder (v - 1)).length = v - 1) → NoRows last →
      FitsAll s.rounds (treesEntries work vs ++ es') → treesOwn vs ≤ C.left s.led →
      treesKey vs ≤ C.keyLeft s.led →
      ∃ last', NoRows last' ∧ FitsAll (Caller.Stand.treesVal vs cs s).2.rounds es' ∧
        C.left (Caller.Stand.treesVal vs cs s).2.led = C.left s.led - treesOwn vs ∧
        C.keyLeft (Caller.Stand.treesVal vs cs s).2.led = C.keyLeft s.led - treesKey vs ∧
        PointsAt vs (Caller.Stand.treesVal vs cs s).1 ∧
        (Lkp.keyTrees C.env vs cs) (s.ctx (treesEntries work vs ++ es') last) =
          .ok ((Caller.Stand.treesVal vs cs s).1, (Caller.Stand.treesVal vs cs s).2.ctx es' last')
  | [], [], s, last, _, _, _, hq, hfit, _, _ =>
    ⟨last, hq, hfit, rfl, rfl, trivial, rfl⟩
  | [], _ :: _, _, _, h, _, _, _, _, _, _ => by simp at h
  | _ :: _, [], _, _, h, _, _, _, _, _, _ => by simp at h
  | v :: vs, c :: cs, s, last, hlen, hcs, hord, hq, hfit, h1, h2 => by
    simp only [treesEntries, treesOwn, treesKey, List.append_assoc] at hfit h1 h2 ⊢
    obtain ⟨last1, hq1, hf1, hl1, hk1, hc1, _, hrun1⟩ :=
      L.chain_val work true v 0 (orderAt_keys C.S v (hord v (by simp)))
          (treesEntries work vs ++ es') v c s
        last (Nat.le_refl v) (by have := (hcs c (by simp)).1; simpa using this)
        (fun _ => (hcs c (by simp)).2) hq hfit (by omega) (by omega)
    obtain ⟨last', hq', hf', hl', hk', hall, hrun'⟩ :=
      Caller.Laws.trees_val L work es' vs cs (Caller.Stand.chainVal true v 0 v c s).2 last1
        (by simpa using hlen) (fun x hx => hcs x (by simp [hx])) (fun x hx => hord x (by simp [hx]))
            hq1
        hf1 (by rw [hl1]; omega) (by rw [hk1]; omega)
    have hv : Caller.Stand.treesVal (v :: vs) (c :: cs) s =
        ((Caller.Stand.chainVal true v 0 v c s).1 ::
            (Caller.Stand.treesVal vs cs (Caller.Stand.chainVal true v 0 v c s).2).1,
          (Caller.Stand.treesVal vs cs (Caller.Stand.chainVal true v 0 v c s).2).2) := rfl
    rw [hv]
    refine ⟨last', hq', hf', by rw [hl', hl1]; omega, by rw [hk', hk1]; omega,
      ⟨by simpa using hc1, hall⟩, ?_⟩
    show ((Lkp.levelChain C.env true v 0 v c) >>= fun x =>
      (Lkp.keyTrees C.env vs cs) >>= fun rest => pure (x :: rest)) _ = _
    refine (bind_ok hrun1).trans ?_
    refine (bind_ok hrun').trans ?_
    rfl

end OnBytes.G4
