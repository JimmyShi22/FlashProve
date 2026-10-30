-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/CloseMeans.lean: THEOREMS: WHAT A YES OF THE CLOSING OF A LINK GIVES
(Johnson/Desc/First/Close/Closing.lean: `heard`, `bat`, `rounds`, `fold`, `closing`, `closeFrame`):
for each of the six a proposition with A CONJUNCT FOR EACH NAMED GUARD, what is handed on written
out, and a theorem that the text says yes JUST IF that proposition holds. No block imports this
file, and no byte of a text turns.

What is said (each an "if and only if", at all arguments).
  `closeFrame_iff`: **`closeFrame owed f S es rs = .ok (f', S')` just if `CloseMeans …`**: K10.owed
    · K10.link · K10.group · K10.due · `ClosingMeans` · and f' is f with the rows that the closing
    hands on, no mask, the next link, `next := .first`.
  `closing_iff`, `ClosingMeans`: K10.stretch · K10.mask · `BatMeans` · K10.kh · `FoldMeans` at the
    plan's shape of the fold.
  `bat_iff`, `BatMeans`: the ground's four clauses of `beginRunL` · K10.layout · the round "BAT"
    (`HeardMeans`) · K10.rows · K10.combine · the layout and the statement behind.
  `fold_iff`, `FoldMeans`: K10.stretch · K10.norows · K10.shape · K10.maskfits · the ground's four
    clauses of `spendAsMaskL` · the round "FOLD epsilon" · K10.rowfits · `RoundsMeans` · what the
    fold puts out.
  `rounds_iff`, `RoundsMeans`: as many entries as rounds; each "FOLD round" holds two coefficients
    and draws one element; the challenges in order; the running claim.
  `heard_iff`, `HeardMeans`: K10.name · K10.nonzero · K10.entry · K10.items · K10.draws · K10.one.

WHAT THE GUARDS READ. The plan's entries and the frame's public shape; the statement's book-keeping
(groups, members, shapes, spent marks); OF WHAT A PROVER SENT: how many items a round holds and that
each is an element of the field (K10.items); of what was drawn: how many (K10.draws, K10.one). NO
GUARD COMPARES A SENT VALUE WITH ANYTHING: the sent coefficients go into the running claim and the
output (`foldClaimRound`, `foldOutput`), which later tests read.

NAMED, NOT OPENED. The ground's clauses and effects (`Ground.beginRunL | beginRunP | spendAsMaskL |
spendAsMaskP`: First/Base/Ground.lean). `Own.batch` (K10.combine) and the fold's three tests
`Own.foldShapeFits | foldMaskFits | foldRowFits`: what each of the three asks, as a proposition:
Johnson/Desc/Own/FoldMean.lean. `foldOutput`, `foldClaimRound`, `ioppFoldShape`, `reqMoments`: the
library's, and they cannot refuse.

THEY ADD NO SECOND, INDEPENDENT EYE: the propositions are the texts read aloud. What a yes MEANS for
the rows (the one direction that a law uses) is other files': Law/Inv.lean, InvMore.lean,
Whole.lean, Lays.lean. Called from Law/Inv.lean, not typed again: `ok_bind`, `need_ok`, `got_ok`.

Limits. `foldD` is taken at a mask that came in an earlier message (`fold`): the arm in which the
fold enters its own mask is not a link's. Nothing on soundness, on an honest prover or on hiding. A
yes on made-up data, and a no under each name for which such data were found: CloseToys.lean, beside
this file; its head lists the names that have no line (K10.layout; three of `spendAsMaskL`'s four).
THAT THESE CANNOT REFUSE IS SHOWN BY NOTHING.

-/
import Johnson.Desc.First.Close.Law.Inv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes

/-! ## 0 Steps of a text that can refuse -/

theorem ok_bind_iff {α β : Type} (x : Except String α) (f : α → Except String β) (y : β) :
    (x >>= f) = .ok y ↔ ∃ a, x = .ok a ∧ f a = .ok y :=
  ⟨ok_bind, by rintro ⟨a, rfl, h⟩; exact h⟩

theorem need_ok_iff (n : String) (b : Bool) (u : Unit) : need n b = .ok u ↔ b = true :=
  ⟨need_ok, fun h => by rw [h]; rfl⟩

theorem need_then_iff {β : Type} (n : String) (b : Bool) (f : Unit → Except String β) (y : β) :
    (need n b >>= f) = .ok y ↔ b = true ∧ f () = .ok y := by
  rw [ok_bind_iff]
  exact ⟨fun ⟨_, h1, h2⟩ => ⟨need_ok h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(), (need_ok_iff n b ()).2 h1, h2⟩⟩

theorem got_ok_iff {α : Type} (n : String) (x : Option α) (a : α) : got n x = .ok a ↔ x = some a :=
  ⟨got_ok, fun h => by rw [h]; rfl⟩

theorem got_then_iff {α β : Type} (n : String) (x : Option α) (f : α → Except String β) (y : β) :
    (got n x >>= f) = .ok y ↔ ∃ a, x = some a ∧ f a = .ok y := by
  rw [ok_bind_iff]
  exact ⟨fun ⟨a, h1, h2⟩ => ⟨a, got_ok h1, h2⟩, fun ⟨a, h1, h2⟩ => ⟨a, (got_ok_iff n x a).2 h1, h2⟩⟩

/-- The ground's clauses, asked one by one under their names: a yes just if all hold. -/
theorem named_ok_iff (l : Ground.Clauses) (u : Unit) :
    named l = .ok u ↔ ∀ c ∈ l, c.2 = true := by
  unfold named
  cases h : l.find? (!·.2) with
  | none =>
    rw [List.find?_eq_none] at h
    exact ⟨fun _ c hc => by simpa using h c hc, fun _ => rfl⟩
  | some c =>
    have h1 := List.find?_some h
    have h2 := List.mem_of_find?_eq_some h
    refine ⟨fun e => (by cases e), fun a => ?_⟩
    rw [a c h2] at h1
    cases h1

theorem named_then_iff {β : Type} (l : Ground.Clauses) (f : Unit → Except String β) (y : β) :
    (named l >>= f) = .ok y ↔ (∀ c ∈ l, c.2 = true) ∧ f () = .ok y := by
  rw [ok_bind_iff]
  exact ⟨fun ⟨u, h1, h2⟩ => ⟨(named_ok_iff l u).1 h1, h2⟩,
    fun ⟨h1, h2⟩ => ⟨(), (named_ok_iff l ()).2 h1, h2⟩⟩

theorem map_ok_iff {α β : Type} (x : Except String α) (f : α → β) (y : β) :
    x.map f = .ok y ↔ ∃ a, x = .ok a ∧ f a = y := by
  cases x <;> simp [Except.map]

/-! ## 1 A round that is heard -/

/-- A round's items, where each is an element of the extension field. -/
def elemsOf (vs : List Fmt.ItemValue) : Option (List E) :=
  vs.mapM fun v =>
    match v with
    | .e x => some (E.ofTriple x)
    | _ => none

/-- **What a yes of `heard` gives**: a conjunct for each named guard. -/
def HeardMeans (name : String) (items : Nat) (e : Fmt.Entry) (r : Fmt.RoundView) (roots : Nat)
    (xs : List E) (x : E) : Prop :=
  -- K10.name
  e.name = name ∧
  -- K10.nonzero
  e.drawNZ = 0 ∧
  -- K10.entry
  (e.count = 1 ∧ e.msg = 24 * items + 32 * roots ∧ e.roots = roots ∧ e.answers = 0 ∧ e.poss = 0 ∧
    e.trits = 0) ∧
  -- K10.items: how many
  r.vals.length = items ∧
  -- K10.draws
  (r.drawn.elems.length = e.drawE ∧ r.drawn.poss.length = e.poss ∧
    r.drawn.trits.length = e.trits) ∧
  -- K10.items: each an element
  elemsOf r.vals = some xs ∧
  -- K10.one
  ∃ t, r.drawn.elems = [t] ∧ x = E.ofTriple t

theorem heard_iff (name : String) (items : Nat) (e : Fmt.Entry) (r : Fmt.RoundView) (roots : Nat)
    (xs : List E) (x : E) :
    heard name items e r roots = .ok (xs, x) ↔ HeardMeans name items e r roots xs x := by
  unfold heard HeardMeans
  rw [need_then_iff, need_then_iff, need_then_iff, need_then_iff, need_then_iff, got_then_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨ys, h1, h⟩
    split at h
    · rename_i t ht
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨h1, t, ht, rfl⟩
    · cases h
  · rintro ⟨h1, t, ht, rfl⟩
    refine ⟨xs, h1, ?_⟩
    rw [ht]
    rfl

/-! ## 2 The batching -/

/-- **What a yes of the batching gives.** The ground's clauses (`beginRunL`) and its effect
(`beginRunP`) are named, not opened. -/
def BatMeans (S : Statement) (g : Nat) (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow)
    (L : GroupLayout) (S1 : Statement) : Prop :=
  -- the ground's four, each under its own name
  (∀ c ∈ Ground.beginRunL S g, c.2 = true) ∧
  -- K10.layout
  ∃ input d, Ground.beginRunP (onSt S) g = some (input, d) ∧
  -- the round "BAT": nothing is sent, one element is drawn
  ∃ xs x, HeardMeans "BAT" 0 e r 0 xs x ∧
  -- K10.rows
  e.rows = input.rows.size ∧
  -- K10.combine
  Own.batch d.st g input x = some row ∧
  L = input.layout ∧ S1 = d.st

theorem bat_iff (S : Statement) (g : Nat) (e : Fmt.Entry) (r : Fmt.RoundView) (row : GroupRow)
    (L : GroupLayout) (S1 : Statement) :
    bat S g e r = .ok (row, L, S1) ↔ BatMeans S g e r row L S1 := by
  unfold bat BatMeans
  rw [named_then_iff, got_then_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨⟨input, d⟩, k1, h⟩
    obtain ⟨x, k2, h⟩ := ok_bind h
    obtain ⟨⟨xs, x'⟩, k2', rfl⟩ := (map_ok_iff _ _ _).1 k2
    obtain ⟨k3, h⟩ := (need_then_iff _ _ _ _).1 h
    obtain ⟨row', k4, h⟩ := (got_then_iff _ _ _ _).1 h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨input, d, k1, xs, x', (heard_iff _ _ _ _ _ _ _).1 k2', beq_iff_eq.1 k3, k4, rfl, rfl⟩
  · rintro ⟨input, d, k1, xs, x, k2, k3, k4, rfl, rfl⟩
    refine ⟨(input, d), k1, ?_⟩
    refine (ok_bind_iff _ _ _).2 ⟨x, (map_ok_iff _ _ _).2 ⟨(xs, x), (heard_iff _ _ _ _ _ _ _).2 k2,
      rfl⟩, ?_⟩
    refine (need_then_iff _ _ _ _).2 ⟨beq_iff_eq.2 k3, ?_⟩
    exact (got_then_iff _ _ _ _).2 ⟨row, k4, rfl⟩

/-! ## 3 The fold -/

/-- **What a yes of the fold's rounds gives**: as many entries as rounds (K10.stretch); each round
"FOLD round" holds two coefficients and draws one element; the challenges in order; the running
claim behind the last. -/
def RoundsMeans : List Fmt.Entry → List Fmt.RoundView → E → List E → E → Prop
  | [], [], claim, gs, cl => gs = [] ∧ cl = claim
  | e :: es, r :: rs, claim, gs, cl =>
    ∃ c0 c2 g gs', HeardMeans "FOLD round" 2 e r 0 [c0, c2] g ∧
      RoundsMeans es rs (foldClaimRound claim c0 c2 g) gs' cl ∧ gs = g :: gs'
  | [], _ :: _, _, _, _ => False
  | _ :: _, [], _, _, _ => False

theorem rounds_iff : ∀ (es : List Fmt.Entry) (rs : List Fmt.RoundView) (claim : E) (gs : List E) (cl : E),
    rounds es rs claim = .ok (gs, cl) ↔ RoundsMeans es rs claim gs cl
  | [], [], claim, gs, cl => by
    simp only [rounds, RoundsMeans, Except.ok.injEq, Prod.mk.injEq]
    exact ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩
  | e :: es, r :: rs, claim, gs, cl => by
    rw [rounds, RoundsMeans, ok_bind_iff]
    constructor
    · rintro ⟨y, h1, h⟩
      split at h
      · rename_i c0 c2 g
        obtain ⟨x, h2, h⟩ := ok_bind h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨c0, c2, g, x.1, (heard_iff _ _ _ _ _ _ _).1 h1,
          (rounds_iff es rs _ x.1 x.2).1 h2, rfl⟩
      · cases h
    · rintro ⟨c0, c2, g, gs', h1, h2, rfl⟩
      refine ⟨([c0, c2], g), (heard_iff _ _ _ _ _ _ _).2 h1, ?_⟩
      exact (ok_bind_iff _ _ _).2 ⟨(gs', cl), (rounds_iff es rs _ gs' cl).2 h2, rfl⟩
  | [], _ :: _, _, _, _ => by simp [rounds, RoundsMeans]
  | _ :: _, [], _, _, _ => by simp [rounds, RoundsMeans]

/-- **What a yes of the fold gives**, its fresh mask sent in an earlier message. The three tests of
Johnson/Desc/Own/Fold.lean are named (what each asks, as a proposition:
Johnson/Desc/Own/FoldMean.lean); the ground's clauses (`spendAsMaskL`) and effect (`spendAsMaskP`)
are named, not opened. -/
def FoldMeans (S : Statement) (F : FoldShape) (row : GroupRow) (m : Nat) (es : List Fmt.Entry)
    (rs : List Fmt.RoundView) (out : SingleRows) (S' : Statement) : Prop :=
  ∃ eE eR rE rR, es = eE :: eR ∧ rs = rE :: rR ∧
  -- K10.stretch
  (eR.length = F.layout.k ∧ rR.length = F.layout.k) ∧
  -- K10.norows
  (∀ e ∈ es, e.rows = 0) ∧
  -- K10.shape
  Own.foldShapeFits S F = true ∧
  -- K10.maskfits
  Own.foldMaskFits S F m = true ∧
  -- the ground's four, each under its own name
  (∀ c ∈ Ground.spendAsMaskL S m, c.2 = true) ∧
  ∃ d2, Ground.spendAsMaskP (onSt S) m = some d2 ∧
  -- the round "FOLD epsilon": one element is sent, one is drawn, no root
  ∃ sum eps, HeardMeans "FOLD epsilon" 1 eE rE 0 [sum] eps ∧
  -- K10.rowfits
  Own.foldRowFits d2.st F row = true ∧
  ∃ gamma claim, RoundsMeans eR rR (maddE sum eps row.target) gamma claim ∧
    out = foldOutput d2.st F row m eps gamma claim ∧ S' = d2.st

theorem fold_iff (S : Statement) (F : FoldShape) (row : GroupRow) (m : Nat) (es : List Fmt.Entry)
    (rs : List Fmt.RoundView) (out : SingleRows) (S' : Statement) :
    fold S F row m es rs = .ok (out, S') ↔ FoldMeans S F row m es rs out S' := by
  unfold fold FoldMeans
  rw [map_ok_iff]
  constructor
  · rintro ⟨y, hD, e⟩
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    unfold foldD at hD
    split at hD
    · rename_i eE eR rE rR
      obtain ⟨k1, hD⟩ := (need_then_iff _ _ _ _).1 hD
      obtain ⟨k2, hD⟩ := (need_then_iff _ _ _ _).1 hD
      obtain ⟨k3, hD⟩ := (need_then_iff _ _ _ _).1 hD
      obtain ⟨p, kp, hD⟩ := ok_bind hD
      simp only [pure, Except.pure, Except.ok.injEq] at kp
      subst kp
      obtain ⟨k4, hD⟩ := (need_then_iff _ _ _ _).1 hD
      obtain ⟨k5, hD⟩ := (named_then_iff _ _ _).1 hD
      obtain ⟨d2, k6, hD⟩ := (got_then_iff _ _ _ _).1 hD
      obtain ⟨z, k7, hD⟩ := ok_bind hD
      split at hD
      · rename_i sum eps
        obtain ⟨k8, hD⟩ := (need_then_iff _ _ _ _).1 hD
        obtain ⟨⟨gamma, claim⟩, k9, hD⟩ := ok_bind hD
        simp only [pure, Except.pure, Except.ok.injEq] at hD
        subst hD
        simp only [Bool.and_eq_true, beq_iff_eq] at k1
        rw [List.all_eq_true] at k2
        exact ⟨eE, eR, rE, rR, rfl, rfl, k1, fun e he => beq_iff_eq.1 (k2 e he), k3, k4, k5, d2, k6,
          sum, eps, (heard_iff _ _ _ _ _ _ _).1 k7, k8, gamma, claim,
          (rounds_iff _ _ _ _ _).1 k9, rfl, rfl⟩
      · cases hD
    · cases hD
  · rintro ⟨eE, eR, rE, rR, rfl, rfl, k1, k2, k3, k4, k5, d2, k6, sum, eps, k7, k8, gamma, claim,
      k9, rfl, rfl⟩
    refine ⟨(foldOutput d2.st F row m eps gamma claim, d2), ?_, rfl⟩
    unfold foldD
    refine (need_then_iff _ _ _ _).2 ⟨by simp only [Bool.and_eq_true, beq_iff_eq]; exact k1, ?_⟩
    refine (need_then_iff _ _ _ _).2
      ⟨List.all_eq_true.2 fun e he => beq_iff_eq.2 (k2 e he), ?_⟩
    refine (need_then_iff _ _ _ _).2 ⟨k3, ?_⟩
    refine (ok_bind_iff _ _ _).2 ⟨(m, onSt S), rfl, ?_⟩
    refine (need_then_iff _ _ _ _).2 ⟨k4, ?_⟩
    refine (named_then_iff _ _ _).2 ⟨k5, ?_⟩
    refine (got_then_iff _ _ _ _).2 ⟨d2, k6, ?_⟩
    refine (ok_bind_iff _ _ _).2 ⟨([sum], eps), (heard_iff _ _ _ _ _ _ _).2 k7, ?_⟩
    refine (need_then_iff _ _ _ _).2 ⟨k8, ?_⟩
    exact (ok_bind_iff _ _ _).2 ⟨(gamma, claim), (rounds_iff _ _ _ _ _).2 k9, rfl⟩

/-! ## 4 The closing of a link, and the frame's -/

/-- **What a yes of the closing gives.** -/
def ClosingMeans (P : Plan) (S : Statement) (g : Nat) (mask : Option Nat) (rs : List Fmt.RoundView)
    (out : SingleRows) (S' : Statement) : Prop :=
  -- K10.stretch
  ∃ eB es rB rs', P.entries = eB :: es ∧ rs = rB :: rs' ∧
  -- K10.mask
  ∃ m, mask = some m ∧
  ∃ row L S1, BatMeans S g eB rB row L S1 ∧
  -- K10.kh
  (L.k = P.k ∧ L.h = P.h) ∧
  FoldMeans S1 (ioppFoldShape { code := P.code, maskCode := P.maskCode, k := P.k, h := P.h } L) row
    m es rs' out S'

theorem closing_iff (P : Plan) (S : Statement) (g : Nat) (mask : Option Nat) (rs : List Fmt.RoundView)
    (out : SingleRows) (S' : Statement) :
    closing P S g mask rs = .ok (out, S') ↔ ClosingMeans P S g mask rs out S' := by
  unfold closing ClosingMeans
  constructor
  · intro h
    split at h
    · rename_i eB es rB rs' he
      obtain ⟨m, k1, h⟩ := (got_then_iff _ _ _ _).1 h
      obtain ⟨⟨row, L, S1⟩, k2, h⟩ := ok_bind h
      obtain ⟨k3, h⟩ := (need_then_iff _ _ _ _).1 h
      simp only [Bool.and_eq_true, beq_iff_eq] at k3
      exact ⟨eB, es, rB, rs', he, rfl, m, k1, row, L, S1, (bat_iff _ _ _ _ _ _ _).1 k2, k3,
        (fold_iff _ _ _ _ _ _ _ _).1 h⟩
    · cases h
  · rintro ⟨eB, es, rB, rs', he, rfl, m, rfl, row, L, S1, k2, k3, k4⟩
    rw [he]
    refine (got_then_iff _ _ _ _).2 ⟨m, rfl, ?_⟩
    refine (ok_bind_iff _ _ _).2 ⟨(row, L, S1), (bat_iff _ _ _ _ _ _ _).2 k2, ?_⟩
    refine (need_then_iff _ _ _ _).2 ⟨by simp only [Bool.and_eq_true, beq_iff_eq]; exact k3, ?_⟩
    exact (fold_iff _ _ _ _ _ _ _ _).2 k4

/-- **WHAT A YES OF THE FRAME'S CLOSING OF A LINK GIVES.** -/
def CloseMeans (owed : Option Nat) (f : ReqFrame) (S : Statement) (es : List Fmt.Entry)
    (rs : List Fmt.RoundView) (f' : ReqFrame) (S' : Statement) : Prop :=
  -- K10.owed
  owed = none ∧
  -- K10.link
  ∃ L, f.shape.link[f.link]? = some L ∧
  -- K10.group
  ∃ G, f.groups[f.link]? = some G ∧
  -- K10.due
  (f.next = .laterOrClose ∧ f.moment = reqMoments L) ∧
  ∃ rows, ClosingMeans
      { code := f.shape.code, maskCode := f.shape.maskCode, k := G.k, h := G.h, entries := es } S
      f.group f.mask rs rows S' ∧
    f' = { f with rows := rows, mask := none, link := f.link + 1, next := .first }

theorem closeFrame_iff (owed : Option Nat) (f : ReqFrame) (S : Statement) (es : List Fmt.Entry)
    (rs : List Fmt.RoundView) (f' : ReqFrame) (S' : Statement) :
    closeFrame owed f S es rs = .ok (f', S') ↔ CloseMeans owed f S es rs f' S' := by
  unfold closeFrame CloseMeans
  rw [need_then_iff, Option.isNone_iff_eq_none, got_then_iff]
  refine and_congr_right fun _ => exists_congr fun L => and_congr_right fun _ => ?_
  rw [got_then_iff]
  refine exists_congr fun G => and_congr_right fun _ => ?_
  rw [need_then_iff]
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    obtain ⟨⟨rows, S''⟩, k1, h⟩ := ok_bind h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rows, (closing_iff _ _ _ _ _ _ _).1 k1, rfl⟩
  · rintro ⟨rows, k1, rfl⟩
    exact (ok_bind_iff _ _ _).2 ⟨(rows, S'), (closing_iff _ _ _ _ _ _ _).2 k1, rfl⟩

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.ok_bind_iff
#print axioms VerifiableInference.Desc.First.Close.need_ok_iff
#print axioms VerifiableInference.Desc.First.Close.need_then_iff
#print axioms VerifiableInference.Desc.First.Close.got_ok_iff
#print axioms VerifiableInference.Desc.First.Close.got_then_iff
#print axioms VerifiableInference.Desc.First.Close.named_ok_iff
#print axioms VerifiableInference.Desc.First.Close.named_then_iff
#print axioms VerifiableInference.Desc.First.Close.map_ok_iff
#print axioms VerifiableInference.Desc.First.Close.heard_iff
#print axioms VerifiableInference.Desc.First.Close.bat_iff
#print axioms VerifiableInference.Desc.First.Close.rounds_iff
#print axioms VerifiableInference.Desc.First.Close.fold_iff
#print axioms VerifiableInference.Desc.First.Close.closing_iff
#print axioms VerifiableInference.Desc.First.Close.closeFrame_iff
