-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LooksWalk.lean: «THE LEDGER's ARRAYS HAVE THE PLAN's SHAPES» ALONG THE
FIRST CHAIN's FOLD: THE FRAME OF THE WALK FROM WHERE A LINK's LEDGER IS LAID TO ITS BATCHING, AND
THREE KINDS' SHARES. Definitions and theorems. It changes no other file.

Why. `totalIn_along` (Johnson/Desc/First/Link/Law/TotalAlong.lean) takes the looks at the state in
front of the batching. They are laid with the ledger, off the plan (`looks_start`,
Johnson/Desc/First/Link/Law/LooksAre.lean); every sub-protocol between must hand them on.
  `LooksInv shOf s`: where the state holds an open ledger and an open link, of the number m, the
    ledger has the looks `shOf m`. shOf: A TERM OFF THE PLAN: link by link. IT HOLDS IDLY WHERE NO
    LEDGER IS OPEN: between two links the ledger is dropped and laid anew.
  `KeepsLooks shOf s s'`: it passes from s to s'. `keeps_refl`, `keeps_trans`.
  `keeps_of_cases`: THE TOOL: the ledger behind has its link's looks outright (a maker), or there
    was a ledger in front, in a link of the same number, with the same looks (a keeper).
    `keeps_same`: the two readings are left. `keeps_none`: no ledger is open behind.
    `keeps_puts`: a writing of a link's context of the same number and of a ledger with the same
    looks.
  `steps_under`: a sub-protocol that says yes only where another says the same yes steps as it does
    (`Block.Under`, `Block.Steps`).
  `looks_reach`: **THE INDUCTION**: the start has it; every sub-protocol of the list steps in
    `KeepsLooks shOf`: THEN EVERY REACHED STATE HAS IT (`Reach`, Johnson/Top/H0/Walk/Reach.lean).
    `looks_reach_from`: THE SAME FROM A BORDER i TO A BORDER n: the sub-protocols of the numbers
    from i on below n alone are asked, where at border i no ledger is open (`looksInv_none`).
    `hasFork_reach`, `hasFork_reach_from`: so, where a ledger and link number m are open:
    `HasFork (LooksAre (shOf m))`.
  THREE KINDS' SHARES, PAID HERE, AT THE KINDS' OWN TEXTS:
    `k8_steps`: the approximate range proof's draw (K8: `K8.approximateRangeProofDrawKind K8.atS p`) leaves both readings.
    `k1_steps`: a segment's later sending (K1: `K1.commitAtS`): it marks arrays as committed and
      turns, of the link's context, the state of the calls and the count of moments
      (`rootTaken_looks` … `commitAtS_looks`: Johnson/Desc/K1/KeepsShapes.lean lemma for lemma, with
      the looks and the link's number in the place of (R, K)).
    `quiet_steps`: a sub-protocol without a round whose function leaves both readings.
Limits. THE OTHER KINDS' SHARES ARE NOT SHOWN IN THIS FILE: `looks_reach`'s second premise is owed
at: the link's opening with the step that lays the ledger (a maker) · the two lookups (K3) · the
callers' own rounds (K4 | K5 | K6) · the reply (K7) · the merge (K11) · the batching, the
sub-protocol behind it and the closing (K9 | K10: LooksAre.lean has the first two and the shutting
in the form `HasFork … → HasFork …`, under the runs' share) · the frame's own steps · what stands
behind the last link. SHOWN BESIDE THIS FILE, IN THAT PREMISE's FORM (`….Steps (KeepsLooks shOf)`),
AT THE KINDS' OWN TEXTS: K3: `k3_steps_calls`, `k3_steps_digits` (LooksK3.lean) · K4: `k4_steps`
(LooksK4.lean) · K5: `k5_steps`, at the seat seatSO (LooksK5.lean) · K6: `k6_steps`, at `blockAt` of
Johnson/Stored/HeadSeatAt.lean (LooksK6.lean) (K4 | K5 | K6: the decision alone: nothing on their
runs of claims) · K7: `k7_steps`, under hL: the seat's laying of the reply leaves the two readings ·
K11: `k11_steps` (both LooksFrame.lean). NONE OF THESE SAYS WHICH SUB-PROTOCOL OF A LIST bs IS SUCH
A TEXT: so none pays the premise at a list. THE INVARIANT ITSELF, by another induction, on the
decisions: `looks_at_reached` (Johnson/LPFK9R/LooksSeat.lean): where `ProofFile.pureRoad.pub` and
`ProofFile.onlineDescription` return, c the chain of which the returned value is made:
`LooksInv (shOfBuilt Z.p.built.links)` at every state reached at a border k ≤ (frontOf c).length:
NOT behind the last link.
Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.LooksAre
import Johnson.Desc.K1.KeepsShapes
import Johnson.Desc.First.K8.LawFunsStay
import Johnson.Desc.Sound.FoldSteps
import Johnson.Desc.Sound.HearsOnce
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (step_ok_iff)
open Johnson.Desc.First.Walk.Tied (Reach StepYes)

/-! ## 1 The frame -/

section
variable (shOf : ℕ → List Look)

/-- **Where a ledger and a link are open, the ledger has that link's looks.** -/
def LooksInv (s : S) : Prop :=
  ∀ G L, s.fork? = some G → s.link? = some L → LooksAre (shOf L.link) G

/-- It passes from s to s'. -/
def KeepsLooks (s s' : S) : Prop := LooksInv shOf s → LooksInv shOf s'

theorem keeps_refl (s : S) : KeepsLooks shOf s s := id

theorem keeps_trans (a b c : S) (h : KeepsLooks shOf a b) (k : KeepsLooks shOf b c) :
    KeepsLooks shOf a c := fun x => k (h x)

/-- **The tool**: a maker, or a keeper. -/
theorem keeps_of_cases {s s' : S}
    (h : ∀ G' L', s'.fork? = some G' → s'.link? = some L' → LooksAre (shOf L'.link) G' ∨
      ∃ G L, s.fork? = some G ∧ s.link? = some L ∧ L.link = L'.link ∧
        G'.trees.map look = G.trees.map look) : KeepsLooks shOf s s' := by
  intro hs G' L' hG hL
  rcases h G' L' hG hL with h1 | ⟨G, L, e1, e2, e3, e4⟩
  · exact h1
  · rw [← e3]
    exact looks_map e4 (hs G L e1 e2)

/-- The two readings are left. -/
theorem keeps_same {s s' : S} (hf : s'.fork? = s.fork?)
    (hl : s'.link?.map (·.link) = s.link?.map (·.link)) : KeepsLooks shOf s s' := by
  refine keeps_of_cases shOf fun G' L' hG hL => Or.inr ?_
  rw [hL] at hl
  cases e : s.link? with
  | none =>
    rw [e] at hl
    exact nomatch hl
  | some L =>
    rw [e] at hl
    exact ⟨G', L, hf ▸ hG, rfl, (Option.some.inj hl).symm, rfl⟩

/-- No ledger is open behind. -/
theorem keeps_none {s s' : S} (hf : s'.fork? = none) : KeepsLooks shOf s s' := by
  intro _ G' L' hG _
  rw [hf] at hG
  exact nomatch hG

end

/-- What is read behind a writing of the link's context and of the ledger. -/
theorem reads_puts (s : S) (L0 : LinkCtx) (F0 : Fork) (hL : s.link? = some L0)
    (hF : s.fork? = some F0) (L : LinkCtx) (F : Fork) :
    ((s.putLink L).putFork F).link? = some L ∧ ((s.putLink L).putFork F).fork? = some F := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | lay x => exact ⟨rfl, rfl⟩
  | att x => exact ⟨rfl, rfl⟩
  | head x =>
    by_cases ho : x.opened = true
    · constructor <;> simp [S.putLink, S.putFork, S.link?, S.fork?, ho]
    · simp [S.link?, ho] at hL
  | _ => exact nomatch hL

/-- A writing of a context of the same number and of a ledger with the same looks. u: any state
with s's two readings (what a kind lays back beside them). -/
theorem keeps_puts (shOf : ℕ → List Look) {s u : S} {L0 L : LinkCtx} {F0 F : Fork}
    (hL : s.link? = some L0) (hF : s.fork? = some F0) (uL : u.link? = some L0)
    (uF : u.fork? = some F0) (el : L.link = L0.link)
    (ef : F.trees.map look = F0.trees.map look) :
    KeepsLooks shOf s ((u.putLink L).putFork F) := by
  obtain ⟨r1, r2⟩ := reads_puts u L0 F0 uL uF L F
  refine keeps_of_cases shOf fun G' L' hG hL' => Or.inr ⟨F0, L0, hF, hL, ?_, ?_⟩
  · rw [← Option.some.inj (r1.symm.trans hL'), el]
  · rw [← Option.some.inj (r2.symm.trans hG), ef]

/-- A sub-protocol that says yes only where another says the same yes steps as it does. -/
theorem steps_under {Cl Cl' : Type} {R : S → S → Prop} {b' : Block S Cl'} {b : Block S Cl}
    (u : b'.Under b) (h : b.Steps R) : b'.Steps R :=
  fun s rs gs s' e => h s rs gs s' (u s rs gs s' e)

/-- **THE INDUCTION ALONG "REACHED".** -/
theorem looks_reach {Cl P : Type} (shOf : ℕ → List Look) (ft : ℕ) (bs : List (Block S Cl))
    (start : P → S) (h0 : ∀ z, LooksInv shOf (start z))
    (hs : ∀ b ∈ bs, b.Steps (KeepsLooks shOf)) {k : ℕ} {a : P × S}
    (h : Reach ft bs start k a) : LooksInv shOf a.2 := by
  induction h with
  | zero z => exact h0 z
  | @succ k z s s' b _ hb hy ih =>
    obtain ⟨R, c, _, e⟩ := hy
    exact hs b (List.mem_of_getElem? hb) _ _ _ _
      ((step_ok_iff ft b s s' R c c.length).1 e).2.2.2 ih

/-- **THE SAME FROM A BORDER i TO A BORDER n**: it holds at every state that is reached at border i
(a link's first: no ledger is open there), and the sub-protocols of the numbers from i on BELOW n
step: so, at i a link's first border and n the border in front of its batching, only that stretch
is asked.
-/
theorem looks_reach_from {Cl P : Type} (shOf : ℕ → List Look) (ft : ℕ) (bs : List (Block S Cl))
    (start : P → S) (i n : ℕ) (hi : ∀ a, Reach ft bs start i a → LooksInv shOf a.2)
    (hs : ∀ j b, i ≤ j → j < n → bs[j]? = some b → b.Steps (KeepsLooks shOf)) {k : ℕ}
    {a : P × S} (h : Reach ft bs start k a) (hik : i ≤ k) (hkn : k ≤ n) :
    LooksInv shOf a.2 := by
  induction h with
  | zero z =>
    obtain rfl : i = 0 := Nat.le_zero.1 hik
    exact hi _ (.zero z)
  | @succ k z s s' b hr hb hy ih =>
    by_cases hk : i ≤ k
    · obtain ⟨R, c, _, e⟩ := hy
      exact hs k b hk hkn hb _ _ _ _ ((step_ok_iff ft b s s' R c c.length).1 e).2.2.2
        (ih hk (Nat.le_of_lt hkn))
    · obtain rfl : i = k + 1 := by omega
      exact hi _ (.succ hr hb hy)

/-- Where no ledger is open the property holds idly. -/
theorem looksInv_none (shOf : ℕ → List Look) {s : S} (h : s.fork? = none) : LooksInv shOf s := by
  intro G _ hG _
  rw [h] at hG
  exact nomatch hG

/-- **So, where a ledger and link number m are open.** -/
theorem hasFork_reach {Cl P : Type} (shOf : ℕ → List Look) (ft : ℕ) (bs : List (Block S Cl))
    (start : P → S) (h0 : ∀ z, LooksInv shOf (start z))
    (hs : ∀ b ∈ bs, b.Steps (KeepsLooks shOf)) {k : ℕ} {a : P × S}
    (h : Reach ft bs start k a) (G : Fork) (L : LinkCtx) (hG : a.2.fork? = some G)
    (hL : a.2.link? = some L) : HasFork (LooksAre (shOf L.link)) a.2 :=
  ⟨G, hG, looks_reach shOf ft bs start h0 hs h G L hG hL⟩

/-- The like from a border i to a border n. -/
theorem hasFork_reach_from {Cl P : Type} (shOf : ℕ → List Look) (ft : ℕ) (bs : List (Block S Cl))
    (start : P → S) (i n : ℕ) (hi : ∀ a, Reach ft bs start i a → a.2.fork? = none)
    (hs : ∀ j b, i ≤ j → j < n → bs[j]? = some b → b.Steps (KeepsLooks shOf)) {k : ℕ}
    {a : P × S} (h : Reach ft bs start k a) (hik : i ≤ k) (hkn : k ≤ n) (G : Fork) (L : LinkCtx)
    (hG : a.2.fork? = some G) (hL : a.2.link? = some L) : HasFork (LooksAre (shOf L.link)) a.2 :=
  ⟨G, hG, looks_reach_from shOf ft bs start i n (fun x hx => looksInv_none shOf (hi x hx)) hs h
    hik hkn G L hG hL⟩

/-! ## 2 Three kinds' shares -/

/-- A sub-protocol without a round whose function leaves both readings. -/
theorem quiet_steps {Cl : Type} (shOf : ℕ → List Look) (n : String) (chain : ℕ) (link : Option ℕ)
    (piece : ℕ) (f : S → Except String S)
    (hf : ∀ s s', f s = .ok s' → s'.fork? = s.fork? ∧
      s'.link?.map (·.link) = s.link?.map (·.link)) :
    (roundlessBlock (Cl := Cl) n chain link piece f).Steps (KeepsLooks shOf) :=
  fun s _ _ s' h => keeps_same shOf (hf s s' h).1 (hf s s' h).2

/-- **K8: the approximate range proof's draw.** -/
theorem k8_steps {Cl : Type} (shOf : ℕ → List Look) (p : First.K8.Par) :
    (First.K8.approximateRangeProofDrawKind (Cl := Cl) First.K8.atS p).Steps (KeepsLooks shOf) := by
  intro s rs gs s' h
  obtain ⟨r, rfl⟩ := First.K8.decide_one First.K8.atS p s s' rs gs h
  obtain ⟨tl, _, hm⟩ := (First.K8.decide_atS_iff p s s' r gs).1 h
  rw [hm.2.2.2.2.2.2.2.2]
  exact keeps_same shOf (First.K8.putTl_fork _ _) (by rw [First.K8.putTl_link])

theorem rootTaken_looks (F : Fork) (t w : ℕ) :
    (F.rootTaken t w).trees.map look = F.trees.map look :=
  map_modify_same look (fun X => { X with root := some w }) (fun _ => rfl) F.trees t

theorem commitOne_looks {L : LinkCtx} {F F' : Fork} {t : ℕ} (h : L3.commitOne L F t = .ok F') :
    F'.trees.map look = F.trees.map look := by
  simp only [L3.commitOne] at h
  split at h <;> split at h <;> first
    | (injection h with h; subst h; exact rootTaken_looks _ _ _)
    | cases h

theorem commitAll_looks {L : LinkCtx} : ∀ (ts : List ℕ) (F F' : Fork),
    ts.foldlM (L3.commitOne L) F = .ok F' → F'.trees.map look = F.trees.map look
  | [], F, F', h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact rfl
  | t :: ts, F, F', h => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    cases h1 : L3.commitOne L F t with
    | error e => simp [h1] at h
    | ok F₁ =>
      simp only [h1] at h
      exact (commitAll_looks ts F₁ F' h).trans (commitOne_looks h1)

theorem commitBehind_looks {L L' : LinkCtx} {check : ChainCheck} {F F' : Fork} {ts : List ℕ}
    (h : L3.commitBehind L check F ts = .ok (L', F')) :
    L'.link = L.link ∧ F'.trees.map look = F.trees.map look := by
  simp only [L3.commitBehind, bind, Except.bind] at h
  cases h1 : ts.foldlM (L3.commitOne L) F with
  | error e => simp [h1] at h
  | ok F₁ =>
    simp only [h1] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1, ← h.2]
      exact ⟨rfl, commitAll_looks ts F F₁ h1⟩
    · cases h

theorem commitStep_looks {W : Type} {send : L3.Send W} {ts : List ℕ} {s s' : L3.St W}
    {rs : List Fmt.RoundView} (h : L3.commitStep send ts s rs = .ok s') :
    s'.L.link = s.L.link ∧ s'.F.trees.map look = s.F.trees.map look := by
  simp only [L3.commitStep, bind, Except.bind] at h
  cases h0 : L3.commitFront s.L with
  | error e => simp [h0] at h
  | ok u =>
    simp only [h0] at h
    cases h1 : send s.L.check s.w rs with
    | error e => simp [h1] at h
    | ok x =>
      simp only [h1] at h
      cases h2 : L3.commitBehind s.L x.1 s.F ts with
      | error e => simp [h2] at h
      | ok y =>
        simp only [h2, pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact commitBehind_looks (L' := y.1) (F' := y.2) h2

theorem commitOwn_looks {Cl : Type} {P : K1.Par} {link moment : ℕ} {arrays : Option (List ℕ)}
    {x y : K1.Owing (L3.St (_root_.Desc.Plain.DState Unit))} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h : (K1.commitOwn (Cl := Cl) P link moment arrays).decide x rs gs = .ok y) :
    y.held.L.link = x.held.L.link ∧ y.held.F.trees.map look = x.held.F.trees.map look := by
  simp only [K1.commitOwn] at h
  split at h
  · split at h
    · cases h
    · rename_i ts
      cases h1 : L3.commitStep (K1.laterOwn P x.owed) ts x.held rs with
      | error e => simp [h1, Except.map] at h
      | ok z =>
        simp only [h1, Except.map, Except.ok.injEq] at h
        subst h
        exact commitStep_looks h1
  · cases h

/-- **K1: a segment's later sending.** -/
theorem k1_steps {Cl : Type} (shOf : ℕ → List Look) (P : K1.Par) (link moment : ℕ)
    (arrays : Option (List ℕ)) :
    (K1.commitAtS (Cl := Cl) P link moment arrays).Steps (KeepsLooks shOf) := by
  intro s rs gs s' h
  simp only [K1.commitAtS] at h
  split at h
  · rename_i L F tl hL hF ht
    cases h1 : (K1.commitOwn (Cl := Cl) P link moment arrays).decide
        { owed := K1.owedOf s, held := { L := L, F := F, tl := tl, w := K1.stateOf s () } } rs
        gs with
    | error e => simp [h1, Except.map] at h
    | ok y =>
      simp only [h1, Except.map, Except.ok.injEq] at h
      obtain ⟨e1, e2⟩ := commitOwn_looks h1
      rw [← h]
      exact keeps_puts shOf hL hF (u := K1.laid s y.held.w) hL hF e1 e2
  · cases h

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.keeps_of_cases
#print axioms VerifiableInference.Desc.LinkJoin.keeps_same
#print axioms VerifiableInference.Desc.LinkJoin.keeps_puts
#print axioms VerifiableInference.Desc.LinkJoin.steps_under
#print axioms VerifiableInference.Desc.LinkJoin.looks_reach
#print axioms VerifiableInference.Desc.LinkJoin.looks_reach_from
#print axioms VerifiableInference.Desc.LinkJoin.hasFork_reach
#print axioms VerifiableInference.Desc.LinkJoin.hasFork_reach_from
#print axioms VerifiableInference.Desc.LinkJoin.quiet_steps
#print axioms VerifiableInference.Desc.LinkJoin.k8_steps
#print axioms VerifiableInference.Desc.LinkJoin.commitOwn_looks
#print axioms VerifiableInference.Desc.LinkJoin.k1_steps
