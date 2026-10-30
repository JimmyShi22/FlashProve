-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/Moves.lean
(kind K9's soundness lemma): THEOREMS: THE BATCHING AS A DRAW WITH MOVES BEHIND IT:
the form of a description in which the claims are added in several steps, so that a later run of
claims is called at a record into which earlier claims are added already.
A MOVE is one of two things:
  add g     g, a function of claims, is called; its claims are added to the ledger of the state that
            it returns (K9.adds, Batch/Kind.lean);
  quiet h   h is called; no claim.
  MoveYes, MovesYes   what a yes of a move, of a row of moves, is: as relations between the state in
            front, the state behind and the claims added.
  Termed    a move with ITS TERMS: tm n p y: the polynomial in chi that its claims sum to, if n
            claims were added before, at the fixed part p and the prover's data y; len: their
            number.
  Fx        A LETTER: Fx q e: "the state e goes on from the fixed part q". q IS THE FIXED PART OF
            THE STATE IN FRONT OF THE DRAW (O.fixed s) AND STAYS ONE VALUE ALONG THE WHOLE ROW: a
            move need not keep a reader's value; it must keep "goes on from q". (So a run may fill
            a free slot behind the draw: Law/FitsAtS.lean.)
  AddOk     THE PREMISE ON A FUNCTION OF CLAIMS, at EVERY fixed part q and EVERY state that goes on
            from q and is good in the other kinds' eyes, whatever its ledger's sums are: it leaves
            the ledger's core alone (the sums, chi, the count of claims, the plan's number:
            Law/Stages.lean: core); it keeps "good" and "goes on from q", and is "more"; it makes
            len q claims; and, WHERE ITS CLAIMS CAN BE ADDED AT ALL (to any ledger
            with the same core and the same frame of the arrays: the step that spends the premise
            has that yes: it adds what it has gathered, or refuses), the sum of its claims with
            their weights, numbered from THE LEDGER's COUNT on, read at any full later state, is
            the polynomial tm. THE TERMS SEE THE COUNT, THE FIXED PART q AND THE DATA y ALONE; q is
            read in front of the draw, and y is a letter of the law that is bound to the witness's
            tables in front of the draw too (Law/RowMoves.lean: the data that the tables hold;
            hpin): so the terms see neither chi nor the ledger's sums. (That a function whose FORMS
            hang on the sums cannot meet AddOk is NOT claimed: the equation is asked at full later
            states alone; at a hollow "full" it asks nothing. What then bears the weight is hend,
            and the test on the exponents in Law/RowMoves.lean.)
  QuietOk   the like of a quiet move.
  FitsM     the hypotheses on the lens and on the other kinds' letters at the draw and at the
            adding.
  Adv, adv_trans, move_adv, moves_adv   the invariant along a row of moves.
  DrawMoves the hypothesis on a block: a yes of its step is the draw's yes and then a yes of the
            row of moves.
  valueF_moves   **ValueF (Law/LawF.lean) at such a block**, at the meaning semOf, under hend:
            behind the last move the state meets "behind" and is full.
Not claimed: that any description's block meets DrawMoves (Law/MovesBlock.lean), nor that any real
run of claims meets AddOk.

-/
import Johnson.Desc.First.Batch.Law.LawF
import Johnson.Desc.First.Batch.Law.BatchAdds
import Johnson.Desc.First.Batch.Law.Stages

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Lens Where drawnClean ledgerEmpty)

variable {T P K : Type}

/-- A move behind the draw. -/
inductive Move (T : Type) where
  | add (g : T → Except String (List Claim × T))
  | quiet (h : T → Except String T)

/-- A yes of a move: from t to t', the claims cls added. -/
def MoveYes (X : Lens T) : Move T → T → T → List Claim → Prop
  | .add g, t, t', cls => ∃ e s G, g t = .ok (cls, e) ∧ X.get? e = some s ∧
      addAll s.F cls = some G ∧ t' = X.set e { s with F := G }
  | .quiet h, t, t', cls => h t = .ok t' ∧ cls = []

/-- A yes of a row of moves. -/
def MovesYes (X : Lens T) : List (Move T) → T → T → List Claim → Prop
  | [], t, t', cls => t' = t ∧ cls = []
  | m :: l, t, t', cls => ∃ u c c', MoveYes X m t u c ∧ MovesYes X l u t' c' ∧ cls = c ++ c'

/-- A move with its terms. -/
structure Termed (T P K : Type) where
  move : Move T
  tm : ℕ → P → Bound K → List (ℕ × K)
  len : P → ℕ

/-- The terms of a row of moves, if n claims were added before. -/
def termsOf (p : P) (y : Bound K) : List (Termed T P K) → ℕ → List (ℕ × K)
  | [], _ => []
  | m :: l, n => m.tm n p y ++ termsOf p y l (n + m.len p)

/-- Where a list of claims can be added, so can each of its fronts. -/
theorem addAll_front (F G : Fork) (a b : List Claim) (h : addAll F (a ++ b) = some G) :
    ∃ X, addAll F a = some X ∧ addAll X b = some G := by
  unfold addAll at h ⊢
  rw [List.foldlM_append] at h
  exact Option.bind_eq_some_iff.1 h

/-- The batching element in a state's ledger; nothing where no segment is open. -/
def thetaOf (X : Lens T) (t : T) : Option E := (X.get? t).map (·.F.theta)

/-- "Later": as semOf has it, AND THE BATCHING ELEMENT IS THE SAME (a run whose equation leans on a
test at the later ledger needs it: that test reads the later ledger's own element). -/
def laterK (X : Lens T) (O : Others T P K) (s t : T) : Prop :=
  planOf X s = planOf X t ∧ O.more s t ∧ thetaOf X s = thetaOf X t

section
variable [Field K] (ρ : Reading K) (X : Lens T) (O : Others T P K) (Fx : P → T → Prop)

/-- The premise on a function of claims. -/
def AddOk (g : T → Except String (List Claim × T)) (tm : ℕ → P → Bound K → List (ℕ × K))
    (len : P → ℕ) : Prop :=
  ∀ q e a c e₁, Fx q e → O.good e → X.get? e = some a → a.F.LS.size = a.F.ns →
    g e = .ok (c, e₁) →
    ∃ a₁, X.get? e₁ = some a₁ ∧ core a₁.F = core a.F ∧ O.good e₁ ∧ O.more e e₁ ∧
      Fx q e₁ ∧ c.length = len q ∧
      ∀ A₀ G, core A₀ = core a₁.F → treesFrame A₀.trees = treesFrame a₁.F.trees →
        addAll A₀ c = some G →
      ∀ t y, laterK X O e₁ t → O.full t →
        wsumK X ρ t y (ρ.val a.F.theta) a.F.nClaim c =
          termsAt K (tm a.F.nClaim q y) (ρ.val a.F.theta)

/-- The premise on a quiet move. -/
def QuietOk (h : T → Except String T) : Prop :=
  ∀ q e a e₁, Fx q e → O.good e → X.get? e = some a → a.F.LS.size = a.F.ns → h e = .ok e₁ →
    ∃ a₁, X.get? e₁ = some a₁ ∧ core a₁.F = core a.F ∧ O.good e₁ ∧ O.more e e₁ ∧ Fx q e₁

/-- The premise on a move with its terms. -/
def MoveOk (m : Termed T P K) : Prop :=
  match m.move with
  | .add g => AddOk ρ X O Fx g m.tm m.len
  | .quiet h => QuietOk X O Fx h ∧ (∀ n p y, m.tm n p y = []) ∧ ∀ p, m.len p = 0

/-- The hypotheses on the lens and on the other kinds' letters. -/
structure FitsM (p : Where) : Prop where
  lens : ∀ s a, (X.get? s).isSome = true → ∃ a', X.get? (X.set s a) = some a' ∧ a'.F = a.F
  moreRefl : ∀ s, O.more s s
  moreTrans : ∀ s t u, O.more s t → O.more t u → O.more s u
  atDraw : ∀ s a o x, O.ready s → X.get? s = some a →
    drawnClean p.rows (E.ofTriple x) a.owed a.used a.L a.F = .ok o →
    Fx (O.fixed s) (X.set s { a with owed := o.owed, L := o.L, F := o.F }) ∧
      O.good (X.set s { a with owed := o.owed, L := o.L, F := o.F })
  atAdd : ∀ q e b G c, Fx q e → O.good e → X.get? e = some b → addAll b.F c = some G →
    O.good (X.set e { b with F := G }) ∧ O.more e (X.set e { b with F := G }) ∧
      Fx q (X.set e { b with F := G })

/-- **The invariant**: from the state e with the part a to the state e' with the part b, the claims
c added; ts: their terms. -/
structure Adv (q : P) (e e' : T) (a b : K9.Part) (c : List Claim)
    (ts : Bound K → List (ℕ × K)) : Prop where
  part : X.get? e' = some b
  theta : b.F.theta = a.F.theta
  plan : b.F.planClaimsF = a.F.planClaimsF
  count : b.F.nClaim = a.F.nClaim + c.length
  sized : b.F.LS.size = b.F.ns
  total : ∀ W : World K, b.F.total ρ W = a.F.total ρ W +
    claimsSum ρ W (ρ.val a.F.theta) a.F.planClaimsF a.F.nClaim c
  good : O.good e'
  more : O.more e e'
  fixed : Fx q e'
  sum : ∀ t y, laterK X O e' t → O.full t →
    wsumK X ρ t y (ρ.val a.F.theta) a.F.nClaim c = termsAt K (ts y) (ρ.val a.F.theta)

theorem wsumK_append (t : T) (y : Bound K) (x : K) : ∀ (a b : List Claim) (n : ℕ),
    wsumK X ρ t y x n (a ++ b) = wsumK X ρ t y x n a + wsumK X ρ t y x (n + a.length) b
  | [], b, n => by simp [wsumK]
  | cl :: a, b, n => by
    simp only [List.cons_append, wsumK, wsumK_append t y x a b (n + 1), List.length_cons]
    rw [show n + 1 + a.length = n + (a.length + 1) by omega, add_assoc]

theorem core_parts {F G : Fork} (h : core G = core F) :
    sums G = sums F ∧ G.theta = F.theta ∧ G.nClaim = F.nClaim ∧
      G.planClaimsF = F.planClaimsF ∧ G.LS = F.LS ∧ G.ns = F.ns := by
  have h1 : sums G = sums F := congrArg Prod.fst h
  have h2 := h1
  simp only [sums, Prod.mk.injEq] at h2
  exact ⟨h1, congrArg (fun x => x.2.1) h, congrArg (fun x => x.2.2.1) h,
    congrArg (fun x => x.2.2.2) h, h2.2.1, h2.2.2.2⟩

end

section
variable [Field K] (ρ : Reading K) (X : Lens T) (O : Others T P K) (Fx : P → T → Prop)

theorem adv_refl (p : Where) (H : FitsM X O Fx p) (q : P) (e : T) (a : K9.Part)
    (ha : X.get? e = some a) (hs : a.F.LS.size = a.F.ns) (hg : O.good e) (hf : Fx q e) :
    Adv ρ X O Fx q e e a a [] fun _ => [] where
  part := ha
  theta := rfl
  plan := rfl
  count := rfl
  sized := hs
  total := fun W => by simp [claimsSum, sumFrom]
  good := hg
  more := H.moreRefl e
  fixed := hf
  sum := fun t y _ _ => by simp [wsumK, termsAt]

/-- Two stretches in a row. -/
theorem adv_trans (p : Where) (H : FitsM X O Fx p) {q : P} {e e₁ e₂ : T} {a b b₂ : K9.Part}
    {c c' : List Claim} {ts ts' : Bound K → List (ℕ × K)} (h1 : Adv ρ X O Fx q e e₁ a b c ts)
    (h2 : Adv ρ X O Fx q e₁ e₂ b b₂ c' ts') :
    Adv ρ X O Fx q e e₂ a b₂ (c ++ c') fun y => ts y ++ ts' y where
  part := h2.part
  theta := h2.theta.trans h1.theta
  plan := h2.plan.trans h1.plan
  count := by rw [h2.count, h1.count, List.length_append, Nat.add_assoc]
  sized := h2.sized
  total := fun W => by
    rw [h2.total W, h1.total W, claimsSum_append, h1.theta, h1.plan, h1.count, add_assoc]
  good := h2.good
  more := H.moreTrans _ _ _ h1.more h2.more
  fixed := h2.fixed
  sum := fun t y ht hf => by
    have hl : laterK X O e₁ t := by
      refine ⟨?_, H.moreTrans _ _ _ h2.more ht.2.1, ?_⟩
      · rw [← ht.1]
        simp only [planOf, h1.part, h2.part, Option.map_some, h2.plan]
      · rw [← ht.2.2]
        simp only [thetaOf, h1.part, h2.part, Option.map_some, h2.theta]
    have s2 := h2.sum t y ht hf
    rw [h1.theta, h1.count] at s2
    rw [wsumK_append, h1.sum t y hl hf, s2, termsAt_append]

/-- One move. -/
theorem move_adv (p : Where) (H : FitsM X O Fx p) (m : Termed T P K) (hm : MoveOk ρ X O Fx m)
    (q : P) (e e' : T) (a : K9.Part) (c : List Claim) (hf : Fx q e) (hg : O.good e)
    (ha : X.get? e = some a) (hs : a.F.LS.size = a.F.ns) (hy : MoveYes X m.move e e' c) :
    c.length = m.len q ∧ ∃ b, Adv ρ X O Fx q e e' a b c fun y => m.tm a.F.nClaim q y := by
  unfold MoveOk at hm
  cases hmv : m.move with
  | add g =>
    rw [hmv] at hm hy
    obtain ⟨e₁, s, G, hge, hse, hG, rfl⟩ := hy
    obtain ⟨a₁, ha₁, hc, g1, m1, f1, l1, sm⟩ := hm q e a c e₁ hf hg ha hs hge
    have es : a₁ = s := Option.some.inj (ha₁.symm.trans hse)
    subst es
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := core_parts hc
    have hs1 : a₁.F.LS.size = a₁.F.ns := by rw [k5, k6]; exact hs
    obtain ⟨b, hb, hF⟩ := H.lens e₁ { a₁ with F := G } (by simp [ha₁])
    have hF' : b.F = G := hF
    obtain ⟨g2, m2, f2⟩ := H.atAdd q e₁ a₁ G c f1 g1 ha₁ hG
    have hGe := (addAll_total ρ ⟨fun _ => 0, fun _ _ _ => 0⟩ c a₁.F G hs1 hG).2
    have gθ : G.theta = a₁.F.theta := by rw [hGe.1]
    have gp : G.planClaimsF = a₁.F.planClaimsF := by rw [hGe.1]
    have gn : G.nClaim = a₁.F.nClaim + c.length := by rw [hGe.1]
    refine ⟨l1, b, ⟨hb, by rw [hF', gθ, k2], by rw [hF', gp, k4], by rw [hF', gn, k3],
      by rw [hF']; exact hGe.2.1, fun W => ?_, g2, H.moreTrans _ _ _ m1 m2, f2,
      fun t y ht hf => sm a₁.F G rfl rfl hG t y ⟨?_, H.moreTrans _ _ _ m2 ht.2.1, ?_⟩ hf⟩⟩
    · rw [hF', (addAll_total ρ W c a₁.F G hs1 hG).1, total_of_sums ρ W a.F a₁.F k1, k2, k3, k4]
    · rw [← ht.1]
      simp only [planOf, ha₁, hb, Option.map_some, hF', gp]
    · rw [← ht.2.2]
      simp only [thetaOf, ha₁, hb, Option.map_some, hF', gθ]
  | quiet h =>
    rw [hmv] at hm hy
    obtain ⟨hq, ht0, hl0⟩ := hm
    obtain ⟨hh, rfl⟩ := hy
    obtain ⟨a₁, ha₁, hc, g1, m1, f1⟩ := hq q e a e' hf hg ha hs hh
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := core_parts hc
    refine ⟨by rw [hl0]; rfl, a₁, ⟨ha₁, k2, k4, by rw [k3]; rfl, by rw [k5, k6]; exact hs,
      fun W => ?_, g1, m1, f1, fun t y _ _ => ?_⟩⟩
    · rw [total_of_sums ρ W a.F a₁.F k1]
      simp [claimsSum, sumFrom]
    · rw [ht0]
      simp [wsumK, termsAt]

/-- **A row of moves.** -/
theorem moves_adv (p : Where) (H : FitsM X O Fx p) (q : P) :
    ∀ (ms : List (Termed T P K)), (∀ m ∈ ms, MoveOk ρ X O Fx m) →
      ∀ (e e' : T) (a : K9.Part) (cls : List Claim), Fx q e → O.good e → X.get? e = some a →
      a.F.LS.size = a.F.ns → MovesYes X (ms.map (·.move)) e e' cls →
      ∃ b, Adv ρ X O Fx q e e' a b cls fun y => termsOf q y ms a.F.nClaim
  | [], _, e, e', a, cls, hf, hg, ha, hs, hy => by
    obtain ⟨rfl, rfl⟩ := hy
    exact ⟨a, adv_refl ρ X O Fx p H q e' a ha hs hg hf⟩
  | m :: l, hms, e, e', a, cls, hf, hg, ha, hs, hy => by
    obtain ⟨u, c, c', h1, h2, rfl⟩ := hy
    obtain ⟨hl, b, A1⟩ :=
      move_adv ρ X O Fx p H m (hms m List.mem_cons_self) q e u a c hf hg ha hs h1
    obtain ⟨b₂, A2⟩ := moves_adv p H q l (fun r hr => hms r (List.mem_cons_of_mem _ hr)) u e' b c'
      A1.fixed A1.good A1.part A1.sized h2
    refine ⟨b₂, ?_⟩
    have A := adv_trans ρ X O Fx p H A1 A2
    rw [A1.count, hl] at A
    exact A

end

/-- **The hypothesis on a block**: a yes of its step is the draw's yes, and then a yes of the row of
moves. -/
def DrawMoves {Cl : Type} (X : Lens T) (p : Where) (ms : List (Move T)) (b : Block T Cl) : Prop :=
  ∀ ft s rs cols s' k, b.step ft s rs cols = .ok (s', k) →
    ∃ r x a o cls, rs = [r] ∧ r.drawn.elems = [x] ∧ X.get? s = some a ∧
      drawnClean p.rows (E.ofTriple x) a.owed a.used a.L a.F = .ok o ∧
      MovesYes X ms (X.set s { a with owed := o.owed, L := o.L, F := o.F }) s' cls

variable [Field K] [Fintype K] [DecidableEq K]

omit [Fintype K] [DecidableEq K] in
/-- **What the law needs of the block, at a draw with moves behind it.** hend: behind the last move
the state meets "behind" and is full (whoever lays what the claims read last owes it). -/
theorem valueF_moves {Cl : Type} (ρ : Reading K) (X : Lens T) (O : Others T P K)
    (Fx : P → T → Prop) (p : Where)
    (H : FitsM X O Fx p) (ms : List (Termed T P K)) (hms : ∀ m ∈ ms, MoveOk ρ X O Fx m)
    (b : Block T Cl) (hb : DrawMoves X p (ms.map (·.move)) b)
    (hend : ∀ s s' cls, O.good s → MovesYes X (ms.map (·.move)) s s' cls →
      O.behind s' ∧ O.full s') (ft : ℕ) :
    ValueF (semOf ρ X O) b (fun q y => termsOf q y ms 0) ft := by
  intro s rs cols s' k hr _ hs
  obtain ⟨r, x, a, o, cls, rfl, hx, ha, ho, hy⟩ := hb ft s rs cols s' k hs
  obtain ⟨d1, d2, d3, _, _, _, _, _, _, _, _, d12⟩ := drawnClean_ok _ _ _ _ _ _ _ ho
  obtain ⟨a₁, ha₁, hF⟩ := H.lens s { a with owed := o.owed, L := o.L, F := o.F } (by simp [ha])
  have hF' : a₁.F = o.F := hF
  obtain ⟨f1, g1⟩ := H.atDraw s a o x hr ha ho
  obtain ⟨b', A⟩ := moves_adv ρ X O Fx p H (O.fixed s) ms hms _ s' a₁ cls f1 g1 ha₁
    (by rw [hF']; exact d12) hy
  obtain ⟨e1, e2⟩ := hend _ _ _ g1 hy
  refine ⟨x, by simp [hx], e1, fun y => ?_⟩
  have hsum := A.sum s' y ⟨rfl, H.moreRefl s', rfl⟩ e2
  rw [hF', d2, d3] at hsum
  show oneK X ρ s' s' y = termsAt K (termsOf (O.fixed s) y ms 0) (ρ.val (E.ofTriple x))
  rw [← hsum, wsumK_eq X ρ s' b' A.part]
  simp only [oneK, A.part]
  rw [A.total, hF', total_of_empty ρ _ o.F d1, zero_add, d2, d3, A.plan, hF']

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.adv_trans
#print axioms VerifiableInference.Desc.K9L.move_adv
#print axioms VerifiableInference.Desc.K9L.moves_adv
#print axioms VerifiableInference.Desc.K9L.valueF_moves
