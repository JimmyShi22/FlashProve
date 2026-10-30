-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Along.lean: lemmas on what `play` (Honest/Frame.lean) keeps and
what it adds along a chain; on the stops and the available tables over two consecutive lists of
sub-protocols; and on the way back from a run's parts to the run. They are general in the
description, the book and the prover.

  1  `hear_mid`, `play_mid`   after a run of `play` the input is the same; the challenges that the
     stops may read are the earlier ones and the run's own; the rounds shown are the earlier ones
     and the run's; `drawsFit_length`, `exists_snoc`, `steps_shaped`, `look_shared`: four small
     lemmas
  2  `chainStopAt_append`   whether a chain stops, over two consecutive lists of sub-protocols
  3  `Env.add_nil`, `Env.add_add`, `Env.add_prefix`, `Env.Tight`, `Env.add_tight`,
     `envOf_tight`   the available tables (`Env`, Honest/Side.lean), at any start (`Env.add_nil`: at
     a start that is `Env.Tight`)
  4  `ends_back`, `run_back`   from the parts of `run_parts` (Honest/Law/Run.lean) back to the run,
     with no stored run to fall back on
  5  `seal_quiet`   if the rounds are played with no stored run to fall back on, the last round
     declares no item except roots and no oracle message, its entry counts no root, and its
     challenge is the empty one, the test on the sealing round passes

Limits.
  * Hypotheses that the prose above does not name: `ready … = .ok` (`ready` returns at these coins):
    `run_back`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Rule
import Johnson.Desc.ProofFile.Honest.Law.Cut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl Xi V W X Y W₀ Rc Ky Tr X₀ : Type}

/-! ## 1 What `play` keeps, and what it adds -/

theorem hear_mid {s : Step W X} {x : Told} {d : Fmt.Drawn} {m m' : Mid W X}
    (h : s.hear x d m = .ok m') :
    m'.st.input = m.st.input ∧ m'.loc = m.loc ++ [d] ∧ m'.seen = m.seen ++ [⟨x.vals, d⟩] := by
  unfold Step.hear at h
  cases hm : s.move with
  | none =>
    simp only [hm] at h
    cases h
    exact ⟨rfl, rfl, rfl⟩
  | some mv =>
    simp only [hm] at h
    split at h
    · cases h
    · cases h
      exact ⟨rfl, rfl, rfl⟩

theorem play_mid : ∀ (ss : List (Step W X)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (m : Mid W X) (y : List Played × Mid W X), play ss ds back m = .ok y →
    y.2.st.input = m.st.input ∧ y.2.loc = m.loc ++ ds ∧ y.2.seen = m.seen ++ roundsOf y.1
  | [], [], _, m, y, h => by
    simp only [play] at h
    cases h
    exact ⟨rfl, (List.append_nil _).symm, (List.append_nil _).symm⟩
  | [], _ :: _, _, _, _, h => by simp [play] at h
  | _ :: _, [], _, _, _, h => by simp [play] at h
  | s :: ss, d :: ds, back, m, y, h => by
    obtain ⟨x, m', z, -, hm, hz, rfl⟩ := play_cons_ok h
    obtain ⟨a1, a2, a3⟩ := hear_mid hm
    obtain ⟨b1, b2, b3⟩ := play_mid ss ds back.tail m' z hz
    refine ⟨b1.trans a1, ?_, ?_⟩
    · show z.2.loc = m.loc ++ d :: ds
      rw [b2, a2, List.append_assoc]
      rfl
    · show z.2.seen = m.seen ++ (⟨x.vals, d⟩ :: roundsOf z.1)
      rw [b3, a3, List.append_assoc]
      rfl

theorem drawsFit_length : ∀ (zs : List Fmt.DeclaredRound) (ds : List Fmt.Drawn),
    drawsFit zs ds = true → ds.length = zs.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [drawsFit] at h
  | _ :: _, [], h => by simp [drawsFit] at h
  | _ :: zs, _ :: ds, h => by
    simp only [drawsFit, Bool.and_eq_true] at h
    exact congrArg (· + 1) (drawsFit_length zs ds h.2)

theorem exists_snoc {α : Type} : ∀ l : List α, l ≠ [] → ∃ A a, l = A ++ [a]
  | [], h => absurd rfl h
  | [a], _ => ⟨[], a, rfl⟩
  | a :: b :: l, _ => by
    obtain ⟨A, z, h⟩ := exists_snoc (b :: l) (by simp)
    exact ⟨a :: A, z, by rw [h]; rfl⟩

/-- If the sub-protocols pass `planOk` and `shaped`, each round declares as many oracle messages as
its entry counts roots. -/
theorem steps_shaped {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {bs : List (Block S Cl)} {hs : List (Placed V W X)} {ss : List (Step W X)}
    (h : chainSteps B rows look v bs hs = .ok ss)
    (hb : ∀ b ∈ bs, b.planOk = true ∧ b.shaped = true) :
    ∀ s ∈ ss, s.oracles.length = s.decl.entry.roots := by
  intro s hs'
  obtain ⟨-, h2⟩ := chainSteps_rows bs hs ss h
  have h1 : (s.decl, s.oracles, s.addr.place, s.move.isSome) ∈
      ss.map (fun s => (s.decl, s.oracles, s.addr.place, s.move.isSome)) :=
    List.mem_map.2 ⟨s, hs', rfl⟩
  rw [h2] at h1
  obtain ⟨b, hb', hz⟩ := List.mem_flatMap.1 h1
  obtain ⟨z, hz', e⟩ := List.mem_map.1 hz
  have e1 : z.1 = s.decl := congrArg (·.1) e
  have e2 : z.2 = s.oracles := congrArg (·.2.1) e
  have h3 := (hb b hb').2
  unfold Block.shaped at h3
  rw [Bool.and_eq_true] at h3
  have h4 := List.all_eq_true.1 h3.2 z hz'
  rw [Bool.and_eq_true] at h4
  rw [← e1, ← e2]
  exact beq_iff_eq.1 h4.1

/-- The coins that the shared chain may be given, in the two forms in which Honest/Frame.lean writes
them. -/
theorem look_shared {B : ProverCoinCounts} (c : Coins B) : c.look 1 = sharedLook B c.shared := rfl

/-! ## 2 The stops, over two consecutive lists -/

theorem or_assoc' {α : Type} (a b c : Option α) : (a.or b).or c = a.or (b.or c) := by
  cases a <;> rfl

theorem chainStopAt_append (v : Option V) (hs : List (Placed V W Y)) :
    ∀ (b₁ b₂ : List (Block S Cl)) (loc ds : List Fmt.Drawn),
    chainStopAt v (b₁ ++ b₂) hs loc ds =
      (chainStopAt v b₁ hs loc (ds.take (b₁.flatMap (·.rounds)).length)).or
        (chainStopAt v b₂ hs (loc ++ ds.take (b₁.flatMap (·.rounds)).length)
          (ds.drop (b₁.flatMap (·.rounds)).length))
  | [], b₂, loc, ds => by
    simp [chainStopAt]
  | b :: b₁, b₂, loc, ds => by
    have ih := chainStopAt_append v hs b₁ b₂ (loc ++ ds.take b.rounds.length)
      (ds.drop b.rounds.length)
    have e1 : (ds.take (b.rounds.length + (b₁.flatMap (·.rounds)).length)).take b.rounds.length =
        ds.take b.rounds.length := by
      rw [List.take_take, Nat.min_eq_left (Nat.le_add_right _ _)]
    have e2 : (ds.take (b.rounds.length + (b₁.flatMap (·.rounds)).length)).drop b.rounds.length =
        (ds.drop b.rounds.length).take (b₁.flatMap (·.rounds)).length := by
      rw [List.drop_take, Nat.add_sub_cancel_left]
    have e3 : ds.take (b.rounds.length + (b₁.flatMap (·.rounds)).length) =
        ds.take b.rounds.length ++ (ds.drop b.rounds.length).take
          (b₁.flatMap (·.rounds)).length := by
      rw [List.take_add]
    simp only [List.cons_append, chainStopAt, List.flatMap_cons, List.length_append]
    rw [ih, e1, e2, e3, or_assoc', List.append_assoc, List.drop_drop]

/-! ## 3 The available tables, at any start -/

theorem Env.ext' {E E' : Env} (h1 : E.stored = E'.stored) (h2 : E.tree = E'.tree)
    (h3 : E.sent = E'.sent) : E = E' := by
  cases E
  cases E'
  cases h1
  cases h2
  cases h3
  rfl

theorem Env.add_nil (E : Env) (hE : ∀ n, E.sent ≤ n → E.tree (.own n) = none) : E.add [] = E := by
  refine Env.ext' rfl ?_ rfl
  funext s
  cases s with
  | own n =>
    show (if n < E.sent then E.tree (.own n) else (([] : List (Option (Place × Table)))[n -
      E.sent]?).bind id) = E.tree (.own n)
    by_cases h : n < E.sent
    · rw [if_pos h]
    · rw [if_neg h, hE n (Nat.le_of_not_lt h)]
      rfl
  | taken ch j => rfl

theorem Env.add_add (E : Env) (ps qs : List Played) : (E.add ps).add qs = E.add (ps ++ qs) := by
  refine Env.ext' rfl ?_ ?_
  · funext s
    cases s with
    | own n =>
      show (if n < E.sent + (tablesOf ps).length then
          (if n < E.sent then E.tree (.own n) else ((tablesOf ps)[n - E.sent]?).bind id)
        else ((tablesOf qs)[n - (E.sent + (tablesOf ps).length)]?).bind id) =
        (if n < E.sent then E.tree (.own n) else ((tablesOf (ps ++ qs))[n - E.sent]?).bind id)
      rw [tablesOf_append]
      by_cases h1 : n < E.sent
      · rw [if_pos h1, if_pos h1, if_pos (Nat.lt_add_right _ h1)]
      · rw [if_neg h1, if_neg h1]
        by_cases h2 : n < E.sent + (tablesOf ps).length
        · rw [if_pos h2, List.getElem?_append_left (by omega)]
        · rw [if_neg h2, List.getElem?_append_right (by omega), Nat.sub_add_eq]
    | taken ch j => rfl
  · show E.sent + (tablesOf ps).length + (tablesOf qs).length =
      E.sent + (tablesOf (ps ++ qs)).length
    rw [tablesOf_append, List.length_append, Nat.add_assoc]

theorem lt_of_bind_some' {α : Type} {l : List (Option α)} {n : Nat} {a : α}
    (h : (l[n]?).bind id = some a) : n < l.length := by
  by_cases hn : n < l.length
  · exact hn
  · rw [List.getElem?_eq_none (Nat.le_of_not_lt hn)] at h
    cases h

theorem Env.add_prefix (E : Env) (ps qs : List Played) (s : Fmt.TreeSource) (pt : Place × Table)
    (h : (E.add ps).tree s = some pt) : (E.add (ps ++ qs)).tree s = some pt := by
  cases s with
  | own n =>
    have h' : (if n < E.sent then E.tree (.own n) else ((tablesOf ps)[n - E.sent]?).bind id) =
      some pt := h
    show (if n < E.sent then E.tree (.own n) else ((tablesOf (ps ++ qs))[n - E.sent]?).bind id) =
      some pt
    by_cases h1 : n < E.sent
    · rw [if_pos h1] at h' ⊢
      exact h'
    · rw [if_neg h1] at h' ⊢
      rw [tablesOf_append, List.getElem?_append_left (lt_of_bind_some' h')]
      exact h'
  | taken ch j => exact h

/-- No tree of the chain's own is available beyond those that it has sent. -/
def Env.Tight (E : Env) : Prop := ∀ n, E.sent ≤ n → E.tree (.own n) = none

/- `Env.Tight` holds after rounds are added. The hypothesis is not used: the statement holds of
every `E`. -/
theorem Env.add_tight {E : Env} (_ : E.Tight) (ps : List Played) : (E.add ps).Tight := by
  intro n hn
  have hn' : E.sent + (tablesOf ps).length ≤ n := hn
  show (if n < E.sent then E.tree (.own n) else ((tablesOf ps)[n - E.sent]?).bind id) = none
  rw [if_neg (by omega), List.getElem?_eq_none (by omega)]
  rfl

theorem envOf_tight (stored : Nat → Nat → Option (List UInt64))
    (taken : Nat → Nat → Option (Place × Table)) (ps : List Played) :
    (envOf stored taken ps).Tight := by
  intro n hn
  have hn' : (tablesOf ps).length ≤ n := hn
  show ((tablesOf ps)[n]?).bind id = none
  rw [List.getElem?_eq_none hn']
  rfl

/-! ## 4 Back to the run -/

theorem ends_back {R : Ready W₀ Rc Xi Ky Tr X₀ X} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {ρ₁ ρ₂ : List Fmt.Drawn} {b₁ b₂ : List Fmt.RoundView}
    {r₁ : List Played × Mid (Local W₀ Rc Xi Tr) X} {r₂ : List Played × Mid (Common W₀ Rc Ky) X₀}
    (h1 : play R.first ρ₁ b₁ (R.start₁ H) = .ok r₁) (hq : sealQuiet r₁.1 = true)
    (h2 : play R.shared ρ₂ b₂ (R.start₂ H) = .ok r₂) :
    R.ends H ρ₁ ρ₂ b₁ b₂ = .ok (r₁, r₂) := by
  unfold Ready.ends
  rw [h1, h2]
  simp [Except.bind, Except.map, sealTest, hq]

/-- **From its parts back to the run**, with no stored run to fall back on. -/
theorem run_back {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc}
    {x : Xi} {c : Coins B} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    {r₁ : List Played × Mid (Local W₀ Rc Xi Tr) X} {r₂ : List Played × Mid (Common W₀ Rc Ky) X₀}
    {r₃ : List Played × Mid (Local W₀ Rc Xi Tr) X} {c₁ c₂ c₃ : List OpenedColumn}
    (hR : ready F B H w₀ rc x c = .ok R) (h1 : play R.first ρ.first [] (R.start₁ H) = .ok r₁)
    (hq : sealQuiet r₁.1 = true) (h2 : play R.shared ρ.shared [] (R.start₂ H) = .ok r₂)
    (h3 : play R.second ρ.second [] (R.start₃ H r₁.2 r₂.2) = .ok r₃)
    (f1 : fillCols (readsOf 0 0 (H.storedWords w₀ rc) (treeOwn r₁.1) F.roundsDeclaredByBlocks.1 ρ.first) [] = .ok c₁)
    (f2 : fillCols (readsOf 1 0 (H.storedWords w₀ rc) (treeOwn r₂.1) F.roundsDeclaredByBlocks.2.1 ρ.shared) [] =
      .ok c₂)
    (f3 : fillCols (readsOf 2 F.lastChainFirstTreeNumber (H.storedWords w₀ rc) (treeThird r₁.1 r₂.1 r₃.1)
      F.roundsDeclaredByBlocks.2.2 ρ.second) [] = .ok c₃) :
    ∃ r, run F B H w₀ rc x c ρ none = .ok r ∧
      r.views = (⟨(roundsOf r₁.1).dropLast, c₁⟩, ⟨roundsOf r₂.1, c₂⟩, ⟨roundsOf r₃.1, c₃⟩) := by
  have hE := ends_back h1 hq h2
  refine ⟨⟨(r₁.1, r₂.1, r₃.1),
    (readsOf 0 0 (H.storedWords w₀ rc) (treeOwn r₁.1) F.roundsDeclaredByBlocks.1 ρ.first,
      readsOf 1 0 (H.storedWords w₀ rc) (treeOwn r₂.1) F.roundsDeclaredByBlocks.2.1 ρ.shared,
      readsOf 2 F.lastChainFirstTreeNumber (H.storedWords w₀ rc) (treeThird r₁.1 r₂.1 r₃.1) F.roundsDeclaredByBlocks.2.2 ρ.second),
    (⟨(roundsOf r₁.1).dropLast, c₁⟩, ⟨roundsOf r₂.1, c₂⟩, ⟨roundsOf r₃.1, c₃⟩)⟩, ?_, rfl⟩
  unfold run
  simp [hR, hE, h3, f1, f2, f3, Except.bind, Except.map, unfit, Except.mapError]

/-! ## 5 The sealing round -/

/- If the rounds are played with no stored run to fall back on, the last round declares no item
except roots and no oracle message, its entry counts no root, and its challenge is the empty one,
the test on the sealing round passes. -/
theorem seal_quiet {ss : List (Step W X)} {s : Step W X} {ds : List Fmt.Drawn}
    {ps : List Played} (h : Yields (ss ++ [s]) (ds ++ [⟨[], [], [], none⟩]) [] ps)
    (hl : ss.length = ds.length) (hi : (s.decl.items.filter (· != .root)) = [])
    (ho : s.oracles = []) (hr : s.decl.entry.roots = 0) : sealQuiet ps = true := by
  induction ss generalizing ds ps with
  | nil =>
    cases ds with
    | cons d ds => simp at hl
    | nil =>
      cases ps with
      | nil => simp [Yields] at h
      | cons p ps =>
        cases ps with
        | cons q ps => simp [Yields] at h
        | nil =>
          have h' : s.Yields none ⟨[], [], [], none⟩ p := h.1
          obtain ⟨e1, -, -, ht, hn⟩ := h'
          have hv : p.vals = [] ∧ p.tables = [] := by
            cases hm : s.move.isSome with
            | true =>
              obtain ⟨-, z, hz, hv, htb⟩ := ht hm
              simp only [Sending.fits, Bool.and_eq_true, beq_iff_eq, hi, ho, List.map_nil,
                List.map_eq_nil_iff] at hz
              rw [hv, htb, hz.1, hz.2]
              exact ⟨rfl, rfl⟩
            | false =>
              obtain ⟨-, hv, htb⟩ := hn hm
              rw [hv, htb, hr]
              exact ⟨rfl, rfl⟩
          simp [sealQuiet, hv.1, hv.2, e1]
  | cons a ss ih =>
    cases ds with
    | nil => simp at hl
    | cons d ds =>
      cases ps with
      | nil => simp [Yields] at h
      | cons p ps =>
        have h' : Yields (ss ++ [s]) (ds ++ [⟨[], [], [], none⟩]) [] ps := h.2
        have h2 := ih h' (by simpa using hl)
        cases ps with
        | nil => simp [sealQuiet] at h2
        | cons q ps =>
          have e : sealQuiet (p :: q :: ps) = sealQuiet (q :: ps) := by
            simp [sealQuiet, List.getLast?_cons_cons]
          rw [e]
          exact h2

end ProofFile.Honest

#print axioms ProofFile.Honest.hear_mid
#print axioms ProofFile.Honest.play_mid
#print axioms ProofFile.Honest.drawsFit_length
#print axioms ProofFile.Honest.exists_snoc
#print axioms ProofFile.Honest.steps_shaped
#print axioms ProofFile.Honest.look_shared
#print axioms ProofFile.Honest.or_assoc'
#print axioms ProofFile.Honest.chainStopAt_append
#print axioms ProofFile.Honest.Env.ext'
#print axioms ProofFile.Honest.Env.add_nil
#print axioms ProofFile.Honest.Env.add_add
#print axioms ProofFile.Honest.lt_of_bind_some'
#print axioms ProofFile.Honest.Env.add_prefix
#print axioms ProofFile.Honest.Env.add_tight
#print axioms ProofFile.Honest.envOf_tight
#print axioms ProofFile.Honest.ends_back
#print axioms ProofFile.Honest.run_back
#print axioms ProofFile.Honest.seal_quiet
