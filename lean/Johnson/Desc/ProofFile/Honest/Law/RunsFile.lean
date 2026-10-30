-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/RunsFile.lean: `runC` (Honest/Walk.lean) returns, at a run's coins
at which the invariants hold at the chains' starts, outside the stops, whatever the verifier's own
steps decide. This is the rule for a file, `runC_returns`. Its hypotheses: the first condition at
every sub-protocol of the three flat lists (`PlaysOn`, Honest/Law/ThreadC.lean), from the invariant
before it to the one after it; the invariants at the two starts, and at the second chain's start
where that accepts, each at the state as `ChainProgress.start` lays it (at the two starts no column has been
opened; at the second chain's start, where the two ends' fields `opened` hold columns, these
joined); and what the plan declares of the rounds that `ready` has prepared (`PlanServes`). And
three more: that `ready` returns at these coins; the executable test `sealPlain F` on the sealing
round's declaration (Honest/Law/Thread.lean); and that the challenges are such as the rounds can
draw (`Draws.due`).

What this is. A conditional lemma on this folder's own functions, pointwise: at one input, one run's
coins and one list of challenges. Its hypotheses are proved here of no description. It says nothing
of a verifier's acceptance, and it is none of the library's goals.

  1  `took_nil`, `plays_of_bare`, `plays_of_quiet`   the first condition at a sub-protocol without a
     prover's side; `took_nil`: where no column is read the field `opened` stays as it is
  2  `walk_seal`   the sealing round as produced, real or substitute, sends nothing
  3  `PlanServes`, `ChainServes`, `served_own`, `taken₃`, `envThird_eq`   what the plan declares;
     the trees to take over
  4  `runC_returns`   the rule

Limits.
  * The rule is pointwise in the run's coins: the invariants at the two starts and at the second
    chain's start are hypotheses at that coin, and may narrow the coins. An invariant that leaves
    the state's field `opened` free asks `PlaysOn` at every value of it, `none` too: at a prover
    with a part that reads the columns and errs at `none` (its duty: Honest/Frame.lean,
    `Seen.opened`), `PlaysOn` at an invariant that lets `none` through before that part's
    sub-protocol is met only vacuously (Honest/Law/ThreadC.lean, Limits).
  * `PlanServes` is a hypothesis. That a description's tests on the plan, a test on the prover's
    sides (`rootedAll`) and its stored columns give it is proved in Honest/Law/PlanGives.lean.
  * Which parts were called, and what the state of the run was before each, is not said here.
  * Nothing is said on how likely a stop or a rejection is.
  * `sealPlain F` and `Draws.due` are hypotheses: without them `runC` can return an error though all
    else holds.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.RunsC
import Johnson.Desc.ProofFile.Honest.WalkOpened

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl Xi V W Y Pb W₀ Rc Ky Tr X₀ X : Type}

/-! ## 1 A sub-protocol without a prover's side -/

/-- Where no column is read the field stays as it is. -/
theorem took_nil (m : Mid W Y) : m.took [] = m := by
  obtain ⟨st, loc, seen, opened⟩ := m
  cases opened <;> simp [Mid.took]

section
variable {φ : Face V W Pb} {Bk : ProverCoinCounts} {chain ft : Nat} {hs : List (Placed V W Y)}
  {b : Block S Cl}

/-- A sub-protocol without a prover's side, with rounds or without: `play` goes through by itself;
the rest is a hypothesis on what it returns, with B at the state that has taken the columns
(`y.2.took cols`). -/
theorem plays_of_bare {A B : Coins Bk → S → Mid W Y → Env → Prop}
    (hf : (hs.find? fun g => g.place == b.place) = none)
    (h : ∀ k s m E ds y, A k s m E → drawsFit b.rounds ds = true →
      play (bareSteps b) ds [] m = .ok y →
      ∃ cols : List OpenedColumn,
        fillCols (readsOf chain ft (E.add y.1).stored (E.add y.1).tree b.rounds ds) [] =
          .ok cols ∧
        ∀ s' n, b.step ft s (roundsOf y.1) cols = .ok (s', n) →
          B k s' (y.2.took cols) (E.add y.1)) :
    PlaysOn φ Bk chain ft hs b A B := by
  intro k s m E ds l hA hd _ hl
  have ho := (chainSteps_rows [b] hs l hl).1 b List.mem_cons_self
  obtain rfl := steps_one_none hf hl
  obtain ⟨y, hy⟩ := play_bare_ok (bareSteps (W := W) (Y := Y) b) ds m
    (fun s' hs' => by
      obtain ⟨r, -, rfl⟩ := List.mem_map.1 hs'
      exact ⟨rfl, rfl, rfl⟩)
    (by
      rw [drawsFit_length _ _ hd]
      simp [bareSteps, ho])
  obtain ⟨cols, h1, h2⟩ := h k s m E ds y hA hd hy
  exact ⟨y, cols, hy, h1, h2⟩

/-- A sub-protocol without a round and without a prover's side (for example the blocks of no kind
that the library adds to a chain's list, such as the one where a segment starts): where its decision
accepts, B. -/
theorem plays_of_quiet {A B : Coins Bk → S → Mid W Y → Env → Prop} (hr : b.rounds = [])
    (hf : (hs.find? fun g => g.place == b.place) = none)
    (h : ∀ k s m E s', A k s m E → b.decide s [] [] = .ok s' → B k s' m (E.add [])) :
    PlaysOn φ Bk chain ft hs b A B := by
  refine plays_of_bare hf fun k s m E ds y hA hd hy => ?_
  rw [hr] at hd
  have hds : ds = [] := by
    cases ds with
    | nil => rfl
    | cons _ _ => simp [drawsFit] at hd
  subst hds
  have hb : bareSteps (W := W) (Y := Y) b = [] := by simp [bareSteps, hr]
  rw [hb] at hy
  simp only [play] at hy
  cases hy
  refine ⟨[], by rw [hr]; rfl, fun s' n hs' => ?_⟩
  have h1 := ((step_iff ft b s s' _ _ n).1 hs').2.1
  have h2 : b.decide s [] [] = .ok s' := by
    unfold Block.shown at h1
    rw [hr] at h1
    exact h1
  show B k s' (m.took []) (E.add [])
  rw [took_nil]
  exact h k s m E s' hA h2

end

/-! ## 2 The sealing round -/

theorem walk_seal {L : Lay} {ss : List (Step W Y)} {s : Step W Y} {ds : List Fmt.Drawn}
    {z z' : ChainProgress S Cl W Y} (hw : walk L (ss ++ [s]) (ds ++ [⟨[], [], [], none⟩]) z = .ok z')
    (hl : ds.length = ss.length) (hi : (s.decl.items.filter (· != .root)) = [])
    (ho : s.oracles = []) (hr : s.decl.entry.roots = 0) : sealQuiet z'.laid = true := by
  obtain ⟨z₁, -, h2⟩ := walk_append_ok [s] [⟨[], [], [], none⟩] ss ds z z' hl hw
  obtain ⟨x, z₂, hx, hz, h3⟩ := walk_cons_ok h2
  rw [walk_nil_ok h3, heard_laid hz]
  obtain ⟨hv, ht, -⟩ := say_fits hx (Or.inr (by rw [hi]; rfl)) (by rw [ho, hr]; rfl)
  rw [hi] at hv
  rw [ho] at ht
  have hv' : x.vals = [] := List.map_eq_nil_iff.1 hv
  have ht' : x.tables = [] := List.eq_nil_of_length_eq_zero ht
  simp [sealQuiet, hv', ht']

/-! ## 3 What the plan declares -/

/-- What a chain's rounds, as `ready` has prepared them, declare: each as many oracle messages as
its entry counts roots; a round without a move declares no root and is under the part 0; a tree of
the chain's own is declared no later than it is opened, with the width at which it is opened; the
stored columns that are read are available with the declared width. -/
structure ChainServes (stored : Nat → Nat → Option (List UInt64)) (l : List (Step W Y)) : Prop where
  shaped : ∀ u ∈ l, u.oracles.length = u.decl.entry.roots
  noRoot : ∀ u ∈ l, u.move.isSome = false → u.decl.entry.roots = 0
  part0 : ∀ u ∈ l, u.move.isSome = false → u.addr.part = 0
  inTime : InTime l
  stored : ∀ u ∈ l, ∀ t ∈ u.decl.stored, ∀ x, x < 2 ^ t.sh.a →
    ∃ c, stored t.item x = some c ∧ c.length = t.sh.W

/-- **What the plan declares of a file's three chains.** The first two take over nothing; what the
second chain takes over is declared by the chain that it names, with the width at which it is
opened. A structure of hypotheses. -/
structure PlanServes (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc)
    (R : Ready W₀ Rc Xi Ky Tr X₀ X) : Prop where
  first : ChainServes (H.storedWords w₀ rc) R.first
  shared : ChainServes (H.storedWords w₀ rc) R.shared
  second : ChainServes (H.storedWords w₀ rc) R.second
  own₁ : ∀ u ∈ R.first, ∀ o ∈ u.decl.opens, ∀ ch j, o.2 ≠ .taken ch j
  own₂ : ∀ u ∈ R.shared, ∀ o ∈ u.decl.opens, ∀ ch j, o.2 ≠ .taken ch j
  taken : ∀ u ∈ R.second, ∀ o ∈ u.decl.opens, ∀ ch j, o.2 = .taken ch j →
    (ch = 0 ∧ ∃ orc, (R.first.flatMap (·.oracles))[j]? = some orc ∧ orc.words = o.1.W) ∨
    (ch = 1 ∧ ∃ orc, (R.shared.flatMap (·.oracles))[j]? = some orc ∧ orc.words = o.1.W)

/-- The look-up of a tree that the second chain takes over, from the rounds that the two earlier
chains have produced. -/
def taken₃ (l₁ l₂ : List Played) (ch j : Nat) : Option (Place × Table) :=
  if ch == 0 then ((tablesOf l₁)[j]?).bind id
  else if ch == 1 then ((tablesOf l₂)[j]?).bind id else none

theorem envThird_eq (stored : Nat → Nat → Option (List UInt64)) (l₁ l₂ : List Played) :
    envThird (envOf stored (fun _ _ => none) l₁) (envOf stored (fun _ _ => none) l₂) =
      envOf stored (taken₃ l₁ l₂) [] := by
  refine Env.ext' rfl ?_ rfl
  funext s
  cases s <;> rfl

theorem served_own {stored : Nat → Nat → Option (List UInt64)} {l : List (Step W Y)}
    (chain ft : Nat) (h : ChainServes stored l)
    (hn : ∀ u ∈ l, ∀ o ∈ u.decl.opens, ∀ ch j, o.2 ≠ .taken ch j) :
    Served ⟨chain, ft, stored, treeOwn⟩ (fun _ _ => none) l :=
  fun u hu => ⟨h.stored u hu, fun o ho ch j e => absurd e (hn u hu o ho ch j)⟩

/-! ## 4 The rule -/

/-- **`runC` returns**, at a run's coins at which the invariants hold at the starts, at the states
as `ChainProgress.start` lays them (a₁, a₂: no column has been opened; a₃: where the two ends' fields
`opened` are `some o₁` and `some o₂`, at `some (o₁ ++ o₂)`: in a run these are the two chains'
columns (`walk_inv`, Honest/WalkOpened.lean)), outside the stops, whatever the verifier's own steps
decide. Further hypotheses: `ready` returns at these coins; `sealPlain F`; the challenges pass
`Draws.due`; `PlanServes`; and `PlaysOn` at every sub-protocol of the three flat lists. A
conditional lemma on this folder's own functions, pointwise. It says nothing of a verifier's
acceptance, and it is none of the library's goals. -/
theorem runC_returns {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F Bk H w₀ rc x k = .ok R) (hq : sealPlain F = true) (hρ : ρ.due F = true)
    (hsil : silentAt F H w₀ rc x ρ = none) (hP : PlanServes H w₀ rc R)
    (I₁ : Nat → Coins Bk → F.S₁ → Mid (Local W₀ Rc Xi Tr) X → Env → Prop)
    (I₂ : Nat → Coins Bk → F.S₂ → Mid (Common W₀ Rc Ky) X₀ → Env → Prop)
    (I₃ : Nat → Coins Bk → F.S₃ → Mid (Local W₀ Rc Xi Tr) X → Env → Prop)
    (h₁ : ∀ j b, F.first.blocksInOrder[j]? = some b → PlaysOn .own Bk 0 0 H.first b (I₁ j) (I₁ (j + 1)))
    (h₂ : ∀ j b, F.shared.blocksInOrder[j]? = some b →
      PlaysOn .shared Bk 1 0 H.shared b (I₂ j) (I₂ (j + 1)))
    (h₃ : ∀ j b, F.second.blocksInOrder[j]? = some b →
      PlaysOn .own Bk 2 F.lastChainFirstTreeNumber H.second b (I₃ j) (I₃ (j + 1)))
    (a₁ : I₁ 0 k (F.start₁ (F.pub x)) { R.start₁ H with opened := some [] }
      (envOf (H.storedWords w₀ rc) (fun _ _ => none) []))
    (a₂ : I₂ 0 k (F.start₂ (F.pub x)) { R.start₂ H with opened := some [] }
      (envOf (H.storedWords w₀ rc) (fun _ _ => none) []))
    (a₃ : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂, I₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      I₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → F.start₃ (F.pub x) e₁ e₂ = .ok s₃ →
      m₁.opened = some o₁ → m₂.opened = some o₂ →
      I₃ 0 k s₃ { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) } (envThird E₁ E₂)) :
    ∃ r, runC F Bk H w₀ rc x k ρ = .ok r := by
  obtain ⟨-, tr, htr, hown, hcom, s1, s2, s3⟩ := ready_ok hR
  simp only [Draws.due, Bool.and_eq_true, beq_iff_eq] at hρ
  obtain ⟨⟨⟨d1, d2⟩, d3⟩, d4⟩ := hρ
  unfold silentAt at hsil
  rw [htr] at hsil
  have hsil' : (chainStopAt (Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr)) F.first.blocksInOrder
      H.first [] ρ.first).or
      ((chainStopAt (Face.shared.sees (⟨w₀, rc, H.key x⟩ : Common W₀ Rc Ky)) F.shared.blocksInOrder
        H.shared [] ρ.shared).or
        (chainStopAt (Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr)) F.second.blocksInOrder H.second
          ρ.first ρ.second)) = none := hsil
  obtain ⟨t1, t23⟩ := or_none hsil'
  obtain ⟨t2, t3⟩ := or_none t23
  rw [← hown] at t1 t3
  rw [← hcom] at t2
  have hLo : ∀ ps, treeOwn ps = (envOf (H.storedWords w₀ rc) (fun _ _ => none) ps).tree :=
    fun ps => ((envOf_tree (H.storedWords w₀ rc) ps [] []).1).symm
  -- the first chain
  obtain ⟨z₁, X₁, T₁, c₁⟩ := chain_returns (φ := Face.own) (hs := H.first)
    ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ (fun _ _ => none) hLo R.first hP.first.inTime
    (served_own 0 0 hP.first hP.own₁) hP.first.shaped hP.first.noRoot hP.first.part0 k
    (Face.own.sees R.own) ρ.first F.first.blocksInOrder I₁ h₁ [] R.first
    ⟨some { R.start₁ H with opened := some [] }, some (F.start₁ (F.pub x)), none, [], [], [],
      F.first.blocksInOrder, []⟩ ρ.first rfl
    rfl tablesFit_nil s1 d1 (Or.inl ⟨_, _, rfl, rfl, rfl, a₁, t1, rfl⟩)
  obtain ⟨b₁, hb₁, hw₁⟩ := exBind_ok X₁
  have hb₁' : ChainProgress.start ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder (some (R.start₁ H))
      (some (F.start₁ (F.pub x))) [] = .ok b₁ := hb₁
  have inv₁ : z₁.Inv [] := walk_inv _ [] _ _ b₁ z₁ (start_inv hb₁') hw₁
  -- the sealing round
  have hne : R.first ≠ [] := by
    intro h0
    have e := steps_decl s1
    rw [h0] at e
    have e' : F.roundsDeclaredByBlocks.1 = [] := e.symm
    simp [sealPlain, e'] at hq
  obtain ⟨ss, sL, hss⟩ := exists_snoc R.first hne
  obtain ⟨dsA, hdsA⟩ := List.getLast?_eq_some_iff.1 d4
  have hdecl : F.roundsDeclaredByBlocks.1 = ss.map (·.decl) ++ [sL.decl] := by
    rw [show F.roundsDeclaredByBlocks.1 = R.first.map (·.decl) from (steps_decl s1).symm, hss, List.map_append]
    rfl
  have hq' : (sL.decl.items.filter (· != .root)) = [] ∧ sL.decl.entry.roots = 0 := by
    simpa [sealPlain, hdecl] using hq
  have hlen : dsA.length = ss.length := by
    have e := drawsFit_length _ _ d1
    rw [hdecl, hdsA] at e
    simp at e
    exact e
  have hor : sL.oracles = [] := by
    have e := hP.first.shaped sL (by rw [hss]; simp)
    rw [hq'.2] at e
    exact List.eq_nil_of_length_eq_zero e
  have hseal : sealQuiet z₁.laid = true := by
    rw [hss, hdsA] at hw₁
    exact walk_seal hw₁ hlen hq'.1 hor hq'.2
  -- the shared chain
  obtain ⟨z₂, X₂, T₂, c₂⟩ := chain_returns (φ := Face.shared) (hs := H.shared)
    ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ (fun _ _ => none) hLo R.shared hP.shared.inTime
    (served_own 1 0 hP.shared hP.own₂) hP.shared.shaped hP.shared.noRoot hP.shared.part0 k
    (Face.shared.sees R.common) ρ.shared F.shared.blocksInOrder I₂ h₂ [] R.shared
    ⟨some { R.start₂ H with opened := some [] }, some (F.start₂ (F.pub x)), none, [], [], [],
      F.shared.blocksInOrder, []⟩ ρ.shared
    rfl rfl tablesFit_nil s2 d2 (Or.inl ⟨_, _, rfl, rfl, rfl, a₂, t2, rfl⟩)
  obtain ⟨b₂, hb₂, hw₂⟩ := exBind_ok X₂
  have hb₂' : ChainProgress.start ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ H))
      (some (F.start₂ (F.pub x))) [] = .ok b₂ := hb₂
  have inv₂ : z₂.Inv [] := walk_inv _ [] _ _ b₂ z₂ (start_inv hb₂') hw₂
  -- the second chain
  have hL₃ : ∀ ps, treeThird z₁.laid z₂.laid ps =
      (envOf (H.storedWords w₀ rc) (taken₃ z₁.laid z₂.laid) ps).tree :=
    fun ps => ((envOf_tree (H.storedWords w₀ rc) z₁.laid z₂.laid ps).2).symm
  have hS₃ : Served ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩
      (taken₃ z₁.laid z₂.laid) R.second := by
    intro u hu
    refine ⟨hP.second.stored u hu, fun o ho ch j e => ?_⟩
    rcases hP.taken u hu o ho ch j e with ⟨rfl, orc, g1, g2⟩ | ⟨rfl, orc, g1, g2⟩
    · obtain ⟨pt, g3, g4⟩ := T₁.2 j orc g1
      exact ⟨pt, by show ((tablesOf z₁.laid)[j]?).bind id = some pt; rw [g3]; rfl, g4.trans g2⟩
    · obtain ⟨pt, g3, g4⟩ := T₂.2 j orc g1
      exact ⟨pt, by show ((tablesOf z₂.laid)[j]?).bind id = some pt; rw [g3]; rfl, g4.trans g2⟩
  have mode₃ : ∀ (m₃ : Option (Mid (Local W₀ Rc Xi Tr) X)) (v₃ : Option F.S₃),
      m₃ = (z₁.mid.bind fun m₁ => z₂.mid.map fun m₂ => R.start₃ H m₁ m₂) →
      v₃ = door₃ F x z₁.ver z₂.ver →
      ((∃ s m, (if v₃.isSome then m₃.map fun y => { y with opened := some (z₁.cols ++ z₂.cols) }
            else none) = some m ∧
          (if m₃.isSome then v₃ else none) = some s ∧ Face.own.sees m.st.input =
            Face.own.sees R.own ∧
          I₃ 0 k s m (envOf (H.storedWords w₀ rc) (taken₃ z₁.laid z₂.laid) []) ∧
          chainStopAt (Face.own.sees R.own) F.second.blocksInOrder H.second m.loc ρ.second = none ∧
          m.loc ++ ρ.second = ρ.first ++ ρ.second) ∨
        ((if v₃.isSome then m₃.map fun y => { y with opened := some (z₁.cols ++ z₂.cols) }
            else none) = none ∧ (if m₃.isSome then v₃ else none) = none)) := by
    intro m₃ v₃ hm hv
    rcases c₁ with ⟨e₁, m₁, v1, q1, i1, l1⟩ | ⟨q1, v1⟩
    · rcases c₂ with ⟨e₂, m₂, v2, q2, i2, -⟩ | ⟨q2, v2⟩
      · rw [q1, q2] at hm
        rw [v1, v2] at hv
        cases hs₃ : F.start₃ (F.pub x) e₁ e₂ with
        | error w =>
          have hv' : v₃ = none := by
            rw [hv]
            show (F.start₃ (F.pub x) e₁ e₂).toOption = none
            rw [hs₃]
            rfl
          rw [hv']
          exact Or.inr ⟨rfl, by split <;> rfl⟩
        | ok s₃ =>
          have hv' : v₃ = some s₃ := by
            rw [hv]
            show (F.start₃ (F.pub x) e₁ e₂).toOption = some s₃
            rw [hs₃]
            rfl
          have hm' : m₃ = some (R.start₃ H m₁ m₂) := hm
          rw [hv', hm']
          have i0 := a₃ _ _ _ _ _ _ s₃ z₁.cols z₂.cols i1 i2 hs₃ (inv₁ m₁ q1) (inv₂ m₂ q2)
          rw [envThird_eq] at i0
          refine Or.inl ⟨s₃, { R.start₃ H m₁ m₂ with opened := some (z₁.cols ++ z₂.cols) }, rfl,
            rfl, rfl, i0, ?_, ?_⟩
          · show chainStopAt (Face.own.sees R.own) F.second.blocksInOrder H.second m₁.loc ρ.second = none
            rw [l1]
            exact t3
          · show m₁.loc ++ ρ.second = _
            rw [l1]
      · have hm' : m₃ = none := by
          rw [hm, q2]
          cases z₁.mid <;> rfl
        rw [hm']
        exact Or.inr ⟨by split <;> rfl, rfl⟩
    · have hm' : m₃ = none := by
        rw [hm, q1]
        rfl
      rw [hm']
      exact Or.inr ⟨by split <;> rfl, rfl⟩
  obtain ⟨z₃, X₃, -, -⟩ := chain_returns (φ := Face.own) (hs := H.second)
    ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ (taken₃ z₁.laid z₂.laid) hL₃
    R.second hP.second.inTime hS₃ hP.second.shaped hP.second.noRoot hP.second.part0 k
    (Face.own.sees R.own) (ρ.first ++ ρ.second) F.second.blocksInOrder I₃ h₃ [] R.second
    ⟨if (door₃ F x z₁.ver z₂.ver).isSome
        then (z₁.mid.bind fun m₁ => z₂.mid.map fun m₂ => R.start₃ H m₁ m₂).map
          fun y => { y with opened := some (z₁.cols ++ z₂.cols) } else none,
      if (z₁.mid.bind fun m₁ => z₂.mid.map fun m₂ => R.start₃ H m₁ m₂).isSome
        then door₃ F x z₁.ver z₂.ver else none, none, [], [], [], F.second.blocksInOrder, []⟩ ρ.second rfl
    rfl tablesFit_nil s3 d3 (mode₃ _ _ rfl rfl)
  obtain ⟨b₃, hb₃, hw₃⟩ := exBind_ok X₃
  have hb₃' : ChainProgress.start ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩
      F.second.blocksInOrder (z₁.mid.bind fun m₁ => z₂.mid.map fun m₂ => R.start₃ H m₁ m₂)
      (door₃ F x z₁.ver z₂.ver) (z₁.cols ++ z₂.cols) = .ok b₃ := hb₃
  refine ⟨⟨⟨(z₁.laid, z₂.laid, z₃.laid), (z₁.reads, z₂.reads, z₃.reads),
      (⟨(roundsOf z₁.laid).dropLast, z₁.cols⟩, ⟨roundsOf z₂.laid, z₂.cols⟩,
        ⟨roundsOf z₃.laid, z₃.cols⟩)⟩,
    (z₁.ver, z₂.ver, z₃.ver), (z₁.refused, z₂.refused, z₃.refused)⟩, ?_⟩
  unfold runC
  simp [hR, hb₁', hw₁, hseal, hb₂', hw₂, hb₃', hw₃, Except.bind, Except.map]

end ProofFile.Honest

#print axioms ProofFile.Honest.took_nil
#print axioms ProofFile.Honest.plays_of_bare
#print axioms ProofFile.Honest.plays_of_quiet
#print axioms ProofFile.Honest.walk_seal
#print axioms ProofFile.Honest.envThird_eq
#print axioms ProofFile.Honest.served_own
#print axioms ProofFile.Honest.runC_returns
#print axioms ProofFile.Honest.ChainServes
#print axioms ProofFile.Honest.PlanServes
#print axioms ProofFile.Honest.taken₃
