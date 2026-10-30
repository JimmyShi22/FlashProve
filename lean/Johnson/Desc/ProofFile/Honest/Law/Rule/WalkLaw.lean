-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/WalkLaw.lean: what a run of `runC` (Honest/Walk.lean) that
goes through consists of. `runC` plays the prover's sides and asks the description's own step after
each sub-protocol. A run of `runC` consists of three walks, and a walk of its rounds. Inside one
sub-protocol a walk is the rounds' messages and updates alone (`lays`), and then the sub-protocols
whose rounds have all been produced are asked once. Most lemmas have the form "… = .ok z' → ∃ …",
like `run_parts` (Honest/Law/Run.lean).

  1  `runC_parts`   a run's three walks: the first chain's and the shared chain's begin where no
     column has been opened (`ChainProgress.start` at `[]`), the second chain's at the columns of these two
     (`runC_views`, Honest/WalkOpened.lean, has the same eight equations, with `ChainProgress.Inv` at the
     three starts; of r, its opened columns alone)
  2  `walk_nil_ok`, `walk_cons_ok`, `walk_append_ok`   a walk, round by round; over two consecutive
     lists
  3  `settle_wait`, `settle_ask_ok`   the asking: a sub-protocol whose rounds have not all been
     produced waits; one whose rounds have all been produced is asked, and where it accepts, the
     columns that it read are laid behind those in the field `opened` of the state of the prover's
     run (`Mid.took`)
     `sayAt`, `hearAtO`, `say_eq`, `heard_ok`   a round's message and update, as functions of the
     state of the prover's run
  4  `lays`, `ChainProgress.grown`, `member_ok`   a sub-protocol's rounds without the asking; inside one
     sub-protocol
  5  `lays_live`, `lays_sub`, `subPlayed`   while the prover's run goes on: the rounds of `play`;
     where nothing more is played: the substitutes

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Walk
import Johnson.Desc.ProofFile.Honest.Law.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place Oracle OpenedColumn)

variable {S Cl Xi W₀ Rc Ky Tr X₀ X W Y : Type}

/-! ## 1 A run -/

/-- **What a run of `runC` that goes through consists of.** -/
theorem runC_parts {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    {rc : Rc} {x : Xi} {c : Coins B} {ρ : Draws} {r : RunC F}
    (h : runC F B H w₀ rc x c ρ = .ok r) :
    ∃ R a₁ z₁ a₂ z₂ a₃ z₃, ready F B H w₀ rc x c = .ok R ∧
      ChainProgress.start ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder (some (R.start₁ H))
        (some (F.start₁ (F.pub x))) [] = .ok a₁ ∧
      walk ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ R.first ρ.first a₁ = .ok z₁ ∧
      sealQuiet z₁.laid = true ∧
      ChainProgress.start ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ H))
        (some (F.start₂ (F.pub x))) [] = .ok a₂ ∧
      walk ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ R.shared ρ.shared a₂ = .ok z₂ ∧
      ChainProgress.start ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ F.second.blocksInOrder
        (z₁.mid.bind fun m₁ => z₂.mid.map fun m₂ => R.start₃ H m₁ m₂)
        (door₃ F x z₁.ver z₂.ver) (z₁.cols ++ z₂.cols) = .ok a₃ ∧
      walk ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ R.second ρ.second
        a₃ = .ok z₃ ∧
      r = ⟨⟨(z₁.laid, z₂.laid, z₃.laid), (z₁.reads, z₂.reads, z₃.reads),
          (⟨(roundsOf z₁.laid).dropLast, z₁.cols⟩, ⟨roundsOf z₂.laid, z₂.cols⟩,
            ⟨roundsOf z₃.laid, z₃.cols⟩)⟩,
        (z₁.ver, z₂.ver, z₃.ver), (z₁.refused, z₂.refused, z₃.refused)⟩ := by
  unfold runC at h
  obtain ⟨R, hR, h⟩ := exBind_ok h
  obtain ⟨a₁, ha₁, h⟩ := exBind_ok h
  obtain ⟨z₁, hz₁, h⟩ := exBind_ok h
  obtain ⟨hq, h⟩ := exIte_ok h
  obtain ⟨a₂, ha₂, h⟩ := exBind_ok h
  obtain ⟨z₂, hz₂, h⟩ := exBind_ok h
  obtain ⟨a₃, ha₃, h⟩ := exBind_ok h
  obtain ⟨z₃, hz₃, h⟩ := exMap_ok h
  exact ⟨R, a₁, z₁, a₂, z₂, a₃, z₃, hR, ha₁, hz₁, by simpa using hq, ha₂, hz₂, ha₃, hz₃, h.symm⟩

/-! ## 2 A walk -/

theorem walk_nil_ok {L : Lay} {z z' : ChainProgress S Cl W Y} (h : walk L [] [] z = .ok z') : z' = z := by
  rw [walk] at h
  exact (Except.ok.inj h).symm

theorem walk_cons_ok {L : Lay} {s : Step W Y} {ss : List (Step W Y)} {d : Fmt.Drawn}
    {ds : List Fmt.Drawn} {z z' : ChainProgress S Cl W Y} (h : walk L (s :: ss) (d :: ds) z = .ok z') :
    ∃ x z₁, z.say s = .ok x ∧ z.heard L s x d = .ok z₁ ∧ walk L ss ds z₁ = .ok z' := by
  rw [walk] at h
  obtain ⟨x, hx, h⟩ := exBind_ok h
  obtain ⟨z₁, hz, h⟩ := exBind_ok h
  exact ⟨x, z₁, hx, hz, h⟩

theorem walk_append_ok {L : Lay} (l₂ : List (Step W Y)) (d₂ : List Fmt.Drawn) :
    ∀ (l₁ : List (Step W Y)) (d₁ : List Fmt.Drawn) (z z' : ChainProgress S Cl W Y),
    d₁.length = l₁.length → walk L (l₁ ++ l₂) (d₁ ++ d₂) z = .ok z' →
    ∃ z₁, walk L l₁ d₁ z = .ok z₁ ∧ walk L l₂ d₂ z₁ = .ok z'
  | [], [], z, z', _, h => ⟨z, by rw [walk], h⟩
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl
  | s :: l₁, d :: d₁, z, z', hl, h => by
    obtain ⟨x, y, hx, hy, h⟩ := walk_cons_ok (ss := l₁ ++ l₂) (ds := d₁ ++ d₂) h
    obtain ⟨z₁, h1, h2⟩ := walk_append_ok l₂ d₂ l₁ d₁ y z' (by simpa using hl) h
    refine ⟨z₁, ?_, h2⟩
    rw [walk]
    simp only [hx, hy, Except.bind]
    exact h1

/-! ## 3 The asking -/

/-- A sub-protocol whose rounds have not all been produced waits. -/
theorem settle_wait (L : Lay) (b : Block S Cl) (bs : List (Block S Cl)) (z : ChainProgress S Cl W Y)
    (h : z.own.length < b.rounds.length) :
    ChainProgress.settle L (b :: bs) z = .ok { z with todo := b :: bs } := by
  rw [ChainProgress.settle, if_pos h]

/-- A sub-protocol whose rounds have all been produced is asked; where it accepts, the state of the
prover's run takes its columns (`Mid.took`); then the sub-protocols after it. -/
theorem settle_ask_ok {L : Lay} {b : Block S Cl} {bs : List (Block S Cl)} {z z' : ChainProgress S Cl W Y}
    (hn : ¬ z.own.length < b.rounds.length) (h : ChainProgress.settle L (b :: bs) z = .ok z') :
    ∃ cols, fillCols (readsOf L.chain L.firstTree L.stored (L.tree z.laid) b.rounds
        (z.own.map (·.drawn))) [] = .ok cols ∧
      ChainProgress.settle L bs
        { z with
          ver := z.ver.bind fun s => judge L.firstTree b s (roundsOf z.own) cols
          mid := if (z.ver.bind fun s => judge L.firstTree b s (roundsOf z.own) cols).isSome
            then z.mid.map (·.took cols) else none
          refused := z.refused.or
            (if z.ver.isSome &&
                (z.ver.bind fun s => judge L.firstTree b s (roundsOf z.own) cols).isNone
              then some b.place else none)
          reads := z.reads ++ readsOf L.chain L.firstTree L.stored (L.tree z.laid) b.rounds
            (z.own.map (·.drawn))
          cols := z.cols ++ cols, own := [] } = .ok z' := by
  rw [ChainProgress.settle, if_neg hn] at h
  obtain ⟨cols, hc, h⟩ := exBind_ok h
  exact ⟨cols, unfit_ok hc, h⟩

/-- A round's message: `Step.tell`, with no stored round to fall back on, while the prover's run
goes on; otherwise the fixed substitute. -/
def sayAt (m : Option (Mid W Y)) (s : Step W Y) : Except Refusal Told :=
  match m with
  | some a => s.tell none a
  | none => .ok (subTold s.decl s.oracles)

/-- After a round's challenge: `Step.hear` while the prover's run goes on; where nothing more is
played, `none` again. -/
def hearAtO (m : Option (Mid W Y)) (s : Step W Y) (x : Told) (d : Fmt.Drawn) :
    Except Refusal (Option (Mid W Y)) :=
  match m with
  | some a => (s.hear x d a).map some
  | none => .ok none

theorem say_eq (z : ChainProgress S Cl W Y) (s : Step W Y) : z.say s = sayAt z.mid s := by
  unfold ChainProgress.say sayAt
  cases z.mid <;> rfl

theorem heard_ok {L : Lay} {z z' : ChainProgress S Cl W Y} {s : Step W Y} {x : Told} {d : Fmt.Drawn}
    (h : z.heard L s x d = .ok z') :
    ∃ m', hearAtO z.mid s x d = .ok m' ∧
      ChainProgress.settle L z.todo
        { z with
          mid := m'
          laid := z.laid ++ [⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d⟩]
          own := z.own ++ [⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d⟩] } =
        .ok z' := by
  unfold ChainProgress.heard at h
  obtain ⟨m', hm, h⟩ := exBind_ok h
  refine ⟨m', ?_, h⟩
  unfold hearAtO
  cases hz : z.mid with
  | none =>
    rw [hz] at hm
    exact hm
  | some a =>
    rw [hz] at hm
    exact hm

/-! ## 4 Inside one sub-protocol -/

/-- **Rounds' messages and updates, without the asking**: `Step.tell` and `Step.hear` while the
prover's run goes on; each round's fixed substitute where nothing more is played. An error where the
two lists differ in length. Each round is filed under its part's number, whether or not a prover's
side made it. -/
def lays : List (Step W Y) → List Fmt.Drawn → Option (Mid W Y) →
    Except Refusal (List Played × Option (Mid W Y))
  | [], [], m => .ok ([], m)
  | s :: ss, d :: ds, m =>
    (sayAt m s).bind fun x =>
    (hearAtO m s x d).bind fun m' =>
    (lays ss ds m').map fun y =>
      (⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d⟩ :: y.1, y.2)
  | _, _, _ => .error ⟨.unfit, "the challenges are not as many as the rounds"⟩

/-- A walk with rounds appended to what it has produced, for the sub-protocol that is being played,
and with the state of the prover's run after them. -/
def ChainProgress.grown (z : ChainProgress S Cl W Y) (y : List Played × Option (Mid W Y)) : ChainProgress S Cl W Y :=
  { z with mid := y.2, laid := z.laid ++ y.1, own := z.own ++ y.1 }

/-- **Inside one sub-protocol** a walk is the rounds' messages and updates; after the sub-protocol's
last round the asking comes, once. -/
theorem member_ok {L : Lay} {b : Block S Cl} {bs : List (Block S Cl)} :
    ∀ (l : List (Step W Y)) (ds : List Fmt.Drawn) (z z' : ChainProgress S Cl W Y), z.todo = b :: bs →
    z.own.length + l.length = b.rounds.length → l ≠ [] → walk L l ds z = .ok z' →
    ∃ y, lays l ds z.mid = .ok y ∧ ChainProgress.settle L (b :: bs) (z.grown y) = .ok z'
  | [], _, _, _, _, _, hne, _ => absurd rfl hne
  | _ :: _, [], _, _, _, _, _, h => by simp [walk] at h
  | s :: l, d :: ds, z, z', ht, hlen, _, h => by
    obtain ⟨x, z₁, hx, hz, h⟩ := walk_cons_ok h
    obtain ⟨m', hm, hs⟩ := heard_ok hz
    have hx' : sayAt z.mid s = .ok x := (say_eq z s).symm.trans hx
    have hs₀ := hs
    rw [ht] at hs
    cases l with
    | nil =>
      cases ds with
      | cons _ _ => simp [walk] at h
      | nil =>
        have e := walk_nil_ok h
        subst e
        refine ⟨([⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d⟩], m'), ?_, ?_⟩
        · simp only [lays, hx', hm, Except.bind, Except.map]
        · rw [← ht]
          exact hs₀
    | cons s' l' =>
      have hw : (z.own ++ [(⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d⟩ :
          Played)]).length < b.rounds.length := by
        rw [List.length_append, List.length_singleton]
        simp only [List.length_cons] at hlen
        omega
      rw [settle_wait L b bs _ hw] at hs
      have e := Except.ok.inj hs
      subst e
      obtain ⟨y, hy, hs'⟩ := member_ok (s' :: l') ds _ z' rfl (by
        show (z.own ++ [_]).length + (s' :: l').length = b.rounds.length
        rw [List.length_append, List.length_singleton]
        simp only [List.length_cons] at hlen ⊢
        omega) (by simp) h
      refine ⟨(⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d⟩ :: y.1, y.2),
        ?_, ?_⟩
      · have hy' : lays (s' :: l') ds m' = .ok y := hy
        rw [lays]
        simp only [hx', hm, hy', Except.bind, Except.map]
      · refine Eq.trans (congrArg (ChainProgress.settle L (b :: bs)) ?_) hs'
        unfold ChainProgress.grown
        simp only [List.append_assoc, List.singleton_append, ht]

/-! ## 5 What the rounds are -/

/-- **While the prover's run goes on, the rounds are those of `play` with no stored run to fall back
on**: at `Step`s of which one without a move has the part number 0, as `chainSteps` prepares them.
-/
theorem lays_live : ∀ (l : List (Step W Y)) (ds : List Fmt.Drawn) (m : Mid W Y)
    (y : List Played × Option (Mid W Y)),
    (∀ s ∈ l, s.move.isSome = false → s.addr.part = 0) → lays l ds (some m) = .ok y →
    ∃ m', y.2 = some m' ∧ play l ds [] m = .ok (y.1, m')
  | [], [], m, y, _, h => by
    rw [lays] at h
    cases h
    exact ⟨m, rfl, by rw [play]⟩
  | [], _ :: _, _, _, _, h => by simp [lays] at h
  | _ :: _, [], _, _, _, h => by simp [lays] at h
  | s :: l, d :: ds, m, y, hp, h => by
    rw [lays] at h
    obtain ⟨x, hx, h⟩ := exBind_ok h
    obtain ⟨o, ho, h⟩ := exBind_ok h
    obtain ⟨m₁, hm, e⟩ := exMap_ok (a := s.hear x d m) (f := some) ho
    subst e
    obtain ⟨y', hy, e⟩ := exMap_ok h
    subst e
    obtain ⟨m', e1, e2⟩ := lays_live l ds m₁ y' (fun t ht => hp t (List.mem_cons_of_mem _ ht)) hy
    refine ⟨m', e1, ?_⟩
    have hx' : s.tell none m = .ok x := hx
    have hpart : (if x.told then s.addr.part else 0) = s.addr.part := by
      cases ht : x.told with
      | true => rfl
      | false =>
        have := (tell_yields hx').1
        rw [ht] at this
        exact (hp s (List.mem_cons.2 (Or.inl rfl)) this.symm).symm
    rw [play]
    simp only [List.head?_nil, List.tail_nil, hx', hm, e2, Except.bind, Except.map, hpart]

/-- A `Step`'s substitute, as a produced round. -/
def subPlayed (s : Step W Y) (d : Fmt.Drawn) : Played :=
  ⟨s.name, s.addr.place, s.addr.part, false, (subTold s.decl s.oracles).vals,
    (subTold s.decl s.oracles).tables, d⟩

/-- **Where nothing more is played, the rounds are the substitutes.** -/
theorem lays_sub : ∀ (l : List (Step W Y)) (ds : List Fmt.Drawn)
    (y : List Played × Option (Mid W Y)), lays l ds none = .ok y →
    y = ((l.zip ds).map fun u => subPlayed u.1 u.2, none)
  | [], [], y, h => by
    rw [lays] at h
    exact (Except.ok.inj h).symm
  | [], _ :: _, _, h => by simp [lays] at h
  | _ :: _, [], _, h => by simp [lays] at h
  | s :: l, d :: ds, y, h => by
    rw [lays] at h
    obtain ⟨x, hx, h⟩ := exBind_ok h
    obtain ⟨o, ho, h⟩ := exBind_ok h
    have ex : x = subTold s.decl s.oracles := (Except.ok.inj hx).symm
    have eo : o = none := (Except.ok.inj ho).symm
    subst ex
    subst eo
    obtain ⟨y', hy, e⟩ := exMap_ok h
    subst e
    rw [lays_sub l ds y' hy]
    rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.runC_parts
#print axioms ProofFile.Honest.walk_nil_ok
#print axioms ProofFile.Honest.walk_cons_ok
#print axioms ProofFile.Honest.walk_append_ok
#print axioms ProofFile.Honest.settle_wait
#print axioms ProofFile.Honest.settle_ask_ok
#print axioms ProofFile.Honest.say_eq
#print axioms ProofFile.Honest.heard_ok
#print axioms ProofFile.Honest.member_ok
#print axioms ProofFile.Honest.lays_live
#print axioms ProofFile.Honest.lays_sub
#print axioms ProofFile.Honest.sayAt
#print axioms ProofFile.Honest.hearAtO
#print axioms ProofFile.Honest.lays
#print axioms ProofFile.Honest.ChainProgress.grown
#print axioms ProofFile.Honest.subPlayed
