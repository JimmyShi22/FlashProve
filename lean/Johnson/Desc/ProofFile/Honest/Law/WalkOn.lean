-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/WalkOn.lean: the walk of Honest/Walk.lean, read forwards:
equations that go from what the rounds of one sub-protocol return to what the walk does. Its
counterpart is Honest/Law/Rule/WalkLaw.lean, which reads a walk that has returned backwards
(`member_ok`, `lays_live`, `lays_sub`); this file uses its terms (`lays`, `ChainProgress.grown`,
`subPlayed`).

  1  `heard_eq`, `settle_ask`, `bind_ok_id`   the walk's two functions, unfolded; `settle_ask`:
     where the sub-protocol accepts, the state of the prover's run takes its columns (`Mid.took`)
  2  `member_on`   inside one sub-protocol the walk is `lays`, then one `ChainProgress.settle`
  3  `lays_of_play`, `lays_none`   where `play` returns with no stored run to fall back on, and a
     round without a move is under the part 0, `lays` returns the same; after a rejection it is the
     substitutes, whenever the challenges are as many as the rounds
  4  `sub_items`, `say_fits`   what a round sends, a prover's side's message or the fixed
     substitute, has the shape that the sub-protocol declares, if a prover's side is defined at the
     round or it declares no item except roots, and it declares as many oracle messages as its entry
     counts roots; `settle_laid`, `heard_laid`: what a round adds to the rounds produced

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.WalkLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl W Y : Type}

/-! ## 1 The walk's two functions -/

theorem heard_eq (L : Lay) (z : ChainProgress S Cl W Y) (s : Step W Y) (x : Told) (d : Fmt.Drawn) :
    z.heard L s x d = (hearAtO z.mid s x d).bind fun m' =>
      ChainProgress.settle L z.todo
        { z with
          mid := m'
          laid := z.laid ++ [⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d⟩]
          own := z.own ++ [⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d⟩] } :=
  rfl

theorem settle_ask (L : Lay) (b : Block S Cl) (bs : List (Block S Cl)) (z : ChainProgress S Cl W Y)
    (hn : ¬ z.own.length < b.rounds.length) :
    ChainProgress.settle L (b :: bs) z =
      (unfit (fillCols (readsOf L.chain L.firstTree L.stored (L.tree z.laid) b.rounds
        (z.own.map (·.drawn))) [])).bind fun cols =>
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
          cols := z.cols ++ cols, own := [] } := by
  conv_lhs => unfold ChainProgress.settle
  rw [if_neg hn]

theorem bind_ok_id {ε α : Type} (a : Except ε α) : (a.bind fun z => .ok z) = a := by
  cases a <;> rfl

/-! ## 2 Inside one sub-protocol -/

/-- **Inside one sub-protocol the walk is `lays`, then one `ChainProgress.settle`.** -/
theorem member_on {L : Lay} {b : Block S Cl} {bs : List (Block S Cl)} :
    ∀ (l : List (Step W Y)) (ds : List Fmt.Drawn) (z : ChainProgress S Cl W Y)
      (y : List Played × Option (Mid W Y)), z.todo = b :: bs →
    z.own.length + l.length = b.rounds.length → l ≠ [] → lays l ds z.mid = .ok y →
    walk L l ds z = ChainProgress.settle L (b :: bs) (z.grown y)
  | [], _, _, _, _, _, h, _ => absurd rfl h
  | _ :: _, [], _, _, _, _, _, h => by simp [lays] at h
  | s :: l, d :: ds, z, y, ht, hn, _, hy => by
    obtain ⟨mid, ver, refused, laid, reads, cols, todo, own⟩ := z
    have ht' : todo = b :: bs := ht
    subst ht'
    simp only [lays] at hy
    obtain ⟨x, hx, hy⟩ := exBind_ok hy
    obtain ⟨m', hm, hy⟩ := exBind_ok hy
    obtain ⟨y', hy', rfl⟩ := exMap_ok hy
    simp only [walk]
    rw [say_eq, hx]
    show ((ChainProgress.heard L ⟨mid, ver, refused, laid, reads, cols, b :: bs, own⟩ s x d).bind
      fun z' => walk L l ds z') = _
    rw [heard_eq, hm]
    show ((ChainProgress.settle L (b :: bs) ⟨m', ver, refused,
               laid ++ [⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d⟩], reads, cols,
               b :: bs, own ++ [⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d⟩]⟩).bind
        fun z' => walk L l ds z') = _
    cases l with
    | nil =>
      cases ds with
      | cons _ _ => simp [lays] at hy'
      | nil =>
        simp only [lays] at hy'
        cases hy'
        have e : (fun z' : ChainProgress S Cl W Y => walk L [] [] z') = fun z' => .ok z' := by
          funext z'
          simp only [walk]
        rw [e, bind_ok_id]
        rfl
    | cons s' l' =>
      have hn' : own.length + (l'.length + 1 + 1) = b.rounds.length := hn
      rw [settle_wait L b bs _ (by
        show (own ++ [_]).length < b.rounds.length
        rw [List.length_append]
        show own.length + 1 < b.rounds.length
        omega)]
      show walk L (s' :: l') ds ⟨m', ver, refused,
        laid ++ [⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d⟩], reads, cols,
        b :: bs, own ++ [⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d⟩]⟩ = _
      rw [member_on (s' :: l') ds _ y' rfl (by
        show (own ++ [_]).length + (l'.length + 1) = b.rounds.length
        rw [List.length_append]
        show own.length + 1 + (l'.length + 1) = b.rounds.length
        omega) (by simp) hy']
      refine congrArg (ChainProgress.settle L (b :: bs)) ?_
      unfold ChainProgress.grown
      simp only [List.append_assoc, List.singleton_append]

/-! ## 3 What `lays` returns -/

theorem lays_of_play : ∀ (l : List (Step W Y)) (ds : List Fmt.Drawn) (m : Mid W Y)
    (y : List Played × Mid W Y), (∀ s ∈ l, s.move.isSome = false → s.addr.part = 0) →
    play l ds [] m = .ok y → lays l ds (some m) = .ok (y.1, some y.2)
  | [], [], m, y, _, h => by
    simp only [play] at h
    cases h
    rfl
  | [], _ :: _, _, _, _, h => by simp [play] at h
  | _ :: _, [], _, _, _, h => by simp [play] at h
  | s :: l, d :: ds, m, y, hp, h => by
    obtain ⟨x, m', z, hx, hm, hz, rfl⟩ := play_cons_ok h
    have ih := lays_of_play l ds m' z (fun s' hs' => hp s' (List.mem_cons_of_mem _ hs')) hz
    have hx' : sayAt (some m) s = .ok x := hx
    have hm' : hearAtO (some m) s x d = .ok (some m') := by
      show (s.hear x d m).map some = _
      rw [hm]
      rfl
    have hpart : (if x.told then s.addr.part else 0) = s.addr.part := by
      have ht := (tell_yields hx).1
      cases hmv : s.move.isSome with
      | true =>
        rw [ht, hmv]
        rfl
      | false =>
        rw [ht, hmv, hp s List.mem_cons_self hmv]
        rfl
    simp only [lays]
    rw [hx']
    show ((hearAtO (some m) s x d).bind fun m'' => (lays l ds m'').map _) = _
    rw [hm']
    show (lays l ds (some m')).map _ = _
    rw [ih, hpart]
    rfl

/-- After a rejection the substitutes are produced, whenever the challenges are as many as the
rounds. -/
theorem lays_none : ∀ (l : List (Step W Y)) (ds : List Fmt.Drawn), ds.length = l.length →
    lays l ds none = .ok ((l.zip ds).map fun u => subPlayed u.1 u.2, none)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | s :: l, d :: ds, h => by
    have ih := lays_none l ds (Nat.succ.inj h)
    simp only [lays]
    show ((lays l ds none).map fun y =>
      ((⟨s.name, s.addr.place, s.addr.part, (subTold s.decl s.oracles).told,
        (subTold s.decl s.oracles).vals, (subTold s.decl s.oracles).tables, d⟩ : Played) :: y.1,
        y.2)) = _
    rw [ih]
    rfl

/-! ## 4 What a round sends has the declared shape; what is produced -/

theorem sub_items : ∀ l : List Fmt.Item,
    ((l.flatMap subSaid).map Said.got).map itemOf = l.filter (· != .root)
  | [] => rfl
  | i :: l => by
    rw [List.flatMap_cons, List.map_append, List.map_append, sub_items l]
    cases i <;> rfl

theorem say_fits {z : ChainProgress S Cl W Y} {s : Step W Y} {x : Told} (h : z.say s = .ok x)
    (hi : s.move.isSome = true ∨
      ([] : List Fmt.ItemValue).map itemOf = s.decl.items.filter (· != .root))
    (ho : s.oracles.length = s.decl.entry.roots) :
    x.vals.map itemOf = s.decl.items.filter (· != .root) ∧ x.tables.length = s.oracles.length ∧
      ∀ (n : Nat) (t : Table), x.tables[n]? = some (some t) →
        (s.oracles.map fun o => (o.logLength, o.words))[n]? = some (t.logLength, t.words) := by
  rw [say_eq] at h
  cases hm : z.mid with
  | some m =>
    rw [hm] at h
    have h' : s.tell none m = .ok x := h
    obtain ⟨-, h1, h2⟩ := tell_yields h'
    cases hmv : s.move.isSome with
    | true =>
      obtain ⟨u, hu, hv, ht⟩ := h1 hmv
      simp only [Sending.fits, Bool.and_eq_true, beq_iff_eq] at hu
      refine ⟨by rw [hv, List.map_map]; exact hu.1, ?_, ?_⟩
      · have e := congrArg List.length hu.2
        rw [List.length_map, List.length_map] at e
        rw [ht, List.length_map, e]
      · intro n t hn
        rw [ht, List.getElem?_map] at hn
        rw [← hu.2, List.getElem?_map]
        cases hu' : u.tables[n]? with
        | none =>
          rw [hu'] at hn
          cases hn
        | some t' =>
          rw [hu'] at hn
          cases hn
          rfl
    | false =>
      obtain ⟨hv, ht⟩ := h2 hmv
      have hv' : x.vals = [] := hv
      refine ⟨?_, by rw [ht, List.length_replicate, ho], ?_⟩
      · rcases hi with h3 | h3
        · rw [hmv] at h3
          cases h3
        · rw [hv']
          exact h3
      · intro n t hn
        rw [ht] at hn
        have h4 := List.mem_of_getElem? hn
        have h5 := (List.mem_replicate.1 h4).2
        cases h5
  | none =>
    rw [hm] at h
    have h' : (Except.ok (subTold s.decl s.oracles) : Except Refusal Told) = .ok x := h
    cases h'
    refine ⟨sub_items _, ?_, ?_⟩
    · show ((s.oracles.map substituteZeroTable).map some).length = _
      rw [List.length_map, List.length_map]
    · intro n t hn
      have hn' : ((s.oracles.map substituteZeroTable).map some)[n]? = some (some t) := hn
      rw [List.getElem?_map, List.getElem?_map] at hn'
      rw [List.getElem?_map]
      cases ho' : s.oracles[n]? with
      | none =>
        rw [ho'] at hn'
        cases hn'
      | some o =>
        rw [ho'] at hn'
        cases hn'
        rfl

theorem settle_laid (L : Lay) : ∀ (todo : List (Block S Cl)) (z z' : ChainProgress S Cl W Y),
    ChainProgress.settle L todo z = .ok z' → z'.laid = z.laid
  | [], z, z', hs => by
    simp only [ChainProgress.settle] at hs
    cases hs
    rfl
  | b :: t, z, z', hs => by
    by_cases hlt : z.own.length < b.rounds.length
    · rw [settle_wait L b t z hlt] at hs
      cases hs
      rfl
    · obtain ⟨cols, -, hs'⟩ := settle_ask_ok hlt hs
      have g := settle_laid L t _ z' hs'
      exact g

theorem heard_laid {L : Lay} {z z' : ChainProgress S Cl W Y} {s : Step W Y} {x : Told} {d : Fmt.Drawn}
    (h : z.heard L s x d = .ok z') :
    z'.laid = z.laid ++ [⟨s.name, s.addr.place, s.addr.part, x.told, x.vals, x.tables, d⟩] := by
  obtain ⟨m', -, hs⟩ := heard_ok h
  exact settle_laid L z.todo _ z' hs

end ProofFile.Honest

#print axioms ProofFile.Honest.heard_eq
#print axioms ProofFile.Honest.settle_ask
#print axioms ProofFile.Honest.bind_ok_id
#print axioms ProofFile.Honest.member_on
#print axioms ProofFile.Honest.lays_of_play
#print axioms ProofFile.Honest.lays_none
#print axioms ProofFile.Honest.sub_items
#print axioms ProofFile.Honest.say_fits
#print axioms ProofFile.Honest.settle_laid
#print axioms ProofFile.Honest.heard_laid
