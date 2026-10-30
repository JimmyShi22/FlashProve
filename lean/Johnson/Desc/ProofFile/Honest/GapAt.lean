-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/GapAt.lean: there are two texts for the state of a run before the
part at an address: `midAt` (Honest/Frame.lean), which plays the rounds before it, and `midAtW`
(Honest/MidW.lean), which walks them with the verifier beside the prover and lays the field
`opened`. This file shows that the two states agree but for that field, as long as every step that
is played before the address is blind (`Step.Blind`, Honest/Blind.lean: its move does not depend on
the columns handed to it). No definition.

The reach is narrow. At an address behind the first part that reads the columns handed to it the
hypothesis on the steps is false and the lemmas are silent. Once the parts of the kind K10 that read
the columns are laid, that is the first chain behind the first of them, and all of the second chain,
because `midAt` reaches the second chain through the whole first chain. What is left is the first
chain up to that part, and the shared chain.

  1  `midIn_field`   `midIn` over blind steps from a state with another field
  2  `start_same`   `ChainProgress.start` changes nothing of the prover's state but the field
  3  `sealQuiet_keys`   `sealQuiet` reads three fields of the rounds alone
  4  `walk_play_keys`, `walk_play_seal`   `walk_play` (Honest/GapSame.lean) once more, with what the
     rounds send and draw: the walk's rounds and those of `play` agree in these three fields, and
     `sealQuiet` says the same of both
  5  `midSharedAtW_midSharedAt`   **the two states agree but for the field, at an address of the
     shared chain**
  6  `midAtW_midAt`   **the same at an address of the first or the second chain**

The direction is from the walk to `play`: where `midAtW` returns a state, `midAt` returns one. The
converse is not shown.

Called, of other authors: `heard_laid` (Honest/Law/WalkOn.lean), `start_laid`
(Honest/WalkHeard.lean), `of_bind_ok` and `map_ok` (Honest/WalkOpened.lean).

Limits.
  * The hypotheses on the steps are shown at no prover.
  * For an address of the second chain all steps of the first and of the shared chain have to be
    blind.
  * Nothing here shows that `midAtW` returns a state at any run.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.GapSame
import Johnson.Desc.ProofFile.Honest.WalkHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription OpenedColumn)

variable {S Cl Xi W₀ Rc Ky Tr X₀ X W Y : Type}

/-! ## 1 One chain -/

/-- `midIn` from a state with another field. `hb`: the steps before the address are blind. -/
theorem midIn_field {steps : List (Step W Y)} {a : Addr}
    (hb : ∀ s ∈ steps.take (steps.takeWhile fun s => s.addr != a).length, s.Blind)
    (ds : List Fmt.Drawn) (back : List Fmt.RoundView) (m : Mid W Y) (o : Option (List OpenedColumn)) :
    midIn steps ds back { m with opened := o } a =
      (midIn steps ds back m a).map ({ · with opened := o }) := by
  by_cases hany : (!steps.any (·.addr == a)) = true
  · unfold midIn
    rw [if_pos hany, if_pos hany]
    rfl
  · unfold midIn
    rw [if_neg hany, if_neg hany]
    show (play _ _ back { m with opened := o }).map _ = Except.map _ ((play _ _ back m).map _)
    rw [play_field _ _ back m o hb]
    cases play (steps.take (steps.takeWhile fun s => s.addr != a).length)
      (ds.take (steps.takeWhile fun s => s.addr != a).length) back m <;> rfl

/-- Where `ChainProgress.start` returns with the run still played, it has changed nothing of the prover's
state but the field. -/
theorem start_same {L : Lay} {bs : List (Block S Cl)} {mo : Option (Mid W Y)} {v : Option S}
    {front : List OpenedColumn} {z : ChainProgress S Cl W Y} {m₀ : Mid W Y}
    (h : ChainProgress.start L bs mo v front = .ok z) (h1 : z.mid = some m₀) :
    ∃ m o, mo = some m ∧ m₀ = { m with opened := o } := by
  unfold ChainProgress.start at h
  obtain ⟨m₁, o, hm, rfl⟩ := settle_same L bs _ z m₀ h h1
  have hm' : (if v.isSome then mo.map ({ · with opened := some front }) else none) = some m₁ := hm
  split at hm'
  · cases mo with
    | none => cases hm'
    | some m =>
      obtain rfl : { m with opened := some front } = m₁ := Option.some.inj hm'
      exact ⟨m, o, rfl, rfl⟩
  · cases hm'

/-- `sealQuiet` reads what the rounds send and draw, and nothing else of them. -/
theorem sealQuiet_keys {l l' : List Played}
    (h : l.map (fun p : Played => (p.vals, p.tables, p.drawn)) =
      l'.map (fun p : Played => (p.vals, p.tables, p.drawn))) :
    sealQuiet l = sealQuiet l' := by
  have e : ∀ t : List Played, sealQuiet t =
      (((t.map (fun p : Played => (p.vals, p.tables, p.drawn))).getLast?).map fun k =>
        k.1.isEmpty && k.2.1.isEmpty && k.2.2 == ⟨[], [], [], none⟩).getD false := by
    intro t
    rw [List.getLast?_map, Option.map_map]
    rfl
  rw [e l, e l', h]

/-- `walk_play` with the rounds, under its hypotheses (the steps are blind; the walk returns with
the run still played): what the walk's rounds send and draw is what those of `play` do. -/
theorem walk_play_keys (L : Lay) : ∀ (ss : List (Step W Y)) (ds : List Fmt.Drawn)
    (z z' : ChainProgress S Cl W Y) (m' : Mid W Y), (∀ s ∈ ss, s.Blind) → walk L ss ds z = .ok z' →
    z'.mid = some m' →
    ∃ m₀ y, z.mid = some m₀ ∧ play ss ds [] m₀ = .ok y ∧ m' = { y.2 with opened := m'.opened } ∧
      z'.laid.map (fun p : Played => (p.vals, p.tables, p.drawn)) =
        z.laid.map (fun p : Played => (p.vals, p.tables, p.drawn)) ++
          y.1.map (fun p : Played => (p.vals, p.tables, p.drawn))
  | [], [], z, z', m', _, h, h1 => by
    rw [walk] at h
    obtain rfl := Except.ok.inj h
    exact ⟨m', ([], m'), h1, by rw [play], rfl, (List.append_nil _).symm⟩
  | s :: ss, d :: ds, z, z', m', hb, h, h1 => by
    rw [walk] at h
    obtain ⟨x, hx, h⟩ := of_bind_ok h
    obtain ⟨z₁, hz₁, h⟩ := of_bind_ok h
    obtain ⟨m₁', y', e1, hp, e', ek⟩ :=
      walk_play_keys L ss ds z₁ z' m' (fun t ht => hb t (List.mem_cons_of_mem _ ht)) h h1
    have hl₁ := heard_laid hz₁
    unfold ChainProgress.heard at hz₁
    obtain ⟨mm, hmm, hz₁⟩ := of_bind_ok hz₁
    obtain ⟨m₁, o₁, e2, rfl⟩ := settle_same L _ _ z₁ m₁' hz₁ e1
    have e3 : mm = some m₁ := e2
    subst e3
    cases hzm : z.mid with
    | none =>
      rw [hzm] at hmm
      cases hmm
    | some m₀ =>
      rw [hzm] at hmm
      obtain ⟨m₂, hh, e⟩ := map_ok hmm
      obtain rfl := Option.some.inj e
      have hx' : s.tell none m₀ = .ok x := by
        unfold ChainProgress.say at hx
        rw [hzm] at hx
        exact hx
      rw [play_field ss ds [] m₂ o₁ fun t ht => hb t (List.mem_cons_of_mem _ ht)] at hp
      obtain ⟨y, hy, rfl⟩ := map_ok hp
      refine ⟨m₀, (⟨s.name, s.addr.place, if x.told then s.addr.part else 0, x.told, x.vals,
        x.tables, d⟩ :: y.1, y.2), rfl, ?_, e', ?_⟩
      · rw [play]
        show (s.tell none m₀).bind _ = _
        rw [hx']
        show (s.hear x d m₀).bind _ = _
        rw [hh]
        show (play ss ds [] m₂).map _ = _
        rw [hy]
        rfl
      · rw [ek, hl₁, List.map_append, List.append_assoc]
        rfl
  | [], _ :: _, _, _, _, _, h, _ => by simp [walk] at h
  | _ :: _, [], _, _, _, _, h, _ => by simp [walk] at h

/-- From a walk that sets out with no round laid, under the hypotheses of `walk_play`: `sealQuiet`
says the same of the walk's rounds and of those of `play`. -/
theorem walk_play_seal {L : Lay} {ss : List (Step W Y)} {ds : List Fmt.Drawn}
    {z z' : ChainProgress S Cl W Y} {m' : Mid W Y} (hb : ∀ s ∈ ss, s.Blind) (h : walk L ss ds z = .ok z')
    (h1 : z'.mid = some m') (h0 : z.laid = []) :
    ∃ m₀ y, z.mid = some m₀ ∧ play ss ds [] m₀ = .ok y ∧ m' = { y.2 with opened := m'.opened } ∧
      sealQuiet y.1 = sealQuiet z'.laid := by
  obtain ⟨m₀, y, e0, hp, e', ek⟩ := walk_play_keys L ss ds z z' m' hb h h1
  rw [h0] at ek
  exact ⟨m₀, y, e0, hp, e', sealQuiet_keys ek.symm⟩

/-! ## 2 A run -/

/-- **They agree but for the field, at an address of the shared chain.** `hb`: the shared chain's
steps before the address are blind. `hR`: `ready` returns. `h`: `midSharedAtW` returns a state. -/
theorem midSharedAtW_midSharedAt {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {w₀ : W₀} {rc : Rc} {x : Xi} {c : Coins B} {ρ : Draws} {a : Addr}
    {R : Ready W₀ Rc Xi Ky Tr X₀ X} {m' : Mid (Common W₀ Rc Ky) X₀}
    (hR : ready F B H w₀ rc x c = .ok R)
    (hb : ∀ s ∈ R.shared.take (R.shared.takeWhile fun s => s.addr != a).length, s.Blind)
    (h : midSharedAtW F B H w₀ rc x c ρ a = .ok (some m')) :
    ∃ m, midSharedAt F B H w₀ rc x c ρ a = .ok m ∧ m' = { m with opened := m'.opened } := by
  unfold midSharedAtW at h
  obtain ⟨R', hR', h⟩ := of_bind_ok h
  obtain rfl : R = R' := Except.ok.inj (hR.symm.trans hR')
  obtain ⟨a₂, s2, h⟩ := of_bind_ok h
  obtain ⟨m₀, m, e0, hp, e'⟩ := midInW_midIn hb h
  obtain ⟨ms, o, es, rfl⟩ := start_same s2 e0
  obtain rfl : R.start₂ H = ms := Option.some.inj es
  rw [midIn_field hb ρ.shared [] (R.start₂ H) o] at hp
  obtain ⟨m₂, hm₂, rfl⟩ := map_ok hp
  refine ⟨m₂, ?_, e'⟩
  unfold midSharedAt
  rw [hR]
  exact hm₂

/-- **They agree but for the field, at an address of the first or the second chain.** `hb₁`, for an
address of the first chain: that chain's steps before it are blind. `hb₂`, for another address: all
steps of the first and of the shared chain are blind, and the second chain's before the address.
`hR`: `ready` returns. `h`: `midAtW` returns a state. -/
theorem midAtW_midAt {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {w₀ : W₀} {rc : Rc} {x : Xi} {c : Coins B} {ρ : Draws} {a : Addr}
    {R : Ready W₀ Rc Xi Ky Tr X₀ X} {m' : Mid (Local W₀ Rc Xi Tr) X}
    (hR : ready F B H w₀ rc x c = .ok R)
    (hb₁ : R.first.any (·.addr == a) = true →
      ∀ s ∈ R.first.take (R.first.takeWhile fun s => s.addr != a).length, s.Blind)
    (hb₂ : ¬ R.first.any (·.addr == a) = true →
      (∀ s ∈ R.first, s.Blind) ∧ (∀ s ∈ R.shared, s.Blind) ∧
        ∀ s ∈ R.second.take (R.second.takeWhile fun s => s.addr != a).length, s.Blind)
    (h : midAtW F B H w₀ rc x c ρ a = .ok (some m')) :
    ∃ m, midAt F B H w₀ rc x c ρ a = .ok m ∧ m' = { m with opened := m'.opened } := by
  have hm : midAt F B H w₀ rc x c ρ a =
      if R.first.any (·.addr == a) then midIn R.first ρ.first [] (R.start₁ H) a
      else (R.ends H ρ.first ρ.shared [] []).bind fun (r₁, r₂) =>
        midIn R.second ρ.second [] (R.start₃ H r₁.2 r₂.2) a := by
    unfold midAt
    rw [hR]
    rfl
  unfold midAtW at h
  obtain ⟨R', hR', h⟩ := of_bind_ok h
  obtain rfl : R = R' := Except.ok.inj (hR.symm.trans hR')
  obtain ⟨a₁, s1, h⟩ := of_bind_ok h
  split at h
  · rename_i hany
    obtain ⟨m₀, m, e0, hp, e'⟩ := midInW_midIn (hb₁ hany) h
    obtain ⟨ms, o, es, rfl⟩ := start_same s1 e0
    obtain rfl : R.start₁ H = ms := Option.some.inj es
    rw [midIn_field (hb₁ hany) ρ.first [] (R.start₁ H) o] at hp
    obtain ⟨m₂, hm₂, rfl⟩ := map_ok hp
    refine ⟨m₂, ?_, e'⟩
    rw [hm, if_pos hany]
    exact hm₂
  · rename_i hany
    obtain ⟨hf, hs, h2⟩ := hb₂ hany
    obtain ⟨z₁, w1, h⟩ := of_bind_ok h
    split at h
    · cases h
    · rename_i hq
      obtain ⟨a₂, s2, h⟩ := of_bind_ok h
      obtain ⟨z₂, w2, h⟩ := of_bind_ok h
      obtain ⟨a₃, s3, h⟩ := of_bind_ok h
      obtain ⟨m₀, m, e0, hp, e'⟩ := midInW_midIn h2 h
      obtain ⟨ms, o, es, rfl⟩ := start_same s3 e0
      cases hz₁ : z₁.mid with
      | none =>
        rw [hz₁] at es
        cases es
      | some m₁ =>
        cases hz₂ : z₂.mid with
        | none =>
          rw [hz₁, hz₂] at es
          cases es
        | some m₂ =>
          rw [hz₁, hz₂] at es
          obtain rfl : R.start₃ H m₁ m₂ = ms := Option.some.inj es
          obtain ⟨n₁, y₁, f1, p1, g1, q1⟩ := walk_play_seal hf w1 hz₁ (start_laid s1)
          obtain ⟨t₁, o₁, u1, rfl⟩ := start_same s1 f1
          obtain rfl : R.start₁ H = t₁ := Option.some.inj u1
          rw [play_field R.first ρ.first [] (R.start₁ H) o₁ hf] at p1
          obtain ⟨r₁, k1, rfl⟩ := map_ok p1
          obtain ⟨n₂, y₂, f2, p2, g2⟩ := walk_play _ R.shared ρ.shared a₂ z₂ m₂ hs w2 hz₂
          obtain ⟨t₂, o₂, u2, rfl⟩ := start_same s2 f2
          obtain rfl : R.start₂ H = t₂ := Option.some.inj u2
          rw [play_field R.shared ρ.shared [] (R.start₂ H) o₂ hs] at p2
          obtain ⟨r₂, k2, rfl⟩ := map_ok p2
          have e3 : R.start₃ H m₁ m₂ = R.start₃ H r₁.2 r₂.2 := by
            rw [g1, g2]
            rfl
          rw [e3, midIn_field h2 ρ.second [] (R.start₃ H r₁.2 r₂.2) o] at hp
          obtain ⟨m₃, hm₃, rfl⟩ := map_ok hp
          refine ⟨m₃, ?_, e'⟩
          have hq' : sealQuiet r₁.1 = true := q1.trans (by simpa using hq)
          have he : R.ends H ρ.first ρ.shared [] [] = .ok (r₁, r₂) := by
            unfold Ready.ends
            rw [k1, k2]
            show (sealTest r₁).bind _ = _
            unfold sealTest
            rw [if_neg (by simp [hq'])]
            rfl
          rw [hm, if_neg hany, he]
          exact hm₃

end ProofFile.Honest

#print axioms ProofFile.Honest.midIn_field
#print axioms ProofFile.Honest.start_same
#print axioms ProofFile.Honest.sealQuiet_keys
#print axioms ProofFile.Honest.walk_play_keys
#print axioms ProofFile.Honest.walk_play_seal
#print axioms ProofFile.Honest.midSharedAtW_midSharedAt
#print axioms ProofFile.Honest.midAtW_midAt
