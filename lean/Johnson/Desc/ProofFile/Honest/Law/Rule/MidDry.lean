-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/MidDry.lean: where `midAtW` or `midSharedAtW`
(Honest/MidW.lean: the walk's own state before a part) returns a state, the state and the challenges
of what it returns are those of the dry fold (Honest/Law/Rule/Real.lean: `dryAt`, `dryEnd`): they
are computed from the rounds' keys, the challenges and the chains' starts alone (`midDry_first`,
`midDry_shared`, `midDry_second`). The proofs go by unfolding, `walk_dry` and `midInW_dry`. It is
the fourteenth piece of the proof of `rowOk_of` (Honest/Law/Rule/Bridge.lean: from `Owed` to
`RowOk`).

  1  `walk_dry`, `midInW_dry`   one chain's walk
  2  `midDry_first`, `midDry_shared`, `midDry_second`   a file

Limits.
  * Nothing is said on the field `opened` of the state returned, which the dry fold does not hold.
  * Of `midAt` and `midSharedAt` (Honest/Frame.lean) nothing is said here.
  * Hypotheses that the prose above does not name: `ready … = .ok` (`ready` returns at these coins):
    `midDry_first`, `midDry_shared`, `midDry_second`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Real
import Johnson.Desc.ProofFile.Honest.Law.Run
import Johnson.Desc.ProofFile.Honest.GapAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription)

/-! ## 1 One chain's walk -/

section
variable {S Cl W Y : Type}

/-- **After a walk that still holds the prover's run**: the state is the fold's; the challenges that
the stops may read are the earlier ones and the walk's own. The like of `play_dry`
(Honest/Law/Rule/Dry.lean); no hypothesis on the steps. -/
theorem walk_dry (L : Lay) : ∀ (ss : List (Step W Y)) (ds : List Fmt.Drawn)
    (z z' : ChainProgress S Cl W Y) (m' : Mid W Y), walk L ss ds z = .ok z' → z'.mid = some m' →
    ∃ m, z.mid = some m ∧ m'.st = dryFold (ss.map Step.hand) ds m.st ∧ m'.loc = m.loc ++ ds
  | [], [], z, z', m', h, h1 => by
    rw [walk] at h
    obtain rfl := Except.ok.inj h
    exact ⟨m', h1, rfl, (List.append_nil _).symm⟩
  | s :: ss, d :: ds, z, z', m', h, h1 => by
    rw [walk] at h
    obtain ⟨x, -, h⟩ := of_bind_ok h
    obtain ⟨z₁, hz₁, h⟩ := of_bind_ok h
    obtain ⟨m₁', e1, b1, b2⟩ := walk_dry L ss ds z₁ z' m' h h1
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
      obtain ⟨a1, a2⟩ := hear_dry hh
      refine ⟨m₀, rfl, ?_, ?_⟩
      · show m'.st = dryFold (s.hand :: ss.map Step.hand) (d :: ds) m₀.st
        rw [b1]
        show dryFold (ss.map Step.hand) ds m₂.st = _
        rw [a1]
        rfl
      · rw [b2]
        show m₂.loc ++ ds = m₀.loc ++ d :: ds
        rw [a2, List.append_assoc]
        rfl
  | [], _ :: _, _, _, _, h, _ => by simp [walk] at h
  | _ :: _, [], _, _, _, h, _ => by simp [walk] at h

/-- **The state of a chain's walk before the part at an address**: state and challenges are computed
from the rounds' keys, the challenges and the walk's first state alone. The like of `midIn_dry`
(Honest/Law/Rule/Dry.lean). -/
theorem midInW_dry {L : Lay} {ss : List (Step W Y)} {ds : List Fmt.Drawn} {z : ChainProgress S Cl W Y}
    {m' : Mid W Y} {a : Addr} (h : midInW L ss ds z a = .ok (some m')) :
    ∃ m, z.mid = some m ∧
      m'.st = dryFold (((ss.map Step.key).take
        ((ss.map Step.key).takeWhile fun y => y.1 != a).length).map (·.2))
        (ds.take ((ss.map Step.key).takeWhile fun y => y.1 != a).length) m.st ∧
      m'.loc = m.loc ++ ds.take ((ss.map Step.key).takeWhile fun y => y.1 != a).length := by
  unfold midInW at h
  split at h
  · cases h
  · obtain ⟨z', hw, e0⟩ := map_ok h
    obtain ⟨m, hm, e1, e2⟩ := walk_dry L _ _ z z' m' hw e0
    rw [takeWhile_key a ss] at e1 e2
    have e : ∀ n : Nat, ((ss.map Step.key).take n).map (·.2) = (ss.take n).map Step.hand := by
      intro n
      simp [List.map_take, List.map_map, Function.comp_def, Step.key]
    exact ⟨m, hm, by rw [e1, e], e2⟩

end

/-! ## 2 A file -/

variable {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {B : ProverCoinCounts}
  {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi} {c : Coins B} {ρ : Draws}
  {R : Ready W₀ Rc Xi Ky Tr X₀ X}

theorem midDry_first (hR : ready F B H w₀ rc x c = .ok R) {a : Addr}
    (ha : R.first.any (·.addr == a) = true) {m : Mid (Local W₀ Rc Xi Tr) X}
    (h : midAtW F B H w₀ rc x c ρ a = .ok (some m)) :
    m.st = (dryAt (R.first.map Step.key) ρ.first (R.start₁ H) a).st ∧
      m.loc = (dryAt (R.first.map Step.key) ρ.first (R.start₁ H) a).loc := by
  unfold midAtW at h
  obtain ⟨R', hR', h⟩ := of_bind_ok h
  obtain rfl : R = R' := Except.ok.inj (hR.symm.trans hR')
  obtain ⟨a₁, s1, h⟩ := of_bind_ok h
  split at h
  · obtain ⟨m₀, e0, e1, e2⟩ := midInW_dry h
    obtain ⟨ms, o, es, rfl⟩ := start_same s1 e0
    obtain rfl : R.start₁ H = ms := Option.some.inj es
    exact ⟨e1, e2⟩
  · rename_i hany
    exact absurd ha hany

theorem midDry_shared (hR : ready F B H w₀ rc x c = .ok R) {a : Addr}
    {m : Mid (Common W₀ Rc Ky) X₀} (h : midSharedAtW F B H w₀ rc x c ρ a = .ok (some m)) :
    m.st = (dryAt (R.shared.map Step.key) ρ.shared (R.start₂ H) a).st ∧
      m.loc = (dryAt (R.shared.map Step.key) ρ.shared (R.start₂ H) a).loc := by
  unfold midSharedAtW at h
  obtain ⟨R', hR', h⟩ := of_bind_ok h
  obtain rfl : R = R' := Except.ok.inj (hR.symm.trans hR')
  obtain ⟨a₂, s2, h⟩ := of_bind_ok h
  obtain ⟨m₀, e0, e1, e2⟩ := midInW_dry h
  obtain ⟨ms, o, es, rfl⟩ := start_same s2 e0
  obtain rfl : R.start₂ H = ms := Option.some.inj es
  exact ⟨e1, e2⟩

theorem midDry_second (hR : ready F B H w₀ rc x c = .ok R) {a : Addr}
    (ha : R.first.any (·.addr == a) = false) {m : Mid (Local W₀ Rc Xi Tr) X}
    (h : midAtW F B H w₀ rc x c ρ a = .ok (some m)) :
    m.st = (dryAt (R.second.map Step.key) ρ.second
        ⟨⟨R.own, (dryEnd (R.first.map Step.key) ρ.first (R.start₁ H)).st.heard ++
            (dryEnd (R.shared.map Step.key) ρ.shared (R.start₂ H)).st.heard,
          H.meet (dryEnd (R.first.map Step.key) ρ.first (R.start₁ H)).st.own
            (dryEnd (R.shared.map Step.key) ρ.shared (R.start₂ H)).st⟩,
          (dryEnd (R.first.map Step.key) ρ.first (R.start₁ H)).loc, [], none⟩ a).st ∧
      m.loc = (dryAt (R.second.map Step.key) ρ.second
        ⟨⟨R.own, (dryEnd (R.first.map Step.key) ρ.first (R.start₁ H)).st.heard ++
            (dryEnd (R.shared.map Step.key) ρ.shared (R.start₂ H)).st.heard,
          H.meet (dryEnd (R.first.map Step.key) ρ.first (R.start₁ H)).st.own
            (dryEnd (R.shared.map Step.key) ρ.shared (R.start₂ H)).st⟩,
          (dryEnd (R.first.map Step.key) ρ.first (R.start₁ H)).loc, [], none⟩ a).loc := by
  have hn : ¬ (R.first.any (·.addr == a) = true) := by
    rw [ha]
    exact Bool.false_ne_true
  unfold midAtW at h
  obtain ⟨R', hR', h⟩ := of_bind_ok h
  obtain rfl : R = R' := Except.ok.inj (hR.symm.trans hR')
  obtain ⟨a₁, s1, h⟩ := of_bind_ok h
  split at h
  · rename_i hany
    exact absurd hany hn
  · obtain ⟨z₁, w1, h⟩ := of_bind_ok h
    split at h
    · cases h
    · obtain ⟨a₂, s2, h⟩ := of_bind_ok h
      obtain ⟨z₂, w2, h⟩ := of_bind_ok h
      obtain ⟨a₃, s3, h⟩ := of_bind_ok h
      obtain ⟨m₀, e0, c1, c2⟩ := midInW_dry h
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
          obtain ⟨n₁, f1, a1, a2⟩ := walk_dry _ R.first ρ.first a₁ z₁ m₁ w1 hz₁
          obtain ⟨t₁, o₁, u1, rfl⟩ := start_same s1 f1
          obtain rfl : R.start₁ H = t₁ := Option.some.inj u1
          obtain ⟨n₂, f2, b1, -⟩ := walk_dry _ R.shared ρ.shared a₂ z₂ m₂ w2 hz₂
          obtain ⟨t₂, o₂, u2, rfl⟩ := start_same s2 f2
          obtain rfl : R.start₂ H = t₂ := Option.some.inj u2
          have k1 : R.first.map Step.hand = (R.first.map Step.key).map (·.2) := by
            rw [List.map_map]
            rfl
          have k2 : R.shared.map Step.hand = (R.shared.map Step.key).map (·.2) := by
            rw [List.map_map]
            rfl
          have e1 : m₁.st = (dryEnd (R.first.map Step.key) ρ.first (R.start₁ H)).st := by
            rw [a1, k1]
            rfl
          have e2 : m₂.st = (dryEnd (R.shared.map Step.key) ρ.shared (R.start₂ H)).st := by
            rw [b1, k2]
            rfl
          have e3 : m₁.loc = (dryEnd (R.first.map Step.key) ρ.first (R.start₁ H)).loc := a2
          have s1' : (R.start₃ H m₁ m₂).st =
              ⟨R.own, (dryEnd (R.first.map Step.key) ρ.first (R.start₁ H)).st.heard ++
                  (dryEnd (R.shared.map Step.key) ρ.shared (R.start₂ H)).st.heard,
                H.meet (dryEnd (R.first.map Step.key) ρ.first (R.start₁ H)).st.own
                  (dryEnd (R.shared.map Step.key) ρ.shared (R.start₂ H)).st⟩ := by
            rw [← e1, ← e2]
            rfl
          have s2' : (R.start₃ H m₁ m₂).loc =
              (dryEnd (R.first.map Step.key) ρ.first (R.start₁ H)).loc := e3
          have c1' : m.st = dryFold (((R.second.map Step.key).take
              ((R.second.map Step.key).takeWhile fun y => y.1 != a).length).map (·.2))
              (ρ.second.take ((R.second.map Step.key).takeWhile fun y => y.1 != a).length)
              (R.start₃ H m₁ m₂).st := c1
          have c2' : m.loc = (R.start₃ H m₁ m₂).loc ++
              ρ.second.take ((R.second.map Step.key).takeWhile fun y => y.1 != a).length := c2
          rw [s1'] at c1'
          rw [s2'] at c2'
          exact ⟨c1', c2'⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.walk_dry
#print axioms ProofFile.Honest.midInW_dry
#print axioms ProofFile.Honest.midDry_first
#print axioms ProofFile.Honest.midDry_shared
#print axioms ProofFile.Honest.midDry_second
