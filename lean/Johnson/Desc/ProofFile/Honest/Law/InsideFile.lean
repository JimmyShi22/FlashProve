-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/InsideFile.lean: the invariant's condition before a called part,
anywhere in its list, at a file. It is `thread_in_chain` (Honest/Law/Inside.lean) in the parameters
of `runC_returns` (Honest/Law/RunsFile.lean). Where a run of `runC` (Honest/Walk.lean) has called
the part at an address before which are the sub-protocols pre and the first i rounds of the next
sub-protocol b: `midAtW` or `midSharedAtW` (Honest/MidW.lean: the walk's own state) returns a state
there; that state is reached by `play` over b's first i rounds from a state at which the invariant
before b holds (`InsideOf`); and what it has seen are the rounds produced before.

What this is. Three conditional lemmas on this folder's own functions, pointwise. None of the
library's goals.

  `thread_in_first`, `thread_in_shared`, `thread_in_second`   the three lemmas

Limits.
  * How many rounds come before the address is a hypothesis (hn).
  * i is less than the number of b's rounds (hi).
  * The invariants at the starts are asked at the states as `ChainProgress.start` (Honest/Walk.lean) lays
    them: the field `opened` is `some []` at the first and the shared chain, and at the second
    chain, where the two ends' fields hold columns, these joined.
  * `PlaysOn` (Honest/Law/ThreadC.lean), at every sub-protocol of the chain (in `thread_in_second`:
    of the three chains), is asked at every state that the invariant allows, at every value of the
    field `opened` too: where a sub-protocol of these has a part that reads the columns and errs at
    `none` (its duty: Honest/Frame.lean, `Seen.opened`), `PlaysOn` at an invariant before it that
    lets `none` through is met only vacuously (there, Limits).
  * Nothing is said of `midAt` and `midSharedAt` (Honest/Frame.lean), which play the rounds by
    `play` and hand no columns.
  * Among the hypotheses that the prose above does not name: `Draws.due` (the challenges are such as
    the description's rounds can draw; the first chain's last challenge is the empty one):
    `thread_in_first`, `thread_in_shared`, `thread_in_second`; `FileDescription.planOk` (the library's
    executable test): `thread_in_first`, `thread_in_shared`, `thread_in_second`; `ready … = .ok`
    (`ready` returns at these coins): `thread_in_first`, `thread_in_shared`, `thread_in_second`;
    `silentAt … = none` (the honest side does not stop at these challenges, or the request has no
    trace): `thread_in_first`, `thread_in_shared`, `thread_in_second`; `PlanServes`
    (Honest/Law/RunsFile.lean): `thread_in_second`; that a `Step` of the chain stands at the address
    (`ha`) and that the rounds at the address are one consecutive stretch (`hseg`; idle:
    Honest/Law/RunMidFile.lean): all three.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Inside
import Johnson.Desc.ProofFile.Honest.Law.RunMidFile
import Johnson.Desc.ProofFile.Honest.Law.RunsFile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-- **The invariant's condition before a called part of the first chain**, i rounds inside its
sub-protocol. -/
theorem thread_in_first {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Tr X₀ X} {r : RunC F}
    (h : runC F Bk H w₀ rc x k ρ = .ok r) (hR : ready F Bk H w₀ rc x k = .ok R)
    (hpl : F.planOk = true) (hρ : ρ.due F = true) (hsil : silentAt F H w₀ rc x ρ = none)
    (I : Nat → Coins Bk → F.S₁ → Mid (Local W₀ Rc Xi Tr) X → Env → Prop)
    (hI : ∀ j b, F.first.blocksInOrder[j]? = some b → PlaysOn .own Bk 0 0 H.first b (I j) (I (j + 1)))
    (a₀ : I 0 k (F.start₁ (F.pub x)) { R.start₁ H with opened := some [] }
      (envOf (H.storedWords w₀ rc) (fun _ _ => none) []))
    {pre : List (Block F.S₁ F.Cl)} {b : Block F.S₁ F.Cl} {t : List (Block F.S₁ F.Cl)}
    (hfl : F.first.blocksInOrder = pre ++ b :: t) (hb0 : 0 < b.rounds.length) (i : Nat)
    (hi : i < b.rounds.length) {a : Addr}
    (ha : R.first.any (·.addr == a) = true)
    (hseg : (R.first.drop (R.first.takeWhile fun s => s.addr != a).length).take
      (R.first.filter fun s => s.addr == a).length = R.first.filter fun s => s.addr == a)
    (hn : (R.first.takeWhile fun s => s.addr != a).length =
      (pre.flatMap (·.rounds)).length + i)
    (hc : r.called a = true) :
    ∃ m, midAtW F Bk H w₀ rc x k ρ a = .ok (some m) ∧
      InsideOf .own Bk 0 H.first b (I pre.length) i k m
        (envOf (H.storedWords w₀ rc) (fun _ _ => none)
          (r.run.played.1.take ((pre.flatMap (·.rounds)).length + i))) ∧
      m.seen = roundsOf (r.run.played.1.take ((pre.flatMap (·.rounds)).length + i)) := by
  have P := (F.planOk_ok).1 hpl
  have hp := P.places
  obtain ⟨-, tr, htr, hown, hcom, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 P.blocks₁
  have o₂ := steps_shaped s2 P.blocks₂
  have o₃ := steps_shaped s3 P.blocks₃
  obtain ⟨l1, l2, l3⟩ := runC_laidAs h hR o₁ o₂ o₃
  obtain ⟨p1, p2, p3⟩ := places_chain hp
  have c1 := steps_chain s1 p1
  have c2 := steps_chain s2 p2
  have c3 := steps_chain s3 p3
  have hA := at_first h hR o₁ o₂ o₃ hp ha
  have hbe := told_behind hA (stretch_of R.first a hseg) hc (fun p hp' hat => by
    rcases List.mem_append.1 hp' with g | g
    · rcases List.mem_append.1 g with g | g
      · exact g
      · rw [all_of_map (laidAs_mask l2 a) (off_chain (by decide) c1 c2 ha) p g] at hat
        cases hat
    · rw [all_of_map (laidAs_mask l3 a) (off_chain (by decide) c1 c3 ha) p g] at hat
      cases hat)
  rw [hn] at hbe
  simp only [Draws.due, Bool.and_eq_true, beq_iff_eq] at hρ
  obtain ⟨⟨⟨d1, d2⟩, d3⟩, -⟩ := hρ
  unfold silentAt at hsil
  rw [htr] at hsil
  have hsil' : (chainStopAt (Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr)) F.first.blocksInOrder
      H.first [] ρ.first).or
      ((chainStopAt (Face.shared.sees (⟨w₀, rc, H.key x⟩ : Common W₀ Rc Ky)) F.shared.blocksInOrder
        H.shared [] ρ.shared).or
        (chainStopAt (Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr)) F.second.blocksInOrder H.second
          ρ.first ρ.second)) = none := hsil
  obtain ⟨t1, t23⟩ := or_none hsil'
  obtain ⟨t2, -⟩ := or_none t23
  rw [← hown] at t1
  rw [← hcom] at t2
  obtain ⟨R', b₁, z₁, b₂, z₂, b₃, z₃, hR', hb, hw, -, -, -, -, -, rfl⟩ := runC_parts h
  rw [hR] at hR'
  cases hR'
  have hbe' : ∃ p ∈ z₁.laid.drop ((pre.flatMap (·.rounds)).length + i), p.told = true := hbe
  have hLo : ∀ ps, treeOwn ps = (envOf (H.storedWords w₀ rc) (fun _ _ => none) ps).tree :=
    fun ps => ((envOf_tree (H.storedWords w₀ rc) ps [] []).1).symm
  have hb' : ChainProgress.start ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ (pre ++ b :: t) (some (R.start₁ H))
      (some (F.start₁ (F.pub x))) [] = .ok b₁ := by
    have e := hb
    rw [hfl] at e
    exact e
  obtain ⟨y, m, w1, q, hIn, hsn⟩ := thread_in_chain (φ := Face.own) (hs := H.first)
    ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ (fun _ _ => none) hLo k (Face.own.sees R.own) pre b t hb0 I
    (fun j c hj => hI j c (by
      rw [hfl, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hj).1]
      exact hj))
    (R.start₁ H) (F.start₁ (F.pub x)) hb' hw (by rw [← hfl]; exact s1) rfl a₀
    (by rw [← hfl]; exact d1) (by rw [← hfl]; exact t1) i hi hbe'
  rw [← hn] at w1
  refine ⟨m, ?_, hIn, ?_⟩
  · unfold midAtW
    simp only [hR, hb, Except.bind]
    rw [if_pos ha]
    exact (midInW_of ha w1).trans (by rw [q])
  · rw [hsn]
    rfl

/-- **The invariant's condition before a called part of the shared chain**, i rounds inside its
sub-protocol. -/
theorem thread_in_shared {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Tr X₀ X} {r : RunC F}
    (h : runC F Bk H w₀ rc x k ρ = .ok r) (hR : ready F Bk H w₀ rc x k = .ok R)
    (hpl : F.planOk = true) (hρ : ρ.due F = true) (hsil : silentAt F H w₀ rc x ρ = none)
    (I : Nat → Coins Bk → F.S₂ → Mid (Common W₀ Rc Ky) X₀ → Env → Prop)
    (hI : ∀ j b, F.shared.blocksInOrder[j]? = some b → PlaysOn .shared Bk 1 0 H.shared b (I j) (I (j + 1)))
    (a₀ : I 0 k (F.start₂ (F.pub x)) { R.start₂ H with opened := some [] }
      (envOf (H.storedWords w₀ rc) (fun _ _ => none) []))
    {pre : List (Block F.S₂ F.Cl)} {b : Block F.S₂ F.Cl} {t : List (Block F.S₂ F.Cl)}
    (hfl : F.shared.blocksInOrder = pre ++ b :: t) (hb0 : 0 < b.rounds.length) (i : Nat)
    (hi : i < b.rounds.length) {a : Addr}
    (ha : R.shared.any (·.addr == a) = true)
    (hseg : (R.shared.drop (R.shared.takeWhile fun s => s.addr != a).length).take
      (R.shared.filter fun s => s.addr == a).length = R.shared.filter fun s => s.addr == a)
    (hn : (R.shared.takeWhile fun s => s.addr != a).length =
      (pre.flatMap (·.rounds)).length + i)
    (hc : r.called a = true) :
    ∃ m, midSharedAtW F Bk H w₀ rc x k ρ a = .ok (some m) ∧
      InsideOf .shared Bk 1 H.shared b (I pre.length) i k m
        (envOf (H.storedWords w₀ rc) (fun _ _ => none)
          (r.run.played.2.1.take ((pre.flatMap (·.rounds)).length + i))) ∧
      m.seen = roundsOf (r.run.played.2.1.take ((pre.flatMap (·.rounds)).length + i)) := by
  have P := (F.planOk_ok).1 hpl
  have hp := P.places
  obtain ⟨-, tr, htr, hown, hcom, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 P.blocks₁
  have o₂ := steps_shaped s2 P.blocks₂
  have o₃ := steps_shaped s3 P.blocks₃
  obtain ⟨l1, l2, l3⟩ := runC_laidAs h hR o₁ o₂ o₃
  obtain ⟨p1, p2, p3⟩ := places_chain hp
  have c1 := steps_chain s1 p1
  have c2 := steps_chain s2 p2
  have c3 := steps_chain s3 p3
  have hA := at_shared h hR o₁ o₂ o₃ hp ha
  have hbe := told_behind hA (stretch_of R.shared a hseg) hc (fun p hp' hat => by
    rcases List.mem_append.1 hp' with g | g
    · rcases List.mem_append.1 g with g | g
      · rw [all_of_map (laidAs_mask l1 a) (off_chain (by decide) c2 c1 ha) p g] at hat
        cases hat
      · exact g
    · rw [all_of_map (laidAs_mask l3 a) (off_chain (by decide) c2 c3 ha) p g] at hat
      cases hat)
  rw [hn] at hbe
  simp only [Draws.due, Bool.and_eq_true, beq_iff_eq] at hρ
  obtain ⟨⟨⟨d1, d2⟩, d3⟩, -⟩ := hρ
  unfold silentAt at hsil
  rw [htr] at hsil
  have hsil' : (chainStopAt (Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr)) F.first.blocksInOrder
      H.first [] ρ.first).or
      ((chainStopAt (Face.shared.sees (⟨w₀, rc, H.key x⟩ : Common W₀ Rc Ky)) F.shared.blocksInOrder
        H.shared [] ρ.shared).or
        (chainStopAt (Face.own.sees (⟨w₀, rc, x, tr⟩ : Local W₀ Rc Xi Tr)) F.second.blocksInOrder H.second
          ρ.first ρ.second)) = none := hsil
  obtain ⟨t1, t23⟩ := or_none hsil'
  obtain ⟨t2, -⟩ := or_none t23
  rw [← hown] at t1
  rw [← hcom] at t2
  obtain ⟨R', b₁, z₁, b₂, z₂, b₃, z₃, hR', -, -, -, hb, hw, -, -, rfl⟩ := runC_parts h
  rw [hR] at hR'
  cases hR'
  have hbe' : ∃ p ∈ z₂.laid.drop ((pre.flatMap (·.rounds)).length + i), p.told = true := hbe
  have hLo : ∀ ps, treeOwn ps = (envOf (H.storedWords w₀ rc) (fun _ _ => none) ps).tree :=
    fun ps => ((envOf_tree (H.storedWords w₀ rc) ps [] []).1).symm
  have hb' : ChainProgress.start ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ (pre ++ b :: t) (some (R.start₂ H))
      (some (F.start₂ (F.pub x))) [] = .ok b₂ := by
    have e := hb
    rw [hfl] at e
    exact e
  obtain ⟨y, m, w1, q, hIn, hsn⟩ := thread_in_chain (φ := Face.shared) (hs := H.shared)
    ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ (fun _ _ => none) hLo k (Face.shared.sees R.common) pre b t
    hb0 I
    (fun j c hj => hI j c (by
      rw [hfl, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hj).1]
      exact hj))
    (R.start₂ H) (F.start₂ (F.pub x)) hb' hw (by rw [← hfl]; exact s2) rfl a₀
    (by rw [← hfl]; exact d2) (by rw [← hfl]; exact t2) i hi hbe'
  rw [← hn] at w1
  refine ⟨m, ?_, hIn, ?_⟩
  · unfold midSharedAtW
    simp only [hR, hb, Except.bind]
    exact (midInW_of ha w1).trans (by rw [q])
  · rw [hsn]
    rfl

/-- **The invariant's condition before a called part of the second chain**, i rounds inside its
sub-protocol. -/
theorem thread_in_second {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Tr X₀ X} {r : RunC F}
    (h : runC F Bk H w₀ rc x k ρ = .ok r) (hR : ready F Bk H w₀ rc x k = .ok R)
    (hpl : F.planOk = true) (hρ : ρ.due F = true) (hsil : silentAt F H w₀ rc x ρ = none)
    (hP : PlanServes H w₀ rc R)
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
      I₃ 0 k s₃ { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) } (envThird E₁ E₂))
    {pre : List (Block F.S₃ F.Cl)} {b : Block F.S₃ F.Cl} {t : List (Block F.S₃ F.Cl)}
    (hfl : F.second.blocksInOrder = pre ++ b :: t) (hb : 0 < b.rounds.length) (i : Nat)
    (hi : i < b.rounds.length) {a : Addr}
    (ha : R.second.any (·.addr == a) = true)
    (hseg : (R.second.drop (R.second.takeWhile fun s => s.addr != a).length).take
      (R.second.filter fun s => s.addr == a).length = R.second.filter fun s => s.addr == a)
    (hn : (R.second.takeWhile fun s => s.addr != a).length =
      (pre.flatMap (·.rounds)).length + i)
    (hc : r.called a = true) :
    ∃ m, midAtW F Bk H w₀ rc x k ρ a = .ok (some m) ∧
      InsideOf .own Bk 2 H.second b (I₃ pre.length) i k m
        (envOf (H.storedWords w₀ rc) (taken₃ r.run.played.1 r.run.played.2.1)
        (r.run.played.2.2.take ((pre.flatMap (·.rounds)).length + i))) ∧
      m.seen = roundsOf r.run.played.1 ++ roundsOf r.run.played.2.1 ++
        roundsOf (r.run.played.2.2.take ((pre.flatMap (·.rounds)).length + i)) := by
  have P := (F.planOk_ok).1 hpl
  have hp := P.places
  obtain ⟨-, tr, htr, hown, hcom, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 P.blocks₁
  have o₂ := steps_shaped s2 P.blocks₂
  have o₃ := steps_shaped s3 P.blocks₃
  obtain ⟨l1, l2, l3⟩ := runC_laidAs h hR o₁ o₂ o₃
  obtain ⟨p1, p2, p3⟩ := places_chain hp
  have c1 := steps_chain s1 p1
  have c2 := steps_chain s2 p2
  have c3 := steps_chain s3 p3
  have hA := at_second h hR o₁ o₂ o₃ hp ha
  have hbe := told_behind hA (stretch_of R.second a hseg) hc (fun p hp' hat => by
    rcases List.mem_append.1 hp' with g | g
    · rcases List.mem_append.1 g with g | g
      · rw [all_of_map (laidAs_mask l1 a) (off_chain (by decide) c3 c1 ha) p g] at hat
        cases hat
      · rw [all_of_map (laidAs_mask l2 a) (off_chain (by decide) c3 c2 ha) p g] at hat
        cases hat
    · exact g)
  rw [hn] at hbe
  have hnot : R.first.any (·.addr == a) = false := by
    rw [List.any_eq_false]
    intro s hs
    rw [off_chain (by decide) c3 c1 ha s hs]
    exact Bool.false_ne_true
  simp only [Draws.due, Bool.and_eq_true, beq_iff_eq] at hρ
  obtain ⟨⟨⟨d1, d2⟩, d3⟩, -⟩ := hρ
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
  obtain ⟨R', b₁, z₁, b₂, z₂, b₃, z₃, hR', hb₁, hw₁, hq, hb₂, hw₂, hb₃, hw₃, rfl⟩ := runC_parts h
  rw [hR] at hR'
  cases hR'
  have hbe' : ∃ p ∈ z₃.laid.drop ((pre.flatMap (·.rounds)).length + i), p.told = true := hbe
  have hLo : ∀ ps, treeOwn ps = (envOf (H.storedWords w₀ rc) (fun _ _ => none) ps).tree :=
    fun ps => ((envOf_tree (H.storedWords w₀ rc) ps [] []).1).symm
  -- the second chain's walk began with the prover's run available
  have hal₃ : b₃.laid = [] := by
    have e := hb₃
    unfold ChainProgress.start at e
    have g := settle_laid _ _ _ b₃ e
    exact g
  have live₃ : b₃.mid.isSome = true := by
    obtain ⟨p, hp', ht⟩ := hbe'
    exact told_live _ _ _ b₃ z₃ z₃.laid hw₃ (by rw [hal₃, List.nil_append])
      ⟨p, List.mem_of_mem_drop hp', ht⟩
  obtain ⟨m₃₀, s₃, em, hdoor⟩ := start_live hb₃ live₃
  have hno : ¬ R.first.any (·.addr == a) = true := by
    rw [hnot]
    exact Bool.false_ne_true
  cases hm₁ : z₁.mid with
  | none =>
    rw [hm₁] at em
    cases em
  | some m₁ =>
  cases hm₂ : z₂.mid with
  | none =>
    rw [hm₁, hm₂] at em
    cases em
  | some m₂ =>
  -- the two earlier chains' ends
  obtain ⟨z₁', X₁, -, e₁c⟩ := chain_returns (φ := Face.own) (hs := H.first)
    ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ (fun _ _ => none) hLo R.first hP.first.inTime
    (served_own 0 0 hP.first hP.own₁) hP.first.shaped hP.first.noRoot hP.first.part0 k
    (Face.own.sees R.own) ρ.first F.first.blocksInOrder I₁ h₁ [] R.first
    ⟨some { R.start₁ H with opened := some [] }, some (F.start₁ (F.pub x)), none, [], [], [],
      F.first.blocksInOrder, []⟩ ρ.first rfl
    rfl tablesFit_nil s1 d1 (Or.inl ⟨_, _, rfl, rfl, rfl, a₁, t1, rfl⟩)
  have E₁ : z₁' = z₁ := by
    have e : ChainProgress.settle ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder
        ⟨some { R.start₁ H with opened := some [] }, some (F.start₁ (F.pub x)), none, [], [], [],
          F.first.blocksInOrder, []⟩ = .ok b₁ := hb₁
    rw [e] at X₁
    have X₁' : walk ⟨0, 0, H.storedWords w₀ rc, treeOwn⟩ R.first ρ.first b₁ = .ok z₁' := X₁
    rw [hw₁] at X₁'
    exact (Except.ok.inj X₁').symm
  subst E₁
  obtain ⟨z₂', X₂, -, e₂c⟩ := chain_returns (φ := Face.shared) (hs := H.shared)
    ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ (fun _ _ => none) hLo R.shared hP.shared.inTime
    (served_own 1 0 hP.shared hP.own₂) hP.shared.shaped hP.shared.noRoot hP.shared.part0 k
    (Face.shared.sees R.common) ρ.shared F.shared.blocksInOrder I₂ h₂ [] R.shared
    ⟨some { R.start₂ H with opened := some [] }, some (F.start₂ (F.pub x)), none, [], [], [],
      F.shared.blocksInOrder, []⟩ ρ.shared
    rfl rfl tablesFit_nil s2 d2 (Or.inl ⟨_, _, rfl, rfl, rfl, a₂, t2, rfl⟩)
  have E₂ : z₂' = z₂ := by
    have e : ChainProgress.settle ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder
        ⟨some { R.start₂ H with opened := some [] }, some (F.start₂ (F.pub x)), none, [], [], [],
          F.shared.blocksInOrder, []⟩ = .ok b₂ := hb₂
    rw [e] at X₂
    have X₂' : walk ⟨1, 0, H.storedWords w₀ rc, treeOwn⟩ R.shared ρ.shared b₂ = .ok z₂' := X₂
    rw [hw₂] at X₂'
    exact (Except.ok.inj X₂').symm
  subst E₂
  rcases e₁c with ⟨e₁, n₁, v1, q1, i1, lc1⟩ | ⟨q1, -⟩
  swap
  · rw [hm₁] at q1
    cases q1
  rcases e₂c with ⟨e₂, n₂, v2, q2, i2, -⟩ | ⟨q2, -⟩
  swap
  · rw [hm₂] at q2
    cases q2
  rw [hm₁] at q1
  rw [hm₂] at q2
  cases q1
  cases q2
  have hs₃ : F.start₃ (F.pub x) e₁ e₂ = .ok s₃ := by
    rw [v1, v2] at hdoor
    have e : (F.start₃ (F.pub x) e₁ e₂).toOption = some s₃ := hdoor
    cases hst : F.start₃ (F.pub x) e₁ e₂ with
    | error w =>
      rw [hst] at e
      cases e
    | ok u =>
      rw [hst] at e
      cases e
      rfl
  have inv₁ : z₁'.Inv [] := walk_inv _ [] _ _ b₁ z₁' (start_inv hb₁) hw₁
  have inv₂ : z₂'.Inv [] := walk_inv _ [] _ _ b₂ z₂' (start_inv hb₂) hw₂
  have i0 := a₃ _ _ _ _ _ _ s₃ z₁'.cols z₂'.cols i1 i2 hs₃ (inv₁ m₁ hm₁) (inv₂ m₂ hm₂)
  rw [envThird_eq] at i0
  have hL₃ : ∀ ps, treeThird z₁'.laid z₂'.laid ps =
      (envOf (H.storedWords w₀ rc) (taken₃ z₁'.laid z₂'.laid) ps).tree :=
    fun ps => ((envOf_tree (H.storedWords w₀ rc) z₁'.laid z₂'.laid ps).2).symm
  have hb₃' : ChainProgress.start ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁'.laid z₂'.laid⟩
      (pre ++ b :: t) (some (R.start₃ H m₁ m₂)) (some s₃) (z₁'.cols ++ z₂'.cols) = .ok b₃ := by
    have e := hb₃
    rw [hm₁, hm₂, hdoor, hfl] at e
    exact e
  obtain ⟨y, m, w1, q, hI, hsn⟩ := thread_in_chain (φ := Face.own) (hs := H.second)
    ⟨2, F.lastChainFirstTreeNumber, H.storedWords w₀ rc, treeThird z₁'.laid z₂'.laid⟩
    (taken₃ z₁'.laid z₂'.laid) hL₃ k (Face.own.sees R.own) pre b t hb I₃
    (fun j c hj => h₃ j c (by
      rw [hfl, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hj).1]
      exact hj))
    (R.start₃ H m₁ m₂) s₃ hb₃' hw₃ (by rw [← hfl]; exact s3) rfl i0
    (by rw [← hfl]; exact d3)
    (by
      rw [← hfl]
      show chainStopAt (Face.own.sees R.own) F.second.blocksInOrder H.second m₁.loc ρ.second = none
      rw [lc1]
      exact t3)
    i hi hbe'
  have q1' := (walk_mid hb₁ hw₁ hm₁).2.2
  have q2' := (walk_mid hb₂ hw₂ hm₂).2.2
  rw [← hn] at w1
  refine ⟨m, ?_, hI, ?_⟩
  · unfold midAtW
    simp only [hR, hb₁, Except.bind]
    rw [if_neg hno]
    simp only [hw₁, hq, hb₂, hw₂, hb₃, Bool.not_true, Bool.false_eq_true, if_false]
    exact (midInW_of ha w1).trans (by rw [q])
  · rw [hsn]
    show (m₁.seen ++ m₂.seen) ++ _ = _
    rw [q1', q2']
    rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.thread_in_first
#print axioms ProofFile.Honest.thread_in_shared
#print axioms ProofFile.Honest.thread_in_second
