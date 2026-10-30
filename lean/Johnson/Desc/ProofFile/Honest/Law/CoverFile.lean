-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverFile.lean: THE CANONICAL COVER, AT A FILE. At one input and
one run's coins: the three lists of canonical gates (Honest/Law/CoverChain.lean), one over each
chain's data, COVER the typed verifier's messages at which the honest run meets a fall (`fallAt`,
Honest/Fall.lean): so the premise «cover» of `falls_held` (Honest/Law/SharesFalls.lean) is paid
once, for all falls and marks, and what is left is `GatesHeld` AT GATES WHOSE TESTS WALK THE FRONTS:
it is brought down to bounds a member in Honest/Law/CoverHeld.lean.

WHAT THIS IS. Definitions, and conditional lemmas on our own fold and the library's own measure
(`Iop.prRho`), at one input and one run's coins. None of the library's goals.

HOW THE THREE CHAINS' WALKS START. As in `runC`'s own text (Honest/Walk.lean): the first two from
the description's starts; the third from the first two chains' ends: so its gates are handed the
first two chains' typed challenges as their front, and walk these two chains anew. The first chain's
sealing round has no typed message: its fixed empty challenge is the first list's tail. The columns
go as in `runC` too: the first two walks start with no column opened (`[]`), the third is handed the
first two chains' columns.

MET FOR NOTHING. A number of 1 somewhere. A fall whose test always speaks is held by 1 alone. Where
the run does not return `fallAt` says nothing: such messages are not counted here.

  0  `fellBy_ok`   `fellBy`, where the walk over the front returns
  1  `noDraw`, `at₁`, `at₂`, `at₃`   what the three chains' walks start from
  2  `views_fall`   where three views of a run meet a fall: in which chain
  3  `falls_cover`, `falls_held_canon`   the law

Limits. No local bound is shown. At one input and one run's coins: see the Limits of
Honest/Law/SharesFalls.lean. `StopsFit` is taken whole; of it the three counts alone are spent.
Among the hypotheses that the prose above does not name: `ready … = .ok` (`ready` returns at these
coins): `falls_cover`, `falls_held_canon`; that `pre₁` is not empty: `falls_cover`,
`falls_held_canon`. This file proves nothing about soundness, completeness, hiding or any other
property of the protocol.
-/
import Johnson.Desc.RunLaws
import Johnson.Desc.ProofFile.Honest.Law.CoverChain
import Johnson.Desc.ProofFile.Honest.Law.SharesFalls
import Johnson.Desc.ProofFile.Honest.Law.SharesStops

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (RDT WholeD uLT drawnT chainsOf)
open _root_.Run.PQ (CK)

variable {Xi W₀ Rc Ky Tr X₀ X TF TJ T3 : Type}

/-! ## 0 `fellBy`, where the walk over the front returns -/

theorem fellBy_ok {S Cl W Y : Type} (bs : List (Block S Cl)) (fs : List (Fall S))
    {X : ChainAt S Cl W Y} {a z : ChainProgress S Cl W Y} {s : S} {n : Nat} {dr : List Fmt.Drawn}
    (hs : X.start = some a) (h0 : X.s₀ = some s)
    (hw : walk X.lay (X.steps.take n) (dr.take n) a = .ok z) :
    fellBy bs fs X n dr =
      (chainFall fs X.lay.firstTree bs s ⟨roundsOf z.laid, z.cols⟩).isSome := by
  unfold fellBy
  rw [hs, h0]
  simp only
  rw [hw]

/-! ## 1 What the three chains' walks start from -/

/-- The sealing round's fixed, empty challenge. -/
abbrev noDraw : Fmt.Drawn := ⟨[], [], [], none⟩

section
variable (F : FileDescription Xi) (P : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi)
  (R : Ready W₀ Rc Xi Ky Tr X₀ X)

/-- The first chain's. No column opened. -/
def at₁ : ChainAt F.S₁ F.Cl (Local W₀ Rc Xi Tr) X :=
  ⟨⟨0, 0, P.storedWords w₀ rc, treeOwn⟩, R.first,
    (ChainProgress.start ⟨0, 0, P.storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder (some (R.start₁ P))
      (some (F.start₁ (F.pub x))) []).toOption, some (F.start₁ (F.pub x))⟩

/-- The shared chain's. No column opened. -/
def at₂ : ChainAt F.S₂ F.Cl (Common W₀ Rc Ky) X₀ :=
  ⟨⟨1, 0, P.storedWords w₀ rc, treeOwn⟩, R.shared,
    (ChainProgress.start ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder (some (R.start₂ P))
      (some (F.start₂ (F.pub x))) []).toOption, some (F.start₂ (F.pub x))⟩

/-- The second chain's, of the first two chains' typed challenges in a row. n₁: how many of them are
the first chain's. Not reached (`start` and `s₀` are `none`) where a walk of the first two chains
does not return. Handed the two walks' columns, the first chain's first. The sealing round's test
(`sealQuiet`) is not asked here. -/
def at₃ (n₁ : Nat) (base : List Fmt.Drawn) : ChainAt F.S₃ F.Cl (Local W₀ Rc Xi Tr) X :=
  match (at₁ F P w₀ rc x R).start.bind fun a =>
      (walk ⟨0, 0, P.storedWords w₀ rc, treeOwn⟩ R.first (base.take n₁ ++ [noDraw])
        a).toOption,
    (at₂ F P w₀ rc x R).start.bind fun a =>
      (walk ⟨1, 0, P.storedWords w₀ rc, treeOwn⟩ R.shared (base.drop n₁) a).toOption with
  | some z₁, some z₂ =>
    ⟨⟨2, F.lastChainFirstTreeNumber, P.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩, R.second,
      (ChainProgress.start ⟨2, F.lastChainFirstTreeNumber, P.storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩ F.second.blocksInOrder
        (z₁.mid.bind fun m₁ => z₂.mid.map fun m₂ => R.start₃ P m₁ m₂)
        (door₃ F x z₁.ver z₂.ver) (z₁.cols ++ z₂.cols)).toOption, door₃ F x z₁.ver z₂.ver⟩
  | _, _ => ⟨⟨2, F.lastChainFirstTreeNumber, P.storedWords w₀ rc, treeOwn⟩, R.second, none, none⟩

end

/-! ## 2 In which chain -/

/-- **Where a run's three views meet a fall**: in the first chain; in the shared chain; or in the
second, from the door's state. -/
theorem views_fall {F : FileDescription Xi} {B : ProverCoinCounts} {P : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc}
    {x : Xi} {c : Coins B} {δ : Draws} {r : RunC F} (h : runC F B P w₀ rc x c δ = .ok r)
    (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃))
    (hv : (viewsFall F f₁ f₂ f₃ x r.run.views).isSome = true) :
    (chainFall f₁ 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (withEmptySealRound r.run.views.1)).isSome = true ∨
    (chainFall f₂ 0 F.shared.blocksInOrder (F.start₂ (F.pub x)) r.run.views.2.1).isSome = true ∨
    ∃ s₃, door₃ F x r.ends.1 r.ends.2.1 = some s₃ ∧
      (chainFall f₃ F.lastChainFirstTreeNumber F.second.blocksInOrder s₃ r.run.views.2.2).isSome = true := by
  obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, -⟩ := runC_ends h
  unfold viewsFall at hv
  simp only at hv
  cases g1 : chainFall f₁ 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (withEmptySealRound r.run.views.1) with
  | some _ => exact Or.inl rfl
  | none =>
    cases g2 : chainFall f₂ 0 F.shared.blocksInOrder (F.start₂ (F.pub x)) r.run.views.2.1 with
    | some _ => exact Or.inr (Or.inl rfl)
    | none =>
      right
      right
      rw [g1, g2] at hv
      have hv' : ((chainAt "" 0 F.first.blocksInOrder (F.start₁ (F.pub x))
          (withEmptySealRound r.run.views.1)).toOption.bind fun e₁ =>
        (chainAt "" 0 F.shared.blocksInOrder (F.start₂ (F.pub x)) r.run.views.2.1).toOption.bind fun e₂ =>
          (F.start₃ (F.pub x) e₁ e₂).toOption.bind fun s₃ =>
            chainFall f₃ F.lastChainFirstTreeNumber F.second.blocksInOrder s₃ r.run.views.2.2).isSome = true := hv
      cases k1 : chainAt "" 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (withEmptySealRound r.run.views.1) with
      | error _ =>
        rw [k1] at hv'
        cases hv'
      | ok e₁ =>
        cases k2 : chainAt "" 0 F.shared.blocksInOrder (F.start₂ (F.pub x)) r.run.views.2.1 with
        | error _ =>
          rw [k1, k2] at hv'
          cases hv'
        | ok e₂ =>
          rw [k1, k2] at hv'
          have hv'' : ((F.start₃ (F.pub x) e₁ e₂).toOption.bind fun s₃ =>
            chainFall f₃ F.lastChainFirstTreeNumber F.second.blocksInOrder s₃ r.run.views.2.2).isSome = true := hv'
          cases k3 : F.start₃ (F.pub x) e₁ e₂ with
          | error _ =>
            rw [k3] at hv''
            cases hv''
          | ok s₃ =>
            rw [k3] at hv''
            refine ⟨s₃, ?_, hv''⟩
            have q1 := (chainAt_ok.1 k1).2
            have q2 := (chainAt_ok.1 k2).2
            have q1' : foldBlocks 0 F.first.blocksInOrder (F.start₁ (F.pub x))
                (withEmptySealRound r.run.views.1).rounds r.run.views.1.opened = .ok (e₁, [], []) := q1
            rw [q1'] at a3
            rw [q2] at b3
            rw [a3, b3]
            show (F.start₃ (F.pub x) e₁ e₂).toOption = some s₃
            rw [k3]
            rfl

/-! ## 3 The law -/

section
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) {F : FileDescription Xi} {Bk : ProverCoinCounts}
  (G : Sides F Bk W₀ Rc Ky Tr X₀ X) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi)
  (k : Coins Bk) (R : Ready W₀ Rc Xi Ky Tr X₀ X) (ms₁ ms₂ ms₃ : List Mark) (p₁ p₂ p₃ : Nat → ℝ≥0∞)
  (pre₁ : List (Block F.S₁ F.Cl))

/-- The first chain's canonical gates: over the members in front of its last. -/
noncomputable def gates₁ : List Gate :=
  coverGates F.first.blocksInOrder G.falls₁ ms₁ 0 (fun _ => at₁ F (G.prover H) w₀ rc x R) p₁
    [noDraw] pre₁ 0 0 D.ds₁

/-- The shared chain's. -/
noncomputable def gates₂ : List Gate :=
  coverGates F.shared.blocksInOrder G.falls₂ ms₂ 0 (fun _ => at₂ F (G.prover H) w₀ rc x R) p₂ []
    F.shared.blocksInOrder 0 0 D.ds₂

/-- The second chain's: handed the first two chains' typed challenges as their front. -/
noncomputable def gates₃ : List Gate :=
  coverGates F.second.blocksInOrder G.falls₃ ms₃ (D.ds₁.length + D.ds₂.length)
    (at₃ F (G.prover H) w₀ rc x R D.ds₁.length) p₃ [] F.second.blocksInOrder 0 0 D.ds₃

variable {pre₁} {e₁ : Block F.S₁ F.Cl}

/-- **THE CANONICAL GATES COVER THE FALLS.** -/
theorem falls_cover (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R)
    (Sf : StopsFit F (G.prover H) D pre₁ e₁) (hne : pre₁ ≠ [])
    (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh)
    (hf : (fallAt G H w₀ rc x k (drawsAt C D tF tJ t3 ρ)).isSome = true) :
    spoken (gates₁ D G H w₀ rc x R ms₁ p₁ pre₁) []
        (drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ)) = true ∨
    spoken (gates₂ D G H w₀ rc x R ms₂ p₂) []
        (drawnT C D.ds₂ ((chainsOf C D tF tJ t3).rho₂ ρ)) = true ∨
    spoken (gates₃ D G H w₀ rc x R ms₃ p₃)
        (drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ) ++
          drawnT C D.ds₂ ((chainsOf C D tF tJ t3).rho₂ ρ))
        (drawnT C D.ds₃ ((chainsOf C D tF tJ t3).rho₃ ρ)) = true := by
  unfold fallAt at hf
  cases hr : runC F Bk (G.prover H) w₀ rc x k (drawsAt C D tF tJ t3 ρ) with
  | error _ =>
    rw [hr] at hf
    cases hf
  | ok r =>
    rw [hr] at hf
    have hf' : (viewsFall F G.falls₁ G.falls₂ G.falls₃ x r.run.views).isSome = true := hf
    have hv := views_fall hr G.falls₁ G.falls₂ G.falls₃ hf'
    obtain ⟨R', a₁, z₁, a₂, z₂, a₃, z₃, hR', ha₁, hw₁, hq, ha₂, hw₂, ha₃, hw₃, rfl⟩ :=
      runC_parts hr
    rw [hR] at hR'
    cases hR'
    obtain ⟨d₁, hd₁⟩ : ∃ u, drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ) = u := ⟨_, rfl⟩
    obtain ⟨d₂, hd₂⟩ : ∃ u, drawnT C D.ds₂ ((chainsOf C D tF tJ t3).rho₂ ρ) = u := ⟨_, rfl⟩
    obtain ⟨d₃, hd₃⟩ : ∃ u, drawnT C D.ds₃ ((chainsOf C D tF tJ t3).rho₃ ρ) = u := ⟨_, rfl⟩
    have l1 : d₁.length = D.ds₁.length := by rw [← hd₁, drawnT_len]
    have l2 : d₂.length = D.ds₂.length := by rw [← hd₂, drawnT_len]
    have l3 : d₃.length = D.ds₃.length := by rw [← hd₃, drawnT_len]
    have hw₁' : walk ⟨0, 0, (G.prover H).storedWords w₀ rc, treeOwn⟩ R.first
        (d₁ ++ [noDraw]) a₁ = .ok z₁ := by
      rw [← hd₁]
      exact hw₁
    have hw₂' : walk ⟨1, 0, (G.prover H).storedWords w₀ rc, treeOwn⟩ R.shared d₂ a₂ = .ok z₂ := by
      rw [← hd₂]
      exact hw₂
    have hw₃' : walk ⟨2, F.lastChainFirstTreeNumber, (G.prover H).storedWords w₀ rc,
        treeThird z₁.laid z₂.laid⟩ R.second d₃ a₃ = .ok z₃ := by
      rw [← hd₃]
      exact hw₃
    have n1 := walk_len _ _ _ _ _ hw₁'
    have n2 := walk_len _ _ _ _ _ hw₂'
    have n3 := walk_len _ _ _ _ _ hw₃'
    rw [hd₁, hd₂, hd₃]
    rcases hv with g | g | ⟨s₃, g0, g⟩
    · left
      have key := cover_chain F.first.blocksInOrder G.falls₁ ms₁ 0
        (fun _ => at₁ F (G.prover H) w₀ rc x R) p₁ [noDraw] [] d₁ rfl pre₁ 0 0 D.ds₁ hne
        Sf.l₁ (by rw [Nat.zero_add, l1, Sf.l₁]) (by
          have e0 : 0 + (pre₁.flatMap (·.rounds)).length + [noDraw].length =
              (d₁ ++ [noDraw]).length := by
            rw [List.length_append, l1, Sf.l₁, Nat.zero_add]
          have hs : (at₁ F (G.prover H) w₀ rc x R).start = some a₁ := by
            show (ChainProgress.start ⟨0, 0, (G.prover H).storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder
              (some (R.start₁ (G.prover H))) (some (F.start₁ (F.pub x))) []).toOption = some a₁
            rw [ha₁]
            rfl
          have hw : walk (at₁ F (G.prover H) w₀ rc x R).lay
              ((at₁ F (G.prover H) w₀ rc x R).steps.take (d₁ ++ [noDraw]).length)
              ((d₁ ++ [noDraw]).take (d₁ ++ [noDraw]).length) a₁ = .ok z₁ := by
            show walk ⟨0, 0, (G.prover H).storedWords w₀ rc, treeOwn⟩
              (R.first.take (d₁ ++ [noDraw]).length)
              ((d₁ ++ [noDraw]).take (d₁ ++ [noDraw]).length) a₁ = .ok z₁
            rw [List.take_length, n1, List.take_length]
            exact hw₁'
          rw [e0, fellBy_ok F.first.blocksInOrder G.falls₁ hs rfl hw]
          have e1 : (⟨roundsOf z₁.laid, z₁.cols⟩ : Fmt.View) =
              withEmptySealRound ⟨(roundsOf z₁.laid).dropLast, z₁.cols⟩ := by
            unfold withEmptySealRound
            rw [seal_back hq]
          rw [e1]
          exact g)
      rw [List.take_zero, List.append_nil, List.drop_zero] at key
      exact key
    · right
      left
      have key := cover_chain F.shared.blocksInOrder G.falls₂ ms₂ 0
        (fun _ => at₂ F (G.prover H) w₀ rc x R) p₂ [] [] d₂ rfl F.shared.blocksInOrder 0 0 D.ds₂
        (by
          intro h0
          have := flat_isEmpty F.shared
          rw [h0] at this
          cases this)
        Sf.l₂ (by rw [Nat.zero_add, l2, Sf.l₂]) (by
          have e0 : 0 + (F.shared.blocksInOrder.flatMap (·.rounds)).length +
              ([] : List Fmt.Drawn).length = d₂.length := by
            rw [l2, Sf.l₂, Nat.zero_add]
            rfl
          have hs : (at₂ F (G.prover H) w₀ rc x R).start = some a₂ := by
            show (ChainProgress.start ⟨1, 0, (G.prover H).storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder
              (some (R.start₂ (G.prover H))) (some (F.start₂ (F.pub x))) []).toOption = some a₂
            rw [ha₂]
            rfl
          have hw : walk (at₂ F (G.prover H) w₀ rc x R).lay
              ((at₂ F (G.prover H) w₀ rc x R).steps.take d₂.length) (d₂.take d₂.length) a₂ =
              .ok z₂ := by
            show walk ⟨1, 0, (G.prover H).storedWords w₀ rc, treeOwn⟩ (R.shared.take d₂.length)
              (d₂.take d₂.length) a₂ = .ok z₂
            rw [List.take_length, n2, List.take_length]
            exact hw₂'
          rw [e0, List.append_nil, fellBy_ok F.shared.blocksInOrder G.falls₂ hs rfl hw]
          exact g)
      rw [List.take_zero, List.append_nil, List.drop_zero] at key
      exact key
    · right
      right
      have hX : at₃ F (G.prover H) w₀ rc x R D.ds₁.length (d₁ ++ d₂) =
          ⟨⟨2, F.lastChainFirstTreeNumber, (G.prover H).storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩,
            R.second, some a₃, door₃ F x z₁.ver z₂.ver⟩ := by
        have hs1 : ((at₁ F (G.prover H) w₀ rc x R).start.bind fun a =>
            (walk ⟨0, 0, (G.prover H).storedWords w₀ rc, treeOwn⟩ R.first
              ((d₁ ++ d₂).take D.ds₁.length ++ [noDraw]) a).toOption) = some z₁ := by
          show ((ChainProgress.start ⟨0, 0, (G.prover H).storedWords w₀ rc, treeOwn⟩ F.first.blocksInOrder
            (some (R.start₁ (G.prover H))) (some (F.start₁ (F.pub x))) []).toOption.bind fun a =>
            (walk ⟨0, 0, (G.prover H).storedWords w₀ rc, treeOwn⟩ R.first
              ((d₁ ++ d₂).take D.ds₁.length ++ [noDraw]) a).toOption) = some z₁
          rw [ha₁, ← l1, List.take_left' rfl]
          show (walk ⟨0, 0, (G.prover H).storedWords w₀ rc, treeOwn⟩ R.first (d₁ ++ [noDraw])
            a₁).toOption = some z₁
          rw [hw₁']
          rfl
        have hs2 : ((at₂ F (G.prover H) w₀ rc x R).start.bind fun a =>
            (walk ⟨1, 0, (G.prover H).storedWords w₀ rc, treeOwn⟩ R.shared
              ((d₁ ++ d₂).drop D.ds₁.length) a).toOption) = some z₂ := by
          show ((ChainProgress.start ⟨1, 0, (G.prover H).storedWords w₀ rc, treeOwn⟩ F.shared.blocksInOrder
            (some (R.start₂ (G.prover H))) (some (F.start₂ (F.pub x))) []).toOption.bind fun a =>
            (walk ⟨1, 0, (G.prover H).storedWords w₀ rc, treeOwn⟩ R.shared
              ((d₁ ++ d₂).drop D.ds₁.length) a).toOption) = some z₂
          rw [ha₂, ← l1, List.drop_left' rfl]
          show (walk ⟨1, 0, (G.prover H).storedWords w₀ rc, treeOwn⟩ R.shared d₂
            a₂).toOption = some z₂
          rw [hw₂']
          rfl
        unfold at₃
        rw [hs1, hs2]
        simp only
        rw [ha₃]
        rfl
      have key := cover_chain F.second.blocksInOrder G.falls₃ ms₃ (D.ds₁.length + D.ds₂.length)
        (at₃ F (G.prover H) w₀ rc x R D.ds₁.length) p₃ [] (d₁ ++ d₂) d₃
        (by rw [List.length_append, l1, l2]) F.second.blocksInOrder 0 0 D.ds₃
        (by
          intro h0
          have := flat_isEmpty F.second
          rw [h0] at this
          cases this)
        Sf.l₃ (by rw [Nat.zero_add, l3, Sf.l₃]) (by
          have e0 : 0 + (F.second.blocksInOrder.flatMap (·.rounds)).length +
              ([] : List Fmt.Drawn).length = d₃.length := by
            rw [l3, Sf.l₃, Nat.zero_add]
            rfl
          have g0' : door₃ F x z₁.ver z₂.ver = some s₃ := g0
          have hw : walk ⟨2, F.lastChainFirstTreeNumber, (G.prover H).storedWords w₀ rc,
              treeThird z₁.laid z₂.laid⟩ (R.second.take d₃.length) (d₃.take d₃.length) a₃ =
              .ok z₃ := by
            rw [List.take_length, n3, List.take_length]
            exact hw₃'
          rw [hX, e0, List.append_nil, fellBy_ok F.second.blocksInOrder G.falls₃ (X := ⟨⟨2, F.lastChainFirstTreeNumber,
                     (G.prover H).storedWords w₀ rc, treeThird z₁.laid z₂.laid⟩, R.second, some a₃,
                     door₃ F x z₁.ver z₂.ver⟩) rfl g0' hw]
          exact g)
      rw [List.take_zero, List.append_nil, List.drop_zero] at key
      exact key

/-- **THE FALLS' NUMBERS, AT THE CANONICAL GATES**: what is left is `GatesHeld` at these gates. The
numbers are letters: no stated share is in them. -/
theorem falls_held_canon (hR : ready F Bk (G.prover H) w₀ rc x k = .ok R)
    (Sf : StopsFit F (G.prover H) D pre₁ e₁) (hne : pre₁ ≠ [])
    (h₁ : GatesHeld C (gates₁ D G H w₀ rc x R ms₁ p₁ pre₁) [])
    (h₂ : GatesHeld C (gates₂ D G H w₀ rc x R ms₂ p₂) [])
    (h₃ : ∀ (a : Iop.Rho (uLT C D.ds₁)) (b : Iop.Rho (uLT C D.ds₂)),
      spoken (gates₁ D G H w₀ rc x R ms₁ p₁ pre₁) [] (drawnT C D.ds₁ a) = false →
      spoken (gates₂ D G H w₀ rc x R ms₂ p₂) [] (drawnT C D.ds₂ b) = false →
      GatesHeld C (gates₃ D G H w₀ rc x R ms₃ p₃) (drawnT C D.ds₁ a ++ drawnT C D.ds₂ b)) :
    Iop.prRho {ρ : Iop.Rho (chainsOf C D tF tJ t3).sh |
        (fallAt G H w₀ rc x k (drawsAt C D tF tJ t3 ρ)).isSome = true} ≤
      ((gates₁ D G H w₀ rc x R ms₁ p₁ pre₁).map (·.p)).sum +
        (((gates₂ D G H w₀ rc x R ms₂ p₂).map (·.p)).sum +
          ((gates₃ D G H w₀ rc x R ms₃ p₃).map (·.p)).sum) :=
  falls_held C D tF tJ t3 G H w₀ rc x k _ _ _ (cover_ds _ _ _ _ _ _ _ _ _ _ _ Sf.l₁)
    (cover_ds _ _ _ _ _ _ _ _ _ _ _ Sf.l₂) (cover_ds _ _ _ _ _ _ _ _ _ _ _ Sf.l₃)
    (fun d₁ d₂ => d₁ ++ d₂)
    (falls_cover C D tF tJ t3 G H w₀ rc x k R ms₁ ms₂ ms₃ p₁ p₂ p₃ hR Sf hne) h₁ h₂ h₃

end

end ProofFile.Honest

#print axioms ProofFile.Honest.fellBy_ok
#print axioms ProofFile.Honest.views_fall
#print axioms ProofFile.Honest.falls_cover
#print axioms ProofFile.Honest.falls_held_canon
#print axioms ProofFile.Honest.noDraw
#print axioms ProofFile.Honest.at₁
#print axioms ProofFile.Honest.at₂
#print axioms ProofFile.Honest.at₃
#print axioms ProofFile.Honest.gates₁
#print axioms ProofFile.Honest.gates₂
#print axioms ProofFile.Honest.gates₃
