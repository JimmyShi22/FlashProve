-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverBelow.lean: the verifier's state beside a walk is reached by
the wrapped sub-protocols too. The library has two families of reached states (`Reach`,
Johnson/Top/H0/Walk/Reach.lean). One steps by a chain's sub-protocols themselves. The other steps by
the same sub-protocols under `below` (Johnson/Desc/Sound/ChainRule.lean): each first tests that
every word that it is shown is below the field's prime. `RchAt` (Johnson/Top/H0/Walk/ReachAt.lean)
is the second family at a description's first chain. A walk (Honest/Walk.lean) asks the
sub-protocols themselves, so its verifier's state is in the first family (`ChainProgress.Tied`,
Honest/Law/WalkFold.lean). These lemmas show that the state is in the second family as well, if the
challenges heard so far are challenges that the rounds can draw.

A view shows three sorts of words (`viewWordsBelowPrime`, Johnson/Desc/Block.lean). The items: a walk collects
typed field elements that are written as words, or the fixed substitute, so their words are below
the prime (`say_lt`, Honest/Law/WalkMid.lean). The opened columns: `walk_lt`
(Honest/Law/AcceptC.lean). The drawn elements: this is a hypothesis, and it is one clause of
`drawFit` (Honest/Frame.lean).

They use `reach_below_of_fold` (Honest/Thread/SaidOk.lean), `fold_more` and `fold_split`
(Johnson/Top/H0/Walk/Reach.lean), `front_stand` (Honest/Law/CoverPay.lean), `fit_of_silent`
(Honest/Law/CoverFit.lean) and `at₁_starts` (Honest/Law/CoverAll.lean).

  1  (`say_lt`, `okRound_lt`, `drawFit_elems`, `drawsFit_elems`, `walk_said`, the words of the
     rounds that a walk has collected: Honest/Law/WalkMid.lean)
  2  `ver_reach_below`   the state just before a sub-protocol that has a round
  3  `walk_fold_below`, `ver_reach_all`   every border up to the last sub-protocol that the walk has
     asked, also a border before a sub-protocol without a round
  4  `ver_rchAt`, `silent_rchAt`, `rchAt_all`   the same at a description's first chain

Limits.
  * The words of the drawn elements are a hypothesis. A list of challenges with a word that is not
    below the prime is not covered.
  * `ver_reach_below`, `ver_rchAt` and `silent_rchAt` cover the state just before a sub-protocol
    that has a round.
  * At a border inside the stretch that the walk has asked, `ver_reach_all` and `rchAt_all` speak of
    the state that the fold over the sub-protocols before the border returns at the walk's rounds
    and columns. A walk itself stores the last of these states alone.
  * `front`: the columns of earlier chains that `ChainProgress.start` hands the parts. The lemmas hold at
    every `front`; no end reads it. `z.cols` are the chain's own columns.
  * Part 4 covers the first chain alone.
  * `silent_rchAt` asks that the marks include `fitMarks` of the gated sub-protocols.
  * The lemmas are applied to no description here.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.AcceptC
import Johnson.Desc.ProofFile.Honest.Law.StratCanonC
import Johnson.Desc.ProofFile.Honest.Law.CoverAll
import Johnson.Desc.ProofFile.Honest.Law.CoverFit
import Johnson.Desc.ProofFile.Honest.Thread.SaidOk
import Johnson.Top.H0.Walk.ReachAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach RchAt fold_more fold_split)

variable {S Cl W Y : Type}

/-! ## 2 The state just before a sub-protocol that has a round -/

/-- Just before a sub-protocol `b` that has a round, the verifier's state beside the walk is reached
by the steps of the sub-protocols under `below`. `A`: the sub-protocols before `b`; `t`: those after
it. `hs`: the words of the stored columns are below the prime. `hd`: the challenges are challenges
that the rounds of `A` can draw. -/
theorem ver_reach_below (L : Lay)
    (hs : ∀ i x u, L.stored i x = some u → ∀ a ∈ u, a < fieldPrimeWord) {P : Type} (start : P → S)
    (zp : P) (A : List (Block S Cl)) (b : Block S Cl) (t : List (Block S Cl))
    (hb : 0 < b.rounds.length) (m₀ : Option (Mid W Y)) (hm : m₀.isSome = true)
    {a z : ChainProgress S Cl W Y} {ss : List (Step W Y)} {dA : List Fmt.Drawn} {s' : S}
    {front : List OpenedColumn} (ha : ChainProgress.start L (A ++ b :: t) m₀ (some (start zp)) front = .ok a)
    (hz : walk L ss dA a = .ok z) (hd : drawsFit (A.flatMap (·.rounds)) dA = true)
    (hv : z.ver = some s') :
    Reach L.firstTree ((A ++ b :: t).map below) start A.length (zp, s') := by
  have hl : ss.length = (A.flatMap (·.rounds)).length := by
    rw [← walk_len L ss dA a z hz, drawsFit_length _ _ hd]
  obtain ⟨e1, e2⟩ := front_stand L (A ++ b :: t) A t b hm ha rfl hb hz hl
  obtain ⟨t0, o0, l0⟩ := start_tied L (A ++ b :: t) m₀ (some (start zp)) ha
  rw [if_pos hm] at t0
  obtain ⟨t1, -, -⟩ := walk_tied L (A ++ b :: t) (some (start zp)) ss dA a z t0 o0 hz
  have hR : viewWordsBelowPrime ⟨roundsOf z.laid, []⟩ = true :=
    walk_said L ss dA a z (drawsFit_elems _ _ hd)
      ((congrArg (fun l => viewWordsBelowPrime ⟨roundsOf l, []⟩) l0).trans rfl) hz
  have hc : ColsLt z := walk_lt L hs ss dA a z (start_lt L hs _ _ _ ha) hz
  obtain ⟨done, front, h1, h2, -, -, h5⟩ := t1
  rw [e1] at h1
  have hdn : A = done := List.append_cancel_right h1
  subst hdn
  rw [e2, List.append_nil] at h2
  rw [← h2, hv] at h5
  have hk : (A ++ b :: t).take A.length = A := List.take_left' rfl
  cases hf : foldBlocks L.firstTree A (start zp) (roundsOf z.laid) z.cols with
  | error e =>
    have h6 : some s' = (foldBlocks L.firstTree A (start zp) (roundsOf z.laid)
      z.cols).toOption.map (·.1) := h5
    rw [hf] at h6
    have h7 : (some s' : Option S) = none := h6
    cases h7
  | ok y =>
    obtain ⟨s₁, r, c⟩ := y
    have h6 : some s' = (foldBlocks L.firstTree A (start zp) (roundsOf z.laid)
      z.cols).toOption.map (·.1) := h5
    rw [hf] at h6
    have h7 : some s' = some s₁ := h6
    cases h7
    exact reach_below_of_fold hR hc A.length
      (by rw [List.length_append]; exact Nat.le_add_right _ _) _ r c (by rw [hk]; exact hf)

/-! ## 3 Every border -/

/-- A fold over the first `k` sub-protocols that accepts, at rounds and columns that the walk has
collected, returns a state that is reached by the steps of the sub-protocols under `below`. `k` is
any border of the chain. `hd`: the words of the drawn elements are below the prime. -/
theorem walk_fold_below (L : Lay)
    (hs : ∀ i x u, L.stored i x = some u → ∀ a ∈ u, a < fieldPrimeWord) {P : Type} (start : P → S)
    (zp : P) (bs : List (Block S Cl)) (m₀ : Option (Mid W Y)) (v₀ : Option S)
    {a z : ChainProgress S Cl W Y} {ss : List (Step W Y)} {dA : List Fmt.Drawn}
    {front : List OpenedColumn} (ha : ChainProgress.start L bs m₀ v₀ front = .ok a) (hz : walk L ss dA a = .ok z)
    (hd : ∀ D ∈ dA,
      (D.elems.all fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true)
    {k : Nat} (hk : k ≤ bs.length) {s : S} {rs r : List Fmt.RoundView} {cs c : List OpenedColumn}
    (hrs : ∀ x ∈ rs, x ∈ roundsOf z.laid) (hcs : ∀ x ∈ cs, x ∈ z.cols)
    (hf : foldBlocks L.firstTree (bs.take k) (start zp) rs cs = .ok (s, r, c)) :
    Reach L.firstTree (bs.map below) start k (zp, s) := by
  obtain ⟨-, -, l0⟩ := start_tied L bs m₀ v₀ ha
  have hR : viewWordsBelowPrime ⟨roundsOf z.laid, []⟩ = true :=
    walk_said L ss dA a z hd ((congrArg (fun l => viewWordsBelowPrime ⟨roundsOf l, []⟩) l0).trans rfl) hz
  have hc : ColsLt z := walk_lt L hs ss dA a z (start_lt L hs _ _ _ ha) hz
  exact reach_below_of_fold (okRounds_sub hR hrs) (fun x hx => hc x (hcs x hx)) k hk s r c hf

/-- Wherever a walk stands with a verifier's state `s'`: `done` are the sub-protocols that it has
asked. The state `s'` is reached at the border after them, and at every border `k` before that the
fold over the first `k` sub-protocols accepts at the walk's rounds and columns and returns a reached
state. All by the steps of the sub-protocols under `below`. -/
theorem ver_reach_all (L : Lay)
    (hs : ∀ i x u, L.stored i x = some u → ∀ a ∈ u, a < fieldPrimeWord) {P : Type} (start : P → S)
    (zp : P) (bs : List (Block S Cl)) (m₀ : Option (Mid W Y)) (hm : m₀.isSome = true)
    {a z : ChainProgress S Cl W Y} {ss : List (Step W Y)} {dA : List Fmt.Drawn} {s' : S}
    {front : List OpenedColumn} (ha : ChainProgress.start L bs m₀ (some (start zp)) front = .ok a)
    (hz : walk L ss dA a = .ok z)
    (hd : ∀ D ∈ dA,
      (D.elems.all fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true)
    (hv : z.ver = some s') :
    ∃ done : List (Block S Cl), bs = done ++ z.todo ∧
      Reach L.firstTree (bs.map below) start done.length (zp, s') ∧
      ∀ k, k ≤ done.length → ∃ (s : S) (r : List Fmt.RoundView) (c : List OpenedColumn),
        foldBlocks L.firstTree (bs.take k) (start zp) (roundsOf z.laid) z.cols = .ok (s, r, c) ∧
          Reach L.firstTree (bs.map below) start k (zp, s) := by
  obtain ⟨t0, o0, -⟩ := start_tied L bs m₀ (some (start zp)) ha
  rw [if_pos hm] at t0
  obtain ⟨t1, -, -⟩ := walk_tied L bs (some (start zp)) ss dA a z t0 o0 hz
  obtain ⟨done, front, h1, h2, -, -, h5⟩ := t1
  rw [hv] at h5
  have h6 : some s' = (foldBlocks L.firstTree done (start zp) (roundsOf front)
    z.cols).toOption.map (·.1) := h5
  cases hf : foldBlocks L.firstTree done (start zp) (roundsOf front) z.cols with
  | error e =>
    rw [hf] at h6
    have h7 : (some s' : Option S) = none := h6
    cases h7
  | ok y =>
    obtain ⟨s₁, r₀, c₀⟩ := y
    rw [hf] at h6
    have h7 : some s' = some s₁ := h6
    have h8 : s₁ = s' := (Option.some.inj h7).symm
    rw [h8] at hf
    have hg := fold_more L.firstTree (roundsOf z.own) [] done (start zp) s' (roundsOf front) r₀
      z.cols c₀ hf
    rw [← roundsOf_append, ← h2] at hg
    simp only [List.append_nil] at hg
    have hlen : done.length ≤ bs.length := by
      rw [h1, List.length_append]
      exact Nat.le_add_right _ _
    have e0 : bs.take done.length = done := by
      rw [h1]
      exact List.take_left' rfl
    refine ⟨done, h1, ?_, ?_⟩
    · exact walk_fold_below L hs start zp bs m₀ _ ha hz hd hlen (r := r₀ ++ roundsOf z.own)
        (c := c₀) (fun _ h => h) (fun _ h => h) (by rw [e0]; exact hg)
    · intro k hk
      have e1 : bs.take k = done.take k := by
        rw [h1]
        exact List.take_append_of_le_length hk
      have hg' : foldBlocks L.firstTree (done.take k ++ done.drop k) (start zp)
          (roundsOf z.laid) z.cols = .ok (s', r₀ ++ roundsOf z.own, c₀) := by
        rw [List.take_append_drop]
        exact hg
      obtain ⟨u, r₁, c₁, g1, -⟩ := fold_split L.firstTree (done.drop k) (done.take k) _ _ _ _ hg'
      rw [← e1] at g1
      exact ⟨u, r₁, c₁, g1, walk_fold_below L hs start zp bs m₀ _ ha hz hd
        (Nat.le_trans hk hlen) (fun _ h => h) (fun _ h => h) g1⟩

/-! ## 4 At a description's first chain -/

section
variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-- At a description's first chain: the library's `RchAt`, at the instance's own public part. `y`:
what stands beside the statement's first half; it is not read. -/
theorem ver_rchAt (F : FileDescription Xi) (P : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi)
    (R : Ready W₀ Rc Xi Ky Tr X₀ X) {A : List (Block F.S₁ F.Cl)} {b : Block F.S₁ F.Cl}
    {t : List (Block F.S₁ F.Cl)} (hF : F.first.blocksInOrder = A ++ b :: t) (hr : b.rounds ≠ [])
    {a z : ChainProgress F.S₁ F.Cl (Local W₀ Rc Xi Tr) X} {ss : List (Step (Local W₀ Rc Xi Tr) X)}
    {dA : List Fmt.Drawn} {s' : F.S₁} (y1 : (at₁ F P w₀ rc x R).start = some a)
    (y2 : walk (at₁ F P w₀ rc x R).lay ss dA a = .ok z)
    (hd : drawsFit (A.flatMap (·.rounds)) dA = true) (hv : z.ver = some s') {Str : Type}
    (y : Str) : RchAt F A.length ((F.pub x, s'), y) := by
  obtain ⟨m₀, _, hm, ha⟩ := at₁_starts F P w₀ rc x R a (F.start₁ (F.pub x)) y1 rfl
  rw [hF] at ha
  have h := ver_reach_below (at₁ F P w₀ rc x R).lay (storedWords_lt P w₀ rc) F.start₁ (F.pub x) A b
    t (List.length_pos_of_ne_nil hr) m₀ hm ha y2 hd hv
  unfold RchAt
  rw [hF]
  exact h

/-- The same from what `debt_busy_P` (Honest/Law/CoverFront.lean) hands whoever proves its
hypothesis `hP` at the first chain: the marks before `b` have been silent, and `fitMarks` are among
the marks. `pre`: the gated sub-protocols; `rest`: those after them. -/
theorem silent_rchAt (F : FileDescription Xi) (P : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc)
    (x : Xi) (R : Ready W₀ Rc Xi Ky Tr X₀ X) (ms : List Mark)
    {pre rest A B : List (Block F.S₁ F.Cl)} {b : Block F.S₁ F.Cl}
    (hall : F.first.blocksInOrder = pre ++ rest) (hsub : ∀ mk ∈ fitMarks pre, mk ∈ ms)
    (e : pre = A ++ b :: B) (hr : b.rounds ≠ []) {fr : List Fmt.Drawn}
    {a z : ChainProgress F.S₁ F.Cl (Local W₀ Rc Xi Tr) X} {ss : List (Step (Local W₀ Rc Xi Tr) X)}
    {s' : F.S₁} (h2 : (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length)
    (h4 : silentQ ms 0 pre (0 + A.length) fr) (y1 : (at₁ F P w₀ rc x R).start = some a)
    (y2 : walk (at₁ F P w₀ rc x R).lay ss (fr.drop 0) a = .ok z) (hv : z.ver = some s')
    {Str : Type} (y : Str) : RchAt F A.length ((F.pub x, s'), y) := by
  have hA : pre.take (0 + A.length) = A := by
    rw [e, Nat.zero_add]
    exact List.take_left' rfl
  have hd := fit_of_silent pre ms hsub 0 (0 + A.length) fr (by rw [hA, h2, Nat.zero_add]) h4
  rw [hA] at hd
  exact ver_rchAt F P w₀ rc x R (t := B ++ rest)
    (by rw [hall, e, List.append_assoc, List.cons_append]) hr y1 y2 hd hv y

/-- Every border of a description's first chain up to the last sub-protocol that the walk has asked:
`ver_reach_all` in the library's `RchAt`. -/
theorem rchAt_all (F : FileDescription Xi) (P : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi)
    (R : Ready W₀ Rc Xi Ky Tr X₀ X) {a z : ChainProgress F.S₁ F.Cl (Local W₀ Rc Xi Tr) X}
    {ss : List (Step (Local W₀ Rc Xi Tr) X)} {dA : List Fmt.Drawn} {s' : F.S₁}
    (y1 : (at₁ F P w₀ rc x R).start = some a)
    (y2 : walk (at₁ F P w₀ rc x R).lay ss dA a = .ok z)
    (hd : ∀ D ∈ dA,
      (D.elems.all fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true)
    (hv : z.ver = some s') {Str : Type} (y : Str) :
    ∃ done : List (Block F.S₁ F.Cl), F.first.blocksInOrder = done ++ z.todo ∧
      RchAt F done.length ((F.pub x, s'), y) ∧
      ∀ k, k ≤ done.length → ∃ (s : F.S₁) (r : List Fmt.RoundView) (c : List OpenedColumn),
        foldBlocks 0 (F.first.blocksInOrder.take k) (F.start₁ (F.pub x)) (roundsOf z.laid) z.cols =
          .ok (s, r, c) ∧ RchAt F k ((F.pub x, s), y) := by
  obtain ⟨m₀, _, hm, ha⟩ := at₁_starts F P w₀ rc x R a (F.start₁ (F.pub x)) y1 rfl
  exact ver_reach_all (at₁ F P w₀ rc x R).lay (storedWords_lt P w₀ rc) F.start₁ (F.pub x)
    F.first.blocksInOrder m₀ hm ha y2 hd hv

end

end ProofFile.Honest

#print axioms ProofFile.Honest.ver_reach_below
#print axioms ProofFile.Honest.walk_fold_below
#print axioms ProofFile.Honest.ver_reach_all
#print axioms ProofFile.Honest.ver_rchAt
#print axioms ProofFile.Honest.silent_rchAt
#print axioms ProofFile.Honest.rchAt_all
