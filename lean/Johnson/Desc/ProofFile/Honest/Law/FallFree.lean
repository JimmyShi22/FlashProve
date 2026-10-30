-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/FallFree.lean: "no fall fires", from the executable test on the
views. If `viewsFall` (Honest/Fall.lean) returns `none` at the views of a run of `runC`, the three
hypotheses `fallFree` of the rule for a file's acceptance (Honest/Law/AcceptC.lean) hold, at the
falls taken by the sub-protocols' places (`fallFree_of_views`). So that rule can be used with the
executable test as its hypothesis (`runC_accepts_views`). Its conclusion is that `FileDescription.run`
accepts, at a parameter F. That is one test of the verdict of the file's interactive oracle
reduction (`FileDescription.toIOR`), which `FileDescription.out_eq` (Johnson/Desc/BlockSlot.lean) unfolds into
nine tests. It is not a verifier's acceptance: the tests on the proof-of-work bits, on the
completeness of the draws, on the stored string's positions and on the three rounds without a
challenge are not reached.

  1  `fallsBy`, `fallsBy_succ`   a chain's falls by the sub-protocol's number: those at its place
  2  `fallFree_of_fronts`, `fallFree_of_chain`   one chain
  3  `fallFree_of_views`   the file
  4  `runC_accepts_views`   the rule for a file's acceptance, with `viewsFall … = none` as its
     hypothesis

The rule can hold vacuously in four ways (Honest/Law/AcceptC.lean tells them in full), and nothing
here excludes any of them: invariants that cannot be entered; a fall that fires too often (always:
the rule says nothing; exactly where the sub-protocol's own step rejects, which is easy at a
sub-protocol without a round: "no fall fires" then contains the conclusion); a prover that stops at
every list of challenges; a book at which `ready` returns an error at every coin. What a fall costs
is its share (`Fall.share`), which nothing compares with the test; whoever writes a fall names the
verifier's own tests that it excuses.

Limits.
  * Nothing is said on how likely a fall is.
  * The invariants at the starts are asked at the states as `ChainProgress.start` lays them, as in
    `runC_accepts`.
  * `PlaysOn` and `SaysYes` are asked at every state that the invariant allows, at every value of
    the field `opened` too: at a prover with a part that reads the columns and errs at `none` (its
    duty: Honest/Frame.lean, `Seen.opened`), `PlaysOn` at an invariant that lets `none` through
    before that part's sub-protocol is met only vacuously (Honest/Law/ThreadC.lean, Limits).
  * Hypotheses that the prose above does not name: `Draws.due` (the challenges are such as the
    description's rounds can draw; the first chain's last challenge is the empty one):
    `runC_accepts_views`; `FileDescription.planOk` (the library's executable test): `runC_accepts_views`;
    `silentAt … = none` (the honest side does not stop at these challenges, or the request has no
    trace): `runC_accepts_views`; `FileDescription.okStart` (the library's executable test, at
    the instance): `runC_accepts_views`; `ready … = .ok` (`ready` returns at these coins):
    `runC_accepts_views`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Fall
import Johnson.Desc.ProofFile.Honest.Law.AcceptC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl Xi W₀ Rc Ky Tr X₀ X : Type}

/-! ## 1 By the number -/

/-- A chain's falls by the sub-protocol's number, from 0: those at its place; beyond the list: none.
Falls go by the place: two sub-protocols at one place would share theirs; the description's test
`FileDescription.placesOk`, which `planOk` includes, forbids that. -/
def fallsBy (fs : List (Fall S)) (bs : List (Block S Cl)) (j : Nat) :
    S → List Fmt.Drawn → Option String :=
  match bs[j]? with
  | some b => fallOf fs b.place
  | none => fun _ _ => none

theorem fallsBy_succ (fs : List (Fall S)) (b : Block S Cl) (l : List (Block S Cl)) :
    (fun j => fallsBy fs (b :: l) (j + 1)) = fallsBy fs l := by
  funext j
  unfold fallsBy
  rw [List.getElem?_cons_succ]

/-! ## 2 One chain -/

theorem fallFree_of_fronts (fs : List (Fall S)) (ft : Nat) : ∀ (bs : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn), (bs.flatMap (·.rounds)).length ≤ rs.length →
    ((frontsOf ft bs s rs cols).findSome? fun x =>
      (fallOf fs x.1 x.2.1 x.2.2).map fun e => (x.1, e)) = none →
    fallFree ft bs (fallsBy fs bs) s rs cols
  | [], _, _, _, _, _ => trivial
  | b :: l, s, rs, cols, hr, h => by
    rw [List.flatMap_cons, List.length_append] at hr
    have hlen : (rs.take b.rounds.length).length = b.rounds.length := by
      rw [List.length_take]
      omega
    have hf : frontsOf ft (b :: l) s rs cols =
        (b.place, s, (rs.take b.rounds.length).map (·.drawn)) ::
          match b.step ft s (rs.take b.rounds.length) cols with
          | .error _ => []
          | .ok (s', k) => frontsOf ft l s' (rs.drop b.rounds.length) (cols.drop k) := by
      conv_lhs => unfold frontsOf
      simp only [hlen, bne_self_eq_false, Bool.false_eq_true, if_false]
      rfl
    rw [hf, List.findSome?_cons] at h
    cases h0 : fallOf fs b.place s ((rs.take b.rounds.length).map (·.drawn)) with
    | some e =>
      rw [h0] at h
      cases h
    | none =>
      rw [h0] at h
      have h' : ((match b.step ft s (rs.take b.rounds.length) cols with
          | .error _ => ([] : List (Place × S × List Fmt.Drawn))
          | .ok (s', k) => frontsOf ft l s' (rs.drop b.rounds.length) (cols.drop k)).findSome?
          fun x : Place × S × List Fmt.Drawn =>
            (fallOf fs x.1 x.2.1 x.2.2).map fun e => (x.1, e)) = none := h
      refine ⟨h0, fun s' k hs => ?_⟩
      rw [hs] at h'
      rw [fallsBy_succ]
      exact fallFree_of_fronts fs ft l s' _ _ (by rw [List.length_drop]; omega) h'

theorem fallFree_of_chain (fs : List (Fall S)) (ft : Nat) (bs : List (Block S Cl)) (s : S)
    (v : Fmt.View) (hr : v.rounds.length = (bs.flatMap (·.rounds)).length)
    (h : chainFall fs ft bs s v = none) : fallFree ft bs (fallsBy fs bs) s v.rounds v.opened :=
  fallFree_of_fronts fs ft bs s v.rounds v.opened (Nat.le_of_eq hr.symm) h

/-! ## 3 The file -/

section
variable {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi}
  {c : Coins B} {ρ : Draws} {r : RunC F}

theorem fallFree_of_views (h : runC F B H w₀ rc x c ρ = .ok r) (f₁ : List (Fall F.S₁))
    (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃))
    (hv : viewsFall F f₁ f₂ f₃ x r.run.views = none) :
    fallFree 0 F.first.blocksInOrder (fallsBy f₁ F.first.blocksInOrder) (F.start₁ (F.pub x))
      (withEmptySealRound r.run.views.1).rounds r.run.views.1.opened ∧
    fallFree 0 F.shared.blocksInOrder (fallsBy f₂ F.shared.blocksInOrder) (F.start₂ (F.pub x))
      r.run.views.2.1.rounds r.run.views.2.1.opened ∧
    ∀ e₁ e₂ s₃, r.ends.1 = some e₁ → r.ends.2.1 = some e₂ → F.start₃ (F.pub x) e₁ e₂ = .ok s₃ →
      fallFree F.lastChainFirstTreeNumber F.second.blocksInOrder (fallsBy f₃ F.second.blocksInOrder) s₃ r.run.views.2.2.rounds
        r.run.views.2.2.opened := by
  obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, ⟨c1, -, -⟩⟩ := runC_ends h
  unfold viewsFall at hv
  obtain ⟨h12, h3⟩ := or_none hv
  obtain ⟨h1, h2⟩ := or_none h12
  refine ⟨fallFree_of_chain f₁ 0 F.first.blocksInOrder _ (withEmptySealRound r.run.views.1) a1 h1,
    fallFree_of_chain f₂ 0 F.shared.blocksInOrder _ r.run.views.2.1 b1 h2, ?_⟩
  intro e₁ e₂ s₃ g1 g2 g3
  rw [g1] at a3
  rw [g2] at b3
  have k1 : chainAt "" 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (withEmptySealRound r.run.views.1) = .ok e₁ :=
    chainAt_ok.2 ⟨flat_isEmpty _, (fold_some 0 _ _ e₁ _ _ a1 a2).1 a3.symm⟩
  have k2 : chainAt "" 0 F.shared.blocksInOrder (F.start₂ (F.pub x)) r.run.views.2.1 = .ok e₂ :=
    chainAt_ok.2 ⟨flat_isEmpty _, (fold_some 0 _ _ e₂ _ _ b1 b2).1 b3.symm⟩
  rw [k1, k2] at h3
  have h3' : ((F.start₃ (F.pub x) e₁ e₂).toOption.bind fun s₃ =>
      chainFall f₃ F.lastChainFirstTreeNumber F.second.blocksInOrder s₃ r.run.views.2.2) = none := h3
  rw [g3] at h3'
  exact fallFree_of_chain f₃ F.lastChainFirstTreeNumber F.second.blocksInOrder s₃ r.run.views.2.2 c1 h3'

end

/-! ## 4 The rule, with the executable test as its hypothesis -/

/-- **The rule for a file's acceptance, where the executable test on the views meets no fall.** A
conditional lemma on this folder's own functions, pointwise. Its conclusion is that `FileDescription.run`
accepts, one of the nine tests of the verdict of the file's interactive oracle reduction: not a
verifier's acceptance. It is none of the library's goals. -/
theorem runC_accepts_views {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀}
    {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Tr X₀ X} {r : RunC F}
    (h : runC F Bk H w₀ rc x k ρ = .ok r) (hR : ready F Bk H w₀ rc x k = .ok R)
    (hp : F.planOk = true) (hx : F.okStart x = true) (hρ : ρ.due F = true)
    (hsil : silentAt F H w₀ rc x ρ = none)
    (I₁ : Nat → Coins Bk → F.S₁ → Mid (Local W₀ Rc Xi Tr) X → Env → Prop)
    (I₂ : Nat → Coins Bk → F.S₂ → Mid (Common W₀ Rc Ky) X₀ → Env → Prop)
    (I₃ : Nat → Coins Bk → F.S₃ → Mid (Local W₀ Rc Xi Tr) X → Env → Prop)
    (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃))
    (h₁ : ∀ j b, F.first.blocksInOrder[j]? = some b → PlaysOn .own Bk 0 0 H.first b (I₁ j) (I₁ (j + 1)))
    (h₂ : ∀ j b, F.shared.blocksInOrder[j]? = some b →
      PlaysOn .shared Bk 1 0 H.shared b (I₂ j) (I₂ (j + 1)))
    (h₃ : ∀ j b, F.second.blocksInOrder[j]? = some b →
      PlaysOn .own Bk 2 F.lastChainFirstTreeNumber H.second b (I₃ j) (I₃ (j + 1)))
    (y₁ : ∀ j b, F.first.blocksInOrder[j]? = some b →
      SaysYes .own Bk 0 0 H.first b (fallOf f₁ b.place) (I₁ j))
    (y₂ : ∀ j b, F.shared.blocksInOrder[j]? = some b →
      SaysYes .shared Bk 1 0 H.shared b (fallOf f₂ b.place) (I₂ j))
    (y₃ : ∀ j b, F.second.blocksInOrder[j]? = some b →
      SaysYes .own Bk 2 F.lastChainFirstTreeNumber H.second b (fallOf f₃ b.place) (I₃ j))
    (a₁ : I₁ 0 k (F.start₁ (F.pub x)) { R.start₁ H with opened := some [] }
      (envOf (H.storedWords w₀ rc) (fun _ _ => none) []))
    (a₂ : I₂ 0 k (F.start₂ (F.pub x)) { R.start₂ H with opened := some [] }
      (envOf (H.storedWords w₀ rc) (fun _ _ => none) []))
    (a₃ : ∀ e₁ m₁ E₁ e₂ m₂ E₂ o₁ o₂, I₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      I₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → m₁.opened = some o₁ → m₂.opened = some o₂ →
      ∃ s₃, F.start₃ (F.pub x) e₁ e₂ = .ok s₃ ∧
        I₃ 0 k s₃ { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) } (envThird E₁ E₂))
    (fin : ∀ e₁ m₁ E₁ e₂ m₂ E₂ e₃ m₃ E₃, I₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      I₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → I₃ F.second.blocksInOrder.length k e₃ m₃ E₃ →
      F.fin x e₁ e₂ e₃ = true)
    (hv : viewsFall F f₁ f₂ f₃ x r.run.views = none) :
    (∃ e₁ e₂ e₃, r.ends = (some e₁, some e₂, some e₃)) ∧
      F.run x r.run.views.1 r.run.views.2.1 r.run.views.2.2 = true := by
  obtain ⟨n₁, n₂, n₃⟩ := fallFree_of_views h f₁ f₂ f₃ hv
  refine runC_accepts h hR hp hx hρ hsil I₁ I₂ I₃ (fallsBy f₁ F.first.blocksInOrder)
    (fallsBy f₂ F.shared.blocksInOrder) (fallsBy f₃ F.second.blocksInOrder) h₁ h₂ h₃ ?_ ?_ ?_ a₁ a₂ a₃ fin n₁ n₂ n₃
  · intro j b hj
    have e : fallsBy f₁ F.first.blocksInOrder j = fallOf f₁ b.place := by
      unfold fallsBy
      rw [hj]
    rw [e]
    exact y₁ j b hj
  · intro j b hj
    have e : fallsBy f₂ F.shared.blocksInOrder j = fallOf f₂ b.place := by
      unfold fallsBy
      rw [hj]
    rw [e]
    exact y₂ j b hj
  · intro j b hj
    have e : fallsBy f₃ F.second.blocksInOrder j = fallOf f₃ b.place := by
      unfold fallsBy
      rw [hj]
    rw [e]
    exact y₃ j b hj

end ProofFile.Honest

#print axioms ProofFile.Honest.fallsBy_succ
#print axioms ProofFile.Honest.fallFree_of_fronts
#print axioms ProofFile.Honest.fallFree_of_chain
#print axioms ProofFile.Honest.fallFree_of_views
#print axioms ProofFile.Honest.runC_accepts_views
#print axioms ProofFile.Honest.fallsBy
