-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/TotalBehind.lean: THE PUBLIC TEST `totalIn`
(Johnson/Desc/First/Batch/FormsIn.lean) AT THE VERIFIER's STATE BEHIND AN ACCEPTING STEP OF THE
FRAME's SUB-PROTOCOL BEHIND THE BATCHING. Theorems. No text already in the library turns.

Why. `totalIn_tests` (Johnson/Desc/First/Link/Law/CoefsFit.lean) speaks at the state behind a yes of
the approximate range proof's run of self tests. The sub-protocol behind the batching runs the
link's order behind it; IN ALL THREE SORTS OF LINK THAT RUN IS THE ORDER's LAST.
  `ran_cut`: a chain of yeses along an order that ends in o: a chain along what stands in front,
    and then a yes of the run at o. (`ran_last`, Johnson/Desc/First/Link/Law/GoodFull.lean, gives
    the last yes without the chain in front.)
  `orderAfter_last`: the driver's order behind the batching ends in "K8.tests", at each sort.
  `full_runBehind`: where the link's order behind the batching ends in an entry whose run stands
    under `k8Tests nU`: the state behind a yes of `Link.runBehind` stands behind a yes of
    `k8Tests nU`, from a state at which whatever the runs in front keep still holds.
  `runBehind_of_step`: an accepting step of the sub-protocol is such a yes.
  `totalIn_runBehind`, `totalIn_behind`: **so the public test there**, from: the looks in front of
  the step; the runs in
    front keep them; `sortsB`; and the three other shares at the state behind.
Limits. That the run which a link's entry states under the name "K8.tests" stands under `k8Tests nU`
is a premise (another file's tie); so is the runs' share; so are the three other shares. Nothing on
soundness.
-/
import Johnson.Desc.First.Link.Law.CoefsFit
import Johnson.Desc.First.Driver.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS totalIn maskSeat arrayIn)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.JoinAtBlocks

/-- A chain of yeses along an order that ends in o. -/
theorem ran_cut {T : Type} (bs : List (Block T Claim)) (o : ℕ × String) :
    ∀ (pre : List (ℕ × String)) (e e₁ : T), Ran bs (pre ++ [o]) e e₁ →
      ∃ run e', ((bs[o.1]?).bind fun b => b.after.lookup o.2) = some run ∧ Ran bs pre e e' ∧
        run e' = .ok e₁
  | [], e, e₁, h => by
    cases h with
    | cons _ _ run _ e' _ hl hr ht =>
      cases ht
      exact ⟨run, e, hl, .nil e, hr⟩
  | p :: pre, e, e₁, h => by
    cases h with
    | cons _ _ run _ e' _ hl hr ht =>
      obtain ⟨run', e'', h1, h2, h3⟩ := ran_cut bs o pre e' e₁ ht
      exact ⟨run', e'', h1, .cons p pre run e e' e'' hl hr h2, h3⟩

/-- **The driver's order behind the batching ends in the run of self tests, at each sort of
link.** -/
theorem orderAfter_last (sub : First.ModelPart) :
    ∃ pre i, First.orderAfterOf sub = pre ++ [(i, "K8.tests")] := by
  cases sub
  · exact ⟨[(4, "K8.lsTail"), (2, "free-slot")], 4, rfl⟩
  · exact ⟨[(4, "K8.lsTail")], 4, rfl⟩
  · exact ⟨[(5, "K8.lsTail")], 5, rfl⟩

/-- **The state behind the runs behind the batching stands behind a yes of the run of self tests.**
Pp: whatever the runs in front keep. -/
theorem full_runBehind (Pp : S → Prop) (nU : Array ℕ) (L : Link S Claim)
    (pre : List (ℕ × String)) (oT : ℕ × String) (hord : L.orderAfter = pre ++ [oT])
    (hT : ∀ run, AtAfter L oT run → UnderAfter run (k8Tests nU))
    (hk : ∀ o' ∈ pre, ∀ run, AtAfter L o' run → ∀ e e₁, run e = .ok e₁ → Pp e → Pp e₁)
    (s s' : S) (h : L.runBehind s = .ok s') (hs : Pp s) : ∃ e, Pp e ∧ k8Tests nU e = .ok s' := by
  have hr := afterIn_ran L.hear L.orderAfter _ _ (Link.afterIn_of_runBehind h)
  rw [hord] at hr
  obtain ⟨run, e', h1, h2, h3⟩ := ran_cut L.hear oT pre _ _ hr
  exact ⟨e', ran_holds Pp L.hear pre _ _ h2 (fun o' ho' run' hl x x₁ hx hp =>
    hk o' ho' run' hl x x₁ hx hp) hs, hT run h1 _ _ h3⟩

/-- **THE PUBLIC TEST BEHIND THE RUNS BEHIND THE BATCHING.** -/
theorem totalIn_runBehind (sh : List Look) (own : List (ℕ × ℕ)) (nU : Array ℕ)
    (L : Link S Claim) (pre : List (ℕ × String)) (oT : ℕ × String)
    (hord : L.orderAfter = pre ++ [oT])
    (hT : ∀ run, AtAfter L oT run → UnderAfter run (k8Tests nU))
    (hk : ∀ o' ∈ pre, ∀ run, AtAfter L o' run → ∀ e e₁, run e = .ok e₁ →
      HasFork (LooksAre sh) e → HasFork (LooksAre sh) e₁)
    (s s' : S) (h : L.runBehind s = .ok s') (hl : HasFork (LooksAre sh) s)
    (hB : ∀ e tl, k8Tests nU e = .ok s' → e.tl? = some tl → sortsB sh tl = true)
    (a : K9.Part) (ha : atS.get? s' = some a)
    (t1 : a.F.LS.size = a.F.ns ∧ a.F.vp.size = a.F.ns ∧ a.F.mf.size = a.F.ns)
    (t2 : (maskSeat own a).isSome = true)
    (t3 : ∀ i, i < sh.length → (arrayIn own a i).isSome = true) : totalIn own s' = true := by
  obtain ⟨e, he, ht⟩ := full_runBehind (HasFork (LooksAre sh)) nU L pre oT hord hT hk s s' h hl
  exact totalIn_tests sh own nU e s' a ht ha he (fun tl => hB e tl ht) t1 t2 t3

/-- An accepting step of the frame's sub-protocol behind the batching is a yes of these runs. -/
theorem runBehind_of_step (L : Link S Claim) (ft : ℕ) (s : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (s' : S) (k : ℕ) (h : L.behindB.step ft s rs cols = .ok (s', k)) :
    L.runBehind s = .ok s' := by
  obtain ⟨rs', gs, hd⟩ := step_decide L.behindB _ _ _ _ _ k h
  obtain ⟨cls, hy⟩ := (behind_isMoves atS L).dec _ _ _ _ hd
  obtain ⟨u, c, c', ⟨hq, _⟩, ⟨rfl, _⟩, _⟩ := hy
  exact hq

/-- **THE PUBLIC TEST BEHIND AN ACCEPTING STEP OF THE FRAME's SUB-PROTOCOL BEHIND THE BATCHING.** -/
theorem totalIn_behind (sh : List Look) (own : List (ℕ × ℕ)) (nU : Array ℕ) (L : Link S Claim)
    (pre : List (ℕ × String)) (oT : ℕ × String) (hord : L.orderAfter = pre ++ [oT])
    (hT : ∀ run, AtAfter L oT run → UnderAfter run (k8Tests nU))
    (hk : ∀ o' ∈ pre, ∀ run, AtAfter L o' run → ∀ e e₁, run e = .ok e₁ →
      HasFork (LooksAre sh) e → HasFork (LooksAre sh) e₁)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (k : ℕ)
    (h : L.behindB.step ft s rs cols = .ok (s', k)) (hl : HasFork (LooksAre sh) s)
    (hB : ∀ e tl, k8Tests nU e = .ok s' → e.tl? = some tl → sortsB sh tl = true)
    (a : K9.Part) (ha : atS.get? s' = some a)
    (t1 : a.F.LS.size = a.F.ns ∧ a.F.vp.size = a.F.ns ∧ a.F.mf.size = a.F.ns)
    (t2 : (maskSeat own a).isSome = true)
    (t3 : ∀ i, i < sh.length → (arrayIn own a i).isSome = true) : totalIn own s' = true :=
  totalIn_runBehind sh own nU L pre oT hord hT hk s s' (runBehind_of_step L ft s rs cols s' k h) hl
    hB a ha t1 t2 t3

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.ran_cut
#print axioms VerifiableInference.Desc.LinkJoin.orderAfter_last
#print axioms VerifiableInference.Desc.LinkJoin.full_runBehind
#print axioms VerifiableInference.Desc.LinkJoin.totalIn_runBehind
#print axioms VerifiableInference.Desc.LinkJoin.runBehind_of_step
#print axioms VerifiableInference.Desc.LinkJoin.totalIn_behind
