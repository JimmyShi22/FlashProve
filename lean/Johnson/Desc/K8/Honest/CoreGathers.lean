-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/CoreGathers.lean: THE GATHERER OF A SEGMENT's CLAIMS, WHOLE, LEAVES THE TEN
FIELDS OF THE LEDGER THAT `SameCore` (Johnson/Desc/K8/Honest/SameCore.lean) NAMES: AT ALL THREE
SORTS OF SEGMENT, UNDER THE TIES ON THEIR RUNS. Statements and proofs. No prover. Lemmas; none of
the library's goals.

  `CoreOk L os`   each run that L's blocks state at an entry of os stands under a run with
      `KeepsCore` (Johnson/Desc/K8/Honest/CoreRuns.lean)
  **`core_along`**   so along the runs of os: the last clause of `pre_one` and `post_one`
      (Johnson/Desc/K8/Honest/GathersPlain.lean), said of `SameCore`
  **`core_of_order`**   L's order is pre, "K8.equations", post; `CoreOk` at pre and post; the run at
      "K8.equations" stands under the smallness test's own: where the gatherer returns from t and
      the batching's lens finds a part at t, it finds one at the state returned, and the ledger
      there has the ten fields of the ledger at t
  **`core_layers`**, **`core_att`**, **`core_head`**   that, under each sort's ties and order: the
      premises of `gathers_layers_plain`, `gathers_att` (FallAtt.lean), `gathers_head`
      (FallHead.lean) but for the two on what the state holds
Limits. Which ten fields, and which five are not carried (vp, mf, gotF, owed, next): SameCore.lean's
head. The ties are premises. That the gatherer returns is not said. Nothing on the claims.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.CoreRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.Kinds.Head (callerReaders planesAt)

/-- Each run at an entry of os stands under a run that leaves the ten fields. -/
def CoreOk (L : Link S Claim) (os : List (Nat × String)) : Prop :=
  ∀ o ∈ os, ∀ run, LinkJoin.At L o run → ∃ f, LinkJoin.Under run f ∧ KeepsCore f

/-- **Along the runs of a list of entries.** -/
theorem core_along (L : Link S Claim) : ∀ (os : List (Nat × String)), CoreOk L os →
    ∀ (x z : List Claim × S), runAll L.each L.hear os x = .ok z →
    ∀ a, K9.atS.get? x.2 = some a → ∃ b, K9.atS.get? z.2 = some b ∧ SameCore a.F b.F
  | [], _, x, z, h => by
    obtain rfl : x = z := Except.ok.inj h
    exact fun a ha => ⟨a, ha, SameCore.refl _⟩
  | o :: os, H, x, z, h => by
    obtain ⟨w, g1, g2⟩ := bind_ok h
    obtain ⟨run, c, e, hat, hy, rfl⟩ := step_ok g1
    obtain ⟨f, hu, hp⟩ := H o (by simp) run hat
    have hf := hu _ _ _ _ hy
    intro a ha
    obtain ⟨b, hb, s1⟩ := hp _ _ _ a hf ha
    obtain ⟨b2, hb2, s2⟩ :=
      core_along L os (fun o' ho' => H o' (List.mem_cons_of_mem _ ho')) _ z g2 b hb
    exact ⟨b2, hb2, s1.trans s2⟩

/-- **The gatherer, whole.** -/
theorem core_of_order (L : Link S Claim) (i : Nat) (pre post : List (Nat × String))
    (hord : L.order = pre ++ (i, "K8.equations") :: post) (Hpre : CoreOk L pre)
    (Hpost : CoreOk L post)
    (tEq : ∀ run, LinkJoin.At L (i, "K8.equations") run → LinkJoin.Under run K9L.k8Run.2)
    (t e : S) (cls : List Claim) (hg : claimsInBy L.each L.hear L.order t = .ok (cls, e))
    (x : K9.Part) (hx : K9.atS.get? t = some x) :
    ∃ y, K9.atS.get? e = some y ∧ SameCore x.F y.F := by
  rw [hord, claimsInBy_eq, runAll_append] at hg
  obtain ⟨⟨fr, e₁⟩, g1, g2⟩ := bind_ok hg
  obtain ⟨w, g3, g4⟩ := bind_ok (show (claimsInStep L.each L.hear (fr, e₁) (i, "K8.equations")).bind
    (runAll L.each L.hear post) = .ok (cls, e) from g2)
  obtain ⟨run, k8, e₂, hat, hy, rfl⟩ := step_ok g3
  obtain ⟨F, tl, funs, tl', F₂, b2, b3, b4, b5, b6⟩ := K9L.k8Run_ok _ _ _ _ (tEq run hat _ _ _ _ hy)
  obtain ⟨x₁, hx₁, s₁⟩ := core_along L pre Hpre _ _ g1 x hx
  obtain rfl : x₁.F = F := Option.some.inj ((K9.get_fork _ _ hx₁).symm.trans b2)
  obtain ⟨x₂, hx₂, hF₂, -⟩ := K9L.get_put e₁ x₁ hx₁ tl' F₂
  rw [b6] at g4
  obtain ⟨y, hy', s₃⟩ := core_along L post Hpost _ _ g4 x₂ hx₂
  have s₂ : SameCore x₁.F x₂.F := by
    rw [hF₂]
    exact SameCore.ofSide (eq_side b5)
  exact ⟨y, hy', (s₁.trans s₂).trans s₃⟩

/-- **At a feed-forward segment.** -/
theorem core_layers (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat)
    (ties : LinkJoin.LayersTies L p4 nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run K9.objectsDigits)
    (hord : L.order = orderOf .layers) (t e : S) (cls : List Claim)
    (hg : claimsInBy L.each L.hear L.order t = .ok (cls, e)) (x : K9.Part)
    (hx : K9.atS.get? t = some x) : ∃ y, K9.atS.get? e = some y ∧ SameCore x.F y.F := by
  refine core_of_order L 4
    [(1, "objects"), (1, "guests"), (2, "front"), (6, "objects"), (6, "guests")] [(2, "back")]
    (by rw [hord]; rfl) ?_ ?_ ties.tEq t e cls hg x hx
  · intro o ho run hat
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, tC run hat, core_objects _⟩
    · exact ⟨_, ties.tGuests 1 (by simp) run hat, core_idle⟩
    · obtain ⟨r, l, u⟩ := ties.tFront run hat
      exact ⟨r, u, core_front p4 r l⟩
    · exact ⟨_, tD run hat, core_objects _⟩
    · exact ⟨_, ties.tGuests 6 (by simp) run hat, core_idle⟩
  · intro o ho run hat
    obtain rfl : o = (2, "back") := List.mem_singleton.1 ho
    obtain ⟨r, l, u⟩ := ties.tBack run hat
    exact ⟨r, u, core_behind p4 r l⟩

/-- **At an attention segment.** -/
theorem core_att (L : Link S Claim) (c : P.ParC) (nU : Array Nat)
    (ties : LinkJoin.AttTies L c nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run K9.objectsDigits)
    (tJ : ∀ run, LinkJoin.At L (2, "join") run →
      LinkJoin.Under run (K9.joinCalls (P.keysOfK (P.seatCO c) c)))
    (tP : ∀ run, LinkJoin.At L (1, "planes") run →
      ∃ lm, LinkJoin.Under run (K9.planesCalls lm (P.readersOfK (P.seatCO c) c)))
    (hord : L.order = orderOf .attention) (t e : S) (cls : List Claim)
    (hg : claimsInBy L.each L.hear L.order t = .ok (cls, e)) (x : K9.Part)
    (hx : K9.atS.get? t = some x) : ∃ y, K9.atS.get? e = some y ∧ SameCore x.F y.F := by
  refine core_of_order L 4 attPre [] (by rw [hord]; rfl) ?_ (fun _ ho => nomatch ho) ties.tEq
    t e cls hg x hx
  intro o ho run hat
  simp only [attPre, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨_, tC run hat, core_objects _⟩
  · exact ⟨_, ties.tGuests 1 (by simp) run hat, core_idle⟩
  · exact ⟨_, ties.tFirst run hat, core_first c⟩
  · exact ⟨_, ties.tKeys run hat, core_keys c⟩
  · exact ⟨_, tJ run hat, core_join _⟩
  · exact ⟨_, ties.tSecond run hat, core_second c⟩
  · obtain ⟨lm, u⟩ := tP run hat
    exact ⟨_, u, core_planes lm _⟩
  · exact ⟨_, tD run hat, core_objects _⟩
  · exact ⟨_, ties.tGuests 6 (by simp) run hat, core_idle⟩

/-- **At the head's segment.** -/
theorem core_head (L : Link S Claim) (hS : Model.Head.Shape) (iU3 l piece : Nat)
    (p6 : Kinds.Head.Par) (nU : Array Nat) (ties : LinkJoin.HeadTies L hS iU3 l piece p6 nU)
    (tC : ∀ run, LinkJoin.At L (2, "objects") run → LinkJoin.Under run K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (7, "objects") run → LinkJoin.Under run K9.objectsDigits)
    (tP : ∀ run, LinkJoin.At L (2, "planes") run →
      ∃ lm, LinkJoin.Under run (K9.planesCalls lm (callerReaders (planesAt iU3))))
    (hord : L.order = orderOf .head) (t e : S) (cls : List Claim)
    (hg : claimsInBy L.each L.hear L.order t = .ok (cls, e)) (x : K9.Part)
    (hx : K9.atS.get? t = some x) : ∃ y, K9.atS.get? e = some y ∧ SameCore x.F y.F := by
  refine core_of_order L 5 headPre headPost (by rw [hord]; rfl) ?_ ?_ ties.tEq t e cls hg x hx
  · intro o ho run hat
    simp only [headPre, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, tC run hat, core_objects _⟩
    · exact ⟨_, ties.tGuests 2 (by simp) run hat, core_idle⟩
    · obtain ⟨r, lr, u⟩ := ties.tK6 "norm" (by simp) run hat
      exact ⟨r, u, core_k6 hS iU3 l piece p6 "norm" r lr⟩
    · exact ⟨_, ties.tJoin run hat, core_join _⟩
    · obtain ⟨r, lr, u⟩ := ties.tK6 "policy" (by simp) run hat
      exact ⟨r, u, core_k6 hS iU3 l piece p6 "policy" r lr⟩
    · obtain ⟨lm, u⟩ := tP run hat
      exact ⟨_, u, core_planes lm _⟩
    · exact ⟨_, tD run hat, core_objects _⟩
    · exact ⟨_, ties.tGuests 7 (by simp) run hat, core_idle⟩
  · intro o ho run hat
    simp only [headPost, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · obtain ⟨r, lr, u⟩ := ties.tK6 "logits" (by simp) run hat
      exact ⟨r, u, core_k6 hS iU3 l piece p6 "logits" r lr⟩
    · exact ⟨_, ties.tMerge run hat, core_merge⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.core_along
#print axioms VerifiableInference.Desc.First.K8.Honest.core_of_order
#print axioms VerifiableInference.Desc.First.K8.Honest.core_layers
#print axioms VerifiableInference.Desc.First.K8.Honest.core_att
#print axioms VerifiableInference.Desc.First.K8.Honest.core_head
