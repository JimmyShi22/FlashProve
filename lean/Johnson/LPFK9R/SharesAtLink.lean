-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
LPFK9R/SharesAtLink.lean: `IM.Hands` AT THE VERY BLOCKS THAT THE
JOIN OF «the half of the table's promise that reads the verifier's state is handed on» NAMES IN ITS
SHARES for the batching kind and the frame's block behind the batching:
HandsAtLink.lean's four theorems carried by `IM.Hands.under`. Theorems.

What is said.
  `behind_under`: a block without a round whose decision is the link's runs behind the batching
    stands under the link's own block. `share_behind`: **`IM.Hands` at every such block.**
    `eq_under`, `shut_under`: the first and the third member of the closing's list (`K9.closeOf p
    Q`), retyped, stand under the kind's own blocks. `share_close0`, `share_close2`: **`IM.Hands` at
    these two.** `share_batch`: **`IM.Hands` at `K9.batch K9.atS p g` WHERE g IS THE LINK's OWN
    GATHERER** and the link's batching is that kind's at p.

Limits. AT A FREE g THE BATCHING's SHARE CANNOT BE PAID: the block runs g and writes into the state
that g returns: whatever state. So `share_batch` names the link. The premises of HandsAtLink.lean
stay, all of them. The closing's second member (the closing kind's own block) is not in this file.
Nothing on soundness.

-/
import Johnson.LPFK9R.HandsAtLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFK9.HandsAt
open VerifiableInference.Desc
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.K9 (atS Where shut)
open VerifiableInference.Desc.First (S ModelPart Numbers rowSegs rowsDue)

variable {N : Numbers} {links : List ModelPart} {ps : List Place} {E : ℕ → S → Bool} {ft k : ℕ}

/-- A block without a round whose decision is the link's runs behind the batching stands under the
link's own block. -/
theorem behind_under (Lk : Link S ProofFile.Cl) (b : Block S ProofFile.Cl) (hr : b.rounds = [])
    (hd : ∀ s rs gs, b.decide s rs gs = Lk.runBehind s) : b.UnderR Lk.behindB :=
  ⟨hr, fun s rs gs s' h => by
    rw [hd] at h
    exact h⟩

/-- **THE SHARE «behind».** -/
theorem share_behind (hfit : linkFit links ps = true) {m : ℕ} {p p' : Place}
    (hp : ps[k]? = some p) (hp' : ps[k + 1]? = some p') (hl : p.link = some m)
    (hpc : p.piece = hearN links m + 2)
    (hT : N.treesAt ps[k + 1]? = N.treesAt ps[k]?) (hM : N.msgsAt ps[k + 1]? = N.msgsAt ps[k]?)
    (Lk : Link S ProofFile.Cl) (pp : Where) (T : TwoBlocks Lk pp)
    (more : ∀ s s', IM.Yes ft Lk.behindB s s' → s.failed = none → s'.failed = none →
      IM.XK N links ps E k s = true → E (k + 1) s' = true)
    (b : Block S ProofFile.Cl) (hr : b.rounds = [])
    (hd : ∀ s rs gs, b.decide s rs gs = Lk.runBehind s) : IM.Hands N links ps E ft k b :=
  (hands_behind hfit hp hp' hl hpc hT hM Lk pp T more).under (behind_under Lk b hr hd)

/-- The closing's first member, retyped, stands under the one equation's block. -/
theorem eq_under (p : Where) (Q : First.Close.Par) (x : Block S Unit)
    (hx : (K9.closeOf p Q : List (Block S Unit))[0]? = some x) :
    (x.retype : Block S ProofFile.Cl).UnderR (K9.oneEquation (Cl := ProofFile.Cl) atS p) := by
  obtain rfl : _ = x := Option.some.inj hx
  exact ⟨rfl, fun _ _ _ _ h => h⟩

/-- The closing's third member, retyped, stands under the shutting. -/
theorem shut_under (p : Where) (Q : First.Close.Par) (x : Block S Unit)
    (hx : (K9.closeOf p Q : List (Block S Unit))[2]? = some x) :
    (x.retype : Block S ProofFile.Cl).UnderR (shut (Cl := ProofFile.Cl) p (Q.piece + 1)) := by
  obtain rfl : _ = x := Option.some.inj hx
  exact ⟨rfl, fun _ _ _ _ h => h⟩

/-- **THE SHARE «close» AT j = 0: THE ONE EQUATION.** -/
theorem share_close0 (hfit : linkFit links ps = true) {m : ℕ} {p p' : Place}
    (hp : ps[k]? = some p) (hp' : ps[k + 1]? = some p') (hl : p.link = some m)
    (hpc : p.piece = hearN links m + 3)
    (hT : N.treesAt ps[k + 1]? = N.treesAt ps[k]?) (hM : N.msgsAt ps[k + 1]? = N.msgsAt ps[k]?)
    (hat : N.rowsAt m .equation = (rowsDue N (IM.openAt links ps k) m, 1))
    (inj : ∀ m' ∈ rowSegs (IM.openAt links ps k), m' ≠ m → N.groupAt m' ≠ N.groupAt m)
    (pw : Where) (Q : First.Close.Par)
    (hg : ∀ s a, IM.XK N links ps E k s = true → atS.get? s = some a →
      N.groupAt m = a.L.check.group)
    (more : ∀ s s', IM.Yes ft (K9.oneEquation (Cl := ProofFile.Cl) atS pw) s s' → s.failed = none →
      s'.failed = none → IM.XK N links ps E k s = true → E (k + 1) s' = true)
    (x : Block S Unit) (hx : (K9.closeOf pw Q : List (Block S Unit))[0]? = some x) :
    IM.Hands N links ps E ft k (x.retype : Block S ProofFile.Cl) :=
  (hands_eq hfit hp hp' hl hpc hT hM hat inj pw (K9.oneEquation (Cl := ProofFile.Cl) atS pw)
    (fun _ _ _ _ _ h => h) hg more).under (eq_under pw Q x hx)

/-- **THE SHARE «close» AT j = 2: THE SHUTTING.** -/
theorem share_close2 (hfit : linkFit links ps = true) {m : ℕ} {p p' : Place}
    (hp : ps[k]? = some p) (hp' : ps[k + 1]? = some p') (hl : p.link = some m)
    (hpc : p.piece = hearN links m + 5)
    (hT : N.treesAt ps[k + 1]? = N.treesAt ps[k]?) (hM : N.msgsAt ps[k + 1]? = N.msgsAt ps[k]?)
    (pw : Where) (Q : First.Close.Par)
    (more : ∀ s s', IM.Yes ft (shut (Cl := ProofFile.Cl) pw (Q.piece + 1)) s s' → s.failed = none →
      s'.failed = none → IM.XK N links ps E k s = true → E (k + 1) s' = true)
    (x : Block S Unit) (hx : (K9.closeOf pw Q : List (Block S Unit))[2]? = some x) :
    IM.Hands N links ps E ft k (x.retype : Block S ProofFile.Cl) :=
  (hands_shut hfit hp hp' hl hpc hT hM pw (Q.piece + 1) (shut (Cl := ProofFile.Cl) pw (Q.piece + 1))
    (fun _ _ _ _ _ h => h) more).under (shut_under pw Q x hx)

/-- **THE SHARE «batch», AT THE LINK's OWN GATHERER.** -/
theorem share_batch (hfit : linkFit links ps = true) {m : ℕ} {p p' : Place}
    (hp : ps[k]? = some p) (hp' : ps[k + 1]? = some p') (hl : p.link = some m)
    (hpc : p.piece = hearN links m + 1)
    (hT : N.treesAt ps[k + 1]? = N.treesAt ps[k]?) (hM : N.msgsAt ps[k + 1]? = N.msgsAt ps[k]?)
    (Lk : Link S ProofFile.Cl) (pp : Where) (hbt : Lk.batch = K9.batch atS pp) (T : TwoBlocks Lk pp)
    (more : ∀ s s', IM.Yes ft Lk.batchB s s' → s.failed = none → s'.failed = none →
      IM.XK N links ps E k s = true → E (k + 1) s' = true) :
    IM.Hands N links ps E ft k (K9.batch atS pp (claimsInBy Lk.each Lk.hear Lk.order)) := by
  have e : Lk.batchB = K9.batch atS pp (claimsInBy Lk.each Lk.hear Lk.order) := by
    unfold Link.batchB
    rw [hbt]
  rw [← e]
  exact hands_batch hfit hp hp' hl hpc hT hM Lk pp T more

end LPFK9.HandsAt

#print axioms LPFK9.HandsAt.share_batch
#print axioms LPFK9.HandsAt.share_behind
#print axioms LPFK9.HandsAt.share_close0
#print axioms LPFK9.HandsAt.share_close2
