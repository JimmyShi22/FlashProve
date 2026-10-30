-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/PromiseConds.lean: CONDITIONAL. One definition of a
hypothesis's form, and three statements with their proofs.

What is here. THE HYPOTHESIS `K4Promise` (Law/Behind.lean) AT THE FIRST
CHAIN's THREAD (`Letters.thread`, Honest/Thread/First.lean), general in that structure's fields,
brought down to conditions on the table of places, its counts and the promise's tests AT TWO STATES.
K4 is the sub-protocol of the feed-forward layers' own rounds.

  `K4Conds L b m pl pl' par Fence`   the member stands at piece 3 of the layers' segment m; the next
      place is piece 4 of that segment, with as many trees and messages in front; the meaning's
      `inOrder` and `held` pass where `Rest` holds (Johnson/Desc/First/K4/ReadsAtS.lean: seven
      fields of the state, four readers of the open segment and four of its fields stay); the public
      items' tests pass from s to s' where the promise holds at s without a mark, the sub-protocol
      has left what `KeptAtS` says, and Fence holds of s; what the open public items say beside
      their tests passes across `KeptAtS`.
  `rest_of_kept`   `Rest` out of `KeptAtS` (Johnson/Road/K4/KeptAtS.lean).
  `shape_kept`   the state's book-keeping behind, from `KeptAtS`.
  `k4Promise_of`   **`K4Promise L.thread b par Fence`, under `K4Conds`.**

Called. The library's `onAt_step_quiet` (Johnson/Desc/First/PromiseRides.lean), clause by clause;
`quiet_k4` (Johnson/Road/K4/K4PromiseBehind.lean); `openSets_succ` and `pubSets_succ`
(Johnson/Desc/First/BordersSucc.lean).

Kin. `K4Conds` goes after the library's `K4Keeps`, and `k4Promise_of` after its `k4_promise_behind`
(both Johnson/Road/K4/K4PromiseBehind.lean), which speak at a piece's yes and at any meaning: nine
fields bear the same names. What parts: `AtK4` is a field here; the pair of states is any under
`KeptAtS` (for inOrder and held: under `Rest`, without that structure's fence); pub has the
parameter Fence besides; pubP asks neither the promise nor «no mark»; its fields dec, below, shown
and noColl have no like here: at the meaning adapted to the honest side (`honest`,
Honest/Thread/First.lean) decodes, shown and noColl are true. `shape_kept` goes after the library's
`shape_behind` (Johnson/Road/K4/K4PromiseBehind.lean), which is typed at a piece's yes: the same
steps, at `KeptAtS`. The general law is `shape_step` (Johnson/Desc/First/Link/Law/RbDef.lean, of
other writers): the test on the state's book-keeping passes from a place to the next where the
state's and the table's stands and the link are the same, and either nothing waits behind or the
table lets the next place wait; `IM.shape_kept` (Johnson/IMR/GrownQuiet.lean, of other writers) is
that law under `StandKept`. Neither is called here. Two more theorems named `shape_behind` say the
like elsewhere on the table: from piece 4 to piece 5 of the head's segment
(Johnson/Desc/Sound/K6Second.lean), and at the chain's end (Johnson/Desc/K13/Law/AtTable.lean).
`heard_reads` (Johnson/Desc/First/K4/ReadsAtS.lean) ends in `Rest` from a yes of the decision;
`rest_of_kept` takes it out of `KeptAtS`, as `behind_of_kept` (Law/Hears.lean) does within its
proof.

Not shown here. THAT THE CONDITIONS HOLD AT ANY VALUE OF THE FIELDS: `K4Conds` is a hypothesis; its
fields pub and pubP hold most of the work. This file gives no example of it; `k4Conds_all`
(Law/PromiseAll.lean) has it at the library's composed meaning, under
hypotheses of its own. Following import lines, and stopping unopened at every module under
Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/ and at every module whose name begins
Cb.Bridge, its imports reach 2 modules under Johnson/Bridge/ and none of the others; what lies
behind the two is not counted; one of the modules that it reaches has RecCompile in its name
(Johnson.TypedOracleCompiler.RecCompile.Bcs, with the library's Johnson/Road/K4/K4PromiseBehind.lean). Nothing on
soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Behind
import Johnson.Desc.ProofFile.Honest.Thread.First
import Johnson.Road.K4.K4PromiseBehind
import Johnson.Desc.First.BordersSucc

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4 (Par Rest)
open OnBytes.Road.K4 (KeptAtS AtK4 quiet_k4)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S ModelPart onAt openSets pubSets start pubHeld pubStep pubRowM
  stepOpen rowOf shapeAt standOf standAt bookAt onAt_step_quiet openSets_succ pubSets_succ)
open ProofFile.Honest.FirstThread (Letters noStrs)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok M : Type}

/-- **The conditions on the table of places, its counts and the promise's tests, at two states.** A
hypothesis's form. Nothing is claimed by the definition. -/
structure K4Conds (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M) (b m : Nat) (pl pl' : Place)
    (par : Par) (Fence : S → Prop) : Prop where
  at_ : AtK4 L.links L.ps b m pl
  next : L.ps[b + 1]? = some pl'
  link' : pl'.link = some m
  piece' : pl'.piece = 4
  trees : L.N.treesAt (some pl') = L.N.treesAt (some pl)
  msgs : L.N.msgsAt (some pl') = L.N.msgsAt (some pl)
  inOrder : ∀ (z : P) s s', Rest s s' → L.mgP.inOrder (z, s) = true → L.mgP.inOrder (z, s') = true
  held : ∀ (z : P) s s' (t j : Nat), Rest s s' → L.mgP.held t j (z, s) = true →
    L.mgP.held t j (z, s') = true
  pub : ∀ (z : P) s s', L.thread.formP b (z, s) → s.failed = none → KeptAtS par s s' → Fence s →
    pubHeld L.mgP ((openSets L.links L.ps (start L.links))[b]?.getD [])
      ((pubSets L.mgP.more L.links L.ps)[b]?.getD []) (z, s) = true →
    pubHeld L.mgP
      (stepOpen ((openSets L.links L.ps (start L.links))[b]?.getD []) (rowOf L.links pl))
      (pubStep ((pubSets L.mgP.more L.links L.ps)[b]?.getD []) (pubRowM L.mgP.more L.links pl))
      (z, s') = true
  pubP : ∀ (z : P) s s', KeptAtS par s s' →
    (∀ x ∈ (pubSets L.mgP.more L.links L.ps)[b]?.getD [], L.mgP.pubP x (z, s)) →
    ∀ x ∈ pubStep ((pubSets L.mgP.more L.links L.ps)[b]?.getD [])
      (pubRowM L.mgP.more L.links pl), L.mgP.pubP x (z, s')

/-- What `KeptAtS` holds on the fields that stay. -/
theorem rest_of_kept {par : Par} {s s' : S} (K : KeptAtS par s s') : Rest s s' := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hR, _⟩ := K
  exact hR

/-- **The state's book-keeping behind.** -/
theorem shape_kept {links : List ModelPart} {ps : List Place} {k m : Nat} {pl pl' : Place} {par : Par}
    (H : AtK4 links ps k m pl) (hl : pl'.link = some m) (hp : pl'.piece = 4) {s s' : S}
    (K : KeptAtS par s s') (hs : shapeAt links (some pl) s = true) :
    shapeAt links (some pl') s' = true := by
  obtain ⟨al, _, _, _, ha, _, _, _, _, _, hro, _, hR, _⟩ := K
  obtain ⟨a', ha', _⟩ := hR.here al ha
  have s1 : standOf s' = .link .layers := by
    unfold standOf
    rw [ha']
  have s2 : standAt links pl' = .link .layers := by
    simp [standAt, hl, H.sub, hp]
  have s3 : s'.noneWaits = true := by
    unfold S.noneWaits
    rw [hro]
  simp only [shapeAt, Bool.and_eq_true] at hs ⊢
  refine ⟨⟨by rw [s1, s2]; rfl, by rw [s3]; rfl⟩, ?_⟩
  rw [hR.link, hl, ← H.link]
  exact hs.2

/-- **The thread's form and promise pass K4's accepting decision**, under the conditions. -/
theorem k4Promise_of {L : Letters Bk VerifiableInference.Desc.Claim W₀ Rc Xi Tr X P Cells Tok M}
    {b m : Nat}
    {pl pl' : Place} {par : Par} {Fence : S → Prop} (K : K4Conds L b m pl pl' par Fence) :
    K4Promise L.thread b par Fence := by
  intro z s s' hf hP hK hFe
  have hR := rest_of_kept hK
  have hu : s.failed = none := by
    have e : s.failed.isNone = true := hf
    exact Option.isNone_iff_eq_none.mp e
  refine ⟨?_, ?_⟩
  · show s'.failed.isNone = true
    rw [hR.failed, hu]
    rfl
  · have ha : onAt L.N L.mgP L.links L.ps[b]? ((openSets L.links L.ps (start L.links))[b]?.getD [])
        ((pubSets L.mgP.more L.links L.ps)[b]?.getD []) (z, s) noStrs := hP
    have hB := (ha.2.resolve_left fun h => h hu).1
    simp only [Bool.and_eq_true] at hB
    show onAt L.N L.mgP L.links L.ps[b + 1]?
      ((openSets L.links L.ps (start L.links))[b + 1]?.getD [])
      ((pubSets L.mgP.more L.links L.ps)[b + 1]?.getD []) (z, s') noStrs
    rw [openSets_succ L.links L.ps (start L.links) b pl K.at_.here,
      pubSets_succ L.mgP.more L.links L.ps b pl K.at_.here]
    refine onAt_step_quiet L.N L.mgP L.links L.ps[b]? L.ps[b + 1]? _ _ _ (rowOf L.links pl) (z, s)
      (z, s') noStrs noStrs (quiet_k4 K.at_) ha (fun hm => absurd hu hm) (fun _ => trivial)
      (fun _ => ?_) (by rw [hR.st]) (by rw [hR.book]) (K.inOrder z s s' hR)
      (fun _ => K.pub z s s' hP hu hK hFe) (fun _ hk => ?_)
      (fun _ => K.pubP z s s' hK) (fun x _ => K.held z s s' x.1 x.2 hR)
      (fun _ _ _ => trivial) (fun _ _ _ => trivial)
    · rw [K.next]
      have b1 := hB.1.1.1.1.1
      rw [K.at_.here] at b1
      exact shape_kept K.at_ K.link' K.piece' hK b1
    · rw [K.at_.here] at hk
      rw [K.next]
      simp only [bookAt, Bool.and_eq_true] at hk ⊢
      rw [hR.book, hR.st, K.trees, K.msgs]
      exact hk

end ProofFile.Honest.K4


#print axioms ProofFile.Honest.K4.K4Conds
#print axioms ProofFile.Honest.K4.rest_of_kept
#print axioms ProofFile.Honest.K4.shape_kept
#print axioms ProofFile.Honest.K4.k4Promise_of
