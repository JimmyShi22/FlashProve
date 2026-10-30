-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Honest/Law/BehindKept.lean: THE NINE PUBLIC TESTS THAT ARE OPEN ON BOTH SIDES OF THE
SUB-PROTOCOL "the output head's own rounds" (K6) STAY TRUE ACROSS A YES OF ITS BARE BLOCK's
DECISION; and what the item "leftOn" says behind, from what "left" says in front. AT A STATE;
general in the composed public tests' data and in the test beneath them. EVERY THEOREM IS
CONDITIONAL.

  `forks_blockAt`      the state behind written out, with the two open ledgers
  `kept_ledger_free`   ledger m and freeAbove m
  `sameOn_blockAt`, `kept_four_at`   linkFresh m, "frame.sentIs" at m, indexIs, indexThere
  `kept_trees_at`      "ledger.treesAre" at m
  `kept_lookOut_at`    lookOut m pc, at a piece of the sort "the calls"
  `kept_objects_at`    formsInT m 3 "objects"
  `leftOn_at`          what "leftOn" says

WHY IT IS TYPED. The library has each of these at a piece of the proof of soundness
(Johnson/Desc/Kinds/Law/K6LedgerAt.lean, K6PubKept.lean, K6PubMore.lean, K6ObjectsKept.lean,
K6PubSentences.lean): their statements take the piece's yes. The honest side has a yes of the block.
One of them the library also has at the bare sub-protocol's decision: where that decision accepts,
`k6_trees` (Johnson/Desc/First/Link/Law/TreesRide.lean) gives `KeepsTrees`, the premise that
`pubAll_treesAre_keeps` takes; it is not called here. WHAT LIES BENEATH THESE STATEMENTS IS CALLED
AS IT LIES: `blockAt_freeAbove`, `sized_iff` (Law/GrowsAt.lean); `rides_of_B`
(Johnson/Desc/First/PubFoot.lean); `blockAt_trees` (Law/KeepsTrees.lean) with
`pubAll_treesAre_keeps` (Johnson/Desc/First/Link/Law/TreesRide.lean); `blockAt_takes`
(Law/TakesAt.lean) with `k3OnOut_takes` (Law/K6PubMore.lean); `blockAt_later` (Law/KeepsAt.lean)
with `kept_on` (Law/K6ObjectsKept.lean) and `readers_kept` (Law/K6RidersAtMgAll.lean);
`leftOn_of_kept` (Law/K6Makes.lean); `wellLaid_of_sized` (Law/HeadLedgerMade.lean); `segAt_head`
(Law/K6RidersAtMgAll.lean); `ledgers_blockAt` (Honest/Law/Keeps.lean). The glue follows the
library's own proofs at a piece, line by line. Not so in `kept_trees_at`: the library's `kept_trees`
(Law/K6PubKept.lean) goes by `blockOf_trees` and an unfolding.

A near twin of `leftOn_at`: `leftOn_below` (Law/K6Makes.lean): the same conclusion at a state, from
a yes of the strict reading of the block and all that the law asks of the state in front.
`leftOn_at` asks less: that the bare sub-protocol's decision accepts, and that the ledger in front
has its sizes; the second follows from what "left" says in front (`left_says`, Law/K6LeftSays.lean,
which is not among what this file imports): it is asked twice. Relatives of `forks_blockAt`:
`ledgers_blockAt` (Honest/Law/Keeps.lean), which it calls and which calls `Came.decide_record`
(Law/RowPromise.lean); `below_ledgers` (Law/PlanesArm.lean).

Limits. No yes is shown. Modules under lean/Johnson/Goal/ are among what this file imports:
it imports no module of that folder by name and calls nothing that is declared there: they lie
beneath the library's files that it calls. Nothing on any property.

-/
import Johnson.Desc.K6.Honest.Law.Keeps
import Johnson.Desc.Kinds.Law.GrowsAt
import Johnson.Desc.Kinds.Law.K6PubMore
import Johnson.Desc.Kinds.Law.K6ObjectsKept
import Johnson.Desc.Kinds.Law.K6Makes
import Johnson.Desc.Kinds.Law.HeadLedgerMade
import Johnson.Desc.First.Link.Law.TreesRide
import Johnson.Desc.First.PubFoot

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Honest
open OnBytes.Model (Fork)
open OnBytes.PscRun (Later Sized)
open VerifiableInference.Desc (Link Claim)
open VerifiableInference.Desc.First (S HeadOwn Pub PubData pubAll SameOn ledgerB)
open VerifiableInference.Desc.Kinds.Head.Law (Takes k6Silent)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (ObjectsStates ObjectsBack kept_on readers_kept
  segAt_head)
open VerifiableInference.Desc.K9 (readersOfLink statesOfLink formsInT)

section
variable (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) {s s' : S} {rs : List Fmt.RoundView}
  {gs : List (List (Nat × List UInt64))}
  (hd : (blockAt h iU3 work l).decide s rs gs = .ok s')
  {P : Type} (D : PubData) (base : Pub → P × S → Bool) (z : P)

include hd

/-- The state behind a yes written out, with the two open ledgers. CONDITIONAL: the yes; so all that
follow. -/
theorem forks_blockAt : ∃ (o : HeadOwn) (F1 : Fork) (X : OnBytes.Model.Head.Heard)
    (Q : OnBytes.Model.Psc), s.here = .head o ∧ o.opened = true ∧
      s' = { s with here := .head { o with F := F1, x := some X, squaresP := some Q } } ∧
      s.fork? = some o.F ∧ s'.fork? = some F1 := by
  obtain ⟨o, F1, X, Q, ho, hop, _, hs', _, _⟩ := ledgers_blockAt h iU3 work l hd
  refine ⟨o, F1, X, Q, ho, hop, hs', ?_, ?_⟩
  · simp [S.fork?, ho, hop]
  · rw [hs']
    simp [S.fork?, hop]

/-- **ledger m and freeAbove m stay true.** CONDITIONAL: both in front. -/
theorem kept_ledger_free (m : Nat) (hL : pubAll D base (.ledger m) (z, s) = true)
    (hf : pubAll D base (.freeAbove m) (z, s) = true) :
    pubAll D base (.ledger m) (z, s') = true ∧ pubAll D base (.freeAbove m) (z, s') = true := by
  rw [First.pubAll_ledger] at hL ⊢
  rw [First.pubAll_freeAbove] at hf ⊢
  revert hf
  cases hn : D.nsOf m with
  | none =>
    intro hf
    cases hf
  | some n =>
    intro hf
    exact Law.blockAt_freeAbove h iU3 work l n s s' rs gs hd hL hf

/-- What five of the library's readers of the state read is as it was. -/
theorem sameOn_blockAt : SameOn D [.st, .out, .frame, .link, .tl] s s' := by
  obtain ⟨o, F1, X, Q, ho, _, e, _, _⟩ := forks_blockAt h iU3 work l hd
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · show s'.st = s.st
    rw [e]
  · show s'.out = s.out
    rw [e]
  · show s'.check.frame = s.check.frame
    rw [e]
  · show s'.link? = s.link?
    rw [e]
    unfold First.S.link?
    rw [ho]
  · show s'.tl? = s.tl?
    rw [e]
    unfold First.S.tl?
    rw [ho]

/-- **linkFresh m, "frame.sentIs" at m, indexIs and indexThere stay true.** CONDITIONAL: hb: the
test beneath does not read where the chain stands. -/
theorem kept_four_at (m : Nat)
    (hb : ∀ (j : Pub) (t : S) w, base j (z, { t with here := w }) = base j (z, t)) (i : Pub)
    (hi : i ∈ [Pub.linkFresh m, .more (some m) "frame.sentIs", .indexIs, .indexThere])
    (ht : pubAll D base i (z, s) = true) : pubAll D base i (z, s') = true := by
  obtain ⟨o, F1, X, Q, _, _, e, _, _⟩ := forks_blockAt h iU3 work l hd
  exact First.rides_of_B D base [.st, .out, .frame, .link, .tl] _ rfl z s s'
    (sameOn_blockAt h iU3 work l hd D) (fun j _ => by rw [e]; exact hb j s _) i hi ht

/-- **"ledger.treesAre" at m stays true.** -/
theorem kept_trees_at (m : Nat)
    (ht : pubAll D base (.more (some m) "ledger.treesAre") (z, s) = true) :
    pubAll D base (.more (some m) "ledger.treesAre") (z, s') = true := by
  obtain ⟨o, F1, X, Q, _, _, _, hF, hG⟩ := forks_blockAt h iU3 work l hd
  refine LinkJoin.pubAll_treesAre_keeps D base z m (fun G hGs => ⟨F1, hG, ?_⟩) ht
  have et := Law.blockAt_trees h iU3 work l s s' rs gs hd
  have e1 : (seatAt h iU3).ledger s = G := by
    show s.fork?.getD {} = G
    rw [hGs]
    rfl
  have e2 : (seatAt h iU3).ledger s' = F1 := by
    show s'.fork?.getD {} = F1
    rw [hG]
    rfl
  rw [e1, e2] at et
  exact et

/-- **lookOut m pc stays true**, at a piece of the sort "the calls". CONDITIONAL: the sort; the
ledger in front has its sizes (which the test in front says too). -/
theorem kept_lookOut_at (m pc : Nat) (hsort : First.Look.k3SortAt D.d3.X m pc = some false)
    (hL : ledgerB s = true) (ht : pubAll D base (.lookOut m pc) (z, s) = true) :
    pubAll D base (.lookOut m pc) (z, s') = true := by
  obtain ⟨o, F1, X, Q, ho, _, e, hF, hG⟩ := forks_blockAt h iU3 work l hd
  rw [First.pubAll_lookOut D base m pc false hsort] at ht ⊢
  unfold First.Look.lookOutC at ht ⊢
  cases hp : First.Look.placeAt D.d3.X m false with
  | none =>
    rw [hp] at ht
    cases ht
  | some p =>
    rw [hp] at ht
    have ht' : K3.k3OnOut p s = true := ht
    show K3.k3OnOut p s' = true
    have hS : Sized ((seatAt h iU3).ledger s) := by
      show Sized (s.fork?.getD {})
      rw [hF]
      exact (Law.sized_iff hF).1 hL
    obtain ⟨t, _, T⟩ := Law.blockAt_takes h iU3 work l s s' rs gs hS hd
    have T' : Takes o.F F1 t := by
      have e1 : (seatAt h iU3).ledger s = o.F := by
        show s.fork?.getD {} = o.F
        rw [hF]
        rfl
      have e2 : (seatAt h iU3).ledger s' = F1 := by
        show s'.fork?.getD {} = F1
        rw [hG]
        rfl
      rw [e1, e2] at T
      exact T
    refine Law.k3OnOut_takes p s s' o.F F1 t hF hG ?_ T' ht'
    unfold K3.heardAt
    rw [e]
    unfold First.S.tl? First.S.lookHeard?
    rw [ho]

/-- **formsInT m 3 "objects" stays true.** CONDITIONAL: the runs' readers at the segment are the
link's, with the silent reader in the hole; which runs stand under the name; two facts on the link's
list of rounds; the ledger in front has its sizes; no row that the lookup on the calls keeps names
an entry. -/
theorem kept_objects_at (m : Nat) {Lk : Link S Claim} {P8 : K8.ReadsQuiet.PH}
    {small : S → Option K9.Read}
    (hreaders : D.Rd m = readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk)
    (hobj : D.runs m 3 "objects" = [(2, "objects"), (2, "guests")])
    (hruns : ObjectsStates (statesOfLink Lk) 2) (hback : ObjectsBack (statesOfLink Lk) 2)
    (hL : ledgerB s = true)
    (hbare : ∀ g, s.lookHeard? = some g → ∀ f ∈ g.rows.toList, f.ents = #[])
    (ht : pubAll D base (.formsInT m 3 "objects") (z, s) = true) :
    pubAll D base (.formsInT m 3 "objects") (z, s') = true := by
  obtain ⟨o, F1, X, Q, ho, hop, e, hF, hG⟩ := forks_blockAt h iU3 work l hd
  have hL' : Later o.F F1 := by
    have h0 := Law.blockAt_later h iU3 work l s s' rs gs hd
    have e1 : (seatAt h iU3).ledger s = o.F := by
      show s.fork?.getD {} = o.F
      rw [hF]
      rfl
    have e2 : (seatAt h iU3).ledger s' = F1 := by
      show s'.fork?.getD {} = F1
      rw [hG]
      rfl
    rw [e1, e2] at h0
    exact h0
  have hSz : Sized o.F := (Law.sized_iff hF).1 hL
  rw [First.pubAll_formsInT] at ht ⊢
  have hin : ∀ p ∈ D.runs m 3 "objects",
      formsInT (D.Rd m) (D.N.sent m 0) p.1 p.2 s = true :=
    fun p hp => List.all_eq_true.1 ht p hp
  obtain ⟨g, hg⟩ : ∃ g, s.lookHeard? = some g := by
    have h2 := hin (2, "objects") (by rw [hobj]; simp)
    rw [hreaders] at h2
    unfold formsInT at h2
    rw [segAt_head s o ho hop] at h2
    cases e2 : (readersOfLink ⟨small, k6Silent P8 (statesOfLink Lk)⟩ Lk).forms 2 "objects" s with
    | none =>
      rw [e2] at h2
      exact absurd h2 Bool.false_ne_true
    | some R =>
      have k0 := readers_kept hruns P8 small "objects" (Or.inl rfl) s R e2
      simp only [Law.AtTable.keptOf, if_true] at k0
      obtain ⟨g, hg, _⟩ := Option.map_eq_some_iff.1 k0
      exact ⟨g, hg⟩
  rw [e]
  refine List.all_eq_true.2 fun p hp => ?_
  have h2 := hin p hp
  rw [hobj] at hp
  have hp' : p.1 = 2 ∧ (p.2 = "objects" ∨ p.2 = "guests") := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨rfl, Or.inl rfl⟩
    · exact ⟨rfl, Or.inr rfl⟩
  rw [hreaders, hp'.1] at h2
  show formsInT (D.Rd m) (D.N.sent m 0) p.1 p.2 _ = true
  rw [hreaders, hp'.1]
  exact kept_on hruns hback P8 small _ p.2 hp'.2 s o F1 X Q ho hop hL' hSz g hg (hbare g hg) h2

/-- **What "left" says in front gives what "leftOn" says behind.** CONDITIONAL: the ledger in front
has its sizes (which what "left" says in front gives too). -/
theorem leftOn_at (hL : ledgerB s = true) (p : First.Look.P)
    (Lf : VerifiableInference.OnPublicFiles.k3LeftItem p s) :
    VerifiableInference.OnPublicFiles.k3LeftOnItem p s' := by
  obtain ⟨o, F1, X, Q, ho, hop, e, hF, hG⟩ := forks_blockAt h iU3 work l hd
  have hL' : Later o.F F1 := by
    have h0 := Law.blockAt_later h iU3 work l s s' rs gs hd
    have e1 : (seatAt h iU3).ledger s = o.F := by
      show s.fork?.getD {} = o.F
      rw [hF]
      rfl
    have e2 : (seatAt h iU3).ledger s' = F1 := by
      show s'.fork?.getD {} = F1
      rw [hG]
      rfl
    rw [e1, e2] at h0
    exact h0
  have hS1 : Sized F1 := hL'.sized ((Law.sized_iff hF).1 hL)
  refine Law.leftOn_of_kept hF hG ?_ hL' (Law.wellLaid_of_sized hS1) Lf
  rw [e]
  unfold First.S.lookHeard?
  rw [ho]

end

end VerifiableInference.Desc.Kinds.Head.Honest

#print axioms VerifiableInference.Desc.Kinds.Head.Honest.forks_blockAt
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.kept_ledger_free
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.sameOn_blockAt
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.kept_four_at
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.kept_trees_at
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.kept_lookOut_at
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.kept_objects_at
#print axioms VerifiableInference.Desc.Kinds.Head.Honest.leftOn_at
