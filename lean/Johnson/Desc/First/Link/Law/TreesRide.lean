--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/TreesRide.lean: THE PUBLIC ITEM "ledger.treesAre"
(`FillSent.treesAreB`, Johnson/Desc/First/FillSent.lean: a ledger is open, and its arrays' rows,
columns and, of each virtual row, first column and number of weights are the plan's) RIDES OVER AN
ACCEPTING DECISION OF THE LOOKUP (K3), OF AN ATTENTION SEGMENT's OWN ROUNDS (K5) AND OF THE OUTPUT
HEAD's OWN ROUNDS (K6), each as the proof file's seat lays it. Definitions and theorems.

What the test reads, and who writes it. It reads `s.fork?` (is a ledger open) and that ledger's
field `trees`; nothing else of the state; nothing that a prover sends. The three kinds' decisions
lay a ledger back where one was open, WITH THE ARRAYS AS THEY WERE (not their looks alone): so the
virtual rows' numbers of weights, which our third new hand's `look` does not hold, stay too.
(K4's decision does turn the weights' VALUES; part 3 has that kind's lemma: `treesAreB_kept`.)

What is said.
  `KeepsTrees s s'`: where a ledger is open at s, one is open at s' and has the same arrays.
  `treesAre_keeps`, `pubAll_treesAre_keeps`: **so the test, and the composed public test at the
    item `.more (some m) "ledger.treesAre"`, pass from s to s'.**
  `via_trees`, `quietAt_trees`, `theOwn_trees`, `theWhole_trees`, **`theStated_trees`**: K3's
    sub-protocol at an address (both seats; with the step without a round behind it; NO PREMISE ON
    THE PLAN).
  `k5_trees`, **`k5AtN_trees`**: K5's. `k6_trees`, **`k6Seated_trees`**: K6's.
How: our third new hand's inversions and walks, called (e₁'s row 75, pack 5: LooksVia.lean:
`ViaL.hearVia_arrays`; LooksK5.lean: `K5L.hear_arrays`, `hear5_reads`; LooksK6.lean: `k6_reads`);
the landed `blockAt_trees` (Johnson/Desc/Kinds/Law/KeepsTrees.lean); the composer's
`pubAll_more_treesAre` (Johnson/Desc/First/PubAllAt.lean).

Limits. Decisions alone: nothing on the runs of claims. One direction: from a yes. That the item is
asked in front of these places, and that the seated sub-protocols are these makers' values, is not
said here. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.LooksVia
import Johnson.Desc.First.PubAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S Pub PubData pubAll pubAll_more_treesAre)
open VerifiableInference.Desc.First.FillSent (SentData treesAreB)
open VerifiableInference.Desc.Keeps (Decides Fn)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits)
open VerifiableInference.OnPublicFiles (SeatKeeps seatCalls_keeps seatDigits_keeps)

/-- Where a ledger is open in front, one is open behind and has the same arrays. -/
def KeepsTrees (s s' : S) : Prop :=
  ∀ G, s.fork? = some G → ∃ G', s'.fork? = some G' ∧ G'.trees = G.trees

theorem keepsTrees_refl (s : S) : KeepsTrees s s := fun G h => ⟨G, h, rfl⟩

theorem keepsTrees_trans (a b c : S) (h : KeepsTrees a b) (k : KeepsTrees b c) :
    KeepsTrees a c := by
  intro G hG
  obtain ⟨G1, h1, e1⟩ := h G hG
  obtain ⟨G2, h2, e2⟩ := k G1 h1
  exact ⟨G2, h2, e2.trans e1⟩

/-- The reading is left. -/
theorem keepsTrees_same {s s' : S} (h : s'.fork? = s.fork?) : KeepsTrees s s' :=
  fun G hG => ⟨G, h.trans hG, rfl⟩

/-- **The test passes.** -/
theorem treesAre_keeps {s s' : S} (h : KeepsTrees s s') (d : SentData) (m : ℕ)
    (ht : treesAreB d m s = true) : treesAreB d m s' = true := by
  unfold treesAreB at ht ⊢
  cases hG : s.fork? with
  | none =>
    rw [hG] at ht
    cases ht
  | some G =>
    obtain ⟨G', h1, h2⟩ := h G hG
    rw [hG, Option.any_some] at ht
    rw [h1, Option.any_some, h2]
    exact ht

/-- **The composed public test at the item passes.** -/
theorem pubAll_treesAre_keeps {P : Type} (D : PubData) (base : Pub → P × S → Bool) (z : P)
    (m : ℕ) {s s' : S} (h : KeepsTrees s s')
    (ht : pubAll D base (.more (some m) "ledger.treesAre") (z, s) = true) :
    pubAll D base (.more (some m) "ledger.treesAre") (z, s') = true := by
  rw [pubAll_more_treesAre] at ht ⊢
  exact treesAre_keeps h D.dS m ht

/-! ### K3 -/

/-- The lookup's decision, at a seat that reads the open ledger and keeps the ledger laid. -/
theorem via_trees {Cl : Type} (seat : Seat S Cl) (hf : ∀ s, seat.fork s = s.fork?)
    (hk : SeatKeeps seat) (piece : ℕ) (laid : Array ℕ) (before : List (ℕ × ℕ))
    (p : First.Look.P) (guests : List (First.Look.Guest S Cl)) :
    Decides KeepsTrees (K3.Law.blockVia seat piece laid before p guests) := by
  intro s rs gs s' h
  have h' : K3.Law.decideVia seat p s rs = .ok s' := h
  unfold K3.Law.decideVia at h'
  obtain ⟨F, hF, h'⟩ := K9L.ok_bind h'
  obtain ⟨_, hn, h'⟩ := K9L.ok_bind h'
  obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
  obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
  obtain ⟨x, hx, h'⟩ := K9L.ok_bind h'
  obtain rfl := Except.ok.inj h'
  have hF' := named_some hF
  have hn' : seat.heard s = none := by
    cases e : seat.heard s with
    | none => rfl
    | some g =>
      rw [e] at hn
      exact nomatch hn
  have e1 : (seat.put s x.1 x.2).fork? = some x.2 := by
    rw [← hf]
    exact hk s x.1 x.2 (by rw [hF']; rfl) hn'
  intro G hG
  obtain rfl : F = G := Option.some.inj (hF'.symm.trans ((hf s).trans hG))
  exact ⟨x.2, e1, ViaL.hearVia_arrays (g := x.1) (G := x.2) (named_some hx)⟩

/-- The steps without a round behind a lookup. -/
theorem quietAt_trees {X : Verify.Public} {i : ℕ} {digits : Bool} {f : S → Except String S}
    (hf : K3.quietAt X i digits = some f) : Fn KeepsTrees f := by
  intro s t h
  have dig : ∀ used claims, K3.quietDigits used claims s = .ok t → KeepsTrees s t := by
    intro used claims k
    unfold K3.quietDigits at k
    obtain ⟨F, hF, k⟩ := K9L.ok_bind k
    obtain ⟨G, hG, k⟩ := K9L.ok_bind k
    obtain rfl := Except.ok.inj k
    have hF' := named_some hF
    have hG' := named_some hG
    unfold First.Look.slotsTaken at hG'
    split at hG'
    · obtain rfl := Option.some.inj hG'
      intro G0 h0
      obtain rfl : F = G0 := Option.some.inj (hF'.symm.trans h0)
      exact ⟨_, fork_putFork s F hF' _, rfl⟩
    · exact nomatch hG'
  have hd : K3.quietHead X s = .ok t → KeepsTrees s t := by
    intro k
    unfold K3.quietHead at k
    split at k
    · rename_i a ha
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain ⟨_, _, k⟩ := K9L.ok_bind k
      obtain rfl := Except.ok.inj k
      exact keepsTrees_same (by simp [S.fork?, ha])
    · exact nomatch k
  have lk : ∀ fs, K3.quietLook fs s = .ok t → KeepsTrees s t := by
    intro fs k
    unfold K3.quietLook at k
    obtain ⟨_, _, k⟩ := K9L.ok_bind k
    obtain ⟨_, _, k⟩ := K9L.ok_bind k
    obtain rfl := Except.ok.inj k
    exact keepsTrees_refl s
  unfold K3.quietAt at hf
  dsimp only at hf
  repeat' split at hf
  all_goals first
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 hf
       exact dig _ _ h)
    | (obtain rfl := Option.some.inj hf
       first
         | exact hd h
         | exact lk _ h)
    | cases hf

/-- K3's own sub-protocol at an address. -/
theorem theOwn_trees {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theOwn claim runs X codes shape a = some b) : Decides KeepsTrees b := by
  unfold K3.theOwn at h
  split at h
  · exact nomatch h
  · obtain ⟨i, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · exact nomatch h
    · obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨sent, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨laid, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨key, _, rfl⟩ := Option.map_eq_some_iff.1 h
      have W : Decides KeepsTrees (K3.Law.blockVia
          (if digits = true then seatDigits claim else seatCalls claim) a.piece laid sent p
          []) := by
        cases digits with
        | true => exact via_trees _ (fun _ => rfl) (seatDigits_keeps claim) a.piece laid sent p []
        | false => exact via_trees _ (fun _ => rfl) (seatCalls_keeps claim) a.piece laid sent p []
      cases runs with
      | true => exact W
      | false => exact W

/-- With the step without a round joined behind it. -/
theorem theWhole_trees {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theWhole claim runs X codes shape a = some b) : Decides KeepsTrees b := by
  unfold K3.theWhole at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  have W := theOwn_trees claim runs X codes shape a h0
  cases hf : (a.link.bind fun i => K3.quietAt X i (a.piece == K3.pieceAt X i true)) with
  | none => exact W
  | some f =>
    obtain ⟨i, _, hq⟩ := Option.bind_eq_some_iff.1 hf
    exact Keeps.andThen_decides KeepsTrees keepsTrees_trans _ _ _ W
      (Keeps.quiet_decides KeepsTrees _ _ _ _ f (quietAt_trees hq))

/-- **K3's sub-protocol at an address, with its runs stated: NO PREMISE ON THE PLAN.** -/
theorem theStated_trees {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theStated claim readers X codes shape a = some b) : Decides KeepsTrees b := by
  unfold K3.theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  have W := theWhole_trees claim true X codes shape a h0
  split at h
  · cases h
    exact W
  · split at h
    · cases h
      exact W
    · split at h
      · cases h
        exact W
      · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
        exact W

/-! ### K5 -/

open VerifiableInference.Desc.First.Att.P (attentionKind seatSO k5AtN) in
/-- An attention segment's own rounds. -/
theorem k5_trees {Cl : Type}
    (claims : List (String × (ℕ → S → Except String (List Cl × S)))) (p : First.Att.P.Par) :
    Decides KeepsTrees (attentionKind seatSO claims p) := by
  intro s rs gs s' h
  have h' : First.Att.P.decide seatSO p s rs = .ok s' := h
  unfold First.Att.P.decide at h'
  obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
  obtain ⟨F, hF, h'⟩ := K9L.ok_bind h'
  obtain ⟨x, hx, h'⟩ := K9L.ok_bind h'
  obtain ⟨hd, G, rest, m⟩ := x
  obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
  have hear1 : First.Att.P.hear p.own (F, rs, 0) = some (hd, G, rest, m) := by
    cases e : First.Att.P.hear p.own (F, rs, 0) with
    | none =>
      rw [e] at hx
      exact nomatch hx
    | some y =>
      rw [e] at hx
      exact congrArg some (Except.ok.inj hx)
  have lay1 : seatSO.lay s hd G = some s' := by
    cases e : seatSO.lay s hd G with
    | none =>
      rw [e] at h'
      exact nomatch h'
    | some y =>
      rw [e] at h'
      exact congrArg some (Except.ok.inj h')
  have led1 : seatSO.ledger s = some F := by
    cases e : seatSO.ledger s with
    | none =>
      rw [e] at hF
      exact nomatch hF
    | some y =>
      rw [e] at hF
      exact congrArg some (Except.ok.inj hF)
  unfold seatSO at lay1 led1
  dsimp only at lay1 led1
  cases hh : s.here with
  | att a =>
    rw [hh] at lay1 led1
    obtain rfl : a.F = F := Option.some.inj led1
    obtain ⟨_, _, lay2⟩ := Option.bind_eq_some_iff.1 lay1
    have lay3 : S.hear5? { s with rowsOwed := none, here := .att { a with F := G } } hd = .ok s' :=
        by
      cases e : S.hear5? { s with rowsOwed := none, here := .att { a with F := G } } hd with
      | error w =>
        rw [e] at lay2
        exact nomatch lay2
      | ok y =>
        rw [e] at lay2
        exact congrArg Except.ok (Option.some.inj lay2)
    obtain ⟨r1, -⟩ := hear5_reads lay3
    intro G0 h0
    have e0 : some a.F = some G0 := by simpa [S.fork?, hh] using h0
    obtain rfl := Option.some.inj e0
    exact ⟨G, by rw [r1]; rfl, K5L.hear_arrays hear1⟩
  | lay a =>
    rw [hh] at led1
    exact nomatch led1
  | head a =>
    rw [hh] at led1
    exact nomatch led1
  | between =>
    rw [hh] at led1
    exact nomatch led1
  | fin a =>
    rw [hh] at led1
    exact nomatch led1
  | mem a =>
    rw [hh] at led1
    exact nomatch led1

open VerifiableInference.Desc.First.Att.P (k5AtN) in
/-- **So of `k5AtN`'s value.** -/
theorem k5AtN_trees {W : Verify.Public} {l g : ℕ} {before : List (ℕ × ℕ)} {b : Block S Claim}
    (h : k5AtN W l g before = some b) : Decides KeepsTrees b := by
  unfold k5AtN at h
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  intro s rs gs s' hd
  exact k5_trees (Cl := Claim) (First.Att.P.runsN p) _ s rs gs s' hd

/-! ### K6 -/

open VerifiableInference.Desc.Kinds.Head VerifiableInference.Desc.Kinds.Head.Law in
/-- The output head's own rounds. -/
theorem k6_trees (h : OnBytes.Model.Head.Shape) (iU3 work l : ℕ) :
    Decides KeepsTrees (blockAt h iU3 work l) := by
  intro s rs gs s' hd
  obtain ⟨F0, F', L, a1, -, a3, -⟩ := k6_reads h iU3 work l s s' rs gs hd
  have ht : (s'.fork?.getD {}).trees = (s.fork?.getD {}).trees :=
    blockAt_trees h iU3 work l s s' rs gs hd
  rw [a1, a3] at ht
  intro G hG
  obtain rfl : F0 = G := Option.some.inj (a1.symm.trans hG)
  exact ⟨F', a3, ht⟩

open VerifiableInference.Desc.Kinds.Head VerifiableInference.Desc.Kinds.Head.Law in
/-- **So of the sub-protocol as a lot seats it.** -/
theorem k6Seated_trees {W : OnBytes.Model.Verify.Public} {l : ℕ} {ms : List (ℕ × ℕ)}
    {b : Block S Claim} (h : seatedClaims W l ms = some b) : Decides KeepsTrees b := by
  obtain ⟨b0, h0, rfl⟩ := seatedClaims_some h
  unfold blockClaims at h0
  obtain ⟨i, _, rfl⟩ := Option.map_eq_some_iff.mp h0
  intro s rs gs s' hd
  exact k6_trees W.hS i _ l s rs gs s' ((tested_decide _ _ _ _ _ _ _ _).1 hd).1

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.treesAre_keeps
#print axioms VerifiableInference.Desc.LinkJoin.pubAll_treesAre_keeps
#print axioms VerifiableInference.Desc.LinkJoin.theStated_trees
#print axioms VerifiableInference.Desc.LinkJoin.k5AtN_trees
#print axioms VerifiableInference.Desc.LinkJoin.k6Seated_trees
