-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/YesAtSeat.lean: THE SEATED BATCHING BLOCK's YES, BROUGHT TO NAMED PREMISES.
Statements and proofs ON THE VERIFIER's TEXT; no prover is in this file, and no goal is stated. NO PREMISE IS PAID AT
A STATE OF A RUN HERE, K9's own (`drawReady`; the equation is open) among them.

  `BatBehind p g s x y G t`   what lies behind the batching's yes, as one structure: y is what draw and gatherer yield
      at x · G is what the adding makes of y's ledger and claims (`K9.addList`), with what it leaves and turns
      (`AddedAll`) · t is y's state with K9's part laid in at the ledger G · t's open ledger is G · as many claims are
      counted as the gatherer made
  `batch_yes_at`    `batch_yes_of` (Honest/K9/BatYes.lean) with the premise on the ledger's core asked AT THE ONE YES
      of the gatherer behind the draw, not of the gatherer at every state; and with `BatBehind` handed on
  `set_failed`, `set_out`   laying K9's part into a state turns neither the mark of failure nor what the state holds
      of the output (the reply among it)
  **`seated_yes_of`**   a block that seats K9's batching alone (`IM.LaidAlone`, under the description's own test on
      the reply) SAYS YES AT x where: a segment is open · `drawReady` · the equation is open · behind the draw the
      gatherer returns, leaves the lens answering, has kept the ledger's core, has made at most the plan's number of
      claims, each of which fits the arrays behind the draw, AND HAS LEFT NO MARK OF FAILURE AND THE REPLY AS IT WAS.
      Handed on, here, in the three below and in Honest/K9/StepYes.lean: `BatBehind`, and that the state behind bears
      no mark of failure and the reply as it was
  **`seated_yes_family`**   the same over the frame's gatherer, with ONE FAMILY J i cs u for its runs
      (`gather_returns_list`, Honest/K9/GatherList.lean): J holds at (0, [], the state behind the draw); at each entry
      THE RUN THAT STANDS IN THE LIST OF BLOCKS returns, passes the test behind it and hands J on; and J at the
      order's length says the rest. J AT THE END IS HANDED BACK
  `sort_layers`     the sealed library's two words for a segment's sort (`IM.subAt`, `IM.sortAt`) agree at a
      feed-forward one
  **`yes_at_seat`**, **`yes_of_family`**   WHEREVER THE DESCRIPTION CAN BE OPENED IN THE GOALS' SCOPE (the premises
      hS, hR, O: that they can be met together is shown by no theorem known to this pen), at each feed-forward
      segment: the two of the description's own block at number 14 l + 9, WITH THE LEDGER's CORE AND THE LENS BEHIND
      THE GATHERER PAID (`layers_keeps`, `layers_side`, Honest/K9/LayersCore.lean). `yes_of_family` goes by
      `seated_yes_family`, and hands on the segment's order and its test behind a run (`K9.eachAtS .layers`)
THE RUNS IN THESE CLAUSES ARE THOSE IN THE DESCRIPTION's LIST (`claimsRunOf Lk.hear o`), WRAPPED BY ITS MAKERS. A
house that shows "my own run returns" has not paid the clause: the sealed ties go the other way at five of the seven
entries (a yes of the list's run is a yes of the kind's own), and take "a run stands at this entry" as a premise: THAT
A RUN STANDS AT AN ENTRY, AND THAT THE WRAP PASSES, IS OWED (the guard on the seat: `guardedRun_yes`,
Honest/K9/GatherYes.lean). Called at members: `seated_yes_of`, `seated_yes_family`, and in them `batch_yes_at`:
Honest/K9/YesToy.lean. `yes_at_seat` by no line; `yes_of_family` by Honest/K9/StepYes.lean alone: no member. (`set_out`
is typed anew: the seal has the same statement as `LPFK9.set_out`, Johnson/LPFK9R/RoomKeepK9.lean.)
WHAT IS NOT CLAIMED. Any of the premises at any state: above all the runs' clauses: J IS ONE FAMILY, chosen by whoever
calls the theorem: who lays which clause into it, and who carries it through the other kinds' runs, is not settled
here. The decision, at the round as `drawnOne` gives it and no column (the step: Honest/K9/StepYes.lean). Attention
and the head IN THIS FILE (there the ledger's core is part 1's, and the yes stands in Honest/K9/YesAll.lean, over
Honest/K9/AtSeatAll.lean's `SeatedFree.keeps`). Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.AtSeat
import Johnson.Desc.ProofFile.Honest.K9.LayersCore
import Johnson.Desc.ProofFile.Honest.K9.GatherList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Claim Link Place KindName Chain FileDescription claimsInBy)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.K9 (atS Where drawAlone batch addList)
open VerifiableInference.Desc.K9H (claimFits AddedAll)

/-- What lies behind the batching's yes at x. -/
structure BatBehind (p : Where) (g : S → Except String (List Claim × S)) (s : S) (x : E)
    (y : S × VerifiableInference.Desc.K9.Part × List Claim) (G : Fork) (t : S) : Prop where
  gathered : gathered p g s x = some y
  added : addList y.2.1.F y.2.2 = .ok G
  all : AddedAll y.2.1.F G y.2.2.length
  state : t = atS.set y.1 { y.2.1 with F := G }
  ledger : t.fork? = some G
  count : G.nClaim = y.2.2.length

/-- `batch_yes_of`, with the core asked at the one yes. -/
theorem batch_yes_at (p : Where) (g : S → Except String (List Claim × S)) (s : S) (x : E)
    (a : VerifiableInference.Desc.K9.Part) (ha : atS.get? s = some a) (hr : drawReady a = true)
    (hdoor : a.F.doorShutF = false)
    (hg : ∀ t₁ a₁, (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁ →
      atS.get? t₁ = some a₁ → ∃ z a', g t₁ = .ok z ∧ atS.get? z.2 = some a' ∧ LedgerCore a₁ a' ∧
        z.1.length ≤ a.F.planClaimsF ∧ z.1.all (claimFits a₁.F.trees a₁.F.ns) = true) :
    ∃ y G t, (batch atS p g).decide s [⟨[], drawnOne x⟩] [] = .ok t ∧ BatBehind p g s x y G t := by
  obtain ⟨t₁, ht⟩ := (draw_iff p s x).2 ⟨a, ha, hr⟩
  obtain ⟨a₁, h1, hl⟩ := draw_facts p s t₁ x a ha ht
  obtain ⟨z, a', hz, ha', hc, hlen, hfit⟩ := hg t₁ a₁ ht h1
  have hy : gathered p g s x = some (z.2, a', z.1) := by
    unfold gathered
    simp only [ht, hz, ha', Option.map_some]
  have hfit' : z.1.all (claimFits a'.F.trees a'.F.ns) = true := by
    rw [VerifiableInference.Desc.K9H.all_congr _ _ _ (fits_behind a₁ a' hc)]
    exact hfit
  obtain ⟨G, hb, hG, hA⟩ := batch_yes p g s x (z.2, a', z.1) hy
    (ready_behind a a₁ a' x hl hc hdoor _ hlen) hfit'
  exact ⟨_, G, _, hb, hy, hG, hA, rfl, set_fork z.2 a' _ ha',
    by rw [hA.count, hc.count, hl.count, Nat.zero_add]⟩

theorem set_failed (u : S) (q : VerifiableInference.Desc.K9.Part) : (atS.set u q).failed = u.failed := by
  cases hh : u.here with
  | head h0 => by_cases ho : h0.opened = true <;> simp [atS, S.putLink, S.putFork, hh, ho]
  | _ => simp [atS, S.putLink, S.putFork, hh]

theorem set_out (u : S) (q : VerifiableInference.Desc.K9.Part) : (atS.set u q).out = u.out := by
  cases hh : u.here with
  | head h0 => by_cases ho : h0.opened = true <;> simp [atS, S.putLink, S.putFork, hh, ho]
  | _ => simp [atS, S.putLink, S.putFork, hh]

/-- **When a block that seats K9's batching alone says yes.** -/
theorem seated_yes_of {b : Block S Claim} {p : Where} {g : S → Except String (List Claim × S)}
    {name : String} {pl : Place} (hb : IM.LaidAlone ProofFile.sameReply b (batch atS p g) name pl)
    (hk : pl.kind ≠ KindName.K7) (s : S) (x : E) (a : VerifiableInference.Desc.K9.Part)
    (ha : atS.get? s = some a) (hr : drawReady a = true) (hdoor : a.F.doorShutF = false)
    (hg : ∀ t₁ a₁, (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁ →
      atS.get? t₁ = some a₁ → ∃ z a', g t₁ = .ok z ∧ atS.get? z.2 = some a' ∧ LedgerCore a₁ a' ∧
        z.1.length ≤ a.F.planClaimsF ∧ z.1.all (claimFits a₁.F.trees a₁.F.ns) = true ∧
        z.2.failed = none ∧ z.2.out.reply = s.out.reply) :
    ∃ y G t, b.decide s [⟨[], drawnOne x⟩] [] = .ok t ∧ BatBehind p g s x y G t ∧ t.failed = none ∧
      t.out.reply = s.out.reply := by
  obtain ⟨y, G, t, hd, hB⟩ := batch_yes_at p g s x a ha hr hdoor (fun t₁ a₁ h1 h2 => by
    obtain ⟨z, a', q1, q2, q3, q4, q5, _, _⟩ := hg t₁ a₁ h1 h2
    exact ⟨z, a', q1, q2, q3, q4, q5⟩)
  obtain ⟨t₁, ht, hz, he⟩ := gathered_split p g s x y hB.gathered
  obtain ⟨a₁, h1, _⟩ := draw_facts p s t₁ x a ha ht
  obtain ⟨z, a', q1, _, _, _, _, q6, q7⟩ := hg t₁ a₁ ht h1
  have ez : z = (y.2.2, y.1) := Except.ok.inj (q1.symm.trans hz)
  rw [ez] at q6 q7
  have hf : t.failed = none := by
    rw [hB.state, set_failed]
    exact q6
  have ho : t.out.reply = s.out.reply := by
    rw [hB.state, set_out]
    exact q7
  refine ⟨y, G, t, (IM.yes_alone hb hk s _ _ []).2 ⟨hd, hf, ?_⟩, hB, hf, ho⟩
  unfold ProofFile.sameReply
  rw [ho]
  exact beq_self_eq_true _

/-- **The same over the frame's gatherer, with one family for its runs.** -/
theorem seated_yes_family {b : Block S Claim} {p : Where}
    {each : ℕ × String → List Claim → S → Except String Unit} {bs : List (Block S Claim)}
    {order : List (ℕ × String)} {name : String} {pl : Place}
    (hb : IM.LaidAlone ProofFile.sameReply b (batch atS p (claimsInBy each bs order)) name pl)
    (hk : pl.kind ≠ KindName.K7) (s : S) (x : E) (a : VerifiableInference.Desc.K9.Part)
    (ha : atS.get? s = some a) (hr : drawReady a = true) (hdoor : a.F.doorShutF = false)
    (J : ℕ → List Claim → S → Prop)
    (start : ∀ t₁, (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁ → J 0 [] t₁)
    (step : ∀ j o, order[j]? = some o → ∀ cs u, J j cs u → ∃ run z, claimsRunOf bs o = some run ∧
      run cs.length u = .ok z ∧ each o z.1 z.2 = .ok () ∧ J (j + 1) (cs ++ z.1) z.2)
    (fin : ∀ t₁ a₁ cs u, (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁ →
      atS.get? t₁ = some a₁ → claimsInBy each bs order t₁ = .ok (cs, u) → J order.length cs u →
      ∃ a', atS.get? u = some a' ∧ LedgerCore a₁ a' ∧ cs.length ≤ a.F.planClaimsF ∧
        cs.all (claimFits a₁.F.trees a₁.F.ns) = true ∧ u.failed = none ∧ u.out.reply = s.out.reply) :
    ∃ y G t, b.decide s [⟨[], drawnOne x⟩] [] = .ok t ∧
      BatBehind p (claimsInBy each bs order) s x y G t ∧ t.failed = none ∧ t.out.reply = s.out.reply ∧
      J order.length y.2.2 y.1 := by
  have key : ∀ t₁, (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁ →
      ∃ z, claimsInBy each bs order t₁ = .ok z ∧ J order.length z.1 z.2 := fun t₁ ht =>
    gather_returns_list each bs order J t₁ (start t₁ ht) step
  obtain ⟨y, G, t, hd, hB, hf, ho⟩ := seated_yes_of hb hk s x a ha hr hdoor (fun t₁ a₁ ht h1 => by
    obtain ⟨z, hz, hJ⟩ := key t₁ ht
    obtain ⟨a', q2, q3, q4, q5, q6, q7⟩ := fin t₁ a₁ z.1 z.2 ht h1 hz hJ
    exact ⟨z, a', hz, q2, q3, q4, q5, q6, q7⟩)
  obtain ⟨t₁, ht, hz, _⟩ := gathered_split p _ s x y hB.gathered
  obtain ⟨z, hz', hJ⟩ := key t₁ ht
  have ez : z = (y.2.2, y.1) := Except.ok.inj (hz'.symm.trans hz)
  rw [ez] at hJ
  exact ⟨y, G, t, hd, hB, hf, ho, hJ⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **At the description's own block at a feed-forward segment**: the ledger's core and the lens behind the gatherer
are paid. -/
theorem yes_at_seat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (hsub : IM.subAt l = .layers) :
    ∃ (Lk : Link S Claim) (p : Where), c.links[l]? = some Lk ∧ IM.k9At Z l = some p ∧
      c.blocksInOrder[14 * l + 9]? = some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) ∧
      ∀ (s : S) (a₀ : LayOwn) (x : E) (a : VerifiableInference.Desc.K9.Part), s.here = .lay a₀ →
        atS.get? s = some a → drawReady a = true → a.F.doorShutF = false →
        (∀ t₁ a₁, (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁ →
          atS.get? t₁ = some a₁ → ∃ z, claimsInBy Lk.each Lk.hear Lk.order t₁ = .ok z ∧
            z.1.length ≤ a.F.planClaimsF ∧ z.1.all (claimFits a₁.F.trees a₁.F.ns) = true ∧
            z.2.failed = none ∧ z.2.out.reply = s.out.reply) →
        ∃ y G t, (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).decide s [⟨[], drawnOne x⟩] [] = .ok t ∧
          BatBehind p (claimsInBy Lk.each Lk.hear Lk.order) s x y G t ∧ t.failed = none ∧
          t.out.reply = s.out.reply := by
  obtain ⟨Lk, p, p4, X, w, e1, e2, -, -, -, f9, -, walk, -, -, -⟩ := free_at_seat hS hR O l hl hsub
  obtain ⟨Lk', p', w', T, e1', e2', -, -, -, -, hb, -⟩ := (IM.k9_of hS hR O).2 l hl
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain rfl : p = p' := Option.some.inj (e2.symm.trans e2')
  have k9ne : KindName.K9 ≠ KindName.K7 := by decide
  refine ⟨Lk, p, e1, e2, f9, fun s a₀ x a hs ha hr hdoor hg => ?_⟩
  refine seated_yes_of (hb (claimsInBy Lk.each Lk.hear Lk.order)) k9ne s x a ha hr hdoor ?_
  intro t₁ a₁ ht h1
  obtain ⟨z, q1, q4, q5, q6, q7⟩ := hg t₁ a₁ ht h1
  have W := walk s a₀ hs
  have hlay : t₁.here = .lay { a₀ with L := (drawnPart p a x).L, F := (drawnPart p a x).F } := by
    rw [draw_is p s t₁ x a ha ht]
    simp [atS, S.putLink, S.putFork, hs]
  obtain ⟨b₁, hb₁, _⟩ := layers_side Lk p4 _ W.ties W.calls W.digits W.order t₁ z.2 _ hlay z.1 q1
  obtain ⟨a', q2, _⟩ := VerifiableInference.Desc.First.K8.Honest.lay_part z.2 b₁ hb₁
  exact ⟨z, a', q1, q2,
    layers_keeps Lk p4 _ W.ties W.calls W.digits W.order t₁ z.2 _ hlay z.1 q1 a₁ a' h1 q2, q4, q5, q6, q7⟩

/-- The sealed library's two words for a segment's sort agree at a feed-forward segment. -/
theorem sort_layers (l : ℕ) (h : IM.subAt l = .layers) : IM.sortAt l = .layers := by
  unfold IM.subAt at h
  unfold IM.sortAt
  by_cases h24 : l = 24
  · rw [if_pos h24] at h; exact nomatch h
  · rw [if_neg h24] at h ⊢
    by_cases h2 : l % 2 = 0
    · rw [if_pos h2]
    · rw [if_neg h2] at h; exact nomatch h

/-- **The same, with one family for the seven runs**: by `seated_yes_family`. -/
theorem yes_of_family (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (hsub : IM.subAt l = .layers) :
    ∃ (Lk : Link S Claim) (p : Where), c.links[l]? = some Lk ∧ IM.k9At Z l = some p ∧
      c.blocksInOrder[14 * l + 9]? = some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) ∧
      Lk.order = VerifiableInference.Desc.First.orderOf .layers ∧
      Lk.each = VerifiableInference.Desc.K9.eachAtS .layers ∧
      ∀ (s : S) (a₀ : LayOwn) (x : E) (a : VerifiableInference.Desc.K9.Part)
        (J : ℕ → List Claim → S → Prop), s.here = .lay a₀ →
        atS.get? s = some a → drawReady a = true → a.F.doorShutF = false →
        (∀ t₁, (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁ → J 0 [] t₁) →
        (∀ j o, Lk.order[j]? = some o → ∀ cs u, J j cs u → ∃ run z, claimsRunOf Lk.hear o = some run ∧
          run cs.length u = .ok z ∧ Lk.each o z.1 z.2 = .ok () ∧ J (j + 1) (cs ++ z.1) z.2) →
        (∀ t₁ a₁ cs u, (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁ →
          atS.get? t₁ = some a₁ → claimsInBy Lk.each Lk.hear Lk.order t₁ = .ok (cs, u) → J 7 cs u →
            cs.length ≤ a.F.planClaimsF ∧
            cs.all (claimFits a₁.F.trees a₁.F.ns) = true ∧ u.failed = none ∧
            u.out.reply = s.out.reply) →
        ∃ y G t, (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).decide s [⟨[], drawnOne x⟩] [] = .ok t ∧
          BatBehind p (claimsInBy Lk.each Lk.hear Lk.order) s x y G t ∧ t.failed = none ∧
          t.out.reply = s.out.reply ∧ J 7 y.2.2 y.1 := by
  obtain ⟨Lk, p, p4, X, w, e1, e2, -, -, -, f9, -, walk, -, -, -⟩ := free_at_seat hS hR O l hl hsub
  obtain ⟨Lk', p', w', T, e1', e2', -, -, -, -, hb, -, -, -, -, hord, -, -, -, hw1, heach, -⟩ :=
    (IM.k9_of hS hR O).2 l hl
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain rfl : p = p' := Option.some.inj (e2.symm.trans e2')
  rw [hsub] at hord
  rw [hw1, sort_layers l hsub] at heach
  have k9ne : KindName.K9 ≠ KindName.K7 := by decide
  refine ⟨Lk, p, e1, e2, f9, hord, heach, fun s a₀ x a J hs ha hr hdoor start step fin => ?_⟩
  have h7 : Lk.order.length = 7 := by rw [hord]; rfl
  have h := seated_yes_family (hb (claimsInBy Lk.each Lk.hear Lk.order)) k9ne s x a ha hr hdoor J start step
    (by
      intro t₁ a₁ cs u ht h1 hz hJ
      rw [h7] at hJ
      obtain ⟨q4, q5, q6, q7⟩ := fin t₁ a₁ cs u ht h1 hz hJ
      have W := walk s a₀ hs
      have hlay : t₁.here = .lay { a₀ with L := (drawnPart p a x).L, F := (drawnPart p a x).F } := by
        rw [draw_is p s t₁ x a ha ht]
        simp [atS, S.putLink, S.putFork, hs]
      obtain ⟨b₁, hb₁, _⟩ := layers_side Lk p4 _ W.ties W.calls W.digits W.order t₁ u _ hlay cs hz
      obtain ⟨a', q2, _⟩ := VerifiableInference.Desc.First.K8.Honest.lay_part u b₁ hb₁
      exact ⟨a', q2, layers_keeps Lk p4 _ W.ties W.calls W.digits W.order t₁ u _ hlay cs hz a₁ a' h1 q2,
        q4, q5, q6, q7⟩)
  rw [h7] at h
  exact h

end

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.batch_yes_at
#print axioms ProofFile.Honest.K9.seated_yes_of
#print axioms ProofFile.Honest.K9.seated_yes_family
#print axioms ProofFile.Honest.K9.sort_layers
#print axioms ProofFile.Honest.K9.yes_at_seat
#print axioms ProofFile.Honest.K9.yes_of_family
#print axioms ProofFile.Honest.K9.BatBehind
#print axioms ProofFile.Honest.K9.set_failed
#print axioms ProofFile.Honest.K9.set_out
