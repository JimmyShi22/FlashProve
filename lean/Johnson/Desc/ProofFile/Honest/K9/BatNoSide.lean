-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/BatNoSide.lean: THE BATCHING's SUB-PROTOCOL AT A PROVER THAT HAS NO SIDE AT ITS PLACE: an implication to
`AcceptedS` (Honest/Thread/PaysS.lean) from "no side there" and two premises on the verifier's state. The thread T and
the second condition Said are variables. Statements and proofs; no definition; no prover is made; no goal is stated.
  `steps_noSide`, `moved_noSide`   where the search at the batching's place finds no side, the frame lays one step without a
      move there; played, it shows one round in which nothing is sent, and reads no column
  `none_at_batching`   from the segment's seat and hno (no side of the list stands at a place of the kind K9): the search
      at the batching's place finds none
  **`accepted_noSide`**   `AcceptedS T Said fall b` from: the seat · the block at b · the search finds none · hfall (where the
      table of falls is silent at b, the test front is silent) · ready (the draw's own guards hold at every stand) · runs
      (one family J for the segment's runs of claims, as `step_seated`, Honest/K9/YesAll.lean, takes it)
  **`accepted_of_hno`**   that from hno
Limits. ready and runs are premises, shown at no thread here (Honest/K9/RunSchema.lean cuts `runs` entry by entry). Of a list in
which a side does stand at the batching's place nothing is said. This file proves no property of a prover or a
protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.PlayLaw
import Johnson.Desc.ProofFile.Honest.K9.YesAll
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

variable {V W X Pb : Type} {Bk : ProverCoinCounts}

/-- What the fold lays at the batching's block where no side stands at its place: one step without a move. -/
theorem steps_noSide {S' Cl : Type} (p : Desc.K9.Where) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (blk : Block S' Cl) (hs : List (Placed V W X)) (l : List (Step W X))
    (hr : blk.rounds = [{ entry := Desc.K9.entry p }]) (ho : blk.oracles = [[]])
    (hn : (hs.find? fun h => h.place == blk.place) = none)
    (hl : chainSteps Bk rows look v [blk] hs = .ok l) :
    l = [⟨blk.name, ⟨blk.place, 0⟩, { entry := Desc.K9.entry p }, [], fun _ _ => none, fun _ _ => none, 0, false,
      none⟩] := by
  unfold chainSteps at hl
  rw [hn] at hl
  simp only at hl
  split at hl
  · exact nomatch hl
  rw [hr, ho] at hl
  exact (Except.ok.inj hl).symm

/-- The prover's side of the member's step there: one round as played, in which nothing is shown; no column. -/
theorem moved_noSide {S' Cl : Type} (T : Thread Bk S' Cl V W X Pb) (p : Desc.K9.Where) (blk : Block S' Cl)
    (hr : blk.rounds = [{ entry := Desc.K9.entry p }]) (ho : blk.oracles = [[]])
    (hn : (T.hs.find? fun h => h.place == blk.place) = none)
    (k : Coins Bk) (m : Mid W X) (En : Env) (d : Fmt.Drawn) (y : List Played × Mid W X) (cols : List Desc.OpenedColumn)
    (hM : T.Moved blk k m En [d] y cols) : roundsOf y.1 = [⟨[], d⟩] ∧ cols = [] := by
  obtain ⟨⟨l, hl, hp⟩, hc⟩ := hM
  obtain rfl := steps_noSide p _ _ _ blk T.hs l hr ho hn hl
  have hy : y = ([⟨blk.name, blk.place, 0, false, [], [], d⟩],
      ⟨m.st.hears d, m.loc ++ [d], m.seen ++ [⟨[], d⟩], m.opened⟩) := (Except.ok.inj hp).symm
  subst hy
  rw [hr, bat_reads] at hc
  exact ⟨rfl, (Except.ok.inj hc).symm⟩

/-- **No side of the kind K9 in the list: so none at the batching's place.** -/
theorem none_at_batching {c : Chain S Claim} {Z : ProofFile.Pub} {l k : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where}
    {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree c Z l k Lk p w) (hs : List (Placed V W X))
    (hno : ∀ g ∈ hs, g.place.kind ≠ KindName.K9) :
    (hs.find? fun h => h.place == (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).place) = none := by
  rw [List.find?_eq_none]
  intro e he hb
  have e1 : e.place = (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).place := beq_iff_eq.1 hb
  apply hno e he
  rw [e1, Sd.seat]

/-- **`AcceptedS` at the batching's member where no side stands at its place, from the pair in front.** -/
theorem accepted_noSide {c : Chain S Claim} {Z : ProofFile.Pub} {l k : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where}
    {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (T : Thread Bk S Claim V W X Pb)
    {Said : ℕ → Coins Bk → Mid W X → Prop} {b : ℕ}
    (Sd : SeatedFree c Z l k Lk p w)
    (hblk : T.bs[b]? = some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)))
    (hn : (T.hs.find? fun h => h.place == (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).place) = none)
    (fall : ℕ → S → List Fmt.Drawn → Option String) (front : S → List Fmt.Drawn → Option String)
    (hfall : ∀ s ds, fall b s ds = none → front s ds = none)
    (ready : ∀ κ s m En, ThrS T Said b κ s m En →
      ∃ a, Desc.K9.atS.get? s = some a ∧ drawReady a = true ∧ a.F.doorShutF = false)
    (runs : ∀ κ s m En tr a, ThrS T Said b κ s m En → front s [⟨[tr], [], [], none⟩] = none →
      Desc.K9.atS.get? s = some a → ∃ J : ℕ → List Claim → S → Prop,
        (∀ t₁, (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne (E.ofTriple tr)⟩] [] =
          .ok t₁ → J 0 [] t₁) ∧
        (∀ j o, Lk.order[j]? = some o → ∀ cs u, J j cs u → ∃ run z, claimsRunOf Lk.hear o = some run ∧
          run cs.length u = .ok z ∧ Lk.each o z.1 z.2 = .ok () ∧ J (j + 1) (cs ++ z.1) z.2) ∧
        (∀ t₁ a₁ cs u,
          (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne (E.ofTriple tr)⟩] [] = .ok t₁ →
          Desc.K9.atS.get? t₁ = some a₁ → claimsInBy Lk.each Lk.hear Lk.order t₁ = .ok (cs, u) →
          J Lk.order.length cs u → cs.length ≤ a.F.planClaimsF ∧
            cs.all (Desc.K9H.claimFits a₁.F.trees a₁.F.ns) = true ∧ u.failed = none ∧
            u.out.reply = s.out.reply)) :
    AcceptedS T Said fall b := by
  intro blk hblk' κ s m En ds y cols hT hd _ hf hM
  rw [hblk] at hblk'
  cases hblk'
  obtain ⟨h1, h2, _⟩ := Sd.shape
  rw [h1] at hd
  obtain ⟨tr, rfl⟩ := draws_one p ds hd
  obtain ⟨hy, rfl⟩ := moved_noSide T p _ h1 h2 hn κ m En _ y cols hM
  obtain ⟨a, ha, hr, hdoor⟩ := ready κ s m En hT
  obtain ⟨J, start, step, fin⟩ := runs κ s m En tr a hT (hfall s _ hf) ha
  obtain ⟨_, _, t, hstep, _⟩ := step_seated Sd s tr a ha hr hdoor J start step fin
  refine ⟨t, hM, ?_⟩
  rw [hy]
  exact hstep T.ft none []

/-- **The same from "no side of the kind K9 in the thread's list".** -/
theorem accepted_of_hno {c : Chain S Claim} {Z : ProofFile.Pub} {l k : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where}
    {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (T : Thread Bk S Claim V W X Pb)
    {Said : ℕ → Coins Bk → Mid W X → Prop} {b : ℕ}
    (Sd : SeatedFree c Z l k Lk p w)
    (hblk : T.bs[b]? = some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)))
    (hno : ∀ g ∈ T.hs, g.place.kind ≠ KindName.K9)
    (fall : ℕ → S → List Fmt.Drawn → Option String) (front : S → List Fmt.Drawn → Option String)
    (hfall : ∀ s ds, fall b s ds = none → front s ds = none)
    (ready : ∀ κ s m En, ThrS T Said b κ s m En →
      ∃ a, Desc.K9.atS.get? s = some a ∧ drawReady a = true ∧ a.F.doorShutF = false)
    (runs : ∀ κ s m En tr a, ThrS T Said b κ s m En → front s [⟨[tr], [], [], none⟩] = none →
      Desc.K9.atS.get? s = some a → ∃ J : ℕ → List Claim → S → Prop,
        (∀ t₁, (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne (E.ofTriple tr)⟩] [] =
          .ok t₁ → J 0 [] t₁) ∧
        (∀ j o, Lk.order[j]? = some o → ∀ cs u, J j cs u → ∃ run z, claimsRunOf Lk.hear o = some run ∧
          run cs.length u = .ok z ∧ Lk.each o z.1 z.2 = .ok () ∧ J (j + 1) (cs ++ z.1) z.2) ∧
        (∀ t₁ a₁ cs u,
          (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne (E.ofTriple tr)⟩] [] = .ok t₁ →
          Desc.K9.atS.get? t₁ = some a₁ → claimsInBy Lk.each Lk.hear Lk.order t₁ = .ok (cs, u) →
          J Lk.order.length cs u → cs.length ≤ a.F.planClaimsF ∧
            cs.all (Desc.K9H.claimFits a₁.F.trees a₁.F.ns) = true ∧ u.failed = none ∧
            u.out.reply = s.out.reply)) :
    AcceptedS T Said fall b :=
  accepted_noSide T Sd hblk (none_at_batching Sd T.hs hno) fall front hfall ready runs

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.steps_noSide
#print axioms ProofFile.Honest.K9.moved_noSide
#print axioms ProofFile.Honest.K9.none_at_batching
#print axioms ProofFile.Honest.K9.accepted_noSide
#print axioms ProofFile.Honest.K9.accepted_of_hno
