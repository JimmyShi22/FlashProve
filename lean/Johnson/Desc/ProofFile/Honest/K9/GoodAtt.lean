-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/GoodAtt.lean: "GOOD" (`goodW`, Honest/K9/GateArms.lean) IN FRONT OF THE BATCHING OF
AN ATTENTION SEGMENT OF THE DESCRIPTION, UNDER THE LIBRARY's HEAD: THE KINDS' CLAUSES JOINED AS FAR AS THEY LIE.
Statements and proofs ON THE VERIFIER's TEXT; no prover is in this file, and no goal is stated. No probability is in
this file. `goodW_of_inv` wants ONE predicate I on states for the whole order. Here I := K5's clause ∧ J: K5's clause
is its house's `HeldLive x k` (Johnson/Desc/K5/Honest/Law/LiveState.lean); J IS A LETTER for what the lookups' house
and K8's owe.
  `rests_heard5`, `set_heard5`, `draw_heard5`   what a state holds of an attention segment's own rounds (`S.heard5?`,
      all that `HeldLive` reads) rests under the four writings of the runs, under the laying of K9's part, and under
      K9's draw
  **`goodW_att_at`**   at the segment 2 g + 1, g < 12, under the head, the opening and the four seating facts (which
      come off K9's seat: Honest/K9/SeatTied.lean): from: the plan A of the segment with K5's two public premises
      (`LiveFits`, A.NC = A.S.calls.size) · `HeldLive x k s` AT THE STATE IN FRONT OF THE BATCHING · AND, ON THE
      LETTER J (each clause may spend K5's `HeldLive` too): it holds behind the draw; every run of the order hands it
      on; every slot below k, and every slot from `k5End x k` on below n, is live in some run's claims; the five runs
      that are neither K5's own nor idle make claims that are plain at every slot: THEN `goodW p ‹the segment's
      gatherer› s n`, AT EVERY n
WHAT IS PAID HERE, so that no house need carry K5's clause: start and hand for K5's clause, at all ten runs,
whosever (by `fieldRun_att_at`, Honest/K9/KeepsAtHead.lean) · the merge's slot: none (K5's `held_merge`) · unnamed:
idle · live at every slot from k to `k5End x k` (K5's `first_state`, `second_state`, through the library's ties
`AttTies`) · plain at K5's three runs and at the two idle runs.
WHAT IS NOT CLAIMED. `HeldLive` at any state (had from its mark's silence, under premises). ANY CLAUSE ON
J: no lemma at a state is at hand for the lookups' two windows: J MAY BE UNMEETABLE. That the three windows cover the
slots below the public number (the numbers: Honest/K9/GoodAttPlan.lean), or that k is public. Plain at the five runs:
paid in Honest/K9/GoodAttSeat.lean. No member. `goodW_att_at` is called by Honest/K9/GoodAttSeat.lean alone. Nothing
on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.GateArms
import Johnson.Desc.ProofFile.Honest.K9.KeepsAtHead
import Johnson.Desc.K5.Honest.Law.JoinState

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.First.Look (placeAt)
open H2K5.Honest (HeldLive heldLive_congr held_merge first_state second_state keys_state LiveFits k5End)

/-- What a state holds of an attention segment's own rounds rests under the four writings. -/
theorem rests_heard5 : FieldRests S.heard5? where
  tl := K5Law.heard5_putTl
  fork := K5Law.heard5_putFork
  wrote e _ _ _ hw := by
    obtain ⟨h1, rfl⟩ := hw
    unfold S.heard5?
    simp [h1]
  head s a G h := by
    unfold S.heard5?
    simp [h]

/-- K9's own share: laying K9's part leaves it. -/
theorem set_heard5 (s : S) (q : Desc.K9.Part) : (Desc.K9.atS.set s q).heard5? = s.heard5? := by
  show S.heard5? ((s.putLink q.L).putFork q.F) = s.heard5?
  rw [K5Law.heard5_putFork, K5Law.heard5_putLink]

/-- So does the draw. -/
theorem draw_heard5 (p : Desc.K9.Where) (s t₁ : S) (x : E)
    (h : (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁) :
    t₁.heard5? = s.heard5? := by
  obtain ⟨a, ha⟩ := draw_open p s t₁ x h
  rw [draw_is p s t₁ x a ha h, set_heard5]

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {F : FileDescription ProofFile.Inst} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)} {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- **"Good" in front of an attention segment's batching**: K5's clause joined with a letter for the others'. -/
theorem goodW_att_at (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base cF A₂ B₂) {g : ℕ} (hg : g < 12)
    (hs : IM.subAt (2 * g + 1) = .attention) (L : Link S ProofFile.Cl) (p : Desc.K9.Where)
    (hlk : h.𝔇.lk (2 * g + 1) = some L) (seg : SegAt (2 * g + 1) (IM.subAt (2 * g + 1)) L)
    (drawB : DrawMoves Desc.K9.atS p [.add (claimsInBy L.each L.hear L.order)] L.batchB)
    (kp : IM.k9At Zp (2 * g + 1) = some p) (u : HTailF2) {A : OnBytes.Attention.Plan}
    (hA : Bs.G₀.W.A[g]? = some A) {xr : OnBytes.Params.AttentionRounds} {k : ℕ}
    (gf : LiveFits (First.Att.P.geoOf A.S) xr) (hN : A.NC = A.S.calls.size) (s : S) (n : ℕ)
    (hI : HeldLive xr k s) (J : S → Prop)
    (Jstart : ∀ y t₁, (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne y⟩] [] = .ok t₁ →
      J t₁)
    (Jhand : ∀ o ∈ L.order, ∀ run, At L o run → ∀ m t z, HeldLive xr k t → J t → run m t = .ok z → J z.2)
    (Jlive : ∀ j < n, j < k ∨ k5End xr k ≤ j → ∃ o ∈ L.order, ∀ run, At L o run →
      ∀ m t z, HeldLive xr k t → J t → run m t = .ok z → Desc.K9H.liveAt z.1 j = true)
    (Jplain : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects"), (4, "K8.equations")],
      ∀ run, At L o run → ∀ m t z, HeldLive xr k t → J t → run m t = .ok z →
        ∀ j, Desc.K9H.plainAt z.1 j = true) :
    goodW p (claimsInBy L.each L.hear L.order) s n := by
  obtain ⟨A', X, hA', _, Wh⟩ := LPFK9.attOwesC_g h O hg hs L p hlk seg drawB kp
  obtain rfl : A' = A := Option.some.inj (hA'.symm.trans hA)
  have T := (Wh (fun _ => False) (((placeAt (P5J.At.X Zp) (2 * g + 1) false).map (·.lm)).getD 0) 0 0 0 u u
    (fun _ hq => hq.elim) (fun _ hq => hq.elim) fun pl e => by rw [e]; rfl).ties
  have ord : L.order = First.orderOf .attention := by
    rw [← hs]
    exact seg.order
  have idle : ∀ i ∈ [1, 6], ∀ run, At L (i, "guests") run → ∀ m t z, run m t = .ok z →
      ∀ j, Desc.K9H.plainAt z.1 j = true := by
    intro i hi run hr m t z hz j
    have e := T.tGuests i hi run hr m t z.1 z.2 hz
    obtain ⟨e1, _⟩ := Prod.mk.inj (Except.ok.inj e)
    rw [← e1]
    rfl
  refine goodW_of_inv p L.each L.hear L.order s n none (fun e => HeldLive xr k e ∧ J e) ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun y t₁ ht => ⟨heldLive_congr (draw_heard5 p s t₁ y ht) hI, Jstart y t₁ ht⟩
  · exact fun o ho run hr m t z hIt hz =>
      ⟨heldLive_congr (fieldRun_att_at h O hg hs L p hlk seg drawB kp u rests_heard5 o ho run hr m t z.1 z.2 hz)
        hIt.1, Jhand o ho run hr m t z hIt.1 hIt.2 hz⟩
  · exact fun e he => held_merge he.1
  · intro j hj _
    by_cases h1 : j < k ∨ k5End xr k ≤ j
    · obtain ⟨o, ho, H⟩ := Jlive j hj h1
      exact ⟨o, ho, fun run hr m t z hIt hz => H run hr m t z hIt.1 hIt.2 hz⟩
    · have hk : k ≤ j := by omega
      have he : j < k5End xr k := by omega
      by_cases h2 : j = First.Att.P.kB xr k ∨ First.Att.P.kV xr k ≤ j
      · refine ⟨(2, "second"), by rw [ord]; decide, fun run hr m t z hIt hz => ?_⟩
        exact (second_state _ gf m t z hIt.1 (T.tSecond run hr m t z.1 z.2 hz)).1 j
          (h2.imp id fun h3 => ⟨h3, he⟩)
      · refine ⟨(2, "first"), by rw [ord]; decide, fun run hr m t z hIt hz => ?_⟩
        exact (first_state _ gf hN m t z hIt.1 (T.tFirst run hr m t z.1 z.2 hz)).1 j hk
          (by omega) fun h3 => h2 (Or.inl h3)
  · intro j _ _ o ho
    rw [ord] at ho
    revert o
    refine (order_attention fun o => ∀ run, claimsRunOf L.hear o = some run → ∀ m t z,
      (HeldLive xr k t ∧ J t) → run m t = .ok z → Desc.K9H.plainAt z.1 j = true).2
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun run hr m t z hIt hz => Jplain _ (by simp) run hr m t z hIt.1 hIt.2 hz j
    · exact fun run hr m t z _ hz => idle 1 (by simp) run hr m t z hz j
    · exact fun run hr m t z hIt hz => (first_state _ gf hN m t z hIt.1 (T.tFirst run hr m t z.1 z.2 hz)).2.1 j
    · exact fun run hr m t z hIt hz => (keys_state A' m t z hIt.1 (T.tKeys run hr m t z.1 z.2 hz)).2.1 j
    · exact fun run hr m t z hIt hz => Jplain _ (by simp) run hr m t z hIt.1 hIt.2 hz j
    · exact fun run hr m t z hIt hz => (second_state _ gf m t z hIt.1 (T.tSecond run hr m t z.1 z.2 hz)).2.1 j
    · exact fun run hr m t z hIt hz => Jplain _ (by simp) run hr m t z hIt.1 hIt.2 hz j
    · exact fun run hr m t z hIt hz => Jplain _ (by simp) run hr m t z hIt.1 hIt.2 hz j
    · exact fun run hr m t z _ hz => idle 6 (by simp) run hr m t z hz j
    · exact fun run hr m t z hIt hz => Jplain _ (by simp) run hr m t z hIt.1 hIt.2 hz j
  · exact fun j _ hm => nomatch hm

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.rests_heard5
#print axioms ProofFile.Honest.K9.set_heard5
#print axioms ProofFile.Honest.K9.draw_heard5
#print axioms ProofFile.Honest.K9.goodW_att_at
