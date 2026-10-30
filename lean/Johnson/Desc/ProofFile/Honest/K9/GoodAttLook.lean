-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/GoodAttLook.lean: `LookLive` (Honest/K9/GoodAttSeat.lean: what is still owed for
"good" in front of an attention segment's batching) CUT DOWN TO "LIVE" ALONE, for a clause that reads of the state
THREE THINGS: what the lookup on the calls heard, in both fields that hold it (`S.lookHeard?`, `S.look?`), and the
library's three numbers (`K9L.numOf u`: the smallness test's data but for its fourteen written fields, so what the
lookup on the digits heard, its window and its shape too; the list of tables; the plan's number of claims). Statements
and proofs ON THE VERIFIER's TEXT; no prover is in this file, and no goal is stated.
  `fieldRests_lookHeard`, `fieldRests_look`, `set_look`, `draw_look`, `draw_look2`   the first two readings rest under
      the four writings of the runs and under K9's draw (`set_look`: the first under the laying of K9's part; the
      second's laying stands inside `draw_look2`). KIN IN THE LIBRARY: `PhiAll.rests_look`
      (Johnson/Desc/First/Link/Law/SortLetters.lean) has the first reading's fork, wrote, head and set in another
      structure; new here: the smallness test's data laid at whatever value
  **`lookLive_of_readers`**   under the head and K9's seat at 2 g + 1: for ANY predicate Jr on the three readings: Jr
      at s, and "every slot below k, and every slot from `k5End xr k` on below n, is live in some run's claims, at
      every state at which K5's clause and Jr hold": THEN `LookLive Lk p xr k n s`. START AND HAND ARE PAID HERE, at
      the draw and at all ten runs, whosever: by the five above, `draw_num` (Honest/K9/DrawNum.lean),
      `fieldRun_att_at` (Honest/K9/KeepsAtHead.lean) and the library's `run_attention` at `rests_num u`
  **`goodW_att_readers`**   so "good" itself, from these
HOW FAR THE THREE READINGS REACH, BY READING: enough at both runs "objects" (their lists are the rows of what was
heard) and at K8's first four claims (the library's `four8_blank`). AT "join" AND "planes" THE RUN READS THE LEDGER
TOO (the caller's key forms and readers), WHICH NO FIXED READING CAN HOLD: every run writes it: a clause there must
hold at every ledger, or `LookLive` with a free J is the form. Two predicates Jr joined are a Jr: so under this form
no part need carry another's clause.
WHAT IS NOT CLAIMED. Any such predicate. That a clause of the lookups' house can do with these readings. What
Honest/K9/GoodAttSeat.lean does not claim. No member: called by no line. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.GoodAttSeat
import Johnson.Desc.ProofFile.Honest.K9.DrawNum
import Johnson.Desc.First.Link.Law.NumRuns
import Johnson.Desc.First.StateLedger
import Johnson.Desc.First.Att.Claims.WalkShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll
open H2K5.Honest (HeldLive LiveFits k5End)

/-- What the lookup on the calls heard rests under the four writings. -/
theorem fieldRests_lookHeard : FieldRests S.lookHeard? where
  tl := S.look_putTl
  fork := S.look_putFork
  wrote e _ _ _ hw := by
    obtain ⟨h1, rfl⟩ := hw
    unfold S.lookHeard?
    simp [h1]
  head s a G h := by
    unfold S.lookHeard?
    simp [h]

/-- So does what the segment's state holds under `S.look?`. -/
theorem fieldRests_look : FieldRests S.look? where
  tl := K5Law.look_putTl
  fork := K5Law.look_putFork
  wrote e _ _ _ hw := by
    obtain ⟨h1, rfl⟩ := hw
    unfold S.look?
    simp [h1]
  head s a G h := by
    unfold S.look?
    simp [h]

/-- K9's own share: laying K9's part leaves it. -/
theorem set_look (s : S) (q : Desc.K9.Part) : (Desc.K9.atS.set s q).lookHeard? = s.lookHeard? := by
  show S.lookHeard? ((s.putLink q.L).putFork q.F) = s.lookHeard?
  rw [S.look_putFork, S.look_putLink]

/-- So does the draw. -/
theorem draw_look (p : Desc.K9.Where) (s t₁ : S) (x : E)
    (h : (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁) :
    t₁.lookHeard? = s.lookHeard? := by
  obtain ⟨a, ha⟩ := draw_open p s t₁ x h
  rw [draw_is p s t₁ x a ha h, set_look]

/-- The like of `S.look?`. -/
theorem draw_look2 (p : Desc.K9.Where) (s t₁ : S) (x : E)
    (h : (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁) :
    t₁.look? = s.look? := by
  obtain ⟨a, ha⟩ := draw_open p s t₁ x h
  rw [draw_is p s t₁ x a ha h]
  show S.look? ((s.putLink _).putFork _) = s.look?
  rw [K5Law.look_putFork, K5Law.look_putLink]

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- **The owed structure from "live" alone**, for a clause on the three readings. -/
theorem lookLive_of_readers (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) {kk : ℕ}
    {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree cF Zp (2 * g + 1) kk Lk p w) (u : HTailF2) (xr : OnBytes.Params.AttentionRounds) (k n : ℕ)
    (s : S) (Jr : Option Forest.Heard → Option Forest.Heard → Option HTailF2 × Option (Array HFun) × Option ℕ → Prop)
    (h0 : Jr s.lookHeard? s.look? (numOf u s))
    (live : ∀ j < n, j < k ∨ k5End xr k ≤ j → ∃ o ∈ Lk.order, ∀ run, At Lk o run →
      ∀ m t z, HeldLive xr k t → Jr t.lookHeard? t.look? (numOf u t) → run m t = .ok z →
        Desc.K9H.liveAt z.1 j = true) :
    LookLive Lk p xr k n s := by
  have hm : 2 * g + 1 < 25 := by omega
  obtain ⟨hlk, seg, drawB, kp⟩ := tied_of_seated h hm Sd
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hs := sub_odd g hg
  obtain ⟨A', X, _, _, Wh⟩ := LPFK9.attOwesC_g h O hg hs Lk p hlk seg drawB kp
  have W := Wh (fun _ => False)
    (((First.Look.placeAt (P5J.At.X Zp) (2 * g + 1) false).map (·.lm)).getD 0) 0 0 0 u u
    (fun _ hq => hq.elim) (fun _ hq => hq.elim) fun pl e => by rw [e]; rfl
  refine ⟨fun e => Jr e.lookHeard? e.look? (numOf u e), ?_, ?_, live⟩
  · intro y t₁ ht
    obtain ⟨a, ha⟩ := draw_open p s t₁ y ht
    show Jr t₁.lookHeard? t₁.look? (numOf u t₁)
    rw [draw_look p s t₁ y ht, draw_look2 p s t₁ y ht, draw_num u p s t₁ y a ha ht]
    exact h0
  · intro o ho run hr m t z _ hJ hz
    show Jr z.2.lookHeard? z.2.look? (numOf u z.2)
    rw [fieldRun_att_at h O hg hs Lk p hlk seg drawB kp u fieldRests_lookHeard o ho run hr m t z.1 z.2 hz,
      fieldRun_att_at h O hg hs Lk p hlk seg drawB kp u fieldRests_look o ho run hr m t z.1 z.2 hz,
      (run_attention (rests_num u) W.seg (take_of_attOwesC W) W.k3f).1 o ho run hr m t z.1 z.2 hz]
    exact hJ

/-- **"Good" in front of an attention segment's batching, from K5's clause and "live" on the lookups' two windows.** -/
theorem goodW_att_readers (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) {kk : ℕ}
    {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree cF Zp (2 * g + 1) kk Lk p w) (u : HTailF2) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {xr : OnBytes.Params.AttentionRounds} {k : ℕ}
    (gf : LiveFits (First.Att.P.geoOf a.S) xr) (hN : a.NC = a.S.calls.size) (s : S) (n : ℕ)
    (hI : HeldLive xr k s)
    (Jr : Option Forest.Heard → Option Forest.Heard → Option HTailF2 × Option (Array HFun) × Option ℕ → Prop)
    (h0 : Jr s.lookHeard? s.look? (numOf u s))
    (live : ∀ j < n, j < k ∨ k5End xr k ≤ j → ∃ o ∈ Lk.order, ∀ run, At Lk o run →
      ∀ m t z, HeldLive xr k t → Jr t.lookHeard? t.look? (numOf u t) → run m t = .ok z →
        Desc.K9H.liveAt z.1 j = true) :
    goodW p (claimsInBy Lk.each Lk.hear Lk.order) s n :=
  goodW_att h hg Sd u ha gf hN s n hI (lookLive_of_readers h hg Sd u xr k n s Jr h0 live)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.fieldRests_lookHeard
#print axioms ProofFile.Honest.K9.fieldRests_look
#print axioms ProofFile.Honest.K9.set_look
#print axioms ProofFile.Honest.K9.draw_look
#print axioms ProofFile.Honest.K9.draw_look2
#print axioms ProofFile.Honest.K9.lookLive_of_readers
#print axioms ProofFile.Honest.K9.goodW_att_readers
