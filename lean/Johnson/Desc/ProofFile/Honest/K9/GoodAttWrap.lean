-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/GoodAttWrap.lean: FOR K9's FALL ON THE FREE SLOT, AT AN ATTENTION SEGMENT: THE LOOKUPS'
HOUSE's LAWS ON ITS SEATED RUNS WRAPPED INTO OUR NAMED STRUCTURE `LookLive` (Honest/K9/GoodAttSeat.lean), AT THE PLAN's
OWN NUMBERS; AND SO "GOOD" (`goodW`) FROM THE HOUSES' CLAUSES AT THE STATE. THE LAWS ARE THAT HOUSE's; OURS IS THE JOIN.
Statements and proofs ON THE VERIFIER's TEXT; no prover is in this file, and no goal is stated. No probability is in
this file.
  **`lookLive_of_clauses`**   under the head, g < 12, K9's seat at 2 g + 1, the segment's plan a off the public
      parameters and the two lookups' places pC, pD: at a state s: FROM: the lookups' `Clause`
      (Honest/K3/Good/Live/Clause.lean) at what s holds as heard by the lookup on the calls (JC) and on the digits (JD)
      · hkeys · h8: `LookLive Lk p a.own (Forest.elems a.fs) w.2.2.filled s`: k IS SET TO `Forest.elems a.fs`; n IS THE
      PUBLIC NUMBER THAT K9's TEST READS
  **`goodW_att_clauses`**   with `HeldLive a.own (Forest.elems a.fs) s` beside: `goodW p ‹the segment's
      gatherer› s w.2.2.filled` (by `goodW_att_plan`, Honest/K9/GoodAttPlan.lean)
THE TWO NAMED PREMISES, EACH ANOTHER HOUSE's. hkeys: at every state with `HeldLive`, the caller's key forms name no slot
of the window of "join" (that house's `KeysClear` at `P.keysOfO a`): K5's house's: it has taken `KeysClear`; that
`HeldLive` alone gives it, it has not said · h8: each slot of the digits' windows of "planes" and "join" is live in the
claims of "K8.equations", at every yes at a state with `HeldLive` and the digits' `Clause`: at the digits the library
seats "objects" alone: by our reading the lookups' law on K8's first four claims (K8's house has left it to them) with
 (Johnson/Desc/K8/Honest/EqSlots.lean), through the library's tie of that run to K8's equations;
not typed.
HOW. `lookLive_of_readers` (Honest/K9/GoodAttLook.lean) at Jr := the two clauses, read off its first and third readings
(that house's `digits_reading`): so start and hand are paid. A slot below `Forest.elems a.fs` lies in one of the calls'
three windows (`window_iff`; `calls_att`: the calls' stretch begins at 0): that window's run is the entry:
`objects_live`, `planes_live` (its premise on the readers: `bitsClear_att`), `join_live` (under hkeys),
behind the library's ties `at_objects_is`, `at_planes_is` at `readersAt_att`, `at_join_is`. A slot from `k5End` on lies
in the digits' stretch (`digits_att` with our `stretches_att` and `seated_w_att`: the digits' first slot is `k5End a.own
(Forest.elems a.fs)`): "objects" by `objects_live`; the two other windows by h8.
SO THE FORM OF `LookLive` IS NO BAR: those laws fit it as they lie. The warnings that `LookLive` or J "MAY BE
UNMEETABLE" in the heads of Honest/K9/GoodAtt.lean, GoodAttSeat.lean, GoodAttPlan.lean and FallDebtAtt.lean are
overtaken ONLY AS TO THE FORM: `LookLive` follows from JC, JD, hkeys and h8. Whether these hold together at a reached
state is as open as before. These files are not turned.
WHAT IS NOT CLAIMED. JC, JD OR `HeldLive` AT ANY STATE: each part has its clause behind its own member's accepting
step, from its mark's silence, under premises; THE CARRIAGE FROM THERE TO THE STATE IN FRONT OF THE BATCHING IS OURS AND
IS NOT TYPED; nor that K5's hearing begins at the slot `Forest.elems a.fs`. hkeys, h8. NO MEMBER: no state is shown at
which the premises hold together. The head's segment and the feed-forward ones. Both theorems are called by no line but
the second's call of the first. Nothing on any property.
GROUND: beneath this file, beside the sealed library, lie 184 files, this one among them; by their folders: 40 of ours ·
83 of the lookups' · 11 of the frame's · 37 of K5's house's · 12 of the hash build's · 1 of K8's house's: reading copies
all but ours. At the full size and the format's second hash function alone: the head's.
-/
import Johnson.Desc.ProofFile.Honest.K9.GoodAttLook
import Johnson.Desc.ProofFile.Honest.K9.GoodAttPlan
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.Runs
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.Windows
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.Bridges
import Johnson.Desc.First.Att.Door.Law.K5RestOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.K3 (faceOf)
open H2K5.Honest (HeldLive k5End)
open ProofFile.Honest.K3 (windowOf Run)
open ProofFile.Honest.K3.Good.Live (Clause KeysClear objects_live join_live planes_live window_iff calls_att digits_att
  digits_reading bitsClear_att)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- **`LookLive` AT THE PLAN's OWN NUMBERS, FROM THE LOOKUPS' CLAUSE AT BOTH LOOKUPS AND TWO NAMED PREMISES.** -/
theorem lookLive_of_clauses (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) {kk : ℕ}
    {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree cF Zp (2 * g + 1) kk Lk p w) (u : HTailF2) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) (2 * g + 1) false = some pC) (hD : placeAt (P5J.At.X Zp) (2 * g + 1) true = some pD)
    (s : S) (JC : Clause pC s.lookHeard?) (JD : Clause pD (s.tl?.bind (·.heard)))
    (hkeys : ∀ t, HeldLive a.own (Forest.elems a.fs) t → ∀ j ∈ windowOf (faceOf a.fs) Run.join,
      KeysClear (First.Att.P.keysOfO a) t j)
    (h8 : ∀ j, j ∈ windowOf (faceOf a.seam.tl.f9) Run.planes ∨ j ∈ windowOf (faceOf a.seam.tl.f9) Run.join →
      ∀ run, At Lk (4, "K8.equations") run → ∀ m t z, HeldLive a.own (Forest.elems a.fs) t →
        Clause pD (t.tl?.bind (·.heard)) → run m t = .ok z → Desc.K9H.liveAt z.1 (pD.first + j) = true) :
    LookLive Lk p a.own (Forest.elems a.fs) w.2.2.filled s := by
  have hm : 2 * g + 1 < 25 := by omega
  obtain ⟨hlk, seg, drawB, kp⟩ := tied_of_seated h hm Sd
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hs := sub_odd g hg
  obtain ⟨h4, g', hg', eg, _⟩ := LPFK9.att_facts h O (2 * g + 1) hm hs
  obtain rfl : g = g' := by omega
  have hA : Bs.G₀.W.A[g]? = some a := by
    rw [O.W]
    exact ha
  have i1 : IM.k3Ix (2 * g + 1) false = 1 := by
    show (1 : ℕ) + (if 2 * g + 1 = 24 then 1 else 0) = 1
    rw [if_neg (by omega)]
  have i6 : IM.k3Ix (2 * g + 1) true = 6 := by
    show (6 : ℕ) + (if 2 * g + 1 = 24 then 1 else 0) = 6
    rw [if_neg (by omega)]
  have ord : Lk.order = First.orderOf .attention := by
    rw [← hs]
    exact seg.order
  have p4X := (H2K5.Door.scope_all h).1
  obtain ⟨sC, fC⟩ := calls_att h.pubOne p4X ha hC
  obtain ⟨sD, -, eD⟩ := digits_att h.pubOne p4X ha hD
  have hst := stretches_att h hg Sd ha
  have hw : w.2.2.filled = a.nMsg := by rw [seated_w_att h hg Sd ha]
  have fD : pD.first = k5End a.own (Forest.elems a.fs) := by omega
  refine lookLive_of_readers h hg Sd u a.own (Forest.elems a.fs) w.2.2.filled s
    (fun y _ c => Clause pC y ∧ Clause pD (c.1.bind (·.heard))) ⟨JC, by rw [digits_reading]; exact JD⟩ ?_
  intro j hj hjw
  rcases hjw with hlo | hhi
  · obtain ⟨rn, hr⟩ := (window_iff a.fs j).1 hlo
    cases rn with
    | objects =>
      refine ⟨(1, "objects"), by rw [ord]; decide, fun run hrun m t z _ hJ hz => ?_⟩
      have e := OnPublicFiles.at_objects_is h.scope h.reads O hm false Sd.link (run := run) (by rw [i1]; exact hrun)
      rw [e] at hz
      have c := objects_live (OnPublicFiles.seatOf K3Lot.ofForm false) (fun _ => rfl) (fun _ => rfl) sC hz hJ.1 hr
      rwa [fC, Nat.zero_add] at c
    | planes =>
      refine ⟨(1, "planes"), by rw [ord]; decide, fun run hrun m t z _ hJ hz => ?_⟩
      obtain ⟨pl, _, e⟩ := OnPublicFiles.at_planes_is h.scope h.reads O hm Sd.link (H2K5.Door.readersAt_att h4 hA)
        (run := run) (by rw [i1]; exact hrun)
      rw [e] at hz
      have c := planes_live _ (fun _ => rfl) (fun _ => rfl) _ _ sC hz hJ.1 hr (bitsClear_att a t _)
      rwa [fC, Nat.zero_add] at c
    | join =>
      refine ⟨(2, "join"), by rw [ord]; decide, fun run hrun m t z hH hJ hz => ?_⟩
      have e := at_join_is O h4 hg' hA Sd.link hrun
      rw [e] at hz
      have c := join_live _ (fun _ => rfl) (fun _ => rfl) _ sC hz hJ.1 hr
        (by rw [fC, Nat.zero_add]; exact hkeys t hH j hr)
      rwa [fC, Nat.zero_add] at c
  · have hlt : j - pD.first < Forest.elems a.seam.tl.f9 := by omega
    have ej : pD.first + (j - pD.first) = j := by omega
    obtain ⟨rn, hr⟩ := (window_iff a.seam.tl.f9 (j - pD.first)).1 hlt
    cases rn with
    | objects =>
      refine ⟨(6, "objects"), by rw [ord]; decide, fun run hrun m t z _ hJ hz => ?_⟩
      have e := OnPublicFiles.at_objects_is h.scope h.reads O hm true Sd.link (run := run) (by rw [i6]; exact hrun)
      rw [e] at hz
      have J2 : Clause pD (t.tl?.bind (·.heard)) := by
        have := hJ.2
        rwa [digits_reading] at this
      have c := objects_live (OnPublicFiles.seatOf K3Lot.ofForm true) (fun _ => rfl) (fun _ => rfl) sD hz J2 hr
      rwa [ej] at c
    | planes =>
      refine ⟨(4, "K8.equations"), by rw [ord]; decide, fun run hrun m t z hH hJ hz => ?_⟩
      have J2 : Clause pD (t.tl?.bind (·.heard)) := by
        have := hJ.2
        rwa [digits_reading] at this
      have c := h8 _ (Or.inl hr) run hrun m t z hH J2 hz
      rwa [ej] at c
    | join =>
      refine ⟨(4, "K8.equations"), by rw [ord]; decide, fun run hrun m t z hH hJ hz => ?_⟩
      have J2 : Clause pD (t.tl?.bind (·.heard)) := by
        have := hJ.2
        rwa [digits_reading] at this
      have c := h8 _ (Or.inr hr) run hrun m t z hH J2 hz
      rwa [ej] at c

/-- **"GOOD" IN FRONT OF AN ATTENTION SEGMENT's BATCHING, AT THE PLAN's OWN NUMBERS, FROM THE HOUSES' CLAUSES AT THE
STATE AND THE TWO NAMED PREMISES.** -/
theorem goodW_att_clauses (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) {kk : ℕ}
    {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree cF Zp (2 * g + 1) kk Lk p w) (u : HTailF2) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) (2 * g + 1) false = some pC) (hD : placeAt (P5J.At.X Zp) (2 * g + 1) true = some pD)
    (s : S) (hI : HeldLive a.own (Forest.elems a.fs) s) (JC : Clause pC s.lookHeard?)
    (JD : Clause pD (s.tl?.bind (·.heard)))
    (hkeys : ∀ t, HeldLive a.own (Forest.elems a.fs) t → ∀ j ∈ windowOf (faceOf a.fs) Run.join,
      KeysClear (First.Att.P.keysOfO a) t j)
    (h8 : ∀ j, j ∈ windowOf (faceOf a.seam.tl.f9) Run.planes ∨ j ∈ windowOf (faceOf a.seam.tl.f9) Run.join →
      ∀ run, At Lk (4, "K8.equations") run → ∀ m t z, HeldLive a.own (Forest.elems a.fs) t →
        Clause pD (t.tl?.bind (·.heard)) → run m t = .ok z → Desc.K9H.liveAt z.1 (pD.first + j) = true) :
    goodW p (claimsInBy Lk.each Lk.hear Lk.order) s w.2.2.filled :=
  goodW_att_plan h hg Sd u ha s hI (lookLive_of_clauses h hg Sd u ha hC hD s JC JD hkeys h8)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.lookLive_of_clauses
#print axioms ProofFile.Honest.K9.goodW_att_clauses
