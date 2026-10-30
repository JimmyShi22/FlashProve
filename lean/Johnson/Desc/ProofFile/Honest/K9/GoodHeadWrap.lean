-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/GoodHeadWrap.lean: `HeadLive` (Honest/K9/GoodHead.lean), AND SO "GOOD" IN FRONT OF THE
OUTPUT HEAD's SEGMENT's BATCHING, FROM THE HOUSES' SHARES: the twin, at l = 24, of `lookLive_of_clauses`
(Honest/K9/GoodAttWrap.lean). Statements and proofs ON THE VERIFIER's TEXT; no definition; no goal is stated. THE
NUMBERS ARE LETTERS HERE.
  **`headLive_of_shares`** the invariant of the output head's own rounds (K6) is a LETTER Kp. PREMISES: K6's
      eight: kDraw · kHand (Kp rides the draw and every run) · kLive (each slot j with b ≤ j, j + 1 < e is live in some
      run's claims) · kPlain · kUn (its three runs and "join": plain everywhere; they name no slot from e on) · kKeys
      (the caller's key vectors name no slot below b) · kBits · kPins (the caller's readers name no slot: stated at
      WHATEVER readers `K3Lot.readersAt` hands at 24) · the lookups' clause at both lookups at s (JC · JD) · Kp at s ·
      seven on numbers: pC.first = 0 · the calls' length = b · b ≤ e · e = pD.first · sv + 1 = e · the digits' end =
      first · n ≤ first + 2 lk + 3. HOW: `headLive_of_readers`; slot by slot: below b the calls' three windows
      (`window_iff`; `objects_live` · `planes_live` · `join_live` behind the sealed `at_objects_is` · `at_planes_is` ·
      `HeadTies.tJoin` at `ties_at_head`'s letters) · from b to e − 2 kLive · e − 1 = sv is left out by `HeadLive`
      itself · from pD.first on the digits' three windows (`objects_live`; `four8_live` behind `tEq`, `k8Run_ok`,
      `take_four`, `live_eq`) · unnamed at the merge's slot: `objects_unnamed` · `planes_unnamed` · `four8_unnamed` ·
      kUn
  `goodW_head_shares` `goodW_head` at that `HeadLive`: with K11's `MergeLive lk first sv s` as one premise more
WHAT IS NOT CLAIMED. ANY OF THE PREMISES AT ANY STATE. NO MEMBER: no state, link or Kp is shown at which they hold
together. That the seven sentences on numbers can be met together: Honest/K9/GoodHeadNums.lean meets six; the seventh
(sv + 1 = e) is met in GoodHeadHanded.lean alone, from a premise. pC and pD are letters too: only their shapes and the
two clauses tie them. `headLive_of_shares` stands under set_option maxHeartbeats 1000000. u and kk are letters; u is
read by nothing in the conclusions. Called by Honest/K9/GoodHeadNums.lean alone. At the full size and the format's
second hash function alone, as h. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.GoodHeadLook
import Johnson.Desc.ProofFile.Honest.K9.GoodAttEight
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.Unnamed
import Johnson.Desc.Kinds.Law.K6AllRunsFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.K3 (faceOf)
open Johnson.Desc.First.ForkMerge.Live (MergeLive)
open ProofFile.Honest.K3 (windowOf Run)
open ProofFile.Honest.K3.Good.Live (Clause KeysClear BitsClear PinsClear objects_live join_live planes_live window_iff
  digits_reading four8_live four8_unnamed objects_unnamed planes_unnamed)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

set_option maxHeartbeats 1000000 in
/-- **`HeadLive` FROM THE PARTS' SHARES**: K6's invariant is a letter `Kp`; what it brings stands as eight
premises; the lookups' clause stands at both lookups; seven premises are on numbers. -/
theorem headLive_of_shares (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {kk : ℕ} {Lk : Link S ProofFile.Cl}
    {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp 24 kk Lk p w) (u : HTailF2)
    {pC pD : First.Look.P} {hsC hsD : Forest.Shape} (spC : pC.shape = some hsC) (spD : pD.shape = some hsD)
    (Kp : S → Prop) {b e lk first sv n : ℕ}
    (kDraw : ∀ t y t₁, (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide t [⟨[], drawnOne y⟩] [] = .ok t₁ →
      Kp t → Kp t₁)
    (kHand : ∀ o ∈ Lk.order, ∀ run, At Lk o run → ∀ m t z, Kp t → run m t = .ok z → Kp z.2)
    (kLive : ∀ j, b ≤ j → j + 1 < e → ∃ o ∈ Lk.order, ∀ run, At Lk o run → ∀ m t z, Kp t → run m t = .ok z →
      Desc.K9H.liveAt z.1 j = true)
    (kPlain : ∀ o ∈ [(3, "norm"), (3, "join"), (3, "policy"), (3, "logits")], ∀ run, At Lk o run → ∀ m t z,
      run m t = .ok z → ∀ j, Desc.K9H.plainAt z.1 j = true)
    (kUn : ∀ j, e ≤ j → ∀ o ∈ [(3, "norm"), (3, "join"), (3, "policy"), (3, "logits")], ∀ run, At Lk o run →
      ∀ m t z, Kp t → run m t = .ok z → Desc.K9H.unnamedAt z.1 j = true)
    (kKeys : ∀ t, Kp t → ∀ j < b, KeysClear (Kinds.Head.callerKeys
      (Kinds.Head.parOf (P5J.At.X Zp).hS (Kinds.Head.Law.workOf (P5J.At.X Zp)))
      (Kinds.Head.seatAt (P5J.At.X Zp).hS (Kinds.Head.Law.readsOf (P5J.At.X Zp)))) t j)
    (kBits : ∀ rd, K3Lot.readersAt (P5J.At.X Zp) 24 = some rd → ∀ t j, BitsClear rd t j)
    (kPins : ∀ rd, K3Lot.readersAt (P5J.At.X Zp) 24 = some rd → ∀ t j, PinsClear rd t j)
    (f0 : pC.first = 0) (eb : Forest.elems hsC = b) (hbe : b ≤ e) (ee : e = pD.first) (esv : sv + 1 = e)
    (ef : pD.first + Forest.elems hsD = first) (hn : n ≤ first + 2 * lk + 3)
    (s : S) (K : Kp s) (JC : Clause pC s.lookHeard?) (JD : Clause pD (s.tl?.bind (·.heard))) :
    HeadLive Lk p lk first sv n s := by
  have hm : 24 < 25 := by omega
  obtain ⟨hlk, seg, drawB, kp⟩ := tied_of_seated h hm Sd
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hs : IM.subAt 24 = .head := rfl
  have ord : Lk.order = First.orderOf .head := by
    rw [← hs]
    exact seg.order
  obtain ⟨l', nU, T⟩ := Kinds.Head.Law.Five.ties_at_head h Sd.link
  have rdX : ∀ rd, K3Lot.readersAt Bs.G₀.W 24 = some rd → K3Lot.readersAt (P5J.At.X Zp) 24 = some rd := by
    intro rd e
    rw [O.W] at e
    exact e
  -- the digits' clause, out of the spelling in which it rests
  have J2 : ∀ t : S, Clause pD ((numOf u t).1.bind (·.heard)) → Clause pD (t.tl?.bind (·.heard)) := by
    intro t c
    rwa [digits_reading] at c
  -- "K8.equations": its first four claims
  have eq8 : ∀ run, At Lk (5, "K8.equations") run → ∀ m t z, Clause pD (t.tl?.bind (·.heard)) → run m t = .ok z →
      ∃ tl gg, Clause pD (some gg) ∧ (∀ j, Desc.K9H.liveAt z.1 j = Desc.K9H.liveAt (four8 tl gg) j) ∧
        ∀ j, Desc.K9H.unnamedAt z.1 j = Desc.K9H.unnamedAt (four8 tl gg) j := by
    intro run hr m t z J hz
    obtain ⟨F, tl, funs, tl', F1, _, etl, _, he, _⟩ := k8Run_ok m t z.2 z.1 (T.tEq run hr m t z.1 z.2 hz)
    obtain ⟨gg, _, hgg, _⟩ := take_four he
    rw [etl] at J
    have J' : Clause pD (some gg) := by
      have e : (some tl : Option HTailF2).bind (·.heard) = some gg := hgg
      rwa [e] at J
    exact ⟨tl, gg, J', First.K8.Honest.live_eq he hgg, First.K8.Honest.unnamed_eq he hgg⟩
  refine headLive_of_readers h Sd u lk first sv n s Kp kDraw kHand
    (fun y c => Clause pC y ∧ Clause pD (c.1.bind (·.heard))) K ⟨JC, by rw [digits_reading]; exact JD⟩ ?_ ?_ ?_
  · intro j hj hsv hjw
    have hjf : j < first := by omega
    by_cases h1 : j < b
    · obtain ⟨rn, hr⟩ := (window_iff hsC j).1 (by omega)
      cases rn with
      | objects =>
        refine ⟨(2, "objects"), by rw [ord]; decide, fun run hrun m t z _ _ hJ hz => ?_⟩
        have e := OnPublicFiles.at_objects_is h.scope h.reads O hm false Sd.link (run := run) hrun
        rw [e] at hz
        have c := objects_live (OnPublicFiles.seatOf K3Lot.ofForm false) (fun _ => rfl) (fun _ => rfl) spC hz hJ.1 hr
        rwa [f0, Nat.zero_add] at c
      | planes =>
        refine ⟨(2, "planes"), by rw [ord]; decide, fun run hrun m t z _ _ hJ hz => ?_⟩
        obtain ⟨rd, hrd⟩ := OnPublicFiles.readers_of_at_planes h.scope h.reads O hm Sd.link (run := run) hrun
        obtain ⟨pl, _, e⟩ := OnPublicFiles.at_planes_is h.scope h.reads O hm Sd.link hrd (run := run) hrun
        rw [e] at hz
        have c := planes_live _ (fun _ => rfl) (fun _ => rfl) _ _ spC hz hJ.1 hr (kBits rd (rdX rd hrd) t _)
        rwa [f0, Nat.zero_add] at c
      | join =>
        refine ⟨(3, "join"), by rw [ord]; decide, fun run hrun m t z _ hK hJ hz => ?_⟩
        have c := join_live _ (fun _ => rfl) (fun _ => rfl) _ spC (T.tJoin run hrun m t z.1 z.2 hz) hJ.1 hr
          (kKeys t hK _ (by omega))
        rwa [f0, Nat.zero_add] at c
    · by_cases h2 : j < pD.first
      · obtain ⟨o, ho, H⟩ := kLive j (by omega) (by omega)
        exact ⟨o, ho, fun run hr m t z _ hK _ hz => H run hr m t z hK hz⟩
      · have hlt : j - pD.first < Forest.elems hsD := by omega
        have ej : pD.first + (j - pD.first) = j := by omega
        obtain ⟨rn, hr⟩ := (window_iff hsD (j - pD.first)).1 hlt
        cases rn with
        | objects =>
          refine ⟨(7, "objects"), by rw [ord]; decide, fun run hrun m t z _ _ hJ hz => ?_⟩
          have e := OnPublicFiles.at_objects_is h.scope h.reads O hm true Sd.link (run := run) hrun
          rw [e] at hz
          have c := objects_live (OnPublicFiles.seatOf K3Lot.ofForm true) (fun _ => rfl) (fun _ => rfl) spD hz
            (J2 t hJ.2) hr
          rwa [ej] at c
        | planes =>
          refine ⟨(5, "K8.equations"), by rw [ord]; decide, fun run hrun m t z _ _ hJ hz => ?_⟩
          obtain ⟨tl, gg, J', eL, -⟩ := eq8 run hrun m t z (J2 t hJ.2) hz
          rw [eL, ← ej]
          exact four8_live tl spD J' (Or.inl hr)
        | join =>
          refine ⟨(5, "K8.equations"), by rw [ord]; decide, fun run hrun m t z _ _ hJ hz => ?_⟩
          obtain ⟨tl, gg, J', eL, -⟩ := eq8 run hrun m t z (J2 t hJ.2) hz
          rw [eL, ← ej]
          exact four8_live tl spD J' (Or.inr hr)
  · exact fun o ho run hr m t z _ _ _ hz => kPlain o ho run hr m t z hz
  · intro o ho run hrun m t z _ hK hJ hz
    have oC : ProofFile.Honest.K3.Good.Live.Outside pC hsC (first + 2 * lk + 2) := Or.inr (by omega)
    have oD : ProofFile.Honest.K3.Good.Live.Outside pD hsD (first + 2 * lk + 2) := Or.inr (by omega)
    have he : e ≤ first + 2 * lk + 2 := by omega
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have e := OnPublicFiles.at_objects_is h.scope h.reads O hm false Sd.link (run := run) hrun
      rw [e] at hz
      exact objects_unnamed (OnPublicFiles.seatOf K3Lot.ofForm false) (fun _ => rfl) spC hz hJ.1 oC
    · exact kUn _ he _ (by simp) run hrun m t z hK hz
    · exact kUn _ he _ (by simp) run hrun m t z hK hz
    · exact kUn _ he _ (by simp) run hrun m t z hK hz
    · obtain ⟨rd, hrd⟩ := OnPublicFiles.readers_of_at_planes h.scope h.reads O hm Sd.link (run := run) hrun
      obtain ⟨pl, _, e⟩ := OnPublicFiles.at_planes_is h.scope h.reads O hm Sd.link hrd (run := run) hrun
      rw [e] at hz
      exact planes_unnamed _ (fun _ => rfl) _ _ spC hz hJ.1 oC (kBits rd (rdX rd hrd) t _) (kPins rd (rdX rd hrd) t _)
    · have e := OnPublicFiles.at_objects_is h.scope h.reads O hm true Sd.link (run := run) hrun
      rw [e] at hz
      exact objects_unnamed (OnPublicFiles.seatOf K3Lot.ofForm true) (fun _ => rfl) spD hz (J2 t hJ.2) oD
    · obtain ⟨tl, gg, J', -, eU⟩ := eq8 run hrun m t z (J2 t hJ.2) hz
      rw [eU]
      exact four8_unnamed tl spD J' oD
    · exact kUn _ he _ (by simp) run hrun m t z hK hz

/-- **"Good" in front of the head's segment's batching, from the houses' shares and K11's clause at the state**:
`goodW_head` with `HeadLive` had from `headLive_of_shares`. -/
theorem goodW_head_shares (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {kk : ℕ} {Lk : Link S ProofFile.Cl}
    {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp 24 kk Lk p w) (u : HTailF2)
    {pC pD : First.Look.P} {hsC hsD : Forest.Shape} (spC : pC.shape = some hsC) (spD : pD.shape = some hsD)
    (Kp : S → Prop) {b e lk first sv n : ℕ}
    (kDraw : ∀ t y t₁, (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide t [⟨[], drawnOne y⟩] [] = .ok t₁ →
      Kp t → Kp t₁)
    (kHand : ∀ o ∈ Lk.order, ∀ run, At Lk o run → ∀ m t z, Kp t → run m t = .ok z → Kp z.2)
    (kLive : ∀ j, b ≤ j → j + 1 < e → ∃ o ∈ Lk.order, ∀ run, At Lk o run → ∀ m t z, Kp t → run m t = .ok z →
      Desc.K9H.liveAt z.1 j = true)
    (kPlain : ∀ o ∈ [(3, "norm"), (3, "join"), (3, "policy"), (3, "logits")], ∀ run, At Lk o run → ∀ m t z,
      run m t = .ok z → ∀ j, Desc.K9H.plainAt z.1 j = true)
    (kUn : ∀ j, e ≤ j → ∀ o ∈ [(3, "norm"), (3, "join"), (3, "policy"), (3, "logits")], ∀ run, At Lk o run →
      ∀ m t z, Kp t → run m t = .ok z → Desc.K9H.unnamedAt z.1 j = true)
    (kKeys : ∀ t, Kp t → ∀ j < b, KeysClear (Kinds.Head.callerKeys
      (Kinds.Head.parOf (P5J.At.X Zp).hS (Kinds.Head.Law.workOf (P5J.At.X Zp)))
      (Kinds.Head.seatAt (P5J.At.X Zp).hS (Kinds.Head.Law.readsOf (P5J.At.X Zp)))) t j)
    (kBits : ∀ rd, K3Lot.readersAt (P5J.At.X Zp) 24 = some rd → ∀ t j, BitsClear rd t j)
    (kPins : ∀ rd, K3Lot.readersAt (P5J.At.X Zp) 24 = some rd → ∀ t j, PinsClear rd t j)
    (f0 : pC.first = 0) (eb : Forest.elems hsC = b) (hbe : b ≤ e) (ee : e = pD.first) (esv : sv + 1 = e)
    (ef : pD.first + Forest.elems hsD = first) (hn : n ≤ first + 2 * lk + 3)
    (s : S) (hI : MergeLive lk first sv s) (K : Kp s) (JC : Clause pC s.lookHeard?)
    (JD : Clause pD (s.tl?.bind (·.heard))) :
    goodW p (claimsInBy Lk.each Lk.hear Lk.order) s n :=
  goodW_head h Sd u s n hI
    (headLive_of_shares h Sd u spC spD Kp kDraw kHand kLive kPlain kUn kKeys kBits kPins f0 eb hbe ee esv ef hn s K JC
      JD)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.headLive_of_shares
#print axioms ProofFile.Honest.K9.goodW_head_shares
