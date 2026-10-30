-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/GoodAttSeat.lean: "GOOD" (`goodW`) IN FRONT OF THE BATCHING OF AN ATTENTION SEGMENT,
UNDER THE LIBRARY's HEAD AND K9's SEAT: Honest/K9/GoodAtt.lean's theorem with "plain" paid at all ten runs, and what
is still owed gathered in ONE NAMED STRUCTURE. Statements and proofs ON THE VERIFIER's TEXT; no prover is in this
file, and no goal is stated. No probability is in this file.
  `plain_of_none`   a list of claims none of which is an equation's is plain at every slot (kin: K5's
      `plainAt_forms`, at bare forms)
  `objects_plain`, `planes_plain`   so are the lists of the lookup's runs "objects" and "planes", at a seat whose
      claims are bare forms (off the library's `objects_cut`, `objects_answer`, `planes_heard`, `planesRun_cut`)
  `equations_plain`   so is the list of the run "K8.equations": `plain_all`
      (Johnson/Desc/K8/Honest/EqSlots.lean), behind the library's `k8Run_ok` and `take_four`
  `LookLive L p xr k n s`   **WHAT IS STILL OWED, AS ONE STRUCTURE**: a predicate J on states with: it holds behind K9's
      draw from s; every run of the order hands it on; every slot below k, and every slot from `k5End xr k` on below
      n, is live in some run's claims (each clause may spend K5's `HeldLive` too). THE TWO WINDOWS ARE THE LOOKUPS'
      (the calls'; the digits', with K8's first four claims) BY A READING OF THE PLANNER, at k := the ledger's next
      slot in front of K5's hearing, xr := a.own, n := a.nMsg (the three stretches as numbers:
      Honest/K9/GoodAttPlan.lean, over the library's tiling of the plan's slots; which slots the lookups' claims name:
      typed nowhere that we found)
  **`goodW_att`**   from the head, g < 12, `SeatedFree` at 2 g + 1 (which the head gives: `seated_at_head`), the plan
      a of the segment OFF THE PUBLIC PARAMETERS, K5's two public premises, `HeldLive xr k s` and `LookLive`: `goodW p
      ‹the segment's gatherer› s n`, AT EVERY n
The ties between the description's runs and the kinds' texts are the library's: `AttTies`, `at_objects_is`,
`at_planes_is` (with `readers_of_at_planes`), `at_join_is`.
WHAT IS NOT CLAIMED. `HeldLive` at any state. `LookLive` AT ANY STATE: no lemma at a state is at hand for the lookups'
two windows: IT MAY BE UNMEETABLE. That the three windows cover the slots below the public number (n is free here; at
the plan's numbers: Honest/K9/GoodAttPlan.lean), or that k is public. No member: `goodW_att` is called by
Honest/K9/GoodAttLook.lean, GoodAttPlan.lean and FallDebtAtt.lean, at no member; three of the four on "plain" also by
Honest/K9/GoodHead.lean. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.GoodAtt
import Johnson.Desc.ProofFile.Honest.K9.SeatTied
import Johnson.Desc.K8.Honest.EqSlots
import Johnson.Desc.First.Link.Law.SortK3Objects
import Johnson.Desc.First.Link.Law.SortK3Join
import Johnson.Desc.First.Link.Law.SortK3Planes
import Johnson.Desc.First.Link.Law.SortK3PlanesReaders
import Johnson.Desc.First.Batch.Law.K8Run
import Johnson.LPFK9R.LookAttAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll
open H2K5.Honest (HeldLive LiveFits k5End join_state)

/-- A list of claims none of which is an equation's is plain at every slot. -/
theorem plain_of_none (cls : List Claim) (h : ∀ cl ∈ cls, cl.eqFirst = none) (j : ℕ) :
    Desc.K9H.plainAt cls j = true := by
  unfold Desc.K9H.plainAt
  rw [List.all_eq_true]
  intro cl hcl
  rw [h cl hcl]
  rfl

/-- The lookup's run "objects". -/
theorem objects_plain (seat : Desc.K3.Seat S Claim) (hc : ∀ a, (seat.claim a).eqFirst = none) {i : ℕ} {t : S}
    {z : List Claim × S} (h : OnPublicFiles.objectsRun seat i t = .ok z) (j : ℕ) : Desc.K9H.plainAt z.1 j = true := by
  obtain ⟨F, g, e1, e2, _⟩ := OnPublicFiles.objects_cut seat (l := z.1) (s' := z.2) h
  rw [OnPublicFiles.objects_answer seat i e1 e2] at h
  rw [← congrArg Prod.fst (Except.ok.inj h)]
  refine plain_of_none _ (fun cl hcl => ?_) j
  obtain ⟨a, _, rfl⟩ := List.mem_map.1 hcl
  exact hc a

/-- The lookup's run "planes". -/
theorem planes_plain (seat : Desc.K3.Seat S Claim) (hc : ∀ a, (seat.claim a).eqFirst = none) (lm : ℕ)
    (readers : Desc.K3.Readers S) {i : ℕ} {t : S} {z : List Claim × S}
    (h : Desc.K3.planesRun seat lm readers i t = .ok z) (j : ℕ) : Desc.K9H.plainAt z.1 j = true := by
  obtain ⟨F, g, e1, e2⟩ := OnPublicFiles.planes_heard seat lm readers (l := z.1) (s' := z.2) h
  obtain ⟨_, rows, _, _, _, _, e, _⟩ := OnPublicFiles.planesRun_cut seat lm readers (cl := z.1) (s' := z.2) e1 e2 h
  rw [e]
  refine plain_of_none _ (fun cl hcl => ?_) j
  obtain ⟨a, _, rfl⟩ := List.mem_map.1 hcl
  exact hc a

/-- The run "K8.equations". -/
theorem equations_plain {i : ℕ} {t : S} {z : List Claim × S} (h : k8Run.2 i t = .ok z) (j : ℕ) :
    Desc.K9H.plainAt z.1 j = true := by
  obtain ⟨F, tl, funs, tl', F1, _, _, _, he, _⟩ := k8Run_ok i t z.2 z.1 h
  obtain ⟨g, _, hg, _⟩ := take_four he
  exact First.K8.Honest.plain_all he hg j

/-- **What is still owed in front of an attention segment's batching**: the lookups' two windows. -/
structure LookLive (L : Link S ProofFile.Cl) (p : Desc.K9.Where) (xr : OnBytes.Params.AttentionRounds) (k n : ℕ)
    (s : S) : Prop where
  owed : ∃ J : S → Prop,
    (∀ y t₁, (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne y⟩] [] = .ok t₁ → J t₁) ∧
    (∀ o ∈ L.order, ∀ run, At L o run → ∀ m t z, HeldLive xr k t → J t → run m t = .ok z → J z.2) ∧
    ∀ j < n, j < k ∨ k5End xr k ≤ j → ∃ o ∈ L.order, ∀ run, At L o run →
      ∀ m t z, HeldLive xr k t → J t → run m t = .ok z → Desc.K9H.liveAt z.1 j = true

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- **"Good" in front of an attention segment's batching, under the head and K9's seat.** -/
theorem goodW_att (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) {kk : ℕ}
    {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree cF Zp (2 * g + 1) kk Lk p w) (u : HTailF2) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {xr : OnBytes.Params.AttentionRounds} {k : ℕ}
    (gf : LiveFits (First.Att.P.geoOf a.S) xr) (hN : a.NC = a.S.calls.size) (s : S) (n : ℕ)
    (hI : HeldLive xr k s) (hJ : LookLive Lk p xr k n s) :
    goodW p (claimsInBy Lk.each Lk.hear Lk.order) s n := by
  have hm : 2 * g + 1 < 25 := by omega
  obtain ⟨hlk, seg, drawB, kp⟩ := tied_of_seated h hm Sd
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hs := sub_odd g hg
  obtain ⟨h4, g', hg', eg, _⟩ := LPFK9.att_facts h O (2 * g + 1) hm hs
  obtain rfl : g = g' := by omega
  have hA : Bs.G₀.W.A[g]? = some a := by
    rw [O.W]
    exact ha
  obtain ⟨J, Js, Jh, Jl⟩ := hJ.owed
  have i1 : IM.k3Ix (2 * g + 1) false = 1 := by
    show (1 : ℕ) + (if 2 * g + 1 = 24 then 1 else 0) = 1
    rw [if_neg (by omega)]
  have i6 : IM.k3Ix (2 * g + 1) true = 6 := by
    show (6 : ℕ) + (if 2 * g + 1 = 24 then 1 else 0) = 6
    rw [if_neg (by omega)]
  refine goodW_att_at h O hg hs Lk p hlk seg drawB kp u hA gf hN s n hI J Js Jh Jl ?_
  intro o ho run hr m t z hH _ hz j
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl
  · have e := OnPublicFiles.at_objects_is h.scope h.reads O hm false Sd.link (run := run) (by rw [i1]; exact hr)
    rw [e] at hz
    exact objects_plain _ (fun _ => rfl) hz j
  · have e := at_join_is O h4 hg' hA Sd.link hr
    rw [e] at hz
    exact (join_state _ m t z hH hz).1 j
  · obtain ⟨rd, hrd⟩ := OnPublicFiles.readers_of_at_planes h.scope h.reads O hm Sd.link (run := run)
      (by rw [i1]; exact hr)
    obtain ⟨pl, _, e⟩ := OnPublicFiles.at_planes_is h.scope h.reads O hm Sd.link hrd (run := run) (by rw [i1]; exact hr)
    rw [e] at hz
    exact planes_plain _ (fun _ => rfl) _ _ hz j
  · have e := OnPublicFiles.at_objects_is h.scope h.reads O hm true Sd.link (run := run) (by rw [i6]; exact hr)
    rw [e] at hz
    exact objects_plain _ (fun _ => rfl) hz j
  · obtain ⟨A', X, hA', _, Wh⟩ := LPFK9.attOwesC_g h O hg hs Lk p hlk seg drawB kp
    have T := (Wh (fun _ => False)
      (((First.Look.placeAt (P5J.At.X Zp) (2 * g + 1) false).map (·.lm)).getD 0) 0 0 0 u u
      (fun _ hq => hq.elim) (fun _ hq => hq.elim) fun pl e => by rw [e]; rfl).ties
    exact equations_plain (T.tEq run hr m t z.1 z.2 hz) j

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.plain_of_none
#print axioms ProofFile.Honest.K9.objects_plain
#print axioms ProofFile.Honest.K9.planes_plain
#print axioms ProofFile.Honest.K9.equations_plain
#print axioms ProofFile.Honest.K9.goodW_att
#print axioms ProofFile.Honest.K9.LookLive
