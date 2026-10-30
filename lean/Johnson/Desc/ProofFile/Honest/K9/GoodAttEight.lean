-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/GoodAttEight.lean: FOR K9's FALL ON THE FREE SLOT, AT AN ATTENTION SEGMENT: THE TWO
THEOREMS OF Honest/K9/GoodAttKeys.lean WITH THEIR LAST NAMED PREMISE h8 PAID, UNDER THE HEAD AND K9's SEAT, BY THE
LOOKUPS' AND K8's HOUSES' THEOREMS. PAID: NO NEW PREMISE COMES IN FOR IT. WHAT IS LEFT ARE THE HOUSES' CLAUSES AT THE
STATE ITSELF; ALL ELSE OWED STANDS UNDER "WHAT IS NOT CLAIMED". The statements are GoodAttKeys.lean's own, cut by
program, with that binder struck. Statements and proofs ON THE VERIFIER's TEXT; no prover is in this file, and no goal
is stated. No probability is in this file.
  **`eight_live_att`**   at every yes of the run that the link states under (4, "K8.equations"), at a state that meets
      the lookups' `Clause` at the digits' place: each slot of the digits' windows of "planes" and "join" is live in the
      run's claims. By: the library's tie of that run to K8's equations (`LPFK9.attOwesC_g`'s ties, field tEq;
      `k8Run_ok`; `take_four`: the data are the state's own, and what they hold as heard is what the clause reads) ·
      K8's `live_eq` (Johnson/Desc/K8/Honest/EqSlots.lean: "live" in the run's list is "live" in its first four
      claims) · the lookups' `four8_live` (Honest/K3/Good/Live/Shares.lean: these four are live on the two windows, from
      the clause alone) · the place's shape: their `digits_att`
  **`lookLive_of_clauses_all`**   `LookLive Lk p a.own (Forest.elems a.fs) w.2.2.filled s` FROM JC AND JD ALONE: the
      lookups' clause at what s holds as heard by the lookup on the calls and on the digits
  **`goodW_att_clauses_all`**   `goodW p ‹the segment's gatherer› s w.2.2.filled` from JC, JD and K5's `HeldLive
      a.own (Forest.elems a.fs) s`
WHAT IS NOT CLAIMED. JC, JD OR `HeldLive` AT ANY STATE: each kind has its clause behind its own member's accepting
step, from its mark's silence, under premises of its own (among them that the member's draws can be drawn); THE CARRIAGE
FROM THERE TO THE STATE IN FRONT OF THE BATCHING IS OURS AND IS NOT TYPED; k is SET to `Forest.elems a.fs`: that K5's
hearing begins at that slot is not had. NO MEMBER: no state is shown at which the three hold together. The head's
segment and the feed-forward ones. The three are called by no line but one another's. Nothing on any property.
GROUND: beneath this file, beside the sealed library, lie 191 files, this one among them: what lies beneath
Honest/K9/GoodAttKeys.lean, and two more of the lookups' (Honest/K3/Good/Live/Shares.lean, Forms.lean): reading copies,
all but ours. At the full size and the format's second hash function alone: the head's.
-/
import Johnson.Desc.ProofFile.Honest.K9.GoodAttKeys
import Johnson.Desc.ProofFile.Honest.K3.Good.Live.Shares

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
open ProofFile.Honest.K3.Good.Live (Clause four8_live digits_att)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- **The premise h8 of Honest/K9/GoodAttWrap.lean, PAID under the head and K9's seat**: each slot of the digits'
windows of "planes" and "join" is live in the claims of "K8.equations", at every yes at a state that meets the digits'
clause. -/
theorem eight_live_att (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) {kk : ℕ}
    {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree cF Zp (2 * g + 1) kk Lk p w) (u : HTailF2) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {pD : First.Look.P}
    (hD : placeAt (P5J.At.X Zp) (2 * g + 1) true = some pD) (j : ℕ)
    (hj : j ∈ windowOf (faceOf a.seam.tl.f9) Run.planes ∨ j ∈ windowOf (faceOf a.seam.tl.f9) Run.join)
    (run : ℕ → S → Except String (List ProofFile.Cl × S)) (hr : At Lk (4, "K8.equations") run) (m : ℕ) (t : S)
    (z : List ProofFile.Cl × S) (J : Clause pD (t.tl?.bind (·.heard))) (hz : run m t = .ok z) :
    Desc.K9H.liveAt z.1 (pD.first + j) = true := by
  have hm : 2 * g + 1 < 25 := by omega
  obtain ⟨hlk, seg, drawB, kp⟩ := tied_of_seated h hm Sd
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hs := sub_odd g hg
  obtain ⟨sD, -, -⟩ := digits_att h.pubOne (H2K5.Door.scope_all h).1 ha hD
  obtain ⟨A', X, hA', _, Wh⟩ := LPFK9.attOwesC_g h O hg hs Lk p hlk seg drawB kp
  have T := (Wh (fun _ => False)
    (((First.Look.placeAt (P5J.At.X Zp) (2 * g + 1) false).map (·.lm)).getD 0) 0 0 0 u u
    (fun _ hq => hq.elim) (fun _ hq => hq.elim) fun pl e => by rw [e]; rfl).ties
  obtain ⟨F, tl, funs, tl', F1, _, etl, _, he, _⟩ := k8Run_ok m t z.2 z.1 (T.tEq run hr m t z.1 z.2 hz)
  obtain ⟨gg, _, hgg, _⟩ := take_four he
  rw [etl] at J
  have J' : Clause pD (some gg) := by
    have e : (some tl : Option HTailF2).bind (·.heard) = some gg := hgg
    rwa [e] at J
  rw [First.K8.Honest.live_eq he hgg]
  exact four8_live tl sD J' hj

/-- **`LookLive` at the plan's own numbers, from the lookups' clause at both lookups: NO NAMED PREMISE IS LEFT BESIDE
THEM.** -/
theorem lookLive_of_clauses_all (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) {kk : ℕ}
    {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree cF Zp (2 * g + 1) kk Lk p w) (u : HTailF2) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) (2 * g + 1) false = some pC) (hD : placeAt (P5J.At.X Zp) (2 * g + 1) true = some pD)
    (s : S) (JC : Clause pC s.lookHeard?) (JD : Clause pD (s.tl?.bind (·.heard))) :
    LookLive Lk p a.own (Forest.elems a.fs) w.2.2.filled s :=
  lookLive_of_clauses_keys h hg Sd u ha hC hD s JC JD
    fun j hj run hr m t z _ J hz => eight_live_att h hg Sd u ha hD j hj run hr m t z J hz

/-- **"Good" at the plan's own numbers, from two houses' three clauses at the state.** -/
theorem goodW_att_clauses_all (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) {kk : ℕ}
    {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree cF Zp (2 * g + 1) kk Lk p w) (u : HTailF2) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) (2 * g + 1) false = some pC) (hD : placeAt (P5J.At.X Zp) (2 * g + 1) true = some pD)
    (s : S) (hI : HeldLive a.own (Forest.elems a.fs) s) (JC : Clause pC s.lookHeard?)
    (JD : Clause pD (s.tl?.bind (·.heard))) :
    goodW p (claimsInBy Lk.each Lk.hear Lk.order) s w.2.2.filled :=
  goodW_att_clauses_keys h hg Sd u ha hC hD s hI JC JD
    fun j hj run hr m t z _ J hz => eight_live_att h hg Sd u ha hD j hj run hr m t z J hz

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.eight_live_att
#print axioms ProofFile.Honest.K9.lookLive_of_clauses_all
#print axioms ProofFile.Honest.K9.goodW_att_clauses_all
