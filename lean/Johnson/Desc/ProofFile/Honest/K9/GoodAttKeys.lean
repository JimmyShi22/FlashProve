-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/GoodAttKeys.lean: FOR K9's FALL ON THE FREE SLOT, AT AN ATTENTION SEGMENT: THE TWO
THEOREMS OF Honest/K9/GoodAttWrap.lean WITH THEIR NAMED PREMISE hkeys PAID, UNDER THE HEAD, BY K5's HOUSE's THEOREM.
PAID: NO NEW PREMISE COMES IN FOR IT. OF THE TWO NAMED PREMISES ONE IS LEFT, h8; ALL ELSE OWED STANDS UNDER "WHAT IS NOT
CLAIMED". The statements are GoodAttWrap.lean's own, cut by program, with that binder struck. Statements and proofs ON
THE VERIFIER's TEXT; no prover is in this file, and no goal is stated. No probability is in this file.
  **`keysClear_at_join`**   under the head, g < 12, the segment's plan a: at every state with `HeldLive a.own
      (Forest.elems a.fs)`: the lookups' `KeysClear (P.keysOfO a) t j` at each j of the window of "join". By K5's
      `keysClear_att` (Honest/K5/Law/KeysClearAt.lean: no key form names a slot in front of k or from `k5End`
      on, under `GeoFits` and `HeldLive`) · `GeoFits`: public numbers: the field geo of `public_at_head`
      (Johnson/Desc/K5/Honest/Law/PublicAtHead.lean) · that the window lies below `Forest.elems a.fs`: the lookups'
      `window_iff`: had because k is SET to that number; that K5's hearing starts there is not had
  **`lookLive_of_clauses_keys`**, **`goodW_att_clauses_keys`**   `LookLive` and `goodW` at the plan's own numbers, from
      JC, JD and h8 (`goodW`: and `HeldLive` at s)
WHAT IS NOT CLAIMED. All that Honest/K9/GoodAttWrap.lean's head does not claim, but hkeys: JC, JD or `HeldLive` at any
state; the carriage, which is ours and is not typed; that K5's hearing begins at the slot `Forest.elems a.fs`; h8. NO
MEMBER. The three are called by no line but one another's. Nothing on any property.
GROUND: beneath this file, beside the sealed library, lie 188 files, this one among them: what lies beneath
Honest/K9/GoodAttWrap.lean, and three more of K5's house's (Honest/K5/Law/KeysClearAt.lean;
Johnson/Desc/K5/Honest/Law/KeysWindow.lean, HeardWindow.lean): reading copies, all but ours. At the full size and the
format's second hash function alone: the head's.
-/
import Johnson.Desc.ProofFile.Honest.K9.GoodAttWrap
import Johnson.Desc.ProofFile.Honest.K5.Law.KeysClearAt
import Johnson.Desc.K5.Honest.Law.PublicAtHead

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
open ProofFile.Honest.K3.Good.Live (Clause KeysClear window_iff)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- **The premise hkeys of Honest/K9/GoodAttWrap.lean, PAID under the head**: at every state with K5's
condition the caller's key forms name no slot of the window of "join". -/
theorem keysClear_at_join (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12)
    {a : OnBytes.Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a) (t : S)
    (hH : HeldLive a.own (Forest.elems a.fs) t) (j : ℕ) (hj : j ∈ windowOf (faceOf a.fs) Run.join) :
    KeysClear (First.Att.P.keysOfO a) t j :=
  H2K5.Honest.Window.keysClear_att a (H2K5.Honest.public_at_head h hg ha).geo hH
    (Or.inl ((window_iff a.fs j).2 ⟨Run.join, hj⟩))

/-- **`LookLive` at the plan's own numbers, from the lookups' clause at both lookups and ONE named premise.** -/
theorem lookLive_of_clauses_keys (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) {kk : ℕ}
    {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree cF Zp (2 * g + 1) kk Lk p w) (u : HTailF2) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) (2 * g + 1) false = some pC) (hD : placeAt (P5J.At.X Zp) (2 * g + 1) true = some pD)
    (s : S) (JC : Clause pC s.lookHeard?) (JD : Clause pD (s.tl?.bind (·.heard)))
    (h8 : ∀ j, j ∈ windowOf (faceOf a.seam.tl.f9) Run.planes ∨ j ∈ windowOf (faceOf a.seam.tl.f9) Run.join →
      ∀ run, At Lk (4, "K8.equations") run → ∀ m t z, HeldLive a.own (Forest.elems a.fs) t →
        Clause pD (t.tl?.bind (·.heard)) → run m t = .ok z → Desc.K9H.liveAt z.1 (pD.first + j) = true) :
    LookLive Lk p a.own (Forest.elems a.fs) w.2.2.filled s :=
  lookLive_of_clauses h hg Sd u ha hC hD s JC JD (keysClear_at_join h hg ha) h8

/-- **"Good" at the plan's own numbers, from the kinds' clauses at the state and ONE named premise.** -/
theorem goodW_att_clauses_keys (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : ℕ} (hg : g < 12) {kk : ℕ}
    {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere}
    (Sd : SeatedFree cF Zp (2 * g + 1) kk Lk p w) (u : HTailF2) {a : OnBytes.Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) (2 * g + 1) false = some pC) (hD : placeAt (P5J.At.X Zp) (2 * g + 1) true = some pD)
    (s : S) (hI : HeldLive a.own (Forest.elems a.fs) s) (JC : Clause pC s.lookHeard?)
    (JD : Clause pD (s.tl?.bind (·.heard)))
    (h8 : ∀ j, j ∈ windowOf (faceOf a.seam.tl.f9) Run.planes ∨ j ∈ windowOf (faceOf a.seam.tl.f9) Run.join →
      ∀ run, At Lk (4, "K8.equations") run → ∀ m t z, HeldLive a.own (Forest.elems a.fs) t →
        Clause pD (t.tl?.bind (·.heard)) → run m t = .ok z → Desc.K9H.liveAt z.1 (pD.first + j) = true) :
    goodW p (claimsInBy Lk.each Lk.hear Lk.order) s w.2.2.filled :=
  goodW_att_clauses h hg Sd u ha hC hD s hI JC JD (keysClear_at_join h hg ha) h8

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.keysClear_at_join
#print axioms ProofFile.Honest.K9.lookLive_of_clauses_keys
#print axioms ProofFile.Honest.K9.goodW_att_clauses_keys
