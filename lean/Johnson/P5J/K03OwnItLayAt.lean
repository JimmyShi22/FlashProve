-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03OwnItLayAt.lean: THE LOOKUP ARGUMENTS ON THE DIGITS AT THE TWELVE LAYERS' SEGMENTS:
THE ITEM "own" OF hForms: THE PREMISE hOwnIt OF `k03_digForms` (Johnson/P5J/K03DigFormsAt.lean), IN
ITS OWN TEXT (`DigItemR` at formsIn (2 g) (3 + shift .layers) "own"), AT THE CLOSED CONSTANT. **ONE
NAMED PREMISE STAYS BEYOND THE HEAD `AtMgA`: hf: what the segment's readers answer at "front" and
"back" in front of the accept they answer behind it (`Fwd`), UNDER THE ITEM's OWN HANDS: WITHOUT THE
TABLE's PROMISE BEHIND** (the item is a part of what shows that promise).
  `k4_low` (general in the letters; UNDER: the second reader is silent there · `StatesAt` · the
    state has a ledger with its sizes · the three windows end at or below its next): the late slots
    of the feed-forward kind's two runs, as a
    link's reader answers them, lie below the ledger's next: the premise hlow of
    `k3_formsIn_fwd`: all calls: `link_reader`, `reader_test` (Johnson/Top/H/Keep/LateLow.lean,
    FormsPassK3.lean), `StatesAt` and `k4_late_below` (Johnson/Road/K4/InT/Statement.lean,
    LateBelowRun.lean).
  **`k03_ownIt_lay`**: the test in front: off the promise in front (`digits_sorted`, `onQ_front`) ·
    it goes forward: `k3_formsIn_fwd` over `k3_digits_step_pass` (the whole seated step) · two of
    the three windows, the segment and the ledger's sizes: `k03_wins_at` · what the link states:
    `k03_states_lay` (both Johnson/P5J/K03OwnFwdLayAt.lean) · the third window: `k03_win_front`
    (Johnson/P5J/K03WinAt.lean).

Limits. hf is a premise: see above. The head `AtMgA` is a premise; a member of it is proved at
`storedPublicFiles` and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/). At OnBytes.secondHashFunction. The full size
alone.
Nothing on soundness.

-/
import Johnson.P5J.K03DigFormsAt
import Johnson.P5J.K03WinAt
import Johnson.P5J.K03OwnFwdLayAt
import Johnson.Road.K4.InT.LateBelowRun
import Johnson.Top.H.Keep.LateLow
import Johnson.Desc.First.Look.K3DigitsPass
import Johnson.Desc.Sound.MgAt.Runs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit Link Claim)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Pub LayOwn shift)
open VerifiableInference.Desc.K9 (Read readersOfLink statesOfLink LinkHoles holesAt formsIn)
open VerifiableInference.Reads.Pass (Fwd)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Road.K4.InT (StatesAt k4_late_below)
open OnBytes.Model.Layer (Own)

/-- **The late slots of K4's two runs, as a link's reader answers them, lie below the ledger's
next.** -/
theorem k4_low (H : LinkHoles) (l : Link S Claim) (b : ℕ) {pK : Par} {name : String}
    (hn : name = "front" ∨ name = "back") {s : S} {F : Fork} (hs : H.silent b name s = none)
    (hSt : StatesAt (statesOfLink l) b pK name s) (hF : s.fork? = some F)
    (hS : OnBytes.PscRun.Sized F)
    (W : ∀ (a : LayOwn) (o : Own), s.here = .lay a → a.own = some o →
      o.H.tV.p.first + o.H.tV.p.walk.1.length ≤ F.next ∧
      o.H.fo.leaves.first + o.H.fo.leaves.walk.1.length ≤ F.next ∧
      o.wo.toWsMerged.p.first + o.wo.toWsMerged.p.walk.1.length ≤ F.next)
    {R : Read} (h : (readersOfLink H l).forms b name s = some R) : ∀ x ∈ R.late, x.1 < F.next := by
  have hne : (name == "K8.equations") = false := by
    rcases hn with rfl | rfl <;> decide
  obtain ⟨nm, run, cl, t, F', G, hf, hr, hF', hG, -, rfl⟩ := reader_test (link_reader hne hs h)
  obtain rfl : F' = F := Option.some.inj (hF'.symm.trans hF)
  obtain ⟨y, runC, hy, hC, e1⟩ := hSt
  obtain rfl : y = (nm, run) := Option.some.inj (hy.symm.trans hf)
  exact k4_late_below hn hC (e1.symm.trans hr) hF hG hS W

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

set_option maxHeartbeats 4000000 in
/-- **THE ITEM "own" AT THE TWELVE LAYERS' DIGITS.** -/
theorem k03_ownIt_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    {g : ℕ} (hg : g < 12)
    (q) (hq : (h.toAtMg.row 𝔏)[k3K (2 * g) true]? = some q)
    (b') (hb : k3Const (At.X Zp) Zp.first.codes Zp.first.shape (2 * g) true = some b')
    (hf : ∀ (z : ProofFile.InstPub) (u v : S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K (2 * g) true) u →
      h.toAtMg.rch (k3K (2 * g) true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      StepRel b' u.1 v.1 →
      ∀ p ∈ [(2, "front"), (2, "back")], Fwd ((h.toAtMg.𝔇 h.𝔇).Rd (2 * g)) p.1 p.2 u.1 v.1) :
    DigItemR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch (2 * g) q b'
      (.formsIn (2 * g) (3 + shift .layers) "own") := by
  intro B' hN z u τ v hout _ _ hu hr hun
  have hl : 2 * g < 25 := by omega
  have Pc := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  have h24 : headLink (At.X Zp) = 24 := headLink_in_scope h.scope h.reads h.pubOne
  have hsub : linksFull[2 * g]? = some ModelPart.layers := by
    have h0 := List.all_eq_true.1 linksLayFull g (List.mem_range.2 hg)
    simpa using h0
  obtain ⟨-, -, -, cols, hd0⟩ := piece_hears_below
    (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (Run.ckP .two) FrD S ProofFile.Cl _) B' rfl (Pc.back (2 * g) hl true q hq) u τ v hout
  have hd := hN.1.2 _ _ _ _ hd0
  obtain ⟨al, o, hal, ho, hSz, w1, w3, hT⟩ := k03_wins_at h hg z u hr
  have hF : u.1.fork? = some al.F := by simp [S.fork?, hal]
  have w2 := (k03_win_front h hl hb z u hu hun al.F hF o.H.fo hT).1
  have W : ∀ (a : LayOwn) (o' : Own), u.1.here = .lay a → a.own = some o' →
      o'.H.tV.p.first + o'.H.tV.p.walk.1.length ≤ al.F.next ∧
      o'.H.fo.leaves.first + o'.H.fo.leaves.walk.1.length ≤ al.F.next ∧
      o'.wo.toWsMerged.p.first + o'.wo.toWsMerged.p.walk.1.length ≤ al.F.next := by
    intro a o' ha ho'
    obtain rfl : a = al := by
      have := ha.symm.trans hal
      injection this
    obtain rfl : o = o' := Option.some.inj (ho.symm.trans ho')
    exact ⟨w1, w2, w3⟩
  obtain ⟨G, P⟩ := k3_digits_step_pass K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape (IM.k3Place (2 * g) true) b' hb
    (Pc.planOk (2 * g) hl true b' hb) (2 * g) rfl (k03_pieceAt_dig h.toAtMg (2 * g)) u.1 v.1 _ _ hd
    hF hSz
  obtain ⟨Lk, hLk⟩ := k03_link_some h hl
  obtain ⟨pK, hSt⟩ := k03_states_lay h hg Lk hLk
  have hRd := k03_hlink h (2 * g) Lk hLk
  have hsil : ∀ (b : ℕ) (n : String) (s : S),
      (holesAt (At.X Zp) (headLink (At.X Zp)) (2 * g) Lk).silent b n s = none := by
    intro b n s
    unfold holesAt
    rw [h24]
    dsimp only
    rw [if_neg (by rw [beq_iff_eq]; omega)]
  have key : ∀ name, name = "front" ∨ name = "back" → (2, name) ∈ [(2, "front"), (2, "back")] →
      formsIn ((h.toAtMg.𝔇 h.𝔇).Rd (2 * g)) ((h.toAtMg.𝔇 h.𝔇).N.group (2 * g)) 2 name u.1 = true →
      formsIn ((h.toAtMg.𝔇 h.𝔇).Rd (2 * g)) ((h.toAtMg.𝔇 h.𝔇).N.group (2 * g)) 2 name v.1 = true :=
    fun name hn hm hin => k3_formsIn_fwd P _ _ 2 name
      (hf z u v hu hr (not_not.2 hun) ⟨_, _, hd⟩ (2, name) hm)
      (fun R hR => by
        rw [hRd] at hR
        exact k4_low _ Lk 2 hn (hsil 2 name u.1) (hSt name hn u.1) hF hSz W hR) hin
  have eM : (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).more = mgMore :=
    mgAll_more_closed (h.toAtMg.𝔇 h.𝔇) mgBase rfl
  have hfront := onQ_front hu hun
  rw [eM] at hfront
  have mOwn : Pub.formsIn (2 * g) 3 "own" ∈ keptDigits (2 * g) .layers := by simp [keptDigits]
  have ht := hfront _ ((digits_sorted hl hsub).2 _ mOwn)
  have eR : (h.toAtMg.𝔇 h.𝔇).pubD.runs (2 * g) 3 "own" = [(2, "front"), (2, "back")] := by
    show runsAt linksFull (2 * g) 3 "own" = _
    rw [runsAt_of linksFull (2 * g) .layers hsub]
    rfl
  show (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pub (.formsIn (2 * g) 3 "own") (z, v.1) = true
  rw [mgAll_pub, VerifiableInference.Desc.First.pubAll_formsIn, eR] at ht ⊢
  have tF := List.all_eq_true.1 ht (2, "front") (by simp)
  have tB := List.all_eq_true.1 ht (2, "back") (by simp)
  refine List.all_eq_true.2 fun p hp => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact key "front" (Or.inl rfl) (by simp) tF
  · exact key "back" (Or.inr rfl) (by simp) tB

end P5J

#print axioms P5J.k4_low
#print axioms P5J.k03_ownIt_lay
