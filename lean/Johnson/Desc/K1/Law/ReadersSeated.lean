-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ReadersSeated.lean: k01_fifty_atBase's BINDER hRd (what a run's reader answers in
front of a later sub-protocol of kind K1 it answers behind) PAID AT ALL TWELVE ATTENTION SEGMENTS AND
AT THE LOOKUP's RUNS OF ALL TWELVE SEGMENTS OF THE SORT "layers", AT BOTH LATER PLACES; what is left
is named. Statements with their proofs: calls.

How. (1) Both later sub-protocols leave what Q.restOf keeps (Johnson/Desc/K1/Law/ReadersStayQ.lean),
so a link's readers answer alike wherever the run that the link states is a member of Q.Respects
(fwd_later, Q.pairStays_of_respects). (2) The seats' forms say what the opened
chain's links state: IM.k3_of, IM.k4_of, IM.k5_of (Johnson/IMR/K3Seat.lean, K4Seat.lean,
K5Seat.lean): the lot's own sub-protocol, alone, each run behind the seat's guard (IM.claims_alone).
(3) The guard keeps Q.Respects (Q.respects_guarded, Q.sameReply_alike). (4) The lots' runs are the
kinds' own: a peeling of the makers' texts (theOwn_calls_of .. k3At_calls_respects,
k5_claims_respects), then Johnson/Desc/K1/Law/RespectsAttQ.lean's members.

Main names:
  laterAlike_blkL · fwd_later · Q.pairStays_of_respects
  respects_laid · respects_states      the seat's form; a link's list of runs
  states_look         **block 1 of every link l < 24** (the lookup on the calls; at an attention
                      segment with "planes")
  states_k5           **block 2 of every attention link** ("first", "keys", "join", "second")
  states_k4           block 2 of every link of the sort "layers", FROM hK4
  runsBelow           [kernel] the runs of runsL l false, l < 24, stand in blocks 1 and 2 and none
                      is the approximate range proof's; runsBelow_fails: the test can fail
  fwd_below           Fwd at every run of a link l < 24
  hRd_seated          **hRd, to the letter.**
PREMISES THAT STAY IN hRd_seated, BY NAME.
  hS hR O hDlk        binders that the top has.
  hlk                 ON THE LETTER Dm.lk: it is the opened chain's list of links.
  hX · hW             two tests on public values: the output head's link is number 24.
  hK4                 **K4's FILES'**: each run of K4's lot's sub-protocols ("front", "back") is a
                      member of Q.Respects. Fenced: at the places of the lot's own list.
  hHead               **THE OUTPUT HEAD's SEVEN RUNS**, as Fwd, behind the accept and the promise.
What is not claimed. hK4, hHead. That a sub-protocol accepts. Nothing on soundness, on an honest
prover or on hiding.
THE RECURSION LIMIT IS RAISED IN THIS FILE (maxRecDepth 1000000): for the kernel's evaluations'
elaboration alone.

-/
import Johnson.Desc.K1.Law.HRdAtBase
import Johnson.Desc.K1.Law.RespectsAttQ
import Johnson.IMR.K3Seat
import Johnson.IMR.K4Seat
import Johnson.IMR.K5Seat
import Johnson.Top.H.K3StatedRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain Link FileDescription Place)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More PubData flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull runsAt MsgT MgData CellsQ mgAll d13 mgBase)
open VerifiableInference.OnPublicFiles (headLink RunK andThen_quiet_runs_of)
open VerifiableInference.Desc.K13.Law (openAt)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.K9 (Readers LinkHoles statesOfLink readersOfLink holesAt)
open VerifiableInference.Reads.Pass (Fwd)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix)
open ProofFile (Cl)

/-! ## 1 Both later places -/

theorem laterAlike_blkL (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ)) : Q.LaterAlike (blkL Z G₀ l d X arrs) := by
  cases d with
  | true => exact Q.laterAlike_laterAt _ _ _ _ _ _
  | false => exact Q.laterAlike_k1Reads _ _ _ _ _ _

/-- **Fwd over the accept of either later place.** -/
theorem fwd_later {Pp : Type} (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ)) (H : LinkHoles) (lk : Link S Claim) (p : ℕ × String)
    (hp : Q.PairStays H lk p) (x x' : Pp × S) (hy : YesOf (blkL Z G₀ l d X arrs) x x') :
    Fwd (readersOfLink H lk) p.1 p.2 x.2 x'.2 := by
  obtain ⟨_, rs, gs, _, hd⟩ := hy
  intro R hR
  rw [Q.readersOfLink_alike H lk p hp (laterAlike_blkL Z G₀ l d X arrs _ _ _ _ hd)]
  exact hR

/-- Away from the output head's segment the second reader is silent. -/
theorem Q.pairStays_of_respects (X : OnBytes.Model.Verify.Public) (mH m : ℕ) (hm : m ≠ mH)
    (lk : Link S Claim) (p : ℕ × String) (hn : (p.2 == "K8.equations") = false)
    (hr : ∀ r, (statesOfLink lk p.1).find? (fun r => r.1 == p.2) = some r → Q.Respects r.2) :
    Q.PairStays (holesAt X mH m lk) lk p := by
  unfold Q.PairStays
  rw [hn]
  refine ⟨hr, fun s s' _ => ?_⟩
  unfold holesAt
  have e : (m == mH) = false := by simpa using hm
  simp only [e]
  rfl

/-! ## 2 The seat's form -/

/-- The seated sub-protocol's runs are members where the lot's are. -/
theorem respects_laid {b b' : Block S Cl} {name : String} {a : Place}
    (la : IM.LaidAlone ProofFile.sameReply b b' name a) (h0 : ∀ r ∈ b'.claims, Q.Respects r.2) :
    ∀ r ∈ b.claims, Q.Respects r.2 := by
  intro r hr
  rw [IM.claims_alone la] at hr
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hr
  exact Q.respects_guarded ProofFile.sameReply (fun s s' t t' h k => Q.sameReply_alike s s' t t' h k) c.2
    (h0 c hc)

/-- A link's list of runs at a hearing sub-protocol. -/
theorem respects_states (lk : Link S Claim) (b : ℕ) (B : Block S Claim) (hB : lk.hear[b]? = some B)
    (h : ∀ r ∈ B.claims, Q.Respects r.2) (name : String) :
    ∀ r, (statesOfLink lk b).find? (fun r => r.1 == name) = some r → Q.Respects r.2 := by
  intro r hr
  have hm : r ∈ statesOfLink lk b := List.mem_of_find?_eq_some hr
  unfold statesOfLink at hm
  rw [hB] at hm
  exact h r hm

/-! ## 3 The lots' runs are the kinds' own -/

section
variable {C : Type}

/-- The lookup's sub-protocol at an address of a piece ≤ 3 is the one on the calls. -/
theorem theOwn_calls_of (Pr : RunK S C → Prop) (claim : Aff → C)
    (hC : ∀ piece laid sent p,
      ∀ c ∈ (Desc.K3.block (K3.seatCalls claim) piece laid sent p []).claims, Pr c)
    (X : Model.Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place)
    (ha : a.piece ≤ 3) (x : Block S C) (h : Desc.K3.theOwn claim true X codes shape a = some x) :
    ∀ c ∈ x.claims, Pr c := by
  unfold Desc.K3.theOwn at h
  split at h
  · exact nomatch h
  · obtain ⟨i, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · exact nomatch h
    · rename_i hpc
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨p, _, h⟩ := h
      repeat (rw [Option.bind_eq_some_iff] at h; obtain ⟨_, _, h⟩ := h)
      rw [Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h
      intro c hc
      cases digits
      · exact hC a.piece #[] [] p c hc
      · exfalso
        have e : a.piece = K3.pieceAt X i true := by simpa using hpc
        have e2 : 7 ≤ K3.pieceAt X i true := by
          unfold K3.pieceAt
          split <;> simp
        omega

theorem theWhole_calls_of (Pr : RunK S C → Prop) (claim : Aff → C)
    (hC : ∀ piece laid sent p,
      ∀ c ∈ (Desc.K3.block (K3.seatCalls claim) piece laid sent p []).claims, Pr c)
    (X : Model.Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place)
    (ha : a.piece ≤ 3) (x : Block S C) (h : Desc.K3.theWhole claim true X codes shape a = some x) :
    ∀ c ∈ x.claims, Pr c := by
  unfold Desc.K3.theWhole at h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  have h0 := theOwn_calls_of Pr claim hC X codes shape a ha b hb
  split
  · exact andThen_quiet_runs_of Pr b _ _ _ _ _ _ h0
  · exact h0

end

/-- **The lookup's lot's sub-protocol on the calls, away from the output head.** -/
theorem k3At_calls_respects (W : Verify.Public) (Z : ProofFile.Pub) (l : ℕ) (a : Place)
    (ha : a.piece ≤ 3) (hl : a.link = some l) (hnh : K3.isHead W l = false) (b' : Block S Cl)
    (h : IM.k3At W Z a = some b') : ∀ r ∈ b'.claims, Q.Respects r.2 := by
  have h' : K3.theStated K3Lot.ofForm (K3Lot.readersAt W) W Z.first.codes Z.first.shape a =
      some b' := h
  unfold K3.theStated at h'
  obtain ⟨b₀, h₀, h'⟩ := Option.bind_eq_some_iff.1 h'
  have e0 : ∀ r ∈ b₀.claims, Q.Respects r.2 :=
    theWhole_calls_of (fun c => Q.Respects c.2) K3Lot.ofForm
      (fun piece laid sent p c hc => Q.block_respects false piece laid sent p c hc rfl) W _ _ a ha
      b₀ h₀
  simp only [hl] at h'
  by_cases hp : (a.piece != K3.pieceAt W l false) = true
  · rw [if_pos hp] at h'
    obtain rfl : b₀ = b' := Option.some.inj h'
    exact e0
  · rw [if_neg hp] at h'
    cases hr : K3Lot.readersAt W l with
    | none =>
      simp only [hr] at h'
      obtain rfl : b₀ = b' := Option.some.inj h'
      exact e0
    | some r =>
      simp only [hr] at h'
      obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h'
      simp only [K3Lot.readersAt, hnh, Bool.false_eq_true, if_false] at hr
      have key : ∃ A, First.Att.P.readersOfO A = r := by
        split at hr
        all_goals
          split at hr
          · cases hr
          · obtain ⟨A, _, e⟩ := Option.map_eq_some_iff.1 hr
            exact ⟨A, e⟩
      obtain ⟨A, rfl⟩ := key
      exact Q.withCaller_respects A _ b₀ p e0 rfl

/-- **K5's lot's sub-protocol.** -/
theorem k5_claims_respects {W : Verify.Public} {l g : ℕ} {before : List (ℕ × ℕ)}
    {b' : Block S Cl} (h : First.Att.P.k5AtN W l g before = some b') (Z : ProofFile.Pub)
    (nm : String) : ∀ r ∈ (IM.k5Dress Z nm b').claims, Q.Respects r.2 := by
  unfold First.Att.P.k5AtN at h
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  intro r hr
  exact Q.runsO_respects p r hr

/-! ## 4 What the opened chain's links state -/

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
  (hR : VerifierAndGoals.readFiles P = .ok pp)
  (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
include hS hR O

/-- **Block 1 of every link l < 24.** -/
theorem states_look (hW : headLink Bs.G₀.W = 24) (l : ℕ) (hl : l < 24) (lk : Link S Cl)
    (eL : c.links[l]? = some lk) (name : String) :
    ∀ r, (statesOfLink lk 1).find? (fun r => r.1 == name) = some r → Q.Respects r.2 := by
  obtain ⟨Lk, b, b', e1, e2, k3, la⟩ := IM.k3_of hS hR O l (by omega) false
  obtain rfl : lk = Lk := Option.some.inj (eL.symm.trans e1)
  have ix : IM.k3Ix l false = 1 := by
    show (if false = true then 6 else 1) + (if l = 24 then 1 else 0) = 1
    rw [if_neg (by omega : ¬ l = 24)]
    rfl
  have hnh : K3.isHead Bs.G₀.W l = false := by
    show (l == (if Bs.G₀.W.p4 then 2 else 1) * Bs.G₀.W.NGr) = false
    rw [show (if Bs.G₀.W.p4 then 2 else 1) * Bs.G₀.W.NGr = 24 from hW]
    exact beq_false_of_ne (by omega)
  have hpc : (IM.k3Place l false).piece ≤ 3 := by
    show IM.k3Ix l false + 1 ≤ 3
    rw [ix]
    omega
  rw [ix] at e2
  exact respects_states lk 1 b e2
    (respects_laid la (k3At_calls_respects Bs.G₀.W Z l _ hpc rfl hnh b' k3)) name

/-- **Block 2 of every attention link.** -/
theorem states_k5 (g : ℕ) (hg : g < 12) (lk : Link S Cl) (eL : c.links[2 * g + 1]? = some lk)
    (name : String) :
    ∀ r, (statesOfLink lk 2).find? (fun r => r.1 == name) = some r → Q.Respects r.2 := by
  obtain ⟨Lk, b, b', a, e1, e2, k5, la, -⟩ := IM.k5_of hS hR O g hg
  obtain rfl : lk = Lk := Option.some.inj (eL.symm.trans e1)
  exact respects_states lk 2 b e2 (respects_laid la (k5_claims_respects k5 Z _)) name

/-- Block 2 of every link of the sort "layers", from K4's files' law. -/
theorem states_k4
    (hK4 : ∀ x ∈ ProofFile.k4From Z Bs.G₀ Bs.G₀.built.toList 0 none,
      ∀ r ∈ (ProofFile.k4Block x).claims, Q.Respects r.2)
    (g : ℕ) (hg : g < 12) (lk : Link S Cl) (eL : c.links[2 * g]? = some lk) (name : String) :
    ∀ r, (statesOfLink lk 2).find? (fun r => r.1 == name) = some r → Q.Respects r.2 := by
  obtain ⟨Lk, b, x, e1, e2, hx, la, -⟩ := IM.k4_of hS hR O g hg
  obtain rfl : lk = Lk := Option.some.inj (eL.symm.trans e1)
  exact respects_states lk 2 b e2 (respects_laid la (hK4 x hx)) name

end

/-! ## 5 Fwd at every run of a link l < 24 -/

/-- The runs of a link l < 24 stand in blocks 1 and 2; none is the approximate range proof's. -/
def runsBelowB (n : ℕ) : Bool :=
  (List.range n).all fun l => (runsL l false).all fun p =>
    (p.1 == 1 || p.1 == 2) && !(p.2 == "K8.equations")

theorem runsBelow : runsBelowB 24 = true := by decide +kernel

/-- The test can fail: the output head's runs stand in blocks 2 and 3. -/
theorem runsBelow_fails : runsBelowB 25 = false := by decide +kernel

theorem fwd_below {Pp : Type} (XV : OnBytes.Model.Verify.Public) (hX : headLink XV = 24)
    (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (l : ℕ) (hl : l < 24) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ)) (lk : Link S Claim)
    (h1 : ∀ name r, (statesOfLink lk 1).find? (fun r => r.1 == name) = some r → Q.Respects r.2)
    (h2 : ∀ name r, (statesOfLink lk 2).find? (fun r => r.1 == name) = some r → Q.Respects r.2)
    (x x' : Pp × S) (hy : YesOf (blkL Z G₀ l d X arrs) x x') :
    ∀ p ∈ runsL l false,
      Fwd (readersOfLink (holesAt XV (headLink XV) l lk) lk) p.1 p.2 x.2 x'.2 := by
  intro p hp
  have ht := List.all_eq_true.1 (List.all_eq_true.1 runsBelow l (List.mem_range.2 hl)) p hp
  obtain ⟨hb, hn⟩ := Eq.mp (Bool.and_eq_true _ _) ht
  have hn' : (p.2 == "K8.equations") = false := by simpa using hn
  refine fwd_later Z G₀ l d X arrs _ lk p
    (Q.pairStays_of_respects XV (headLink XV) l (by omega) lk p hn' ?_) x x' hy
  rcases Eq.mp (Bool.or_eq_true _ _) hb with e | e
  · rw [eq_of_beq e]
    exact h1 p.2
  · rw [eq_of_beq e]
    exact h2 p.2

/-! ## 6 hRd -/

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **hRd, to the letter**: paid at the attention segments and at the lookup's runs. -/
theorem hRd_seated (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hX : headLink XV = 24)
    (hW : headLink Bs.G₀.W = 24)
    (hK4 : ∀ x ∈ ProofFile.k4From Z Bs.G₀ Bs.G₀.built.toList 0 none,
      ∀ r ∈ (ProofFile.k4Block x).claims, Q.Respects r.2)
    (hHead : ∀ d : Bool, ∀ X arrs, Bs.G₀.built[24]? = some X → ∀ lk, c.links[24]? = some lk →
      ∀ x x' y, YesOf (blkL Z Bs.G₀ 24 d X arrs) x x' →
      InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) linksFull (flatPlacesOf linksFull true)
        (noL 24 d) x y →
      ∀ p ∈ runsL 24 false,
        Fwd (readersOfLink (holesAt XV (headLink XV) 24 lk) lk) p.1 p.2 x.2 x'.2) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y m j r, YesOf (blkL Z Bs.G₀ l d X arrs) x x' → InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) linksFull (flatPlacesOf linksFull true) (noL l d) x y → (Pub.formsIn m j r ∈ (First.pubSets (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)).more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) ∨ Pub.formsInT m j r ∈ (First.pubSets (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)).more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++ First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d))) → ReadersStay (dK Dm.pubD Dm.sent) m j r x.2 x'.2 := by
  refine hRd_atBase Dm dk Z Bs.G₀ hDlk ?_
  intro l hl d X arrs hXb lk elk x x' y hy hIn
  rw [hlk l hl] at elk
  by_cases h24 : l = 24
  · subst h24
    exact hHead d X arrs hXb lk elk x x' y hy hIn
  · have hl' : l < 24 := by omega
    refine fwd_below XV hX Z Bs.G₀ l hl' d X arrs lk
      (fun name => states_look hS hR O hW l hl' lk elk name) ?_ x x' hy
    rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
    · exact fun name => states_k4 hS hR O hK4 g (by omega) lk elk name
    · exact fun name => states_k5 hS hR O g (by omega) lk elk name

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.laterAlike_blkL
#print axioms VerifiableInference.Desc.K1.fwd_later
#print axioms VerifiableInference.Desc.K1.Q.pairStays_of_respects
#print axioms VerifiableInference.Desc.K1.respects_laid
#print axioms VerifiableInference.Desc.K1.respects_states
#print axioms VerifiableInference.Desc.K1.theOwn_calls_of
#print axioms VerifiableInference.Desc.K1.theWhole_calls_of
#print axioms VerifiableInference.Desc.K1.k3At_calls_respects
#print axioms VerifiableInference.Desc.K1.k5_claims_respects
#print axioms VerifiableInference.Desc.K1.states_look
#print axioms VerifiableInference.Desc.K1.states_k5
#print axioms VerifiableInference.Desc.K1.states_k4
#print axioms VerifiableInference.Desc.K1.runsBelow
#print axioms VerifiableInference.Desc.K1.runsBelow_fails
#print axioms VerifiableInference.Desc.K1.fwd_below
#print axioms VerifiableInference.Desc.K1.hRd_seated
