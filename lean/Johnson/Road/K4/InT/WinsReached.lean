-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/InT/WinsReached.lean: AT EVERY STATE THAT THE FIRST CHAIN's RUN REACHES IN FRONT OF
THE LOOKUP ON THE DIGITS OF A LAYERS' SEGMENT (28 g + 8): the state stands in a layers' segment;
what K4's hearing returned is there; the open ledger has arrays of the right sizes; and TWO OF THE
THREE WINDOWS of K4's runs of claims (the row products' token sumcheck's and the merge's) END AT OR
BELOW THE LEDGER's NEXT. For the premise `K4StaysBelow` (Johnson/Road/K4/InT/RunsSameK4.lean).
Statements with their proofs: calls.

  `kept_reached`: whoever is reached at 28 g + 5 came by an accept of K4's sub-protocol from a state
    reached at 28 g + 4 whose ledger has arrays of the right sizes: `KeptAtS` (the road from
    "reached" to KeptAtS, once for all).
  `lay_of_own`: a state that bears what K4's hearing returned stands in a layers' segment.
  **`wins_reached`**: hS · hR · an opening · F.planOk = true · g < 12 · Reach 0 c.blocksInOrder start (28 * g
  + 8) (z, s) ⟹ ∃ a o, s.here = .lay a ∧ a.own = some o ∧ Sized a.F ∧ the two windows end at or
  below a.F.next ∧ s.lookHeard? = some o.H.fo (so a law in other files on the third window, which
  speaks of what lookHeard? finds, speaks of o.H.fo.leaves).
  `OwnHeard` | `ownHeard_back`: the walk of ownLater_back at a relation that also holds
    "what the lookup on the calls was heard to return stays". `both_reached`: in front of K4's
    sub-protocol a.fo = a.lookHeard (by `theStated_calls_yes` | `k3_lays_both`,
    Johnson/Meaning/HeardCalls.lean).

Called: `hear_wins` (Johnson/Road/K4/Slots/RunsSpare.lean) ·
`ownLater_back` (Johnson/Desc/First/Link/Law/StretchParts.lean) · `sized_upTo`
(Johnson/Desc/First/Look/K03RowsBare.lean).
Limits. THE THIRD WINDOW (the leaves' of the lookup on the calls) IS THE LOOKUPS' FILES' TO PLACE.
That there is an opening is shown by no theorem here. K04_law, the law of K4's sub-protocol itself,
IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.FunsThirdReached
import Johnson.Road.K4.Slots.RunsSpare
import Johnson.Desc.First.Look.K03RowsBare
import Johnson.Desc.First.Link.Law.StretchParts
import Johnson.Meaning.HeardCalls
import Johnson.P4R.FreeAt341N

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.InT
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Slots (hear_wins)
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc
open VerifiableInference
open VerifiableInference.Desc.Keeps (Decides)
open Johnson.Desc.First.Walk.Tied (Reach stepYes_decide)

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  {g : ℕ} {Q : Type} {start : Q → S}

/-- **From "reached behind K4" to what an accept of K4's sub-protocol leaves.** -/
theorem kept_reached (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (hg : g < 12) {z : Q} {s' : S} (h : Reach 0 c.blocksInOrder start (28 * g + 5) (z, s')) :
    ∃ (p : Par) (s : S), Reach 0 c.blocksInOrder start (28 * g + 4) (z, s) ∧ KeptAtS p s s' ∧
      ∀ F₀, s.fork? = some F₀ → PscRun.Sized F₀ := by
  obtain ⟨z', s, s'', b, e, hr, hb, hy⟩ := reach_pred (k := 28 * g + 4) h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  obtain ⟨Lk, b₀, x, e1, e2, _, e4, _⟩ := IM.k4_of hS hR O g hg
  have hi : IM.flatIx c (2 * g) 2 = 28 * g + 4 := by
    rw [IM.flatIx_scope hS hR O (by omega) 2]
    omega
  have hf : c.blocksInOrder[28 * g + 4]? = some b₀ := by
    rw [← hi]
    exact IM.hear_at_flat e1 e2
  obtain rfl : b₀ = b := Option.some.inj (hf.symm.trans hb)
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  obtain ⟨_, R, C, hfold⟩ := hr.fold
  have hk : 28 * g + 4 = 14 * (2 * g) + 1 + 2 + 1 := by omega
  rw [hk] at hfold
  obtain ⟨F₀, hF₀, hZ₀⟩ := VerifiableInference.OnPublicFiles.sized_upTo hS hR O hOk (2 * g) (by omega) 1
    (by omega) hfold
  refine ⟨{ x.2 with k3Runs := true }, s, hr, kept_atS ((IM.k4_yes e4 s s' rs gs).1 hd).1,
    fun F' hF' => ?_⟩
  obtain rfl : F₀ = F' := Option.some.inj (hF₀.symm.trans hF')
  exact hZ₀

theorem lay_of_own {s : S} {o : Own} (h : s.own? = some o) :
    ∃ a : LayOwn, s.here = .lay a ∧ a.own = some o := by
  unfold S.own? at h
  cases hh : s.here with
  | lay a =>
    rw [hh] at h
    exact ⟨a, rfl, h⟩
  | between => rw [hh] at h; exact nomatch h
  | att a => rw [hh] at h; exact nomatch h
  | head a => rw [hh] at h; exact nomatch h
  | fin a => rw [hh] at h; exact nomatch h
  | mem a => rw [hh] at h; exact nomatch h

/-! ## One relation for "own? stays, the ledger is later" and "what was heard of the calls stays" -/

/-- Both at once, so that one walk back carries both. -/
def OwnHeard (s s' : S) : Prop := OwnLater s s' ∧ s'.lookHeard? = s.lookHeard?

theorem ownHeard_trans (a b c : S) (h : OwnHeard a b) (k : OwnHeard b c) : OwnHeard a c :=
  ⟨ownLater_trans a b c h.1 k.1, k.2.trans h.2⟩

theorem putLink_heard (s : S) (L : LinkCtx) : (s.putLink L).lookHeard? = s.lookHeard? := by
  unfold S.putLink
  split <;> (try split) <;> simp_all [S.lookHeard?]

theorem putFork_heard (s : S) (G : Fork) : (s.putFork G).lookHeard? = s.lookHeard? := by
  unfold S.putFork
  split <;> (try split) <;> simp_all [S.lookHeard?]

theorem putTl_heard (s : S) (tl : HTailF2) : (s.putTl tl).lookHeard? = s.lookHeard? := by
  unfold S.putTl
  split <;> (try split) <;> simp_all [S.lookHeard?]

theorem k1_ownHeard (q : Params.First) (gp : _root_.Desc.Plain.GPar) (link piece moment : ℕ)
    (arrays : Option (List ℕ)) :
    Decides OwnHeard (K1.laterAt (Cl := Unit) q gp link piece moment arrays) := by
  intro s rs gs s' h
  refine ⟨k1_ownLater q gp link piece moment arrays s rs gs s' h, ?_⟩
  have h' := h
  unfold K1.laterAt K1.commitAtS at h'
  dsimp only at h'
  split at h'
  · obtain ⟨y, _, rfl⟩ := VerifiableInference.Desc.mapOk h'
    exact ((putFork_heard _ _).trans (putLink_heard _ _)).trans rfl
  · cases h'

theorem k8_ownHeard (p : First.K8.ParW) : Decides OwnHeard (First.K8.whole p) := by
  intro s rs gs s' h
  exact ⟨k8_ownLater p s rs gs s' h,
    First.K8.hear_leaves (Cl := Claim) S.lookHeard? putTl_heard p.toPar s rs gs s' h⟩

theorem quietLayers_ownHeard (P : K8.ReadsQuiet.PG) :
    Decides OwnHeard (K8.ReadsQuiet.layers P) := by
  intro s rs gs s' h
  refine ⟨quietLayers_ownLater P s rs gs s' h, ?_⟩
  have h' : (match s.here with
      | .lay a => do
        let own ←
          (a.own.elim (.error "reads: the own rounds' record is not laid") .ok : Except String _)
        let tl ← K8.ReadsQuiet.closed P.tl own.funs a.L s.st
        pure { s with here := .lay { a with tl := tl } }
      | _ => .error "reads: no layers' link is open" : Except String S) = .ok s' := h
  split at h'
  · rename_i a ha
    obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
    obtain rfl := Except.ok.inj h'
    simp [S.lookHeard?, ha]
  · exact nomatch h'

/-- **From the front of the lookup on the digits back to the border behind K4's sub-protocol, with
both.** (ownLater_back, its walk at the wider relation.) -/
theorem ownHeard_back (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hg : g < 12) {z : Q}
    {s' : S} (h : Reach 0 c.blocksInOrder start (28 * g + 8) (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start (28 * g + 5) (z, s) ∧ OwnHeard s s' := by
  have n24 : 2 * g ≠ 24 := by omega
  have i1 : IM.k1Ix (2 * g) true = 5 := by
    show (if true = true then 5 else 3) + (if 2 * g = 24 then 1 else 0) = 5
    simp [n24]
  have i8 : k8Ix (2 * g) = 4 := by
    show 4 + (if 2 * g = 24 then 1 else 0) = 4
    simp [n24]
  have e8 : 28 * g + 8 = 14 * (2 * g) + 5 + 2 + 1 := by omega
  rw [e8] at h
  obtain ⟨s₂, r2, q2⟩ := back_k1_of k1_ownHeard hS hR O (l := 2 * g) (by omega) (z := z) (s' := s')
    (by rw [i1]; exact h)
  rw [i1] at r2
  obtain ⟨s₁, r1, q1⟩ := back_k8_of k8_ownHeard hS hR O (l := 2 * g) (by omega) (z := z)
    (s' := s₂) (by rw [i8]; exact r2)
  rw [i8] at r1
  have e6 : 14 * (2 * g) + 4 + 2 = 28 * g + 6 := by omega
  rw [e6] at r1
  obtain ⟨s₀, r0, q0⟩ := back_readsL_of ownHeard_trans k1_ownHeard quietLayers_ownHeard hS hR O hg
    r1
  exact ⟨s₀, r0, ownHeard_trans _ _ _ q0 (ownHeard_trans _ _ _ q1 q2)⟩

/-- An address of the kind K3 whose piece is 2 is the lookup on the calls' at a segment that is not the
head's. (stated_via3, Johnson/Desc/Kinds/Law/CallsLedgerKept.lean, has the like at 3.) -/
theorem piece_two {Cl : Type} {X : Verify.Public} (claim : Aff → Cl)
    (readers : ℕ → Option (K3.Readers S)) (codes : Codes) (shape : Params.ReqShape) (a : Place)
    (B₀ : Block S Cl) (h : K3.theStated claim readers X codes shape a = some B₀) {i : ℕ}
    (hl : a.link = some i) (h2 : a.piece = 2) : a.piece = K3.pieceAt X i false := by
  obtain ⟨B₁, hB₁, -⟩ := K3.theStated_is claim readers X codes shape a B₀ h
  obtain ⟨b, hb, -⟩ := K3.theWhole_is claim true X codes shape a B₁ hB₁
  obtain ⟨j, digits, _, _, _, hj, hpj, -⟩ := K3.theOwn_is claim true X codes shape a b hb
  obtain rfl : i = j := Option.some.inj (hl.symm.trans hj)
  rw [h2] at hpj ⊢
  unfold K3.pieceAt at hpj ⊢
  cases hH : K3.isHead X i <;> cases digits <;> simp [hH] at hpj ⊢

/-- **Whoever is reached in front of K4's sub-protocol, in a layers' segment a: a.fo = a.lookHeard**:
the lookup on the calls has laid both at once. -/
theorem both_reached (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (hg : g < 12) {z : Q} {s : S} (h : Reach 0 c.blocksInOrder start (28 * g + 4) (z, s)) {a : LayOwn}
    (ha : s.here = .lay a) : a.fo = a.lookHeard := by
  obtain ⟨z', s₃, s'', b, e, _, hb, hy⟩ := reach_pred (k := 28 * g + 3) h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  obtain ⟨Lk, c3, c3', n1, n2, hk3, hla3⟩ := IM.k3_of hS hR O (2 * g) (by omega) false
  have n24 : 2 * g ≠ 24 := by omega
  have ix : IM.k3Ix (2 * g) false = 1 := by
    show (if false = true then 6 else 1) + (if 2 * g = 24 then 1 else 0) = 1
    simp [n24]
  have hf : c.blocksInOrder[28 * g + 3]? = some c3 := by
    have hi : IM.flatIx c (2 * g) (IM.k3Ix (2 * g) false) = 28 * g + 3 := by
      rw [IM.flatIx_scope hS hR O (by omega) _, ix]
      omega
    rw [← hi]
    exact IM.hear_at_flat n1 n2
  obtain rfl : c3 = b := Option.some.inj (hf.symm.trans hb)
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  have a3 := ((IM.k3_yes hla3 s₃ s rs gs).1 hd).1
  have hp : c3'.planOk = true := by
    rw [← IM.alone_planOk hla3]
    exact P4.plan_at O hOk _ _ hf
  have hk3' : K3.theStated K3Lot.ofForm (K3Lot.readersAt Bs.G₀.W) Bs.G₀.W Z.first.codes
      Z.first.shape (IM.k3Place (2 * g) false) = some c3' := hk3
  have h2 : (IM.k3Place (2 * g) false).piece = 2 := by
    show IM.k3Ix (2 * g) false + 1 = 2
    rw [ix]
  have hpc := piece_two _ _ _ _ _ _ hk3' (i := 2 * g) rfl h2
  have ePl : IM.k3Place (2 * g) false =
      ⟨1, some (2 * g), K3.pieceAt Bs.G₀.W (2 * g) false, .K3⟩ := by
    rw [← hpc]
  rw [ePl] at hk3'
  obtain ⟨p, laid, sent, rs', gs', _, hk⟩ :=
    Meaning.Planes.theStated_calls_yes K3Lot.ofForm (K3Lot.readersAt Bs.G₀.W) Bs.G₀.W
      Z.first.codes Z.first.shape (2 * g) hk3' hp a3
  exact Meaning.Planes.k3_lays_both _ _ _ _ _ _ hk ha

/-- **In front of the lookup on the digits: two of K4's three windows lie below the ledger's next; and
what the lookup on the calls was heard to return is what K4's hearing bears.** -/
theorem wins_reached (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (hg : g < 12) {z : Q} {s : S} (h : Reach 0 c.blocksInOrder start (28 * g + 8) (z, s)) :
    ∃ (a : LayOwn) (o : Own), s.here = .lay a ∧ a.own = some o ∧ PscRun.Sized a.F ∧
      o.H.tV.p.first + o.H.tV.p.walk.1.length ≤ a.F.next ∧
      o.wo.toWsMerged.p.first + o.wo.toWsMerged.p.walk.1.length ≤ a.F.next ∧
      s.lookHeard? = some o.H.fo := by
  obtain ⟨s₅, r5, K, kh⟩ := ownHeard_back hS hR O hg h
  obtain ⟨p, s₄, r4, K4, hZ⟩ := kept_reached hS hR O hOk hg r5
  obtain ⟨a₄, fo, o, G, ha₄, hfo, hG, L4, ho, _, _, _, Rs, efo, _, t, u, hh⟩ := K4
  have hb4 : a₄.fo = a₄.lookHeard := both_reached hS hR O hOk hg r4 ha₄
  have h4 : s₄.lookHeard? = some fo := by
    have : s₄.lookHeard? = a₄.lookHeard := by simp [S.lookHeard?, ha₄]
    rw [this, ← hb4]
    exact hfo
  have hF₄ : PscRun.Sized a₄.F := hZ _ (by simp [S.fork?, ha₄])
  obtain ⟨⟨_, w1⟩, ⟨_, w2⟩⟩ := hear_wins hF₄ hh
  obtain ⟨a, ha, hoa⟩ := lay_of_own (K.1.trans ho)
  obtain ⟨F₈, hF₈, L8⟩ := K.2 G hG
  have e8 : F₈ = a.F := by
    have : s.fork? = some a.F := by simp [S.fork?, ha]
    exact Option.some.inj (hF₈.symm.trans this)
  subst e8
  have n8 := L8.next
  exact ⟨a, o, ha, hoa, L8.sized (L4.sized hF₄), by omega, by omega,
    by rw [kh, Rs.lookHeard, h4, efo]⟩

end OnBytes.Road.K4.InT

#print axioms OnBytes.Road.K4.InT.kept_reached
#print axioms OnBytes.Road.K4.InT.lay_of_own
#print axioms OnBytes.Road.K4.InT.ownHeard_back
#print axioms OnBytes.Road.K4.InT.piece_two
#print axioms OnBytes.Road.K4.InT.both_reached
#print axioms OnBytes.Road.K4.InT.wins_reached
