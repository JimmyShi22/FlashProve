-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ReadersHead.lean: AT THE OUTPUT HEAD's SEGMENT: the second reader (k6Silent,
Johnson/Desc/Kinds/Law/K6SilentCode.lean: the run itself, called at the state with the reads' tables
laid silently) answers alike at two states that part in nothing but what a later commitment or the
reads' quiet step writes (Q.RestAlike, Johnson/Desc/K1/Law/RestQDef.lean); so the lookup's runs
"objects" and "guests" of that segment are paid at both later places of kind K1. Statements with
their proofs.

Main names:
  restOf_tables       laying tables leaves what Q.restOf keeps.
  withTables_alike    **withTables answers at both states or at neither, with alike states.**
  silent_alike        so k6Silent answers alike, at a run that is a member of Q.Respects.
  Q.pairStays_head    Q.PairStays at the output head's segment, from Q.Respects of the stated run.
  k3At_calls_named    the lookup's lot's sub-protocol on the calls, at ANY link: each run but
                      "planes" is a member.
  states_look_head    block 2 of link 24, at a name other than "planes".
  fwd_head_look       **Fwd at (2, objects) and (2, guests), at both later places.**
What is not claimed. Anything on "planes" or on the output head's own four runs: these four read
the tables, so they are no members of Q.Respects. Nothing on soundness, on an honest prover or on
hiding.

-/
import Johnson.Desc.K1.Law.ReadersSeated
import Johnson.Desc.Kinds.Law.K6Silent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription Place)
open VerifiableInference.Desc.First (S Here HeadOwn)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.K9 (Readers RunOf readerOf LinkHoles statesOfLink readersOfLink holesAt
  phAt)
open VerifiableInference.Desc.Kinds.Head.Law (withTables withTables_iff k6Silent)
open VerifiableInference.Reads.Pass (Fwd)
open OnBytes.Model.Stages (LinkH)
open ProofFile (Cl)

/-! ## 1 The second reader -/

theorem restOf_tables (s : S) (a : HeadOwn) (ha : s.here = .head a) (tt : Head.Tables) :
    Q.restOf { s with here := .head { a with t := some tt } } = Q.restOf s := by
  simp [Q.restOf, Q.blank, Q.blankHere, restOf, hereRest, ha]

/-- **withTables at two alike states.** -/
theorem withTables_alike (P : K8.ReadsQuiet.PH) {s s' e : S} (hA : Q.RestAlike s s')
    (he : withTables P s = some e) : ∃ e', withTables P s' = some e' ∧ Q.RestAlike e e' := by
  obtain ⟨a, cov, x, tt, ha, hop, hcov, hx, ht, rfl⟩ := (withTables_iff P s e).1 he
  have hh : (Q.restOf s).here = (Q.restOf s').here := congrArg S.here hA
  have hreq : s'.req = s.req := (congrArg S.req hA).symm
  have hout : s'.out = s.out := hA.out.symm
  cases ha' : s'.here with
  | head a' =>
    have e1 : Q.blankHere (hereRest (.head a)) = Q.blankHere (hereRest (.head a')) := by
      rw [← ha, ← ha']
      exact hh
    have e2 := Here.head.inj e1
    have o1 : a'.opened = a.opened := (congrArg HeadOwn.opened e2).symm
    have o2 : a'.x = a.x := (congrArg HeadOwn.x e2).symm
    refine ⟨{ s' with here := .head { a' with t := some tt } },
      (withTables_iff P s' _).2 ⟨a', cov, x, tt, ha', o1.trans hop, ?_, o2.trans hx, ht, rfl⟩, ?_⟩
    · unfold S.covered S.replyTok? S.coveredAt at hcov ⊢
      rw [hreq, hout]
      exact hcov
    · show Q.restOf _ = Q.restOf _
      rw [restOf_tables s a ha tt, restOf_tables s' a' ha' tt]
      exact hA
  | _ =>
    exfalso
    have e1 : Q.blankHere (hereRest s.here) = Q.blankHere (hereRest s'.here) := hh
    rw [ha, ha'] at e1
    cases e1

/-- The second reader answers alike, at a run that is a member. -/
theorem silent_alike (P : K8.ReadsQuiet.PH) (states : ℕ → List (RunOf S)) (b : ℕ) (name : String)
    (hr : ∀ r, (states b).find? (fun r => r.1 == name) = some r → Q.Respects r.2) {s s' : S}
    (hA : Q.RestAlike s s') : k6Silent P states b name s' = k6Silent P states b name s := by
  show (withTables P s').bind (readerOf states b name) =
    (withTables P s).bind (readerOf states b name)
  cases h : withTables P s with
  | some e =>
    obtain ⟨e', he', k⟩ := withTables_alike P hA h
    rw [he']
    exact Q.readerOf_alike states b name hr k
  | none =>
    cases h' : withTables P s' with
    | none => rfl
    | some e' =>
      obtain ⟨e, he, _⟩ := withTables_alike P hA.symm h'
      rw [h] at he
      cases he

/-- Q.PairStays at the output head's segment. -/
theorem Q.pairStays_head (X : OnBytes.Model.Verify.Public) (mH : ℕ) (lk : Link S Claim)
    (p : ℕ × String) (hn : (p.2 == "K8.equations") = false)
    (hr : ∀ r, (statesOfLink lk p.1).find? (fun r => r.1 == p.2) = some r → Q.Respects r.2) :
    Q.PairStays (holesAt X mH mH lk) lk p := by
  unfold Q.PairStays
  rw [hn]
  refine ⟨hr, fun s s' hA => ?_⟩
  have e : (holesAt X mH mH lk).silent = k6Silent (phAt X mH) (statesOfLink lk) := by
    unfold holesAt
    simp
  rw [e]
  exact silent_alike _ _ _ _ hr hA

/-! ## 2 The lookup's runs at link 24 -/

/-- The lookup's lot's sub-protocol on the calls, at any link: each run but "planes". -/
theorem k3At_calls_named (W : Verify.Public) (Z : ProofFile.Pub) (a : Place) (ha : a.piece ≤ 3)
    (b' : Block S Cl) (h : IM.k3At W Z a = some b') :
    ∀ r ∈ b'.claims, r.1 ≠ "planes" → Q.Respects r.2 := by
  have h' : K3.theStated K3Lot.ofForm (K3Lot.readersAt W) W Z.first.codes Z.first.shape a =
      some b' := h
  unfold K3.theStated at h'
  obtain ⟨b₀, h₀, h'⟩ := Option.bind_eq_some_iff.1 h'
  have e0 : ∀ r ∈ b₀.claims, Q.Respects r.2 :=
    theWhole_calls_of (fun c => Q.Respects c.2) K3Lot.ofForm
      (fun piece laid sent p c hc => Q.block_respects false piece laid sent p c hc rfl) W _ _ a ha
      b₀ h₀
  cases hl : a.link with
  | none =>
    simp only [hl] at h'
    obtain rfl : b₀ = b' := Option.some.inj h'
    exact fun r hr _ => e0 r hr
  | some l =>
    simp only [hl] at h'
    by_cases hp : (a.piece != K3.pieceAt W l false) = true
    · rw [if_pos hp] at h'
      obtain rfl : b₀ = b' := Option.some.inj h'
      exact fun r hr _ => e0 r hr
    · rw [if_neg hp] at h'
      cases hr : K3Lot.readersAt W l with
      | none =>
        simp only [hr] at h'
        obtain rfl : b₀ = b' := Option.some.inj h'
        exact fun r hr _ => e0 r hr
      | some rd =>
        simp only [hr] at h'
        obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h'
        intro r hm hne
        have hm' : r ∈ b₀.claims ++ [("planes", K3.planesRun (K3.seatCalls K3Lot.ofForm) p.lm rd)] :=
          hm
        rcases List.mem_append.1 hm' with h1 | h1
        · exact e0 r h1
        · rw [List.mem_singleton.1 h1] at hne
          exact absurd rfl hne

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
  (hR : VerifierAndGoals.readFiles P = .ok pp)
  (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
include hS hR O

/-- **Block 2 of link 24**, at a name other than "planes". -/
theorem states_look_head (lk : Link S Cl) (eL : c.links[24]? = some lk) (name : String)
    (hne : name ≠ "planes") :
    ∀ r, (statesOfLink lk 2).find? (fun r => r.1 == name) = some r → Q.Respects r.2 := by
  obtain ⟨Lk, b, b', e1, e2, k3, la⟩ := IM.k3_of hS hR O 24 (by omega) false
  obtain rfl : lk = Lk := Option.some.inj (eL.symm.trans e1)
  have e2' : lk.hear[2]? = some b := e2
  intro r hr
  have hb := List.find?_some (p := fun r : RunOf S => r.1 == name) hr
  have hnm : r.1 = name := eq_of_beq hb
  have hm : r ∈ statesOfLink lk 2 := List.mem_of_find?_eq_some hr
  unfold statesOfLink at hm
  rw [e2'] at hm
  have hm' : r ∈ b.claims := hm
  rw [IM.claims_alone la] at hm'
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hm'
  exact Q.respects_guarded ProofFile.sameReply (fun s s' t t' h k => Q.sameReply_alike s s' t t' h k) q.2
    (k3At_calls_named Bs.G₀.W Z _ (by decide) b' k3 q hq (by rw [show q.1 = name from hnm]; exact hne))

/-- **Fwd at the output head's (2, objects) and (2, guests), at both later places.** -/
theorem fwd_head_look {Pp : Type} (XV : OnBytes.Model.Verify.Public) (hX : headLink XV = 24)
    (d : Bool) (X : LinkH) (arrs : Option (List ℕ)) (lk : Link S Cl)
    (eL : c.links[24]? = some lk) (x x' : Pp × S) (hy : YesOf (blkL Z Bs.G₀ 24 d X arrs) x x')
    (name : String) (hnm : name = "objects" ∨ name = "guests") :
    Fwd (readersOfLink (holesAt XV (headLink XV) 24 lk) lk) 2 name x.2 x'.2 := by
  have hne : name ≠ "planes" := by rcases hnm with rfl | rfl <;> decide
  have hn8 : (name == "K8.equations") = false := by rcases hnm with rfl | rfl <;> decide
  rw [hX]
  exact fwd_later Z Bs.G₀ 24 d X arrs _ lk (2, name)
    (Q.pairStays_head XV 24 lk (2, name) hn8 (states_look_head hS hR O lk eL name hne)) x x' hy

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.restOf_tables
#print axioms VerifiableInference.Desc.K1.withTables_alike
#print axioms VerifiableInference.Desc.K1.silent_alike
#print axioms VerifiableInference.Desc.K1.Q.pairStays_head
#print axioms VerifiableInference.Desc.K1.k3At_calls_named
#print axioms VerifiableInference.Desc.K1.states_look_head
#print axioms VerifiableInference.Desc.K1.fwd_head_look
