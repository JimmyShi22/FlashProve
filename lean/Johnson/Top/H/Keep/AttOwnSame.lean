-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/AttOwnSame.lean: AT AN ATTENTION LINK THE CALLING KIND's OWN THREE RUNS OF
CLAIMS ("first", "keys", "second": what the table's name "own" stands for there) ANSWER BEHIND A
LOOKUP ON THE DIGITS WHAT THEY ANSWERED IN FRONT: RunSame (Johnson/Top/H/Keep/FormsPassK3.lean) at
each; so the kept public test formsIn at these three runs passes. Statements and proofs: joinings
over the laws of K5's files.

OBJECT: Att.P.runsN A (Johnson/Desc/First/Att/SeatN.lean): K5's named runs, typed at Claim;
  K9.readersOfLink.
USER: Johnson/P5J/K03OwnFwdAttAt.lean (runsN_same); Johnson/P5J/K03OwnItAttAt.lean (own_low);
  Johnson/Top/H/Keep/HeadOwnAtSeat.lean (own_low); and others.
  Meant: the kept item "own" across the lookup on the digits, at the twelve
  attention links.
LETTERS: A; s, s', a, a'; F, G; H, l, b, own.
Compiled with the whole library.

Why it is short. The three runs leave the state as it is and lay nothing late
(Johnson/Desc/First/Att/RunsK.lean: firstK, keysK, secondK return s itself).
firstK_mono, secondK_mono, keysOfK_mono (Johnson/Desc/First/Att/Claims/LeftLater.lean) say that
what they return at s they return at s', with s' in the place of s, where what K5 heard, the
lookup's heard value, what the ledger shows and the arrays' widths stay.

Main names:
  runN_named_same: THE RULE: a run of forms that leaves the state and goes forward is RunSame,
    typed at Claim.
  k5first_same, k5keys_same, k5second_same: at the three runs, to the letter of runsN A's entries.
  runsN_is: runsN A's four entries. runsN_same: ∀ x ∈ runsN A, x.1 ≠ "join" → RunSame x.2 s s'.
  own_low: these runs lay nothing late. own_formsIn_pass: THE END, under hr and hfind.
  k3_digits_runsN_same: at the digits' decision's accept.

Limits. hfind (the link states runsN A's run at that name) and hr (the run itself answers in front;
at an attention link the second hole is empty, so hr follows from the kept test) are premises.
"join" is not here. Over the decision's own accept: the seated sub-protocol is K3's block and then
a step without a round.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.AttCallersStay
import Johnson.Top.H.Keep.FormsPassRun
import Johnson.Desc.First.Att.SeatN

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.PscRun
open VerifiableInference.Desc (Claim Link)
open VerifiableInference.Desc.First (S AttOwn)
open VerifiableInference.Desc.First.Att.P (seatCO seatCH seatCO_eq parCOf runN runN_ok runsN claimOf
  firstK keysK secondK keysOfK keysOfO)
open VerifiableInference.Desc.K3 (seatDigits)
open VerifiableInference.Desc.K9 (Read readerOf readersOfLink statesOfLink LinkHoles formsIn lateOf)
open K5Law (ShownLe firstK_mono secondK_mono keysOfK_mono widths)
open VerifiableInference.Reads.Pass (Fwd)

/-- **THE RULE.** -/
theorem runN_named_same {nm : String} {f : S → Option (List Aff × S)} {s s' : S} {F G : Fork}
    (hF : s.fork? = some F) (hG : s'.fork? = some G) (htr : G.trees = F.trees)
    (hst : ∀ y, f s = some y → y.2 = s) (hm : ∀ y, f s = some y → f s' = some (y.1, s')) :
    RunSame (runN fun _ s => Desc.named nm (f s)) s s' := by
  intro cl t F1 G1 hr hF1 hG1
  obtain ⟨l, hl, hcl⟩ := runN_ok hr
  have hl' : Desc.named nm (f s) = .ok (l, t) := hl
  have hcl' : cl = l.map claimOf := hcl
  cases e : f s with
  | none =>
    rw [e] at hl'
    exact nomatch hl'
  | some y =>
    rw [e] at hl'
    obtain rfl : y = (l, t) := Except.ok.inj hl'
    obtain rfl : t = s := hst _ e
    obtain rfl : F = F1 := Option.some.inj (hF.symm.trans hF1)
    obtain rfl : F = G1 := Option.some.inj (hF.symm.trans hG1)
    refine ⟨s', G, G, ?_, hG, hG, ?_, htr⟩
    · show ((Desc.named nm (f s')).map fun y => (y.1.map claimOf, y.2)) = .ok (cl, s')
      rw [hm _ e, hcl']
      rfl
    · rw [lateOf_same G G rfl, lateOf_same F F rfl]

section
variable (A : Attention.Plan) {s s' : S} {a a' : AttOwn} (hs : s.here = .att a)
  (hs' : s'.here = .att a') (hg : a'.g = a.g) (h5 : a'.heard5 = a.heard5)
  (H : ShownLe a.F a'.F) (hw : widths a'.F = widths a.F) {F G : Fork} (hF : s.fork? = some F)
  (hG : s'.fork? = some G) (htr : G.trees = F.trees)
include hs hs' hg h5 H hw hF hG htr

theorem k5first_same :
    RunSame (runN fun _ s => Desc.named "K5.first" (firstK (seatCO (parCOf A)) (parCOf A) s)) s
      s' := by
  refine runN_named_same hF hG htr (fun y e => ?_) fun y e => ?_
  · unfold firstK at e
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at e
    obtain ⟨x, _, f, _, r⟩ := e
    rw [← Option.some.inj r]
  · rw [seatCO_eq] at e ⊢
    exact firstK_mono (parCOf A) hs hs' hg h5 H hw e

theorem k5second_same :
    RunSame (runN fun _ s => Desc.named "K5.second" (secondK (seatCO (parCOf A)) (parCOf A) s)) s
      s' := by
  refine runN_named_same hF hG htr (fun y e => ?_) fun y e => ?_
  · unfold secondK at e
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at e
    obtain ⟨x, _, f, _, r⟩ := e
    rw [← Option.some.inj r]
  · rw [seatCO_eq] at e ⊢
    exact secondK_mono (parCOf A) hs hs' hg h5 H hw e

theorem k5keys_same :
    RunSame (runN fun _ s => Desc.named "K5.keys" (keysK (seatCO (parCOf A)) (parCOf A) s)) s
      s' := by
  refine runN_named_same hF hG htr (fun y e => ?_) fun y e => ?_
  · unfold keysK at e
    obtain ⟨kf, _, r⟩ := Option.map_eq_some_iff.1 e
    rw [← r]
  · unfold keysK at e ⊢
    obtain ⟨kf, hk, r⟩ := Option.map_eq_some_iff.1 e
    rw [seatCO_eq] at hk ⊢
    rw [keysOfK_mono (parCOf A) hs hs' hg h5 H hw hk, ← r]
    rfl

omit hs hs' hg h5 H hw hF hG htr in
/-- The four entries. -/
theorem runsN_is : runsN A =
    [("first", runN fun _ s => Desc.named "K5.first" (firstK (seatCO (parCOf A)) (parCOf A) s)),
     ("keys", runN fun _ s => Desc.named "K5.keys" (keysK (seatCO (parCOf A)) (parCOf A) s)),
     ("join", runN (Desc.K3.joinRun (Desc.K3.seatCalls (Cl := Aff) id) (keysOfO A))),
     ("second",
       runN fun _ s => Desc.named "K5.second" (secondK (seatCO (parCOf A)) (parCOf A) s))] :=
  rfl

/-- **K5's own three runs.** -/
theorem runsN_same : ∀ x ∈ runsN A, x.1 ≠ "join" → RunSame x.2 s s' := by
  intro x hx hj
  rw [runsN_is] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact k5first_same A hs hs' hg h5 H hw hF hG htr
  · exact k5keys_same A hs hs' hg h5 H hw hF hG htr
  · exact absurd rfl hj
  · exact k5second_same A hs hs' hg h5 H hw hF hG htr

end

/-- These runs lay nothing late: the state behind the run is the state in front. -/
theorem own_low {states : ℕ → List (Desc.K9.RunOf S)} {b : ℕ} {name : String} {s : S} {R : Read}
    (hst : ∀ nm r, (states b).find? (fun x => x.1 == name) = some (nm, r) →
      ∀ cl t, r 0 s = .ok (cl, t) → t = s)
    (h : readerOf states b name s = some R) : R.late = [] := by
  obtain ⟨nm, run, cl, t, F, G, hf, hr, hF, hG, _, rfl⟩ := reader_test h
  obtain rfl := hst nm run hf cl t hr
  obtain rfl : F = G := Option.some.inj (hF.symm.trans hG)
  exact lateOf_same F F rfl

/-- **THE END**: the kept test at a run that is RunSame and leaves the state passes. -/
theorem own_formsIn_pass (H : LinkHoles) (l : Link S Claim) (b : ℕ) (own : List (ℕ × ℕ))
    {name : String} (hn : (name == "K8.equations") = false) {s s' : S} {F G : Fork}
    (P : K3Pass s s' F G)
    (hr : (readerOf (statesOfLink l) b name s).isSome = true)
    (h1 : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == name) = some (nm, r) → RunSame r s s')
    (hst : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == name) = some (nm, r) →
      ∀ cl t, r 0 s = .ok (cl, t) → t = s)
    (hin : formsIn (readersOfLink H l) own b name s = true) :
    formsIn (readersOfLink H l) own b name s' = true :=
  k3_formsIn_fwd P (readersOfLink H l) own b name (link_fwd_r H l b hn hr h1)
    (fun R hR x hx => by
      rw [own_low hst (link_reader_r hn hr hR)] at hx
      exact absurd hx List.not_mem_nil) hin

/-- **At the digits' decision's accept.** -/
theorem k3_digits_runsN_same {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (seatDigits claim) piece laid before p guests).decide s rs cols =
      .ok s')
    {a : AttOwn} (hs : s.here = .att a) (hS : Sized a.F) (A : Attention.Plan) :
    ∀ x ∈ runsN A, x.1 ≠ "join" → RunSame x.2 s s' := by
  obtain ⟨a', hs', hg, h5, H, hw⟩ :=
    k3_digits_attSame claim piece laid before p guests s s' rs cols hd hs hS
  have hF : s.fork? = some a.F := by simp [S.fork?, hs]
  obtain ⟨G, P⟩ := k3_digits_pass claim piece laid before p guests s s' rs cols hd hF hS
  exact runsN_same A hs hs' hg h5 H hw hF P.behind P.trees

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.runN_named_same
#print axioms VerifiableInference.OnPublicFiles.k5first_same
#print axioms VerifiableInference.OnPublicFiles.k5second_same
#print axioms VerifiableInference.OnPublicFiles.k5keys_same
#print axioms VerifiableInference.OnPublicFiles.runsN_is
#print axioms VerifiableInference.OnPublicFiles.runsN_same
#print axioms VerifiableInference.OnPublicFiles.own_low
#print axioms VerifiableInference.OnPublicFiles.own_formsIn_pass
#print axioms VerifiableInference.OnPublicFiles.k3_digits_runsN_same
