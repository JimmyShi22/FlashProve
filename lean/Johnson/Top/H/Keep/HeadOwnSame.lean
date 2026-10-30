-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/HeadOwnSame.lean: AT THE OUTPUT HEAD's LINK THE CALLING KIND's OWN THREE RUNS OF
CLAIMS ("norm", "policy", "logits": what the table's name "own" stands for there) AND THE LOOKUP's
RUN "join" AT THAT KIND's KEY VECTORS ANSWER BEHIND A LOOKUP ON THE DIGITS WHAT THEY ANSWERED IN
FRONT: THE FORWARD HALF. So, UNDER hback AS A NAMED PREMISE, the link's reader goes forward
whichever of the run and the link's second hole answers, and the kept public tests formsIn pass.
Statements and proofs: joinings over the laws of K6's files.

OBJECT: (Kinds.Head.kind asClaim (seatAt h iU3) lk piece p).claims; Kinds.Head.callerKeys;
  K3.joinRun;
  K9.readersOfLink at K9.holesAt's letters.
Used by Johnson/Top/H/Keep/HeadOwnAtSeat.lean and Johnson/P5J/K03HeadOwnAt.lean.
LETTERS: h, iU3, lk, piece, p; s, s', F, G; X, mH, m, l, b, own.
The three of K6's files that this head names
  are in this library.
Compiled with the whole library.
What K6's files hold: Alike, letters_alike (Johnson/Desc/Kinds/Law/RunsFixed.lean): where the
letters are read at s they are read the same at s'; k6_run_spec (Law/K06Runs.lean); k6_same
(Law/HeadRunsCarry.lean): the state behind one of the three runs is the state in front.

Main names:
  k6_run_make: the way back of k6_run_spec: where the letters are read and the run's forms are
    there, the run returns.
  alike_of_pass: Alike from SamePlanes, a K3Pass and "squaresP stays". k3_digits_squares: that, at
    the decision's accept.
  k6_runSame: RunSame at each of the three runs. callerKeys_alike: the key vectors go forward.
  withTables_alike: Alike lifts to the two states with the tables laid.
  own_fwd_head, own_formsIn_pass_head; join_fwd_head, join_formsIn_pass_head: THE ENDS, UNDER hback.

Limits. hback ("if the run's own reader answers behind, it answers in front") IS NOT PAID: the
law of K6's files on what was heard is one-sided.
(Where this and lean/THEOREM.md differ, the page holds.) hfind is a premise. Over
a K3Pass with SamePlanes.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.HeadHoleFwd
import Johnson.Top.H.Keep.AttOwnSame
import Johnson.Desc.Kinds.Law.RunsFixed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.PscRun
open VerifiableInference.Desc (Claim Link)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K3 (seatCalls seatDigits joinRun)
open VerifiableInference.Desc.K9 (Read readerOf readersOfLink statesOfLink LinkHoles formsIn holesAt
  lateOf)
open VerifiableInference.Desc.Kinds.Head (seatAt asClaim callerKeys lettersAt)
open VerifiableInference.Desc.Kinds.Head.Law (withTables SamePlanes Alike letters_alike k6_run_spec
  k6_same lookup_mem lookup_map_self)
open VerifiableInference.Reads.Pass (Fwd)

/-- **The way back of k6_run_spec.** -/
theorem k6_run_make {T Cl : Type} (cl : Aff → Cl) (L : Desc.Kinds.Head.Seat T)
    (link piece : ℕ) (par : Desc.Kinds.Head.Par) (name : String)
    (run : ℕ → T → Except String (List Cl × T)) (n : ℕ) (s : T) (g : Desc.Kinds.Head.Given)
    (b : Desc.Kinds.Head.Behind) (x : Desc.Kinds.Head.Places) (fs : List Aff)
    (h1 : (Desc.Kinds.Head.kind cl L link piece par).claims.lookup name = some run)
    (hv : lettersAt par L s = .ok (g, b, x))
    (h2 : ((fun (_ : Desc.Kinds.Head.Given) (_ : Desc.Kinds.Head.Behind)
      (_ : Desc.Kinds.Head.Places) => Desc.Kinds.Head.claims) g b x).lookup name = some fs) :
    ∃ s', run n s = .ok (fs.map cl, s') := by
  have h1' : (Desc.Kinds.Head.runsBy ["norm", "policy", "logits"]
      (fun _ _ _ => Desc.Kinds.Head.claims)
      (fun g _ _ => g.calls.map fun c => Desc.Kinds.Head.keyVector Desc.Kinds.Head.key c.1 c.2)
      cl par L).lookup name = some run := h1
  unfold Desc.Kinds.Head.runsBy at h1'
  have hr := lookup_map_self _ _ _ _ h1'
  subst hr
  simp only [bind, Except.bind, pure, Except.pure, hv, h2, Desc.named]
  exact ⟨_, rfl⟩

/-- **Alike, from what the digits' accept hands on.** -/
theorem alike_of_pass {s s' : S} {F G : Fork} (A : SamePlanes s s') (P : K3Pass s s' F G)
    {o : HeadOwn} (ho : s.here = .head o)
    (hsq : ∀ o', s'.here = .head o' → o'.squaresP = o.squaresP) : Alike s s' := by
  obtain ⟨o', h', o1, o2, o3, o4, _, _, _, _⟩ := A.head o ho
  have hop : o.opened = true := by
    cases hc : o.opened with
    | true => rfl
    | false =>
      have hf := P.front
      simp [S.fork?, ho, hc] at hf
  have eF : o.F = F := by
    have hf := P.front
    simpa [S.fork?, ho, hop] using hf
  have eG : o'.F = G := by
    have hf := P.behind
    simpa [S.fork?, h', o1.trans hop] using hf
  exact ⟨o, o', ho, h', o2, hsq o' h', o3, o1, o4, A.reply, A.req,
    by rw [eF, eG]; exact ⟨P.later.next, P.later.ns, fun _ => P.sizedG, P.later.keep⟩,
    by rw [eF, eG, P.trees]⟩

/-- The digits' decision leaves the state of the squares' level's sumcheck. -/
theorem k3_digits_squares {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (seatDigits claim) piece laid before p guests).decide s rs cols =
      .ok s')
    {o : HeadOwn} (ho : s.here = .head o) :
    ∀ o', s'.here = .head o' → o'.squaresP = o.squaresP := by
  obtain ⟨F, G, g, tl, hF, _, e, _⟩ :=
    k3_digits_footprint claim piece laid before p guests s s' rs cols hd
  have hop : o.opened = true := by
    cases hc : o.opened with
    | true => rfl
    | false => simp [S.fork?, ho, hc] at hF
  intro o' h'
  rw [e] at h'
  simp [S.putTl, S.putFork, ho, hop] at h'
  rw [← h']

section
variable (h : OnBytes.Model.Head.Shape) (iU3 lk piece : ℕ) (p : Desc.Kinds.Head.Par)

/-- **RunSame at each of the three runs.** -/
theorem k6_runSame {name : String} {run : ℕ → S → Except String (List Claim × S)}
    (hrun : (Desc.Kinds.Head.kind asClaim (seatAt h iU3) lk piece p).claims.lookup name = some run)
    {s s' : S} (a : Alike s s') {F G : Fork} (hF : s.fork? = some F) (hG : s'.fork? = some G)
    (htr : G.trees = F.trees) : RunSame run s s' := by
  intro cl t F1 G1 hr hF1 hG1
  obtain ⟨g, b, x, fs, h1, h2, h3⟩ :=
    k6_run_spec asClaim (seatAt h iU3) lk piece p name run 0 s t cl hrun hr
  obtain rfl : t = s :=
    k6_same h iU3 lk piece p (name, run) (lookup_mem _ _ _ hrun) 0 s (cl, t) hr
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans hF1)
  obtain rfl : F = G1 := Option.some.inj (hF.symm.trans hG1)
  obtain ⟨t', ht'⟩ := k6_run_make asClaim (seatAt h iU3) lk piece p name run 0 s' g b x fs hrun
    (letters_alike h iU3 p a (g, b, x) h1) h2
  obtain rfl : t' = s' :=
    k6_same h iU3 lk piece p (name, run) (lookup_mem _ _ _ hrun) 0 s' (fs.map asClaim, t') ht'
  refine ⟨t', G, G, by rw [h3]; exact ht', hG, hG, ?_, htr⟩
  rw [lateOf_same G G rfl, lateOf_same F F rfl]

/-- **The key vectors go forward.** -/
theorem callerKeys_alike {s s' : S} (a : Alike s s') (KF : Array Aff)
    (e : callerKeys p (seatAt h iU3) s = some KF) : callerKeys p (seatAt h iU3) s' = some KF := by
  unfold callerKeys at e ⊢
  cases hv : lettersAt p (seatAt h iU3) s with
  | error w =>
    rw [hv] at e
    simp [Except.toOption] at e
  | ok v =>
    rw [letters_alike h iU3 p a v hv]
    rw [hv] at e
    exact e

end

/-- **Alike lifts to the two states with the tables laid.** -/
theorem withTables_alike {Ph : Desc.K8.ReadsQuiet.PH} {s s' t : S} (A : SamePlanes s s')
    (a : Alike s s') (h : withTables Ph s = some t) :
    ∃ t', withTables Ph s' = some t' ∧ Alike t t' := by
  obtain ⟨o0, tb, hh, htb, hop, rfl⟩ := withTables_is h
  obtain ⟨o, o', ho, ho', e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := a
  obtain rfl : o0 = o := Desc.First.Here.head.inj (hh.symm.trans ho)
  refine ⟨layT s' o' tb, ?_, ⟨{ o0 with t := some tb }, { o' with t := some tb }, rfl, rfl, e1, e2,
    rfl, e4, e5, e6, e7, e8, e9⟩⟩
  unfold withTables
  simp only [ho']
  rw [tablesAt_same Ph A hh, htb]
  rfl

section
variable (X : Verify.Public) (mH m : ℕ) (hm : (m == mH) = true) (l : Link S Claim) (b : ℕ)
  (own : List (ℕ × ℕ)) (h : OnBytes.Model.Head.Shape) (iU3 lk piece : ℕ)
  (p : Desc.Kinds.Head.Par) {s s' : S} {F G : Fork} (P : K3Pass s s' F G) (A : SamePlanes s s')
  (a : Alike s s')
include hm P A a

/-- **Fwd at one of the head's own three runs, whichever of the two answers: under hback.** -/
theorem own_fwd_head {name : String} (hn : (name == "K8.equations") = false)
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == name) = some (nm, r) →
      (Desc.Kinds.Head.kind asClaim (seatAt h iU3) lk piece p).claims.lookup name = some r)
    (hback : (readerOf (statesOfLink l) b name s').isSome = true →
      (readerOf (statesOfLink l) b name s).isSome = true) :
    Fwd (readersOfLink (holesAt X mH m l) l) b name s s' := by
  refine fwd_k6 (Desc.K9.phAt X m) (holesAt X mH m l) l b (holesAt_k6 X mH m hm l) hn
    (fun nm r hf => k6_runSame h iU3 lk piece p (hfind nm r hf) a P.front P.behind P.trees) hback
    fun t ht => ?_
  obtain ⟨t', ht', Pt, _⟩ := withTables_pass A P ht
  obtain ⟨t'', ht'', at'⟩ := withTables_alike A a ht
  obtain rfl : t' = t'' := Option.some.inj (ht'.symm.trans ht'')
  exact ⟨t', ht', fun nm r hf =>
    k6_runSame h iU3 lk piece p (hfind nm r hf) at' Pt.front Pt.behind Pt.trees⟩

/-- **The kept test at one of the three runs passes: under hback.** -/
theorem own_formsIn_pass_head {name : String} (hn : (name == "K8.equations") = false)
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == name) = some (nm, r) →
      (Desc.Kinds.Head.kind asClaim (seatAt h iU3) lk piece p).claims.lookup name = some r)
    (hback : (readerOf (statesOfLink l) b name s').isSome = true →
      (readerOf (statesOfLink l) b name s).isSome = true)
    (hin : formsIn (readersOfLink (holesAt X mH m l) l) own b name s = true) :
    formsIn (readersOfLink (holesAt X mH m l) l) own b name s' = true := by
  refine k3_formsIn_fwd P (readersOfLink (holesAt X mH m l) l) own b name
    (own_fwd_head X mH m hm l b h iU3 lk piece p P A a hn hfind hback) (fun R hR y hy => ?_) hin
  have hst : ∀ u : S, ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == name) = some (nm, r) →
      ∀ cl t, r 0 u = .ok (cl, t) → t = u := fun u nm r hf cl t hr =>
    k6_same h iU3 lk piece p (name, r) (lookup_mem _ _ _ (hfind nm r hf)) 0 u (cl, t) hr
  rcases forms_cases (Desc.K9.phAt X m) (holesAt X mH m l) l b (holesAt_k6 X mH m hm l) hn hR
    with h0 | ⟨_, t, _, hRt⟩
  · rw [own_low (hst s) h0] at hy
    exact absurd hy List.not_mem_nil
  · rw [own_low (hst t) hRt] at hy
    exact absurd hy List.not_mem_nil

/-- **Fwd at "join", whichever of the two answers: under hback.** -/
theorem join_fwd_head (hA : AtS2 (seatCalls asClaim))
    (hh : (seatCalls asClaim).heard s' = (seatCalls asClaim).heard s)
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "join") = some (nm, r) →
      r = joinRun (seatCalls asClaim) (callerKeys p (seatAt h iU3)))
    (hback : (readerOf (statesOfLink l) b "join" s').isSome = true →
      (readerOf (statesOfLink l) b "join" s).isSome = true) :
    Fwd (readersOfLink (holesAt X mH m l) l) b "join" s s' := by
  refine fwd_k6 (Desc.K9.phAt X m) (holesAt X mH m l) l b (holesAt_k6 X mH m hm l) (by decide)
    (fun nm r hf => ?_) hback fun t ht => ?_
  · rw [hfind nm r hf]
    exact join_runSame' (seatCalls asClaim) hA P hh _ (callerKeys_alike h iU3 p a)
  · obtain ⟨t', ht', Pt, _, e1, e2, _⟩ := withTables_pass A P ht
    obtain ⟨t'', ht'', at'⟩ := withTables_alike A a ht
    obtain rfl : t' = t'' := Option.some.inj (ht'.symm.trans ht'')
    refine ⟨t', ht', fun nm r hf => ?_⟩
    rw [hfind nm r hf]
    have hht : (seatCalls asClaim).heard t' = (seatCalls asClaim).heard t := by
      show t'.lookHeard? = t.lookHeard?
      rw [e2, e1]
      exact hh
    exact join_runSame' (seatCalls asClaim) hA Pt hht _ (callerKeys_alike h iU3 p at')

/-- **The kept test at "join" passes: under hback.** -/
theorem join_formsIn_pass_head (hA : AtS2 (seatCalls asClaim))
    (hh : (seatCalls asClaim).heard s' = (seatCalls asClaim).heard s)
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "join") = some (nm, r) →
      r = joinRun (seatCalls asClaim) (callerKeys p (seatAt h iU3)))
    (hback : (readerOf (statesOfLink l) b "join" s').isSome = true →
      (readerOf (statesOfLink l) b "join" s).isSome = true)
    (hin : formsIn (readersOfLink (holesAt X mH m l) l) own b "join" s = true) :
    formsIn (readersOfLink (holesAt X mH m l) l) own b "join" s' = true := by
  refine k3_formsIn_fwd P (readersOfLink (holesAt X mH m l) l) own b "join"
    (join_fwd_head X mH m hm l b h iU3 p P A a hA hh hfind hback) (fun R hR y hy => ?_) hin
  rcases forms_cases (Desc.K9.phAt X m) (holesAt X mH m l) l b (holesAt_k6 X mH m hm l)
    (by decide) hR with h0 | ⟨_, t, _, hRt⟩
  · rw [join_low (noSilent (holesAt X mH m l)) l b (seatCalls asClaim) hA _ rfl hfind
      (link_answers (noSilent (holesAt X mH m l)) l b (by decide) h0)] at hy
    exact absurd hy List.not_mem_nil
  · rw [join_low (noSilent (holesAt X mH m l)) l b (seatCalls asClaim) hA _ rfl hfind
      (link_answers (noSilent (holesAt X mH m l)) l b (by decide) hRt)] at hy
    exact absurd hy List.not_mem_nil

end

/-- PAYERS AGAINST PREMISES, at the digits' decision's accept at the head's link: k3_digits_pass,
k3_digits_samePlanes, k3_digits_squares into alike_of_pass and own_formsIn_pass_head. It proves
nothing new. -/
example (X : Verify.Public) (mH m : ℕ) (hm : (m == mH) = true) (l : Link S Claim) (b : ℕ)
    (own : List (ℕ × ℕ)) (h : OnBytes.Model.Head.Shape) (iU3 lk pc : ℕ) (p : Desc.Kinds.Head.Par)
    {Cl : Type} (cl2 : Aff → Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (q : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl)) (s s' : S)
    (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (seatDigits cl2) piece laid before q guests).decide s rs cols = .ok s')
    {F : Fork} (hF : s.fork? = some F) (hS : Sized F) {o : HeadOwn} (ho : s.here = .head o)
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "norm") = some (nm, r) →
      (Desc.Kinds.Head.kind asClaim (seatAt h iU3) lk pc p).claims.lookup "norm" = some r)
    (hback : (readerOf (statesOfLink l) b "norm" s').isSome = true →
      (readerOf (statesOfLink l) b "norm" s).isSome = true)
    (hin : formsIn (readersOfLink (holesAt X mH m l) l) own b "norm" s = true) :
    formsIn (readersOfLink (holesAt X mH m l) l) own b "norm" s' = true := by
  obtain ⟨G, P⟩ := k3_digits_pass cl2 piece laid before q guests s s' rs cols hd hF hS
  have A := k3_digits_samePlanes cl2 piece laid before q guests s s' rs cols hd
  exact own_formsIn_pass_head X mH m hm l b own h iU3 lk pc p P A
    (alike_of_pass A P ho (k3_digits_squares cl2 piece laid before q guests s s' rs cols hd ho))
    (by decide) hfind hback hin

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k6_run_make
#print axioms VerifiableInference.OnPublicFiles.alike_of_pass
#print axioms VerifiableInference.OnPublicFiles.k3_digits_squares
#print axioms VerifiableInference.OnPublicFiles.k6_runSame
#print axioms VerifiableInference.OnPublicFiles.callerKeys_alike
#print axioms VerifiableInference.OnPublicFiles.withTables_alike
#print axioms VerifiableInference.OnPublicFiles.own_fwd_head
#print axioms VerifiableInference.OnPublicFiles.own_formsIn_pass_head
#print axioms VerifiableInference.OnPublicFiles.join_fwd_head
#print axioms VerifiableInference.OnPublicFiles.join_formsIn_pass_head
