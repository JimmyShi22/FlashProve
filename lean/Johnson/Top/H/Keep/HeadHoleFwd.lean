-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/HeadHoleFwd.lean: The kind "lookup" (K3): AT THE OUTPUT HEAD's LINK A LINK's
READER ANSWERS BEHIND A K3Pass WHAT IT ANSWERED IN FRONT, WHICHEVER OF THE TWO ANSWERED: the run
itself, or the link's second hole, which the description fills there with "the run itself at the
state with the tables laid" (k6Silent, Johnson/Desc/Kinds/Law/K6SilentCode.lean). So the kept
public test formsIn at "planes" passes: WITH NO PREMISE ON THE HOLE AND NONE THAT THE RUN ITSELF
ANSWERS. Definitions, statements and proofs.

OBJECT: K9.readersOfLink at K9.holesAt's letters; k6Silent, withTables, tablesAt; K3.planesRun at
  the head's caller's readers callerReaders (planesAt iU3).
Used by Johnson/Desc/Sound/MgAt/K3DigitsPlanesHead.lean,
  Johnson/Desc/Sound/MgAt/K3RidesDigFwd3.lean, Johnson/Top/H/Keep/HeadOwnSame.lean and others.
LETTERS: Ph, H, l, b, name; s, s', F, G; X, mH, m; claim, lm, iU3.
Compiled with the whole library.

The road. (1) The run answers at s: it answers the same at s' (reader_fwd). (2) The run is silent
at s: then it is silent at s' (RunBack: a yes at s' gives a yes at s), so both states ask the hole;
the tables read the request, the heard reply, "opened" and the head's own heard rounds, which
SamePlanes keeps: so the same tables are laid over both; the pass lifts to the two states with the
tables laid; the run answers the same there.

Main names:
  forms_cases, forms_of_hole: what a link's reader's answer is, at k6Silent.
  fwd_k6: THE KIND-FREE RULE.
  RunBack, reader_back. planes_back: "planes" goes back.
  layT, withTables_is, tablesAt_same, withTables_pass: the pass lifts.
  unpaid_pop, k3_digits_hob: hob AT THE DIGITS' DECISION's ACCEPT.
  planes_fwd_head, planes_formsIn_pass_head: THE ENDS.

Limits. hob ("a debt that is unpaid behind was unpaid in front") is one clause more than K3Pass
has. "join" at the head's link: fwd_k6 serves, under premises on the calling kind's keys that are
not paid here. Over a K3Pass: that a seated accept gives one, with SamePlanes and hob, is shown
here at the decision's own accept alone.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.RunAnswers
import Johnson.Top.H.Keep.CallersStay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.PscRun
open VerifiableInference.Desc (Claim Link)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.Look (planeClaimsOwn planesAddedF)
open VerifiableInference.Desc.K3 (Seat Readers seatCalls seatDigits planesRun unpaid k3OnOut)
open VerifiableInference.Desc.K9 (Read RunOf readerOf readersOfLink statesOfLink LinkHoles formsIn
  holesAt mergeOf)
open VerifiableInference.Desc.Kinds.Head (planesAt callerReaders)
open VerifiableInference.Desc.Kinds.Head.Law (k6Silent withTables SamePlanes covered_same)
open VerifiableInference.Reads.Pass (Fwd)

/-! ## What the reader's answer is -/

section
variable (Ph : Desc.K8.ReadsQuiet.PH) (H : LinkHoles) (l : Link S Claim) (b : ℕ) {name : String}
  (hH : ∀ b n s, H.silent b n s = k6Silent Ph (statesOfLink l) b n s)
  (hn : (name == "K8.equations") = false)
include hH hn

/-- The run's own reader's answer; or, where that is silent, its answer with the tables laid. -/
theorem forms_cases {s : S} {R : Read} (h : (readersOfLink H l).forms b name s = some R) :
    readerOf (statesOfLink l) b name s = some R ∨
      (readerOf (statesOfLink l) b name s = none ∧
        ∃ t, withTables Ph s = some t ∧ readerOf (statesOfLink l) b name t = some R) := by
  have h' : (if name == "K8.equations" then H.small s
      else match readerOf (statesOfLink l) b name s with
        | some R => some R
        | Option.none => H.silent b name s) = some R := h
  rw [hn] at h'
  cases e : readerOf (statesOfLink l) b name s with
  | some R0 =>
    simp only [e] at h'
    exact Or.inl h'
  | none =>
    simp only [e] at h'
    have h2 : H.silent b name s = some R := h'
    rw [hH] at h2
    unfold k6Silent at h2
    obtain ⟨t, ht, hR⟩ := Option.bind_eq_some_iff.1 h2
    exact Or.inr ⟨rfl, t, ht, hR⟩

theorem forms_of_hole {s t : S} {R : Read} (e : readerOf (statesOfLink l) b name s = none)
    (ht : withTables Ph s = some t) (hR : readerOf (statesOfLink l) b name t = some R) :
    (readersOfLink H l).forms b name s = some R := by
  have h1 : (readersOfLink H l).forms b name s = H.silent b name s := by
    show (if name == "K8.equations" then H.small s
      else match readerOf (statesOfLink l) b name s with
        | some R => some R
        | Option.none => H.silent b name s) = H.silent b name s
    rw [hn, e]
    rfl
  rw [h1, hH]
  unfold k6Silent
  rw [ht]
  exact hR

/-- **THE KIND-FREE RULE.** -/
theorem fwd_k6 {s s' : S}
    (h1 : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == name) = some (nm, r) → RunSame r s s')
    (hback : (readerOf (statesOfLink l) b name s').isSome = true →
      (readerOf (statesOfLink l) b name s).isSome = true)
    (hT : ∀ t, withTables Ph s = some t → ∃ t', withTables Ph s' = some t' ∧
      ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == name) = some (nm, r) → RunSame r t t') :
    Fwd (readersOfLink H l) b name s s' := by
  intro R hR
  rcases forms_cases Ph H l b hH hn hR with h0 | ⟨h0, t, ht, hRt⟩
  · exact link_answers H l b hn (reader_fwd h1 R h0)
  · have e' : readerOf (statesOfLink l) b name s' = none := by
      cases e : readerOf (statesOfLink l) b name s' with
      | none => rfl
      | some R1 =>
        have hb := hback (by rw [e]; rfl)
        rw [h0] at hb
        exact nomatch hb
    obtain ⟨t', ht', hrun⟩ := hT t ht
    exact forms_of_hole Ph H l b hH hn e' ht' (reader_fwd hrun R hRt)

end

/-! ## Back -/

/-- A yes of the run at s' gives a yes at s, with the same claims. -/
def RunBack (r : ℕ → S → Except String (List Claim × S)) (s s' : S) : Prop :=
  ∀ cl t', r 0 s' = .ok (cl, t') → ∃ t Gt, r 0 s = .ok (cl, t) ∧ t.fork? = some Gt

theorem reader_back {states : ℕ → List (RunOf S)} {b : ℕ} {name : String} {s s' : S} {F G : Fork}
    (hF : s.fork? = some F) (hG : s'.fork? = some G) (htr : G.trees = F.trees)
    (h : ∀ nm r, (states b).find? (fun x => x.1 == name) = some (nm, r) → RunBack r s s') :
    (readerOf states b name s').isSome = true → (readerOf states b name s).isSome = true := by
  intro hs
  obtain ⟨R, hR⟩ := Option.isSome_iff_exists.1 hs
  obtain ⟨nm, run, cl, t', F1, G1, hf, hr, hF1, hG1, ht, _⟩ := reader_test hR
  obtain rfl : G = F1 := Option.some.inj (hG.symm.trans hF1)
  obtain ⟨t, Gt, hr0, hGt⟩ := h nm run hf cl t' hr
  rw [reader_make hf hr0 hF hGt (by rw [← ownRow_trees htr]; exact ht)]
  rfl

/-- **"planes" goes back.** -/
theorem planes_back (seat : Seat S Claim) (hA : AtS2 seat) {s s' : S} {F G : Fork}
    (P : K3Pass s s' F G) (hh : seat.heard s' = seat.heard s) (lm : ℕ) (readers : Readers S)
    (hread : ∀ r, readers s' = some r → readers s = some r)
    (hob : ∀ i, unpaid G i = true → unpaid F i = true)
    (hwin : ∀ g, seat.heard s = some g → g.leaves.first + lvLen g ≤ F.next ∧
      g.leaves.first + lvLen g ≤ F.ns ∧
      ∀ j, g.leaves.first ≤ j → j < g.leaves.first + lvLen g → ¬ Filled F j) :
    RunBack (planesRun seat lm readers) s s' := by
  intro cl t' hr
  have hr0 := hr
  unfold planesRun at hr0
  rw [named_bind] at hr0
  obtain ⟨G2, e1, hr0⟩ := hr0
  obtain rfl : G = G2 := Option.some.inj (P.behind.symm.trans ((hA.fork s').symm.trans e1))
  rw [named_bind] at hr0
  obtain ⟨g, e2, hr0⟩ := hr0
  rw [need_bind] at hr0
  obtain ⟨hun, hr0⟩ := hr0
  rw [named_bind] at hr0
  obtain ⟨r, e3, hr0⟩ := hr0
  dsimp only at hr0
  rw [named_bind] at hr0
  obtain ⟨⟨rows, Gx, u⟩, e4, hr0⟩ := hr0
  have e5 : (rows.toList.map seat.claim, seat.mark s' Gx) = (cl, t') := Except.ok.inj hr0
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e5
  obtain ⟨fs, Ga, ua, k1, k2⟩ := flThen_inv
    (x := planeClaimsOwn g lm (fun e col => Fl.need (r.1 e col)) fun col => Fl.need (r.2 col)) e4
  obtain ⟨_, Gb, ub, _, k4⟩ := flThen_inv (x := planesAddedF g) k2
  have hrows : fs = rows :=
    congrArg (fun y : Array Aff × Fork × Tape => y.1) (Option.some.inj k4)
  have e2s : seat.heard s = some g := hh.symm.trans e2
  obtain ⟨w1, w2, w3⟩ := hwin g e2s
  obtain ⟨H', hH'⟩ := own_write_returns (G := F) (g := g) P.sizedF ⟨w1, w3⟩ w2
  have c1 := planeClaimsOwn_at g lm r.1 r.2 k1 (F' := F) (G' := H') hH'
  refine ⟨seat.mark s (H'.paid g.owedPlanes), H'.paid g.owedPlanes, ?_, by
    rw [hA.mark]
    exact fork_putFork s F _ P.front⟩
  unfold planesRun
  rw [named_bind]
  refine ⟨F, (hA.fork s).trans P.front, ?_⟩
  rw [named_bind]
  refine ⟨g, e2s, ?_⟩
  rw [need_bind]
  refine ⟨hob _ hun, ?_⟩
  rw [named_bind]
  refine ⟨r, hread r e3, ?_⟩
  dsimp only
  rw [named_bind]
  refine ⟨(rows, H'.paid g.owedPlanes, []), ?_, rfl⟩
  rw [← hrows]
  exact (flThen_some _ _ F H' [] [] fs c1).trans rfl

/-! ## The pass lifts to the states with the tables laid -/

/-- The state with tables laid in the head's own part a. -/
def layT (s : S) (a : HeadOwn) (tb : OnBytes.Model.Head.Tables) : S :=
  { s with here := .head { a with t := some tb } }

section
variable {s : S} {a : HeadOwn} (hh : s.here = .head a) (tb : OnBytes.Model.Head.Tables)
include hh

theorem layT_fork : (layT s a tb).fork? = s.fork? := by simp [layT, S.fork?, hh]

theorem layT_link : (layT s a tb).link? = s.link? := by simp [layT, S.link?, hh]

theorem layT_tl : (layT s a tb).tl? = s.tl? := by simp [layT, S.tl?, hh]

theorem layT_look : (layT s a tb).lookHeard? = s.lookHeard? := by simp [layT, S.lookHeard?, hh]

theorem layT_merge : mergeOf (layT s a tb) = mergeOf s := by simp [layT, mergeOf, hh]

end

theorem withTables_is {Ph : Desc.K8.ReadsQuiet.PH} {s t : S} (h : withTables Ph s = some t) :
    ∃ a tb, s.here = .head a ∧ Desc.Kinds.Head.Law.tablesAt Ph s = some tb ∧ a.opened = true ∧
      t = layT s a tb := by
  unfold withTables at h
  cases hh : s.here with
  | head a =>
    simp only [hh] at h
    obtain ⟨tb, htb, rfl⟩ := Option.map_eq_some_iff.1 h
    refine ⟨a, tb, rfl, htb, ?_, rfl⟩
    cases ho : a.opened with
    | true => rfl
    | false => simp [Desc.Kinds.Head.Law.tablesAt, hh, ho] at htb
  | between => simp [hh] at h
  | fin _ => simp [hh] at h
  | mem _ => simp [hh] at h
  | lay _ => simp [hh] at h
  | att _ => simp [hh] at h

theorem tablesAt_same (Ph : Desc.K8.ReadsQuiet.PH) {s s' : S} (A : SamePlanes s s') {a : HeadOwn}
    (hh : s.here = .head a) :
    Desc.Kinds.Head.Law.tablesAt Ph s' = Desc.Kinds.Head.Law.tablesAt Ph s := by
  obtain ⟨a', h', o1, o2, _⟩ := A.head a hh
  simp only [Desc.Kinds.Head.Law.tablesAt, hh, h', o1, o2, covered_same A]

/-- **The pass lifts.** -/
theorem withTables_pass {Ph : Desc.K8.ReadsQuiet.PH} {s s' t : S} {F G : Fork}
    (A : SamePlanes s s') (P : K3Pass s s' F G) (h : withTables Ph s = some t) :
    ∃ t', withTables Ph s' = some t' ∧ K3Pass t t' F G ∧ SamePlanes t t' ∧
      t.lookHeard? = s.lookHeard? ∧ t'.lookHeard? = s'.lookHeard? ∧ ∃ o, t.here = .head o := by
  obtain ⟨a, tb, hh, htb, hop, rfl⟩ := withTables_is h
  obtain ⟨a', h', o1, o2, o3, o4, o5, o6, o7, o8⟩ := A.head a hh
  have hop' : a'.opened = true := o1.trans hop
  have ht' : withTables Ph s' = some (layT s' a' tb) := by
    unfold withTables
    simp only [h']
    rw [tablesAt_same Ph A hh, htb]
    rfl
  refine ⟨layT s' a' tb, ht', ?_, ?_, layT_look hh tb, layT_look h' tb, ⟨_, rfl⟩⟩
  · exact
      { same := ⟨P.same.st, P.same.book, P.same.roots, P.same.rowsOwed, P.same.failed,
          P.same.check, P.same.out, P.same.req,
          by rw [layT_link h' tb, layT_link hh tb]; exact P.same.link,
          Or.inr (Or.inr ⟨_, _, rfl, rfl, hop, hop'⟩)⟩
        front := (layT_fork hh tb).trans P.front
        behind := (layT_fork h' tb).trans P.behind
        later := P.later
        sizedF := P.sizedF
        sizedG := P.sizedG
        trees := P.trees
        below := P.below
        owed := P.owed
        merge := by rw [layT_merge h' tb, layT_merge hh tb]; exact P.merge
        tl := by rw [layT_tl h' tb, layT_tl hh tb]; exact P.tl }
  · refine ⟨A.req, A.reply, fun o ho => ?_⟩
    have e : ({ a with t := some tb } : HeadOwn) = o := Desc.First.Here.head.inj ho
    subst e
    exact ⟨{ a' with t := some tb }, rfl, o1, o2, rfl, o4, o5, o6, o7, o8⟩

/-! ## hob at the digits' decision's accept -/

theorem unpaid_pop (A : Array Owed) (o : Owed) (i : ℕ)
    (h : ((((A.push o)[i]?).map (·.added)) != some true) = true) :
    (((A[i]?).map (·.added)) != some true) = true := by
  rw [Array.getElem?_push] at h
  by_cases hi : i = A.size
  · rw [hi, Array.getElem?_eq_none (Nat.le_refl _)]
    rfl
  · rw [if_neg hi] at h
    exact h

/-- **A debt that is unpaid behind the digits' decision was unpaid in front.** -/
theorem k3_digits_hob {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (seatDigits claim) piece laid before p guests).decide s rs cols =
      .ok s')
    {F G : Fork} (P : K3Pass s s' F G) : ∀ i, unpaid G i = true → unpaid F i = true := by
  obtain ⟨F0, x, hF0, hn, e, hE⟩ :=
    decide_ledger (seatDigits claim) piece laid before p guests s s' rs cols hd
  obtain rfl : F = F0 := Option.some.inj (P.front.symm.trans hF0)
  obtain ⟨E, L, ht, ho⟩ := hE P.sizedF
  have hG : s'.fork? = some x.2 := by
    rw [e]
    exact seatDigits_keeps claim s x.1 x.2 (by rw [hF0]; rfl) hn
  obtain rfl : G = x.2 := Option.some.inj (P.behind.symm.trans hG)
  intro i hi
  unfold unpaid at hi ⊢
  rw [ho] at hi
  exact unpaid_pop _ _ i (unpaid_pop _ _ i (unpaid_pop _ _ i hi))

/-! ## "planes" at the head's link -/

section
variable (X : Verify.Public) (mH m : ℕ) (hm : (m == mH) = true) (l : Link S Claim) (b : ℕ)
  (own : List (ℕ × ℕ)) (claim : Aff → Claim) (hA : AtS2 (seatCalls claim)) {s s' : S}
  {F G : Fork} (P : K3Pass s s' F G) (A : SamePlanes s s')
  (hh : (seatCalls claim).heard s' = (seatCalls claim).heard s)
  (hob : ∀ i, unpaid G i = true → unpaid F i = true) (lm iU3 : ℕ)
  (hwin : ∀ g, (seatCalls claim).heard s = some g → g.leaves.first + lvLen g ≤ F.next ∧
    g.leaves.first + lvLen g ≤ F.ns ∧
    ∀ j, g.leaves.first ≤ j → j < g.leaves.first + lvLen g → ¬ Filled F j)
  (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "planes") = some (nm, r) →
    r = planesRun (seatCalls claim) lm (callerReaders (planesAt iU3)))
  {o : HeadOwn} (ho : s.here = .head o)

include hm in
theorem holesAt_k6 : ∀ b n s, (holesAt X mH m l).silent b n s =
    k6Silent (Desc.K9.phAt X m) (statesOfLink l) b n s := by
  intro b n s
  show (if m == mH then k6Silent (Desc.K9.phAt X m) (statesOfLink l)
    else fun _ _ _ => none) b n s = _
  rw [hm]
  rfl

include hm hA P A hh hob hwin hfind ho

/-- **Fwd at "planes", whichever of the two answers.** -/
theorem planes_fwd_head : Fwd (readersOfLink (holesAt X mH m l) l) b "planes" s s' := by
  refine fwd_k6 (Desc.K9.phAt X m) (holesAt X mH m l) l b (holesAt_k6 X mH m hm l) (by decide)
    (fun nm r hf => ?_) (reader_back P.front P.behind P.trees fun nm r hf => ?_) fun t ht => ?_
  · rw [hfind nm r hf]
    exact planes_runSame' (seatCalls claim) hA P hh lm _ (fun r e => by
      rw [headReaders_same A ho P.front P.behind P.trees iU3]
      exact e) hwin
  · rw [hfind nm r hf]
    exact planes_back (seatCalls claim) hA P hh lm _ (fun r e => by
      rw [← headReaders_same A ho P.front P.behind P.trees iU3]
      exact e) hob hwin
  · obtain ⟨t', ht', Pt, At, e1, e2, ot, hot⟩ := withTables_pass A P ht
    refine ⟨t', ht', fun nm r hf => ?_⟩
    rw [hfind nm r hf]
    have hht : (seatCalls claim).heard t' = (seatCalls claim).heard t := by
      show t'.lookHeard? = t.lookHeard?
      rw [e2, e1]
      exact hh
    exact planes_runSame' (seatCalls claim) hA Pt hht lm _ (fun r e => by
      rw [headReaders_same At hot Pt.front Pt.behind Pt.trees iU3]
      exact e) fun g hg => hwin g (by
        show s.lookHeard? = some g
        rw [← e1]
        exact hg)

/-- **The kept test at "planes" passes: no premise on the hole; none that the run itself
answers.** -/
theorem planes_formsIn_pass_head
    (hin : formsIn (readersOfLink (holesAt X mH m l) l) own b "planes" s = true) :
    formsIn (readersOfLink (holesAt X mH m l) l) own b "planes" s' = true := by
  refine k3_formsIn_fwd P (readersOfLink (holesAt X mH m l) l) own b "planes"
    (planes_fwd_head X mH m hm l b claim hA P A hh hob lm iU3 hwin hfind ho) (fun R hR => ?_) hin
  rcases forms_cases (Desc.K9.phAt X m) (holesAt X mH m l) l b (holesAt_k6 X mH m hm l)
    (by decide) hR with h0 | ⟨_, t, ht, hRt⟩
  · exact planes_low (noSilent (holesAt X mH m l)) l b (seatCalls claim) hA lm _ rfl hfind
      (fun F' hF' => by
        obtain rfl : F = F' := Option.some.inj (P.front.symm.trans hF')
        exact P.sizedF)
      (fun g hg => (hwin g hg).1)
      (link_answers (noSilent (holesAt X mH m l)) l b (by decide) h0)
  · obtain ⟨t', _, Pt, _, e1, _, _, _⟩ := withTables_pass A P ht
    exact planes_low (noSilent (holesAt X mH m l)) l b (seatCalls claim) hA lm _ rfl hfind
      (fun F' hF' => by
        obtain rfl : F = F' := Option.some.inj (Pt.front.symm.trans hF')
        exact P.sizedF)
      (fun g hg => (hwin g (by
        show s.lookHeard? = some g
        rw [← e1]
        exact hg)).1)
      (link_answers (noSilent (holesAt X mH m l)) l b (by decide) hRt)

end

/-- PAYERS AGAINST PREMISES, at the digits' decision's accept at the head's link: k3_digits_pass,
k3_digits_samePlanes, digits_keeps_calls, k3_digits_hob, hwin_of_onOut. It proves nothing new. -/
example (X : Verify.Public) (mH m : ℕ) (hm : (m == mH) = true) (l : Link S Claim) (b : ℕ)
    (own : List (ℕ × ℕ)) (claim : Aff → Claim) (hA : AtS2 (seatCalls claim))
    {Cl : Type} (cl2 : Aff → Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl)) (s s' : S)
    (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block (seatDigits cl2) piece laid before p guests).decide s rs cols = .ok s')
    {F : Fork} (hF : s.fork? = some F) (hS : Sized F) {o : HeadOwn} (ho : s.here = .head o)
    {pc : Desc.First.Look.P} (hdc : pc.digits = false) (hO : k3OnOut pc s = true)
    (hL : k3LeftOnItem pc s) (lm iU3 : ℕ)
    (hfind : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "planes") = some (nm, r) →
      r = planesRun (seatCalls claim) lm (callerReaders (planesAt iU3)))
    (hin : formsIn (readersOfLink (holesAt X mH m l) l) own b "planes" s = true) :
    formsIn (readersOfLink (holesAt X mH m l) l) own b "planes" s' = true := by
  obtain ⟨G, P⟩ := k3_digits_pass cl2 piece laid before p guests s s' rs cols hd hF hS
  obtain ⟨F0, x, _, _, e, _⟩ :=
    decide_ledger (seatDigits cl2) piece laid before p guests s s' rs cols hd
  exact planes_formsIn_pass_head X mH m hm l b own claim hA P
    (k3_digits_samePlanes cl2 piece laid before p guests s s' rs cols hd)
    (by rw [e]; exact digits_keeps_calls cl2 claim s x.1 x.2)
    (k3_digits_hob cl2 piece laid before p guests s s' rs cols hd P) lm iU3
    (hwin_of_onOut hdc hF hO hL) hfind ho hin

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.forms_cases
#print axioms VerifiableInference.OnPublicFiles.forms_of_hole
#print axioms VerifiableInference.OnPublicFiles.fwd_k6
#print axioms VerifiableInference.OnPublicFiles.reader_back
#print axioms VerifiableInference.OnPublicFiles.planes_back
#print axioms VerifiableInference.OnPublicFiles.layT_fork
#print axioms VerifiableInference.OnPublicFiles.layT_link
#print axioms VerifiableInference.OnPublicFiles.layT_tl
#print axioms VerifiableInference.OnPublicFiles.layT_look
#print axioms VerifiableInference.OnPublicFiles.layT_merge
#print axioms VerifiableInference.OnPublicFiles.withTables_is
#print axioms VerifiableInference.OnPublicFiles.tablesAt_same
#print axioms VerifiableInference.OnPublicFiles.withTables_pass
#print axioms VerifiableInference.OnPublicFiles.unpaid_pop
#print axioms VerifiableInference.OnPublicFiles.k3_digits_hob
#print axioms VerifiableInference.OnPublicFiles.holesAt_k6
#print axioms VerifiableInference.OnPublicFiles.planes_fwd_head
#print axioms VerifiableInference.OnPublicFiles.planes_formsIn_pass_head
