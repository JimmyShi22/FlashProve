-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/HeadOwnAtSeat.lean: THE ENDS OF Johnson/Top/H/Keep/HeadOwnSame.lean AGAIN, AT
THE RUNS THAT THE SEATED LINK STATES, WHICH ARE TIED TO THE KIND's OWN RUNS BY TWO IMPLICATIONS ON
RETURNS AND BY NO EQUATION; AND WITH hback PAID UNDER ONE NAMED PREMISE. At the output head's link
the kept public tests formsIn at "norm", "policy", "logits" and "join" pass a lookup on the digits,
whichever of the run and the link's second hole answers. Definitions, statements and proofs:
joinings.

OBJECT: K9.readersOfLink at K9.holesAt's letters; K6States
  (Johnson/Desc/Kinds/Law/K6Silent.lean) and the two clauses of K6Back
  (Johnson/Desc/Kinds/Law/K6SilentRides.lean), WRITTEN OUT HERE AS PREMISES hBo, hBj, to the letter.
Used by Johnson/P5J/K03HeadSixAt.lean and Johnson/P5J/K03HeadOwnAt.lean.
LETTERS: those of HeadOwnSame.lean; K, hBo, hBj, hReady.
This file does not import K6SilentRides.lean, and so was not compiled over it.
Compiled with the whole library.
NOT TYPECHECKED: that the payer of K6States and K6Back at the description as it
is opened (six_at_seat, Johnson/P4SR/SixClosed.lean) meets K, hBo, hBj as they are typed here: its
files are not imported here. (Where this and
lean/THEOREM.md differ, the page holds.)

Main names:
  replySame; runSame_through, runBack_through: RunSame and RunBack go through RunUnder and RunOver.
  letters_goBack: the letters go back, by letters_back and letters_at
    (Johnson/Desc/Kinds/Law/RunsStill.lean), under hReady.
  k6_runBack, callerKeys_back, join_back: the runs go back.
  own_fwd_seat, own_formsIn_pass_seat; join_fwd_seat, join_formsIn_pass_seat: THE ENDS.

Limits. hReady: "K6Ready at whatever the state in front shows": A FACT ON THE STATE IN FRONT OF THE
DIGITS: by report nobody has walked it there. (Where
this and lean/THEOREM.md differ, the page holds.) hob, SamePlanes, Alike
and the K3Pass are premises: paid at the digits' decision's own accept in HeadHoleFwd.lean and
HeadOwnSame.lean.

Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.HeadOwnSame
import Johnson.Top.H.Keep.RunUnder
import Johnson.Desc.Kinds.Law.K6Silent
import Johnson.Desc.Kinds.Law.RunsStill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.PscRun
open VerifiableInference.Desc (Claim Link)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K3 (Seat seatCalls joinRun unpaid)
open VerifiableInference.Desc.K9 (Read RunOf readerOf readersOfLink statesOfLink LinkHoles formsIn
  holesAt lateOf)
open VerifiableInference.Desc.Kinds.Head (seatAt asClaim callerKeys lettersAt)
open VerifiableInference.Desc.Kinds.Head.Law (withTables SamePlanes Alike k6_run_spec k6_same
  k6_join lookup_mem K6States K6Ready Sees letters_back letters_at same_putFork)
open VerifiableInference.Reads.Pass (Fwd)

/-- The second state has the first one's heard reply. -/
def replySame (t u : S) : Prop := u.out.reply = t.out.reply

/-- **RunSame goes through two implications on returns.** -/
theorem runSame_through {run run' : ℕ → S → Except String (List Claim × S)} {pass : S → S → Prop}
    {s s' : S} (hU : RunUnder run run') (hO : RunOver pass run run')
    (hp : ∀ cl t', run' 0 s' = .ok (cl, t') → pass s' t') (h : RunSame run' s s') :
    RunSame run s s' := by
  intro cl t F G hr hF hG
  obtain ⟨t', F', G', e1, e2, e3, e4, e5⟩ := h cl t F G (hU 0 s (cl, t) hr) hF hG
  exact ⟨t', F', G', hO 0 s' (cl, t') e1 (hp cl t' e1), e2, e3, e4, e5⟩

/-- So does RunBack. -/
theorem runBack_through {run run' : ℕ → S → Except String (List Claim × S)} {pass : S → S → Prop}
    {s s' : S} (hU : RunUnder run run') (hO : RunOver pass run run')
    (hp : ∀ cl t, run' 0 s = .ok (cl, t) → pass s t) (h : RunBack run' s s') :
    RunBack run s s' := by
  intro cl t' hr
  obtain ⟨t, Gt, e1, e2⟩ := h cl t' (hU 0 s' (cl, t') hr)
  exact ⟨t, Gt, hO 0 s (cl, t) e1 (hp cl t e1), e2⟩

section
variable (h : OnBytes.Model.Head.Shape) (iU3 lk piece : ℕ) (p : Desc.Kinds.Head.Par)

/-- **The letters go back**, where the promise K6Ready stands at what the state in front shows. -/
theorem letters_goBack {s s' : S} (a : Alike s s')
    (hReady : ∀ z U, Sees s z U → K6Ready h iU3 p z U) :
    ∀ v, lettersAt p (seatAt h iU3) s' = .ok v → lettersAt p (seatAt h iU3) s = .ok v := by
  obtain ⟨o, o', ho, ho', e1, e2, e3, e4, e5, e6, e7, hL, hK⟩ := a
  have hs : Sees s ⟨o.x, o.squaresP, o.t, o.opened, o.lookHeard, s.out.reply, s.req⟩ o.F :=
    ⟨o, ho, rfl, rfl⟩
  have hs' : Sees s' ⟨o.x, o.squaresP, o.t, o.opened, o.lookHeard, s.out.reply, s.req⟩ o'.F :=
    ⟨o', ho', rfl, by rw [e1, e2, e3, e4, e5, e6, e7]⟩
  intro v hv
  exact letters_at h iU3 p (letters_back h iU3 p (hReady _ _ hs) hs' hL hK hv) hs (Later.refl _) rfl

/-- **Each of the three own runs goes back.** -/
theorem k6_runBack {name : String} {run : ℕ → S → Except String (List Claim × S)}
    (hrun : (Desc.Kinds.Head.kind asClaim (seatAt h iU3) lk piece p).claims.lookup name = some run)
    {s s' : S}
    (hlb : ∀ v, lettersAt p (seatAt h iU3) s' = .ok v → lettersAt p (seatAt h iU3) s = .ok v)
    {F : Fork} (hF : s.fork? = some F) : RunBack run s s' := by
  intro cl t' hr
  obtain ⟨g, b, x, fs, h1, h2, h3⟩ :=
    k6_run_spec asClaim (seatAt h iU3) lk piece p name run 0 s' t' cl hrun hr
  obtain ⟨t, ht⟩ := k6_run_make asClaim (seatAt h iU3) lk piece p name run 0 s g b x fs hrun
    (hlb _ h1) h2
  obtain rfl : t = s :=
    k6_same h iU3 lk piece p (name, run) (lookup_mem _ _ _ hrun) 0 s (fs.map asClaim, t) ht
  exact ⟨t, F, by rw [h3]; exact ht, hF⟩

/-- The key vectors go back. -/
theorem callerKeys_back {s s' : S}
    (hlb : ∀ v, lettersAt p (seatAt h iU3) s' = .ok v → lettersAt p (seatAt h iU3) s = .ok v)
    (KF : Array Aff) (e : callerKeys p (seatAt h iU3) s' = some KF) :
    callerKeys p (seatAt h iU3) s = some KF := by
  unfold callerKeys at e ⊢
  cases hv : lettersAt p (seatAt h iU3) s' with
  | error w =>
    rw [hv] at e
    simp [Except.toOption] at e
  | ok v =>
    rw [hlb v hv]
    rw [hv] at e
    exact e

end

/-- **"join" goes back.** -/
theorem join_back (seat : Seat S Claim) (hA : AtS2 seat) {s s' : S} {F G : Fork}
    (P : K3Pass s s' F G) (hh : seat.heard s' = seat.heard s) (keys : S → Option (Array Aff))
    (hkb : ∀ KF, keys s' = some KF → keys s = some KF)
    (hob : ∀ i, unpaid G i = true → unpaid F i = true) : RunBack (joinRun seat keys) s s' := by
  intro cl t' hr
  have hr0 := hr
  unfold joinRun at hr0
  rw [named_bind] at hr0
  obtain ⟨G2, e1, hr0⟩ := hr0
  obtain rfl : G = G2 := Option.some.inj (P.behind.symm.trans ((hA.fork s').symm.trans e1))
  rw [named_bind] at hr0
  obtain ⟨g, e2, hr0⟩ := hr0
  rw [need_bind] at hr0
  obtain ⟨hun, hr0⟩ := hr0
  rw [named_bind] at hr0
  obtain ⟨KF, e3, hr0⟩ := hr0
  rw [named_bind] at hr0
  obtain ⟨⟨c, Gx, u⟩, e4, hr0⟩ := hr0
  have e5 : ([seat.claim c], seat.mark s' Gx) = (cl, t') := Except.ok.inj hr0
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e5
  refine ⟨seat.mark s (F.paid g.owedJoin), F.paid g.owedJoin, ?_, by
    rw [hA.mark]
    exact fork_putFork s F _ P.front⟩
  unfold joinRun
  rw [named_bind]
  refine ⟨F, (hA.fork s).trans P.front, ?_⟩
  rw [named_bind]
  refine ⟨g, hh.symm.trans e2, ?_⟩
  rw [need_bind]
  refine ⟨hob _ hun, ?_⟩
  rw [named_bind]
  refine ⟨KF, hkb KF e3, ?_⟩
  rw [named_bind]
  exact ⟨(c, F.paid g.owedJoin, []), joinF_at e4 F, rfl⟩

section
variable (X : Verify.Public) (mH m : ℕ) (hm : (m == mH) = true) (l : Link S Claim) (b : ℕ)
  (own : List (ℕ × ℕ)) (h : OnBytes.Model.Head.Shape) (iU3 lk piece : ℕ)
  (p : Desc.Kinds.Head.Par) {s s' : S} {F G : Fork} (P : K3Pass s s' F G) (A : SamePlanes s s')
  (a : Alike s s') (K : K6States h iU3 p lk piece (statesOfLink l) b)
  (hReady : ∀ z U, Sees s z U → K6Ready h iU3 p z U)
include hm P A a K hReady

section Own
variable
  (hBo : ∀ name run run', (statesOfLink l b).find? (fun r => r.1 == name) = some (name, run) →
    (Desc.Kinds.Head.kind asClaim (seatAt h iU3) lk piece p).claims.lookup name = some run' →
    ∀ k t y, run' k t = .ok y → y.2.out.reply = t.out.reply → run k t = .ok y)
include hBo

/-- **Fwd at one of the head's own three runs, as the seated link states it.** -/
theorem own_fwd_seat {name : String} (hn3 : name = "norm" ∨ name = "policy" ∨ name = "logits") :
    Fwd (readersOfLink (holesAt X mH m l) l) b name s s' := by
  obtain ⟨run, run', hf, hrun, hU⟩ := K.own name hn3
  have hn : (name == "K8.equations") = false := by
    rcases hn3 with rfl | rfl | rfl <;> decide
  have hO : RunOver replySame run run' := hBo name run run' hf hrun
  have key : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == name) = some (nm, r) → r = run :=
    fun nm r e => by
      rw [hf] at e
      exact (congrArg Prod.snd (Option.some.inj e)).symm
  have stay : ∀ u cl t, run' 0 u = .ok (cl, t) → replySame u t := fun u cl t e => by
    obtain rfl : t = u :=
      k6_same h iU3 lk piece p (name, run') (lookup_mem _ _ _ hrun) 0 u (cl, t) e
    rfl
  refine fwd_k6 (Desc.K9.phAt X m) (holesAt X mH m l) l b (holesAt_k6 X mH m hm l) hn
    (fun nm r e => ?_) (reader_back P.front P.behind P.trees fun nm r e => ?_) fun t ht => ?_
  · rw [key nm r e]
    exact runSame_through hU hO (stay s')
      (k6_runSame h iU3 lk piece p hrun a P.front P.behind P.trees)
  · rw [key nm r e]
    exact runBack_through hU hO (stay s)
      (k6_runBack h iU3 lk piece p hrun (letters_goBack h iU3 p a hReady) P.front)
  · obtain ⟨t', ht', Pt, _⟩ := withTables_pass A P ht
    obtain ⟨t'', ht'', at'⟩ := withTables_alike A a ht
    obtain rfl : t' = t'' := Option.some.inj (ht'.symm.trans ht'')
    refine ⟨t', ht', fun nm r e => ?_⟩
    rw [key nm r e]
    exact runSame_through hU hO (stay t')
      (k6_runSame h iU3 lk piece p hrun at' Pt.front Pt.behind Pt.trees)

/-- **The kept test at one of the three runs passes.** -/
theorem own_formsIn_pass_seat {name : String}
    (hn3 : name = "norm" ∨ name = "policy" ∨ name = "logits")
    (hin : formsIn (readersOfLink (holesAt X mH m l) l) own b name s = true) :
    formsIn (readersOfLink (holesAt X mH m l) l) own b name s' = true := by
  have hn : (name == "K8.equations") = false := by
    rcases hn3 with rfl | rfl | rfl <;> decide
  refine k3_formsIn_fwd P (readersOfLink (holesAt X mH m l) l) own b name
    (own_fwd_seat X mH m hm l b h iU3 lk piece p P A a K hReady hBo hn3) (fun R hR y hy => ?_) hin
  obtain ⟨run, run', hf, hrun, hU⟩ := K.own name hn3
  have hst : ∀ u : S, ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == name) = some (nm, r) →
      ∀ cl t, r 0 u = .ok (cl, t) → t = u := fun u nm r e cl t hr => by
    rw [hf] at e
    obtain rfl : run = r := congrArg Prod.snd (Option.some.inj e)
    exact k6_same h iU3 lk piece p (name, run') (lookup_mem _ _ _ hrun) 0 u (cl, t)
      (hU 0 u (cl, t) hr)
  rcases forms_cases (Desc.K9.phAt X m) (holesAt X mH m l) l b (holesAt_k6 X mH m hm l) hn hR
    with h0 | ⟨_, t, _, hRt⟩
  · rw [own_low (hst s) h0] at hy
    exact absurd hy List.not_mem_nil
  · rw [own_low (hst t) hRt] at hy
    exact absurd hy List.not_mem_nil

end Own

section Join
variable
  (hBj : ∀ run, (statesOfLink l b).find? (fun r => r.1 == "join") = some ("join", run) →
    ∀ k t y, joinRun (seatCalls asClaim) (callerKeys p (seatAt h iU3)) k t = .ok y →
      y.2.out.reply = t.out.reply → run k t = .ok y)
  (hA : AtS2 (seatCalls asClaim))
  (hh : (seatCalls asClaim).heard s' = (seatCalls asClaim).heard s)
  (hob : ∀ i, unpaid G i = true → unpaid F i = true)
include hBj hA hh hob

/-- **Fwd at "join", as the seated link states it.** -/
theorem join_fwd_seat : Fwd (readersOfLink (holesAt X mH m l) l) b "join" s s' := by
  obtain ⟨run, hf, hU⟩ := K.join
  have hO : RunOver replySame run
      (joinRun (seatCalls asClaim) (callerKeys p (seatAt h iU3))) := hBj run hf
  have key : ∀ nm r, (statesOfLink l b).find? (fun x => x.1 == "join") = some (nm, r) → r = run :=
    fun nm r e => by
      rw [hf] at e
      exact (congrArg Prod.snd (Option.some.inj e)).symm
  have stay : ∀ u cl t, joinRun (seatCalls asClaim) (callerKeys p (seatAt h iU3)) 0 u =
      .ok (cl, t) → replySame u t := fun u cl t e => by
    obtain ⟨F', g, _, _, e3⟩ := k6_join _ 0 u (cl, t) e
    have e3' : t = u.putFork (F'.paid g.owedJoin) := e3
    rw [e3']
    exact (same_putFork u _).reply
  refine fwd_k6 (Desc.K9.phAt X m) (holesAt X mH m l) l b (holesAt_k6 X mH m hm l) (by decide)
    (fun nm r e => ?_) (reader_back P.front P.behind P.trees fun nm r e => ?_) fun t ht => ?_
  · rw [key nm r e]
    exact runSame_through hU hO (stay s')
      (join_runSame' (seatCalls asClaim) hA P hh _ (callerKeys_alike h iU3 p a))
  · rw [key nm r e]
    exact runBack_through hU hO (stay s)
      (join_back (seatCalls asClaim) hA P hh _
        (callerKeys_back h iU3 p (letters_goBack h iU3 p a hReady)) hob)
  · obtain ⟨t', ht', Pt, _, e1, e2, _⟩ := withTables_pass A P ht
    obtain ⟨t'', ht'', at'⟩ := withTables_alike A a ht
    obtain rfl : t' = t'' := Option.some.inj (ht'.symm.trans ht'')
    refine ⟨t', ht', fun nm r e => ?_⟩
    rw [key nm r e]
    have hht : (seatCalls asClaim).heard t' = (seatCalls asClaim).heard t := by
      show t'.lookHeard? = t.lookHeard?
      rw [e2, e1]
      exact hh
    exact runSame_through hU hO (stay t')
      (join_runSame' (seatCalls asClaim) hA Pt hht _ (callerKeys_alike h iU3 p at'))

/-- **The kept test at "join" passes.** -/
theorem join_formsIn_pass_seat
    (hin : formsIn (readersOfLink (holesAt X mH m l) l) own b "join" s = true) :
    formsIn (readersOfLink (holesAt X mH m l) l) own b "join" s' = true := by
  refine k3_formsIn_fwd P (readersOfLink (holesAt X mH m l) l) own b "join"
    (join_fwd_seat X mH m hm l b h iU3 lk piece p P A a K hReady hBj hA hh hob)
    (fun R hR y hy => ?_) hin
  obtain ⟨run, hf, hU⟩ := K.join
  have low : ∀ u : S, ∀ R', readerOf (statesOfLink l) b "join" u = some R' → R'.late = [] := by
    intro u R' hR'
    obtain ⟨nm, r, cl, t, F1, G1, hfd, hr, hF1, hG1, _, rfl⟩ := reader_test hR'
    rw [hf] at hfd
    obtain rfl : run = r := congrArg Prod.snd (Option.some.inj hfd)
    obtain ⟨F2, g, e1, _, e3⟩ := k6_join _ 0 u (cl, t) (hU 0 u (cl, t) hr)
    obtain rfl : F1 = F2 := Option.some.inj (hF1.symm.trans e1)
    have e3' : t = u.putFork (F1.paid g.owedJoin) := e3
    rw [e3', fork_putFork u F1 _ hF1] at hG1
    obtain rfl := Option.some.inj hG1
    exact lateOf_same F1 (F1.paid g.owedJoin) rfl
  rcases forms_cases (Desc.K9.phAt X m) (holesAt X mH m l) l b (holesAt_k6 X mH m hm l)
    (by decide) hR with h0 | ⟨_, t, _, hRt⟩
  · rw [low s R h0] at hy
    exact absurd hy List.not_mem_nil
  · rw [low t R hRt] at hy
    exact absurd hy List.not_mem_nil

end Join

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.runSame_through
#print axioms VerifiableInference.OnPublicFiles.runBack_through
#print axioms VerifiableInference.OnPublicFiles.letters_goBack
#print axioms VerifiableInference.OnPublicFiles.k6_runBack
#print axioms VerifiableInference.OnPublicFiles.callerKeys_back
#print axioms VerifiableInference.OnPublicFiles.join_back
#print axioms VerifiableInference.OnPublicFiles.own_fwd_seat
#print axioms VerifiableInference.OnPublicFiles.own_formsIn_pass_seat
#print axioms VerifiableInference.OnPublicFiles.join_fwd_seat
#print axioms VerifiableInference.OnPublicFiles.join_formsIn_pass_seat
