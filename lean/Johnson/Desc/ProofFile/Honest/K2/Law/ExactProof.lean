-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ExactProof.lean: the kind "the code switch" (K2): THE STATEMENT
`SwitchExact` (Honest/K2/Exact.lean), PROVED: AN IMPLICATION FROM ITS NAMED PREMISES. Definitions;
statements with their proofs.

WHAT IS PROVED IS THE IMPLICATION. ITS PREMISES ARE NOT SHOWN HERE: among them stands a law on the
sender (`SendSameLaw`), which Honest/K2/Law/AtCore.lean shows of the core's sender over another
writer's theorem, and public premises that are shown at no plan. Of the lot's own closing the
premise `returns` is had where `closingOk` says yes (`returnsLaw`, Honest/K2/Law/SegmentAlike.lean).
The premises `fits` and `oneRow` are spent to open the sender's law alone. ALL PREMISES HOLD
TOGETHER AT THREE MADE-UP SWITCHES ALONE (Honest/K2/Law/TinyWhole.lean, MidAsks.lean,
WideAsks.lean). THESE THREE ARE NO FILES OF THIS LIBRARY: A
READER OF THE LIBRARY ALONE CANNOT OPEN THEM, AND HAS THAT SENTENCE ON THEIR AUTHORS' WORD.
THE STATEMENT IS NEVER TO BE QUOTED WITHOUT THE ONE IN Honest/K2/Fresh.lean. It is none of the
library's goals. Of the premises that `ExactOf` lays in front of its equation the proof reads two
alone: that the challenges fit the rounds (`drawsFit`) and the bud; the others are not read.

  `afterSend`       what is made of what a sending shows: the two public tests on the sizes, then
                    the frame's two tests and the two rounds as shown (`frameOf`)
  `coreShows_error`, `coreShows_ok`   `coreShows` where the data is refused: the one symbol; where
                    it is there: `afterSend` of `senderShows`
  `core_law`        under the end of the sender's law at the given challenge and positions (hs):
                    `coreShows` has one law at any two data; on the left the coins stand beside an
                    empty list of spent runs. That seeds and positions fit is spent in `switchExact`
  `headD_get`       a tool: a list's first member, or the empty list, said in two ways
  `seatedPart`      the kind's part as its half seats it; `switch_members`: a side with the kind's
                    row has that one member
  `exact_at`        the equation, at the part and the simulator written out
  `draws_two`       two rounds can draw just two challenges; the first fits the first
  `switchExact`     THE IMPLICATION

Limits. As above. Nothing here says what the statement would mean for any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchShows
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Oracle Block)
open VerifiableInference.Desc.K2.Honest (Sizes)

/-- What is made of what a sending shows. -/
def afterSend (Z : Sizes) (d₁ d₂ : Fmt.DeclaredRound) (o₁ o₂ : List Oracle)
    (y : Option (List ((Nat × Nat) × List (Nat × List UInt64)) × List Cb.Gl.E)) :
    Option (List Shown) :=
  if !Z.serves then none else
  if !Z.roomy then none else y.bind (frameOf d₁ d₂ o₁ o₂)

section
variable (Sd : Sender) (Z : Sizes) (others : Array OnBytes.OracleNotice) (k : Nat)
  (d₁ d₂ : Fmt.DeclaredRound) (o₁ o₂ : List Oracle) (x₁ : Fmt.Drawn) (asks : List (List (List Nat)))

/-- Where the data is refused the two rounds show the one symbol, at every coin. -/
theorem coreShows_error (e : String)
    (c : Cs (sendingDue Z.codes (switchSent Z others) (switchFresh Z others k))) :
    coreShows Sd Z others k d₁ d₂ o₁ o₂ x₁ asks (.error e) c = none := by
  rw [coreShows_eq]
  by_cases c₁ : (!Z.serves) = true
  · rw [if_pos c₁]
  rw [if_neg c₁]
  by_cases c₂ : (!Z.roomy) = true
  · rw [if_pos c₂]
  rw [if_neg c₂]
  rfl

/-- Where the data is there the two rounds show `afterSend` of `senderShows`, at every coin. -/
theorem coreShows_ok (D : Nat → Nat → Nat → Cb.Gl.E)
    (c : Cs (sendingDue Z.codes (switchSent Z others) (switchFresh Z others k))) :
    coreShows Sd Z others k d₁ d₂ o₁ o₂ x₁ asks (.ok D) c =
      afterSend Z d₁ d₂ o₁ o₂
        (senderShows Sd Z.codes (switchSent Z others) (switchFresh Z others k) D x₁.elems
          ((asks[0]?).getD []) c) := by
  rw [coreShows_eq]
  rfl

/-- hs IS A PREMISE: the end of the sender's law at x₁ and asks. **`coreShows` has one law at any
two data**, over uniform coins of the sending; the left side's coins are paired with `CsAll []`: no
spent run. -/
theorem core_law
    (hs : ∀ data data' : Nat → Nat → Nat → Cb.Gl.E,
      (Prob.unif (Cs (sendingDue Z.codes (switchSent Z others) (switchFresh Z others k)))).map
          (senderShows Sd Z.codes (switchSent Z others) (switchFresh Z others k) data x₁.elems
            ((asks[0]?).getD [])) =
        (Prob.unif (Cs (sendingDue Z.codes (switchSent Z others) (switchFresh Z others k)))).map
          (senderShows Sd Z.codes (switchSent Z others) (switchFresh Z others k) data' x₁.elems
            ((asks[0]?).getD [])))
    (D D' : Nat → Nat → Nat → Cb.Gl.E) :
    (Prob.unif (Cs (sendingDue Z.codes (switchSent Z others) (switchFresh Z others k)) ×
        CsAll ([] : List (String × Due)))).map
        (fun c => coreShows Sd Z others k d₁ d₂ o₁ o₂ x₁ asks (.ok D) c.1) =
      (Prob.unif (Cs (sendingDue Z.codes (switchSent Z others) (switchFresh Z others k)))).map
        (fun c => coreShows Sd Z others k d₁ d₂ o₁ o₂ x₁ asks (.ok D') c) := by
  have e₁ : (fun c : Cs (sendingDue Z.codes (switchSent Z others) (switchFresh Z others k)) ×
        CsAll ([] : List (String × Due)) =>
        coreShows Sd Z others k d₁ d₂ o₁ o₂ x₁ asks (.ok D) c.1) =
      afterSend Z d₁ d₂ o₁ o₂ ∘
        (senderShows Sd Z.codes (switchSent Z others) (switchFresh Z others k) D x₁.elems
          ((asks[0]?).getD [])) ∘ Prod.fst :=
    funext fun c => coreShows_ok Sd Z others k d₁ d₂ o₁ o₂ x₁ asks D c.1
  have e₂ : (fun c : Cs (sendingDue Z.codes (switchSent Z others) (switchFresh Z others k)) =>
        coreShows Sd Z others k d₁ d₂ o₁ o₂ x₁ asks (.ok D') c) =
      afterSend Z d₁ d₂ o₁ o₂ ∘
        (senderShows Sd Z.codes (switchSent Z others) (switchFresh Z others k) D' x₁.elems
          ((asks[0]?).getD [])) :=
    funext fun c => coreShows_ok Sd Z others k d₁ d₂ o₁ o₂ x₁ asks D' c
  rw [e₁, e₂, ← PMF.map_comp, ← PMF.map_comp, ← PMF.map_comp, Prob.map_fst_unif, hs D D']

end

/-- A tool: a list's first member, or the empty list, said in two ways. -/
theorem headD_get {α : Type} (l : List (List α)) : l.headD [] = (l[0]?).getD [] := by
  cases l <;> rfl

variable {S Cl W₀ Rc Xi Tr X : Type}

/-- The kind's part as its half seats it. -/
abbrev seatedPart (Sd : Sender) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) :
    Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  (switchPart Sd p.sizes p.others p.foldVars p.carries).lift (fun _ => ())
    (switchWit D readers closing p) (fun _ => ()) fun x _ => x

/-- A side with the kind's row has one member. -/
theorem switch_members (Sd : Sender) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (ok : Xi → Bool) (r₁ r₂ : Fmt.DeclaredRound × List Oracle)
    (b : Block S Cl) (fall : S → List Fmt.Drawn → Option String)
    (hb : b.rounds.zip b.oracles = [r₁, r₂]) :
    (⟨b, switchRow (X := X) Sd D readers closing p ok [r₁, r₂], fall⟩ :
        Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi).members =
      [⟨0, [r₁, r₂], seatedPart Sd D readers closing p, switchSim Sd p ok [r₁, r₂]⟩] := by
  unfold Side.members
  dsimp only
  rw [hb]
  rfl

/-- **The equation, at the part and the simulator written out.** -/
theorem exact_at (Sd : Sender) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (ok : Xi → Bool) (d₁ d₂ : Fmt.DeclaredRound)
    (o₁ o₂ : List Oracle) (nm : String) (ad : Addr) (v : Option (Local W₀ Rc Xi Tr))
    (ca : CsAll p.carries) (m : Mid (Local W₀ Rc Xi Tr) X) (front : Before) (x₁ x₂ : Fmt.Drawn)
    (asks : List (List (List Nat)))
    (hlaw : ∀ data data' : Nat → Nat → Nat → Cb.Gl.E,
      (Prob.unif (Cs (sendingDue p.sizes.codes (switchSent p.sizes p.others)
          (switchFresh p.sizes p.others p.foldVars)))).map
          (senderShows Sd p.sizes.codes (switchSent p.sizes p.others)
            (switchFresh p.sizes p.others p.foldVars) data x₁.elems ((asks[0]?).getD [])) =
        (Prob.unif (Cs (sendingDue p.sizes.codes (switchSent p.sizes p.others)
          (switchFresh p.sizes p.others p.foldVars)))).map
          (senderShows Sd p.sizes.codes (switchSent p.sizes p.others)
            (switchFresh p.sizes p.others p.foldVars) data' x₁.elems ((asks[0]?).getD [])))
    (hret : (closing p (D m.st.input.x) (readers m.st.input)
      (m.st.heard.take (m.st.heard.length - 0))
      (Stretch.carried p.carries ca)).toOption.isSome = ok m.st.input.x) :
    (Prob.unif (Cs (sendingDue p.sizes.codes (switchSent p.sizes p.others)
        (switchFresh p.sizes p.others p.foldVars)) × CsAll ([] : List (String × Due)))).map
        (fun c => (play ((seatedPart (X := X) Sd D readers closing p).steps nm ad
          [(d₁, o₁), (d₂, o₂)] v (c.1, c.2, ca)) [x₁, x₂] [] m).toOption.map
            fun y => shownOf y.1 asks) =
      (Prob.unif (Cs (sendingDue p.sizes.codes (switchSent p.sizes p.others)
        (switchFresh p.sizes p.others p.foldVars)))).map
        fun c => (switchSim Sd p ok [(d₁, o₁), (d₂, o₂)]).tell m.st.input.x front [x₁, x₂] asks
          c := by
  have eL : (fun c : Cs (sendingDue p.sizes.codes (switchSent p.sizes p.others)
        (switchFresh p.sizes p.others p.foldVars)) × CsAll ([] : List (String × Due)) =>
        (play ((seatedPart (X := X) Sd D readers closing p).steps nm ad
          [(d₁, o₁), (d₂, o₂)] v (c.1, c.2, ca)) [x₁, x₂] [] m).toOption.map
            fun y => shownOf y.1 asks) =
      fun c => coreShows Sd p.sizes p.others p.foldVars d₁ d₂ o₁ o₂ x₁ asks
        (switchRowsAt p.sizes p.carries ca
          (m.st.narrow (switchWit D readers closing p) fun _ => ()) 0) c.1 :=
    funext fun c => lifted_shows Sd p.sizes p.others p.foldVars p.carries (fun _ => ())
      (switchWit D readers closing p) (fun _ => ()) (fun x _ => x) nm ad d₁ d₂ o₁ o₂ v c.1 ca x₁ x₂
      m asks
  have eR : (fun c : Cs (sendingDue p.sizes.codes (switchSent p.sizes p.others)
        (switchFresh p.sizes p.others p.foldVars)) =>
        (switchSim Sd p ok [(d₁, o₁), (d₂, o₂)]).tell m.st.input.x front [x₁, x₂] asks c) =
      fun c => coreShows Sd p.sizes p.others p.foldVars d₁ d₂ o₁ o₂ x₁ asks
        (switchRowsAt p.sizes [] () ⟨simAsk (ok m.st.input.x), [], ()⟩ 0) c :=
    funext fun c => sim_tells Sd p ok d₁ d₂ o₁ o₂ m.st.input.x front x₁ x₂ asks c
  refine (congrArg (fun f => PMF.map f (Prob.unif _)) eL).trans
    (Eq.trans ?_ (congrArg (fun f => PMF.map f (Prob.unif _)) eR).symm)
  beta_reduce
  cases hc : closing p (D m.st.input.x) (readers m.st.input)
      (m.st.heard.take (m.st.heard.length - 0)) (Stretch.carried p.carries ca) with
  | error e =>
    rw [hc] at hret
    have hok : ok m.st.input.x = false := hret.symm
    have h₁ : switchRowsAt p.sizes p.carries ca
        (m.st.narrow (switchWit D readers closing p) fun _ => ()) 0 = .error e := by
      show (closing p (D m.st.input.x) (readers m.st.input)
        (m.st.heard.take (m.st.heard.length - 0)) (Stretch.carried p.carries ca)).map _ = _
      rw [hc]
      rfl
    have h₂ : switchRowsAt p.sizes [] () ⟨simAsk (ok m.st.input.x), [], ()⟩ 0 =
        .error "the filling does not fit the place" := by
      rw [hok]
      rfl
    rw [h₁, h₂]
    simp only [coreShows_error]
    exact (PMF.map_const _ none).trans (PMF.map_const _ none).symm
  | ok Wl =>
    rw [hc] at hret
    have hok : ok m.st.input.x = true := hret.symm
    have h₁ : switchRowsAt p.sizes p.carries ca
        (m.st.narrow (switchWit D readers closing p) fun _ => ()) 0 =
        .ok (VerifiableInference.Desc.K2.Honest.mainRows p.sizes Wl
          (switchWit D readers closing p m.st.input).own) := by
      show (closing p (D m.st.input.x) (readers m.st.input)
        (m.st.heard.take (m.st.heard.length - 0)) (Stretch.carried p.carries ca)).map _ = _
      rw [hc]
      rfl
    have h₂ : switchRowsAt p.sizes [] () ⟨simAsk (ok m.st.input.x), [], ()⟩ 0 =
        .ok (VerifiableInference.Desc.K2.Honest.mainRows p.sizes zeroLeft
          (simAsk true).own) := by
      rw [hok]
      rfl
    rw [h₁, h₂]
    exact core_law Sd p.sizes p.others p.foldVars d₁ d₂ o₁ o₂ x₁ asks hlaw _ _

/-- Two rounds can draw just two challenges; the first fits the first. -/
theorem draws_two (d₁ d₂ : Fmt.DeclaredRound) (ds : List Fmt.Drawn)
    (hd : drawsFit [d₁, d₂] ds = true) : ∃ x₁ x₂, ds = [x₁, x₂] ∧ drawFit d₁ x₁ = true := by
  rcases ds with _ | ⟨x₁, _ | ⟨x₂, _ | ⟨x₃, r⟩⟩⟩
  · simp [drawsFit] at hd
  · simp [drawsFit] at hd
  · refine ⟨x₁, x₂, rfl, ?_⟩
    simp [drawsFit] at hd
    exact hd.1
  · simp [drawsFit] at hd

/-- **THE IMPLICATION.** -/
theorem switchExact (Sd : Sender) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (ok : Xi → Bool)
    (rounds : List (Fmt.DeclaredRound × List Oracle)) (bs : List (Block S Cl)) (fs : List (Fall S))
    (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) (chain firstTree : Nat) :
    SwitchExact Sd D readers closing p ok rounds bs fs σ chain firstTree := by
  intro h u hu ca m front ds asks _ _ hd hbud _ _
  obtain ⟨⟨d₁, o₁⟩, ⟨d₂, o₂⟩, rfl⟩ := List.length_eq_two.1 h.two
  obtain ⟨b, -, rfl⟩ := Option.map_eq_some_iff.1 h.seated
  rw [switch_members Sd D readers closing p ok (d₁, o₁) (d₂, o₂) b _ h.blocks] at hu
  obtain rfl := List.mem_singleton.1 hu
  obtain ⟨x₁, x₂, rfl, hx₁⟩ := draws_two d₁ d₂ ds hd
  have hseeds : seedsFit p.sizes.codes (switchSent p.sizes p.others) x₁.elems :=
    h.seeds (d₁, o₁) rfl x₁ hx₁
  have hasks : asksWithin p.sizes.codes (switchSent p.sizes p.others) ((asks[0]?).getD []) := by
    have h0 : asksWithin p.sizes.codes (switchSent p.sizes p.others) (asks.headD []) := hbud
    rwa [headD_get] at h0
  exact exact_at Sd D readers closing p ok d₁ d₂ o₁ o₂ b.name ⟨b.place, 0⟩ (some m.st.input) ca m
    front x₁ x₂ asks
    (fun data data' => h.send h.fits h.oneRow data data' x₁.elems ((asks[0]?).getD []) hseeds
      hasks)
    (h.returns m.st.input (m.st.heard.take (m.st.heard.length - 0)) ca)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.afterSend
#print axioms ProofFile.Honest.K2.Law.coreShows_error
#print axioms ProofFile.Honest.K2.Law.coreShows_ok
#print axioms ProofFile.Honest.K2.Law.core_law
#print axioms ProofFile.Honest.K2.Law.headD_get
#print axioms ProofFile.Honest.K2.Law.seatedPart
#print axioms ProofFile.Honest.K2.Law.switch_members
#print axioms ProofFile.Honest.K2.Law.exact_at
#print axioms ProofFile.Honest.K2.Law.draws_two
#print axioms ProofFile.Honest.K2.Law.switchExact
