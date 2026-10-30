-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/ExactOfRows.lean: kind K14: IMPLICATIONS: FROM THE SHARED
SENDING's LAW AT THE ROWS (Spec.rowsExact, Johnson/SendSim/At/Sim.lean: what the two moves show has
one distribution at any two data) TO THE FOUR STATEMENTS OF Honest/K14/ExactStated.lean at this
kind's parts. THE PREMISE IS NOT PROVED IN THIS FILE. No property is claimed.

  shown_law       over the part's own coins, what the part shows has the distribution of what the
                  shared sending's two moves show, over as many coins, AT ANY DATA: at a job whose
                  shapes pass the test, a sub-protocol that declares the part's messages, a stand
                  with SameData, challenges that the two rounds can sample and POSITIONS WITHIN THE
                  COUNT
  tells_law       what sendingSim tells, coin by coin: the two moves at no data: where the shapes
                  pass the test and the challenges fit
  shownOneLaw_of_rows   Spec.rowsExact → ShownOneLaw
  exactAtSending_of_rows   Spec.rowsExact → ExactAtSending
  sameData_u, sameData_omega   pointApart gives SameData at the two jobs
  fit_u, fit_omega   the test on both sendings' shapes gives the test on each, at any number of the
                  round "LIN point"
  exactAtU_of_rows, exactAtOmega_of_rows   Spec.rowsExact → ExactAtU, ExactAtOmega
  shown_averaged  THE AVERAGING LINE: the stand sampled first, by any distribution; then the coins:
                  under shown_law's premises, SameData at every cause

How. The tie (shows_tie, Honest/K14/TieShown.lean) turns what the part shows into the shared
sending's shownR at the same coins, number by number; recount_unif (Honest/K14/TieCoins.lean)
carries the uniform coins; the premise exchanges the data; play_send (Johnson/SendSim/At/Shows.lean)
says what the simulator tells; draws_send (Johnson/SendSim/At/SeatedAt.lean) reads off the frame's
test on challenges that the first challenge holds just the seeds and that no factor is 0.
WITH EVERY ONE OF THEM. What a part shows is not all that a run shows of its messages: the proximity
tests behind the sendings, and of o_omega each request's own test, are handed these messages' coins;
nothing is said here of what they show · not to be quoted without the owner's sentence (the field
fresh) · the challenges and the positions are fixed before the coins are sampled · the simulator's
rows are laid at no data: they meet none of the constraints that later sub-protocols test on these
messages · one request: that the positions of all requests of a batch together are within the count
is said by nothing here.
-/
import Johnson.Desc.ProofFile.Honest.K14.TieShown
import Johnson.Desc.ProofFile.Honest.K14.ExactStated
import Johnson.SendSim.At.Shows
import Johnson.SendSim.At.SeatedAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- An instance of the library (Cb.instNonemptyPGD, Cb/Obj/LdObjectReqStd.lean) is offered to every
-- search for Nonempty and sends it after a field that nothing determines; it is struck here.
attribute [-instance] Cb.instNonemptyPGD

namespace ProofFile.Honest.K14
open OnBytes.Slice (GE GF)
open ProofFile.Honest.Small (ExactMember)
open ProofFile.Honest.K1 (dueR)
open OnBytes.SendSim.At (Spec.rowsExact shownR budAt sendSim play_send draws_send)

variable {S Cl X Pb W : Type}

/-- **What the part shows has the distribution of what the shared sending's two moves show at any
data**: at a job whose shapes pass the test, a sub-protocol that declares the part's messages,
challenges that the two rounds can sample and POSITIONS WITHIN THE COUNT, at a stand with SameData.
The premise H is not proved here. -/
theorem shown_law (H : Spec.rowsExact) (J : SendJob) (hfit : sendShapeFits J = true)
    (wit : W → Ask) (φ : Face Empty W Pb) (σ : Side S Cl Empty W X Pb) (sim : Sim Pb)
    (hd : SendDeclared σ.block J) (m : Mid W X) (hsame : SameData J m.st.heard)
    (ds : List Fmt.Drawn) (hds : drawsFit (VerifiableInference.Desc.K1.rounds J.Q) ds = true)
    (asks : List (List (List Nat))) (hb : budAt J.Q asks)
    (data : Nat → Nat → Nat → Option (GF ⊕ GE)) :
    (Prob.unif (Cs (sendingPart J).takes)).map
        (fun c => σ.shows φ (sendingMember σ J wit sim) (c, (), ()) m ds asks) =
      (Prob.unif (Cs (dueR J.Q (rideBySort J)))).map
        fun c => some (shownR J.Q 0 (rideBySort J) data ds asks c) := by
  obtain ⟨hseeds, hβ⟩ := draws_send J.Q hds
  obtain ⟨x₀, x₁, rfl, -, -⟩ := drawsFit_two
    (d₀ := { entry := VerifiableInference.Desc.K1.seedEntry J.Q })
    (d₁ := { entry := VerifiableInference.Desc.K1.answerEntry J.Q }) hds
  have e : (fun c => σ.shows φ (sendingMember σ J wit sim) (c, (), ()) m [x₀, x₁] asks) =
      (fun c => some (shownR J.Q 0 (rideBySort J)
        (vecData J { input := wit m.st.input, heard := m.st.heard, own := () }) [x₀, x₁] asks
        c)) ∘ recount (due_tie J hfit) :=
    funext fun c => shows_tie J hfit wit φ σ sim hd m hsame x₀ x₁ asks c
  rw [e]
  refine (PMF.map_comp (recount (due_tie J hfit)) _ _).symm.trans ?_
  rw [recount_unif]
  have h := congrArg (PMF.map some) (H J.Q 0 (rideBySort J)
    (vecData J { input := wit m.st.input, heard := m.st.heard, own := () }) data [x₀, x₁] asks
    (fits_tie J hfit) hseeds hβ hb)
  rw [PMF.map_comp, PMF.map_comp] at h
  exact h

/-- **What the simulator tells, coin by coin**: the two moves at no data: where the shapes pass the
test and the challenges fit. -/
theorem tells_law (J : SendJob) (hfit : sendShapeFits J = true) (a : Addr) (pb : Pb)
    (front : Before) (ds : List Fmt.Drawn)
    (hds : drawsFit (VerifiableInference.Desc.K1.rounds J.Q) ds = true)
    (asks : List (List (List Nat))) (c : Cs (dueR J.Q (rideBySort J))) :
    (sendingSim J a : Sim Pb).tell pb front ds asks c =
      some (shownR J.Q 0 (rideBySort J) (fun _ _ _ => none) ds asks c) := by
  obtain ⟨hseeds, -⟩ := draws_send J.Q hds
  obtain ⟨x₀, x₁, rfl, -, -⟩ := drawsFit_two
    (d₀ := { entry := VerifiableInference.Desc.K1.seedEntry J.Q })
    (d₁ := { entry := VerifiableInference.Desc.K1.answerEntry J.Q }) hds
  show (play ((ProofFile.Honest.K1.sendPart (V := Empty)
    (OnBytes.SendSim.At.bare J.Q 0 (rideBySort J))).steps "" a
    (OnBytes.SendSim.At.roundsOf J.Q) none (c, (), ())) [x₀, x₁] []
    OnBytes.SendSim.At.standIn).toOption.map (fun y => shownOf y.1 asks) = _
  rw [OnBytes.SendSim.At.roundsOf_eq]
  exact play_send (OnBytes.SendSim.At.bare J.Q 0 (rideBySort J)) _ _ _ _ _ c
    OnBytes.SendSim.At.standIn x₀ x₁ asks rfl rfl (fits_tie J hfit) hseeds

/-- Spec.rowsExact → ShownOneLaw. The premise is not proved here. -/
theorem shownOneLaw_of_rows (H : Spec.rowsExact) : ShownOneLaw := by
  intro S Cl X Pb W J hfit wit φ σ sim _ hd m m' ds asks hs hs' hds hb
  rw [shown_law H J hfit wit φ σ sim hd m hs ds hds asks hb (fun _ _ _ => none),
    shown_law H J hfit wit φ σ sim hd m' hs' ds hds asks hb (fun _ _ _ => none)]

/-- Spec.rowsExact → ExactAtSending. The premise is not proved here. -/
theorem exactAtSending_of_rows (H : Spec.rowsExact) : ExactAtSending := by
  intro S Cl X Pb W J hfit wit φ σ hrow hr hd chain firstTree On hOn bud hbud u hu ca m front ds
    asks hon _ hds hb _ _
  rw [members_send σ _ _ hrow, List.mem_singleton] at hu
  subst hu
  have hds' : drawsFit (VerifiableInference.Desc.K1.rounds J.Q) ds = true := by
    obtain ⟨d₀, d₁, os, h1, h2, -⟩ := hd.rounds
    have e : ((σ.block.rounds.zip σ.block.oracles).take 2).map (·.1) = σ.block.rounds := by
      rw [h1, h2]
      rfl
    rw [← hr, ← e]
    exact hds
  have hlaw := shown_law H J hfit wit φ σ (sendingSim J ⟨σ.block.place, 0⟩) hd m
    (hOn _ ca m front hon) ds hds' asks (hbud ds asks hb) (fun _ _ _ => none)
  have e1 : (fun c : Cs (sendingPart J).takes × Unit =>
      σ.shows φ (sendingMember σ J wit (sendingSim J ⟨σ.block.place, 0⟩)) (c.1, c.2, ca) m ds
        asks) =
      (fun c => σ.shows φ (sendingMember σ J wit (sendingSim J ⟨σ.block.place, 0⟩)) (c, (), ()) m
        ds asks) ∘ Prod.fst := rfl
  show (Prob.unif (Cs (sendingPart J).takes × Unit)).map (fun c =>
      σ.shows φ (sendingMember σ J wit (sendingSim J ⟨σ.block.place, 0⟩)) (c.1, c.2, ca) m ds
        asks) =
    (Prob.unif (Cs (dueR J.Q (rideBySort J)))).map fun c =>
      (sendingSim J ⟨σ.block.place, 0⟩ : Sim Pb).tell (φ.pub m.st.input) front ds asks c
  rw [e1]
  refine ((PMF.map_comp Prod.fst _ _).symm.trans
    (congrArg (PMF.map _) Prob.map_fst_unif)).trans (hlaw.trans ?_)
  exact congrArg (fun f => PMF.map f (Prob.unif (Cs (dueR J.Q (rideBySort J))))) (funext fun c =>
    (tells_law J hfit ⟨σ.block.place, 0⟩ (φ.pub m.st.input) front ds hds' asks c).symm)

/-! ## The two sendings -/

/-- One challenge more behind a list does not turn what is read at a number other than its
length. -/
theorem drop_take_snoc {α : Type} (h : List α) (x : α) (i : Nat) (hi : i ≠ h.length) :
    ((h ++ [x]).drop i).take 1 = (h.drop i).take 1 := by
  rcases Nat.lt_or_gt_of_ne hi with hlt | hgt
  · rw [List.drop_append_of_le_length (Nat.le_of_lt hlt),
      List.take_append_of_le_length (by rw [List.length_drop]; omega)]
  · rw [List.drop_eq_nil_of_le (by rw [List.length_append, List.length_singleton]; omega),
      List.drop_eq_nil_of_le (by omega)]

/-- pointApart gives SameData at "send o_u". -/
theorem sameData_u (A : SendPub) (h : List Fmt.Drawn) (hp : pointApart A h) :
    SameData (jobU A) h := by
  intro a x₀ k
  show Desc.K14.Honest.uAtE A.P.S (elems (((h ++ [x₀]).drop A.atPoint).take 1)) a.rows =
    Desc.K14.Honest.uAtE A.P.S (elems ((h.drop A.atPoint).take 1)) a.rows
  rw [drop_take_snoc h x₀ A.atPoint hp]

/-- pointApart gives SameData at "send o_omega". -/
theorem sameData_omega (A : SendPub) (h : List Fmt.Drawn) (hp : pointApart A h) :
    SameData (jobOmega A) h := by
  intro a x₀ k
  show Desc.K14.Honest.omegaAtE A.P.S (elems (((h ++ [x₀]).drop A.atPoint).take 1)) a.rows =
    Desc.K14.Honest.omegaAtE A.P.S (elems ((h.drop A.atPoint).take 1)) a.rows
  rw [drop_take_snoc h x₀ A.atPoint hp]

/-- The test on both sendings' shapes gives the test on each, at any number of "LIN point": the
test reads the parameters and the sorts alone. -/
theorem fit_u (A : SendPub) (hfit : sendingsFit A.P = true) : sendShapeFits (jobU A) = true := by
  have e : sendShapeFits (jobU A) = sendShapeFits (jobU ⟨A.P, 0⟩) := by
    unfold sendShapeFits
    rfl
  unfold sendingsFit at hfit
  simp only [Bool.and_eq_true] at hfit
  rw [e]
  exact hfit.1.1.1.2

/-- The like at "send o_omega". -/
theorem fit_omega (A : SendPub) (hfit : sendingsFit A.P = true) :
    sendShapeFits (jobOmega A) = true := by
  have e : sendShapeFits (jobOmega A) = sendShapeFits (jobOmega ⟨A.P, 0⟩) := by
    unfold sendShapeFits
    rfl
  unfold sendingsFit at hfit
  simp only [Bool.and_eq_true] at hfit
  rw [e]
  exact hfit.1.1.2

/-- Spec.rowsExact → ExactAtU. The premise is not proved here. -/
theorem exactAtU_of_rows (H : Spec.rowsExact) : ExactAtU :=
  fun S Cl X Pb W₀ Rc Ky A hfit wit φ σ hrow hr hd chain firstTree On hOn bud hbud =>
    exactAtSending_of_rows H S Cl X Pb (Common W₀ Rc Ky) (jobU A) (fit_u A hfit) wit φ σ hrow hr hd
      chain firstTree On (fun u ca m front h => sameData_u A _ (hOn u ca m front h)) bud hbud

/-- Spec.rowsExact → ExactAtOmega. The premise is not proved here. -/
theorem exactAtOmega_of_rows (H : Spec.rowsExact) : ExactAtOmega :=
  fun S Cl X Pb W₀ Rc Ky A hfit wit φ σ hrow hr hd chain firstTree On hOn bud hbud =>
    exactAtSending_of_rows H S Cl X Pb (Common W₀ Rc Ky) (jobOmega A) (fit_omega A hfit) wit φ σ
      hrow hr hd chain firstTree On (fun u ca m front h => sameData_omega A _ (hOn u ca m front h))
      bud hbud

/-! ## From every fixed stand to a distribution over stands -/

/-- **THE AVERAGING LINE.** Let the stand in front of the part (so the index, the index committer's
coins and the key) be sampled FIRST, by any distribution p over any type of causes, through any
function stand: so a key that is MADE of the committer's coins is one case. THE CHALLENGES, THE
POSITIONS, THE JOB AND THE SIDE ARE ONE AT ALL CAUSES: they are fixed before the stand is sampled;
where they hang on the cause this line says nothing. ASKED: at a job whose shapes pass the test, a
sub-protocol that declares the part's messages, challenges that the two rounds can sample and
POSITIONS WITHIN THE COUNT; SameData at every cause. Then the part's own coins are sampled. The pair
(cause, what the part shows) has the distribution in which the second is what the shared sending's
two moves show at no data, over coins of their own: it does not hang on the cause. THIS IS THE FORM
IN WHICH THE LAW AT EVERY FIXED STAND MAY BE AVERAGED. IN EVERY CASE THE INNER DISTRIBUTION RANGES
OVER THE PART's OWN COINS ALONE: the committer's coins enter through the cause, and in no other way.
THE UNSAFE FORM IS ANOTHER, AND DOES NOT FOLLOW: a law in which the committer's coins are sampled in
the place of the part's own, under a key that is a free variable. A case of this line in which the
key is held fixed while the committer's coins vary speaks of stands that no run reaches: there the
key is not made of the coins. The premise H is not proved here. -/
theorem shown_averaged (H : Spec.rowsExact) {ι : Type} (p : PMF ι) (J : SendJob)
    (hfit : sendShapeFits J = true) (wit : W → Ask) (φ : Face Empty W Pb)
    (σ : Side S Cl Empty W X Pb) (sim : Sim Pb) (hd : SendDeclared σ.block J)
    (stand : ι → Mid W X) (hsame : ∀ i, SameData J (stand i).st.heard) (ds : List Fmt.Drawn)
    (hds : drawsFit (VerifiableInference.Desc.K1.rounds J.Q) ds = true)
    (asks : List (List (List Nat))) (hb : budAt J.Q asks) :
    (p.bind fun i => (Prob.unif (Cs (sendingPart J).takes)).map fun c =>
        (i, σ.shows φ (sendingMember σ J wit sim) (c, (), ()) (stand i) ds asks)) =
      p.bind fun i => (Prob.unif (Cs (dueR J.Q (rideBySort J)))).map fun c =>
        (i, some (shownR J.Q 0 (rideBySort J) (fun _ _ _ => none) ds asks c)) := by
  refine congrArg _ (funext fun i => ?_)
  have h := congrArg (PMF.map (Prod.mk i))
    (shown_law H J hfit wit φ σ sim hd (stand i) (hsame i) ds hds asks hb (fun _ _ _ => none))
  rw [PMF.map_comp, PMF.map_comp] at h
  exact h

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.shown_law
#print axioms ProofFile.Honest.K14.tells_law
#print axioms ProofFile.Honest.K14.shownOneLaw_of_rows
#print axioms ProofFile.Honest.K14.exactAtSending_of_rows
#print axioms ProofFile.Honest.K14.drop_take_snoc
#print axioms ProofFile.Honest.K14.sameData_u
#print axioms ProofFile.Honest.K14.sameData_omega
#print axioms ProofFile.Honest.K14.fit_u
#print axioms ProofFile.Honest.K14.fit_omega
#print axioms ProofFile.Honest.K14.exactAtU_of_rows
#print axioms ProofFile.Honest.K14.exactAtOmega_of_rows
#print axioms ProofFile.Honest.K14.shown_averaged
