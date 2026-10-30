-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotStandFirst.lean: THE FIRST CHAIN's STAND: at the key file's prover, where ready returns, at every
border from 0 to 15 and at EVERY list of challenges that fits the rounds in front of it, there is a state at which the
pair stands: the thread Th (E2E/FirstHSeat.lean) with the letter walkedFirst (E2E/LotBegunFirst.lean); the run has heard
that list, at the run's own input.

  `chainSteps_member`: where a chain's rounds can be laid, so can each member's. General.
  `stands_upTo`: GENERAL IN THE THREAD AND THE LETTER: from the pair at border 0, the five debts and SaidNext at the members
    in front, no stop, no fall, and the chain's rounds laid: the pair at every border up to n, at every list that fits:
    by step_pair (E2E/KeyStandStep.lean), member by member.
  `fits_front`, **`some_list_fits`**: THE GUARD: at every border some list of challenges fits the rounds in front (the
    library's written list, Draws.ofDecl_due, Honest/Law/DrawsOfDecl.lean): "at every list that fits" is said of something.
  `LeftTo15`: what is left at the members in front of border 15: five fields: LotFirstFromLeft's at 4, 10 and 5, 11.
  `fiveTo15`: the five debts at members 0 to 14 from it, at no fall.
  `LotStandFirst`, **`lotStandFirst`**: the lot.
  `standFirst_at`: the stand up to any border n ≤ 19 AT ANY LETTER that holds at the walk's start and is carried, from the
    five debts in front at that letter: for whoever wants more in the letter (the field, say).
  `standFirst_to19`: at every border, the last (19) among them, from LeftFirst (E2E/LotFirstFromLeft.lean).
  **`standFirst_to4`**: AT THE BORDERS 0 TO 4 NOTHING IS LEFT AT THE MEMBERS: the pair stands there with no premise on any
    member (the premises on the files, FirstPublic, RangeTie, Q.Rel, no stop and «ready returns» stay).

Limits. UNDER «ready returns»: shown nowhere here. FROM BORDER 5 ON AN IMPLICATION: no member of LeftTo15 is known: the first
lookup, member 4, stands in the way. A stand is a sentence "there is": it names no state; one state for each run is
walked_unique's. RangeTie, Q.Rel, FirstPublic and "no part of the first chain stops" are premises; at the real value
the first is paid (E2E/LotEntersFirstTie.lean). No fall: the acceptance is asked at every fitting list. Nothing on
soundness, completeness, hiding or binding.
-/
import E2E.LotEntersFirstCore
import E2E.LotBegunFirst
import E2E.LotFirstFromLeft
import E2E.KeyStandStep
import E2E.NoStop
import E2E.KeyThreadFits
import Johnson.Desc.ProofFile.Honest.Law.Cut
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw
import Johnson.Desc.ProofFile.Honest.Law.DrawsOfDecl

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.Key (Xi FirstState KItem Source LaterPlaces)
open AtPublicFiles.KeyThread (rowsFirst form_behind₁ exchange_of_nil)
open AtPublicFiles.KeyFile (KeyParts In1 keyProver)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.AtFiles.Full (accepted_first)
open AtPublicFiles.Stops (NoStop chainStopAt_none)
open AtPublicFiles.KeyStandStep (step_pair)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest

section General
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- Where a chain's rounds can be laid, so can each member's. -/
theorem chainSteps_member {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {hs : List (Placed V W X)} {bs : List (Block S Cl)} {L : List (Step W X)}
    (h : chainSteps B rows look v bs hs = .ok L) {b : Nat} {blk : Block S Cl}
    (hb : bs[b]? = some blk) : ∃ l, chainSteps B rows look v [blk] hs = .ok l := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.1 hb
  have e : bs.take b ++ ([bs[b]] ++ bs.drop (b + 1)) = bs := by
    rw [List.singleton_append, ← List.drop_eq_getElem_cons hlt, List.take_append_drop]
  have h' : chainSteps B rows look v (bs.take b ++ ([bs[b]] ++ bs.drop (b + 1))) hs = .ok L := by
    rw [e]
    exact h
  rw [chainSteps_append] at h'
  obtain ⟨l₁, -, h'⟩ := exBind_ok h'
  obtain ⟨l₂, h2, -⟩ := exMap_ok h'
  rw [chainSteps_append] at h2
  obtain ⟨l, hl, -⟩ := exBind_ok h2
  exact ⟨l, hl⟩

/-- **The pair stands at every border up to n, at every list that fits**: general in the thread and the letter. -/
theorem stands_upTo (T : Thread Bk S Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String) {n N : Nat} (hfit : T.fits N = true)
    (hnN : n ≤ N) (hlen : n ≤ T.bs.length)
    (hsh : ∀ y ∈ T.bs, y.planOk = true ∧ y.shaped = true)
    (five : ∀ b, b < n → FiveAt T Said fall b) (hfall : ∀ b s ds, fall b s ds = none)
    (next : ∀ b, SaidNext T Said b) (hstop : NoStop T.hs) {k : Coins Bk} {s₀ : S} {m₀ : Mid W X}
    {E₀ : Env} (h0 : ThrS T Said 0 k s₀ m₀ E₀) {L : List (Step W X)}
    (hsteps : chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m₀.st.input) T.bs T.hs =
      .ok L) :
    ∀ b, b ≤ n → ∀ ds, drawsFit (declsTo T.bs b) ds = true →
      ∃ s m E, ThrS T Said b k s m E ∧ m.st.heard = m₀.st.heard ++ ds ∧
        m.st.input = m₀.st.input := by
  intro b
  induction b with
  | zero =>
    intro _ ds hd
    have e : ds = [] := by
      cases ds with
      | nil => rfl
      | cons _ _ => cases hd
    exact ⟨s₀, m₀, E₀, h0, by rw [e, List.append_nil], rfl⟩
  | succ b ih =>
    intro hb ds hd
    have hlt : b < T.bs.length := by omega
    have hblk : T.bs[b]? = some T.bs[b] := List.getElem?_eq_getElem hlt
    rw [declsTo_succ hblk, drawsFit_append, Bool.and_eq_true] at hd
    obtain ⟨s, m, E, hA, hh, hi⟩ := ih (by omega) _ hd.1
    obtain ⟨l, hl⟩ := chainSteps_member hsteps hblk
    have f5 := five b (by omega)
    obtain ⟨s', m', E', hA', hh', -, y, cols, hMv, rfl, -⟩ :=
      step_pair T Said fall hfit (show b < N by omega) hblk (next b) f5.1 f5.2.2.2.2 f5.2.1
        f5.2.2.1 f5.2.2.2.1 (made_next T hfit hsh b) hA hd.2 (chainStopAt_none _ hstop _ _ _)
        (by rw [hi]; exact hl) (hfall _ _ _)
    refine ⟨s', _, E', hA', ?_, ?_⟩
    · rw [hh', hh, List.append_assoc, List.take_append_drop]
    · obtain ⟨⟨l', -, hy⟩, -⟩ := hMv
      exact ((play_mid _ _ _ _ _ hy).1).trans hi

/-- Where a list fits a chain's rounds, its front fits the rounds in front of each border. -/
theorem fits_front (bs : List (Block S Cl)) {D : List Fmt.Drawn}
    (h : drawsFit (bs.flatMap (·.rounds)) D = true) (b : Nat) :
    ∃ ds, drawsFit (declsTo bs b) ds = true := by
  have e : bs.flatMap (·.rounds) = declsTo bs b ++ (bs.drop b).flatMap (·.rounds) := by
    unfold declsTo
    rw [← List.flatMap_append, List.take_append_drop]
  rw [e, drawsFit_append, Bool.and_eq_true] at h
  exact ⟨_, h.1⟩

end General

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X' Wk : Type} (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
  (K : KeyParts W₀ Rc X₀ X' Wk) (f : W₀ → Weights) (Q : LaterFill Bk W₀ Rc) (w₀ : W₀) (rc : Rc)
  (x : Xi)

/-- **What is left at the members in front of border 15.** A premise's form: no member is known. -/
structure LeftTo15 (Said : Nat → Coins Bk → Mid (In1 W₀ Rc) X' → Prop) : Prop where
  playsK3 : ∀ b ∈ [4, 10], PlaysS (Th Xs N Pl K f Q w₀ rc x) Said b
  keepsK3 : ∀ b ∈ [4, 10], ∀ blk, (Th Xs N Pl K f Q w₀ rc x).bs[b]? = some blk →
    ∀ k s m E ds y cols s', ThrS (Th Xs N Pl K f Q w₀ rc x) Said b k s m E →
      drawsFit blk.rounds ds = true → (Th Xs N Pl K f Q w₀ rc x).Stepped blk k s m E ds y cols s' →
      Q.kind₁ b s s'
  exchangeK3 : ∀ b ∈ [4, 10], ExchangeS (Th Xs N Pl K f Q w₀ rc x) Said b
  ridesK3 : ∀ b ∈ [4, 10], RidesPastS (Th Xs N Pl K f Q w₀ rc x) Said b
  exchangeLayer : ∀ b ∈ [5, 11], ExchangeS (Th Xs N Pl K f Q w₀ rc x) Said b

/-- **The first chain's stand**, border 0 to 15. -/
def LotStandFirst : Prop :=
  ∀ {Z : PublicFiles}, KeySourced Z Xs N Pl → InScope Z = true → FirstPublic (Pl := Pl) Xs N K f →
    RangeTie Xs K f w₀ → Q.Rel w₀ rc x → NoStop (keyProver K).first →
    LeftTo15 Xs N Pl K f Q w₀ rc x (walkedFirst Xs N Pl K f Q w₀ rc x) →
    ∀ (k : Coins Bk) R, ready (keyFileDescription Xs N Pl) Bk (keyProver K) w₀ rc x k = .ok R →
    ∀ b, b ≤ 15 → ∀ ds, drawsFit (declsTo (Th Xs N Pl K f Q w₀ rc x).bs b) ds = true →
      ∃ s m E, ThrS (Th Xs N Pl K f Q w₀ rc x) (walkedFirst Xs N Pl K f Q w₀ rc x) b k s m E ∧
        m.st.heard = ds ∧ m.st.input = inFirst w₀ rc x

variable {Xs N Pl K f Q w₀ rc x} {Z : PublicFiles}

/-- **THE GUARD: AT EVERY BORDER SOME LIST FITS**: so no stand below is said of no list. -/
theorem some_list_fits (hs : KeySourced Z Xs N Pl) (b : Nat) :
    ∃ ds, drawsFit (declsTo (Th Xs N Pl K f Q w₀ rc x).bs b) ds = true := by
  have hd := Draws.ofDecl_due hs.named.data_at
  unfold Draws.due at hd
  simp only [Bool.and_eq_true] at hd
  exact fits_front _ hd.1.1.1 b

/-- The five debts at the members 0 to 3: nothing is left there. -/
theorem fiveTo4 (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f) (Said : Nat → Coins Bk → Mid (In1 W₀ Rc) X' → Prop)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    ∀ b, b < 4 → FiveAt (Th Xs N Pl K f Q w₀ rc x) Said fall b := by
  have quiet := fiveQuiet_Th Xs N Pl K f Q w₀ rc x hs scope Said fall
  intro b hb
  interval_cases b
  · exact rows_idx hs scope hp Said fall
  · exact rows_msg hs scope hp Said fall
  · exact quiet 2 (by decide)
  · exact quiet 3 (by decide)

/-- The five debts at the members 0 to 14, from what is left. -/
theorem fiveTo15 (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f) (Said : Nat → Coins Bk → Mid (In1 W₀ Rc) X' → Prop)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String)
    (left : LeftTo15 Xs N Pl K f Q w₀ rc x Said) :
    ∀ b, b < 15 → FiveAt (Th Xs N Pl K f Q w₀ rc x) Said fall b := by
  have quiet := fiveQuiet_Th Xs N Pl K f Q w₀ rc x hs scope Said fall
  have layer := fourLayer_Th Xs N Pl K f Q w₀ rc x hs scope Said fall
  have acc : ∀ b, b < 19 → b ≠ 15 → AcceptedS (Th Xs N Pl K f Q w₀ rc x) Said fall b :=
    fun b hb h15 => acceptedS_of _ _ (accepted_first hs scope (Th Xs N Pl K f Q w₀ rc x) rfl
      (fun _ _ _ _ _ hbeg => ⟨_, hbeg⟩) fall hb h15
      (fitsAt_of_halved (Th Xs N Pl K f Q w₀ rc x) (halved_first scope hs.named K hp.places) b))
  have form : ∀ b, b < 19 → ∀ blk, (Th Xs N Pl K f Q w₀ rc x).bs[b]? = some blk →
      ∀ k s m E ds y cols s', ThrS (Th Xs N Pl K f Q w₀ rc x) Said b k s m E →
      (Th Xs N Pl K f Q w₀ rc x).Stepped blk k s m E ds y cols s' →
      (Th Xs N Pl K f Q w₀ rc x).Form (b + 1) k s' y.2 :=
    fun b hb blk hblk k s m E ds y cols s' hA hS =>
      form_behind₁ Xs N Pl (Fl Xs N Pl K f Q x) w₀ rc x hs scope hb hblk hA.1 hS
  intro b hb
  interval_cases b
  · exact rows_idx hs scope hp Said fall
  · exact rows_msg hs scope hp Said fall
  · exact quiet 2 (by decide)
  · exact quiet 3 (by decide)
  · exact ⟨left.playsK3 4 (by decide),
      fun blk hblk k s m E ds y cols s' hA hd hS =>
        ⟨form 4 (by decide) blk hblk k s m E ds y cols s' hA hS, trivial,
          left.keepsK3 4 (by decide) blk hblk k s m E ds y cols s' hA hd hS⟩,
      left.exchangeK3 4 (by decide), left.ridesK3 4 (by decide), acc 4 (by decide) (by decide)⟩
  · exact ⟨(layer 5 (by decide)).1, (layer 5 (by decide)).2.1, left.exchangeLayer 5 (by decide),
      (layer 5 (by decide)).2.2.1, (layer 5 (by decide)).2.2.2⟩
  · exact quiet 6 (by decide)
  · exact quiet 7 (by decide)
  · exact quiet 8 (by decide)
  · exact quiet 9 (by decide)
  · exact ⟨left.playsK3 10 (by decide),
      fun blk hblk k s m E ds y cols s' hA hd hS =>
        ⟨form 10 (by decide) blk hblk k s m E ds y cols s' hA hS, trivial,
          left.keepsK3 10 (by decide) blk hblk k s m E ds y cols s' hA hd hS⟩,
      left.exchangeK3 10 (by decide), left.ridesK3 10 (by decide),
      acc 10 (by decide) (by decide)⟩
  · exact ⟨(layer 11 (by decide)).1, (layer 11 (by decide)).2.1,
      left.exchangeLayer 11 (by decide), (layer 11 (by decide)).2.2.1,
      (layer 11 (by decide)).2.2.2⟩
  · exact quiet 12 (by decide)
  · exact quiet 13 (by decide)
  · exact five14 Xs N Pl (fillH Xs N Pl K f Q x) w₀ rc x hs scope (readsL_fillH Xs N Pl K f Q x)
      Said fall

/-- **The stand up to a border n ≤ 19, AT ANY LETTER** that holds at the walk's start and is carried, from the five
debts in front of the border at that letter. -/
theorem standFirst_at (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (tie : RangeTie Xs K f w₀) (rel : Q.Rel w₀ rc x) (hstop : NoStop (keyProver K).first)
    (Said : Nat → Coins Bk → Mid (In1 W₀ Rc) X' → Prop)
    (next : ∀ b, SaidNext (Th Xs N Pl K f Q w₀ rc x) Said b) {n : Nat} (hn : n ≤ 19)
    (five : ∀ b, b < n → FiveAt (Th Xs N Pl K f Q w₀ rc x) Said (fun _ _ _ => none) b)
    (k : Coins Bk) (R : Ready W₀ Rc Xi OnBytes.TableKey Unit X₀ X')
    (hR : ready (keyFileDescription Xs N Pl) Bk (keyProver K) w₀ rc x k = .ok R)
    (start : Said 0 k { R.start₁ (keyProver K) with opened := some [] }) :
    ∀ b, b ≤ n → ∀ ds, drawsFit (declsTo (Th Xs N Pl K f Q w₀ rc x).bs b) ds = true →
      ∃ s m E, ThrS (Th Xs N Pl K f Q w₀ rc x) Said b k s m E ∧
        m.st.heard = ds ∧ m.st.input = inFirst w₀ rc x := by
  intro b hb ds hd
  have hE := entersFirst_of_ready Xs N Pl K f Q w₀ rc x hs scope tie rel k R hR
  have h0 : ThrS (Th Xs N Pl K f Q w₀ rc x) Said 0 k _
      { R.start₁ (keyProver K) with opened := some [] } _ := ⟨hE, start⟩
  obtain ⟨-, ⟨⟩, -, hown, -, hst, -⟩ := ready_ok hR
  have hlen : (Th Xs N Pl K f Q w₀ rc x).bs.length = 19 := (AtPublicFiles.KeyThread.lengths scope hs.named).1
  have hfit : (Th Xs N Pl K f Q w₀ rc x).fits 19 = true := by
    have h := AtPublicFiles.KeyThread.fits₁ (keyProver K) scope hs.named
      (AtPublicFiles.KeyThread.rest₁ Xs N Pl (fillH Xs N Pl K f Q x) w₀ rc x)
    rw [(AtPublicFiles.KeyThread.lengths scope hs.named).1] at h
    exact h
  obtain ⟨s, m, E, hA, hh, hi⟩ := stands_upTo (Th Xs N Pl K f Q w₀ rc x)
    Said (fun _ _ _ => none) hfit hn (by rw [hlen]; exact hn)
    (planOk_all hs.named.plan).1 five (fun _ _ _ => rfl) next hstop h0 hst b hb ds hd
  exact ⟨s, m, E, hA, hh.trans (List.nil_append ds), hi.trans hown⟩

/-- The same at the letter walkedFirst. -/
theorem standFirst_of_five (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (tie : RangeTie Xs K f w₀) (rel : Q.Rel w₀ rc x) (hstop : NoStop (keyProver K).first) {n : Nat}
    (hn : n ≤ 19)
    (five : ∀ b, b < n → FiveAt (Th Xs N Pl K f Q w₀ rc x) (walkedFirst Xs N Pl K f Q w₀ rc x)
      (fun _ _ _ => none) b)
    (k : Coins Bk) (R : Ready W₀ Rc Xi OnBytes.TableKey Unit X₀ X')
    (hR : ready (keyFileDescription Xs N Pl) Bk (keyProver K) w₀ rc x k = .ok R) :
    ∀ b, b ≤ n → ∀ ds, drawsFit (declsTo (Th Xs N Pl K f Q w₀ rc x).bs b) ds = true →
      ∃ s m E, ThrS (Th Xs N Pl K f Q w₀ rc x) (walkedFirst Xs N Pl K f Q w₀ rc x) b k s m E ∧
        m.st.heard = ds ∧ m.st.input = inFirst w₀ rc x :=
  standFirst_at hs scope tie rel hstop _ (lotSaidNextFirst Xs N Pl K f Q w₀ rc x) hn five k R hR
    (lotBegunFirst Xs N Pl K f Q w₀ rc x k R hR)

/-- **The first chain's stand, border 0 to 15.** -/
theorem lotStandFirst : LotStandFirst Xs N Pl K f Q w₀ rc x :=
  fun hs scope hp tie rel hstop left k R hR =>
    standFirst_of_five hs scope tie rel hstop (by decide)
      (fiveTo15 hs scope hp _ _ left) k R hR

/-- **The stand at every border, the last one (19) among them**, from all that is left at the first chain
(LeftFirst, E2E/LotFirstFromLeft.lean), at no fall. -/
theorem standFirst_to19 (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f) (tie : RangeTie Xs K f w₀) (rel : Q.Rel w₀ rc x)
    (hstop : NoStop (keyProver K).first)
    (left : LeftFirst Xs N Pl K f Q w₀ rc x (walkedFirst Xs N Pl K f Q w₀ rc x) fun _ _ _ => none)
    (k : Coins Bk) (R : Ready W₀ Rc Xi OnBytes.TableKey Unit X₀ X')
    (hR : ready (keyFileDescription Xs N Pl) Bk (keyProver K) w₀ rc x k = .ok R) :
    ∀ b, b ≤ 19 → ∀ ds, drawsFit (declsTo (Th Xs N Pl K f Q w₀ rc x).bs b) ds = true →
      ∃ s m E, ThrS (Th Xs N Pl K f Q w₀ rc x) (walkedFirst Xs N Pl K f Q w₀ rc x) b k s m E ∧
        m.st.heard = ds ∧ m.st.input = inFirst w₀ rc x :=
  standFirst_of_five hs scope tie rel hstop (Nat.le_refl 19) (fiveFromLeft hs scope hp _ _ left) k R hR

/-- **At the borders 0 to 4 nothing is left**: the pair stands there with no premise on any member. -/
theorem standFirst_to4 (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f) (tie : RangeTie Xs K f w₀) (rel : Q.Rel w₀ rc x)
    (hstop : NoStop (keyProver K).first) (k : Coins Bk)
    (R : Ready W₀ Rc Xi OnBytes.TableKey Unit X₀ X')
    (hR : ready (keyFileDescription Xs N Pl) Bk (keyProver K) w₀ rc x k = .ok R) :
    ∀ b, b ≤ 4 → ∀ ds, drawsFit (declsTo (Th Xs N Pl K f Q w₀ rc x).bs b) ds = true →
      ∃ s m E, ThrS (Th Xs N Pl K f Q w₀ rc x) (walkedFirst Xs N Pl K f Q w₀ rc x) b k s m E ∧
        m.st.heard = ds ∧ m.st.input = inFirst w₀ rc x :=
  standFirst_of_five hs scope tie rel hstop (by decide) (fiveTo4 hs scope hp _ _) k R hR

end

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.chainSteps_member
#print axioms AtPublicFiles.FirstH.Lots.stands_upTo
#print axioms AtPublicFiles.FirstH.Lots.fits_front
#print axioms AtPublicFiles.FirstH.Lots.some_list_fits
#print axioms AtPublicFiles.FirstH.Lots.fiveTo4
#print axioms AtPublicFiles.FirstH.Lots.fiveTo15
#print axioms AtPublicFiles.FirstH.Lots.standFirst_at
#print axioms AtPublicFiles.FirstH.Lots.standFirst_to19
#print axioms AtPublicFiles.FirstH.Lots.standFirst_of_five
#print axioms AtPublicFiles.FirstH.Lots.lotStandFirst
#print axioms AtPublicFiles.FirstH.Lots.standFirst_to4
