-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/FirstHWRow.lean: number 17 of the key file's first chain, W's sending, at the thread `T₁`: all
debts but the claim (Eval).

  `w_claim`: a yes of W's sub-protocol leaves the linear claim as it was.
  `keeps_w`, `behind_w`: what the step keeps, and the clause behind it.
  `ride_pile`, `rides_w`: what rides past it, the item "pile" among it.
  `exchange_w`: what the row owes, from the claim (Eval).

Limits. The claim (Eval) is a premise of `exchange_w`. Conditional on `FirstPublic` and on the thread
in front.
-/
import E2E.FirstHRows
import Johnson.Desc.Key.KeyLensLaws

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.FirstH
open OnBytes OnBytes.Params OnBytes.Means
open VerifiableInference.Desc (Block OpenedColumn Strs)
open VerifiableInference.Desc.Key (Xi FirstState Claim ChainState KItem Source LaterPlaces start₁
  sendW sendingSeat Pieces batchLens lens_get)
open VerifiableInference.Desc.Keeps (ebind_ok emap_ok)
open VerifiableInference.Desc.ChainEnd (bind_ok)
open Johnson.RunOne.KeyRows1 (readers₁)
open AtPublicFiles.KeyThread (D one₀ rowsFirst form_behind₁)
open AtPublicFiles.KeyFile (KeyParts In1)
open AtPublicFiles.AtFiles (KeySourced sendWAt)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest
open ProofFile.Honest.K1 (SendJob)

section Text
variable {β Cl : Type}

/-- The text behind W's commitment hands back the claim that it was given. -/
theorem rows_claim {S : LinShape} {claim : LinClaim} {ids : Array Nat}
    {d : VerifiableInference.Desc.K13.St} {y : LinFirst × VerifiableInference.Desc.K13.St}
    (h : VerifiableInference.Desc.K13.rows S claim ids d = .ok y) : y.1.claim = claim := by
  unfold VerifiableInference.Desc.K13.rows at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  rw [← Except.ok.inj h]

/-- **A yes of W's sub-protocol leaves the linear claim.** -/
theorem w_claim {one : OneTime} {N : Pieces} {sent : Nat} {groups : List (List Nat)}
    {bw : Block (ChainState β) Cl} (hb : sendW one N sent groups = some bw) {s s' : ChainState β}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (h : bw.decide s rs gs = .ok s') :
    s'.lin.map (·.claim) = s.lin.map (·.claim) := by
  unfold sendW at hb
  cases hm : linMessageW one.lin with
  | none =>
    rw [hm] at hb
    cases hb
  | some msg =>
    rw [hm] at hb
    have hb' := Option.some.inj hb
    subst hb'
    obtain ⟨m₃, h₃, hr⟩ := ebind_ok h
    obtain ⟨m₂, h₂, hq₂⟩ := ebind_ok h₃
    obtain ⟨m₁, hq₁, hk⟩ := ebind_ok h₂
    obtain ⟨_, _, hq₁⟩ := bind_ok hq₁
    obtain rfl : s = m₁ := Except.ok.inj hq₁
    obtain ⟨y, -, he⟩ := emap_ok hk
    have e₂ : m₂.lin = s.lin := by
      rw [← he]
    have e₃ : m₃.lin = m₂.lin := by
      rw [← Except.ok.inj hq₂]
    obtain ⟨p, hp, hr⟩ := bind_ok hr
    obtain ⟨-, rfl⟩ := (lens_get _ _).1 (VerifiableInference.Desc.K13.part_ok hp)
    obtain ⟨l, hl, hr⟩ := bind_ok hr
    obtain ⟨o, ho, hr⟩ := bind_ok hr
    have hl' : m₃.lin = some l := VerifiableInference.Desc.K13.there_ok hl
    have e₄ : s'.lin = some o.1 := by
      rw [← Except.ok.inj hr] <;> rfl
    rw [e₄, ← e₂, ← e₃, hl', Option.map_some, Option.map_some, rows_claim ho]

end Text

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X' Wk : Type} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
  {K : KeyParts W₀ Rc X₀ X' Wk} {f : W₀ → Weights} {Q : LaterFill Bk W₀ Rc} {w₀ : W₀} {rc : Rc}
  {x : Xi} {Z : PublicFiles}

/-- **The clause behind W's sending.** -/
theorem behind_w (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f) : Behind (Th Xs N Pl K f Q w₀ rc x) 17 := by
  have h := seat_w (Q := Q) (w₀ := w₀) (rc := rc) (x := x) hs scope hp
  obtain ⟨bw, hw⟩ := w_there hs scope
  have hw' : sendW Xs.Y.k.oneTime VerifiableInference.Desc.Key.pieces
      (AtPublicFiles.AtFiles.sentAt Xs.Y.D.1) (AtPublicFiles.AtFiles.groupsW Xs.Y.D.1 Xs.Y.told.1) = some bw := hw
  intro blk hblk k s m E ds y cols s' hT hd hS
  have e : (Th Xs N Pl K f Q w₀ rc x).bs[17]? = some bw.asBare := (member_back hs scope hw).2
  obtain rfl : bw.asBare = blk := Option.some.inj (e.symm.trans hblk)
  refine ⟨form_behind₁ Xs N Pl (Fl Xs N Pl K f Q x) w₀ rc x hs scope (by decide) e hT hS, trivial,
    seat_stays h e hT hd hS, ?_⟩
  obtain ⟨-, gs, hdec⟩ := VerifiableInference.Desc.K1.step_ok _ _ s s' _ _ _ hS.2
  exact w_claim hw' hdec

/-- **The item "pile" rides past a step that leaves the claim.** -/
theorem ride_pile {k : Coins Bk} {m : Mid (In1 W₀ Rc) X'} {s s' : FirstState} {y y' : Strs} {v}
    (hs : StaysW s s') :
    (Th Xs N Pl K f Q w₀ rc x).means m.st.input .pile ((Th Xs N Pl K f Q w₀ rc x).seat k m s) y v →
    (Th Xs N Pl K f Q w₀ rc x).means m.st.input .pile ((Th Xs N Pl K f Q w₀ rc x).seat k m s') y' v := by
  rintro ⟨r, hr, ht⟩
  refine ⟨r, ?_, ht⟩
  have e := congrArg (Option.map VerifiableInference.Desc.Key.rowOfLinClaim) hs.2
  simp only [Option.map_map, Function.comp_def] at e
  exact e.trans hr

/-- **What rides past W's sending.** -/
theorem rides_w : RidesPast (Th Xs N Pl K f Q w₀ rc x) 17 := by
  intro k s m E s' ps i v hT hkeep hi hn ho hm
  have hc : ∀ i ∈ ProofFile.Honest.fwdOpen (start₁ 2) rowsFirst 17, i ∉ (rowsFirst 17).shuts →
      i ∉ (rowsFirst 17).owes → rideKind i = true ∨ i = .pile := by decide
  rcases hc i hi hn ho with h | rfl
  · exact ride_any hkeep.1 (order_of hT.2.2.1) h hm
  · exact ride_pile hkeep hm

/-- **What the row owes**, from the claim (Eval). -/
theorem exchange_w (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (hp : FirstPublic (Pl := Pl) Xs N K f)
    (hEval : ∀ blk, (Th Xs N Pl K f Q w₀ rc x).bs[17]? = some blk → ∀ k s m E ds y cols s',
      Thr (Th Xs N Pl K f Q w₀ rc x) 17 k s m E → drawsFit blk.rounds ds = true →
      (Th Xs N Pl K f Q w₀ rc x).Stepped blk k s m E ds y cols s' →
      (Th Xs N Pl K f Q w₀ rc x).Items [.claim 1 "Eval"] k s' y.2 (E.add y.1)) :
    Exchange (Th Xs N Pl K f Q w₀ rc x) 17 := by
  have h := seat_w (Q := Q) (w₀ := w₀) (rc := rc) (x := x) hs scope hp
  intro blk hblk k s m E ds y cols s' hT hd hS
  have hF := form_behind₁ Xs N Pl (Fl Xs N Pl K f Q x) w₀ rc x hs scope (by decide) hblk hT hS
  have hP := seat_pin h (E := E.add y.1) hF
  have hR := seat_srow h hblk hT hd hS hF (order_of hF)
  have hE := hEval blk hblk k s m E ds y cols s' hT hd hS
  show (Th Xs N Pl K f Q w₀ rc x).Items (rowsFirst 17).owes k s' y.2 (E.add y.1)
  have ho : (rowsFirst 17).owes = [.pin 2, .srow 2, .claim 1 "Eval"] := by decide
  rw [ho]
  intro ds' i hi
  rcases List.mem_cons.1 hi with rfl | hi
  · exact hP ds' _ (List.mem_singleton.2 rfl)
  rcases List.mem_cons.1 hi with rfl | hi
  · exact hR ds' _ (List.mem_singleton.2 rfl)
  obtain rfl := List.mem_singleton.1 hi
  exact hE ds' _ (List.mem_singleton.2 rfl)

end AtPublicFiles.FirstH

#print axioms AtPublicFiles.FirstH.rows_claim
#print axioms AtPublicFiles.FirstH.w_claim
#print axioms AtPublicFiles.FirstH.behind_w
#print axioms AtPublicFiles.FirstH.ride_pile
#print axioms AtPublicFiles.FirstH.rides_w
#print axioms AtPublicFiles.FirstH.exchange_w
