-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/AtSeats/KeptAtRch.lean: ALONG THE STATES THAT THE VERIFIER REACHES ON THE PROOF FILE's FIRST CHAIN, IN FRONT OF
EACH FEED-FORWARD LINK's READS: THE STATE STANDS BEHIND AN ACCEPT OF K4's OWN SUB-PROTOCOL AT THAT LINK's PUBLIC
PARAMETERS (`KeptAtS`, Johnson/Road/K4/KeptAtS.lean: the hearing's own equation
among its twelve), AND THE OPEN LINK's FRAME's NUMBER IS THE LINK's. FROM THE GOALS' SCOPE.
OBJECT: `Reach 0 c.blocksInOrder start`, `RchAt` (Johnson/Top/H0/Walk/).
USER: the payers of the clause JLay2 (Johnson/Desc/K1/Law/ArmLayIn.lean).
HOW: BY POSITION, on the road of Johnson/Desc/AtSeats/TablesAtHead.lean | TlAtRch.lean: at l = 2 g: the first place with
"opened" joined (14 l + 2) · the lookup on the calls (14 l + 3) · K4 (14 l + 4) · the reads (14 l + 5).
  `lnOf s`, `LN s s'`   the open link's frame's number, none where no link is open; it stays
  section "The lookup"   MIRRORS Johnson/Desc/K1/Law/TablesWalkHead.lean's section of that name LEMMA FOR LEMMA, at the
                   relation LN (made by program off its text; so does TlAtRch.lean at A4): a form general in the
                   relation would hold all three: not typed
  `ln_behind_first` · `ln_behind_look`   along Reach
  `KeptAt W g s`     there are K4's parameters p and a state s₀ with KeptAtS p s₀ s · p.g = g · p.P = W.layers ·
                   W.G[g]? = some p.hp · p.k3Runs = true · the frame's number is 2 g
  `kept_front_reads` | `kept_at_reads`   **along Reach | along RchAt**
  `u3_of_kept`       so the plan's number of the array of the reads is the state's (`hear_public`, OnBytes/Desc/First/K4/HearPublic.lean)
  `forms_of_reader`  where the reader of a run of K4's answers, the run's own function has returned and the
                   answer's forms are its list (the reader, the guard, the typing at claims and the lift to the
                   state, each inverted: `IM.guardRun_yes`, `atClaims_run`, `liftPart_run`, `runOf_ok`)
What is not claimed. That the scope can be met. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.TlAtRch
import Johnson.Desc.K1.Law.ArmLayIn
import Johnson.Road.K4.KeptAtS
import Johnson.Road.K4.ArmKept
import Johnson.IMR.K4Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Model OnBytes.Params Desc.Plain
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open Johnson.Desc.First.Walk
open Meaning.K2 (bindE unmarked_eq quiet_unmarked blockVia_whole withCaller_whole whole_same whole_sub
  guarded_whole mem_of_mapM_ok)

variable {Cl : Type}

/-! ## The relation -/

/-- The open link's frame's number; none where no link is open. -/
def lnOf (s : S) : Option ℕ := s.link?.map (·.check.frame.link)

/-- **It stays.** -/
def LN (s s' : S) : Prop := lnOf s' = lnOf s

theorem ln_refl (s : S) : LN s s := rfl

theorem ln_trans (a b c : S) (h : LN a b) (k : LN b c) : LN a c := Eq.trans k h

theorem ln_link {s s' : S} (h : s'.link? = s.link?) : LN s s' := by
  unfold LN lnOf
  rw [h]

theorem ln_here {s s' : S} (h : s'.here = s.here) : LN s s' := by
  refine ln_link ?_
  unfold S.link?
  rw [h]

/-! ## Writers of the state -/

theorem ln_mark (s : S) (name : String) : LN s (s.mark name) := by
  unfold S.mark
  split
  · exact ln_refl s
  · exact ln_here rfl

theorem ln_putFork (s : S) (F : Fork) : LN s (s.putFork F) := by
  unfold S.putFork
  repeat' split
  all_goals first
    | exact ln_refl _
    | exact ln_mark _ _
    | (unfold LN lnOf S.link?; simp [*])

theorem ln_putTl (s : S) (tl : HTailF2) : LN s (s.putTl tl) := by
  unfold S.putTl
  repeat' split
  all_goals first
    | exact ln_refl _
    | exact ln_mark _ _
    | (unfold LN lnOf S.link?; simp [*])

theorem ln_hearLook (s : S) (g : Forest.Heard) : LN s (s.hearLook g) := by
  unfold S.hearLook
  repeat' split
  all_goals first
    | exact ln_refl _
    | exact ln_mark _ _
    | (unfold LN lnOf S.link?; simp [*])

/-! ## The lookup -/

theorem seatCalls_put_ln (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    LN s ((K3.seatCalls claim).put s g G) :=
  ln_trans _ _ _ (ln_putFork s G) (ln_hearLook _ g)

theorem seatCalls_mark_ln (claim : Aff → Cl) (s : S) (G : Fork) :
    LN s ((K3.seatCalls claim).mark s G) := ln_putFork s G

theorem seatDigits_put_ln (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    LN s ((K3.seatDigits claim).put s g G) := by
  show LN s (match s.tl?, s.fork? with
    | some tl, some F =>
      (s.putTl { tl with
        foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next,
        heard := some g }).putFork G
    | _, _ => s.mark "K3 seat: no record of the smallness test")
  split
  · exact ln_trans _ _ _ (ln_putTl s _) (ln_putFork _ G)
  · exact ln_mark s _

theorem seatDigits_mark_ln (claim : Aff → Cl) (s : S) (G : Fork) :
    LN s ((K3.seatDigits claim).mark s G) := ln_putFork s G

theorem quietLook_ln (fs : Forest.Shape) : Fn LN (K3.quietLook fs) := fun s s' h => by
  unfold K3.quietLook at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  cases h
  exact ln_refl s

theorem quietDigits_ln (used claims : Nat) : Fn LN (K3.quietDigits used claims) :=
  fun s s' h => by
  unfold K3.quietDigits at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨G, _, h⟩ := bindE h
  cases h
  exact ln_putFork s G

theorem quietHead_ln (X : Verify.Public) : Fn LN (K3.quietHead X) := fun s s' h => by
  unfold K3.quietHead at h
  split at h
  · rename_i a ha
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    cases h
    unfold LN lnOf S.link?
    simp [ha]
  · cases h

theorem quietAt_ln (X : Verify.Public) (i : Nat) (digits : Bool)
    {f : S → Except String S} (h : K3.quietAt X i digits = some f) : Fn LN f := by
  unfold K3.quietAt at h
  simp only at h
  repeat' split at h
  all_goals first
    | (cases h; exact quietHead_ln X)
    | (cases h; exact quietLook_ln _)
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h; exact quietDigits_ln _ _)
    | cases h

theorem theOwn_ln (claim : Aff → Cl) (runs : Bool) (X : Verify.Public) (codes : Codes)
    (shape : ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theOwn claim runs X codes shape a = some b) : Whole LN b := by
  unfold K3.theOwn at h
  split at h
  · cases h
  · obtain ⟨i, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · cases h
    · obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨sent, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨laid, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨key, _, h⟩ := Option.map_eq_some_iff.1 h
      have W : Whole LN (K3.Law.blockVia (if digits = true then K3.seatDigits claim
          else K3.seatCalls claim) a.piece laid sent p []) := by
        cases digits
        · exact blockVia_whole LN ln_refl _ (seatCalls_put_ln claim) (seatCalls_mark_ln claim)
            _ _ _ _ _
        · exact blockVia_whole LN ln_refl _ (seatDigits_put_ln claim) (seatDigits_mark_ln claim)
            _ _ _ _ _
      rw [← h]
      cases runs
      · exact whole_same W rfl (fun _ hx => nomatch hx) rfl
      · exact whole_same W rfl (fun _ hx => hx) rfl

theorem theWhole_ln (claim : Aff → Cl) (runs : Bool) (X : Verify.Public) (codes : Codes)
    (shape : ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theWhole claim runs X codes shape a = some b) : Whole LN b := by
  unfold K3.theWhole at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  have W := theOwn_ln claim runs X codes shape a h0
  split
  · rename_i f hf
    obtain ⟨i, _, hq⟩ := Option.bind_eq_some_iff.1 hf
    exact Keeps.andThen_whole LN ln_trans _ _ _ W
      ⟨Keeps.quiet_decides LN _ _ _ _ f (quietAt_ln X i _ hq), (fun _ hc => nomatch hc),
        (fun _ hc => nomatch hc)⟩
  · exact W

/-- **The lookup's sub-protocol at any address.** -/
theorem theStated_ln (claim : Aff → Cl) (readers : Nat → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theStated claim readers X codes shape a = some b) : Whole LN b := by
  unfold K3.theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  have W := theWhole_ln claim true X codes shape a h0
  split at h
  · cases h
    exact W
  · split at h
    · cases h
      exact W
    · split at h
      · cases h
        exact W
      · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
        exact withCaller_whole LN _ (seatCalls_mark_ln claim) p _ W

/-! ## The walk -/

open Johnson.Desc.First.Walk.Tied (Reach RchAt rchAt_raw stepYes_decide)
open VerifiableInference.Desc.Sound (linksFull onQ Frame linkNo)
open OnBytes.Road.K4 (KeptAtS kept_atS)
open IM (Open k1Ix)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

/-- **Behind a feed-forward link's first place**, with "opened" joined behind it. -/
theorem ln_behind_first (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (g : ℕ) (hg : g < 12) (a : Q × S)
    (h : Reach 0 c.blocksInOrder start (14 * (2 * g) + 2 + 1) a) : lnOf a.2 = some (2 * g) := by
  obtain ⟨fs, hfs, hh⟩ := IM.frames_sit hS hR O
  obtain ⟨f, _, k, _, b, b', _, hf, _, _, _, _, _, iB, hk, _, ep, hj, _, _, _⟩ :=
    hh (2 * g) (by omega)
  obtain ⟨nam, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨X, _, hX, hkX, hgX, _⟩ := nam g hg
  obtain ⟨bX, hbX, ek, eg⟩ := built_of_ground O.blank hX
  cases h with
  | @succ _ z s s' b₁ h1 hb₁ hy =>
    obtain rfl : b = b₁ := Option.some.inj (iB.symm.trans hb₁)
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    obtain ⟨fs', f', m, hfs', hf', d1, _, d2, _, _⟩ := hj.yes hd
    rcases IM.frames_arms hfs' (2 * g) f' hf' with ⟨X2, h2, k2, _⟩ | ⟨l0, Pa, _, _, hop, _⟩ |
      ⟨Pa, nLin, hfa, _⟩ | ⟨Pa, hfa, _, hop, _⟩
    · obtain rfl : bX = X2 := Option.some.inj (hbX.symm.trans h2)
      rw [ek, hkX] at k2
      cases k2
    · rw [hop] at d2
      obtain ⟨_, _, hl, _, _, hL, _⟩ := Law.openLayZero_ok d2
      unfold lnOf
      rw [hL, l0]
      exact congrArg some hl
    · unfold Seat.frameAt at hfa
      rw [hbX] at hfa
      simp only [Option.bind_eq_bind, Option.bind_some, ek, hkX, eg, hgX] at hfa
      split at hfa
      · cases hfa
      · simp only [show ((0 : ℕ) == 1) = false from rfl, Bool.false_eq_true, if_false,
          beq_self_eq_true, if_true] at hfa
        obtain ⟨q, _, e⟩ := Option.bind_eq_some_iff.1 hfa
        cases Option.some.inj e
    · rw [hop] at d2
      obtain ⟨_, _, _, hl, _, hL, _⟩ := Law.openLay_ok d2
      have hPl : Pa.l = 2 * g := by
        unfold Seat.frameAt at hfa
        rw [hbX] at hfa
        simp only [Option.bind_eq_bind, Option.bind_some, ek, hkX, eg, hgX] at hfa
        split at hfa
        · cases hfa
        · simp only [show ((0 : ℕ) == 1) = false from rfl, Bool.false_eq_true, if_false,
            beq_self_eq_true, if_true] at hfa
          obtain ⟨q, _, e⟩ := Option.bind_eq_some_iff.1 hfa
          have e' := Option.some.inj e
          injection e' with e1
          rw [← e1]
      unfold lnOf
      rw [hL]
      exact congrArg some (hl.trans hPl)

/-- **Behind the lookup on the calls.** -/
theorem ln_behind_look (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (g : ℕ) (hg : g < 12) (a : Q × S)
    (h : Reach 0 c.blocksInOrder start (14 * (2 * g) + 2 + 1 + 1) a) : lnOf a.2 = some (2 * g) := by
  obtain ⟨Lk, b, b', e1, e2, h3, hla⟩ := IM.k3_of hS hR O (2 * g) (by omega) false
  have iB := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) (IM.k3Ix (2 * g) false)] at iB
  have hix : IM.k3Ix (2 * g) false = 1 := by
    show (if false = true then 6 else 1) + (if 2 * g = 24 then 1 else 0) = 1
    rw [if_neg (by omega : ¬ 2 * g = 24)]
    rfl
  rw [hix] at iB
  cases h with
  | @succ _ z s s' b₁ h1 hb₁ hy =>
    obtain rfl : b = b₁ := Option.some.inj (iB.symm.trans (by
      rw [show 14 * (2 * g) + 1 + 2 = 14 * (2 * g) + 2 + 1 by omega]
      exact hb₁))
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    exact ((theStated_ln _ _ _ _ _ _ h3).1 _ _ _ _
      ((IM.yes_alone hla (fun e => nomatch e) s s' rs gs).1 hd).1).trans
      (ln_behind_first hS hR O g hg (z, s) h1)

/-- Behind an accept of K4's own sub-protocol at group g's public parameters, in link 2 g. -/
def KeptAt (W : Verify.Public) (g : ℕ) (s : S) : Prop :=
  ∃ (p : OnBytes.Desc.First.K4.Par) (s₀ : S), KeptAtS p s₀ s ∧ p.g = g ∧ p.P = W.layers ∧
    W.G[g]? = some p.hp ∧ p.k3Runs = true ∧ lnOf s = some (2 * g)

/-- **Behind K4: in front of the reads.** -/
theorem kept_front_reads (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (g : ℕ) (hg : g < 12) (a : Q × S)
    (h : Reach 0 c.blocksInOrder start (14 * (2 * g) + 2 + 1 + 1 + 1) a) : KeptAt Bs.G₀.W g a.2 := by
  obtain ⟨Lk, b, x, e1, e2, _, hla, _, xg, xP, xh, _⟩ := IM.k4_of hS hR O g hg
  have iB := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) 2] at iB
  cases h with
  | @succ _ z s s' b₁ h1 hb₁ hy =>
    obtain rfl : b = b₁ := Option.some.inj (iB.symm.trans (by
      rw [show 14 * (2 * g) + 2 + 2 = 14 * (2 * g) + 2 + 1 + 1 by omega]
      exact hb₁))
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    have hd' := ((IM.yes_alone hla (fun e => nomatch e) s s' rs gs).1 hd).1
    have K : KeptAtS { x.2 with k3Runs := true } s s' :=
      kept_atS (rs := rs) (cols := gs) hd'
    have K2 := K
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hRest, _⟩ := K2
    refine ⟨{ x.2 with k3Runs := true }, s, K, xg, xP, xh, rfl, ?_⟩
    unfold lnOf
    rw [hRest.link]
    exact ln_behind_look hS hR O g hg (z, s) h1

/-- **Along "reached at the description's first chain", in front of each feed-forward link's reads.** -/
theorem kept_at_reads (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Str : Type} (l : ℕ) (hl : l < 25)
    (hsub : (linksFull[l]?).getD .layers = ModelPart.layers) (a : (ProofFile.InstPub × S) × Str)
    (hr : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      (14 * l + k1Ix l false + 2) a) : KeptAt Bs.G₀.W (l / 2) a.1.2 := by
  obtain ⟨e, hg⟩ := layIsEven l hl hsub
  have hk : k1Ix l false = 3 := by
    show (if false = true then 5 else 3) + (if l = 24 then 1 else 0) = 3
    rw [if_neg (by omega : ¬ l = 24)]
    rfl
  have hr' := rchAt_raw hr
  rw [hk, e, show 14 * (2 * (l / 2)) + 3 + 2 = 14 * (2 * (l / 2)) + 2 + 1 + 1 + 1 by omega] at hr'
  exact kept_front_reads hS hR O (l / 2) hg a.1 hr'

end

/-! ## What the hearing's return gives -/

section
open OnBytes.Road.K4.InT (kept_open)
open OnBytes.Desc.First.K4 (hear_public engFl hear)
open OnBytes.Tie.Pv.Tail.Port (u3Of)

/-- **The plan's number of the reads is the state's.** -/
theorem u3_of_kept {W : Verify.Public} {g : ℕ} {s : S} (K : KeptAt W g s) {b₀ : LayOwn}
    {o : Layer.Own} {hp : Layer.HPlan2} (hs : s.here = .lay b₀) (ho : b₀.own = some o)
    (hg : W.G[g]? = some hp) : u3Of hp.tl = o.v.iU3 := by
  obtain ⟨p, s₀, K, _, _, ph, _, _⟩ := K
  obtain ⟨a, a', fo, o', G, t, u, _, _, ha', _, eo, _, _, hh⟩ := kept_open K
  obtain rfl : b₀ = a' := First.Here.lay.inj (hs.symm.trans ha')
  obtain rfl : o = o' := Option.some.inj (ho.symm.trans eo)
  obtain rfl : p.hp = hp := Option.some.inj (ph.symm.trans hg)
  obtain ⟨-, -, iU3, _, _, _, _, _, _, _, e3, -, -, -, ev, -⟩ :=
    hear_public (show hear engFl _ p.hp p.g fo a.F t = some (o, G, u) from hh)
  unfold u3Of
  rw [e3, ev]
  rfl

end

/-! ## The readers of K4's two runs, inverted -/

section
open OnBytes.Desc.First.K4 (blockAtC blockAtS block seatOwn runOf runOf_ok part? setPart liftPart_run
  atClaims_run claimOf frontOf formsBack block_front block_back)
open OnBytes.Desc.First.K4.InT (find_of_lookup forms_claimOf)
open VerifiableInference.Desc.K9 (readerOf)

/-- **Where the reader of a run of K4's answers, the run's own function has returned, and the answer's forms
are its list.** -/
theorem forms_of_reader {p : OnBytes.Desc.First.K4.Par} {name nm : String}
    {f : Layer.Own → Fork → Option (Array Aff × Fork)}
    (hl : (block seatOwn p).claims.lookup name = some fun _ s => runOf seatOwn nm f s)
    {states : ℕ → List (K9.RunOf S)} {b : ℕ} {same : S → S → Bool}
    (hst : states b = (blockAtC p).claims.map fun c => (c.1, IM.guardRun same c.2)) {s : S}
    {R : K9.Read} {b₀ : LayOwn} {o : Layer.Own} (hs : s.here = .lay b₀) (ho : b₀.own = some o)
    (h : readerOf states b name s = some R) :
    ∃ ff G₁, f o b₀.F = some (ff, G₁) ∧ R.forms = ff.toList := by
  have e := liftPart_run part? setPart (block seatOwn p) name
  rw [hl] at e
  have eC := atClaims_run (blockAtS p) name
  rw [show List.lookup name (blockAtS p).claims = _ from e] at eC
  have hfind := find_of_lookup _ _ _ eC
  unfold readerOf at h
  obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.1 h
  rw [hst, List.find?_map] at hr
  obtain ⟨c0, hc0, rfl⟩ := Option.map_eq_some_iff.1 hr
  have hc1 : (blockAtC p).claims.find? (fun x => x.1 == name) = some c0 := hc0
  rw [show (blockAtC p).claims.find? (fun x => x.1 == name) = _ from hfind] at hc1
  obtain rfl := Option.some.inj hc1
  dsimp only at h
  split at h
  · rename_i z F hz hF
    obtain ⟨G, hG, h⟩ := Option.bind_eq_some_iff.1 h
    split at h
    · obtain rfl := Option.some.inj h
      obtain ⟨h1, _⟩ := (IM.guardRun_yes _ 0 s z).1 hz
      have hq : part? s = some (b₀, (if s.noneWaits then none else s.rowsOwed), s.tokv) := by
        simp only [part?, hs]
      rw [hq] at h1
      cases hrun : runOf seatOwn nm f (b₀, (if s.noneWaits then none else s.rowsOwed), s.tokv) with
      | error e =>
        have h2 : Except.map (fun y : List Aff × S => (List.map claimOf y.1, y.2))
            (Except.map (fun y => (y.1, setPart s y.2))
              (runOf seatOwn nm f (b₀, (if s.noneWaits then none else s.rowsOwed), s.tokv))) =
            .ok z := h1
        rw [hrun] at h2
        cases h2
      | ok y =>
        have h2 : Except.map (fun y : List Aff × S => (List.map claimOf y.1, y.2))
            (Except.map (fun y => (y.1, setPart s y.2))
              (runOf seatOwn nm f (b₀, (if s.noneWaits then none else s.rowsOwed), s.tokv))) =
            .ok z := h1
        rw [hrun] at h2
        obtain rfl : (List.map claimOf y.1, setPart s y.2) = z := Except.ok.inj h2
        obtain ⟨o', fs, F', ho', hf, hcl, _⟩ := (runOf_ok seatOwn nm f _ y.2 y.1).1 hrun
        obtain rfl : o = o' := Option.some.inj (ho.symm.trans ho')
        refine ⟨fs, F', hf, ?_⟩
        show (List.map claimOf y.1).map (·.form) = _
        rw [forms_claimOf, hcl]
    · cases h
  · cases h

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.theStated_ln
#print axioms VerifiableInference.Desc.K1.ln_behind_first
#print axioms VerifiableInference.Desc.K1.ln_behind_look
#print axioms VerifiableInference.Desc.K1.kept_front_reads
#print axioms VerifiableInference.Desc.K1.kept_at_reads
#print axioms VerifiableInference.Desc.K1.u3_of_kept
#print axioms VerifiableInference.Desc.K1.forms_of_reader
