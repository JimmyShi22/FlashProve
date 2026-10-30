-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/AtSeats/RowsBareWalk.lean: «THE ROWS THAT THE LOOKUP ON THE CALLS HEARD NAME NO ENTRY» (RowsBare,
Johnson/Desc/K1/Law/ArmElsePaid.lean) ALONG THE REACHED STATES OF THE FIRST CHAIN, IN FRONT OF THE OUTPUT
HEAD's READS' PLACE (number 342 of the flat list): A WALK OF FOUR SUB-PROTOCOLS, BY POSITION, on the road of
Johnson/Desc/AtSeats/TablesAtHead.lean, UNDER ONE NAMED PREMISE ON THE LOOKUP's OWN
STEP (hK3: k3Bare_of, Johnson/Desc/AtSeats/RowsBareAtHead.lean, pays it in scope, from the tests on
the plan of the chain's sub-protocols; it does not call stated_rowsBare,
Johnson/Desc/First/Look/K03RowsBare.lean). Definitions, and
statements with their proofs.

  338  K7's place (the front step that enters the segment, then K7's own; the frame's "opened" joined):
       BEHIND IT THE STATE STANDS IN THE HEAD                                        head_339
  339  K2's place: at a state in the head the arm that accepts is "the switch, then the step that opens the
       segment": THE LEDGER THAT IT LAYS HAS ITS SIZES (headOpenQ_laid)                sized_340
  340  the lookup on the calls: hK3: from a ledger with its sizes: RowsBare behind    rowsBare_341
  341  K6: it leaves what the lookup heard (LK)                                      rowsBare_342
Main names beside: HK · k7Of_here · blockOf_head · headFrontQ_head · k7Block_head · opened_head · k2Is_sized ·
  LK (lk_refl, lk_trans) · seatedClaims_lk · K3Bare (the premise's form) ·
  rowsBareH_at_reads  **RowsBareH at the reached states in front of all 25 reads' places** (idle at l < 24).
What is not claimed. hK3. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.ArmElsePaid
import Johnson.Top.H0.Tw.K2C.HeadLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Johnson.Desc.First.Walk.Tied (Reach RchAt rchAt_raw stepYes_decide)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head (seatAt HeardAll)
open VerifiableInference.Desc.Sound (linksFull onQ Frame)
open Johnson.Desc.First.Walk
open Meaning.K2 (bindE unmarked_eq quiet_unmarked k7_whole entered_whole k6Join_whole whole_sub
  guarded_whole mem_of_mapM_ok)
open OnBytes.PscRun (Sized)
open IM (Open k1Ix subAt)
open ProofFile (Cl)

/-! ## 338: behind K7's place the state stands in the head -/

/-- "here" stays. -/
def HK (s s' : S) : Prop := s'.here = s.here

theorem k7Of_here (W : Verify.Public) (l : Nat) : Whole HK (Reply.blockOf W l) :=
  entered_whole (k7_whole HK Reply.seatAt (fun _ _ => rfl) l 1 W.hS.V)

theorem blockOf_head (W : Verify.Public) (l : Nat) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (e : (Reply.blockOf W l).decide s rs gs = .ok s') :
    ∃ o, s'.here = .head o := by
  have hk : s'.here = s.here := (k7Of_here W l).1 s rs gs s' e
  cases hh : s.here with
  | head o => exact ⟨o, hk.trans hh⟩
  | _ =>
    exfalso
    simp only [Reply.blockOf, Reply.blockAt, Reply.entered, hh] at e
    cases e

/-- Behind K7's place's sub-protocol, as the lot lays it. -/
theorem k7Block_head (X : Verify.Public) (l : ℕ) {s m : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (e : (IM.k7Block X l).decide s rs gs = .ok m) :
    ∃ o, m.here = .head o := by
  unfold IM.k7Block at e
  dsimp only at e
  obtain ⟨s₁, _, h2⟩ := (bind_ok _ _ _).1 e
  exact blockOf_head X l h2

theorem not_between_of_head {s : S} {o : HeadOwn} (h : s.here = .head o) : s.atBetween = false := by
  unfold S.atBetween
  rw [h]

open Johnson.Desc.First.Walk.Seat in
/-- A row's "opened" that accepts at a state in the head leaves it there. -/
theorem opened_head {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} (h : framesOf built first W = .ok fs) : ∀ f ∈ fs, ∀ m t o,
    f.opened m = .ok t → m.here = .head o → ∃ o', t.here = .head o' := by
  intro f hf m t o hd ho
  have nb := not_between_of_head ho
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      cases hd
      exact ⟨o, ho⟩
  · split at e
    · split at e
      · cases e
      · cases e
        exfalso
        have hd' : openLayZero _ _ _ m = .ok t := hd
        unfold openLayZero at hd'
        obtain ⟨_, hb, _⟩ := bindE hd'
        rw [nb] at hb
        cases hb
    · split at e
      · cases e
      · cases e
        exfalso
        have hd' : openAtt _ m = .ok t := hd
        unfold openAtt at hd'
        obtain ⟨_, hb, _⟩ := bindE hd'
        rw [nb] at hb
        cases hb
      · cases e
        exfalso
        have hd' : openLay _ m = .ok t := hd
        unfold openLay at hd'
        obtain ⟨_, hb, _⟩ := bindE hd'
        rw [nb] at hb
        cases hb

/-! ## 339: the ledger that K2's place lays has its sizes -/

/-- A ledger is open at the state, with its sizes. -/
def SizedOpen (s : S) : Prop := ∃ F, s.fork? = some F ∧ Sized F

theorem headOpenQ_sized (P : K2.HeadPar) : Fn (fun _ s' => SizedOpen s') (K2.headOpenQ P) :=
  fun _ s' h => by
    obtain ⟨F, h1, _, h3, h4, h5, _, _⟩ := K2.headOpenQ_laid h
    exact ⟨F, h1, h4, h5, h3⟩

/-- K2's lot's sub-protocol at a place in a link, at a state in the head. -/
theorem k2Is_sized {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : Place} {nm : String} {x : Block S Unit}
    (h : IM.K2Is Z G a nm x) {l : ℕ} (hl : a.link = some l) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {o : HeadOwn} (ho : s.here = .head o)
    (e : x.decide s rs gs = .ok s') : SizedOpen s' := by
  rcases h with ⟨-, hm⟩ | ⟨P, n, -, -, h | h | h⟩
  · obtain ⟨er, he⟩ := hm s rs gs
    rw [he] at e
    cases e
  · rw [hl] at h
    exact nomatch h.1
  · obtain ⟨l', HP, -, -, rfl⟩ := h
    have e' : ((K2.codeSwitchKind (IM.k2P Z a nm .head n) : Block S Unit).decide s
        (rs.take (K2.codeSwitchKind (IM.k2P Z a nm .head n) : Block S Unit).rounds.length)
        (gs.take (K2.codeSwitchKind (IM.k2P Z a nm .head n) : Block S Unit).openings)).bind (fun m =>
                    (K2.headOpened nm a HP : Block S Unit).decide m
                      (rs.drop (K2.codeSwitchKind (IM.k2P Z a nm .head n) : Block S Unit).rounds.length)
                      (gs.drop (K2.codeSwitchKind (IM.k2P Z a nm .head n) : Block S Unit).openings)) = .ok s' := e
    obtain ⟨m, _, h2⟩ := (bind_ok _ _ _).1 e'
    have D : Decides (fun _ s' => SizedOpen s') (roundlessBlock (nm ++ ": opened") a.chain a.link a.piece
        (K2.headOpenQ HP) : Block S Unit) := Keeps.quiet_decides _ _ _ _ _ _ (headOpenQ_sized HP)
    exact D m (rs.drop (K2.codeSwitchKind (IM.k2P Z a nm .head n) : Block S Unit).rounds.length)
      (gs.drop (K2.codeSwitchKind (IM.k2P Z a nm .head n) : Block S Unit).openings) s' h2
  · obtain ⟨l', -, rfl⟩ := h
    exfalso
    have e' : K2.decideWith _root_.Tw.K2.sendByL8 (IM.k2P Z a nm .link n) s rs gs = .ok s' := e
    unfold K2.decideWith at e'
    dsimp only [IM.k2P] at e'
    rw [ho] at e'
    split at e' <;> cases e'

/-! ## 341: K6 leaves what the lookup heard -/

/-- What the lookup on the calls heard stays. -/
def LK (s s' : S) : Prop := s'.lookHeard? = s.lookHeard?

theorem lk_refl (s : S) : LK s s := rfl

theorem lk_trans (a b c : S) (h : LK a b) (k : LK b c) : LK a c := Eq.trans k h

theorem lk_putFork (s : S) (F : Fork) : LK s (s.putFork F) := by
  unfold S.putFork
  repeat' split
  all_goals first
    | exact lk_refl _
    | (unfold LK S.lookHeard?; simp [*])

theorem seatAt_ledger_lk (h : Model.Head.Shape) (iU3 : Nat) (s : S) (F : Fork) (s' : S)
    (e : (seatAt h iU3).setLedger s F = .ok s') : LK s s' := by
  have e' : s.putFork? F = .ok s' := e
  unfold S.putFork? at e'
  split at e'
  · rw [quiet_unmarked e']
    exact lk_putFork s F
  · cases e'

theorem seatAt_heard_lk (h : Model.Head.Shape) (iU3 : Nat) (s : S) (H : HeardAll) (s' : S)
    (e : (seatAt h iU3).setHeard s H = .ok s') : LK s s' := by
  simp only [seatAt] at e
  split at e
  · rename_i o ho
    split at e
    · cases e
      unfold LK S.lookHeard?
      simp [ho]
    · cases e
  · cases e

theorem blockClaims_lk {W : Verify.Public} {l : Nat} {b : Block S Claim}
    (h : Kinds.Head.blockClaims W l = some b) : Whole LK b := by
  unfold Kinds.Head.blockClaims at h
  obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.1 h
  exact k6Join_whole LK lk_refl lk_trans _ (fun s G => lk_putFork s G) (seatAt W.hS iU3)
    (seatAt_ledger_lk W.hS iU3) (seatAt_heard_lk W.hS iU3) (fun s _ => lk_refl s)
    (fun s _ => lk_refl s) l 4 _

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
theorem seatedClaims_lk {W : Verify.Public} {l : Nat} {before : List (Nat × Nat)}
    {b : Block S Claim} (h : Kinds.Head.seatedClaims W l before = some b) : Whole LK b := by
  unfold Kinds.Head.seatedClaims at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  refine whole_sub (blockClaims_lk h0) (fun s rs gs s' k => ?_) (fun _ hx => hx) rfl
  first
    | exact k
    | (unfold Kinds.Head.tested at k
       dsimp only at k
       split at k
       · exact k
       · cases k)

theorem LK.bare {s s' : S} (h : LK s s') (k : RowsBare s) : RowsBare s' := by
  intro g hg
  exact k g (h.symm.trans hg)

/-! ## The walk -/

/-- **The premise on the lookup's own step at link 24.** -/
def K3Bare (W : Verify.Public) (Z : ProofFile.Pub) : Prop :=
  ∀ b' s s' rs gs, IM.k3At W Z (IM.k3Place 24 false) = some b' → b'.decide s rs gs = .ok s' →
    SizedOpen s → RowsBare s'

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

theorem head_339 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (a : Q × S)
    (h : Reach 0 c.blocksInOrder start (338 + 1) a) : ∃ o, a.2.here = .head o := by
  obtain ⟨fs, hfs, hh⟩ := IM.frames_sit hS hR O
  obtain ⟨f, _, k, _, b, b', _, hf, _, _, _, _, _, iB, hk, ⟨L, hL, hb'⟩, ep, hj, _, _, _⟩ :=
    hh 24 (by omega)
  have h0 : (kindsBeforeBatching (subAt 24) (24 == 0))[0]? = some KindName.K7 := rfl
  obtain rfl : KindName.K7 = k := Option.some.inj (h0.symm.trans hk)
  obtain ⟨sz, -⟩ := IM.ground_gets hS hR O.pub O.blank
  obtain ⟨x, hm, rfl⟩ := IM.lot_K7 hL hb' (by rw [ep])
  unfold ProofFile.h1Own at hm
  rw [sz] at hm
  obtain rfl := List.mem_singleton.1 hm
  cases h with
  | @succ _ z s s' b₁ h1 hb₁ hy =>
    obtain rfl : b = b₁ := Option.some.inj (iB.symm.trans hb₁)
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    obtain ⟨fs', f', m, hfs', hf', d1, _, d2, _, _⟩ := hj.yes hd
    obtain ⟨o, ho⟩ := k7Block_head Bs.G₀.W 24 d1
    exact opened_head hfs' f' (List.mem_of_getElem? hf') m s' o d2 ho

theorem sized_340 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (a : Q × S)
    (h : Reach 0 c.blocksInOrder start (339 + 1) a) : SizedOpen a.2 := by
  obtain ⟨Lk, b, x, e1, e2, _, hla, his⟩ := IM.k2_head_of hS hR O
  have iB := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) 1] at iB
  cases h with
  | @succ _ z s s' b₁ h1 hb₁ hy =>
    obtain rfl : b = b₁ := Option.some.inj (iB.symm.trans hb₁)
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    obtain ⟨o, ho⟩ := head_339 hS hR O (z, s) h1
    exact k2Is_sized his rfl ho ((IM.yes_alone hla (fun e => nomatch e) s s' rs gs).1 hd).1

theorem rowsBare_341 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hK3 : K3Bare Bs.G₀.W Z) (a : Q × S)
    (h : Reach 0 c.blocksInOrder start (340 + 1) a) : RowsBare a.2 := by
  obtain ⟨Lk, b, b', e1, e2, h3, hla⟩ := IM.k3_of hS hR O 24 (by omega) false
  have iB := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) (IM.k3Ix 24 false)] at iB
  cases h with
  | @succ _ z s s' b₁ h1 hb₁ hy =>
    obtain rfl : b = b₁ := Option.some.inj (iB.symm.trans hb₁)
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    exact hK3 b' s s' rs gs h3 ((IM.yes_alone hla (fun e => nomatch e) s s' rs gs).1 hd).1
      (sized_340 hS hR O (z, s) h1)

/-- **In front of the output head's reads' place.** -/
theorem rowsBare_342 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hK3 : K3Bare Bs.G₀.W Z) (a : Q × S)
    (h : Reach 0 c.blocksInOrder start (341 + 1) a) : RowsBare a.2 := by
  obtain ⟨Lk, b, b', ms, e1, e2, _, h6, hla, _⟩ := IM.k6_of hS hR O
  have iB := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) 3] at iB
  cases h with
  | @succ _ z s s' b₁ h1 hb₁ hy =>
    obtain rfl : b = b₁ := Option.some.inj (iB.symm.trans hb₁)
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    exact ((seatedClaims_lk h6).1 s rs gs s'
      ((IM.yes_alone hla (fun e => nomatch e) s s' rs gs).1 hd).1).bare
      (rowsBare_341 hS hR O hK3 (z, s) h1)

/-- **RowsBareH at the reached states in front of all 25 reads' places.** -/
theorem rowsBareH_at_reads (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hK3 : K3Bare Bs.G₀.W Z) {W : Type}
    {Fr : Frame} (N : Numbers) (Mg : Meaning ProofFile.InstPub W) :
    ∀ l, l < 25 → ∀ a : (ProofFile.InstPub × S) × Fr.E.Str,
      RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
        (14 * l + k1Ix l false + 2) a →
      onQ N Mg linksFull (flatPlacesOf linksFull true) (fun a => a) (14 * l + k1Ix l false + 2) a →
      a.1.2.failed = none → RowsBareH a.1.2 := by
  intro l hl a hr hon hm o ho
  by_cases h24 : l = 24
  · subst h24
    exact rowsBare_342 hS hR O hK3 a.1 (rchAt_raw hr)
  · exfalso
    have hs := stand_of_promise l hl a.1 _ ⟨hon, hm⟩
    unfold standOf at hs
    rw [ho] at hs
    dsimp only at hs
    split at hs
    · exact absurd (First.Stand.link.inj hs).symm (low_not_head l (by omega))
    · cases hs

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.k7Of_here
#print axioms VerifiableInference.Desc.K1.blockOf_head
#print axioms VerifiableInference.Desc.K1.k7Block_head
#print axioms VerifiableInference.Desc.K1.opened_head
#print axioms VerifiableInference.Desc.K1.headOpenQ_sized
#print axioms VerifiableInference.Desc.K1.k2Is_sized
#print axioms VerifiableInference.Desc.K1.lk_putFork
#print axioms VerifiableInference.Desc.K1.seatedClaims_lk
#print axioms VerifiableInference.Desc.K1.LK.bare
#print axioms VerifiableInference.Desc.K1.head_339
#print axioms VerifiableInference.Desc.K1.sized_340
#print axioms VerifiableInference.Desc.K1.rowsBare_341
#print axioms VerifiableInference.Desc.K1.rowsBare_342
#print axioms VerifiableInference.Desc.K1.rowsBareH_at_reads
