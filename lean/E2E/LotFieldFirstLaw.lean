-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotFieldFirstLaw.lean: WHAT THE LAST CHAIN's DOOR ASKS OF AN EARLIER CHAIN, at the letter WalkedFrom (E2E/WalkedFrom.lean), general
in the thread. For E2E/LotFieldFirst.lean.

Why a second law on the field. walked_field (E2E/WalkedField.lean) takes hTrees at EVERY list of challenges and without the letter:
«Thr T b k s m E → T.Moved blk k m E ds y cols → T.Trees (T.fresh b) …». The members' own debt PlaysS (Honest/Thread/PaysS.lean)
gives its last clause only at a pair (ThrS), at a list that fits, outside the stops. The walk's second constructor holds just
these: the letter in front, and drawsFit. So the field comes from PlaysS itself, and no new premise is named.

Main names.
  trees_of_plays      PlaysS's last clause, at whatever Moved holds of: play and chainSteps are functions. hstop: no part stops.
  walked_field_plays  walked_field with PlaysS at the members in front in hTrees' place: that proof, with one line turned.
  oneState_walked     OneState at the letter: oneStand_walked, oneColumns_of, oneState_at. NO PREMISE ON ANY MEMBER.
  DoorAsks            the structure, field by field as at E2E/KeyLastTerm.lean:56 (AtPublicFiles.KeyLastChain.DoorAsks; that file is typed and
                      has heavy imports, so it is not imported: ⟨D.one, D.state, D.field, D.next⟩ is a term of that structure).
  doorAsks_walked     all four at the letter that begins at one named state whose field is some [].
  enter_walked        that letter holds at that state (the page's fifth ask, «enter»).

What stays open: every premise is a letter's here. Nothing says that the pair stands at any border: where it stands nowhere,
state and field are empty. No law over coins. Nothing on soundness, completeness, hiding or binding.
-/
import E2E.WalkedField
import E2E.NoStop
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.LotField
open ProofFile.Honest
open VerifiableInference.Desc (Block OpenedColumn)
open AtPublicFiles.Stops (NoStop chainStopAt_none)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S Cl V W X Pb}

/-- **The last clause of PlaysS, at whatever Moved holds of.** -/
theorem trees_of_plays {Said : Nat → Coins Bk → Mid W X → Prop} {b : Nat} (hP : PlaysS T Said b)
    (hstop : NoStop T.hs) {blk : Block S Cl} (hblk : T.bs[b]? = some blk) {k : Coins Bk} {s : S}
    {m : Mid W X} {E : Env} {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List OpenedColumn}
    (hT : ThrS T Said b k s m E) (hd : drawsFit blk.rounds ds = true)
    (hM : T.Moved blk k m E ds y cols) : T.Trees (T.fresh b) k y.2 (E.add y.1) := by
  obtain ⟨⟨l, hl, hp⟩, -⟩ := id hM
  obtain ⟨y', cols', ⟨⟨l', hl', hp'⟩, -⟩, hTr⟩ :=
    hP blk hblk k s m E ds l hT hd (chainStopAt_none _ hstop [blk] _ _) hl
  obtain rfl : l = l' := Except.ok.inj (hl.symm.trans hl')
  obtain rfl : y = y' := Except.ok.inj (hp.symm.trans hp')
  exact hTr

variable {Begun : Coins Bk → Mid W X → Prop}

/-- **The field along a walk, from PlaysS at the members in front.** -/
theorem walked_field_plays {n : Nat} {base : List OpenedColumn} (hfit : T.fits n = true)
    (hO : ∀ b, b ≤ n → T.opensAvailable b = true)
    (hD : ∀ b, b ≤ n → ∀ k m, DepthsAt T b k m) (hstop : NoStop T.hs)
    (hP : ∀ b, b < n → PlaysS T (WalkedFrom T Begun) b)
    (hBegun : ∀ k m, Begun k m → m.opened = some base) {b : Nat} {k : Coins Bk} {m : Mid W X}
    (hb : b ≤ n) (h : WalkedFrom T Begun b k m) :
    ∀ E, T.Hand b k m E → T.Field base b m E := by
  induction h with
  | begun h₀ =>
    intro E _
    exact (T.field_zero_iff base _ E).2 (hBegun _ _ h₀)
  | @next b blk k s m E ds y cols hw hblk hT hd hM ih =>
    intro E' hE'
    have hF := ih (by omega) E hT.1
    have hF₁ := T.field_next hblk hT hF hM
    obtain ⟨⟨l, hl, hp⟩, hc⟩ := id hM
    have hH := hand_next (cols := cols) hfit (by omega) hT hp
      (trees_of_plays (hP b (by omega)) hstop hblk ⟨hT, hw⟩ hd hM)
    obtain ⟨c, hc₁, ho⟩ := (field_iff T base _ _ _).1 hF₁
    refine (field_iff T base _ _ _).2 ⟨c, ?_, ho⟩
    rw [← T.colsTo_congr_at hH hE' (hO _ hb) (hD _ hb _ _)]
    exact hc₁

/-- **One run, one state, at the letter.** No premise on any member. -/
theorem oneState_walked {n : Nat} (hTaken : ∀ j, Fmt.TreeSource.own j ∉ T.taken)
    (hO : ∀ b, b ≤ n → T.opensAvailable b = true)
    (hD : ∀ b, b ≤ n → ∀ k m, DepthsAt T b k m)
    (hfun : ∀ k w hd s₀ s₁, T.begun k w hd s₀ → T.begun k w hd s₁ → s₀ = s₁)
    (hB : ∀ k m m', Begun k m → Begun k m' → m.st.input = m'.st.input →
      m.st.heard = m'.st.heard → m = m') : OneState T (WalkedFrom T Begun) n :=
  oneState_at T
    (oneStand_walked hB (oneColumns_of hTaken (fun b hb => hO (b + 1) hb) fun b hb => hD (b + 1) hb))
    hfun (hO n (Nat.le_refl n)) fun k _ m _ _ => hD n (Nat.le_refl n) k m

/-- **What the last chain's door asks of an earlier thread and its letter**, at its last border n. -/
structure DoorAsks (T : Thread Bk S Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop) (n : Nat) :
    Prop where
  /-- one run, one state of the prover's run -/
  one : OneStand Said n
  /-- one run, one state of the verifier -/
  state : OneState T Said n
  /-- at the last border the field holds what the thread's columns say, from the empty list on -/
  field : ∀ k e m E, ThrS T Said n k e m E → T.Field [] n m E
  /-- the letter is carried over every member -/
  next : ∀ b, SaidNext T Said b

/-- **All four at the letter that begins at one named state whose field is some [].** -/
theorem doorAsks_walked {n : Nat} {start : Mid W X} (hfit : T.fits n = true)
    (hTaken : ∀ j, Fmt.TreeSource.own j ∉ T.taken) (hO : ∀ b, b ≤ n → T.opensAvailable b = true)
    (hD : ∀ b, b ≤ n → ∀ k m, DepthsAt T b k m)
    (hfun : ∀ k w hd s₀ s₁, T.begun k w hd s₀ → T.begun k w hd s₁ → s₀ = s₁)
    (hstop : NoStop T.hs) (hP : ∀ b, b < n → PlaysS T (WalkedFrom T fun _ m => m = start) b)
    (ho : start.opened = some []) : DoorAsks T (WalkedFrom T fun _ m => m = start) n where
  one := oneStand_walked (fun _ _ _ h h' _ _ => h.trans h'.symm)
    (oneColumns_of hTaken (fun b hb => hO (b + 1) hb) fun b hb => hD (b + 1) hb)
  state := oneState_walked hTaken hO hD hfun fun _ _ _ h h' _ _ => h.trans h'.symm
  field := fun _ _ _ E h =>
    walked_field_plays hfit hO hD hstop hP (fun _ _ e => by rw [e]; exact ho) (Nat.le_refl n) h.2 E
      h.1.1
  next := fun b => saidNext_walked _ _ b

/-- **The letter holds at the state at which it begins.** -/
theorem enter_walked (T : Thread Bk S Cl V W X Pb) (start : Mid W X) (k : Coins Bk) :
    WalkedFrom T (fun _ m => m = start) 0 k start := .begun rfl

end AtPublicFiles.LotField

#print axioms AtPublicFiles.LotField.trees_of_plays
#print axioms AtPublicFiles.LotField.walked_field_plays
#print axioms AtPublicFiles.LotField.oneState_walked
#print axioms AtPublicFiles.LotField.doorAsks_walked
#print axioms AtPublicFiles.LotField.enter_walked
