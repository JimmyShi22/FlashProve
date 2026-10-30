--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H0/MergeLaw/PieceOut.lean: when a piece's reduction puts out: the way back from
`piece_yes` (Johnson/Top/H0/MergeLaw/AtPiece.lean). General in the block: no kind is named. Theorems
with their proofs.

A piece (Johnson/Desc/Sound/ChainRule.lean) is one block of the description run over its written
rounds. `piece_yes` says what a yes of its reduction holds. A law of the form "whatever the verifier
puts out, …" asks nothing where the verifier never puts out: so a member wants the way back. It is
no converse to the letter: `piece_yes` concludes four things; `piece_out` asks six, which are more.

Main names:
  `chainAt_one_of`: the chain's fold at a list of one block says yes where the stretch has just the
    block's number of rounds, the block's step says yes at all the rounds, and the step takes all
    the columns. The way back from `chainAt_one`.
  `piece_out`: at a piece whose block is `below b` and behind whose rounds nothing is shown: where
    (1) the stage's tests pass (`sTests`: the work; no part of a round's draws is shortened; a leaf
    read of the stored table carries its own position), (2) the transcript shows as many rounds as b
    declares, (3) `Block.Fits`: the rounds fit, and the view's next columns are those that b wants,
    (4) these are all the columns that the view opens, (5) every word shown is below the prime,
    (6) b's decision says yes with s': the reduction puts out s' with the strings that the stage
    leaves.

  `wantsOf_quiet`, `fullOf_quiet`, `groupsOf_quiet`: rounds that open no tree and no stored table
  ask
    for no column, and their test on the parts of the draws passes.
  `piece_out_quiet`: for a block that reads no oracle the six come down to four: the work's tests
    pass; the rounds fit (`roundsFit`); every word shown is below the prime; b's decision says yes.

Limits. The premises are shown of no block and no transcript here. No random step. Nothing on
soundness or on hiding.

-/
import Johnson.Top.H0.StepLaws.StepLaws
import Johnson.Desc.Sound.ChainRule

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open Iop IOR
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc (Block roundsFit noDigest viewWordsBelowPrime chainAt foldBlocks step_iff groupsOf
  regroup roundsFit_length)
open VerifiableInference.Desc.Sound (Frame Piece below foldRun)
open _root_.Run (ckP)

/-- The chain's fold at one block says yes where the block's step does at all the rounds, the
stretch has just the block's number of rounds, and the step takes all the columns. -/
theorem chainAt_one_of {S Cl : Type} (name : String) (ft : Nat) (b : Block S Cl) (s s' : S)
    (v : Fmt.View) (k : Nat) (hlen : v.rounds.length = b.rounds.length)
    (hs : b.step ft s v.rounds v.opened = .ok (s', k)) (hk : v.opened.drop k = []) :
    chainAt name ft [b] s v = .ok s' := by
  unfold chainAt
  simp only [List.isEmpty_cons, Bool.false_eq_true, if_false]
  have e1 : v.rounds.take b.rounds.length = v.rounds := List.take_of_length_le (by omega)
  have e2 : v.rounds.drop b.rounds.length = [] := List.drop_eq_nil_iff.2 (by omega)
  have hf : foldBlocks ft [b] s v.rounds v.opened = .ok (s', [], []) := by
    unfold foldBlocks
    simp only [List.splitAt_eq, e1, e2, hlen, ne_eq, not_true_eq_false, if_false, hs]
    unfold foldBlocks
    rw [hk]
  rw [hf]

variable {F : Frame} {W : Type}

/-- **WHEN THE PIECE's REDUCTION PUTS OUT**: the way back from `piece_yes`. -/
theorem piece_out {S Cl : Type} (b : Block S Cl) (p : Piece (ckP .two) F S Cl W)
    (hb : p.b = below b) (hback : p.back = []) (a : S × F.E.Str) (τ : Tr (uLT (ckP .two) p.ds))
    (s' : S) (ht : sTests (ckP .two) p.stage a.2 τ = true)
    (hlen : (rvT (ckP .two) p.ds τ).length = b.rounds.length)
    (hfit : b.Fits F.ft (rvT (ckP .two) p.ds τ) (sView (ckP .two) p.stage a.2 τ).opened)
    (hall : (sView (ckP .two) p.stage a.2 τ).opened.drop
      (b.want F.ft (rvT (ckP .two) p.ds τ)).length = [])
    (hw : viewWordsBelowPrime ⟨(rvT (ckP .two) p.ds τ).map noDigest,
                  ((b.shown F.ft (rvT (ckP .two) p.ds τ) (sView (ckP .two) p.stage a.2 τ).opened).flatMap
                    id).map fun c => (0, c.1, c.2)⟩ = true)
    (hdec : b.decide a.1 ((rvT (ckP .two) p.ds τ).map noDigest)
      (b.shown F.ft (rvT (ckP .two) p.ds τ) (sView (ckP .two) p.stage a.2 τ).opened) = .ok s') :
    p.ior.red.out a τ = some (s', p.ior.imp a.2 τ) := by
  show (if sTests (ckP .two) p.stage a.2 τ = true
      then p.run a.1 (sView (ckP .two) p.stage a.2 τ) else none).map
        (fun xo => (xo, p.ior.imp a.2 τ)) = some (s', p.ior.imp a.2 τ)
  rw [if_pos ht]
  have hstep : (below b).step F.ft a.1 (rvT (ckP .two) p.ds τ)
      (sView (ckP .two) p.stage a.2 τ).opened =
        .ok (s', (b.want F.ft (rvT (ckP .two) p.ds τ)).length) := by
    refine (step_iff _ _ _ _ _ _ _).2 ⟨hfit, ?_, rfl⟩
    show (if viewWordsBelowPrime ⟨(rvT (ckP .two) p.ds τ).map noDigest,
                    ((b.shown F.ft (rvT (ckP .two) p.ds τ) (sView (ckP .two) p.stage a.2 τ).opened).flatMap
                      id).map fun c => (0, c.1, c.2)⟩ = true
        then b.decide a.1 ((rvT (ckP .two) p.ds τ).map noDigest)
          (b.shown F.ft (rvT (ckP .two) p.ds τ) (sView (ckP .two) p.stage a.2 τ).opened)
        else .error "a word is not below the prime") = .ok s'
    rw [if_pos hw]
    exact hdec
  have hc : chainAt p.b.name F.ft [p.b] a.1
      ⟨(sView (ckP .two) p.stage a.2 τ).rounds ++ p.back,
        (sView (ckP .two) p.stage a.2 τ).opened⟩ = .ok s' := by
    rw [hb, hback, List.append_nil]
    exact chainAt_one_of _ _ _ _ _ _ _ hlen hstep hall
  show ((chainAt p.b.name F.ft [p.b] a.1
      ⟨(sView (ckP .two) p.stage a.2 τ).rounds ++ p.back,
        (sView (ckP .two) p.stage a.2 τ).opened⟩).toOption).map
          (fun xo => (xo, p.ior.imp a.2 τ)) = some (s', p.ior.imp a.2 τ)
  rw [hc]
  rfl

/-! ## A block that reads no oracle -/

/-- Written rounds that open nothing ask for nothing. -/
theorem wantsOf_quiet (a : ℕ) (dep : ℕ → Option ℕ) : ∀ (ds : List RDT) (Rs : List Fmt.Drawn),
    (∀ d ∈ ds, d.stored = [] ∧ d.opens = []) → wantsOf a dep ds Rs = []
  | [], _, _ => by simp [wantsOf]
  | _ :: _, [], _ => by simp [wantsOf]
  | d :: ds, R :: Rs, h => by
    have hd := h d (by simp)
    simp [wantsOf, hd.1, hd.2, wantsOf_quiet a dep ds Rs fun x hx => h x (by simp [hx])]

theorem fullOf_quiet : ∀ (ds : List RDT) (Rs : List Fmt.Drawn),
    (∀ d ∈ ds, d.stored = [] ∧ d.opens = []) → fullOf ds Rs = true
  | [], _, _ => by simp [fullOf]
  | _ :: _, [], _ => by simp [fullOf]
  | d :: ds, R :: Rs, h => by
    have hd := h d (by simp)
    simp [fullOf, hd.1, fullOf_quiet ds Rs fun x hx => h x (by simp [hx])]

/-- Declared rounds that open nothing are owed no column. -/
theorem groupsOf_quiet (ft : ℕ) : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    (∀ d ∈ ds, d.stored = [] ∧ d.opens = []) → groupsOf ft ds Rs = []
  | [], _, _ => by simp [groupsOf]
  | _ :: _, [], _ => by simp [groupsOf]
  | d :: ds, R :: Rs, h => by
    have hd := h d (by simp)
    simp [groupsOf, hd.1, hd.2, groupsOf_quiet ft ds Rs fun x hx => h x (by simp [hx])]

/-- **WHEN THE PIECE OF A BLOCK THAT READS NO ORACLE PUTS OUT**: the work's tests pass, the rounds
fit, every word shown is below the prime, and the decision says yes. -/
theorem piece_out_quiet {S Cl : Type} (b : Block S Cl) (p : Piece (ckP .two) F S Cl W)
    (hb : p.b = below b) (hback : p.back = [])
    (hq : ∀ d ∈ p.ds, d.stored = [] ∧ d.opens = [])
    (hqb : ∀ d ∈ b.rounds, d.stored = [] ∧ d.opens = [])
    (a : S × F.E.Str) (τ : Tr (uLT (ckP .two) p.ds)) (s' : S)
    (hp : passT (ckP .two) p.ds (rhoT (ckP .two) p.ds τ) = true)
    (hfit : roundsFit b.rounds (rvT (ckP .two) p.ds τ) = true)
    (hw : viewWordsBelowPrime ⟨(rvT (ckP .two) p.ds τ).map noDigest, []⟩ = true)
    (hdec : b.decide a.1 ((rvT (ckP .two) p.ds τ).map noDigest) [] = .ok s') :
    p.ior.red.out a τ = some (s', p.ior.imp a.2 τ) := by
  have hwant : sWants (ckP .two) p.stage (rhoT (ckP .two) p.ds τ) = [] :=
    wantsOf_quiet _ _ _ _ hq
  have hop : (sView (ckP .two) p.stage a.2 τ).opened = [] := by
    show ((sWants (ckP .two) p.stage (rhoT (ckP .two) p.ds τ)).filterMap _) = []
    rw [hwant]
    rfl
  have hg : groupsOf F.ft b.rounds ((rvT (ckP .two) p.ds τ).map (·.drawn)) = [] :=
    groupsOf_quiet _ _ _ hqb
  have hwn : b.want F.ft (rvT (ckP .two) p.ds τ) = [] := by
    unfold Block.want
    rw [hg]
    rfl
  have hsh : b.shown F.ft (rvT (ckP .two) p.ds τ) (sView (ckP .two) p.stage a.2 τ).opened = [] := by
    unfold Block.shown
    rw [hg]
    rfl
  refine piece_out b p hb hback a τ s' ?_ (roundsFit_length _ _ hfit) ⟨hfit, ?_⟩ ?_ ?_ ?_
  · unfold sTests
    rw [hp, fullOf_quiet _ _ hq, hwant]
    rfl
  · rw [hwn, hop]
    rfl
  · rw [hop]
    exact List.drop_nil
  · rw [hsh]
    exact hw
  · rw [hsh]
    exact hdec

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.piece_out_quiet
#print axioms VerifiableInference.Desc.First.MergeLaw.chainAt_one_of
#print axioms VerifiableInference.Desc.First.MergeLaw.piece_out
