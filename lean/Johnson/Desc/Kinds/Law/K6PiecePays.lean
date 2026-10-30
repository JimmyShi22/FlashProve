-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6PiecePays.lean: two premises of the law of the output head's own rounds at
a piece (Johnson/Desc/Kinds/Law/K6Cut.lean: k6OwnCutBy), paid from the seated block's own test on
the plan: every round's logN is at most 64; and the piece's errors bear the numbers asked. Who calls
them: Johnson/Desc/Kinds/Law/K6CutPaid.lean [not in this library]: k6OwnCutByPaid.

What the file holds. W: a public part. b: the block that the description seats
(seatedClaims W l ms = some b), whose test on the plan says yes. p: a piece, AT ANY TYPES of carried
records and of claims: of its block the file reads the declared rounds alone.
  seated_lt        1 <= lt <= 2 ^ 60 at W's sizes.
  seated_entries   the entries of b's declared rounds are the planner's list of the head's own
                   rounds (OnBytes.Tie.Pv.Head.headOwnList), at W's bits of work and sizes.
  own_logN         every entry of that list has logN at most 64.
  along_same       written rounds that are the declared ones round by round (Along (RoundIs num),
                   Johnson/Desc/Sound/Stretch.lean), and as many, have their entries, in order; and
                   each one's kind is the kind of its entry's name.
  logN_of, err_of  the two premises, from: hE (the written rounds have the entries of b's declared
                   rounds), hn (each one's kind is its name's), herr (the errors are the cap's row).
  pays_logN        **for all d in toRDs p.ds: d.entry.logN <= 64.**
  pays_err         **ErrBears (ckP .two) (fun j => kitK (toRDs p.ds) j *
                   (priceAt (parOf W.hS (workOf W)) j * kitFs .two (toRDs p.ds) j)) (toRDs p.ds) 0
                   p.err.**
What pays_logN and pays_err ask of the piece, each with who pays it elsewhere.
  hr    p.b.rounds = b.rounds: the piece's block declares b's rounds. So it holds of "below b"
        (rounds_below), and of b lifted, guarded or renamed, wherever that keeps the rounds.
  hback no round is put back: a premise of k6OwnCutBy already.
  hlen  the stretch has as many rounds as the block declares, less those put back: the first count
        of Piece.Owed (Johnson/Desc/Sound/ChainRule.lean); fitsOfData pays it at the maker's pieces.
  hA    Along (RoundIs num) p.b.rounds p.ds: stretchOfData (Johnson/Desc/Sound/Stretch.lean) pays it
        at every piece that the maker cuts, for every description F with F.data file = .ok D.
  herr  p.err = Err.cap 128 _ (pays_err alone): the filling restCap
        (Johnson/Desc/Sound/BoundsAtCap.lean: AtCap) lays that row at every piece.

What it does not give. Nothing on soundness by itself. No piece of the seated description is named
here: that the block which the maker's piece holds at the head's place (lifted to a pair:
Johnson/Desc/Sound/PaidAtDesc.lean: held; under the chain's guards) declares b's rounds is hr: the
caller's. The field is .two alone. 128 bits a round; no sum over the rounds.

-/
import Johnson.Desc.Kinds.Law.K06Bears
import Johnson.Desc.Kinds.Law.SeatedSays
import Johnson.Desc.Sound.Stretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.PiecePays

open OnBytes.Maker (toRDs uLT RDT)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Piece Frame ErrBears kitK kitFs Along RoundIs)
open _root_.Iop (Err)
open Prices (recAt)
open Norm (lt lPd)

variable {W : OnBytes.Model.Verify.Public} {l : Nat} {ms : List (Nat × Nat)} {b : Block S Claim}

/-- 1 <= lt <= 2 ^ 60, from the seated block's test on the plan. -/
theorem seated_lt (h : seatedClaims W l ms = some b) (hp : b.planOk = true) :
    letI := (parOf W.hS (workOf W)).sizes
    1 ≤ lt ∧ lt ≤ 2 ^ 60 := by
  obtain ⟨_, hl⟩ := seatedClaims_plan h hp
  rw [laidOk_is] at hl
  obtain ⟨_, a2, a3, _, _, _, _, _, a9, _⟩ := laid_says _ _ hl
  refine ⟨a2, ?_⟩
  show W.hS.lt ≤ 2 ^ 60
  have : (63 : Nat) ≤ 2 ^ 60 := by norm_num
  omega

/-- **The seated block's declared rounds have the planner's entries.** -/
theorem seated_entries (h : seatedClaims W l ms = some b) (hp : b.planOk = true) :
    letI := (parOf W.hS (workOf W)).sizes
    b.rounds.map (·.entry) = OnBytes.Tie.Pv.Head.headOwnList (workOf W) (recAt lt lPd) := by
  letI := (parOf W.hS (workOf W)).sizes
  have h1 := (seated_lt h hp).1
  obtain ⟨b0, h0, rfl⟩ := seatedClaims_some h
  unfold blockClaims at h0
  obtain ⟨iU3, _, rfl⟩ := Option.map_eq_some_iff.mp h0
  rw [tested_rounds]
  show ((rounds.map fun R => ({ entry := R.entry (workOf W) } : Fmt.DeclaredRound)).map (·.entry)) = _
  rw [List.map_map]
  exact Prices.k6_entries (workOf W) h1

/-- Every entry of the planner's list has logN at most 64. -/
theorem own_logN (lt lPd w : Nat) (e : Fmt.Entry)
    (he : e ∈ OnBytes.Tie.Pv.Head.headOwnList w (recAt lt lPd)) : e.logN ≤ 64 := by
  rw [← Below.k6Priced_entries] at he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  have e : Below.k6Priced lt lPd w =
      (OnBytes.Tie.Pv.Lay.eDraw "ZERO" w 0 lt, lt * Below.q ^ (lt - 1)) ::
        (Below.k6Priced lt lPd w).tail := rfl
  rw [e] at hx
  rcases List.mem_cons.mp hx with rfl | hx
  · simp [OnBytes.Tie.Pv.Lay.eDraw]
  · exact (Bears.tail_small lt lPd w x hx).log

variable {Fr : Frame} {S' Cl' Wt : Type} (p : Piece (_root_.Run.ckP .two) Fr S' Cl' Wt)

/-- Every written round's logN is at most 64: from the entries. -/
theorem logN_of (h : seatedClaims W l ms = some b) (hp : b.planOk = true)
    (hE : (toRDs p.ds).map (·.entry) = b.rounds.map (·.entry)) :
    ∀ d, d ∈ toRDs p.ds → d.entry.logN ≤ 64 := by
  intro d hd
  letI := (parOf W.hS (workOf W)).sizes
  refine own_logN lt lPd (workOf W) d.entry ?_
  rw [← seated_entries h hp, ← hE]
  exact List.mem_map_of_mem hd

/-- The cap's row bears the numbers asked: from the entries and the kinds. -/
theorem err_of (h : seatedClaims W l ms = some b) (hp : b.planOk = true)
    (hE : (toRDs p.ds).map (·.entry) = b.rounds.map (·.entry))
    (hn : ∀ d ∈ toRDs p.ds, Fmt.kindOf d.entry.name = some d.kind)
    (herr : p.err = Err.cap 128 (uLT (_root_.Run.ckP .two) p.ds)) :
    ErrBears (_root_.Run.ckP .two)
      (fun j => kitK (toRDs p.ds) j *
        (priceAt (parOf W.hS (workOf W)) j * kitFs .two (toRDs p.ds) j)) (toRDs p.ds) 0 p.err := by
  rw [herr]
  exact Bears.k06BearsCapNames (parOf W.hS (workOf W)) (workOf W) (toRDs p.ds) (seated_lt h hp).1
    (seated_lt h hp).2 (hE.trans (seated_entries h hp)) hn

/-- Written rounds that are the declared ones, round by round, and as many. -/
theorem along_same (num : Fmt.TreeSource → Nat) : ∀ (rs : List Fmt.DeclaredRound) (ds : List RDT),
    Along (RoundIs num) rs ds → ds.length = rs.length →
      (toRDs ds).map (·.entry) = rs.map (·.entry) ∧
        ∀ d ∈ toRDs ds, Fmt.kindOf d.entry.name = some d.kind
  | [], [], _, _ => ⟨rfl, fun _ hd => by cases hd⟩
  | [], _ :: _, _, hl => by cases hl
  | _ :: _, [], _, hl => by cases hl
  | r :: rs, d :: ds, hA, hl => by
    obtain ⟨⟨a1, a2, _⟩, hA'⟩ : RoundIs num r d ∧ Along (RoundIs num) rs ds := hA
    obtain ⟨i1, i2⟩ := along_same num rs ds hA' (Nat.succ.inj hl)
    refine ⟨?_, ?_⟩
    · show d.entry :: (toRDs ds).map (·.entry) = r.entry :: rs.map (·.entry)
      rw [a1, i1]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · show Fmt.kindOf d.entry.name = some d.kind
        rw [a1]
        exact a2
      · exact i2 x hx

/-- What the two ask of the piece gives hE and hn. -/
theorem same_of_piece (hr : p.b.rounds = b.rounds) (hback : p.back = [])
    (hlen : p.ds.length + p.back.length = p.b.rounds.length) {num : Fmt.TreeSource → Nat}
    (hA : Along (RoundIs num) p.b.rounds p.ds) :
    (toRDs p.ds).map (·.entry) = b.rounds.map (·.entry) ∧
      ∀ d ∈ toRDs p.ds, Fmt.kindOf d.entry.name = some d.kind := by
  rw [hback, List.length_nil, Nat.add_zero, hr] at hlen
  rw [hr] at hA
  exact along_same num _ _ hA hlen

/-- **Every written round's logN is at most 64.** -/
theorem pays_logN (h : seatedClaims W l ms = some b) (hp : b.planOk = true)
    (hr : p.b.rounds = b.rounds) (hback : p.back = [])
    (hlen : p.ds.length + p.back.length = p.b.rounds.length) {num : Fmt.TreeSource → Nat}
    (hA : Along (RoundIs num) p.b.rounds p.ds) : ∀ d, d ∈ toRDs p.ds → d.entry.logN ≤ 64 :=
  logN_of p h hp (same_of_piece p hr hback hlen hA).1

/-- **The cap's row bears the numbers asked.** -/
theorem pays_err (h : seatedClaims W l ms = some b) (hp : b.planOk = true)
    (hr : p.b.rounds = b.rounds) (hback : p.back = [])
    (hlen : p.ds.length + p.back.length = p.b.rounds.length) {num : Fmt.TreeSource → Nat}
    (hA : Along (RoundIs num) p.b.rounds p.ds)
    (herr : p.err = Err.cap 128 (uLT (_root_.Run.ckP .two) p.ds)) :
    ErrBears (_root_.Run.ckP .two)
      (fun j => kitK (toRDs p.ds) j *
        (priceAt (parOf W.hS (workOf W)) j * kitFs .two (toRDs p.ds) j)) (toRDs p.ds) 0 p.err :=
  err_of p h hp (same_of_piece p hr hback hlen hA).1 (same_of_piece p hr hback hlen hA).2 herr

/-- The device "below" keeps a block's declared rounds. -/
theorem rounds_below {σ Cl : Type} (c : Block σ Cl) : (Sound.below c).rounds = c.rounds := rfl

end VerifiableInference.Desc.Kinds.Head.Law.PiecePays

#print axioms VerifiableInference.Desc.Kinds.Head.Law.PiecePays.seated_entries
#print axioms VerifiableInference.Desc.Kinds.Head.Law.PiecePays.pays_logN
#print axioms VerifiableInference.Desc.Kinds.Head.Law.PiecePays.pays_err
