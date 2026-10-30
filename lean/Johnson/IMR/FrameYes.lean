-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/FrameYes.lean: opened_sits (Joined → YesBehind b b' f.opened at the link's own row) · frames_sit (the frame's three at each of the 25 links, by their numbers in the flat list, at ONE row f). THE OWED INSTANCE «frames_sit» (see OBJECT) IS MET IN ITS FORM (three blocks by their numbers, at one row, the row the link's own, something always joined); WHICH FUNCTION THE ROW's opened | clear IS AT WHICH LINK IS OWED (see «What is not claimed»). It imports IM.FirstSeats; FramePlain.lean IS ONE OF THE FILES BELOW IT. opened_arms stays for its callers.
frames_sit's STATEMENT PINS b': Lk · k · c.links[l]? · Lk.hear[0]? · b'.place whole · Joined.
Where the rest of this head and the Lean text differ, the Lean text holds.
 Johnson/IMR/FrameSeat.lean's seats of the link's frame IN THE LETTERS OF Johnson/Top/H0/Walk/FramePlain.lean: YesOf | YesBehind (that file
imports Johnson/Desc/Plain/K7Law · Walk/FrameProps · Walk/FrameSized).
OBJECT. The three blocks of which frames_sit speaks: in onlineDescription's first chain's flat list «link l: laid» · the block at the link's first place · «link l: cleared».
USER. FramePlain.lean's six laws (they take YesOf | YesBehind at p.b as premises). OF THE SIX, ONE HAS ITS OBJECT BY THIS FILE: laid_law (YesOf bL f.lay with f.lay = layFront l; any Piece with p.b := bL). THE OTHER FIVE DO NOT YET: cleared_law | clearedRow_law want
YesOf p.b (clearWith X counts left row): we hand YesOf bC f.clear, and what f.clear IS stands in Johnson/IMR/FrameSeat.lean's frames_arms arm by arm, WITHOUT «which arm at which link» (and at l = 24 f.clear is the head's frame's, of which none of the six speaks); the three on «opened» want YesBehind at the
link's own row: see below. LETTERS. As in Johnson/IMR/FrameSeat.lean.

Compiled with the whole library.
THE LETTER o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): WHAT NEEDS NO SCOPE STANDS AT EVERY o; WHAT STANDS ON A LAW OF THE LIBRARY OVER «publicOf … = .ok X» STANDS AT OnBytes.secondHashFunction, where publicOfO_older (Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean) makes
publicOfO publicOf (the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7' | G7'bits (Ladder.lean · Ladder/Bits.lean) hand every o: for these the in-scope halves are owed, at PublicCut, Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean).

  laid_cleared_sit  in scope, at secondHashFunction: ∃ fs, framesOf … = ok fs ∧ ∀ l < 25, ∃ Lk f bL bC, c.links[l]? = some Lk ∧ fs[l]? = some f ∧ f.lay = layFront l ∧ c.blocksInOrder[14 l + 1]? = some bL ∧ YesOf bL f.lay ∧ c.blocksInOrder[14 l + Lk.hear.length + 7]? = some bC ∧ YesOf bC f.clear.
  opened_arms       (NO SEAT: TWO ARMS) a block that is LaidOpened of b': says yes only where b' does (alone), OR YesBehind b b' f.opened at link l's own row f. (Overtaken by opened_sits.)

What is not claimed. WHICH FUNCTION f.opened | f.clear IS AT WHICH LINK: FramePlain.lean's three laws on «opened» take YesBehind p.b first (openAtt P | openLay P | openLayZero P fvs kCol), its laws on «cleared» take clearWith …; we hand YesBehind b b' f.opened and YesOf bC f.clear: that f.opened | f.clear is one of these stands in Johnson/IMR/FrameSeat.lean's frames_arms, four arms; only the head's is settled (frames_head). SO FIVE OF FramePlain.lean's SIX LAWS WANT «which arm at which l» (a law «framesOf_at» on this framesOf is declared nowhere in this library). AT l = 24 THE MIDDLE THIRD IS EMPTY OF CONTENT: the head's row's «opened» hands the record on; the record ENTERS the head's link in K2.headFrontQ (the first half of k7Block at «H:1») and the link is OPENED in K2.headOpenQ (headOpened, the second half of the switch's block at «H:2» = links[24].hear[1]): Johnson/Top/H0/Tw/K2C/Head.lean; which of K2Is' arms holds there is not paid by this folder's seats. No soundness.
-/
import Johnson.IMR.FirstSeats
import Johnson.Top.H0.Walk.FramePlain

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Plain (YesOf YesBehind)
open ProofFile (Cl)

/-- **«laid» AND «cleared» SIT**, in FramePlain.lean's letters. -/
theorem laid_cleared_sit {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp) (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ fs, Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
    ∀ l < 25, ∃ (Lk : Link S Cl) (f : Johnson.Desc.First.Walk.Seat.LinkFrame) (bL bC : Block S Cl),
      c.links[l]? = some Lk ∧ fs[l]? = some f ∧ f.lay = Johnson.Desc.First.Walk.layFront l ∧
      c.blocksInOrder[14 * l + 1]? = some bL ∧ YesOf bL f.lay ∧
      c.blocksInOrder[14 * l + Lk.hear.length + 7]? = some bC ∧ YesOf bC f.clear := by
  obtain ⟨-, fs, hfs, h⟩ := frame_of hS hR O
  refine ⟨fs, hfs, fun l hl => ?_⟩
  obtain ⟨Lk, f, bL, -, bC, e1, -, hf, -, hlay, yL, yC, iL, -, dL, -, -, -, iC, -, dC⟩ := h l hl
  refine ⟨Lk, f, bL, bC, e1, hf, hlay, iL, fun s rs gs t hy => ?_, iC, fun s rs gs t hy => ?_⟩
  · rw [dL] at hy
    exact ((yL s t).1 hy).1
  · rw [dC] at hy
    exact ((yC s t).1 hy).1

/-- **What can be said of «opened»**, in FramePlain.lean's letters. -/
theorem opened_arms {Z : ProofFile.Pub} {l : ℕ} {b b' : Block S Cl} {a : Place}
    (h : LaidOpened Z l b b' a) :
    (∀ s rs gs t, b.decide s rs gs = .ok t → b'.decide s rs gs = .ok t) ∨
      ∃ (fs : List Johnson.Desc.First.Walk.Seat.LinkFrame)
          (f : Johnson.Desc.First.Walk.Seat.LinkFrame),
        Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
        fs[l]? = some f ∧ YesBehind b b' f.opened := by
  rcases h with h | ⟨fs, f, hfs, hf, h⟩
  · exact Or.inl fun s rs gs t hy => (alone_underR h).2 s rs gs t hy
  · refine Or.inr ⟨fs, f, hfs, hf, fun s rs gs t hy => ?_⟩
    obtain ⟨m, h1, -, h3, -⟩ := yes_with h hy
    exact ⟨m, _, _, h1, ((guardMark_yes _ m t _ _).1 h3).1⟩

/-- **«opened» SITS**, in FramePlain.lean's letters: the block at a link's first place is its lot's block with the link's own row's «opened» behind it. -/
theorem opened_sits {Z : ProofFile.Pub} {l : ℕ} {b b' : Block S Cl} {a : Place} (h : Joined Z l b b' a) :
    ∃ (fs : List Johnson.Desc.First.Walk.Seat.LinkFrame)
        (f : Johnson.Desc.First.Walk.Seat.LinkFrame),
      Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
      fs[l]? = some f ∧ YesBehind b b' f.opened := by
  obtain ⟨fs, f, hfs, hf, e⟩ := h
  refine ⟨fs, f, hfs, hf, fun s rs gs t hy => ?_⟩
  obtain ⟨m, h1, -, h3, -⟩ := yes_with e hy
  exact ⟨m, _, _, h1, ((guardMark_yes _ m t _ _).1 h3).1⟩

/-- **THE FRAME's THREE SIT, AT EACH OF THE 25 LINKS, IN SCOPE**: «laid» · the first place with «opened» behind it · «cleared», each by its number in the flat list, at ONE row f of framesOf. -/
theorem frames_sit {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp) (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ fs, Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
    ∀ l < 25, ∃ (f : Johnson.Desc.First.Walk.Seat.LinkFrame) (Lk : Link S Cl) (k : KindName)
        (bL b b' bC : Block S Cl),
      fs[l]? = some f ∧ f.lay = Johnson.Desc.First.Walk.layFront l ∧
      c.blocksInOrder[14 * l + 1]? = some bL ∧ YesOf bL f.lay ∧
      c.links[l]? = some Lk ∧ Lk.hear[0]? = some b ∧ c.blocksInOrder[14 * l + 2]? = some b ∧
      (VerifiableInference.Desc.First.kindsBeforeBatching (subAt l) (l == 0))[0]? = some k ∧
      (∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks Bs.G₀) ∧
      b'.place = { chain := 1, link := some l, piece := 1, kind := k } ∧
      Joined Z l b b' { chain := 1, link := some l, piece := 1, kind := k } ∧
      YesBehind b b' f.opened ∧
      c.blocksInOrder[14 * l + (if l = 24 then 9 else 7) + 7]? = some bC ∧ YesOf bC f.clear := by
  obtain ⟨-, fs, hfs, h⟩ := frame_of hS hR O
  refine ⟨fs, hfs, fun l hl => ?_⟩
  obtain ⟨Lk, f, bL, -, bC, e1, hn, hf, -, hlay, yL, yC, iL, -, dL, -, -, -, iC, -, dC⟩ := h l hl
  obtain ⟨k, hk⟩ : ∃ k, (VerifiableInference.Desc.First.kindsBeforeBatching (subAt l) (l == 0))[0]? = some k := by
    unfold subAt
    split
    · exact ⟨_, rfl⟩
    · split <;> cases (l == 0) <;> exact ⟨_, rfl⟩
  obtain ⟨Lk', b, e1', e2, L, hL, b', hb', ep, hj⟩ := first_sits hS hR O l hl k hk
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain ⟨fs', f', hfs', hf', yB⟩ := opened_sits hj
  obtain rfl : fs = fs' := Except.ok.inj (hfs.symm.trans hfs')
  obtain rfl : f = f' := Option.some.inj (hf.symm.trans hf')
  have iB := hear_at_flat e1 e2
  rw [flatIx_scope hS hR O (by omega) 0] at iB
  rw [hn] at iC
  refine ⟨f, Lk, k, bL, b, b', bC, hf, hlay, iL, fun s rs gs t hy => ?_, e1, e2, iB, hk,
    ⟨L, hL, hb'⟩, ep, hj, yB, iC, fun s rs gs t hy => ?_⟩
  · rw [dL] at hy
    exact ((yL s t).1 hy).1
  · rw [dC] at hy
    exact ((yC s t).1 hy).1

end IM

#print axioms IM.opened_sits
#print axioms IM.frames_sit
#print axioms IM.laid_cleared_sit
#print axioms IM.opened_arms
