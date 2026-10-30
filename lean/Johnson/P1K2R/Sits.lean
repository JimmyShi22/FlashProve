-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/Sits.lean (over the proof
file's description and the seats of Johnson/IMR/): THE ROW
«K02_sits»: in the proof file's written description the entry of the list of blocks at each place of
the kind «the code switch» is the constant of which the kind's laws speak, at the plan's numbers,
under the seat's wrappers alone; and its yes gives that constant's yes. NO BLOCK IMPORTS THIS FILE.
THE CONSTANT: VerifiableInference.Desc.First.K2.decideWith sendByL8 p, the decision of K2.codeSwitchKind p (by
rfl: K2C/Fields.lean's k2_decide), at p := IM.k2P Z a nm st n: the lot's own numbers: n by
P1K2.prepOf Z G₀ = some P and P1K2.numsAt P a.link = some n.
WHOSE IS WHAT. Which block of onlineDescription's own chain stands at the kind's place, and that
it is a member x of the lot's table under the seat's two wrappers (LaidAlone; at a link's
first place Joined: with the link's own «opened» joined behind), and what x is (K2Is):
OTHER FILES' (Johnson/IMR/K2Seat.lean: k2_head_of · k2_finish_of; FirstSeats.lean:
k2_link_sits; FlatIx | FlatScope: the number in the flat list): CALLED. THIS FILE's: the
two things that K2Seat.lean's head names as not shown (that x is no mute; which of the
dresses), and the way from a yes of the seated block to the constant's yes.
  is_planOk      K2Is and x's yes on the plan: x is no mute: the numbers and one of the three
                 dresses
  yes_of_is      K2Is and a yes of x: the numbers, and by the dress: behind the links:
                 "F.0.front"'s yes, THE CONSTANT's YES at «finish», "F.0.quiet"'s yes · in a link,
                 at a record that stands in the head's link: THE CONSTANT's YES at «head», then
                 "H.1.quiet"'s yes · in a link, at a record that stands between the links: THE
                 CONSTANT's YES at «link». WHICH DRESS IS TOLD BY WHERE THE RECORD STANDS
                 (K2C/StandsBy.lean)
  k02_sits       in the goals' scope, where onlineDescription returns F at the second hash function: F's
                 first chain c: at each link 1 ≤ l < 24 the flat list's entry number 14 l + 2, at
                 the head's link the entry number 14 · 24 + 3, and the first block behind the links:
                 each is a member x of the lot's table under the wrappers, K2Is at its address
  yes_alone_gives · yes_joined_gives   a yes of the SEATED (guarded) block at these places gives
                                       yes_of_is's right side for x, no mark behind the switch; at
                                       a link the link's own «opened» (f.opened, f the l-th row of
                                       framesOf) says yes from the switch's record on, no mark,
                                       the reply as it was
  yes_framed_gives   the elder, weaker form at a link (alone, or with some block joined behind):
                     kept for whoever calls it
LIMITS. ONE DIRECTION: from the seated block's yes. In scope and at OnBytes.secondHashFunction alone for the
links and the head (the seats' own bound); the finish at every o. That the record stands between
the links in front of a link's first place is the frame's law, not shown here: where it does not,
the constant refuses (its guard [B2]). The kind's law on soundness is another file's; nothing here
says that it holds. No soundness is claimed.
-/
import Johnson.IMR.K2Seat
import Johnson.IMR.FlatScope
import Johnson.IMR.FirstSeats
import Johnson.Top.H0.Tw.K2C.StandsBy
import Johnson.Top.H0.Tw.K2C.Reply

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName roundlessBlock)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 At codeSwitchKind finishPlace headOpened decideWith finishFrontQ
  finishBehindQ headOpenQ HeadPar)
open _root_.Tw.K2 (sendByL8)
open ProofFile (Cl)
open IM (K2Is k2P under LaidAlone LaidFramed Joined Open)

/-- The three dresses, without the mute. -/
def Dressed (Z : ProofFile.Pub) (G : ProofFile.Ground) (a : Place) (nm : String) (x : Block S Unit) : Prop :=
  ∃ P n, prepOf Z G = some P ∧ numsAt P a.link = some n ∧
    ((a.link = none ∧ x = under nm a (finishPlace (k2P Z a nm .finish n))) ∨
      (∃ l HP, a.link = some l ∧ pureLetters G l = some HP ∧
        x = under nm a ((codeSwitchKind (k2P Z a nm .head n) : Block S Unit).andThen nm (headOpened nm a HP))) ∨
      (∃ l, a.link = some l ∧ x = under nm a (codeSwitchKind (k2P Z a nm .link n))))

theorem is_planOk {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : Place} {nm : String} {x : Block S Unit}
    (h : K2Is Z G a nm x) (hp : x.planOk = true) : Dressed Z G a nm x := by
  rcases h with ⟨hm, _⟩ | h
  · rw [hm] at hp
    cases hp
  · exact h

theorem is_yes {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : Place} {nm : String} {x : Block S Unit}
    (h : K2Is Z G a nm x) {s t : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hy : x.decide s rs gs = .ok t) : Dressed Z G a nm x := by
  rcases h with ⟨_, hm⟩ | h
  · obtain ⟨e, he⟩ := hm s rs gs
    rw [he] at hy
    cases hy
  · exact h

/-- What a yes of a member of the lot's table gives. -/
def YesGives (Z : ProofFile.Pub) (G : ProofFile.Ground) (a : Place) (nm : String) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) : Prop :=
  ∃ P n, prepOf Z G = some P ∧ numsAt P a.link = some n ∧
    ((a.link = none ∧ ∃ s₁ s₂ rs' gs', finishFrontQ s = .ok s₁ ∧
        decideWith sendByL8 (k2P Z a nm .finish n) s₁ rs' gs' = .ok s₂ ∧ finishBehindQ s₂ = .ok t) ∨
      (∃ l HP m rs' gs' h, a.link = some l ∧ pureLetters G l = some HP ∧ s.here = .head h ∧
        decideWith sendByL8 (k2P Z a nm .head n) s rs' gs' = .ok m ∧ headOpenQ HP m = .ok t) ∨
      (∃ l, a.link = some l ∧ s.here = .between ∧
        decideWith sendByL8 (k2P Z a nm .link n) s rs gs = .ok t))

theorem yes_of_is {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : Place} {nm : String} {x : Block S Unit}
    (h : K2Is Z G a nm x) {s t : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hy : x.decide s rs gs = .ok t) : YesGives Z G a nm s t rs gs := by
  obtain ⟨P, n, hP, hn, h⟩ := is_yes h hy
  refine ⟨P, n, hP, hn, ?_⟩
  rcases h with ⟨ha, rfl⟩ | ⟨l, HP, ha, hH, rfl⟩ | ⟨l, ha, rfl⟩
  · refine Or.inl ⟨ha, ?_⟩
    simp only [under, finishPlace, Block.andThen, roundlessBlock] at hy
    obtain ⟨s₂, h₂, h₃⟩ := VerifiableInference.Desc.First.K2.bindOk hy
    obtain ⟨s₁, h₁, h₂⟩ := VerifiableInference.Desc.First.K2.bindOk h₂
    exact ⟨s₁, s₂, _, _, h₁, h₂, h₃⟩
  · refine Or.inr (Or.inl ?_)
    simp only [under, Block.andThen] at hy
    obtain ⟨m, h₁, h₂⟩ := VerifiableInference.Desc.First.K2.bindOk hy
    have h₁' : decideWith sendByL8 (k2P Z a nm .head n) s _ _ = .ok m := h₁
    obtain ⟨hd, hh⟩ := VerifiableInference.Desc.First.K2.head_of_stands h₁' rfl
    exact ⟨l, HP, m, _, _, hd, ha, hH, hh, h₁', h₂⟩
  · refine Or.inr (Or.inr ⟨l, ha, ?_, hy⟩)
    exact VerifiableInference.Desc.First.K2.between_of_link
      (show decideWith sendByL8 (k2P Z a nm .link n) s rs gs = .ok t from hy) rfl

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}

/-- **THE ROW K02_sits.** -/
theorem k02_sits (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) :
    ∃ Z Bs base c A B, Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B ∧
      (∀ l, 1 ≤ l → l < 24 → ∃ (b : Block S Cl) (x : Block S Unit),
        c.blocksInOrder[14 * l + 0 + 2]? = some b ∧ x ∈ pureTable (fun _ _ => some none) Z Bs.G₀ ∧
        Joined Z l b x.retype { chain := 1, link := some l, piece := 1, kind := .K2 } ∧
        K2Is Z Bs.G₀ { chain := 1, link := some l, piece := 1, kind := .K2 } x.name x) ∧
      (∃ (b : Block S Cl) (x : Block S Unit),
        c.blocksInOrder[14 * 24 + 1 + 2]? = some b ∧ x ∈ pureTable (fun _ _ => some none) Z Bs.G₀ ∧
        LaidAlone ProofFile.sameReply b x.retype b.name
          { chain := 1, link := some 24, piece := 2, kind := .K2 } ∧
        K2Is Z Bs.G₀ { chain := 1, link := some 24, piece := 2, kind := .K2 } x.name x) ∧
      (∃ (b : Block S Cl) (x : Block S Unit),
        c.back[0]? = some b ∧ x ∈ pureTable (fun _ _ => some none) Z Bs.G₀ ∧
        LaidAlone ProofFile.sameReply b x.retype b.name IM.k2PlaceF ∧
        K2Is Z Bs.G₀ IM.k2PlaceF x.name x) := by
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := IM.seat_open hF
  refine ⟨Z, Bs, base, c, A, B, O, fun l h1 h24 => ?_, ?_, ?_⟩
  · obtain ⟨Lk, b, x, e1, e2, hx, hl, hi⟩ := IM.k2_link_sits hS hR O l h1 h24
    have hf := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope hS hR O (by omega) 0] at hf
    exact ⟨b, x, hf, hx, hl, hi⟩
  · obtain ⟨Lk, b, x, e1, e2, hx, hl, hi⟩ := IM.k2_head_of hS hR O
    have hf := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope hS hR O (by omega) 1] at hf
    exact ⟨b, x, hf, hx, hl, hi⟩
  · obtain ⟨b, x, e1, hx, ep, hl, _⟩ := IM.k2_finish_of O
    have hi := IM.k2_mem hx
    rw [ep] at hi
    exact ⟨b, x, e1, hx, hl, hi⟩

end

/-- A yes of the seated block where it stands alone (the head's link; the finish). -/
theorem yes_alone_gives {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : Place} {b : Block S Cl}
    {x : Block S Unit} (hl : LaidAlone ProofFile.sameReply b x.retype b.name a)
    (hk : a.kind ≠ KindName.K7) (hi : K2Is Z G a x.name x) {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hy : b.decide s rs gs = .ok t) :
    YesGives Z G a x.name s t rs gs ∧ t.failed = none ∧ s.out.reply = t.out.reply := by
  obtain ⟨h1, h2, h3⟩ := (IM.yes_alone hl hk s t rs gs).1 hy
  exact ⟨yes_of_is hi (show x.decide s rs gs = .ok t from h1), h2, IM.sameReply_eq h3⟩

/-- A yes of the seated block at a link's first place: alone, or with a block joined behind. -/
theorem yes_framed_gives {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : Place} {b : Block S Cl}
    {x : Block S Unit} (hl : LaidFramed Z b x.retype b.name a) (hi : K2Is Z G a x.name x) {s t : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (hy : b.decide s rs gs = .ok t) :
    (YesGives Z G a x.name s t rs gs ∧ t.failed = none) ∨
      ∃ (q : Block S Cl) (m : S) (rs' rs'' : List Fmt.RoundView) (gs' gs'' : List (List (Nat × List
                 UInt64))),
        YesGives Z G a x.name s m rs' gs' ∧ m.failed = none ∧ q.decide m rs'' gs'' = .ok t := by
  rcases IM.yes_laid hl.laid hy with ⟨_, h1, h2⟩ | ⟨q, m, _, h1, h2, h3, _⟩
  · exact Or.inl ⟨yes_of_is hi (show x.decide s rs gs = .ok t from h1), h2⟩
  · exact Or.inr ⟨q, m, _, _, _, _, yes_of_is hi (show x.decide s _ _ = .ok m from h1), h2, h3⟩

/-- A yes of the seated block at a link's first place: the switch, then the link's own «opened». -/
theorem yes_joined_gives {Z : ProofFile.Pub} {G : ProofFile.Ground} {l : Nat} {a : Place} {b : Block S Cl}
    {x : Block S Unit} (hl : Joined Z l b x.retype a) (hi : K2Is Z G a x.name x) {s t : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (hy : b.decide s rs gs = .ok t) :
    ∃ (fs : List Johnson.Desc.First.Walk.Seat.LinkFrame)
      (f : Johnson.Desc.First.Walk.Seat.LinkFrame) (m : S) (rs' : List Fmt.RoundView)
      (gs' : List (List (Nat × List UInt64))),
      Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
      fs[l]? = some f ∧ YesGives Z G a x.name s m rs' gs' ∧ m.failed = none ∧
      f.opened m = .ok t ∧ t.failed = none ∧ m.out.reply = t.out.reply := by
  obtain ⟨fs, f, m, h1, h2, h3, h4, h5, h6, h7⟩ := hl.yes hy
  exact ⟨fs, f, m, _, _, h1, h2, yes_of_is hi (show x.decide s _ _ = .ok m from h3), h4, h5, h6,
    IM.sameReply_eq h7⟩

end P1K2

#print axioms P1K2.yes_of_is
#print axioms P1K2.k02_sits
#print axioms P1K2.yes_alone_gives
#print axioms P1K2.yes_framed_gives
#print axioms P1K2.yes_joined_gives
