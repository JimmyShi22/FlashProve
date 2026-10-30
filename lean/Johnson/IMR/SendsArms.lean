-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/SendsArms.lean: FoldFacts' FIELD «K12.seatsCarried» AND «placesAre»
(Johnson/Desc/Sound/SmpPlaces.lean): THE DEBT SendsAt (Johnson/IMR/SendsFold.lean) AT THE FORMS OF
Johnson/IMR/FlatCases.lean THAT SEND NOTHING AND ARE NAMED UNDER «PAID HERE»; AND TWO RULES FOR
WHOEVER PAYS A SENDER's.
ON WORDS: «the state» is the verifier's state; a «sub-protocol» is a block of the IOP as written in Lean.
CALLED, NOT TYPED: Johnson/Goal/Meaning/SizeSeated.lean («the makers that send nothing leave the number of oracle messages, the book and the count of roots»: framesOf_three · closeOf_three) · CoreSeated.lean (atM3_core) with Ground.coreStill_three · GrowsSeated.lean (framesOf_grows · closeOf_grows: the code table stays) · RecGrows.lean
(layFront_quiet) · Johnson/IMR/QuietLot.lean (quiet_lot) · step_inv · chainEnd_decide_iff.

  Calm s s'         the code table, the number of oracle messages and the book are as they were.
  sends_of_calm     a sub-protocol each of whose decision's acceptings is Calm owes nothing more: SendsAt ft codes [] b.
  SendsAt.under     the debt of a SEATED sub-protocol is its lot's own's (b.UnderR b').
  sends_first       AT A LINK's FIRST PLACE (two stages): the lot's own sub-protocol's SendsAt at snd gives the joined one's: «opened» is Calm.
  sends_front · sends_laid · sends_cleared · sends_hear_quiet · sends_close · sends_last · sends_355   THE ARMS.

PAID HERE, BY COUNT OF NUMBERS: the front 1 · «laid» 25 · «cleared» 25 · K3 · K4 · K5 · K6 · K8 · K11: 101 · the closing's three: 75 · K13's batching 1 · the seal 1: 229 of the 358. «opened» at all 25 first places (as the second stage).
NOT PAID HERE: the batching (25) and the sub-protocol behind it (25): their acceptings run the link's gathered runs: owed · K7's place (338): its first stage · the senders: K1 (52) · K2 (25) · K12 (1). No soundness.
-/
import Johnson.IMR.SendsFold
import Johnson.IMR.FlatCases
import Johnson.IMR.QuietLot
import Johnson.Goal.Meaning.SizeSeated
import Johnson.Goal.Meaning.GrowsSeated
import Johnson.Desc.ChainEndExact

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open OnBytes (Codes OracleNotice)
open VerifiableInference.Desc (Block Chain Link Place KindName OpenedColumn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Whole Decides Fn)
open VerifiableInference.Desc.Ground (Core ByC)
open VerifiableInference.Desc.K1.RelCore (coreS)
open VerifiableInference.Desc.K12.Coin (Appends)
open Meaning.K2 (Quiet Enters GR)
open ProofFile (Cl)

/-- The code table, the number of oracle messages and the book are as they were. -/
def Calm (s s' : S) : Prop :=
  s'.st.codes = s.st.codes ∧ s'.st.oracles.size = s.st.oracles.size ∧ s'.book = s.book

theorem calm_of_enters {s s' : S} (h : Enters s s') : Calm s s' :=
  ⟨by rw [h.1], by rw [h.1], h.2.2.1⟩

/-- The three that SizeSeated.lean's lemmas speak of, as a relation. -/
def ThreeC (a b : Core) : Prop :=
  b.st.oracles.size = a.st.oracles.size ∧ b.book = a.book ∧ b.roots = a.roots

theorem three_h3 : ∀ a b : Core, b.st.oracles.size = a.st.oracles.size → b.book = a.book →
    b.roots = a.roots → ThreeC a b := fun _ _ h1 h2 h3 => ⟨h1, h2, h3⟩

theorem calm_of {s s' : S} (h : ByC ThreeC coreS s s') (g : GR s s') : Calm s s' :=
  ⟨g.1, h.1, h.2.1⟩

/-- **A sub-protocol each of whose acceptings is Calm sends nothing.** -/
theorem sends_of_calm {ft : ℕ} {codes : Codes} {b : Block S Cl} (h : Decides Calm b) :
    SendsAt ft codes [] b := by
  intro s s' rs cols n hy hc
  obtain ⟨-, -, -, hd⟩ := VerifiableInference.Desc.step_inv ft b s s' rs cols n hy
  obtain ⟨c1, c2, c3⟩ := h s _ _ s' hd
  refine ⟨c1.trans hc, Appends.nil codes _ _ (by rw [c3]) (by rw [c3]), fun hi => ?_⟩
  unfold InStep at hi ⊢
  rw [c2, c3]
  exact hi

/-- The debt of a seated sub-protocol is its lot's own's. -/
theorem SendsAt.under {ft : ℕ} {codes : Codes} {snd : List (Array OracleNotice)}
    {b b' : Block S Cl} (hU : b.UnderR b') (h : SendsAt ft codes snd b') :
    SendsAt ft codes snd b :=
  fun s s' rs cols n hy hc => h s s' rs cols n (VerifiableInference.Desc.step_under hU hy) hc

/-- Chain.blocksInOrder's «hasNoClaimsAndNothingAfter» turns the test on the plan alone. (The same as under_bare in Johnson/IMR/GrownJoin.lean, which this file does not import.) -/
theorem underR_bare {b b' : Block S Cl} (h : b.UnderR b') :
    ({ b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } : Block S Cl).UnderR b' := h

/-- Every row of the links' frame: its three steps are Calm. -/
theorem frames_calm {built : Array OnBytes.Model.Stages.LinkH} {first : OnBytes.Params.First}
    {W : OnBytes.Model.Verify.Public} {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame}
    (h : Johnson.Desc.First.Walk.Seat.framesOf built first W = .ok fs) {f} (hf : f ∈ fs) :
    Fn Calm f.lay ∧ Fn Calm f.opened ∧ Fn Calm f.clear := by
  obtain ⟨a1, a2, a3⟩ := Meaning.K2.framesOf_three three_h3 h f hf
  obtain ⟨g1, g2, g3⟩ := Meaning.K2.framesOf_grows h f hf
  exact ⟨fun s t k => calm_of (a1 s t k) (g1 s t k), fun s t k => calm_of (a2 s t k) (g2 s t k),
    fun s t k => calm_of (a3 s t k) (g3 s t k)⟩

/-- **At a link's first place: two stages.** -/
theorem sends_first {ft : ℕ} {codes : Codes} {snd : List (Array OracleNotice)} {Z : ProofFile.Pub}
    {l : ℕ} {b b' : Block S Cl} {a : Place} (hj : Joined Z l b b' a)
    (h : SendsAt ft codes snd b') : SendsAt ft codes snd b := by
  intro s s' rs cols n hy hc
  obtain ⟨fs, f, m, hfs, hf, h1, -, h3, -, -⟩ := hj.step hy
  obtain ⟨c1, a1, i1⟩ := h s m rs cols n h1 hc
  obtain ⟨k1, k2, k3⟩ := (frames_calm hfs (List.mem_of_getElem? hf)).2.1 m s' h3
  refine ⟨k1.trans c1, by rw [k3]; exact a1, fun hi => ?_⟩
  have := i1 hi
  unfold InStep at this ⊢
  rw [k2, k3]
  exact this

theorem sends_front {ft : ℕ} {codes : Codes} {b : Block S Cl}
    (hd : ∀ s rs gs t, b.decide s rs gs = .ok t ↔ t = s) : SendsAt ft codes [] b :=
  sends_of_calm fun s rs gs s' h => by
    obtain rfl := (hd s rs gs s').1 h
    exact ⟨rfl, rfl, rfl⟩

theorem sends_laid {ft : ℕ} {codes : Codes} {l : ℕ} {b : Block S Cl}
    (hd : ∀ s rs gs t, b.decide s rs gs = .ok t ↔
      Johnson.Desc.First.Walk.layFront l s = .ok t ∧ t.failed = none ∧
        ProofFile.sameReply s t = true) : SendsAt ft codes [] b :=
  sends_of_calm fun s rs gs s' h =>
    calm_of_enters (Meaning.K2.layFront_quiet l s s' ((hd s rs gs s').1 h).1).1

theorem sends_cleared {ft : ℕ} {codes : Codes} {Z : ProofFile.Pub} {l : ℕ}
    {fs : List Johnson.Desc.First.Walk.Seat.LinkFrame} {f : Johnson.Desc.First.Walk.Seat.LinkFrame}
    {b : Block S Cl}
    (hfs : Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs)
    (hf : fs[l]? = some f)
    (hd : ∀ s rs gs t, b.decide s rs gs = .ok t ↔
      f.clear s = .ok t ∧ t.failed = none ∧ ProofFile.sameReply s t = true) : SendsAt ft codes [] b :=
  sends_of_calm fun s rs gs s' h =>
    (frames_calm hfs (List.mem_of_getElem? hf)).2.2 s s' ((hd s rs gs s').1 h).1

theorem sends_hear_quiet {ft : ℕ} {codes : Codes} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}
    {b b' : Block S Cl} {name : String} {a : Place} (lot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hq : quietMaker b'.place.kind = true) (hla : LaidAlone ProofFile.sameReply b b' name a) :
    SendsAt ft codes [] b := by
  obtain ⟨L, hL, hb⟩ := lot
  exact (sends_of_calm fun s rs gs s' h => calm_of_enters (quiet_lot hL hb hq s rs gs s' h).1).under
    (alone_underR hla)

theorem sends_close {ft : ℕ} {codes : Codes} {p : VerifiableInference.Desc.K9.Where}
    {Q : VerifiableInference.Desc.First.Close.Par} {j : ℕ} {b : Block S Cl} {x : Block S Unit}
    {name : String} {a : Place}
    (ex : (VerifiableInference.Desc.K9.closeOf p Q : List (Block S Unit))[j]? = some x)
    (hla : LaidAlone ProofFile.sameReply b x.retype name a) : SendsAt ft codes [] b := by
  have hm := List.mem_of_getElem? ex
  have h1 := (Meaning.K2.closeOf_three (Cl := Unit) three_h3 p Q x hm).1
  have h2 := (Meaning.K2.closeOf_grows (Cl := Unit) p Q x hm).1
  exact (sends_of_calm (b := x.retype) fun s rs gs s' h =>
    calm_of (h1 s rs gs s' h) (h2 s rs gs s' h)).under (alone_underR hla)

theorem sends_last {ft : ℕ} {codes : Codes} {Z : ProofFile.Pub} {b : Block S Cl} {name : String}
    {a : Place}
    (hla : LaidAlone ProofFile.sameReply b
      ((VerifiableInference.Desc.ChainEnd.chainEnd 1 5 true
        (VerifiableInference.Desc.K13.inFrontOf Z) VerifiableInference.Desc.First.endAsks :
        Block S Unit).retype : Block S Cl) name a) :
    SendsAt ft codes [] ({ b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } : Block S Cl) := by
  refine SendsAt.under (b' := ((VerifiableInference.Desc.ChainEnd.chainEnd 1 5 true
    (VerifiableInference.Desc.K13.inFrontOf Z) VerifiableInference.Desc.First.endAsks :
    Block S Unit).retype : Block S Cl)) (underR_bare (alone_underR hla))
    (sends_of_calm fun s rs gs s' h => ?_)
  have h' : (VerifiableInference.Desc.ChainEnd.chainEnd (Cl := Unit) 1 5 true
      (VerifiableInference.Desc.K13.inFrontOf Z) VerifiableInference.Desc.First.endAsks).decide s rs
      gs = .ok s' := h
  obtain rfl := ((VerifiableInference.Desc.ChainEnd.chainEnd_decide_iff (Cl := Unit) 1 5 true
    (VerifiableInference.Desc.K13.inFrontOf Z) VerifiableInference.Desc.First.endAsks s s' rs
    gs).1 h').1
  exact ⟨rfl, rfl, rfl⟩

/-- K13's batching (number 355). -/
theorem sends_355 {ft : ℕ} {codes : Codes} {Z : ProofFile.Pub} {b : Block S Cl} {name : String}
    {a : Place} (hla : LaidAlone ProofFile.sameReply b (k13Dress Z).retype name a) :
    SendsAt ft codes [] ({ b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } : Block S Cl) := by
  refine SendsAt.under (b' := (k13Dress Z).retype) (underR_bare (alone_underR hla))
    (sends_of_calm fun s rs gs s' h => ?_)
  have h' : (VerifiableInference.Desc.K13.atM3 (Cl := Unit)
      (VerifiableInference.Desc.K13.whereOf Z)).decide s rs gs = .ok s' := h
  exact calm_of
    ((Meaning.K2.atM3_core (Cl := Unit) (Rc := ThreeC)
      VerifiableInference.Desc.Ground.coreStill_three _).1 s rs gs s' h')
    (VerifiableInference.Desc.K13.atM3_grows _ s rs gs s' h')

end IM

#print axioms IM.sends_of_calm
#print axioms IM.sends_first
#print axioms IM.sends_front
#print axioms IM.sends_laid
#print axioms IM.sends_cleared
#print axioms IM.sends_hear_quiet
#print axioms IM.sends_close
#print axioms IM.sends_last
#print axioms IM.sends_355
