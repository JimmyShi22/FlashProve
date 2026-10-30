-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/Later.lean: THE RECORD `NoHouse`
(Honest/Law/NoHouse/Bare.lean) AT THE THREE MEMBERS WITHOUT A ROUND AND WITHOUT A HOUSE OF THE TWO
LATER CHAINS: «the shared chain's front» (place ⟨2, none, 0, frame⟩) · «the taken trees' sources»
(⟨3, none, 1, frame⟩) · «the end of chain 3» (⟨3, none, 3, frame⟩): each at its chain's thread,
GENERAL IN THE THREAD's LETTERS (Honest/Thread/Shared.lean, Honest/Thread/Last.lean): no term is
laid for these letters yet, so what is asked of them stands as named premises. With
Honest/Law/NoHouse/End2.lean these are all four members of the kind frame of the two later chains.

WHAT THIS IS. Conditional lemmas on definitions of ours and on the library's own texts. None of the
library's goals.

  1  GENERAL IN THE THREAD: `noHouse_quiet_still`   the record at a member without a round whose yes
     returns the state and says G of it, at a row that owes nothing: one call of
     `NoHouse.ofDecide` (Honest/Law/NoHouse/Fill.lean)
  2  `noHouse_front2`   G := True: THE BLOCK NEVER REFUSES: no premise of content
  3  `noHouse_taken3`   G := the library's `Third.Law.Tied` (Johnson/Desc/Third/Law/Sources.lean:
     `takenSources_exact`)
  4  `noHouse_end3`   G := the library's `ChainEnd.NothingLeft` of the statement
  5  `f0t_front2`, `f0t_end2`, `f0t_taken3`, `f0t_end3`   THE FOUR SEATS AT THE LIBRARY's TERM
     `P5J.F0T`: by the lists' texts: the payers of the premise seat wherever a thread's flat list is
     laid as that term's

WHICH FIELDS FALL OUT, AND WHICH ARE CONTENT.
  seat     a premise by name (the letters' flat list is a letter); section 5 pays it at the term.
  bare     by the blocks' texts; «no half stands there»: a premise on the prover (noHalf).
  behind   a yes returns the state (by the block's text · `takenSources_exact` · `end_decide`). The
           form one border on: the shape: a premise on a letter (hShape); «nothing is left» is asked
           behind the last member alone: there PAID FROM THE BLOCK's OWN YES under hLeft; in front
           of it the clause is idle: by evaluation of the places' number. The riders and «keeps» at
           a state that does not turn: premises on letters.
  owes     NOTHING IS OWED: the tables' rows at these places are empty: by evaluation.
  yes      front 2: PAID OUTRIGHT. **CONTENT: asks: at «the taken trees' sources»: `Tied own s`**
           (every member of the own group, and the mask, has a tree in the book · each such tree is
           declared as taken from the chain that sent it · no other tree is declared as taken) ·
           **at the end of chain 3: `NothingLeft s.st`**: each AT THE THREAD's STATE in front of the
           member.
  said, rides   PREMISES, as the record has them.

MET FOR NOTHING. As `NoHouse`. Limits. NO TERM IS LAID FOR THE LETTERS. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.End2
import Johnson.Desc.ProofFile.Honest.Thread.Last
import Johnson.Desc.Third.Law.Sources
import Johnson.Desc.ProofFile.Lot.LastChainFour

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! ## 1 General in the thread -/

namespace ProofFile.Honest
open VerifiableInference.Desc (Block)

/-- **THE RECORD AT A MEMBER WITHOUT A ROUND WHOSE YES RETURNS THE STATE AND SAYS G OF IT**, at a
row that owes nothing. -/
theorem noHouse_quiet_still {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S Cl V W X Pb}
    {Said : Nat → Coins Bk → Mid W X → Prop} {fall : Nat → S → List Fmt.Drawn → Option String}
    {b : Nat} {blk : Block S Cl} {G : S → Prop} (seat : T.bs[b]? = some blk)
    (hr : blk.rounds = []) (ho : blk.oracles = [])
    (hn : (T.hs.find? fun g => g.place == blk.place) = none)
    (hd : ∀ s t, blk.decide s [] [] = .ok t ↔ t = s ∧ G s)
    (said : ∀ k m, Said b k m → Said (b + 1) k m)
    (form : ∀ k s m E, ThrS T Said b k s m E → G s → T.Form (b + 1) k s m)
    (hrd : ∀ v s, T.rides b v s → T.rides (b + 1) v s)
    (hkp : ∀ k s m E, ThrS T Said b k s m E → T.keeps b s s) (howes : (T.row b).owes = [])
    (asks : ∀ k s m E, ThrS T Said b k s m E → fall b s [] = none → G s)
    (rides : RidesPastS T Said b) : NoHouse T Said fall b blk :=
  NoHouse.ofDecide seat hr (by rw [hr, ho]; rfl) hn said
    (fun k s m E s' hA hs => by
      obtain ⟨rfl, hG⟩ := (hd s s').1 hs
      exact ⟨form k _ m E hA hG, hrd _ _ hA.1.2.2.2.2.2.1, hkp k _ m E hA⟩)
    (fun k s m E s' _ _ ds i hi => by
      rw [howes] at hi
      cases hi)
    (fun k s m E hA hf => ⟨s, (hd s s).2 ⟨rfl, asks k s m E hA hf⟩⟩)
    rides

end ProofFile.Honest

/-! ## 2 The shared chain's front -/

namespace ProofFile.Honest.SharedThread
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.Shared (sharedPlaces)
open Desc.K14 (St frontBlock)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Ky X₀ P₁ Wt : Type} {L : Letters Bk St Cl W₀ Rc Ky X₀ P₁ Wt}

theorem places_long (sp : Bool) : decide ((sharedPlaces sp).length ≤ 1) = false := by
  cases sp <;> rfl

/-- **`NoHouse` AT THE SHARED CHAIN's FRONT**: the block never refuses: NO PREMISE OF CONTENT. -/
theorem noHouse_front2 {Said : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop}
    {fall : Nat → St → List Fmt.Drawn → Option String} {c : OnBytes.Model.Verify.Chains}
    {q : Bool}
    (seat : L.bs[0]? = some { ((frontBlock c : Block St Unit).retype : Block St Cl) with
      planOk := q })
    (noHalf : ∀ g ∈ L.hs, g.place.kind ≠ KindName.frame)
    (said : ∀ k m, Said 0 k m → Said 1 k m)
    (hShape : ∀ s, L.shape 0 s = true → L.shape 1 s = true)
    (hr : ∀ v s, L.rides 0 v s → L.rides 1 v s) (hkp : ∀ s, L.keeps 0 s s)
    (rides : RidesPastS L.thread Said 0) :
    NoHouse L.thread Said fall 0 { ((frontBlock c : Block St Unit).retype : Block St Cl) with
      planOk := q } :=
  noHouse_quiet_still (G := fun _ => True) seat rfl rfl
    (List.find?_eq_none.2 fun g hg hp => noHalf g hg (by rw [eq_of_beq hp]; rfl))
    (fun s t => ⟨fun h => ⟨(Except.ok.inj h).symm, trivial⟩, fun h => by rw [h.1]; rfl⟩)
    said
    (fun k s m E hA _ => by
      have hF : (L.shape 0 s && (!decide ((sharedPlaces L.split).length ≤ 0) ||
          L.nothingLeft s)) = true ∧ L.order s := hA.1.2.2.1
      have h1 : L.shape 0 s = true := by
        have h0 := hF.1
        simp only [Bool.and_eq_true] at h0
        exact h0.1
      show (L.shape 1 s && (!decide ((sharedPlaces L.split).length ≤ 1) ||
          L.nothingLeft s)) = true ∧ L.order s
      rw [hShape s h1, places_long]
      exact ⟨rfl, hF.2⟩)
    hr (fun _ s _ _ _ => hkp s)
    (by
      show ((((sharedPlaces L.split)[0]?).map (SharedRows.rowAt L.split)).getD {}).owes = []
      rfl)
    (fun _ _ _ _ _ _ => trivial) rides

end ProofFile.Honest.SharedThread

/-! ## 3, 4 The second chain's two -/

namespace ProofFile.Honest.LastThread
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.ChainEnd (chainEnd refuse untestedL NothingLeft untested_iff)
open VerifiableInference.Desc.Last (lastPlaces)
open VerifiableInference.Desc.Third (S₃ takenSources)
open VerifiableInference.Desc.Third.Law (Tied takenSources_exact)

variable {Bk : ProverCoinCounts} {S₂ Cl W₀ Rc Xi Tr X P₁ Wt : Type}
  {L : Letters Bk S₂ S₃ Cl W₀ Rc Xi Tr X P₁ Wt}

/-- **`NoHouse` AT «THE TAKEN TREES' SOURCES».** own: the block of the request's own proximity test,
which stands behind it. **asks: THE LIBRARY's `Tied own s` AT THE THREAD's STATE: THE CONTENT.** -/
theorem noHouse_taken3 {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}
    {fall : Nat → S₃ → List Fmt.Drawn → Option String} {own : Block S₃ Unit} {q : Bool}
    (seat : L.bs[1]? = some { ((takenSources own : Block S₃ Unit).retype : Block S₃ Cl) with
      planOk := q })
    (noHalf : ∀ g ∈ L.hs, g.place.kind ≠ KindName.frame)
    (said : ∀ k m, Said 1 k m → Said 2 k m)
    (hShape : ∀ p s₂ s, L.PL.shape 1 p s₂ s = true → L.PL.shape 2 p s₂ s = true)
    (hr : ∀ v s, L.rides 1 v s → L.rides 2 v s) (hkp : ∀ s, L.keeps 1 s s)
    (asks : ∀ k s m E, ThrS L.thread Said 1 k s m E → fall 1 s [] = none → Tied own s)
    (rides : RidesPastS L.thread Said 1) :
    NoHouse L.thread Said fall 1 { ((takenSources own : Block S₃ Unit).retype : Block S₃ Cl) with
      planOk := q } :=
  noHouse_quiet_still (G := Tied own) seat rfl rfl
    (List.find?_eq_none.2 fun g hg hp => noHalf g hg (by rw [eq_of_beq hp]; rfl))
    (fun s t => takenSources_exact own s [] [] t) said
    (fun k s m E hA _ => by
      have hF : (L.PL.shape 1 (L.thread.seat k m s).1.1 (L.thread.seat k m s).1.2 s &&
          (!decide (lastPlaces.length ≤ 1) || L.PL.nothingLeft s)) = true ∧ L.order s :=
        hA.1.2.2.1
      have h1 : L.PL.shape 1 (L.thread.seat k m s).1.1 (L.thread.seat k m s).1.2 s = true := by
        have h0 := hF.1
        simp only [Bool.and_eq_true] at h0
        exact h0.1
      show (L.PL.shape 2 (L.thread.seat k m s).1.1 (L.thread.seat k m s).1.2 s &&
          (!decide (lastPlaces.length ≤ 2) || L.PL.nothingLeft s)) = true ∧ L.order s
      rw [hShape _ _ s h1]
      exact ⟨rfl, hF.2⟩)
    hr (fun _ s _ _ _ => hkp s) rfl asks rides

/-- **`NoHouse` AT THE END OF CHAIN 3**: not sealed: no round. hLeft: «nothing is left» holds
wherever the library's `NothingLeft` does. **asks: THAT SENTENCE AT THE THREAD's STATE: THE
CONTENT.** -/
theorem noHouse_end3 {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}
    {fall : Nat → S₃ → List Fmt.Drawn → Option String} {inF : List Fmt.DeclaredRound} {q : Bool}
    (seat : L.bs[3]? = some { ((chainEnd 3 3 false inF fun s : S₃ => untestedL s.st :
      Block S₃ Unit).retype : Block S₃ Cl) with planOk := q })
    (noHalf : ∀ g ∈ L.hs, g.place.kind ≠ KindName.frame)
    (said : ∀ k m, Said 3 k m → Said 4 k m)
    (hShape : ∀ p s₂ s, L.PL.shape 3 p s₂ s = true → L.PL.shape 4 p s₂ s = true)
    (hLeft : ∀ s : S₃, NothingLeft s.st → L.PL.nothingLeft s = true)
    (hr : ∀ v s, L.rides 3 v s → L.rides 4 v s) (hkp : ∀ s, L.keeps 3 s s)
    (asks : ∀ k s m E, ThrS L.thread Said 3 k s m E → fall 3 s [] = none → NothingLeft s.st)
    (rides : RidesPastS L.thread Said 3) :
    NoHouse L.thread Said fall 3 { ((chainEnd 3 3 false inF fun s : S₃ => untestedL s.st :
      Block S₃ Unit).retype : Block S₃ Cl) with planOk := q } :=
  noHouse_quiet_still (G := fun s => NothingLeft s.st) seat rfl rfl
    (List.find?_eq_none.2 fun g hg hp => noHalf g hg (by rw [eq_of_beq hp]; rfl))
    (fun s t => by
      rw [end_decide, untested_iff]
      exact and_comm)
    said
    (fun k s m E hA hG => by
      have hF : (L.PL.shape 3 (L.thread.seat k m s).1.1 (L.thread.seat k m s).1.2 s &&
          (!decide (lastPlaces.length ≤ 3) || L.PL.nothingLeft s)) = true ∧ L.order s :=
        hA.1.2.2.1
      have h1 : L.PL.shape 3 (L.thread.seat k m s).1.1 (L.thread.seat k m s).1.2 s = true := by
        have h0 := hF.1
        simp only [Bool.and_eq_true] at h0
        exact h0.1
      show (L.PL.shape 4 (L.thread.seat k m s).1.1 (L.thread.seat k m s).1.2 s &&
          (!decide (lastPlaces.length ≤ 4) || L.PL.nothingLeft s)) = true ∧ L.order s
      rw [hShape _ _ s h1, hLeft s hG]
      exact ⟨by simp, hF.2⟩)
    hr (fun _ s _ _ _ => hkp s) rfl asks rides

end ProofFile.Honest.LastThread

/-! ## 5 The four seats at the library's term -/

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.ChainEnd (chainEnd untestedL)
open VerifiableInference.Desc.Third (S₃ takenSources)
open Desc.K14 (St frontBlock)
open P5J (F0T TS)

variable (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)

theorem f0t_front2 : ∃ q, (F0T o Zp Np cF).shared.blocksInOrder[0]? =
    some { ((frontBlock Zp.p.chains : Block St Unit).retype : Block St ProofFile.Cl) with
      planOk := q } := ⟨_, rfl⟩

theorem f0t_end2 : ∃ (b : Nat) (inF : List Fmt.DeclaredRound) (q : Bool),
    (F0T o Zp Np cF).shared.blocksInOrder[b]? =
    some { ((chainEnd 2 11 true inF fun d : St => untestedL d.st : Block St Unit).retype :
      Block St ProofFile.Cl) with planOk := q } :=
  ⟨_, _, _, IM.last_at_flat (F0T o Zp Np cF).shared⟩

theorem f0t_taken3 : ∃ q, (F0T o Zp Np cF).second.blocksInOrder[1]? =
    some { ((takenSources (P2Third.lastOwn Np) : Block S₃ Unit).retype : Block S₃ ProofFile.Cl) with
      planOk := q } := ⟨_, rfl⟩

theorem f0t_end3 : ∃ inF q, (F0T o Zp Np cF).second.blocksInOrder[3]? =
    some { ((chainEnd 3 3 false inF fun s : S₃ => untestedL s.st : Block S₃ Unit).retype :
      Block S₃ ProofFile.Cl) with planOk := q } := ⟨_, _, rfl⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.noHouse_quiet_still
#print axioms ProofFile.Honest.SharedThread.places_long
#print axioms ProofFile.Honest.SharedThread.noHouse_front2
#print axioms ProofFile.Honest.LastThread.noHouse_taken3
#print axioms ProofFile.Honest.LastThread.noHouse_end3
#print axioms ProofFile.Honest.f0t_front2
#print axioms ProofFile.Honest.f0t_end2
#print axioms ProofFile.Honest.f0t_taken3
#print axioms ProofFile.Honest.f0t_end3
