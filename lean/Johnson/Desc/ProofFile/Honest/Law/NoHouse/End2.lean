-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/End2.lean: THE RECORD `NoHouse`
(Honest/Law/NoHouse/Bare.lean) AT THE SHARED CHAIN's LAST MEMBER, «the end of chain 2»: place ⟨2,
none, 11, frame⟩: the library's one text for a chain's end (`ChainEnd.chainEnd`,
Johnson/Desc/ChainEnd.lean) at chain 2, piece 11, sealed, asking that nothing is left untested
(`K12.Seat.last`, Johnson/Desc/K12/Seat/Fill.lean), as the proof file's description lays it (by
`Chain.retype` and `Chain.blocksInOrder`: no guard is laid over it). AT THE SHARED CHAIN's THREAD, GENERAL IN
ITS LETTERS (`SharedThread.Letters`, Honest/Thread/Shared.lean): no term is laid for these letters
yet, so what is asked of them stands as named premises.

WHAT THIS IS. Conditional lemmas on definitions of ours and on the library's own texts. None of the
library's goals.

  1  GENERAL, ON A CHAIN's END AS A LATER CHAIN HOLDS IT (any state, any clauses, sealed or not):
     thin, over the library's own laws on that text (Johnson/Desc/ChainEndLaw | Fold | Exact.lean):
     `end_decide` · `end_yes` (a yes of its step returns the state, and the clauses hold there) ·
     `end_bare` · `end_says`
  2  `row_end2` (the table's row at the place owes nothing) · `noHouse_end2`

WHICH FIELDS FALL OUT, AND WHICH ARE CONTENT (at `noHouse_end2`).
  seat     A PREMISE BY NAME (the letters' flat list is a letter). Where that list is a chain's, the
           library's `IM.last_at_flat` (Johnson/IMR/BackSeat.lean) says where its last block stands.
  bare     its lists and «plain»: BY THE BLOCK's TEXT; «no half stands there»: a premise on the
           prover (noHalf).
  behind   the form at the last border asks «nothing is left»: PAID FROM THE BLOCK's OWN YES, under
           hLeft: the letter nothingLeft holds wherever the library's `ChainEnd.NothingLeft` does
           (`untested_iff`). The shape one border on, the riders and «keeps», at a state that does
           not turn: premises on letters (hShape, hr, hkp). «In order»: as it was.
  owes     NOTHING IS OWED: the table's row at piece 11 is empty: by evaluation.
  yes      **CONTENT: asks: THE LIBRARY's `ChainEnd.NothingLeft` OF THE STATEMENT AT THE THREAD's
           STATE IN FRONT OF THE END**: a proximity test has begun on every group · every sampled
           message is in a tested group. The test on the rounds is paid.
  said, rides   PREMISES, as the record has them.

MET FOR NOTHING. As `NoHouse`; hLeft at a letter that is true everywhere. Limits. NO TERM IS LAID
FOR THE LETTERS. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.Seal
import Johnson.Desc.ProofFile.Honest.Thread.Shared
import Johnson.Desc.K12.Seat.Fill
import Johnson.Desc.ChainEndExact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Chain Place KindName step_iff)
open VerifiableInference.Desc.ChainEnd (chainEnd sealRound refuse untestedL Clauses)
open ProofFile.Honest.FirstThread (roundsFit_plain)

/-! ## 1 A chain's end, as a later chain holds it -/

section
variable {T Cl : Type} {chain piece : Nat} {sealed : Bool} {inF : List Fmt.DeclaredRound}
  {asks : T → Clauses} {q : Bool}

/-- What it decides: its clauses; the state as it was: the library's `chainEnd_decide_iff` and
`refuse_ok_iff`, at the block as a later chain holds it. -/
theorem end_decide (s t : T) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    ({ ((chainEnd chain piece sealed inF asks : Block T Unit).retype : Block T Cl) with
      planOk := q } : Block T Cl).decide s rs gs = .ok t ↔ refuse (asks s) = .ok () ∧ t = s := by
  show (chainEnd chain piece sealed inF asks : Block T Unit).decide s rs gs = .ok t ↔ _
  rw [VerifiableInference.Desc.ChainEnd.chainEnd_decide_iff,
    VerifiableInference.Desc.ChainEnd.refuse_ok_iff]
  exact and_comm

/-- **A yes of its step returns the state, and the clauses hold there.** -/
theorem end_yes {ft : Nat} {s s' : T} {rs : List Fmt.RoundView}
    {cols : List VerifiableInference.Desc.OpenedColumn} {n : Nat}
    (h : ({ ((chainEnd chain piece sealed inF asks : Block T Unit).retype : Block T Cl) with
      planOk := q } : Block T Cl).step ft s rs cols = .ok (s', n)) :
    refuse (asks s) = .ok () ∧ s' = s := by
  obtain ⟨rs', gs', hd⟩ := VerifiableInference.Desc.ChainEnd.step_decide ft _ s s' rs cols n h
  exact (end_decide s s' rs' gs').1 hd

/-- **`Bare` BY THE BLOCK's TEXT**, where no half stands at its place. -/
theorem end_bare {V W X : Type} {hs : List (Placed V W X)}
    (hn : (hs.find? fun g => g.place == (⟨chain, none, piece, .frame⟩ : Place)) = none) :
    Bare hs ({ ((chainEnd chain piece sealed inF asks : Block T Unit).retype : Block T Cl) with
      planOk := q } : Block T Cl) where
  none := hn
  lists := rfl
  plain := fun r hr => by
    have hr' : r ∈ (if sealed then [sealRound] else []) := hr
    cases sealed with
    | false => cases hr'
    | true =>
      obtain rfl := List.mem_singleton.1 hr'
      exact ⟨rfl, rfl, rfl⟩

/-- **ITS STEP SAYS YES at rounds that show no item**, at challenges that they can draw, at a state
that meets its clauses. -/
theorem end_says (ft : Nat) (s : T) (ds : List Fmt.Drawn)
    (hd : drawsFit (if sealed then [sealRound] else []) ds = true)
    (ha : refuse (asks s) = .ok ()) :
    ({ ((chainEnd chain piece sealed inF asks : Block T Unit).retype : Block T Cl) with
      planOk := q } : Block T Cl).step ft s (ds.map fun d => ⟨[], d⟩) [] = .ok (s, 0) := by
  have hr : ({ ((chainEnd chain piece sealed inF asks : Block T Unit).retype : Block T Cl) with
      planOk := q } : Block T Cl).rounds = if sealed then [sealRound] else [] := rfl
  have hw : ({ ((chainEnd chain piece sealed inF asks : Block T Unit).retype : Block T Cl) with
      planOk := q } : Block T Cl).want ft (ds.map fun d => ⟨[], d⟩) = [] := by
    unfold VerifiableInference.Desc.Block.want
    rw [hr]
    cases sealed with
    | false => rfl
    | true =>
      cases ds with
      | nil => rfl
      | cons d t => rfl
  refine (step_iff ft _ s s _ [] 0).2 ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · show VerifiableInference.Desc.roundsFit (if sealed then [sealRound] else [])
      (ds.map fun d => ⟨[], d⟩) = true
    refine roundsFit_plain _ _ (fun r hr' => ?_) hd
    have hr'' : r ∈ (if sealed then [sealRound] else []) := hr'
    cases sealed with
    | false => cases hr''
    | true =>
      obtain rfl := List.mem_singleton.1 hr''
      rfl
  · rw [hw]
    rfl
  · exact (end_decide s s _ _).2 ⟨ha, rfl⟩
  · rw [hw]
    rfl

end

end ProofFile.Honest

/-! ## 2 At the shared chain's thread -/

namespace ProofFile.Honest.SharedThread
open VerifiableInference.Desc (Block Chain Place KindName)
open VerifiableInference.Desc.ChainEnd (chainEnd sealRound refuse untestedL NothingLeft
  untested_iff)
open VerifiableInference.Desc.Shared (sharedPlaces)
open Desc.K14 (St)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Ky X₀ P₁ Wt : Type} {L : Letters Bk St Cl W₀ Rc Ky X₀ P₁ Wt}

/-- The table's row at the place of the chain's end owes nothing. -/
theorem row_end2 {b : Nat} (hb : (sharedPlaces L.split)[b]? = some ⟨2, none, 11, .frame⟩) :
    (L.thread.row b).owes = [] := by
  show ((((sharedPlaces L.split)[b]?).map (SharedRows.rowAt L.split)).getD {}).owes = []
  rw [hb]
  rfl

/-- **`NoHouse` AT THE END OF CHAIN 2**, general in the shared chain's letters. seat: the letters'
flat list holds the library's block there. hb: the place's number in the table's list. noHalf: no
half of the prover's shared chain is of the kind frame. hShape, hr, hkp: the shape one border on,
the riders and «keeps», at a state that does not turn. hLeft: «nothing is left» holds wherever the
library's `NothingLeft` does. **asks: THAT SENTENCE AT THE THREAD's STATE: THE CONTENT.** -/
theorem noHouse_end2 {Said : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop}
    {fall : Nat → St → List Fmt.Drawn → Option String} {b : Nat} {inF : List Fmt.DeclaredRound}
    {q : Bool}
    (seat : L.bs[b]? = some { ((chainEnd 2 11 true inF fun d : St => untestedL d.st :
      Block St Unit).retype : Block St Cl) with planOk := q })
    (hb : (sharedPlaces L.split)[b]? = some ⟨2, none, 11, .frame⟩)
    (noHalf : ∀ g ∈ L.hs, g.place.kind ≠ KindName.frame)
    (said : ∀ k m ds, Said b k m → drawsFit [sealRound] ds = true → Said (b + 1) k (m.past ds))
    (hShape : ∀ s, L.shape b s = true → L.shape (b + 1) s = true)
    (hLeft : ∀ s : St, NothingLeft s.st → L.nothingLeft s = true)
    (hr : ∀ v s, L.rides b v s → L.rides (b + 1) v s) (hkp : ∀ s, L.keeps b s s)
    (asks : ∀ k s m E ds, ThrS L.thread Said b k s m E → fall b s ds = none → NothingLeft s.st)
    (rides : RidesPastS L.thread Said b) :
    NoHouse L.thread Said fall b { ((chainEnd 2 11 true inF fun d : St => untestedL d.st :
      Block St Unit).retype : Block St Cl) with planOk := q } where
  seat := seat
  bare := end_bare (List.find?_eq_none.2 fun g hg hp => noHalf g hg (by rw [eq_of_beq hp]))
  said := said
  behind := fun k s m E ds s' hA _ hs => by
    obtain ⟨ha, rfl⟩ := end_yes hs
    have hF : (L.shape b s' && (!decide ((sharedPlaces L.split).length ≤ b) ||
        L.nothingLeft s')) = true ∧ L.order s' := hA.1.2.2.1
    have h1 : L.shape b s' = true := by
      have h0 := hF.1
      simp only [Bool.and_eq_true] at h0
      exact h0.1
    refine ⟨?_, hr _ _ hA.1.2.2.2.2.2.1, hkp s'⟩
    show (L.shape (b + 1) s' && (!decide ((sharedPlaces L.split).length ≤ b + 1) ||
        L.nothingLeft s')) = true ∧ L.order s'
    rw [hShape s' h1, hLeft s' ((untested_iff s'.st).1 ha)]
    exact ⟨by simp, hF.2⟩
  owes := fun k s m E ds s' _ _ _ ds' i hi => by
    rw [row_end2 hb] at hi
    cases hi
  yes := fun k s m E ds hA hd hf =>
    ⟨s, end_says 0 s ds hd ((untested_iff s.st).2 (asks k s m E ds hA hf))⟩
  rides := rides

end ProofFile.Honest.SharedThread

#print axioms ProofFile.Honest.end_decide
#print axioms ProofFile.Honest.end_yes
#print axioms ProofFile.Honest.end_bare
#print axioms ProofFile.Honest.end_says
#print axioms ProofFile.Honest.SharedThread.row_end2
#print axioms ProofFile.Honest.SharedThread.noHouse_end2
