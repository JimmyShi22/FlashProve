-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/AtDesc.lean: if the maker of the proof file's description (ProofFile.onlineDescription)
succeeds, every side that Side.seated returns for the sender's row (sendRow, "our row") at the first
segment's opening is Seated. The same holds at a segment's reads, at its digits and at the request's
own table, each under two public premises that identify the place. No premise on the side's
sub-protocol is left.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file proves. Why these statements need a proof is said under "Why it is needed" below: the
description holds each lot's sub-protocol in a wrapped form. The premise of seatedAt_first,
seatedAt_reads, seatedAt_digits, seatedAt_w, seatedAt_own and member_of_own is IM.Open: the maker
has succeeded. The five named seatedAt_… hold for every way to read the input (wit), every number
first of the first new oracle message, all data D and every side that Side.seated returns (premise
hσ) from the first chain's list F.first.blocksInOrder for our row at the job. The opening is the first
segment's first sending. Each segment has two later sendings, which the library calls its reads and
its digits.
  seatedAt_first   That side is Seated at the job of the first segment's opening (openJob).
  seatedAt_reads, seatedAt_digits   The same at the reads and at the digits of segment number l, if
                   the ground has that segment (Bs.G₀.built) and K1.linkNumbers gives its numbers.
  seatedAt_w       The same at the sending of the request's own table, if linMessageW gives that
                   sending's oracle messages and K13.wBlock its sub-protocol.
  seatedAt_own     The general form: the same at every job that has the place, rounds and oracle
                   messages of some sub-protocol of K1's own lot at the ground Bs.G₀.
  member_of_own    Every member of the first chain's list at the place of a sub-protocol of K1's own
                   lot at the ground Bs.G₀ has that sub-protocol's rounds and oracle messages.
  seatedAt_first_returns   seatedAt_first with IM.Open replaced by the premise ProofFile.onlineDescription o pol
                   lay KL = .ok F. The public part Z and the base Bs are then bound by "there are".
                   By its proof they are the ones that the maker built; the statement does not say
                   so.
  returns_of_live  If the test FlashProve.protocolDataWellFormed accepts at three public files, the maker succeeds
                   there, with its parameter o, a hash function, set to OnBytes.secondHashFunction. protocolDataWellFormed is
                   an executable test on the public files that is part of the library's verifier.
                   OnBytes.secondHashFunction is the format's second hash function, a fixed function.

Limits.
Where the premise is met. That the maker succeeds at given public files is not proved in this file;
returns_of_live derives it from protocolDataWellFormed, with o set to OnBytes.secondHashFunction. That protocolDataWellFormed accepts at the
stored full-size public files (VerifierAndGoals.storedPublicFiles) is proved as theLive_zFull
(AtFullSide/Top/LiveAtFull.lean). That the maker succeeds there: proofPlanOk_zFull
(AtFullSide/Top/PlanOkAtFull.lean). Both are in a side library that the main library does not
import. Many closed facts beneath them are proved by evaluation in Lean's kernel, and no Lean code
connects the three stored terms with files (Johnson/SendSim/Defs.lean, the table of premises).
The statements are about single values: no distribution is named.
That Side.seated returns a side is a premise (hσ). Under IM.Open, AtDescStands.lean proves that the
list has a member at the place of each job of lotJobs and wJobs (stands_at_job), and then
Side.seated returns a side (seated_of_member, AtDescSome.lean). Under IM.Open, AtDescStands.lean
also proves the two premises of seatedAt_w (wJobs_some, wBlock_of_msg).
wit, first and D are free variables. Nothing says which wit, first and D are the honest prover's.
The premises on the book, on queried positions and on challenges in the statements over Seated
remain (see AtDescLots.lean, Limits).

How it fits. seatedAt_own and seatedAt_w give seatedAt_job (AtDescStands.lean), which serves
Spec.fieldsAtLots. AtDescOwn.lean uses seatedAt_own, AtDescSome.lean seatedAt_first, AtDescHand.lean
member_of_own. No file uses seatedAt_reads, seatedAt_digits, seatedAt_first_returns or
returns_of_live. The first two are seatedAt_own at the two later sorts of place, for a reader who
looks for one place. seatedAt_first_returns states seatedAt_first with the maker's success as its
only premise. returns_of_live, which is by pseat_name (Johnson/Goal/Description/ProofSeat.lean),
connects that premise with the library's test on the public files.

Why it is needed. The member of the first chain's list at a place is not the lot's own sub-protocol.
It is that sub-protocol with the type of its claims changed (Block.retype), and wrapped:
  - it rejects if the verifier's state after it bears a mark of failure (guardMark);
  - it bears the place's name;
  - it rejects if the field reply of the verifier's state has changed (sameReply,
    Johnson/Desc/ProofFile/Frames1.lean: only the one place that receives the reply may write it);
  - at a segment's first place a further step is joined behind it (IM.Joined);
  - outside the segments it has one more test on the plan.
So the premise "the side's sub-protocol is the lot's" of seated_first, seated_later, seated_reads
(Lot.lean) and seated_w (LotW.lean) cannot hold there. Seated requires less: the rounds, the oracle
messages and the row. That the wrapping keeps rounds and oracle messages is the library's, under
IM.Open: member_first with joined_gives, member_alone with alone_gives
(Johnson/Desc/ProofFile/Honest/Member/AtLot.lean) and k13_m4_alone
(Johnson/Desc/ProofFile/Honest/Member/Uses.lean).

The other names.
  openJob          the first job of lotJobs (Lot.lean), with the number first as a parameter.
  find_of_seated   the side's sub-protocol is what List.find? returns at the place.
  k1_in_seat       K1's own lot is among the description's lots (ProofFile.onlineFirstChainBlockTables Z).
  own_first, own_later, own_reads, own_digits   that lot has the opening's sub-protocol and, for
                   each segment, the reads' (with a step without rounds joined) and the digits'.
-/
import Johnson.SendSim.Seat.LotW
import Johnson.Desc.ProofFile.Honest.Member.Uses
import Johnson.IMR.K1Seat
import Johnson.Goal.Description.ProofSeat

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At
open ProofFile.Honest.AtPlace (AsFlat member_first member_alone alone_gives joined_gives of_find
  k13_m4_alone)

variable {V W X Xi Pb : Type}

/-- The job at the first segment's opening: the first job of lotJobs
(Johnson/SendSim/Seat/Lot.lean), with the number first of its first new oracle message as a
parameter. -/
abbrev openJob (Z : ProofFile.Pub) (G : ProofFile.Ground) (first : Nat) (D : RowDataOf Xi) :
    SendJob (PlaceIn Xi) X :=
  placeJob (K1.firstPar G.first (K1.gpOf Z)) first (firstFold G.first) D

/-- The sub-protocol of a side that Side.seated returns is what List.find? returns at the place. -/
theorem find_of_seated {S Cl : Type} {bs : List (Block S Cl)} {a : Place}
    {row : List (ProofFile.Honest.Part V W X × Sim Pb)} {fs : List (Fall S)} {σ : Side S Cl V W X Pb}
    (h : Side.seated bs a row fs = some σ) : (bs.find? fun b => b.place == a) = some σ.block := by
  unfold Side.seated at h
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 h
  exact hb

/-- K1's own lot is among the description's lots. -/
theorem k1_in_seat (Z : ProofFile.Pub) : ProofFile.k1Pure Z ∈ ProofFile.onlineFirstChainBlockTables Z := by
  unfold ProofFile.onlineFirstChainBlockTables
  simp

/-- The opening's sub-protocol is in K1's own lot. -/
theorem own_first (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    K1.firstSegmentOpening G.first (K1.gpOf Z) ∈ (ProofFile.k1Pure Z).own G :=
  List.mem_append_left _ (List.mem_singleton.2 rfl)

/-- If the ground has segment number l (hY) and K1.linkNumbers gives its numbers (hn), the reads'
and the digits' sub-protocols of that segment are in K1's own lot. -/
theorem own_later (Z : ProofFile.Pub) (G : ProofFile.Ground) {l : ℕ} {Y : OnBytes.Model.Stages.LinkH}
    {pr pd : ℕ} {reads digits : Option (List ℕ)} (hY : G.built[l]? = some Y)
    (hn : K1.linkNumbers G Y = some (pr, pd, reads, digits)) :
    IM.k1Reads Z G l Y pr reads ∈ (ProofFile.k1Pure Z).own G ∧
      K1.laterAt G.first (K1.gpOf Z) l pd 2 digits ∈ (ProofFile.k1Pure Z).own G := by
  have hz : (Y, l) ∈ G.built.toList.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.2 (by rw [Array.getElem?_toList]; simpa using hY)
  unfold ProofFile.k1Pure K1.lotWith
  dsimp only
  unfold K1.blocks
  dsimp only
  constructor
  · refine List.mem_append_right _ (List.mem_flatMap.2 ⟨(Y, l), hz, ?_⟩)
    dsimp only
    rw [hn]
    exact List.mem_cons_self ..
  · refine List.mem_append_right _ (List.mem_flatMap.2 ⟨(Y, l), hz, ?_⟩)
    dsimp only
    rw [hn]
    exact List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)

theorem own_reads (Z : ProofFile.Pub) (G : ProofFile.Ground) {l : ℕ} {Y : OnBytes.Model.Stages.LinkH}
    {pr pd : ℕ} {reads digits : Option (List ℕ)} (hY : G.built[l]? = some Y)
    (hn : K1.linkNumbers G Y = some (pr, pd, reads, digits)) :
    IM.k1Reads Z G l Y pr reads ∈ (ProofFile.k1Pure Z).own G := (own_later Z G hY hn).1

theorem own_digits (Z : ProofFile.Pub) (G : ProofFile.Ground) {l : ℕ} {Y : OnBytes.Model.Stages.LinkH}
    {pr pd : ℕ} {reads digits : Option (List ℕ)} (hY : G.built[l]? = some Y)
    (hn : K1.linkNumbers G Y = some (pr, pd, reads, digits)) :
    K1.laterAt G.first (K1.gpOf Z) l pd 2 digits ∈ (ProofFile.k1Pure Z).own G := (own_later Z G hY hn).2

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block First.S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- If the maker has succeeded (IM.Open), every member of the first chain's list at the place of a
sub-protocol of K1's own lot at the ground Bs.G₀ has that sub-protocol's rounds and oracle messages.
-/
theorem member_of_own (O : IM.Open o pol lay KL F Z Bs base c A B) {b₀ : Block First.S Unit}
    (hown : b₀ ∈ (ProofFile.k1Pure Z).own Bs.G₀) {m : Block First.S ProofFile.Cl} (hm : m ∈ c.blocksInOrder)
    (hp : m.place = b₀.place) : m.rounds = b₀.rounds ∧ m.oracles = b₀.oracles := by
  have hb : (b₀.retype : Block First.S ProofFile.Cl) ∈ (ProofFile.k1Pure Z).blocks Bs.G₀ :=
    List.mem_append_left _ (List.mem_map.2 ⟨b₀, hown, rfl⟩)
  have alone : b₀.place.kind = KindName.K1 → 2 ≤ b₀.place.piece → b₀.place.piece ≤ 9 →
      m.rounds = b₀.rounds ∧ m.oracles = b₀.oracles := fun hk h2 h9 => by
    obtain ⟨x, hF, hA⟩ := member_alone o pol lay KL F Z Bs base c A B O _ (k1_in_seat Z) _ hb
      (by show b₀.place.kind ≠ _; rw [hk]; decide)
      (Or.inr (Or.inl ⟨by show b₀.place.kind ≠ _; rw [hk]; decide,
        by show b₀.place.kind ≠ _; rw [hk]; decide, h2, h9⟩)) m hm hp
    obtain ⟨-, -, hr, ho, -⟩ := alone_gives _ x m _ _ _ hF hA
    exact ⟨hr, ho⟩
  rcases IM.k1_mem hown with rfl | ⟨l, Y, pr, pd, reads, digits, -, hn, rfl | rfl⟩
  · have hJ := member_first o pol lay KL F Z Bs base c A B O 0 .K1 _ (k1_in_seat Z) _ hb rfl
      (by decide) m hm hp
    obtain ⟨_, _, -, -, -, hr, ho, -⟩ := joined_gives Z 0 m m _ _ (Or.inl rfl) hJ
    exact ⟨hr, ho⟩
  · rcases IM.numbers_pieces hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact alone rfl (show 2 ≤ 4 by decide) (show 4 ≤ 9 by decide)
    · exact alone rfl (show 2 ≤ 5 by decide) (show 5 ≤ 9 by decide)
  · rcases IM.numbers_pieces hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact alone rfl (show 2 ≤ 6 by decide) (show 6 ≤ 9 by decide)
    · exact alone rfl (show 2 ≤ 7 by decide) (show 7 ≤ 9 by decide)

/-- If the maker has succeeded (IM.Open): let b₀ be a sub-protocol of K1's own lot at the ground
Bs.G₀ and J a job with b₀'s place, rounds and oracle messages. Every side that Side.seated returns
from the description's first chain for our row at J is Seated at J, its data read through wit. -/
theorem seatedAt_own (O : IM.Open o pol lay KL F Z Bs base c A B) {b₀ : Block First.S Unit}
    (hown : b₀ ∈ (ProofFile.k1Pure Z).own Bs.G₀) (J : SendJob (PlaceIn Xi) X) (wit : W → PlaceIn Xi)
    (hpl : b₀.place = J.P.place) (hr : b₀.rounds = K1.rounds J.P)
    (ho : b₀.oracles = K1.oracles J.P) {fs₀ : List (Fall F.S₁)} {σ₀ : Side F.S₁ F.Cl V W X Pb}
    (hσ : Side.seated F.first.blocksInOrder (sendRow (V := V) (Pb := Pb) J.P.place (jobOver J wit)).place
      (sendRow (V := V) (Pb := Pb) J.P.place (jobOver J wit)).row fs₀ = some σ₀) :
    Seated σ₀ (jobOver J wit) := by
  have e := O.desc
  subst e
  obtain ⟨hm, hp⟩ := of_find (find_of_seated hσ)
  obtain ⟨h1, h2⟩ := member_of_own O hown hm (hp.trans hpl.symm)
  exact seated_lifted J wit hσ (h1.trans hr) (h2.trans ho)

/-- If the maker has succeeded (IM.Open), every side that Side.seated returns from the description's
first chain for our row at the first segment's opening is Seated. -/
theorem seatedAt_first (O : IM.Open o pol lay KL F Z Bs base c A B) (wit : W → PlaceIn Xi)
    (first : Nat) (D : RowDataOf Xi) {fs₀ : List (Fall F.S₁)} {σ₀ : Side F.S₁ F.Cl V W X Pb}
    (hσ : Side.seated F.first.blocksInOrder (sendRow (V := V) (Pb := Pb)
                 (openJob (X := X) Z Bs.G₀ first D).P.place
                 (jobOver (openJob (X := X) Z Bs.G₀ first D) wit)).place
      (sendRow (V := V) (Pb := Pb) (openJob (X := X) Z Bs.G₀ first D).P.place
        (jobOver (openJob (X := X) Z Bs.G₀ first D) wit)).row fs₀ = some σ₀) :
    Seated σ₀ (jobOver (openJob (X := X) Z Bs.G₀ first D) wit) :=
  seatedAt_own O (own_first Z Bs.G₀) _ wit rfl rfl rfl hσ

/-- If the maker has succeeded (IM.Open), the ground has segment number l (hY) and K1.linkNumbers
gives its numbers (hn): every side that Side.seated returns from the description's first chain for
our row at that segment's reads is Seated. In the lot, the reads' sub-protocol has a step without
rounds or oracle messages joined behind it (IM.k1Reads). -/
theorem seatedAt_reads (O : IM.Open o pol lay KL F Z Bs base c A B) (wit : W → PlaceIn Xi)
    {l : ℕ} {Y : OnBytes.Model.Stages.LinkH} {pr pd : ℕ} {reads digits : Option (List ℕ)}
    (hY : Bs.G₀.built[l]? = some Y) (hn : K1.linkNumbers Bs.G₀ Y = some (pr, pd, reads, digits))
    (first : Nat) (D : RowDataOf Xi) {fs₀ : List (Fall F.S₁)} {σ₀ : Side F.S₁ F.Cl V W X Pb}
    (hσ : Side.seated F.first.blocksInOrder (sendRow (V := V) (Pb := Pb)
                 (laterJobAt (X := X) Bs.G₀.first (K1.gpOf Z) l pr 1 first D).P.place
                 (jobOver (laterJobAt (X := X) Bs.G₀.first (K1.gpOf Z) l pr 1 first D) wit)).place
      (sendRow (V := V) (Pb := Pb)
        (laterJobAt (X := X) Bs.G₀.first (K1.gpOf Z) l pr 1 first D).P.place
        (jobOver (laterJobAt (X := X) Bs.G₀.first (K1.gpOf Z) l pr 1 first D) wit)).row fs₀ =
          some σ₀) :
    Seated σ₀ (jobOver (laterJobAt (X := X) Bs.G₀.first (K1.gpOf Z) l pr 1 first D) wit) :=
  seatedAt_own O (own_reads Z Bs.G₀ hY hn) _ wit
    (reads_member (X := X) Z Bs.G₀ l Y pr reads first D).2.2
    (reads_member (X := X) Z Bs.G₀ l Y pr reads first D).1
    (reads_member (X := X) Z Bs.G₀ l Y pr reads first D).2.1 hσ

/-- If the maker has succeeded (IM.Open), the ground has segment number l (hY) and K1.linkNumbers
gives its numbers (hn): every side that Side.seated returns from the description's first chain for
our row at that segment's digits is Seated. -/
theorem seatedAt_digits (O : IM.Open o pol lay KL F Z Bs base c A B) (wit : W → PlaceIn Xi)
    {l : ℕ} {Y : OnBytes.Model.Stages.LinkH} {pr pd : ℕ} {reads digits : Option (List ℕ)}
    (hY : Bs.G₀.built[l]? = some Y) (hn : K1.linkNumbers Bs.G₀ Y = some (pr, pd, reads, digits))
    (first : Nat) (D : RowDataOf Xi) {fs₀ : List (Fall F.S₁)} {σ₀ : Side F.S₁ F.Cl V W X Pb}
    (hσ : Side.seated F.first.blocksInOrder (sendRow (V := V) (Pb := Pb)
                 (laterJobAt (X := X) Bs.G₀.first (K1.gpOf Z) l pd 2 first D).P.place
                 (jobOver (laterJobAt (X := X) Bs.G₀.first (K1.gpOf Z) l pd 2 first D) wit)).place
      (sendRow (V := V) (Pb := Pb)
        (laterJobAt (X := X) Bs.G₀.first (K1.gpOf Z) l pd 2 first D).P.place
        (jobOver (laterJobAt (X := X) Bs.G₀.first (K1.gpOf Z) l pd 2 first D) wit)).row fs₀ =
          some σ₀) :
    Seated σ₀ (jobOver (laterJobAt (X := X) Bs.G₀.first (K1.gpOf Z) l pd 2 first D) wit) :=
  seatedAt_own O (own_digits Z Bs.G₀ hY hn) _ wit
    (later_rounds (X := X) Bs.G₀.first (K1.gpOf Z) l pd 2 first D digits).2.2
    (later_rounds (X := X) Bs.G₀.first (K1.gpOf Z) l pd 2 first D digits).1
    (later_rounds (X := X) Bs.G₀.first (K1.gpOf Z) l pd 2 first D digits).2.1 hσ

/-- If the maker has succeeded (IM.Open), linMessageW gives the oracle messages of the sending of
the request's own table (hmsg) and K13.wBlock gives its sub-protocol (hw): every side that
Side.seated returns from the description's first chain for our row at that sending is Seated. In the
lot a sub-protocol of another kind is joined behind that sending's (K13.atM4), and the description
wraps the two as one. -/
theorem seatedAt_w (O : IM.Open o pol lay KL F Z Bs base c A B) (wit : W → PlaceIn Xi)
    {msg : Array OracleNotice} {w : Block First.S Unit} (hmsg : linMessageW Z.first.lin = some msg)
    (hw : K13.wBlock Z = some w) (first : Nat) (D : RowDataOf Xi) {fs₀ : List (Fall F.S₁)}
    {σ₀ : Side F.S₁ F.Cl V W X Pb}
    (hσ : Side.seated F.first.blocksInOrder (sendRow (V := V) (Pb := Pb)
                 (wJobAt (X := X) Z.first (wGp Z) 4 msg first D).P.place
                 (jobOver (wJobAt (X := X) Z.first (wGp Z) 4 msg first D) wit)).place
      (sendRow (V := V) (Pb := Pb) (wJobAt (X := X) Z.first (wGp Z) 4 msg first D).P.place
        (jobOver (wJobAt (X := X) Z.first (wGp Z) 4 msg first D) wit)).row fs₀ = some σ₀) :
    Seated σ₀ (jobOver (wJobAt (X := X) Z.first (wGp Z) 4 msg first D) wit) := by
  have e := O.desc
  subst e
  obtain ⟨h1, h2, h3⟩ := w_member (X := X) Z.first (wGp Z) 4 first msg D w (K13.whereOf Z) hmsg hw
  obtain ⟨hm, hp⟩ := of_find (find_of_seated hσ)
  have hp4 : (wJobAt (X := X) Z.first (wGp Z) 4 msg first D).P.place = ⟨1, none, 4, .K1⟩ := rfl
  obtain ⟨x, hF, hA⟩ := k13_m4_alone O hw hm (hp.trans hp4)
  obtain ⟨-, -, hr, ho, -⟩ := alone_gives _ x _ _ _ _ hF hA
  exact seated_lifted _ wit hσ (hr.trans h1) (ho.trans h2)

end

/-- seatedAt_first with IM.Open replaced by the premise that the maker succeeds with the value F.
The public part Z and the base Bs are then bound by "there are": the statement does not say that
they are the ones that the maker built. -/
theorem seatedAt_first_returns {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {F : FileDescription ProofFile.Inst} (hF : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : ProofFile.Pub) (Bs : ProofFile.PureBase), ∀ (wit : W → PlaceIn Xi) (first : Nat)
      (D : RowDataOf Xi) (fs₀ : List (Fall F.S₁)) (σ₀ : Side F.S₁ F.Cl V W X Pb),
      Side.seated F.first.blocksInOrder (sendRow (V := V) (Pb := Pb)
                   (openJob (X := X) Z Bs.G₀ first D).P.place
                   (jobOver (openJob (X := X) Z Bs.G₀ first D) wit)).place
        (sendRow (V := V) (Pb := Pb) (openJob (X := X) Z Bs.G₀ first D).P.place
          (jobOver (openJob (X := X) Z Bs.G₀ first D) wit)).row fs₀ = some σ₀ →
      Seated σ₀ (jobOver (openJob (X := X) Z Bs.G₀ first D) wit) := by
  obtain ⟨Z, Bs, base, c, A, B, O⟩ := IM.seat_open hF
  exact ⟨Z, Bs, fun wit first D _ _ hσ => seatedAt_first O wit first D hσ⟩

/-- If the library's test FlashProve.protocolDataWellFormed accepts at three public files, the maker of the proof
file's description succeeds there, at the format's second hash function OnBytes.secondHashFunction. That
protocolDataWellFormed accepts is proved at the stored full-size files VerifierAndGoals.storedPublicFiles (theLive_zFull,
AtFullSide/Top/LiveAtFull.lean, in a side library); proofPlanOk_zFull
(AtFullSide/Top/PlanOkAtFull.lean) states that the maker succeeds there. -/
theorem returns_of_live (Z : VerifierAndGoals.PublicFiles) (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) :
    ∃ F, ProofFile.onlineDescription OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok F :=
  (FlashProve.pseat_name Z live).imp fun _ h => h.1

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.member_of_own
#print axioms OnBytes.SendSim.Seat.seatedAt_first
#print axioms OnBytes.SendSim.Seat.seatedAt_reads
#print axioms OnBytes.SendSim.Seat.seatedAt_digits
#print axioms OnBytes.SendSim.Seat.seatedAt_w
#print axioms OnBytes.SendSim.Seat.seatedAt_first_returns
#print axioms OnBytes.SendSim.Seat.returns_of_live
