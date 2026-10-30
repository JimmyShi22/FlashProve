-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/SamplesThrough.lean: **THE PROXIMITY TEST's OWN BLOCK LEAVES EVERY OLDER MESSAGE's SAMPLE, A MEMBER's TOO.** Statements and proofs, on the text of the
block: no premise on the view, and of the place only p.early = true and p.answers = 1.

Why. On the shared chain o_sp is a member of BOTH groups: the test on G_u must leave what the test on G_omega, and o_sp's pin, read of it: its shape, its mark "sampled", its sample
rows. Law/OutK2.lean says: a message that is neither a member nor the first mask stands to the letter; "of a member nothing else is said than that its ledger is
shut". Here the rest is said.
  k12_old_of · k12_old   a yes of the decision from t0 to tE: every message o of t0 that is not the first mask is, in tE, what it is BEHIND THE TEST's BEGINNING (the library's begun:
                         the members' ledgers shut, nothing else).
  smpPart x              what a reader of a sample reads of a message: its shape, its mark, its sample rows. KIN: SameMsgs (Johnson/Desc/K1/Law/SeedIs.lean) asks
                         the same triple of EVERY number at once: a block that sends messages has not that; here it is asked number by number.
  k12_smp                so smpPart stands, at members too.
  **seat_leaves**        AT THE SHARED CHAIN's TWO SEATS (Seat.enter g mask · Seat.leave): a yes from d to d' leaves: the codes · smpPart of every message but the mask handed in · every
                         group but the one under test, to the letter · the small record · each place of the book and each tree's shape, number and parts.
  onGu_leaves · onGomega_leaves   at the two named seats.
Limits. Nothing on what a sample is worth. The first mask's message is spent: nothing is said of it. NO SOUNDNESS.

-/
import Johnson.Desc.K12.Law.OutK3
import Johnson.Desc.K12.Seat
import Johnson.Desc.K12.SeatLaws
import OnBytes.Slice.BlkProxEarlierMessagesAndGroups

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw H2K.Out
open H2K.FoldLaw (bind_ok got_ok)

/-- Every older message but the first mask is what it is behind the test's beginning. -/
theorem k12_old_of (X : Parts T12) (p : P12) (hX : Like X p)
    (hB : ∀ (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t' : T12)
      (rs : List Fmt.RoundView) (gs : Gs), (X.base p j cur cut).decide t rs gs = .ok t' → BaseSt t t')
    (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind X p : Blk').decide t0 rs gs = .ok tE) :
    ∃ G, t0.st.groups[t0.g]? = some G ∧ ∀ o, o < t0.st.oracles.size → t0.mask ≠ some o →
      tE.st.oracles[o]? = (begun t0.st t0.g G).oracles[o]? := by
  obtain ⟨first, rest, ds, tF, t1, hs, _, hfr, hbat, _, hst⟩ := k12_ok X p t0 tE rs gs h
  have hF : tF = t0 := by
    have hfr' := hX.front _ _ hfr
    unfold frontJ at hfr'
    dsimp only at hfr'
    split at hfr'
    · obtain ⟨_, _, hfr'⟩ := bind_ok hfr'
      cases hfr'
      rfl
    · cases hfr'
  subst hF
  obtain ⟨e, r, row, L, S', _, hb, rfl⟩ := batJ_ok p he _ _ _ _ _ (hX.bat _ _ _ _ _ hbat)
  obtain ⟨G, hG, rfl⟩ := bat_st _ _ _ _ _ _ _ hb
  have k := stages_st X p hX hB he ha rest 0 first _ _ tE _ _ hst
  have osz : (begun tF.st tF.g G).oracles.size = tF.st.oracles.size := H2K.Out.closeLedgers_size _ _
  have k5 := k.oraclesOld
  dsimp only at k5
  rw [osz] at k5
  exact ⟨G, hG, k5⟩

/-- Of the variant proximityTestKind guardedProximityTestParts p. -/
theorem k12_old (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) :
    ∃ G, t0.st.groups[t0.g]? = some G ∧ ∀ o, o < t0.st.oracles.size → t0.mask ≠ some o →
      tE.st.oracles[o]? = (begun t0.st t0.g G).oracles[o]? :=
  k12_old_of guardedProximityTestParts p (like_P5 p)
    (fun j cur cut t t' rs gs h => baseJ5_st p j cur cut t t' rs gs (ranged_ok _ _ _ _ _ _ h).1)
    he ha t0 tE rs gs h

/-- What a reader of a sample reads of a message. -/
def smpPart (x : OnBytes.Oracle) : OracleShape × Bool × Array OnBytes.Row :=
  (x.shape, x.sampled, x.sampleRows)

theorem smpPart_shut (x : OnBytes.Oracle) : smpPart (shut x) = smpPart x := rfl

/-- The test's beginning leaves it. -/
theorem begun_smp (S : Statement) (g : ℕ) (G : Group) (o : ℕ) :
    ((begun S g G).oracles[o]?).map smpPart = (S.oracles[o]?).map smpPart := by
  have e : (begun S g G).oracles[o]? = (S.oracles[o]?).map fun x =>
      if o ∈ G.members.toList then shut x else x := closeLedgers_get _ _ _
  rw [e, Option.map_map]
  congr 1
  funext x
  show smpPart (if o ∈ G.members.toList then shut x else x) = smpPart x
  split
  · exact smpPart_shut x
  · rfl

/-- **So does the whole test.** -/
theorem k12_smp (p : P12) (he : p.early = true) (ha : p.answers = 1) (t0 tE : T12)
    (rs : List Fmt.RoundView) (gs : Gs) (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) (o : ℕ)
    (ho : o < t0.st.oracles.size) (hm : t0.mask ≠ some o) :
    (tE.st.oracles[o]?).map smpPart = (t0.st.oracles[o]?).map smpPart := by
  obtain ⟨G, _, k⟩ := k12_old p he ha t0 tE rs gs h
  rw [k o ho hm, begun_smp]

/-- **AT THE SHARED CHAIN's TWO SEATS.** -/
theorem seat_leaves (g : _root_.Desc.K14.Lin → Nat) (mask : _root_.Desc.K14.Lin → Option Nat) (p : P12)
    (he : p.early = true) (ha : p.answers = 1) (d d' : _root_.Desc.K14.St) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Block.inside (Seat.enter g mask) (proximityTestKind guardedProximityTestParts p : Blk') Seat.leave).decide d rs gs =
      .ok d') :
    d'.st.codes = d.st.codes ∧
      (∀ o, o < d.st.oracles.size → mask d.loc ≠ some o →
        (d'.st.oracles[o]?).map smpPart = (d.st.oracles[o]?).map smpPart) ∧
      (∀ q, q < d.st.groups.size → q ≠ g d.loc → d'.st.groups[q]? = d.st.groups[q]?) ∧
      d'.loc = d.loc ∧ BookKeeps d.book d'.book := by
  have h' : ((Seat.enter g mask d).bind fun t =>
      ((proximityTestKind guardedProximityTestParts p : Blk').decide t rs gs).bind (Seat.leave d)) = .ok d' := h
  obtain ⟨t, ht, h'⟩ := (Seat.ebind_ok _ _ _).1 h'
  obtain ⟨t', ht', hl⟩ := (Seat.ebind_ok _ _ _).1 h'
  cases ht
  cases hl
  have o1 := k12_out p he ha _ t' rs gs ht'
  obtain ⟨G, o2⟩ := k12_out2 p he ha _ t' rs gs ht'
  exact ⟨o1.codes, fun o ho hm => k12_smp p he ha _ t' rs gs ht' o ho hm, o2.others, rfl, o1.book⟩

theorem onGu_leaves (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (d d' : _root_.Desc.K14.St) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Seat.onGu (proximityTestKind guardedProximityTestParts p : Blk')).decide d rs gs = .ok d') :
    d'.st.codes = d.st.codes ∧
      (∀ o, o < d.st.oracles.size → d.loc.firstMask ≠ some o →
        (d'.st.oracles[o]?).map smpPart = (d.st.oracles[o]?).map smpPart) ∧
      (∀ q, q < d.st.groups.size → q ≠ d.loc.gU → d'.st.groups[q]? = d.st.groups[q]?) ∧
      d'.loc = d.loc ∧ BookKeeps d.book d'.book :=
  seat_leaves _ _ p he ha d d' rs gs h

theorem onGomega_leaves (p : P12) (he : p.early = true) (ha : p.answers = 1)
    (d d' : _root_.Desc.K14.St) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Seat.onGomega (proximityTestKind guardedProximityTestParts p : Blk')).decide d rs gs = .ok d') :
    d'.st.codes = d.st.codes ∧
      (∀ o, o < d.st.oracles.size →
        (d'.st.oracles[o]?).map smpPart = (d.st.oracles[o]?).map smpPart) ∧
      (∀ q, q < d.st.groups.size → q ≠ d.loc.gOmega → d'.st.groups[q]? = d.st.groups[q]?) ∧
      d'.loc = d.loc ∧ BookKeeps d.book d'.book := by
  obtain ⟨a, b, c, e, f⟩ := seat_leaves (·.gOmega) (fun _ => none) p he ha d d' rs gs h
  exact ⟨a, fun o ho => b o ho (by simp), c, e, f⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.k12_old
#print axioms VerifiableInference.Desc.K12.Coin.k12_smp
#print axioms VerifiableInference.Desc.K12.Coin.onGu_leaves
#print axioms VerifiableInference.Desc.K12.Coin.onGomega_leaves
