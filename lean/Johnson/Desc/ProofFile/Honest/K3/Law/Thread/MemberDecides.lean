-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/MemberDecides.lean: the kind "lookup" (K3): the
description's own member at a lookup's place returns, on any rounds that fit: where the state in
front passes the seated decision's four tests and bears no mark, the lookup's slots are there and
free in its ledger, and the rounds and columns pass the step's own two tests, the member's own
decision returns. No honest prover is spoken of: of what the rounds show nothing is asked beyond
these two tests. For either sort of site. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: the seated decision is `decideVia`
(Johnson/Desc/First/Look/Via/Via.lean). The step's own two tests are `Block.Fits`
(Johnson/Top/H0/StepLaws/StepLaws.lean).

What is shown.
  `fits_same`: the step's own two tests read a sub-protocol's rounds alone.
  `toHeard_shape`: what the seated hearing hands back bears the lookup's shape.
  `member_decides`: the title's sentence.

Hypotheses that remain, in `member_decides`.
  `O`: the description returns (`IM.Open`, Johnson/IMR/SeatOpen.lean).
  `hs`: s is a site of the public part (`lookSites Z`).
  `hb`, `hbs`: lot is one of the lookups' own sub-protocols (`(K3Lot.lot Z).blocks`); it stands at
    the site's place.
  `hm`, `hmp`, `hpk`: the member is in the first chain's flat list; it stands at that place; it
    passes its own test on the plan (planOk).
  `hok`, `hT2`, `hT3`: three tests with code on public data.
  `h0`, `hF`, `hh0`, `hO`, `hn`, `hfree`: on the state in front: it bears no mark; the seat reads a
    ledger F; nothing is heard; no row waits; the next slot of F is the lookup's first slot; the
    lookup's slots are there and free in F.
  `hHead`: at the digits of the head's link alone: the step without a round behind that lookup
    returns. This is a hypothesis for other kinds' files to show.
  `hFit`: the rounds and columns pass the step's own two tests.
In the helpers: `h`: (in `fits_same`) two sub-protocols declare the same rounds. `hp`, `hh`, `hH`:
(in `toHeard_shape`) the parameters make the shape h; `hearV` returns; `toHeard` returns.
(`toHeard_fields`, Honest/K3/Law/SeatedWorth.lean, and `toHeard_parts`,
Honest/K3/Law/Thread/ExchangeRows.lean, have its conclusion, the structure's shape is h, from the
last of the three alone.)

How the proof goes. The member's test on the plan gives the lookups' own sub-protocol its form, its
rounds, the entries' test and several calls (`site_block`, Honest/K3/Law/MemberSite.lean). The
hearing returns on rounds that fit (`hearV_returns_at`, Honest/K3/Shape/ReturnsStep.lean). So the
seated decision accepts (`calls_accepts`, `digits_accepts`, Honest/K3/Law/SeatedAll.lean). What
stands behind it without a round returns (`site_behind`, Honest/K3/Law/MemberSite.lean). So the
sub-protocol's step accepts; the state behind bears no mark and the reply is as in front; so the
member's step accepts (`memberAtSite`, Honest/K3/Law/MemberAtSite.lean, read backwards), and with it
its decision.

Users. `returns_calls` and `returns_digits` (Honest/K3/Law/Thread/ReturnsLook.lean) and
`returns_headDigits` (Honest/K3/Law/Thread/CarriesHeadDigits.lean) call `member_decides`.

Limits. It says that the decision returns, not what the decision sets. On the verifier's side alone.
No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Top.H0.StepLaws.StepLaws
import Johnson.Desc.ProofFile.Honest.K3.Law.SlotsElems
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.K3Keeps
import Johnson.Desc.ProofFile.Honest.K3.Shape.ReturnsStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn step_iff noDigest)
open VerifiableInference.Desc.K3 (HeardV hearV faceOf toHeard toHeardG quietAt)
open VerifiableInference.Desc.K3.Law (decideVia)
open VerifiableInference.Desc.First.Look (sameShape)
open VerifiableInference.Desc.First.Shape (ledSh freeB sized_of_B)
open ProofFile.Honest.K3.Shape (hearV_returns_at win_of_freeB)

local notation "FS" => VerifiableInference.Desc.First.S
local notation "FShape" => OnBytes.Model.Forest.Shape

/-- **The step's own two tests read a sub-protocol's rounds alone.** -/
theorem fits_same {S Cl : Type} {b b' : Block S Cl} (h : b.rounds = b'.rounds) (ft : Nat)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (hF : b.Fits ft rs cols) : b'.Fits ft rs cols := by
  unfold Block.Fits Block.want at hF ⊢
  rw [← h]
  exact hF

/-- **What the seated hearing hands back bears the lookup's shape.** -/
theorem toHeard_shape {h : FShape} {F G : Fork} {rs : List Fmt.RoundView} {g : HeardV}
    {H : OnBytes.Model.Forest.Heard} {p : VerifiableInference.Desc.First.Look.P}
    (hp : p.shape = some h) (hh : hearV (faceOf h) F rs = some (g, G))
    (hH : toHeard h (toHeardG g) = some H) : H.shape = h := by
  obtain ⟨pt, form, hk, hsz⟩ := keys_of_hearV h hh
  obtain ⟨g', hg', hsh, _⟩ := toHeard_returns h g pt form hk hsz (countsOk_of_shape hp)
  obtain rfl : g' = H := Option.some.inj (hg'.symm.trans hH)
  exact hsh

/-- **The description's own member at a lookup's place returns, on any rounds that fit.**
Conditional on the hypotheses that the head of this file lists. No instance of these hypotheses is
exhibited in this file. -/
theorem member_decides (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
    (hs : s ∈ lookSites Z) (lot blk : Block FS ProofFile.Cl) (hb : lot ∈ (K3Lot.lot Z).blocks Bs.G₀)
    (hbs : lot.place = s.at_.place) (hm : blk ∈ ch.blocksInOrder) (hmp : blk.place = lot.place)
    (hpk : blk.planOk = true) (hok : s.at_.face.ok = true)
    (hT2 : (s.digits || s.caller != .layers || sameShape s.shape Z.p.X.y.fo) = true)
    (hT3 : (!s.digits || s.caller == .head ||
      usedAt Z.p.X s == some (s.p.first + s.at_.face.slots)) = true)
    (ft : Nat) (sj : FS) (F : Fork) (h0 : sj.failed = none)
    (hF : (seatOf K3Lot.ofForm s.digits).fork sj = some F)
    (hh0 : ((seatOf K3Lot.ofForm s.digits).heard sj).isNone = true)
    (hO : ((seatOf K3Lot.ofForm s.digits).owed sj).noneWaits = true) (hn : F.next = s.p.first)
    (hfree : freeB (ledSh F) F.next (faceOf s.shape).slots = true)
    (hHead : s.digits = true → s.caller = .head → ∀ (rs : List Fmt.RoundView) (g : HeardV) (G : Fork)
      (s' : FS), rs.length = (s.p.entries.getD []).length →
      hearV (faceOf s.shape) F rs = some (g, G) →
      decideVia (seatOf K3Lot.ofForm s.digits) s.p sj rs = .ok s' → ∃ t, HeadBehind Z.p.X s' t)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (hFit : blk.Fits ft rs cols) :
    ∃ s', blk.decide sj (rs.map noDigest) (blk.shown ft rs cols) = .ok s' := by
  obtain ⟨Fm, hfit, hN, hr, _⟩ := site_block o pol lay KL Fd Z Bs base ch A B O s hs lot blk hb hbs
    hm hmp hpk
  obtain ⟨_, g3, _, _, hst⟩ := memberAtSite o pol lay KL Fd Z Bs base ch A B O lot hb blk hm hmp
  have hp := site_shape hs
  have hface : s.at_.face = faceOf s.shape := by
    have hs' := hs
    unfold lookSites at hs'
    obtain ⟨x, _, hsx⟩ := List.mem_filterMap.1 hs'
    exact (site_facts _ _ x s hsx).2.2.2.2.2.1
  rw [hface] at hok hfit
  have hLF : lot.Fits ft rs cols := fits_same g3 ft rs cols hFit
  have hSz := sized_of_B (by
    unfold freeB at hfree
    simp only [Bool.and_eq_true] at hfree
    exact hfree.1.1)
  -- the hearing returns
  obtain ⟨g, G, hh⟩ := hearV_returns_at (faceOf s.shape) hok (win_of_freeB hfree) (blk := lot)
    (es := s.p.entries.getD []) hr hfit hLF
  have hlen : (rs.map noDigest).length = (s.p.entries.getD []).length := by
    rw [List.length_map, fit_len _ _ hLF.1, hr, List.length_map]
  -- the seated decision accepts
  have hdec : ∃ g' s', toHeard s.shape (toHeardG g) = some g' ∧
      decideVia (seatOf K3Lot.ofForm s.digits) s.p sj (rs.map noDigest) = .ok s' ∧
      (seatOf K3Lot.ofForm s.digits).heard s' = some g' ∧
      (seatOf K3Lot.ofForm s.digits).fork s' = some G ∧ s'.failed = sj.failed := by
    cases hd : s.digits with
    | false =>
      rw [hd] at hF hh0 hO
      exact calls_accepts K3Lot.ofForm s.p s.shape sj hp hN hF hh0 hO hn hh
    | true =>
      rw [hd] at hF hh0 hO
      exact digits_accepts K3Lot.ofForm s.p s.shape sj hp hN hF hh0 hO hn hh
  obtain ⟨g', s', hg', hd', a1, a2, a3⟩ := hdec
  -- what stands behind returns
  obtain ⟨t, hQ⟩ := site_behind Z s hs (s.p.entries.getD []).length sj F hSz hn hT2 hT3 hHead
    (rs.map noDigest) g G g' s' hlen hh hg' hd' a1 a2
  -- the state behind: no mark; the reply as in front
  obtain ⟨gp, Gp, hput⟩ := decideVia_put _ s.p sj s' (rs.map noDigest) hd'
  have hout' : s'.out = sj.out := by rw [hput]; exact seatOf_put_out K3Lot.ofForm s.digits sj gp Gp
  have hplen : (rs.map noDigest).length = s.p.rounds.length := by
    rw [List.length_map, fit_len _ _ hLF.1, Fm.rounds]
  have hlot : lot.decide sj (rs.map noDigest) (lot.shown ft rs cols) = .ok t ∧ t.out = sj.out ∧
      t.failed = none := by
    unfold QuietBehind at hQ
    rcases Fm.form with ⟨hq, hbd⟩ | ⟨f, hq, hbd⟩
    · rw [hq] at hQ
      subst hQ
      exact ⟨by rw [hbd]; exact hd', hout', by rw [a3]; exact h0⟩
    · rw [hq] at hQ
      obtain ⟨k1, k2⟩ := quietAt_keeps Z.p.X s.link s.digits f hq s' t hQ
      refine ⟨?_, k1.trans hout', by rw [k2, a3]; exact h0⟩
      rw [hbd, ← hplen, List.take_length, hd']
      exact hQ
  obtain ⟨hl1, hl2, hl3⟩ := hlot
  have hstep : lot.step ft sj rs cols = .ok (t, (lot.want ft rs).length) :=
    (step_iff ft lot sj t rs cols _).2 ⟨hLF, hl1, rfl⟩
  have hrep : sameReply sj t = true := by
    unfold sameReply
    rw [hl2]
    exact beq_self_eq_true _
  have hmem := (hst ft sj t _ rs cols).2 ⟨hstep, hl3, hrep⟩
  exact ⟨t, ((step_iff ft blk sj t rs cols _).1 hmem).2.1⟩

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.fits_same
#print axioms ProofFile.Honest.K3.Law.AtThr.toHeard_shape
#print axioms ProofFile.Honest.K3.Law.AtThr.member_decides
