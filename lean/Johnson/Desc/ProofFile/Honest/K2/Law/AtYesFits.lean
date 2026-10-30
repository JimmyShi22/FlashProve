-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/AtYesFits.lean: the kind "the code switch" (K2): THREE MORE OF
THE TWENTY-ONE FIELDS OF THE RECORD OF PREMISES `MadeAsks` (Honest/K2/Law/ExchangeAtMade.lean), EACH
IN ITS OWN TEXT: check · fits · seated: at a yes of the kind's own decision, at a switch of the
plan, under the library's head and the opening. All three speak of the statement behind the joins
(S3). ON THE VERIFIER's STATE AT A YES: codes, shapes, numbers of messages, the forms of stored
sample rows: no tests on the public files. That file is not imported. No definition. Lemmas: calls
and carryings; none of the library's goals.

  `shape_of_tables`, `samples_of_tables`   two statements with the same tables have, number by
                    number, the same shape and the same stored sample rows, the blank message's
                    where there is none
  `oldFits_of_tables`   `OldFits` passes between two such statements
  `sent_kept`       the numbers that a sending gives its messages 1 to k
  `link_bounds`     a switch of the plan stands at a link from 1 to 25
  `good_named_at_reach`   at a reached state the front's stored sample rows are good, and each
                    form of the carried claim on a kept member names a kept member: three sealed
                    pairs of laws, joined over `SwitchArm`
  `check_at_yes`    THE FIELD check. From the fold alone: no reach under `below`
  `shape_below_at_reach`   what the next two spend: the library's eight facts at the front; the
                    kept members' numbers lie below the front's count of messages
  `fits_at_yes`     THE FIELD fits
  `seated_at_yes`   THE FIELD seated

By. Of other authors, in the library: `check_at_S3`, `keptOld_of`, `g_at_S3`, `copy_at_S3`,
`ids_at`, `notices_size` (Johnson/Top/H0/K2Hands/AtYes.lean) · `ids_cut`
(Johnson/Top/H0/Tw/K2C/GroupsAtYes.lean) · `firstFront_iff` (K2C/Asks.lean) · `frontOf_iff`
(K2C/DebtsState.lean) · `pin_facts` (K2Hands/FrameOne.lean) · `AtYes`, `SentOk`, `SameTables`. Under
Johnson/Desc/K2/Honest/Returns/: `shape_of_test`, `olds_once`, `link_pinned_reached`
(PinReached.lean) · `head_pinned_reached`, `fin_pinned_reached` (PinArms.lean) ·
`link_members_reached` (MembersReached.lean) · `head_members_reached`, `fin_members_reached`
(ClosedArms.lean) · `oldFits_stored` (StoredReached.lean) · `AlikeKept.oldFits` (AlikeKept.lean).
Beside the library: `front_test_at_reach` (SizesAtYes.lean of this folder) · `two_at_yes`
(AtYesTarget.lean) · `placeLinksW` (AtYesMore.lean) · `SwitchArm` (BlockAtHead.lean). The last
clause of seated goes as in the proof of `frontFits_sent` (Returns/SentFront.lean), which has the
like behind the sending, at the honest prover's own sending.

Kin, none a twin by its statement. `Alike.old`, `Alike.shapeD`, `Alike.rowsD` (Returns/Alike.lean)
are to `Alike` what `oldFits_of_tables`, `shape_of_tables`, `samples_of_tables` are to `SameTables`;
the first goes limb for limb as here. No law of the library leads from one of the two relations to
the other. `sizes_of_tables` (SizesAtYes.lean) has the four cases of `shape_of_tables` inside its
proof. `numbers_kept` (Returns/SentFront.lean) is `sent_kept` at the honest sending's own numbers.
`good_named_at_reach` walks the three arms of `front_test_at_reach` a second time: it takes the last
end of the three sealed laws on the pinned front, which that lemma drops.

Limits. No coin, input or run occurs in a statement; each stands behind a yes and reads the
verifier's state there. `AtYes` is a premise. For fits and seated hr (THE STATE IS REACHED OVER THE
MEMBERS UNDER `below`) IS A PREMISE: from a thread's stand it is had where what was said lies below
the prime (`reach_below`, Honest/Thread/SaidOk.lean): not called here. The head and the opening are
premises. That the three texts are the record's is held by no theorem here. It speaks at the head's
own size and hash: the full size, the format's second hash function. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SizesAtYes
import Johnson.Desc.K2.Honest.Returns.MembersReached
import Johnson.Desc.K2.Honest.Returns.ClosedArms
import Johnson.Desc.K2.Honest.Returns.StoredReached
import Johnson.Top.H0.K2Hands.AtYes
import Johnson.Top.H0.Tw.K2C.GroupsAtYes
import Johnson.Top.H0.Tw.K2C.Asks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 AtYes SameTables SentOk KeptPos KeptOld frontAt
  frontOf_iff SampleGoodS check_at_S3 keptOld_of g_at_S3 copy_at_S3 ids_at notices_size ids_cut
  sentIds)
open VerifiableInference.Desc.First.K2Hands (Pinned frontB2 pin_facts)
open VerifiableInference.Desc.K2.Honest (OldFits SeatedAt)
open VerifiableInference.Desc.K2.Honest.Returns (link_pinned_reached head_pinned_reached
  fin_pinned_reached link_members_reached head_members_reached fin_members_reached
  oldFits_stored AlikeKept shape_of_test olds_once tests_at_head row_at)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Johnson.G (fxAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)
open IM (k2P)
open _root_.Tw.K2 (switchNotices firstFront_iff)
open _root_.Desc.K14.Law (secondAt seatZ)

/-! ## 1 General -/

/-- Number by number the same shape; the blank message's where there is none. -/
theorem shape_of_tables {A B : Statement} (h : SameTables A B) (o : Nat) :
    (B.oracles.getD o default).shape = (A.oracles.getD o default).shape := by
  have e := h.shape o
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  cases hb : B.oracles[o]? with
  | none =>
    rw [hb] at e
    cases ha : A.oracles[o]? with
    | none => rfl
    | some a =>
      rw [ha] at e
      cases e
  | some b =>
    rw [hb] at e
    cases ha : A.oracles[o]? with
    | none =>
      rw [ha] at e
      cases e
    | some a =>
      rw [ha] at e
      exact Option.some.inj e

/-- Number by number the same stored sample rows. -/
theorem samples_of_tables {A B : Statement} (h : SameTables A B) (o : Nat) :
    (B.oracles.getD o default).sampleRows = (A.oracles.getD o default).sampleRows := by
  have e := h.samples o
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?]
  cases hb : B.oracles[o]? with
  | none =>
    rw [hb] at e
    cases ha : A.oracles[o]? with
    | none => rfl
    | some a =>
      rw [ha] at e
      cases e
  | some b =>
    rw [hb] at e
    cases ha : A.oracles[o]? with
    | none =>
      rw [ha] at e
      cases e
    | some a =>
      rw [ha] at e
      exact Option.some.inj e

/-- **`OldFits` passes between two statements with the same tables.** -/
theorem oldFits_of_tables {A B : Statement} (h : SameTables A B) {old : SingleRows}
    (F : OldFits A old) : OldFits B old where
  mainVars := by rw [h.codes]; exact F.mainVars
  d0 := by rw [h.codes]; exact F.d0
  d1 := by rw [h.codes]; exact F.d1
  rows := by simp only [shape_of_tables h]; exact F.rows
  named := F.named
  once := F.once
  keptCode := fun o ho => by rw [shape_of_tables h]; exact F.keptCode o ho
  stored := fun o ho => by rw [samples_of_tables h]; exact F.stored o ho

/-- The numbers that a sending gives its messages 1 to k. -/
theorem sent_kept {A B : Statement} {notices : Array OracleNotice} {ids : Array Nat}
    (h : SentOk A notices ids B) (k : Nat) (hk : 1 + k ≤ notices.size) :
    (ids.extract 1 (1 + k)).toList = (List.range k).map (· + (A.oracles.size + 1)) := by
  have e : ids = sentIds A.oracles.size notices.size := h.ids
  rw [e, ids_cut A.oracles.size notices.size 1 k hk]
  simp

/-! ## 2 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {p : SwitchPlace} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}
  {n : P1K2.Nums} {st : First.K2.At} {before : TS → Except String TS}
  {after : TS → TS → Except String TS} {z₀ : ProofFile.InstPub} {s s₁ t : TS} {r₁ r₂ : Fmt.RoundView}
  {gs : List (List (Nat × List UInt64))} {x : _root_.Tw.K2.Front} {z : _root_.Tw.K2.Sent}
  {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {cd : Code}

/-- A switch of the plan stands at a link from 1 to 25. -/
theorem link_bounds (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀) (hA : SwitchArm Zp Bs.G₀ p st before after) :
    1 ≤ p.link ∧ p.link ≤ 25 := by
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  have hlk : p.link = p.place.link.getD 25 := beq_iff_eq.1 (List.all_eq_true.1 placeLinksW.1 p hpW)
  rcases hA with ⟨-, -, h1, h24, -⟩ | ⟨-, ep, -⟩ | ⟨-, ep, -⟩
  · exact ⟨h1, by omega⟩
  · have e24 : p.link = 24 := by
      rw [hlk, ep]
      rfl
    omega
  · have e25 : p.link = 25 := by
      rw [hlk, ep]
      rfl
    omega

/-- **At a reached state the front's stored sample rows are good, and each form of the carried claim
on a kept member names a kept member.** -/
theorem good_named_at_reach (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hA : SwitchArm Zp Bs.G₀ p st before after)
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (P5J.At.ps.findIdx (· == p.place)) (z₀, s))
    (hb : before s = .ok s₁) (nm : String)
    (hx : frontAt (k2P Zp p.place nm st n) s₁ = some x) :
    SampleGoodS x.st ∧ ∀ f ∈ x.f.rows.kept.toList, f.oracle ∈ (switchKept x.f.rows).toList := by
  obtain ⟨hy, hcut, hB⟩ := tests_at_head h.toAtMg O
  have hF := frontOf_iff.2 hx
  rcases hA with ⟨rfl, -, h1, h24, ei, rfl, -⟩ | ⟨rfl, ep, ei, rfl, -⟩ | ⟨rfl, ep, ei, rfl, -⟩
  · obtain rfl : s = s₁ := Except.ok.inj hb
    obtain ⟨m, hm⟩ : ∃ m, p.link = m + 1 := ⟨p.link - 1, by omega⟩
    rw [ei, hm] at hr
    rcases hF with ⟨-, hf⟩ | ⟨c, -⟩ | ⟨c, -⟩
    · obtain ⟨w, hw⟩ := row_at (m := m) (by omega)
      obtain ⟨-, -, -, hG⟩ := link_pinned_reached h.scope h.reads O h.laid.value h.laid.planOk hy
        hcut hB (by omega) hr hf hw
      obtain ⟨L, Q, S', g, a⟩ := (firstFront_iff _ _ _).1 hf
      refine ⟨hG, ?_⟩
      rw [a.out]
      exact (link_members_reached h.scope h.reads O (by omega) hr L Q).2.1
    · cases c
    · cases c
  · obtain rfl : s = s₁ := Except.ok.inj hb
    rw [ei] at hr
    rcases hF with ⟨c, -⟩ | ⟨-, a, Q, here, group, rfl⟩ | ⟨c, -⟩
    · cases c
    · obtain ⟨w, hw⟩ := row_at (m := 23) (by decide)
      obtain ⟨-, -, -, hG⟩ := head_pinned_reached h.scope h.reads O h.laid.value h.laid.planOk hy
        hcut hB hr here group hw
      exact ⟨hG, (head_members_reached h.scope h.reads O hr here Q.target).2.1⟩
    · cases c
  · rw [ei] at hr
    rcases hF with ⟨c, -⟩ | ⟨c, -⟩ | ⟨-, a, Q, here, laid, rfl⟩
    · cases c
    · cases c
    · obtain ⟨w, hw⟩ := row_at (m := 24) (by decide)
      obtain ⟨-, -, -, hG⟩ := fin_pinned_reached h.scope h.reads O h.laid.value h.laid.planOk hy
        hcut hB hr hb here laid hw
      exact ⟨hG, (fin_members_reached h.scope h.reads O hr hb here Q).2.1⟩

/-- **THE FIELD check OF `MadeAsks`, IN ITS OWN TEXT**: the program's test on the target says yes at
the statement behind the joins. -/
theorem check_at_yes (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hA : SwitchArm Zp Bs.G₀ p st before after) {R : List Fmt.RoundView} {C : List OpenedColumn}
    (hf : foldBlocks 0 (cF.blocksInOrder.take (P5J.At.ps.findIdx (· == p.place))) (ProofFile.startS Zp z₀) R C =
      .ok (s, [], [])) (hb : before s = .ok s₁) (nm : String)
    (A : AtYes (k2P Zp p.place nm st n) s₁ t r₁ r₂ gs x z S3 Y rows G cd) :
    switchTargetCheck S3 x.f.rows x.T = true :=
  check_at_S3 A.sent A.same (keptOld_of A.check (two_at_yes h O hA hf hb nm A).1) A.check

/-- What both of the next two spend: the eight at the front; the kept members lie below. -/
theorem shape_below_at_reach (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀) (hA : SwitchArm Zp Bs.G₀ p st before after)
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (P5J.At.ps.findIdx (· == p.place)) (z₀, s))
    (hb : before s = .ok s₁) (nm : String)
    (hx : frontAt (k2P Zp p.place nm st n) s₁ = some x) :
    VerifiableInference.Desc.K2.Honest.Returns.ShapeFits x ∧ KeptOld x.st x.f.rows := by
  obtain ⟨w, W, hw, hW, ht⟩ := front_test_at_reach h O hp hA hr hb nm hx
  obtain ⟨h1, h25⟩ := link_bounds h O hp hA
  have ht' := ht
  simp only [frontB2, Bool.and_eq_true] at ht'
  have Pn : Pinned (fxAt w) x := pin_facts ht'.1.1
  exact ⟨shape_of_test (List.mem_of_getElem? hw) hW (olds_once h1 h25) ht, Pn.below⟩

/-- **THE FIELD fits OF `MadeAsks`, IN ITS OWN TEXT.** -/
theorem fits_at_yes (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀) (hA : SwitchArm Zp Bs.G₀ p st before after)
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (P5J.At.ps.findIdx (· == p.place)) (z₀, s))
    (hb : before s = .ok s₁) (nm : String)
    (A : AtYes (k2P Zp p.place nm st n) s₁ t r₁ r₂ gs x z S3 Y rows G cd) :
    OldFits S3 x.f.rows := by
  obtain ⟨SF, hk⟩ := shape_below_at_reach h O hp hA hr hb nm A.front
  obtain ⟨hG, hn⟩ := good_named_at_reach h O hA hr hb nm A.front
  have F0 : OldFits x.st x.f.rows :=
    ⟨SF.mainVars, SF.d0, SF.d1, SF.rows, hn, SF.once, SF.keptCode, oldFits_stored hG.good _⟩
  have K : AlikeKept x.f.rows x.st z.st := ⟨A.sent.codes, fun o ho => A.sent.old o (hk o ho)⟩
  exact oldFits_of_tables A.same (K.oldFits F0)

/-- **THE FIELD seated OF `MadeAsks`, IN ITS OWN TEXT.** -/
theorem seated_at_yes (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀) (hA : SwitchArm Zp Bs.G₀ p st before after)
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) (P5J.At.ps.findIdx (· == p.place)) (z₀, s))
    (hb : before s = .ok s₁) (nm : String)
    (A : AtYes (k2P Zp p.place nm st n) s₁ t r₁ r₂ gs x z S3 Y rows G cd) :
    SeatedAt S3 x.f.rows x.T (z.ids.getD 0 noId) (z.ids.extract 1 (1 + x.T.kept.size)) := by
  obtain ⟨SF, hk⟩ := shape_below_at_reach h O hp hA hr hb nm A.front
  have hN : (switchNotices x.T x.others).size = 1 + x.T.kept.size + x.others.size :=
    notices_size x.T x.others
  have hg : z.ids.getD 0 noId = x.st.oracles.size := by
    rw [ids_at A.sent 0 (by omega)]
    rfl
  have ha := sent_kept A.sent x.T.kept.size (by omega)
  have hat : ∀ a, a < x.T.kept.size →
      (z.ids.extract 1 (1 + x.T.kept.size))[a]? = some (x.st.oracles.size + (1 + a)) :=
    fun a h' => by
      rw [← Array.getElem?_toList, ha]
      simp [h']
      omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨y, hy, e⟩ := g_at_S3 A.sent A.same
    rw [hg, hy, Option.map_some, e]
  · intro a k hka
    obtain ⟨h', rfl⟩ := Array.getElem?_eq_some_iff.1 hka
    obtain ⟨y, hy, e⟩ := copy_at_S3 A.sent A.same a h'
    rw [hat a h', Option.bind_some, hy, Option.map_some, e]
  · intro o ho
    rw [A.same.size, A.sent.size]
    have := hk o ho
    omega
  · rw [hg, ha]
    have hnew : ∀ v ∈ (List.range x.T.kept.size).map (· + (x.st.oracles.size + 1)),
        x.st.oracles.size < v := fun v hv => by
      obtain ⟨i, _, rfl⟩ := List.mem_map.1 hv
      omega
    refine List.nodup_cons.2 ⟨fun hin => ?_, List.Nodup.append
      ((List.nodup_range).map fun a b e => by omega) SF.once fun v h1 h2 => ?_⟩
    · rcases List.mem_append.1 hin with h' | h'
      · exact absurd (hnew _ h') (Nat.lt_irrefl _)
      · exact absurd (hk _ h') (Nat.lt_irrefl _)
    · have := hnew v h1
      have := hk v h2
      omega

end ProofFile.Honest.K2.Law

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K2.Law.shape_of_tables
#print axioms ProofFile.Honest.K2.Law.samples_of_tables
#print axioms ProofFile.Honest.K2.Law.oldFits_of_tables
#print axioms ProofFile.Honest.K2.Law.sent_kept
#print axioms ProofFile.Honest.K2.Law.link_bounds
#print axioms ProofFile.Honest.K2.Law.good_named_at_reach
#print axioms ProofFile.Honest.K2.Law.check_at_yes
#print axioms ProofFile.Honest.K2.Law.shape_below_at_reach
#print axioms ProofFile.Honest.K2.Law.fits_at_yes
#print axioms ProofFile.Honest.K2.Law.seated_at_yes
