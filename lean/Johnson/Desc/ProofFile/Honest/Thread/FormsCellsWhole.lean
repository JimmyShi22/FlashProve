-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FormsCellsWhole.lean: the open item `forms m k r` of the first
chain's invariant passes over the sending of a segment's digits (kind K1), the lookup on a segment's
digits (kind K3) and the draw of the smallness test (kind K8), at every `r`, "weights" included.
The invariant's `keeps` is `kpBy fHeadG` (FHeadG.lean). No definition.

FormsCells.lean, K8FormsCell.lean and CellsByKind.lean state these cells under a hypothesis `hwt` on
the letter `wt` at "weights". As it is stated there, `hwt` ranges over all pairs of states, so at
"weights" nobody can show it. The cells of this file have no such hypothesis and replace them.

How. At the library's data the letter `wt` is `wtK6` (Johnson/Desc/Kinds/Law/WtK6.lean). It reads no
string, and of the verifier's state it reads the statement `WeightAt` alone
(`AtTable.hmono_atAll`, `AtTable.hidle_atAll`, Johnson/Desc/Kinds/Law/WtK6Mono.lean). `WeightAt`
holds at both or at neither of two states in the relation `KeptW`, if the reader "heard" answers at
the earlier one (`weightAt_kept`, Johnson/Desc/Kinds/Law/WeightAtSame.lean). Where `WeightAt` holds,
that reader answers and the state stands in the output head's segment. The three kinds' clauses of
`keeps` give `KeptW` at such a state.

  1  `weightAt_stands`, `weightAt_fwd`, `wt_fwd`   the letter `wt` passes forward, if `KeptW` holds
     wherever the earlier state stands in the output head's segment
  2  `keptW_drawn`, `keptW_commit`, `keptW_digitsArms`, `keptW_k3Digits`, `keptW_k3Head`   `KeptW`
     from the clauses of K8, K1 and K3
  3  `forms_whole_k3`, `forms_whole_k1`, `forms_whole_k8`   the hypothesis `RidesPastAt`
     (Honest/Thread/Shares.lean) at the numbers `k3K l true`, `noL l true` and at a place of the
     kind K8
  4  `cellW_forms_k1`, `cellW_forms_k3`, `cellW_forms_k8`   the hypothesis `RidesPastAtS`
     (Honest/Thread/SharesS.lean) by the kind of the place

Limits.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * Nothing here shows that an item's statement holds at any state of a run.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.CellsByKind
import Johnson.Desc.Kinds.Law.KeptWLegs
import Johnson.Desc.Kinds.Law.WtK6Mono

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open OnBytes.PscRun (Later)
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (S Item HeadOwn)
open VerifiableInference.Desc.First.K8 (Drawn drawAt)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Kinds.Head.Law (WeightAt KeptW weightAt_kept keptW_putTl)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K1 (noL)
open VerifiableInference.OnPublicFiles (k3K)
open ProofFile.Honest.K3.Law.AtThr (k3KeepsAt rngWritten_holds)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-! ## 1 The letter `wt` passes forward -/

/-- Where `WeightAt` holds, the state stands in the output head's segment. -/
theorem weightAt_stands (W : OnBytes.Model.Verify.Public) {s : S} {c : _} {m : _}
    (H : WeightAt W s c m) : ∃ a, s.here = .head a := by
  obtain ⟨_, Hh, _, e, _⟩ := H
  revert e
  obtain ⟨st, book, roots, ro, fl, ck, out, here, req⟩ := s
  cases here with
  | head a => exact fun _ => ⟨a, rfl⟩
  | between => exact fun e => nomatch e
  | lay a => exact fun e => nomatch e
  | att a => exact fun e => nomatch e
  | fin a => exact fun e => nomatch e
  | mem a => exact fun e => nomatch e

/-- `WeightAt` passes forward. -/
theorem weightAt_fwd (W : OnBytes.Model.Verify.Public) {s s' : S}
    (hK : ∀ a, s.here = .head a → KeptW s s') {c : _} {m : _} (H : WeightAt W s c m) :
    WeightAt W s' c m := by
  obtain ⟨a, ha⟩ := weightAt_stands W H
  have H0 := H
  obtain ⟨_, Hh, _, e, _⟩ := H
  exact (weightAt_kept W (hK a ha) ⟨Hh, e⟩ c m).2 H0

/-! ## 2 `KeptW` from the three kinds' clauses -/

/-- The draw's writing. -/
theorem keptW_drawn {s s' : S} (hD : Drawn s s') {a : HeadOwn} (ha : s.here = .head a) :
    KeptW s s' := by
  obtain ⟨tl, mm, f, -, rfl⟩ := hD
  exact keptW_putTl ha _

/-- A segment's later sending. -/
theorem keptW_commit {s s' : S} (k : ProofFile.Honest.K1.K1CommitKeeps s s') {a : HeadOwn}
    (ha : s.here = .head a) : KeptW s s' := by
  obtain ⟨⟨-, hout, hreq, -⟩, -, -, L, F, tl, L', F', -, hF, -, hh, hS, -⟩ := k
  have hop : a.opened = true := by
    by_contra c
    simp [S.fork?, ha, c] at hF
  have eF : F = a.F := by
    simp [S.fork?, ha, hop] at hF
    exact hF.symm
  have e : ((s.putLink L').putFork F').here = .head { a with L := L', F := F' } := by
    obtain ⟨st, book, roots, ro, fl, ck, out, here, req⟩ := s
    obtain rfl : here = .head a := ha
    simp [S.putLink, S.putFork, hop]
  refine ⟨a, { a with L := L', F := F' }, ha, hh.trans e, rfl, rfl, rfl, rfl,
    congrArg (fun o => o.reply) hout, hreq, ?_⟩
  show Later a.F F'
  rw [← eF]
  exact hS.later

/-- The state after a lookup on the digits, by the sort of the segment. -/
theorem keptW_digitsArms {s s' : S} {tl' : OnBytes.Model.HTailF2} {F G' : OnBytes.Model.Fork}
    (hF : s.fork? = some F) (k : ProofFile.Honest.K3.Law.AtThr.DigitsArms s s' tl' G')
    (hl : Later F G') {a : HeadOwn} (ha : s.here = .head a) : KeptW s s' := by
  rcases k with ⟨a₀, e1, -⟩ | ⟨a₀, e1, -⟩ | ⟨a₀, e1, ho, rfl⟩
  · exact nomatch e1.symm.trans ha
  · exact nomatch e1.symm.trans ha
  · have eF : F = a₀.F := by
      simp [S.fork?, e1, ho] at hF
      exact hF.symm
    refine ⟨a₀, _, e1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    show Later a₀.F G'
    rw [← eF]
    exact hl

/-- The lookup on the digits of a feed-forward or an attention segment. -/
theorem keptW_k3Digits {hs : OnBytes.Model.Forest.Shape} {claims : Nat} {s s' : S}
    (k : ProofFile.Honest.K3.Law.AtThr.K3KeepsDigits hs claims s s') {a : HeadOwn}
    (ha : s.here = .head a) : KeptW s s' := by
  obtain ⟨-, tl, F, H, G, -, hF, hA, hL⟩ := k
  exact keptW_digitsArms hF hA
    (hL.1.trans (VerifiableInference.Desc.LinkJoin.later_plan G claims)) ha

/-- The lookup on the digits of the output head's segment. -/
theorem keptW_k3Head {hs : OnBytes.Model.Forest.Shape} {s s' : S}
    (k : ProofFile.Honest.K3.Law.AtThr.K3KeepsHead hs s s') : KeptW s s' := by
  obtain ⟨-, tl, F, H, G, a₀, claim, -, hF, e1, ho, rfl, hL⟩ := k
  have eF : F = a₀.F := by
    simp [S.fork?, e1, ho] at hF
    exact hF.symm
  refine ⟨a₀, _, e1, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  show Later a₀.F G
  rw [← eF]
  exact hL.1

/-! ## 1, 3 and 4 At the library's data and at the invariant -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The letter `wt` passes forward. -/
theorem wt_fwd {s s' : TS} (hK : ∀ a, s.here = .head a → KeptW s s') (m : Nat)
    (z : ProofFile.InstPub) (y y' : Strs) (v : WtF) (H₀ : h.𝔇.wt m (z, s) y v) :
    h.𝔇.wt m (z, s') y' v := by
  by_cases e : m = 24
  · subst e
    exact VerifiableInference.Desc.Kinds.Head.Law.AtTable.hmono_atAll h (z, s') (z, s) y' y v
      (fun _ _ W => weightAt_fwd _ hK W) H₀
  · exact VerifiableInference.Desc.Kinds.Head.Law.AtTable.hidle_atAll h m e _ _ _

variable (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)

/-- The item passes over the lookup on the digits of segment `l`. -/
theorem forms_whole_k3 {l : Nat} (hl : l < 25) (m k : Nat) (ρ : String)
    (ho : Item.forms m k ρ ∈ IM.openAt P5J.At.links P5J.At.ps (k3K l true))
    (ho' : Item.forms m k ρ ∈ IM.openAt P5J.At.links P5J.At.ps (k3K l true + 1)) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread
      (k3K l true) (Item.forms m k ρ) := by
  have t := List.all_eq_true.1 rels_none_missed l (List.mem_range.2 hl)
  simp only [Bool.and_eq_true] at t
  have hp : P5J.At.ps[k3K l true]? = some (IM.k3Place l true) := eq_of_beq t.1.2
  have hc : (IM.k3Place l true).piece = 7 ∨ (IM.k3Place l true).piece = 8 := by
    simpa using t.2
  have hparts : ∀ s s', k3KeepsAt Zp (IM.k3Place l true) s s' →
      (∀ a, segAt? s = some a → ∃ b', segAt? s' = some b' ∧ b'.L = a.L ∧ b'.d.st = a.d.st ∧
        b'.d.book = a.d.book ∧ Later a.F b'.F) ∧ ∀ a, s.here = .head a → KeptW s s' := by
    by_cases e : l = 24
    · subst e
      obtain ⟨sh, hh⟩ := fHead_h3H h rngWritten_holds
      exact fun s s' a => ⟨k3Head_part (hh s s' a), fun _ _ => keptW_k3Head (hh s s' a)⟩
    · obtain ⟨sh, claims, hh⟩ := fHead_h3 h rngWritten_holds (l := l) (by omega)
      have ep : IM.k3Place l true =
          { chain := 1, link := some l, piece := 7, kind := KindName.K3 } := by
        show (⟨1, some l, (6 + if l = 24 then 1 else 0) + 1, KindName.K3⟩ : Place) = _
        rw [if_neg e]
      rw [ep]
      exact fun s s' a => ⟨k3Digits_part (hh s s' a), fun _ ha => keptW_k3Digits (hh s s' a) ha⟩
  exact forms_cell_later h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hp m k ρ ho ho'
    fun s s' a => ⟨(hparts s s' a.1.1).1, a.2 hc, a.1.2,
      fun _ z y y' v => wt_fwd h (hparts s s' a.1.1).2 m z y y' v⟩

/-- The item passes over the sending of the digits of segment `l`. -/
theorem forms_whole_k1 {l : Nat} (hl : l < 25) (m k : Nat) (ρ : String)
    (ho : Item.forms m k ρ ∈ IM.openAt P5J.At.links P5J.At.ps (noL l true))
    (ho' : Item.forms m k ρ ∈ IM.openAt P5J.At.links P5J.At.ps (noL l true + 1)) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread
      (noL l true) (Item.forms m k ρ) := by
  have t := List.all_eq_true.1 rels_none_missed l (List.mem_range.2 hl)
  simp only [Bool.and_eq_true] at t
  have hp : P5J.At.ps[noL l true]? = some (IM.k1PlaceL l true) := eq_of_beq t.1.1.1
  have hc : (IM.k1PlaceL l true).piece = 6 ∨ (IM.k1PlaceL l true).piece = 7 := by
    simpa using t.1.1.2
  have hrest : ∀ s s', ProofFile.Honest.K1.K1KeepsAt (IM.k1PlaceL l true) s s' →
      ProofFile.Honest.K1.K1CommitKeeps s s' := by
    by_cases e : l = 24
    · subst e
      exact fun s s' a => (show ProofFile.Honest.K1.K1CommitKeepsM s s' from a).1
    · have ep : IM.k1PlaceL l true =
          { chain := 1, link := some l, piece := 6, kind := KindName.K1 } := by
        show (⟨1, some l, (5 + if l = 24 then 1 else 0) + 1, KindName.K1⟩ : Place) = _
        rw [if_neg e]
      rw [ep]
      exact fun s s' a => (show ProofFile.Honest.K1.K1CommitKeepsM s s' from a).1
  have h1 : (IM.k1PlaceL l true).piece ≠ 1 := by
    rcases hc with hc | hc <;> rw [hc] <;> decide
  exact forms_cell_rec h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w (l := l) hp m k ρ ho ho'
    fun s s' a => by
      have c := hrest s s' ((fHead_K1_later Zp cF G take P11 p12 P13
        (p := IM.k1PlaceL l true) (l := l) rfl h1 s s').1 a.1.1).1
      exact ⟨c.1, a.2 l rfl hc, a.1.2,
        fun _ z y y' v => wt_fwd h (fun _ ha => keptW_commit c ha) m z y y' v⟩

/-- The item passes over the draw of the smallness test, at every place of the kind K8. -/
theorem forms_whole_k8 {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hκ : p.kind = KindName.K8) (m k : Nat) (ρ : String)
    (ho : Item.forms m k ρ ∈ IM.openAt P5J.At.links P5J.At.ps b)
    (ho' : Item.forms m k ρ ∈ IM.openAt P5J.At.links P5J.At.ps (b + 1)) :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread
      b (Item.forms m k ρ) :=
  forms_cell_later h H Q test carryX item n₁ n₂ b₀ Vd Rd
    (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hp m k ρ ho ho'
    fun s s' a => by
      obtain ⟨hl, e⟩ := k8_number hb hp hκ
      have a' : fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD KindName.K8 p s s' :=
        (kpBy_at _ hκ s s').1 a
      have hD : Drawn s s' := k8Keeps_drawn a'.1.1.1
      exact ⟨drawn_part hD, k8_readersStayAt h hl (by rw [← e]; exact hp) hD, a'.1.2,
        fun _ z y y' v => wt_fwd h (fun _ ha => keptW_drawn hD ha) m z y y' v⟩

variable (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- The item `forms m k r` at a place of the kind K1. -/
theorem cellW_forms_k1 {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K1) {m k : Nat} {ρ : String}
    (hi : Item.forms m k ρ ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.opened b)
    (h1 : Item.forms m k ρ ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.row b).shuts) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.forms m k ρ) := by
  obtain ⟨ho, ho'⟩ := head_open_both h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hb hi h1 (fun e => by cases e)
  obtain ⟨l, hl, rfl⟩ := forms_k1_number hb hp hk ho
  exact ridesPastAtS_of _ _ (forms_whole_k1 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take
    P11 p12 P13 hl m k ρ ho ho')

/-- The item `forms m k r` at a place of the kind K3. -/
theorem cellW_forms_k3 {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K3) {m k : Nat} {ρ : String}
    (hi : Item.forms m k ρ ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.opened b)
    (h1 : Item.forms m k ρ ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.row b).shuts) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.forms m k ρ) := by
  obtain ⟨ho, ho'⟩ := head_open_both h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hb hi h1 (fun e => by cases e)
  obtain ⟨l, hl, rfl⟩ := forms_k3_number hb hp hk ho
  exact ridesPastAtS_of _ _ (forms_whole_k3 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take
    P11 p12 P13 hl m k ρ ho ho')

/-- The item `forms m k r` at a place of the kind K8. -/
theorem cellW_forms_k8 {b : Nat} {p : Place} (hb : b < 358) (hp : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K8) {m k : Nat} {ρ : String}
    (hi : Item.forms m k ρ ∈ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.opened b)
    (h1 : Item.forms m k ρ ∉ ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread.row b).shuts) :
    RidesPastAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w).thread Said
      b (Item.forms m k ρ) := by
  obtain ⟨ho, ho'⟩ := head_open_both h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy (fHeadG Zp cF G take P11 p12 P13 h.𝔇.pubD)) w hb hi h1 (fun e => by cases e)
  exact ridesPastAtS_of _ _ (forms_whole_k8 h H Q test carryX item n₁ n₂ b₀ Vd Rd w G take
    P11 p12 P13 hb hp hk m k ρ ho ho')

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.weightAt_stands
#print axioms ProofFile.Honest.FirstThread.weightAt_fwd
#print axioms ProofFile.Honest.FirstThread.keptW_drawn
#print axioms ProofFile.Honest.FirstThread.keptW_commit
#print axioms ProofFile.Honest.FirstThread.keptW_digitsArms
#print axioms ProofFile.Honest.FirstThread.keptW_k3Digits
#print axioms ProofFile.Honest.FirstThread.keptW_k3Head
#print axioms ProofFile.Honest.FirstThread.wt_fwd
#print axioms ProofFile.Honest.FirstThread.forms_whole_k3
#print axioms ProofFile.Honest.FirstThread.forms_whole_k1
#print axioms ProofFile.Honest.FirstThread.forms_whole_k8
#print axioms ProofFile.Honest.FirstThread.cellW_forms_k1
#print axioms ProofFile.Honest.FirstThread.cellW_forms_k3
#print axioms ProofFile.Honest.FirstThread.cellW_forms_k8
