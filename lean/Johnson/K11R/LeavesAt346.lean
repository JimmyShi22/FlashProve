-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K11R/LeavesAt346.lean: FOR THE FIELD
"leaves" OF THE MERGE'S NAMED CONDITION (K11/LawAtMg.lean: K11Cond): A FACT ALONG "REACHED", UNDER
ONE NAMED PREMISE: in the goals' scope, at the hash secondHashFunction, at an opening: at every state that is
reached at border 346 of the first chain's flat list the test leavesLenB (MergeLaw/RunsLate.lean)
accepts: the walk of the sumcheck over the leaves that the lookup on the calls has heard has
1 + 2 d + 5 members, d its own shape's.

THE ONE PREMISE, hSz: at EVERY state that is reached at border 340 the open ledger has its sizes
(Sized): it is asked without the clause "that bears no mark". It is shown by nobody here. The
lookups' sized_upTo (First/Look/K03RowsBare.lean) has it at the 24 links in front of the head's
alone.

THE ROAD. Number 340 is the lookup on the calls: its accept from a ledger with its sizes lays what
it heard, and the walk has that length (decide_exact, PadExact.len). Numbers 341 to 345
(the head's own rounds; a later sending with the step that lays the tables; the smallness test; a
later sending; the lookup on the digits) leave what was heard at the calls' seat.

  decide_len, via_len, stated_len   what an accept of a lookup leaves as heard has that length
  KeepsLook s t     what the lookup on the calls has heard at s stands at t
  stated_keeps      the lookup on the digits keeps it
  k6_keeps, commit_keepsL, readsQuietAt_keeps, k1Reads_keeps, k8_keeps   the four other makers
  seated_five       numbers 341 to 345 of the flat list keep it
  seated_calls      number 340 makes it, from a ledger with its sizes
  leaves_reach      THE TOP, along "reached"
  leaves_at346      in the form of the facts along "reached" (∀ a, Rch 346 a → no mark → the test
                    accepts), general in a family Rch that gives the description's own "reached" at
                    346. THE FIELD ITSELF HAS ANOTHER FORM (two binders z and a, the table's promise
                    at 346 in front, a double negation): this file does not hold the one against
                    the other; K11/CondOfRest.lean does

Limits. hSz is a premise. A law from accepts: idle where nothing is reached. leaves_reach is general
in the number ft of the first tree; it is spent at 0 alone. No soundness statement.

-/
import Johnson.K11R.MaskSeat
import Johnson.Top.H0.MergeLaw.RunsLate
import Johnson.Top.H.Keep.PadExact
import Johnson.Top.H.Keep.RowsBare
import Johnson.Desc.First.Look.K03States
import Johnson.Desc.First.Look.K03PlanOf
import Johnson.Desc.First.Look.K3StatedSteps
import Johnson.Desc.First.K8.LawRuns
import Johnson.Desc.Kinds.Law.RowPins
import Johnson.Desc.Kinds.Law.HeadPlanesFive
import Johnson.Desc.Kinds.Law.HeadPlanesHost

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.PscRun
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat SeatReads seatCalls seatDigits pieceAt)

/-- What an accept of K3.block lays as heard: the walk over the leaves has its length. -/
theorem decide_len {T Cl : Type} (seat : Seat T Cl) (hR : SeatReads seat) (piece : ℕ)
    (laid : Array Nat) (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest T Cl)) (s s' : T) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s')
    (hS : ∀ F, seat.fork s = some F → Sized F) :
    ∃ g, seat.heard s' = some g ∧ lvLen g = 1 + 2 * g.shape.d + 5 := by
  obtain ⟨F0, x, hF0, hn, rfl, hP⟩ := decide_exact seat piece laid before p guests s s' rs cols hd
  exact ⟨x.1, hR s x.1 x.2 (by rw [hF0]; rfl) hn, (hP (hS F0 hF0)).1.len⟩

/-- The like of the block that hears on a view's rounds, under its test on the plan. -/
theorem via_len {T Cl : Type} (seat : Seat T Cl) (hR : SeatReads seat) (piece : ℕ)
    (laid : Array Nat) (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest T Cl)) (s s' : T) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64)))
    (hplan : (Desc.K3.Law.blockVia seat piece laid before p guests).planOk = true)
    (hd : (Desc.K3.Law.blockVia seat piece laid before p guests).decide s rs cols = .ok s')
    (hS : ∀ F, seat.fork s = some F → Sized F) :
    ∃ g, seat.heard s' = some g ∧ lvLen g = 1 + 2 * g.shape.d + 5 :=
  decide_len seat hR piece laid before p guests s s' rs cols
    (Desc.K3.Law.blockVia_decide hplan hd) hS

section
variable {Cl : Type}

/-! Four small laws on the two seats. The lookups have them (First/Look/K03RowsBare.lean:
seatOf_reads, seatOf_fork, seatOf_putFork, seatOf_headClaim); they are
shown here, under names of their own. -/

theorem lvSeat_reads (claim : Aff → Cl) (d : Bool) : Desc.K3.SeatReads (seatOf claim d) := by
  cases d
  · exact Desc.K3.seatCalls_reads claim
  · exact Desc.K3.seatDigits_reads claim

theorem lvSeat_fork (claim : Aff → Cl) (d : Bool) (s : S) : (seatOf claim d).fork s = s.fork? := by
  cases d <;> rfl

theorem lvSeat_putFork (claim : Aff → Cl) (d : Bool) (s : S) (G : Fork) :
    (seatOf claim d).heard (S.putFork s G) = (seatOf claim d).heard s := by
  cases d
  · exact lookHeard_putFork s G
  · exact congrArg (fun x : Option HTailF2 => x.bind (·.heard)) (tl_putFork s G)

theorem lvSeat_headClaim (claim : Aff → Cl) (d : Bool) (s : S) (a : Desc.First.HeadOwn) (c : _)
    (ha : s.here = .head a) :
    (seatOf claim d).heard { s with here := .head { a with claim := some c } } =
      (seatOf claim d).heard s := by
  cases d
  · have k : S.lookHeard? ({ s with here := .head { a with claim := some c } } : S) =
        S.lookHeard? s := by simp [S.lookHeard?, ha]
    exact k
  · have k : tlHeard ({ s with here := .head { a with claim := some c } } : S) = tlHeard s := by
      simp [tlHeard, S.tl?, ha]
    exact k

/-- **What an accept of the stated lookup leaves as heard: the walk has its length.** -/
theorem stated_len (claim : Aff → Cl) (readers : ℕ → Option (Desc.K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (d : Bool) (hl : a.link = some i) (hpc : a.piece = pieceAt X i d) (s t : S)
    (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) (hdec : B.decide s rs gs = .ok t)
    (hS : ∀ F, s.fork? = some F → Sized F) :
    ∃ g, (seatOf claim d).heard t = some g ∧ lvLen g = 1 + 2 * g.shape.d + 5 := by
  obtain ⟨B₁, h1, -, ed, -, ep⟩ := Desc.K3.theStated_is claim readers X codes shape a B h
  obtain ⟨b, hb, hw⟩ := Desc.K3.theWhole_is claim true X codes shape a B₁ h1
  obtain ⟨i', digits, p, sent, laid, hl', hpc', -, -, -, -, edb, -, hpb⟩ :=
    Desc.K3.theOwn_is claim true X codes shape a b hb
  obtain rfl : i = i' := Option.some.inj (hl.symm.trans hl')
  obtain rfl : d = digits := Desc.K3.pieceAt_inj X i (hpc.symm.trans hpc')
  rw [ed] at hdec
  rw [ep] at hOk
  have e : Desc.K3.seatOfLookupOnDigitsOrCalls claim d = seatOf claim d := by
    cases d <;> simp [Desc.K3.seatOfLookupOnDigitsOrCalls, seatOf]
  have own : ∀ (s₁ : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
      b.planOk = true → b.decide s rs gs = .ok s₁ →
      ∃ g, (seatOf claim d).heard s₁ = some g ∧ lvLen g = 1 + 2 * g.shape.d + 5 := by
    intro s₁ rs gs hp hdc
    rw [edb, e] at hdc
    have hv := hpb hp
    rw [e] at hv
    exact via_len _ (lvSeat_reads claim d) _ _ _ _ _ s s₁ rs gs hv hdc
      fun F hF => hS F ((lvSeat_fork claim d s).symm.trans hF)
  rcases hw with ⟨-, rfl⟩ | ⟨f, hf', rfl⟩
  · exact own t rs gs hOk hdec
  · have hp : b.planOk = true := by
      simpa [Desc.Block.andThen, Desc.roundlessBlock] using hOk
    obtain ⟨i', -, hf''⟩ := Option.bind_eq_some_iff.1 hf'
    have hdec' : (b.decide s (rs.take b.rounds.length) (gs.take b.openings)).bind
        (fun s₁ => f s₁) = .ok t := hdec
    cases hb1 : b.decide s (rs.take b.rounds.length) (gs.take b.openings) with
    | error x =>
      rw [hb1] at hdec'
      have k : (Except.error x : Except String S) = .ok t := hdec'
      cases k
    | ok s₁ =>
      rw [hb1] at hdec'
      have hq : f s₁ = .ok t := hdec'
      obtain ⟨g, hg, hlen⟩ := own s₁ _ _ hp hb1
      exact ⟨g, (quietAt_frame (seatOf claim d).heard (lvSeat_putFork claim d)
        (lvSeat_headClaim claim d) X i' _ f hf'' s₁ t hq).1 g hg, hlen⟩

/-- What the lookup on the calls has heard at s stands at t. -/
def KeepsLook (s t : S) : Prop := ∀ g, s.lookHeard? = some g → t.lookHeard? = some g

theorem keepsLook_of_eq {s t : S} (e : t.lookHeard? = s.lookHeard?) : KeepsLook s t :=
  fun g hg => e.trans hg

theorem KeepsLook.trans {a b c : S} (h : KeepsLook a b) (k : KeepsLook b c) : KeepsLook a c :=
  fun g hg => k g (h g hg)

/-- What the digits' seat lays leaves what the calls' seat holds. -/
theorem lvDigits_put_look (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    ((seatDigits claim).put s g G).lookHeard? = s.lookHeard? := by
  show (match s.tl?, s.fork? with
    | some tl, some F => (s.putTl _).putFork G
    | _, _ => s.mark _).lookHeard? = s.lookHeard?
  split
  · rw [lookHeard_putFork, lookHeard_putTl]
  · exact lookHeard_mark s _

/-- **The stated lookup on the digits keeps what the lookup on the calls has heard.** -/
theorem stated_keeps (claim : Aff → Cl) (readers : ℕ → Option (Desc.K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (i : ℕ) (hl : a.link = some i) (hpc : a.piece = pieceAt X i true) (s t : S)
    (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) (hdec : B.decide s rs gs = .ok t) :
    KeepsLook s t := by
  obtain ⟨B₁, h1, -, ed, -, ep⟩ := Desc.K3.theStated_is claim readers X codes shape a B h
  obtain ⟨b, hb, hw⟩ := Desc.K3.theWhole_is claim true X codes shape a B₁ h1
  obtain ⟨i', digits, p, sent, laid, hl', hpc', -, -, -, -, edb, -, hpb⟩ :=
    Desc.K3.theOwn_is claim true X codes shape a b hb
  obtain rfl : i = i' := Option.some.inj (hl.symm.trans hl')
  obtain rfl : true = digits := Desc.K3.pieceAt_inj X i (hpc.symm.trans hpc')
  rw [ed] at hdec
  rw [ep] at hOk
  have e : Desc.K3.seatOfLookupOnDigitsOrCalls claim true = seatDigits claim := by simp [Desc.K3.seatOfLookupOnDigitsOrCalls]
  have own : ∀ (s₁ : S) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
      b.planOk = true → b.decide s rs gs = .ok s₁ → KeepsLook s s₁ := by
    intro s₁ rs gs hp hdc
    rw [edb, e] at hdc
    have hv := hpb hp
    rw [e] at hv
    obtain ⟨F0, x, -, -, rfl, -⟩ := decide_exact _ _ _ _ _ _ s s₁ rs gs
      (Desc.K3.Law.blockVia_decide hv hdc)
    exact keepsLook_of_eq (lvDigits_put_look claim s x.1 x.2)
  rcases hw with ⟨-, rfl⟩ | ⟨f, hf', rfl⟩
  · exact own t rs gs hOk hdec
  · have hp : b.planOk = true := by
      simpa [Desc.Block.andThen, Desc.roundlessBlock] using hOk
    obtain ⟨i', -, hf''⟩ := Option.bind_eq_some_iff.1 hf'
    have hdec' : (b.decide s (rs.take b.rounds.length) (gs.take b.openings)).bind
        (fun s₁ => f s₁) = .ok t := hdec
    cases hb1 : b.decide s (rs.take b.rounds.length) (gs.take b.openings) with
    | error x =>
      rw [hb1] at hdec'
      have k : (Except.error x : Except String S) = .ok t := hdec'
      cases k
    | ok s₁ =>
      rw [hb1] at hdec'
      have hq : f s₁ = .ok t := hdec'
      exact (own s₁ _ _ hp hb1).trans
        (quietAt_frame (seatOf claim false).heard (lvSeat_putFork claim false)
          (lvSeat_headClaim claim false) X i' _ f hf'' s₁ t hq).1

end

end VerifiableInference.OnPublicFiles

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc.Keeps (Decides Whole)
open Johnson.Desc.First.Walk.Tied (Reach RchAt rchAt_raw stepYes_decide)
open VerifiableInference.OnPublicFiles (KeepsLook keepsLook_of_eq stated_keeps stated_len lvLen seatOf)
open ProofFile (Cl)

/-! ## The test rides on what is kept -/

theorem leaves_keeps {s t : S} (k : KeepsLook s t) (h : leavesLenB s = true) :
    leavesLenB t = true := by
  unfold leavesLenB at h ⊢
  cases hg : s.lookHeard? with
  | none =>
    rw [hg] at h
    cases h
  | some g =>
    rw [hg] at h
    rw [k g hg]
    exact h

theorem leaves_of_len {t : S} {g : OnBytes.Model.Forest.Heard} (hg : t.lookHeard? = some g)
    (h : lvLen g = 1 + 2 * g.shape.d + 5) : leavesLenB t = true := by
  unfold leavesLenB
  rw [hg]
  exact beq_iff_eq.2 h

/-! ## The makers at numbers 341 to 345 -/

section
variable {Cl' : Type}

/-- The output head's own rounds. -/
theorem k6_keeps {W : OnBytes.Model.Verify.Public} {l : ℕ} {before : List (ℕ × ℕ)}
    {b : Block S Claim} (h : Kinds.Head.seatedClaims W l before = some b) :
    Decides KeepsLook b := by
  intro s rs gs t hd
  unfold Kinds.Head.seatedClaims at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold Kinds.Head.blockClaims at h0
  obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.1 h0
  have L : Kinds.Head.Law.Leaves (fun s : S => s.lookHeard?)
      (Kinds.Head.kind Kinds.Head.asClaim (Kinds.Head.seatAt W.hS iU3) l 4
        (Kinds.Head.parOf W.hS ((Params.settingOf W.P.frame).workOf .field .request))) := by
    refine Kinds.Head.Law.k6_leaves _ (Kinds.Head.seatAt W.hS iU3) l 4 _ _ ?_ ?_ ?_
    · intro s F s1 e
      rw [Kinds.Head.Law.putFork?_ok (show s.putFork? F = .ok s1 from e),
        Kinds.Head.Law.Came.lookHeard_putFork]
    · intro s H s2 e
      exact Kinds.Head.Law.Came.lookHeard_setHeard W.hS iU3 e
    · intro s w
      rfl
  unfold Kinds.Head.tested at hd
  dsimp only at hd
  split at hd
  · exact keepsLook_of_eq (L s rs gs t hd)
  · cases hd

/-- A segment's later sending. -/
theorem laterAt_keeps (q : Params.First) (gp : _root_.Desc.Plain.GPar) (link piece moment : ℕ)
    (arrays : Option (List ℕ)) :
    Decides KeepsLook (K1.laterAt (Cl := Cl') q gp link piece moment arrays) :=
  fun _ _ _ _ h => keepsLook_of_eq (Kinds.Head.Law.commit_keeps h).2

/-- The smallness test. -/
theorem k8_keeps (p : K8.ParW) : Decides KeepsLook (K8.whole p) :=
  fun s rs gs t h => keepsLook_of_eq ((K8.whole_leaves_fork_look p).2 s rs gs t h)

/-- Two sub-protocols as one. -/
theorem keeps_andThen {p q : Block S Cl'} (hp : Decides KeepsLook p) (hq : Decides KeepsLook q)
    (n : String) : Decides KeepsLook (p.andThen n q) := by
  intro s rs gs s' h
  have h' : (p.decide s (rs.take p.rounds.length) (gs.take p.openings)).bind
      (fun t => q.decide t (rs.drop p.rounds.length) (gs.drop p.openings)) = .ok s' := h
  obtain ⟨t, h1, h2⟩ := Keeps.ebind_ok h'
  exact (hp _ _ _ _ h1).trans (hq _ _ _ _ h2)

end

/-- The step that lays the tables, at a layers' or the head's segment. -/
theorem readsBlockAt_keeps {G : Array OnBytes.Model.Layer.HPlan2} {hS : OnBytes.Model.Head.Shape}
    {HLy : OnBytes.Model.Head.HL} {Hp : OnBytes.Model.Head.HPlanH2} {kinds : List (ℕ × ℕ)} {l : ℕ}
    {b : Block S Unit} (h : K8.ReadsQuiet.blockAt G hS HLy Hp kinds l = some b) :
    Whole KeepsLook b := by
  unfold K8.ReadsQuiet.blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
    refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
    obtain ⟨a, own, tl', ha, -, -, rfl⟩ := K8.ReadsQuiet.layers_ok h
    exact keepsLook_of_eq (by simp [S.lookHeard?, ha])
  · split at h
    · cases h
      exact ⟨fun s rs gs s' h => keepsLook_of_eq (Kinds.Head.Law.readsQuiet_keeps h).2.1,
        (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
    · cases h

/-- The like at an attention segment. -/
theorem readsAtO_keeps {W : OnBytes.Model.Verify.Public} {l g : ℕ} {b : Block S Unit}
    (h : Att.readsAtO W l g = some b) : Whole KeepsLook b := by
  unfold Att.readsAtO at h
  obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
  refine ⟨fun s _ _ s' e => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  obtain ⟨a, t, tl, ha, rfl⟩ := _root_.Meaning.K2.readsAtSO_eq e
  exact keepsLook_of_eq (by simp [S.lookHeard?, ha])

theorem readsQuietAt_keeps {G : ProofFile.Ground} {l : ℕ} {X : OnBytes.Model.Stages.LinkH} {piece : ℕ}
    {b : Block S Unit} (h : ProofFile.readsQuietAt G l X piece = some b) : Whole KeepsLook b := by
  unfold ProofFile.readsQuietAt at h
  repeat' split at h
  all_goals first
    | exact readsAtO_keeps h
    | exact readsBlockAt_keeps h
    | cases h

/-- The sending in front of the smallness test, with the step that lays the tables. -/
theorem k1Reads_keeps (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : OnBytes.Model.Stages.LinkH)
    (pr : ℕ) (reads : Option (List ℕ)) : Decides KeepsLook (IM.k1Reads Z G l X pr reads) :=
  keeps_andThen (laterAt_keeps G.first (K1.gpOf Z) l pr 1 reads) (q := IM.k1Quiet G l X)
    (_root_.Meaning.K2.orLoud_whole fun _ hb => readsQuietAt_keeps hb).1 _

/-! ## At the chain's flat list -/

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

theorem k1_head_keeps (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {i : ℕ} (hi : i = 4 ∨ i = 6) :
    ∃ Lk b, c.links[24]? = some Lk ∧ Lk.hear[i]? = some b ∧ Decides KeepsLook b := by
  have hk : (kindsBeforeBatching .head (24 == 0))[i]? = some KindName.K1 := by
    rcases hi with rfl | rfl <;> (unfold kindsBeforeBatching; rfl)
  obtain ⟨Lk, b, Xl, pr, pd, reads, digits, eL, e, -, hn, harm⟩ :=
    IM.k1_later O 24 .head (IM.subs_head hS hR O.pub O.blank) i hk
      (by rcases hi with rfl | rfl <;> decide)
  refine ⟨Lk, b, eL, e, ?_⟩
  have hp := IM.numbers_pieces hn
  rcases hi with rfl | rfl
  · rcases harm with ⟨h5, la⟩ | ⟨h5, -⟩
    · exact alone_decides (by intro k; cases k) la
        (retype_decides (k1Reads_keeps Z Bs.G₀ 24 Xl pr reads))
    · omega
  · rcases harm with ⟨h7, -⟩ | ⟨h7, la⟩
    · omega
    · exact alone_decides (by intro k; cases k) la
        (retype_decides (laterAt_keeps Bs.G₀.first (K1.gpOf Z) 24 pd 2 digits))

/-- **Numbers 341 to 345 of the flat list keep what the lookup on the calls has heard.** -/
theorem seated_five (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true) :
    ∀ i, i < 5 → ∃ b, c.blocksInOrder[341 + i]? = some b ∧ Decides KeepsLook b := by
  intro i hi
  obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  · obtain ⟨Lk, b, b', ms, eL, e, -, k6, la, -⟩ := IM.k6_of hS hR O
    exact ⟨b, flat_at hS hR O eL e rfl, alone_decides (by intro k; cases k) la (k6_keeps k6)⟩
  · obtain ⟨Lk, b, eL, e, hd⟩ := k1_head_keeps hS hR O (Or.inl rfl)
    exact ⟨b, flat_at hS hR O eL e rfl, hd⟩
  · obtain ⟨Lk, b, Xl, eL, e, -, la, -⟩ := IM.k8_of_head hS hR O
    exact ⟨b, flat_at hS hR O eL e rfl, alone_decides (by intro k; cases k) la (k8_keeps _)⟩
  · obtain ⟨Lk, b, eL, e, hd⟩ := k1_head_keeps hS hR O (Or.inr rfl)
    exact ⟨b, flat_at hS hR O eL e rfl, hd⟩
  · obtain ⟨Lk, b, b', eL, e, k3, la⟩ := IM.k3_of hS hR O 24 (by decide) true
    have e' : Lk.hear[7]? = some b := e
    obtain ⟨b'', k3', hk⟩ := VerifiableInference.OnPublicFiles.k03_const_ok hS hR O hOk 24 (by omega) true
    obtain rfl : b' = b'' := Option.some.inj (k3.symm.trans k3')
    exact ⟨b, flat_at hS hR O eL e' rfl, alone_decides (by intro k; cases k) la
      fun s rs gs t hd => stated_keeps _ _ _ _ _ _ b' k3 hk 24 rfl
        (_root_.K3Lot.k03_place _ _ _ _ _ 24 true b' k3).1 s t rs gs hd⟩

/-- **Number 340 makes it, from a ledger with its sizes.** -/
theorem seated_calls (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true) :
    ∃ b, c.blocksInOrder[340]? = some b ∧
      Decides (fun s t => (∀ G, s.fork? = some G → Sized G) → leavesLenB t = true) b := by
  obtain ⟨Lk, b, b', eL, e, k3, la⟩ := IM.k3_of hS hR O 24 (by decide) false
  have e' : Lk.hear[2]? = some b := e
  obtain ⟨b'', k3', hk⟩ := VerifiableInference.OnPublicFiles.k03_const_ok hS hR O hOk 24 (by omega) false
  obtain rfl : b' = b'' := Option.some.inj (k3.symm.trans k3')
  refine ⟨b, flat_at hS hR O eL e' rfl, alone_decides (by intro k; cases k) la
    fun s rs gs t hd hSz => ?_⟩
  obtain ⟨g, hg, hlen⟩ := stated_len _ _ _ _ _ _ b' k3 hk 24 false rfl
    (_root_.K3Lot.k03_place _ _ _ _ _ 24 false b' k3).1 s t rs gs hd hSz
  exact leaves_of_len hg hlen

/-- n steps back over sub-protocols that keep it. -/
theorem back_keeps {Pp : Type} {ft : ℕ} {bs : List (Block S Cl)} {start : Pp → S} {k : ℕ} :
    ∀ n : ℕ, (∀ i, i < n → ∃ b, bs[k + i]? = some b ∧ Decides KeepsLook b) →
    ∀ (z : Pp) (s' : S), Reach ft bs start (k + n) (z, s') →
      ∃ s, Reach ft bs start k (z, s) ∧ KeepsLook s s'
  | 0, _, _, s', h => ⟨s', h, fun _ hg => hg⟩
  | n + 1, hk, z, s', h => by
    obtain ⟨t, b, hr, hb, hy⟩ := reach_pred h (k + n) rfl
    obtain ⟨b', hb', hd⟩ := hk n (Nat.lt_succ_self n)
    obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
    obtain ⟨rs, gs, hyes⟩ := stepYes_decide hy
    obtain ⟨s, hs, hst⟩ := back_keeps n (fun i hi => hk i (Nat.lt_succ_of_lt hi)) z t hr
    exact ⟨s, hs, hst.trans (hd t rs gs s' hyes)⟩

/-- **THE TOP, ALONG "REACHED".** -/
theorem leaves_reach (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true) {ft : ℕ}
    (hSz : ∀ a, Reach ft c.blocksInOrder (ProofFile.startS Z) 340 a → ∀ G, a.2.fork? = some G → Sized G)
    {a : ProofFile.InstPub × S} (R : Reach ft c.blocksInOrder (ProofFile.startS Z) 346 a) :
    leavesLenB a.2 = true := by
  obtain ⟨s₁, R₁, k⟩ := back_keeps (k := 341) 5 (seated_five hS hR O hOk) a.1 a.2 R
  obtain ⟨s₀, b, R₀, hb, hy⟩ := reach_pred R₁ 340 rfl
  obtain ⟨b', hb', hd⟩ := seated_calls hS hR O hOk
  obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
  obtain ⟨rs, gs, hyes⟩ := stepYes_decide hy
  exact leaves_keeps k (hd s₀ rs gs s₁ hyes (hSz _ R₀))

/-- **The fact along "reached" that the field "leaves" wants, under hSz.** -/
theorem leaves_at346 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {Fr : Sound.Frame} (Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop)
    (hsub : ∀ a, Rch 346 a → RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B
      (fun s => s) (ProofFile.startS Z) c) 346 a)
    (hSz : ∀ a, Reach 0 c.blocksInOrder (ProofFile.startS Z) 340 a → ∀ G, a.2.fork? = some G → Sized G) :
    ∀ a, Rch 346 a → a.1.2.failed = none → leavesLenB a.1.2 = true :=
  fun a hr _ => leaves_reach hS hR O hOk hSz (rchAt_raw (hsub a hr))

end

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.OnPublicFiles.decide_len
#print axioms VerifiableInference.OnPublicFiles.via_len
#print axioms VerifiableInference.OnPublicFiles.lvSeat_reads
#print axioms VerifiableInference.OnPublicFiles.lvSeat_fork
#print axioms VerifiableInference.OnPublicFiles.lvSeat_putFork
#print axioms VerifiableInference.OnPublicFiles.lvSeat_headClaim
#print axioms VerifiableInference.OnPublicFiles.stated_len
#print axioms VerifiableInference.OnPublicFiles.keepsLook_of_eq
#print axioms VerifiableInference.OnPublicFiles.KeepsLook.trans
#print axioms VerifiableInference.OnPublicFiles.lvDigits_put_look
#print axioms VerifiableInference.OnPublicFiles.stated_keeps
#print axioms VerifiableInference.Desc.First.MergeLaw.leaves_keeps
#print axioms VerifiableInference.Desc.First.MergeLaw.leaves_of_len
#print axioms VerifiableInference.Desc.First.MergeLaw.k6_keeps
#print axioms VerifiableInference.Desc.First.MergeLaw.laterAt_keeps
#print axioms VerifiableInference.Desc.First.MergeLaw.k8_keeps
#print axioms VerifiableInference.Desc.First.MergeLaw.keeps_andThen
#print axioms VerifiableInference.Desc.First.MergeLaw.readsBlockAt_keeps
#print axioms VerifiableInference.Desc.First.MergeLaw.readsAtO_keeps
#print axioms VerifiableInference.Desc.First.MergeLaw.readsQuietAt_keeps
#print axioms VerifiableInference.Desc.First.MergeLaw.k1Reads_keeps
#print axioms VerifiableInference.Desc.First.MergeLaw.k1_head_keeps
#print axioms VerifiableInference.Desc.First.MergeLaw.seated_five
#print axioms VerifiableInference.Desc.First.MergeLaw.seated_calls
#print axioms VerifiableInference.Desc.First.MergeLaw.back_keeps
#print axioms VerifiableInference.Desc.First.MergeLaw.leaves_reach
#print axioms VerifiableInference.Desc.First.MergeLaw.leaves_at346
