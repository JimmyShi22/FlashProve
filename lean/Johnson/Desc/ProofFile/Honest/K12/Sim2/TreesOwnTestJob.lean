-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the clause trees at the request's own test, at the job that the filling lays.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/TreesOwnTestJob.lean: trees_at_own_test with its three ties
paid, at a job whose members are made of their senders' jobs.

  fresh_of_ride            a riding message's rows are the table that the test's state packs
  purse_none, look_last_of_first, look_last_of_shared, first_row_of_cut, shared_row_of_cut   the last
                           chain's look-up at a sender's address
  k1CutFits, k1_member_coins   a public test on the book; what it gives
  tie_index_member, tie_riding_member, tie_omega_member   the three ties
  trees_at_job_own_test    the clause
  real_job_form            jobRealW's job has these members and trees

What is left of trees_at_job_own_test. On the book: hbkI, hbkW, hbkF, hbkO, hnotO. On what W's data
hears: hheard. On Omega's sender: hatO, ha', haskO. Public numbers: the rest. On the run: hR, hrun, hc,
S, hmid, hlp.

Limits. A conditional on a run. The clause reads the input and the carried values: no later law may
take it as a hypothesis on a run and then speak of the random values as sampled anew. The book's tests
are evaluated at no book here. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.TreesOwnTestRun
import Johnson.Desc.ProofFile.Honest.K12.CutOfBook
import Johnson.Desc.ProofFile.Honest.K12.AtProof.FirstMemberSent
import Johnson.Desc.ProofFile.Honest.K12.AtProof.WMemberSent
import Johnson.Desc.ProofFile.Honest.K12.AtProof.OmegaMemberSent
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block FileDescription Oracle Place)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light
open Johnson.Prover.Send (col shapeAt)
open Johnson.Prover.Link (packedN)
open OnBytes.Slice (GE)
open H2K.Pub (sgOf)

/-- **A message that a fold's fresh table rides**: its mask rows are the table that the test's state
packs, where the stretch e holds the message's coins. -/
theorem fresh_of_ride (Q : VerifiableInference.Desc.K1.Par) (ride : ℕ → Option K1.Ride)
    (data : ℕ → ℕ → ℕ → Option (OnBytes.Slice.GF ⊕ GE)) (c : Cs (K1.dueR Q ride)) (k : ℕ)
    (s : Fmt.M1.Stage) (hk : ride k = some ⟨s.k, s.h⟩) (hh : s.h ≤ s.k)
    (hroom : 2 * s.k + 1 ≤ s.h + s.Z.l) (hd : ((shapeAt Q k).mainDeg == 3) = false)
    (hn : (shapeAt Q k).maskRows = 2 ^ s.h)
    (hl : (Q.codes.mask.getD (shapeAt Q k).maskCode default).ell = s.Z.l)
    (hr : (Q.codes.mask.getD (shapeAt Q k).maskCode default).r = s.Z.r) (e : ℕ → GE)
    (he : ∀ i, i < 2 * s.k + 1 + 2 ^ s.h * s.Z.r → K1.ce c ((K1.startR Q ride k).e + i) = e i) :
    (∀ r < 2 ^ s.h, ∀ j < s.Z.l, (K1.rowsR Q ride data c k).mask r j =
      packedN (sgOf s) (hideAt ((sgOf s).h + (sgOf s).g) e) r j) ∧
    (∀ r < 2 ^ s.h, ∀ q < s.Z.r, (K1.rowsR Q ride data c k).maskTl r q = tailsIn s e r q) := by
  have hK : (sgOf s).h + (sgOf s).g = s.k := by
    show s.h + (s.k - s.h) = s.k
    omega
  refine ⟨fun r hr' j hj => ?_, fun r hr' q hq => ?_⟩
  · have hb : r < (shapeAt Q k).maskRows ∧ j < (Q.codes.mask.getD (shapeAt Q k).maskCode default).ell :=
      ⟨by rw [hn]; exact hr', by rw [hl]; exact hj⟩
    have e1 : (K1.rowsR Q ride data c k).mask r j =
        (⟨s.k, s.h⟩ : K1.Ride).lay (fun i => if i < (⟨s.k, s.h⟩ : K1.Ride).count then
          K1.ce c ((K1.startR Q ride k).e + i) else 0) r j := by
      simp only [K1.rowsR, hk, hd, if_pos hb]
      simp
    rw [e1, lay_is_packed s hh hroom _ r j hr' hj]
    refine congrArg (fun f => packedN (sgOf s) f r j) (hideAt_congr _ _ _ fun n hn' => ?_)
    have hn2 : n < 2 * s.k + 1 := by rw [hK] at hn'; exact hn'
    have : n < (⟨s.k, s.h⟩ : K1.Ride).count := hn2
    rw [if_pos this]
    exact he n (by omega)
  · have hb : r < (shapeAt Q k).maskRows ∧ q < (Q.codes.mask.getD (shapeAt Q k).maskCode default).r :=
      ⟨by rw [hn]; exact hr', by rw [hr]; exact hq⟩
    have hlt : r * s.Z.r + q < 2 ^ s.h * s.Z.r := by
      have h1 : (r + 1) * s.Z.r ≤ 2 ^ s.h * s.Z.r := Nat.mul_le_mul_right _ hr'
      have h2 : (r + 1) * s.Z.r = r * s.Z.r + s.Z.r := Nat.succ_mul r _
      omega
    have e1 : (K1.rowsR Q ride data c k).maskTl r q =
        K1.ce c ((K1.startR Q ride k).e + (2 * s.k + 1 + r * s.Z.r + q)) := by
      have hb2 : r < (shapeAt Q k).maskRows ∧ q < s.Z.r := ⟨hb.1, hq⟩
      simp only [K1.rowsR, hk, hd, K1.stepsOf, hr, if_pos hb2, Bool.false_eq_true, if_false,
        Option.map_some, Option.getD_some, K1.Ride.count, Nat.add_zero]
      congr 1
      omega
    rw [e1]
    exact he _ (by omega)

/-! ## What the last chain's look-up holds -/

/-- An address without a row has no coins. -/
theorem purse_none : ∀ (l : List (Addr × Due)) (c : Purse l) (a : Addr), (∀ r ∈ l, r.1 ≠ a) →
    Purse.find? l c a = none
  | [], _, _, _ => rfl
  | r :: l, c, a, h => by
    have h1 : (r.1 == a) = false := by
      simpa using h r List.mem_cons_self
    show (if r.1 == a then some ⟨r.2, c.1⟩ else Purse.find? l c.2 a) = none
    rw [h1]
    exact purse_none l c.2 a fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem look_last_of_first {B : ProverCoinCounts} (k : Coins B) (a : Addr)
    (h : (Purse.find? B.first k.first a).isSome = true) : k.look 2 a = k.look 0 a := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
  unfold Coins.look
  simp [hv]

theorem look_last_of_shared {B : ProverCoinCounts} (k : Coins B) (a : Addr)
    (h0 : Purse.find? B.first k.first a = none)
    (h : (Purse.find? B.shared k.shared a).isSome = true) :
    k.look 2 a = sharedLook B k.shared a := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
  unfold Coins.look sharedLook
  simp [hv, h0]

/-- Where a part takes coins, its address has a row. -/
theorem first_row_of_cut {B : ProverCoinCounts} (k : Coins B) (a : Addr) {t : Due} {c : Cs t}
    (hown : (k.look 0 a).2.cut ⟨0, 0⟩ t = some c) (hpos : 0 < t.f + t.e) :
    (Purse.find? B.first k.first a).isSome = true := by
  cases hf : Purse.find? B.first k.first a with
  | some v => rfl
  | none =>
    have e : k.look 0 a = ⟨⟨0, 0⟩, Cs.empty⟩ := by
      unfold Coins.look
      simp [hf]
    rw [e] at hown
    unfold Cs.cut at hown
    split at hown
    · rename_i h
      have h1 : 0 + t.f ≤ 0 := h.1
      have h2 : 0 + t.e ≤ 0 := h.2
      omega
    · cases hown

theorem shared_row_of_cut {B : ProverCoinCounts} (k : Coins B) (a : Addr) {t : Due} {c : Cs t}
    (hown : (sharedLook B k.shared a).2.cut ⟨0, 0⟩ t = some c) (hpos : 0 < t.f + t.e) :
    (Purse.find? B.shared k.shared a).isSome = true := by
  cases hf : Purse.find? B.shared k.shared a with
  | some v => rfl
  | none =>
    have e : sharedLook B k.shared a = ⟨⟨0, 0⟩, Cs.empty⟩ := by
      unfold sharedLook
      simp [hf]
    rw [e] at hown
    unfold Cs.cut at hown
    split at hown
    · rename_i h
      have h1 : 0 + t.f ≤ 0 := h.1
      have h2 : 0 + t.e ≤ 0 := h.2
      omega
    · cases hown

/-- **A public test on the book**: entry number n that a carries is message kk's coins of the sending
at s. -/
def k1CutFits (Bk : ProverCoinCounts) (a : Addr) (n : ℕ) (s : Addr) (Q : VerifiableInference.Desc.K1.Par)
    (ride : ℕ → Option K1.Ride) (kk : ℕ) : Bool :=
  match (Light.carriedOf Bk a)[n]? with
  | some e => e.owner == s && e.start == K1.startR Q ride kk &&
      e.count == K1.dueMsg Q.codes (shapeAt Q kk) (ride kk) &&
      decide (e.start.f + e.count.f ≤ (K1.dueR Q ride).f) &&
      decide (e.start.e + e.count.e ≤ (K1.dueR Q ride).e)
  | none => false

/-- **What the book lends a part of the last chain is the sender's own coins**, message by message. -/
theorem k1_member_coins {Bk : ProverCoinCounts} (k : Coins Bk) (a s : Addr)
    (Q : VerifiableInference.Desc.K1.Par) (ride : ℕ → Option K1.Ride) (own : Cs (K1.dueR Q ride))
    (hown : (k.look 0 s).2.cut ⟨0, 0⟩ (K1.dueR Q ride) = some own)
    (hpos : 0 < (K1.dueR Q ride).f + (K1.dueR Q ride).e)
    (ds : List (String × Due)) (ca : CsAll ds) (hl : lend (k.look 2) ds (Light.carriedOf Bk a) = .ok ca)
    (n kk : ℕ) (hf : k1CutFits Bk a n s Q ride kk = true) :
    (∀ i, i < (K1.dueMsg Q.codes (shapeAt Q kk) (ride kk)).f →
      K1.cf own ((K1.startR Q ride kk).f + i) = (stretches ds ca n).f i) ∧
    (∀ i, i < (K1.dueMsg Q.codes (shapeAt Q kk) (ride kk)).e →
      K1.ce own ((K1.startR Q ride kk).e + i) = (stretches ds ca n).e i) := by
  unfold k1CutFits at hf
  split at hf
  · rename_i e he
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
    obtain ⟨⟨⟨⟨ho, hs⟩, hc⟩, b1⟩, b2⟩ := hf
    obtain ⟨x, hx, hst⟩ := lend_cut (k.look 2) ds _ ca hl n e he
    rw [hst]
    have hrow := first_row_of_cut k s hown hpos
    rw [ho, look_last_of_first k s hrow] at hx
    obtain ⟨en, eo, es, ec, ep, eb⟩ := e
    dsimp only at ho hs hc b1 b2 hx
    subst hs hc
    exact lent_agrees _ own x hown hx b1 b2
  · cases hf

/-! ## The three ties at a run -/

section Ties
open ProofFile.Honest.K14 (SendJob jobOmega Ask sendingsFit)

variable {Xi W₀ Rc Ky Tr X₀ Y W X : Type}

/-- **The index-mask member is its sender's**, at the coins that the book lends. JI: the member's
sending, JS: the sender's, of one place and one ride. -/
theorem tie_index_member {Rd : Type} {Bk : ProverCoinCounts} (k : Coins Bk) (a : Addr)
    (JI : K1.SendJob Rd X) (JS : K1.SendJob (K1.PlaceIn Xi) Y) (hP : JI.P = JS.P)
    (hride : JI.ride = JS.ride) (readers : W → Rd) (at_ : Addr) (fs : Option ℕ × Option ℕ)
    (wit : Local W₀ Rc Xi Tr → K1.PlaceIn Xi) (b : Place)
    (w : W) (fr : Front X) (kI : ℕ) (hk : kI < JS.P.sent.size)
    (hm : (shapeAt JS.P kI).mainRows = 0)
    (hpos : 0 < (K1.dueR JS.P JS.ride).f + (K1.dueR JS.P JS.ride).e)
    (ds : List (String × Due)) (ca : CsAll ds) (hcar : lend (k.look 2) ds (Light.carriedOf Bk a) = .ok ca)
    (hf : k1CutFits Bk a 0 ⟨b, 0⟩ JS.P JS.ride kI = true)
    (mᵢ : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y)
    (c : ((K1.sendPart (V := Local W₀ Rc Xi Tr) JS).lift id wit id fun _ y => y :
      Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).Coins)
    (hl : lendPart Bk (Bk.rowsOf 0) (k.look 0) ⟨b, 0⟩
      ((K1.sendPart (V := Local W₀ Rc Xi Tr) JS).lift id wit id fun _ y => y) = .ok c) :
    (memK1 JI readers at_ kI fs).rows w fr (stretches ds ca 0) =
      psOfRows JS.P kI (JS.rows c.1 mᵢ.shown (mᵢ.st.narrow wit id) 0 kI) := by
  obtain ⟨P₁, f₁, r₁, d₁⟩ := JI
  obtain ⟨P₂, f₂, r₂, d₂⟩ := JS
  dsimp only at hP hride hk hm hpos hf
  subst hP hride
  have hown := own_of_lendPart hl
  obtain ⟨f, e⟩ := k1_member_coins k a ⟨b, 0⟩ P₁ r₁ c.1 hown hpos ds ca hcar 0 kI hf
  show psOfRows P₁ kI (K1.rowsR P₁ r₁ (d₁ (readers w) fr) (csAt _ (K1.startR P₁ r₁ kI) _) kI) =
    psOfRows P₁ kI (K1.rowsR P₁ r₁ _ c.1 kI)
  rw [rowsR_no_main P₁ r₁ (d₁ (readers w) fr) _ _ kI hm, rowsR_csAt P₁ r₁ _ kI hk _ c.1 f e]

/-- **W's member is its sender's**, and the fresh message's rows are the table that the test's state
packs. N: the challenges in front of the sender. hheard: what W's data hears lies in front of it. -/
theorem tie_riding_member {Bk : ProverCoinCounts} (k : Coins Bk) (a : Addr)
    (PW : VerifiableInference.Desc.K1.Par) (fW : ℕ) (foldW : Option (ℕ × OnBytes.FoldShape))
    (DW : RowDataOf Xi) (pW : ℕ) (wit : Local W₀ Rc Xi Tr → K1.PlaceIn Xi) (b : Place) (at_ : Addr)
    (fs : Option ℕ × Option ℕ) (w : Local W₀ Rc Xi Tr) (fr : Front Y)
    (N : ℕ) (ρ₁ : List Fmt.Drawn) (hfr : fr.heard.take N = ρ₁.take N)
    (hheard : ∀ a', (DW (wit w).x).heardAt a' ≤ N)
    (h0 : 0 < PW.sent.size)
    (hpos : 0 < (K1.dueR PW (K1.rideOf foldW)).f + (K1.dueR PW (K1.rideOf foldW)).e)
    (ds : List (String × Due)) (ca : CsAll ds) (hcar : lend (k.look 2) ds (Light.carriedOf Bk a) = .ok ca)
    (nW nF : ℕ) (hf0 : k1CutFits Bk a nW ⟨b, 0⟩ PW (K1.rideOf foldW) 0 = true)
    (hf1 : k1CutFits Bk a nF ⟨b, 0⟩ PW (K1.rideOf foldW) 1 = true)
    (s : Fmt.M1.Stage) (hride : K1.rideOf foldW 1 = some ⟨s.k, s.h⟩) (hh : s.h ≤ s.k)
    (hroom : 2 * s.k + 1 ≤ s.h + s.Z.l) (hd : ((shapeAt PW 1).mainDeg == 3) = false)
    (hn : (shapeAt PW 1).maskRows = 2 ^ s.h)
    (hl : (PW.codes.mask.getD (shapeAt PW 1).maskCode default).ell = s.Z.l)
    (hr : (PW.codes.mask.getD (shapeAt PW 1).maskCode default).r = s.Z.r)
    (hdue : 2 * s.k + 1 + 2 ^ s.h * s.Z.r ≤ (K1.dueMsg PW.codes (shapeAt PW 1) (K1.rideOf foldW 1)).e)
    (mᵢ : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y)
    (c : ((K1.sendPart (V := Local W₀ Rc Xi Tr) (K1.placeJob (X := Y) PW fW foldW DW pW)).lift id wit id
        fun _ y => y : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y).Coins)
    (hlend : lendPart Bk (Bk.rowsOf 0) (k.look 0) ⟨b, 0⟩
      ((K1.sendPart (V := Local W₀ Rc Xi Tr) (K1.placeJob (X := Y) PW fW foldW DW pW)).lift id wit id
        fun _ y => y) = .ok c)
    (hin : mᵢ.st.input = w) (hh₂ : mᵢ.st.heard = ρ₁.take N) :
    (memK1 (K1.placeJob (X := Y) PW fW foldW DW pW) wit at_ 0 fs).rows w fr (stretches ds ca nW) =
        psOfRows PW 0 ((K1.placeJob (X := Y) PW fW foldW DW pW).rows c.1 mᵢ.shown
          (mᵢ.st.narrow wit id) 0 0) ∧
      (∀ r < 2 ^ s.h, ∀ j < s.Z.l, ((K1.placeJob (X := Y) PW fW foldW DW pW).rows c.1 mᵢ.shown
          (mᵢ.st.narrow wit id) 0 1).mask r j =
        packedN (sgOf s) (hideAt ((sgOf s).h + (sgOf s).g) (stretches ds ca nF).e) r j) ∧
      ∀ r < 2 ^ s.h, ∀ q < s.Z.r, ((K1.placeJob (X := Y) PW fW foldW DW pW).rows c.1 mᵢ.shown
          (mᵢ.st.narrow wit id) 0 1).maskTl r q = tailsIn s (stretches ds ca nF).e r q := by
  have hown := own_of_lendPart hlend
  obtain ⟨f0, e0⟩ := k1_member_coins k a ⟨b, 0⟩ PW (K1.rideOf foldW) c.1 hown hpos ds ca hcar nW 0 hf0
  obtain ⟨-, e1⟩ := k1_member_coins k a ⟨b, 0⟩ PW (K1.rideOf foldW) c.1 hown hpos ds ca hcar nF 1 hf1
  subst hin
  obtain ⟨g1, g2⟩ := fresh_of_ride PW (K1.rideOf foldW)
    ((K1.placeJob (X := Y) PW fW foldW DW pW).data (wit mᵢ.st.input)
      { heard := mᵢ.st.heard.take (mᵢ.st.heard.length - 0), own := mᵢ.st.own,
        seen := mᵢ.shown.front 0 }) c.1 1 s hride hh hroom hd hn hl hr (stretches ds ca nF).e
    fun i hi => e1 i (by omega)
  refine ⟨?_, g1, g2⟩
  refine wMember_mem_rows PW fW foldW DW pW wit at_ fs mᵢ.st.input fr _ (fun a' => ?_) 0 h0 _ c.1
    f0 e0
  have hb := hheard a'
  show fr.heard.take _ = (mᵢ.st.heard.take (mᵢ.st.heard.length - 0)).take _
  rw [Nat.sub_zero, List.take_length, hh₂]
  have e := congrArg (List.take ((DW (wit mᵢ.st.input).x).heardAt a')) hfr
  rw [List.take_take, List.take_take, Nat.min_eq_left hb] at e
  rw [List.take_take, Nat.min_eq_left hb]
  exact e

/-- **Omega's member is its sender's**: one vector, one cut. -/
theorem tie_omega_member {Bk : ProverCoinCounts} (k : Coins Bk) (a : Addr) (Pq : Desc.K14.P14) (ao : ℕ)
    (witO : Common W₀ Rc Ky → Ask) (b : Place)
    (hnot : ∀ r ∈ Bk.first, r.1 ≠ ⟨b, 0⟩)
    (hpos : 0 < (ProofFile.Honest.K14.takesOf (jobOmega ⟨Pq, ao⟩).Q.codes (jobOmega ⟨Pq, ao⟩).Q.sent
        (jobOmega ⟨Pq, ao⟩).sort).f +
      (ProofFile.Honest.K14.takesOf (jobOmega ⟨Pq, ao⟩).Q.codes (jobOmega ⟨Pq, ao⟩).Q.sent
        (jobOmega ⟨Pq, ao⟩).sort).e)
    {V W X : Type} (p : Part V W X) (cc : p.Coins)
    (hl : lendPart Bk (Bk.rowsOf 2) (k.look 2) a p = .ok cc)
    (nO : ℕ) (hf : Light.cutFits Bk a nO ⟨b, 0⟩ (jobOmega ⟨Pq, ao⟩) 0 = true)
    (askv : Ask) (h₁ h₂ e₂ : List Fmt.Drawn) (hat : ao < h₂.length)
    (mᵢ : ProofFile.Honest.Mid (Common W₀ Rc Ky) X₀)
    (c : (ProofFile.Honest.K14.liftSend witO (ProofFile.Honest.K14.sendingPart (jobOmega ⟨Pq, ao⟩)) :
      Part Empty (Common W₀ Rc Ky) X₀).Coins)
    (hlend : lendPart Bk (Bk.rowsOf 1) (sharedLook Bk k.shared) ⟨b, 0⟩
      (ProofFile.Honest.K14.liftSend witO (ProofFile.Honest.K14.sendingPart (jobOmega ⟨Pq, ao⟩))) = .ok c)
    (hask : witO mᵢ.st.input = askv) (hheard : mᵢ.st.heard = h₂) :
    (jobOmega ⟨Pq, h₁.length + ao⟩).data ⟨askv, h₁ ++ (h₂ ++ e₂), ()⟩ 0 =
        (jobOmega ⟨Pq, ao⟩).data (mᵢ.st.narrow witO fun _ => ()) 0 ∧
      SameCut (jobOmega ⟨Pq, ao⟩) 0 (coinsE c.1).toArray (stretches p.carries cc.2.2 nO) := by
  refine ⟨?_, ?_⟩
  · have e := omega_data_at_sender Pq ao askv h₁ h₂ e₂ 0 hat
    rw [e]
    show _ = (jobOmega ⟨Pq, ao⟩).data ⟨witO mᵢ.st.input, mᵢ.st.heard, ()⟩ 0
    rw [hask, hheard]
  · have hown := own_of_lendPart hlend
    have hrow := shared_row_of_cut k ⟨b, 0⟩ hown hpos
    have hlast := look_last_of_shared k ⟨b, 0⟩ (purse_none _ _ _ hnot) hrow
    have hown' : (k.look 2 ⟨b, 0⟩).2.cut ⟨0, 0⟩ (ProofFile.Honest.K14.takesOf (jobOmega ⟨Pq, ao⟩).Q.codes
        (jobOmega ⟨Pq, ao⟩).Q.sent (jobOmega ⟨Pq, ao⟩).sort) = some c.1 := by
      rw [hlast]
      exact hown
    exact sameCut_of_book Bk _ _ a p cc hl ⟨b, 0⟩ (jobOmega ⟨Pq, ao⟩) c.1 hown' nO 0 hf

end Ties

/-! ## The clause at the job -/

section AtJob
open OnBytes.Slice (codeOf)
open Johnson.Prover.Send (mainSyms maskSyms Rows)
open ProofFile.Honest.K14 (SendJob jobOmega Ask columnOf sendingsFit)

variable {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type}

/-- **The clause trees at the request's own test, at a run, at a job whose members are made of their
senders' jobs**: trees_at_own_test with the three ties paid. -/
theorem trees_at_job_own_test {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₃ F.Cl V (Local W₀ Rc Xi Tr) Y Pb) (u : Member V (Local W₀ Rc Xi Tr) Y Pb)
    (pre' t' : List (Block F.S₃ F.Cl)) (i : ℕ) (S : StandsAt F.second.blocksInOrder R.second σ u pre' t' i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (st : List (ℕ × ℕ × List UInt64))
    -- the job
    (B : ManyJob (Local W₀ Rc Xi Tr) Y) (hk : B.s₀.h ≤ B.s₀.k) (Pq : Desc.K14.P14)
    (hQ : sendingsFit Pq = true) (a a' : ℕ) (m₀ m₁ : Mem (Local W₀ Rc Xi Tr) Y) (at_ : Addr)
    (fs : Option ℕ × Option ℕ) (ask : Local W₀ Rc Xi Tr → Ask)
    (hm : B.mems = [m₀, m₁, memOfSending (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none])
    (d₀ d₁ d₂ : ℕ)
    (ht : B.trees = [(d₀, [.mask 0]), (d₁, [.main 1, .mask 1, .fresh]), (d₂, [.main 2])])
    (os : List (Fmt.Shape × Fmt.TreeSource)) (hd : [d₀, d₁, d₂] = os.map (·.1.a))
    (j₀ j₁ j₂ : ℕ) (hsrc : os.map (fun o => ProofFile.Honest.srcOf 2 o.2) = [(0, j₀), (0, j₁), (1, j₂)])
    -- the state and the members' stretches
    (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Tr) Y)
    (hmid : midAtW F Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m))
    (hi : i = firstLen B.toRun.toTest.p.nums.stages)
    (Vc Wc Xc : Type) (pc : Part Vc Wc Xc) (cc : pc.Coins)
    (hlp : lendPart Bk (Bk.rowsOf 2) (k.look 2) ⟨σ.block.place, u.number⟩ pc = .ok cc)
    -- the first chain's two senders
    (preI preW : List (Block F.S₁ F.Cl)) (bI bW : Block F.S₁ F.Cl) (tI tW : List (Block F.S₁ F.Cl))
    (hcutI : F.first.blocksInOrder = preI ++ bI :: tI) (hcutW : F.first.blocksInOrder = preW ++ bW :: tW)
    (hbI : bI.rounds ≠ []) (hbW : bW.rounds ≠ [])
    (wit : Local W₀ Rc Xi Tr → K1.PlaceIn Xi) (JI JW : K1.SendJob (K1.PlaceIn Xi) Y)
    (hgI : (P.first.find? fun g => g.place == bI.place) =
      some (K1.placeHalf (V := Local W₀ Rc Xi Tr) wit JI))
    (hgW : (P.first.find? fun g => g.place == bW.place) =
      some (K1.placeHalf (V := Local W₀ Rc Xi Tr) wit JW))
    (τI τW kI : ℕ) (shI shW : OnBytes.TreeShape) (hτI : JI.P.trees[τI]? = some shI)
    (hτW : JW.P.trees[τW]? = some shW)
    (hWI : columnWidth JI.P τI = shI.mainWidth + shI.maskWidth)
    (hWW : columnWidth JW.P τW = shW.mainWidth + shW.maskWidth)
    (hjI : treesTo F.first.blocksInOrder preI.length + τI = j₀)
    (hjW : treesTo F.first.blocksInOrder preW.length + τW = j₁)
    -- what the two members are
    (Rd : Type) (JIm : K1.SendJob Rd Y) (readers : Local W₀ Rc Xi Tr → Rd) (at₀ at₁ : Addr)
    (fs₀ fs₁ : Option ℕ × Option ℕ) (hm₀ : m₀ = memK1 JIm readers at₀ kI fs₀)
    (hPI : JIm.P = JI.P) (hrI : JIm.ride = JI.ride) (hkI : kI < JI.P.sent.size)
    (hposI : 0 < (K1.dueR JI.P JI.ride).f + (K1.dueR JI.P JI.ride).e)
    (hbkI : k1CutFits Bk ⟨σ.block.place, u.number⟩ 0 ⟨bI.place, 0⟩ JI.P JI.ride kI = true)
    (PW : VerifiableInference.Desc.K1.Par) (fW : ℕ) (foldW : Option (ℕ × OnBytes.FoldShape))
    (DW : RowDataOf Xi) (pW : ℕ) (hJW : JW = K1.placeJob PW fW foldW DW pW)
    (hm₁ : m₁ = memK1 (K1.placeJob (X := Y) PW fW foldW DW pW) wit at₁ 0 fs₁)
    (hheard : ∀ a', (DW (wit m.st.input).x).heardAt a' ≤ (preW.flatMap (·.rounds)).length)
    (h0W : 0 < PW.sent.size)
    (hposW : 0 < (K1.dueR PW (K1.rideOf foldW)).f + (K1.dueR PW (K1.rideOf foldW)).e)
    (hbkW : k1CutFits Bk ⟨σ.block.place, u.number⟩ 1 ⟨bW.place, 0⟩ PW (K1.rideOf foldW) 0 = true)
    (hbkF : k1CutFits Bk ⟨σ.block.place, u.number⟩ 3 ⟨bW.place, 0⟩ PW (K1.rideOf foldW) 1 = true)
    (hride : K1.rideOf foldW 1 = some ⟨B.s₀.k, B.s₀.h⟩)
    (hroom : 2 * B.s₀.k + 1 ≤ B.s₀.h + B.s₀.Z.l) (hdF : ((shapeAt PW 1).mainDeg == 3) = false)
    (hdue : 2 * B.s₀.k + 1 + 2 ^ B.s₀.h * B.s₀.Z.r ≤
      (K1.dueMsg PW.codes (shapeAt PW 1) (K1.rideOf foldW 1)).e)
    -- public, at the two senders
    (hinZ₀ : m₀.shape.maskFirst + m₀.shape.maskRows ≤ 2 ^ B.s₀.h)
    (hnI : m₀.shape.maskRows = (Johnson.Prover.Send.shapeAt JI.P kI).maskRows)
    (hzI : codeOf (JI.P.codes.mask.getD (Johnson.Prover.Send.shapeAt JI.P kI).maskCode default) =
      B.s₀.Z)
    (hmineI : (List.range JI.P.sent.size).filter (fun k =>
      ((VerifiableInference.Desc.Own.treesMade JI.P.codes JI.P.sent).getD {}).tree[k]? == some τI) =
        [kI])
    (hmainI : (Johnson.Prover.Send.shapeAt JI.P kI).mainRows = 0)
    (hbase₁ : m₁.shape.base = false)
    (hoffM : ∀ b, m₁.shape.mainFirst ≤ b → b < m₁.shape.mainFirst + m₁.shape.mainRows →
      ¬ (m₀.shape.mainFirst ≤ b ∧ b < m₀.shape.mainFirst + m₀.shape.mainRows))
    (hoffZ : ∀ b, m₁.shape.maskFirst ≤ b → b < m₁.shape.maskFirst + m₁.shape.maskRows →
      ¬ (m₀.shape.maskFirst ≤ b ∧ b < m₀.shape.maskFirst + m₀.shape.maskRows))
    (hinM : m₁.shape.mainFirst + m₁.shape.mainRows ≤ 2 ^ B.s₀.k)
    (hinZ : m₁.shape.maskFirst + m₁.shape.maskRows ≤ 2 ^ B.s₀.h)
    (hnM : m₁.shape.mainRows = (Johnson.Prover.Send.shapeAt JW.P 0).mainRows)
    (hnZ : m₁.shape.maskRows = (Johnson.Prover.Send.shapeAt JW.P 0).maskRows)
    (hdW : (Johnson.Prover.Send.shapeAt JW.P 0).mainDeg = 3)
    (hzC : codeOf (JW.P.codes.base.getD (Johnson.Prover.Send.shapeAt JW.P 0).code default) = B.s₀.C)
    (hzZ : codeOf (JW.P.codes.mask.getD (Johnson.Prover.Send.shapeAt JW.P 0).maskCode default) =
      B.s₀.Z)
    (hzF : codeOf (JW.P.codes.mask.getD (Johnson.Prover.Send.shapeAt JW.P 1).maskCode default) =
      B.s₀.Z)
    (hnF : (Johnson.Prover.Send.shapeAt JW.P 1).maskRows = 2 ^ B.s₀.h)
    (hmF : (Johnson.Prover.Send.shapeAt JW.P 1).mainRows = 0)
    (hmineW : (List.range JW.P.sent.size).filter (fun k =>
      ((VerifiableInference.Desc.Own.treesMade JW.P.codes JW.P.sent).getD {}).tree[k]? == some τW) =
        [0, 1])
    -- the shared chain's sender
    (preO : List (Block F.S₂ F.Cl)) (bO : Block F.S₂ F.Cl) (tO : List (Block F.S₂ F.Cl))
    (hcutO : F.shared.blocksInOrder = preO ++ bO :: tO) (hbO : bO.rounds ≠ [])
    (witO : Common W₀ Rc Ky → Ask)
    (hgO : (P.shared.find? fun g => g.place == bO.place) =
      some ⟨bO.place, [(ProofFile.Honest.K14.liftSend witO (ProofFile.Honest.K14.sendingPart (jobOmega ⟨Pq, a⟩)) :
        Part Empty (Common W₀ Rc Ky) X₀)]⟩)
    (hwO : widthFits (jobOmega ⟨Pq, a⟩) 0 = true)
    (hjO : Johnson.G.OfPlan.rootsOf (preO.flatMap (·.rounds)) + 0 = j₂)
    (hnotO : ∀ r ∈ Bk.first, r.1 ≠ ⟨bO.place, 0⟩)
    (hposO : 0 < (ProofFile.Honest.K14.takesOf (jobOmega ⟨Pq, a⟩).Q.codes (jobOmega ⟨Pq, a⟩).Q.sent
        (jobOmega ⟨Pq, a⟩).sort).f +
      (ProofFile.Honest.K14.takesOf (jobOmega ⟨Pq, a⟩).Q.codes (jobOmega ⟨Pq, a⟩).Q.sent
        (jobOmega ⟨Pq, a⟩).sort).e)
    (hbkO : Light.cutFits Bk ⟨σ.block.place, u.number⟩ 2 ⟨bO.place, 0⟩ (jobOmega ⟨Pq, a⟩) 0 = true)
    (hatO : a < (preO.flatMap (·.rounds)).length)
    (ha' : a' = ρ.first.length + a)
    (haskO : witO R.common = ask m.st.input)
    (hbaseO : (memOfSending (X := Y) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.base = false)
    (hoffO : ∀ y ∈ [m₀, m₁], ∀ b,
      (memOfSending (X := Y) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainFirst ≤ b →
      b < (memOfSending (X := Y) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainFirst +
        (memOfSending (X := Y) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainRows →
      ¬ (y.shape.mainFirst ≤ b ∧ b < y.shape.mainFirst + y.shape.mainRows))
    (hinO : (memOfSending (X := Y) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainFirst +
      (memOfSending (X := Y) (jobOmega ⟨Pq, a'⟩) at_ 0 fs ask none).shape.mainRows ≤ 2 ^ B.s₀.k)
    (hcO : sameCode ((jobOmega ⟨Pq, a⟩).Q.codes.base.getD
      (Light.shapeAt (jobOmega ⟨Pq, a⟩) 0).code default) B.s₀.C = true)
    (hmineO : mineOf (jobOmega ⟨Pq, a⟩) 0 = [0])
    (hmaskO : (Light.shapeAt (jobOmega ⟨Pq, a⟩) 0).maskRows = 0) :
    TreesAt B.toRun.toTest 2 os (stretches pc.carries cc.2.2) m
      (r.run.beforeAt st ⟨σ.block.place, u.number⟩) := by
  subst hJW hm₀ hm₁ ha'
  have Q := (F.planOk_ok).1 hpl
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have o₁ := steps_shaped s1 Q.blocks₁
  have o₂ := steps_shaped s2 Q.blocks₂
  have o₃ := steps_shaped s3 Q.blocks₃
  obtain ⟨lS₁, lS₂, lS₃⟩ := runC_laidAs hrun hR o₁ o₂ o₃
  obtain ⟨m', hm', hin', hheard', -⟩ := frame_at_second hpl hR hrun σ u pre' t' i _ S rfl hc st
  obtain rfl : m = m' := Option.some.inj (Except.ok.inj (hmid.symm.trans hm'))
  have hcar := carried_of_lendPart Bk _ _ _ pc cc hlp
  -- what the part's front has heard
  obtain ⟨e', hrest⟩ : ∃ e', (restFront B.toRun.toTest m).heard = ρ.first ++ (ρ.shared ++ e') := by
    have hT : i ≤ (ρ.second.take ((pre'.flatMap (·.rounds)).length + i)).length := by
      have := S.fits
      have := lS₃.1
      rw [List.length_take]
      omega
    refine ⟨(ρ.second.take ((pre'.flatMap (·.rounds)).length + i)).take
      ((ρ.second.take ((pre'.flatMap (·.rounds)).length + i)).length - i), ?_⟩
    show m.st.heard.take (m.st.heard.length - firstLen B.toRun.toTest.p.nums.stages) = _
    rw [← hi, hheard', List.append_assoc, List.length_append, List.length_append,
      show ρ.first.length + (ρ.shared.length + (ρ.second.take ((pre'.flatMap (·.rounds)).length +
        i)).length) - i = ρ.first.length + (ρ.shared.length + ((ρ.second.take
        ((pre'.flatMap (·.rounds)).length + i)).length - i)) by omega,
      List.take_length_add_append, List.take_length_add_append]
  have hN : (preW.flatMap (·.rounds)).length ≤ ρ.first.length := by
    rw [lS₁.1, chainSteps_length _ _ s1, ← List.length_flatMap, hcutW, List.flatMap_append,
      List.length_append]
    exact Nat.le_add_right _ _
  have hfr : (restFront B.toRun.toTest m).heard.take (preW.flatMap (·.rounds)).length =
      ρ.first.take (preW.flatMap (·.rounds)).length := by
    rw [hrest, List.take_append_of_le_length hN]
  have hlen3 : B.toRun.toTest.members.length = 3 := by
    show (B.mems.map (·.sent)).length = 3
    rw [hm]
    rfl
  refine trees_at_own_test hpl hR hrun σ u pre' t' i S hc st B hk Pq hQ a _ _ _ at_ fs ask hm d₀ d₁ d₂
    ht os hd j₀ j₁ j₂ hsrc m (stretches pc.carries cc.2.2) preI preW bI bW tI tW hcutI hcutW hbI hbW
    wit JI _ hgI hgW τI τW kI shI shW hτI hτW hWI hWW hjI hjW
    (fun mᵢ c hl _ _ => tie_index_member k _ JIm JI hPI hrI readers at₀ fs₀ wit bI.place m.st.input
      (restFront B.toRun.toTest m) kI hkI hmainI hposI _ _ hcar hbkI mᵢ c hl)
    (fun mᵢ c hl hin hh => ?_) hinZ₀ hnI hzI hmineI hmainI hbase₁ hoffM hoffZ hinM hinZ hnM hnZ hdW
    hzC hzZ hzF hnF hmF hmineW preO bO tO hcutO hbO witO hgO hwO hjO
    (fun mᵢ c hl hin hh => ?_) hbaseO hoffO hinO hcO hmineO hmaskO
  · have hh₀ := hin.trans hin'.symm
    obtain ⟨r1, r2, r3⟩ := tie_riding_member k _ PW fW foldW DW pW wit bW.place at₁ fs₁ m.st.input
      (restFront B.toRun.toTest m) _ ρ.first hfr hheard h0W hposW _ _ hcar 1 3 hbkW hbkF B.s₀ hride hk
      hroom hdF hnF (congrArg Fmt.M1.Code.l hzF) (congrArg Fmt.M1.Code.r hzF) hdue mᵢ c hl hh₀ hh
    refine ⟨r1, fun r hr j hj => ?_, fun r hr q hq => ?_⟩
    · refine (r2 r hr j hj).trans ?_
      show _ = packedN (sgOf B.s₀) (hideAt ((sgOf B.s₀).h + (sgOf B.s₀).g)
        (stretches pc.carries cc.2.2 B.toRun.toTest.members.length).e) r j
      rw [hlen3]
    · refine (r3 r hr q hq).trans ?_
      show _ = tailsIn B.s₀ (stretches pc.carries cc.2.2 B.toRun.toTest.members.length).e r q
      rw [hlen3]
  · have e := tie_omega_member (X₀ := X₀) k _ Pq a witO bO.place hnotO hposO pc cc hlp 2 hbkO (ask m.st.input)
      ρ.first (ρ.shared.take (preO.flatMap (·.rounds)).length)
      (ρ.shared.drop (preO.flatMap (·.rounds)).length ++ e') (by
        have hlen : (preO.flatMap (·.rounds)).length ≤ ρ.shared.length := by
          rw [lS₂.1, chainSteps_length _ _ s2, ← List.length_flatMap, hcutO, List.flatMap_append,
            List.length_append]
          exact Nat.le_add_right _ _
        rw [List.length_take]
        omega) mᵢ c hl (by rw [hin]; exact haskO) hh
    have e3 : ρ.shared ++ e' = ρ.shared.take (preO.flatMap (·.rounds)).length ++
        (ρ.shared.drop (preO.flatMap (·.rounds)).length ++ e') := by
      rw [← List.append_assoc, List.take_append_drop]
    rw [hrest, e3]
    exact e

end AtJob

/-! ## The job that the filling lays has this form -/

section Real
variable {W₀ Rc Xi Tr Y : Type}

/-- **What the filling's job is**: trees_at_job_own_test's premises hm, ht, hm₀, hm₁, hJW read off
jobRealW. -/
theorem real_job_form (S : OnBytes.HonestTrace.Sz) (Fd : FileDescription Xi)
    (enter : Fd.S₃ → Except String VerifiableInference.Desc.K12.T12)
    (pile : ProofFile.Pub → ProofFile.Ground → K13.PileOf Xi) (no : Place → ℕ)
    (readers : Local W₀ Rc Xi Tr → Readers) (weights : Local W₀ Rc Xi Tr → Weights)
    (rand : Desc.K14.P14 → Local W₀ Rc Xi Tr → TableRand) (Z : ProofFile.Pub) (G : ProofFile.Ground)
    {M : ManyJob (Local W₀ Rc Xi Tr) Y}
    (hM : jobRealW S Fd enter pile no readers weights rand Z G = some M) :
    ∃ (Fo : Four) (A : ProofFile.Honest.K14.SendPub) (msg : Array OnBytes.OracleNotice)
      (fs₀ fs₁ fs₂ : Option ℕ × Option ℕ),
      four Z = some Fo ∧ sendPub Z = some A ∧ OnBytes.linMessageW Z.first.lin = some msg ∧
      M.p = Fo.W ∧ M.trees = treesW Fo.W ∧
      M.mems = [memK1 (K1.firstJob S Z G) readers senderI
          ((K1.firstJob (X := Y) S Z G).P.sent.size - 1) fs₀,
        memK1 (K1.wJobAt Z.first (K1.wGp Z) 4 msg (no ⟨1, none, 4, .K1⟩) (K13.wDataAt pile Z G))
          (inOf readers) senderW 0 fs₁,
        memOfSending (ProofFile.Honest.K14.jobOmega
          ⟨A.P, (Fd.first.blocksInOrder.flatMap (·.rounds)).length + A.atPoint⟩) senderO 0 fs₂
          (askOf A weights (rand A.P)) none] := by
  unfold jobRealW at hM
  obtain ⟨Fo, hF, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨A, hA, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨msg, hmsg, rfl⟩ := Option.map_eq_some_iff.1 hM
  exact ⟨Fo, A, msg, _, _, _, hF, hA, hmsg, rfl, rfl, rfl⟩

end Real

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.fresh_of_ride
#print axioms ProofFile.Honest.K12.Sim2.real_job_form
#print axioms ProofFile.Honest.K12.Sim2.trees_at_job_own_test
#print axioms ProofFile.Honest.K12.Sim2.tie_index_member
#print axioms ProofFile.Honest.K12.Sim2.tie_riding_member
#print axioms ProofFile.Honest.K12.Sim2.tie_omega_member
#print axioms ProofFile.Honest.K12.Sim2.k1_member_coins
#print axioms ProofFile.Honest.K12.Sim2.look_last_of_shared
#print axioms ProofFile.Honest.K12.Sim2.shared_row_of_cut
#print axioms ProofFile.Honest.K12.Sim2.purse_none
