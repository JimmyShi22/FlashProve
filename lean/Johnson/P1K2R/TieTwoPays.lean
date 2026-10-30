-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/TieTwoPays.lean: code switching (K2): FIVE PREMISES OF THE SECOND TIE AT A
PLACE (k02_t2S, Johnson/P1K2R/TieTwoS.lean: hbk · hBF · hnew · hshN · hSR; fields of K2Short), EACH
IN THE BINDER's OWN LETTERS, FROM THE HEAD, NAMED TESTS, THE PLACE AND THE WAY IN.
  hbk_id · hbk_fin  (1) hbk: the way in leaves the book: at the way in that lets a state in as it
               is; at the finish's
  hBF_plain    (2) hBF: the book fits in front of an accept and behind it: atFirstFits_all at
               both borders; «reached» behind by reach_next (both in Johnson/IMR/)
  noticesW_link · noticesW_head · noticesW_fin  in scope, at the written shape, what a switch's
               front announces is the written list sentW g
  noticesFit_full · noticesFit_at  THE TEST noticesFitB ACCEPTS AT ALL 25 WRITTEN LISTS: by
               Lean's kernel
  noticesFit_can_fail  a negative test: with one notice more laid behind, so that the fold's mask
               is no longer the last, the test rejects at the first list
  book_of_on   what the promise in front says of the book's counts (bookAt)
  hnew_of_fence      (3) hnew, general: from the accept through the door · the test sentFitB · the
               promise · «the front's notices are sent and its codes are codes» · «each notice but
               the last counts an answer and has a row»
  hnew_link · hnew_head · hnew_fin  (3) hnew at the 25 places, sentFitB at the written list
  hnew_link_n · hnew_head_n · hnew_fin_n  the same, sentFitB at the plan's numbers n of the switch
  hshN_of      (4) hshN: every leaf of the new members' trees is shown behind: from
               Piece.ShownAll at the piece, and «each new member's tree is one that the piece's
               stretch sends»
  sentInB · hsent_of_test · sentIn_can_fail  a test with code for «each new member's tree is one
               that the piece's stretch sends», its law, and a negative test
  seedReads    (5) hSR: K2.SeedReads IS A THEOREM: ToldDesc.seedOf_form
               (Johnson/ToldDescR/SeedOfForm.lean)
(1) AND (2): by report hbk | hBF also compile in
Tw/K2C/FitsAtPlace.lean (not opened here); of hBF_plain the first
half (the book fits at a reached state, with no field of FoldFacts) is this file's own.
WHAT STAYS IN FRONT, PREMISE BY PREMISE.
  (1) hent (HT1Tight.lean's) alone. (5) nothing.
  (2) O · hpl · hRch · hft: the frame's first tree is 0 · hBk: B is the chain's sub-protocol number
      k.
  (3) hS · hR · O (at the public files' own layout file) · hy (madePinnedAt's accept: for the
      written shape) · hRch · hT: THE TEST sentFitB ACCEPTS at N, the group, the place, the public
      part's codes and the written list sentW g (closed once N is closed); in hnew_…_n: at n.codes
      and n.sent, the plan's numbers of the switch (then also hF · hpl · hP · hn) · hSit: B sits
      over the kind's own sub-protocol behind the door · hent · hq · the promise in front, which
      is spent. noticesFitB IS NO PREMISE.
  (4) hAll: q.ShownAll G r.cs r.l seatN (shownOfData gives it at every piece that the maker
      cuts, under SeatFits) · hsent: each new member's seat's tree is q.base + n with a shape in
      q.ds. SeatFits HAS A PAYER AT THE 25 PLACES: seats_full (K2Caller/SeatFitsFull.lean):
      under the head's named test fit, at seatN i := (N0Full.sent (m + 1) 0).getD i
      (0, 0). FOR hsent THIS WRITER HAS FOUND NO LEMMA: here it is brought down to a test with code
      on closed lists (sentInB · hsent_of_test), EVALUATED AT NO REAL VALUE.
LIMITS. Joins, and one closed fact by the kernel. No premise is shown met at a real value: no
example. The full size alone. No probability; no soundness is claimed.
-/
import Johnson.P1K2R.BookTight
import Johnson.P1K2R.HstReached
import Johnson.P1K2R.TieTwoAt
import Johnson.Top.H0.Tw.K2C.HeldAtPlan
import Johnson.Top.H0.Tw.K2C.HandsLink
import Johnson.Desc.K12.Law.Sits
import Johnson.Desc.Sound.ShownOfData
import Johnson.Desc.Sound.SendLaw
import Johnson.Desc.Sound.BookTestsLaw
import Johnson.IMR.HandsReach
import Johnson.ToldDescR.SeedOfForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes OnBytes.Model
open OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open _root_.Iop (Err)
open VerifiableInference.Desc
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.K2 (ownPiece noticesFitB sentFitB sent_of_test hall_of_test
  SeedReads)
open VerifiableInference.Desc.First.K2Hands (sentW)
open VerifiableInference.PlanWritten (madePinnedAt)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open H2K.JointK (Sits)
open IM (openAt)
open _root_.Tw.K2 (switchNotices)
open ProofFile (Cl)

/-! ## (1) hbk -/

theorem hbk_id {enter : S → Except String S} (hent : ∀ s t, enter s = .ok t → t = s) :
    ∀ s t, enter s = .ok t → t.book = s.book := fun s t h => (keeps_id hent s t h).1

theorem hbk_fin {enter : S → Except String S}
    (hent : ∀ s t, enter s = .ok t → K2.finishFrontQ s = .ok t) :
    ∀ s t, enter s = .ok t → t.book = s.book := fun s t h => (keeps_fin hent s t h).1

/-! ## (5) hSR -/

/-- **K2.SeedReads is a theorem.** -/
theorem seedReads : SeedReads := fun _ _ _ _ _ _ y h h1 h2 => ToldDesc.seedOf_form y h h1 h2

/-! ## The test noticesFitB at the 25 written lists -/

/-- **It accepts at all 25**: by Lean's kernel. -/
theorem noticesFit_full :
    (List.range 25).all (fun i => noticesFitB (sentW (i + 1)).toArray) = true := by
  decide +kernel

theorem noticesFit_at {g : ℕ} (h1 : 1 ≤ g) (h25 : g ≤ 25) :
    noticesFitB (sentW g).toArray = true := by
  have k := List.all_eq_true.1 noticesFit_full (g - 1) (List.mem_range.2 (by omega))
  rwa [show g - 1 + 1 = g by omega] at k

/-- **A negative test**: one notice more behind the first list: the fold's mask is no longer the
last, and the test rejects. -/
theorem noticesFit_can_fail : noticesFitB ((sentW 1).toArray.push default) = false := by
  decide +kernel

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B' : ProofFile.SecondSeat}

/-! ## What a switch's front announces, at the written shape -/

theorem noticesW_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B')
    (hsh : Z.first.shape = K2Hands.shW) {m : ℕ} (h23 : m < 23) {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s)) {p : K2.P2}
    (hq : p.stands = .link) {x : _root_.Tw.K2.Front} (h : K2.frontAt p s = some x) :
    x.st.codes = Z.first.codes ∧ (switchNotices x.T x.others).toList = sentW (m + 1) := by
  obtain ⟨-, R, C, f⟩ := (reach_raw hr).fold
  obtain ⟨a1, -, a3, a4, -⟩ := Meaning.K2.front_pin_link hS hR O (l := m + 1) (by omega) (by omega)
    f hq h
  refine ⟨a1, ?_⟩
  rw [a3, a4, hsh]
  unfold K2Hands.sentW
  rw [if_neg (by omega)]

theorem noticesW_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B')
    (hsh : Z.first.shape = K2Hands.shW) {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) {p : K2.P2}
    (hq : p.stands = .head) {x : _root_.Tw.K2.Front} (h : K2.frontAt p s = some x) :
    x.st.codes = Z.first.codes ∧ (switchNotices x.T x.others).toList = sentW 24 := by
  obtain ⟨-, R, C, f⟩ := (reach_raw hr).fold
  obtain ⟨a1, -, a3, a4, -⟩ := Meaning.K2.front_pin_head hS hR O f hq h
  refine ⟨a1, ?_⟩
  rw [a3, a4, hsh]
  unfold K2Hands.sentW
  rw [if_neg (by omega)]

theorem noticesW_fin (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B')
    (hsh : Z.first.shape = K2Hands.shW) {z : ProofFile.InstPub} {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (he : K2.finishFrontQ s = .ok t) {p : K2.P2}
    (hq : p.stands = .finish) {x : _root_.Tw.K2.Front} (h : K2.frontAt p t = some x) :
    x.st.codes = Z.first.codes ∧ (switchNotices x.T x.others).toList = sentW 25 := by
  obtain ⟨-, R, C, f⟩ := (reach_raw hr).fold
  obtain ⟨a1, -, a3, a4, -⟩ := Meaning.K2.front_pin_fin hS hR O f he hq h
  refine ⟨a1, ?_⟩
  rw [a3, a4, hsh]
  unfold K2Hands.sentW
  rw [if_pos rfl]

end

section
variable {C : CK} {Fr : Frame} {Wt : Type} {N : Numbers} {Mg : Meaning ProofFile.InstPub Wt}
  {links : List ModelPart} {ps : List Place} {Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop}
  {q : Piece C Fr (ProofFile.InstPub × S) Cl Wt} {B : Block S Cl}
  {ext : ProofFile.InstPub → S × Fr.E.Str → Iop.Tr (uLT C q.ds) → Wt → Wt} {err : Err (uLT C q.ds)}

/-- What the promise in front says of the book's counts. -/
theorem book_of_on {k : ℕ} {z : ProofFile.InstPub} {a : S × Fr.E.Str}
    (ha : onQ N Mg links ps (fun s => (z, s)) k a) (hm : ¬ a.1.failed ≠ none) :
    bookAt N ps[k]? a.1 = true := by
  have ha' : onAt N Mg links ps[k]? (openAt links ps k) (pubAt Mg links ps k) (z, a.1)
      (strsOf Fr a.2) := ha
  rcases ha'.2 with h | ⟨h, -⟩
  · exact absurd h hm
  · simp only [Bool.and_eq_true] at h
    exact h.2

/-! ## (2) hBF -/

section
variable {P : VerifierAndGoals.PublicFiles} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B' : ProofFile.SecondSeat}

/-- **hBF: the book fits in front of an accept and behind it.** -/
theorem hBF_plain (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B')
    (hpl : F.planOk = true)
    (hRch : ∀ k x, Rch k x → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    (hft : Fr.ft = 0) {k : ℕ} (hBk : c.blocksInOrder[k]? = some B) :
    ∀ z a τ b, onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none → (ownPiece q B (ext z) err).ior.red.out a τ = some b →
      BookFits a.1.book ∧ BookFits b.1.book := by
  intro z a τ b _ hr _ hb
  have r := reach_raw (hRch _ _ hr)
  have hy : IM.Yes Fr.ft B a.1 b.1 := yes_of_out hb
  rw [hft] at hy
  have r' := IM.reach_next r hBk hy
  exact ⟨(bookFitsB_iff _).1 (Meaning.K2.atFirstFits_all O (plan_of O hpl) r),
    (bookFitsB_iff _).1 (Meaning.K2.atFirstFits_all O (plan_of O hpl) r')⟩

end

/-! ## (3) hnew -/

/-- **hnew, general.** -/
theorem hnew_of_fence {k g : ℕ} {codes : Codes} {sent : Array OracleNotice}
    (hT : sentFitB N g ps[k]? codes sent = true) {p : K2.P2} {enter : S → Except String S}
    {leave : S → S → Except String S} (hSit : Sits B (K2.codeSwitchKind p : Block S Unit) enter leave)
    (hbk : ∀ s t, enter s = .ok t → t.book = s.book)
    (hfence : ∀ z, ∀ a : S × Fr.E.Str, Rch k ((z, a.1), a.2) → ∀ t, enter a.1 = .ok t →
      ∀ x, K2.frontAt p t = some x → switchNotices x.T x.others = sent ∧ x.st.codes = codes ∧
        noticesFitB (switchNotices x.T x.others) = true) :
    ∀ z a τ b, onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none → (ownPiece q B (ext z) err).ior.red.out a τ = some b →
      ∀ t, enter a.1 = .ok t → ∃ (x : _root_.Tw.K2.Front) (lay : TreeLay) (n : Nat),
        K2.frontAt p t = some x ∧
        layTrees x.st.codes (switchNotices x.T x.others) = some lay ∧
        sameMembers ((List.range n).map fun i =>
          (t.book.trees.size + lay.tree.getD i 0, lay.part.getD i 0)) (N.sent g 0) = true ∧
        ∀ i, i < n → ∃ nt, (switchNotices x.T x.others)[i]? = some nt ∧
          nt.shape.answers ≠ 0 ∧ 0 < nt.shape.mainRows + nt.shape.maskRows := by
  intro z a τ b ha hr hm hb t he
  obtain ⟨rs, cols, n₁, hy⟩ := yes_of_out hb
  obtain ⟨t₁, t', e1, e2, -⟩ := hSit.step Fr.ft a.1 b.1 rs cols n₁ hy
  obtain rfl : t₁ = t := Except.ok.inj (e1.symm.trans he)
  obtain ⟨r₁, r₂, gs, -, hd⟩ := K2.k2_step_two e2
  obtain ⟨x, lay, f, hl, -, -⟩ := K2.yes_seated hd
  have hx := K2.frontAt_of f
  obtain ⟨h1, h2, h3⟩ := hfence z a hr t₁ he x hx
  refine ⟨x, lay, (switchNotices x.T x.others).size - 1, hx, hl, ?_, hall_of_test h3 rfl rfl⟩
  rw [hbk _ _ he]
  exact sent_of_test hT (book_of_on ha hm) h1 h2 hl rfl

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B' : ProofFile.SecondSeat}

/-- The test at a front's own notices, from the written list. -/
theorem noticesFit_of_written {ns : Array OracleNotice} {g : ℕ} (h1 : 1 ≤ g) (h25 : g ≤ 25)
    (h : ns.toList = sentW g) : noticesFitB ns = true := by
  have e : ns = (sentW g).toArray := by rw [← h]
  rw [e]
  exact noticesFit_at h1 h25

/-- **hnew AT THE SWITCH INTO GROUP m + 1, m < 23.** -/
theorem hnew_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B')
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hRch : ∀ k x, Rch k x → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    {m : ℕ} (h23 : m < 23)
    (hT : sentFitB N (m + 1) ps[14 * (m + 1) + 2]? Z.first.codes (sentW (m + 1)).toArray = true)
    {p : K2.P2} (hq : p.stands = .link) {enter : S → Except String S}
    {leave : S → S → Except String S} (hSit : Sits B (K2.codeSwitchKind p : Block S Unit) enter leave)
    (hent : ∀ s t, enter s = .ok t → t = s) :
    ∀ z a τ b, onQ N Mg links ps (fun s => (z, s)) (14 * (m + 1) + 2) a →
      Rch (14 * (m + 1) + 2) ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (ownPiece q B (ext z) err).ior.red.out a τ = some b →
      ∀ t, enter a.1 = .ok t → ∃ (x : _root_.Tw.K2.Front) (lay : TreeLay) (n : Nat),
        K2.frontAt p t = some x ∧
        layTrees x.st.codes (switchNotices x.T x.others) = some lay ∧
        sameMembers ((List.range n).map fun i =>
          (t.book.trees.size + lay.tree.getD i 0, lay.part.getD i 0)) (N.sent (m + 1) 0) = true ∧
        ∀ i, i < n → ∃ nt, (switchNotices x.T x.others)[i]? = some nt ∧
          nt.shape.answers ≠ 0 ∧ 0 < nt.shape.mainRows + nt.shape.maskRows :=
  hnew_of_fence hT hSit (hbk_id hent) fun z a hr t he x hx => by
    obtain rfl := hent _ _ he
    obtain ⟨h1, h2⟩ := noticesW_link hS hR O (written3 hS O.pub hy).2.1 h23 (hRch _ _ hr) hq hx
    exact ⟨by rw [← h2], h1, noticesFit_of_written (by omega) (by omega) h2⟩

/-- **hnew AT THE OUTPUT HEAD's SWITCH.** -/
theorem hnew_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B')
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hRch : ∀ k x, Rch k x → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    (hT : sentFitB N 24 ps[339]? Z.first.codes (sentW 24).toArray = true)
    {p : K2.P2} (hq : p.stands = .head) {enter : S → Except String S}
    {leave : S → S → Except String S} (hSit : Sits B (K2.codeSwitchKind p : Block S Unit) enter leave)
    (hent : ∀ s t, enter s = .ok t → t = s) :
    ∀ z a τ b, onQ N Mg links ps (fun s => (z, s)) (339) a →
      Rch (339) ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (ownPiece q B (ext z) err).ior.red.out a τ = some b →
      ∀ t, enter a.1 = .ok t → ∃ (x : _root_.Tw.K2.Front) (lay : TreeLay) (n : Nat),
        K2.frontAt p t = some x ∧
        layTrees x.st.codes (switchNotices x.T x.others) = some lay ∧
        sameMembers ((List.range n).map fun i =>
          (t.book.trees.size + lay.tree.getD i 0, lay.part.getD i 0)) (N.sent 24 0) = true ∧
        ∀ i, i < n → ∃ nt, (switchNotices x.T x.others)[i]? = some nt ∧
          nt.shape.answers ≠ 0 ∧ 0 < nt.shape.mainRows + nt.shape.maskRows :=
  hnew_of_fence hT hSit (hbk_id hent) fun z a hr t he x hx => by
    obtain rfl := hent _ _ he
    obtain ⟨h1, h2⟩ := noticesW_head hS hR O (written3 hS O.pub hy).2.1 (hRch _ _ hr) hq hx
    exact ⟨by rw [← h2], h1, noticesFit_of_written (by omega) (by omega) h2⟩

/-- **hnew AT THE FINISH's SWITCH.** -/
theorem hnew_fin (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B')
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hRch : ∀ k x, Rch k x → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    (hT : sentFitB N 25 ps[353]? Z.first.codes (sentW 25).toArray = true)
    {p : K2.P2} (hq : p.stands = .finish) {enter : S → Except String S}
    {leave : S → S → Except String S} (hSit : Sits B (K2.codeSwitchKind p : Block S Unit) enter leave)
    (hent : ∀ s t, enter s = .ok t → K2.finishFrontQ s = .ok t) :
    ∀ z a τ b, onQ N Mg links ps (fun s => (z, s)) (353) a →
      Rch (353) ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (ownPiece q B (ext z) err).ior.red.out a τ = some b →
      ∀ t, enter a.1 = .ok t → ∃ (x : _root_.Tw.K2.Front) (lay : TreeLay) (n : Nat),
        K2.frontAt p t = some x ∧
        layTrees x.st.codes (switchNotices x.T x.others) = some lay ∧
        sameMembers ((List.range n).map fun i =>
          (t.book.trees.size + lay.tree.getD i 0, lay.part.getD i 0)) (N.sent 25 0) = true ∧
        ∀ i, i < n → ∃ nt, (switchNotices x.T x.others)[i]? = some nt ∧
          nt.shape.answers ≠ 0 ∧ 0 < nt.shape.mainRows + nt.shape.maskRows :=
  hnew_of_fence hT hSit (hbk_fin hent) fun z a hr t he x hx => by
    obtain ⟨h1, h2⟩ := noticesW_fin hS hR O (written3 hS O.pub hy).2.1 (hRch _ _ hr) (hent _ _ he)
      hq hx
    exact ⟨by rw [← h2], h1, noticesFit_of_written (by omega) (by omega) h2⟩

/-! ### The same with sentFitB at the plan's numbers of the switch -/

theorem hnew_link_n (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B')
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hRch : ∀ k x, Rch k x → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    {m : ℕ} (h23 : m < 23) {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp)
    (hn : numsAt Pp (some (m + 1)) = some n)
    (hT : sentFitB N (m + 1) ps[14 * (m + 1) + 2]? n.codes n.sent = true)
    {p : K2.P2} (hq : p.stands = .link) {enter : S → Except String S}
    {leave : S → S → Except String S} (hSit : Sits B (K2.codeSwitchKind p : Block S Unit) enter leave)
    (hent : ∀ s t, enter s = .ok t → t = s) :
    ∀ z a τ b, onQ N Mg links ps (fun s => (z, s)) (14 * (m + 1) + 2) a →
      Rch (14 * (m + 1) + 2) ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (ownPiece q B (ext z) err).ior.red.out a τ = some b →
      ∀ t, enter a.1 = .ok t → ∃ (x : _root_.Tw.K2.Front) (lay : TreeLay) (n : Nat),
        K2.frontAt p t = some x ∧
        layTrees x.st.codes (switchNotices x.T x.others) = some lay ∧
        sameMembers ((List.range n).map fun i =>
          (t.book.trees.size + lay.tree.getD i 0, lay.part.getD i 0)) (N.sent (m + 1) 0) = true ∧
        ∀ i, i < n → ∃ nt, (switchNotices x.T x.others)[i]? = some nt ∧
          nt.shape.answers ≠ 0 ∧ 0 < nt.shape.mainRows + nt.shape.maskRows :=
  hnew_of_fence hT hSit (hbk_id hent) fun z a hr t he x hx => by
    obtain rfl := hent _ _ he
    obtain ⟨h1, h2⟩ := noticesW_link hS hR O (written3 hS O.pub hy).2.1 h23 (hRch _ _ hr) hq hx
    have hx' : _root_.Tw.K2.firstFront a.1.st a.1.check.frame = .ok x := by
      rcases K2.frontOf_iff.2 hx with ⟨-, e⟩ | ⟨e, -⟩ | ⟨e, -⟩
      · exact e
      · rw [hq] at e; cases e
      · rw [hq] at e; cases e
    exact ⟨(sw_link hS hR O hF hpl h23 hP hn (hRch _ _ hr)).2 x hx',
      h1.trans (codes_at O hP hn).symm, noticesFit_of_written (by omega) (by omega) h2⟩

theorem hnew_head_n (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B')
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hRch : ∀ k x, Rch k x → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some 24) = some n)
    (hT : sentFitB N 24 ps[339]? n.codes n.sent = true)
    {p : K2.P2} (hq : p.stands = .head) {enter : S → Except String S}
    {leave : S → S → Except String S} (hSit : Sits B (K2.codeSwitchKind p : Block S Unit) enter leave)
    (hent : ∀ s t, enter s = .ok t → t = s) :
    ∀ z a τ b, onQ N Mg links ps (fun s => (z, s)) (339) a →
      Rch (339) ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (ownPiece q B (ext z) err).ior.red.out a τ = some b →
      ∀ t, enter a.1 = .ok t → ∃ (x : _root_.Tw.K2.Front) (lay : TreeLay) (n : Nat),
        K2.frontAt p t = some x ∧
        layTrees x.st.codes (switchNotices x.T x.others) = some lay ∧
        sameMembers ((List.range n).map fun i =>
          (t.book.trees.size + lay.tree.getD i 0, lay.part.getD i 0)) (N.sent 24 0) = true ∧
        ∀ i, i < n → ∃ nt, (switchNotices x.T x.others)[i]? = some nt ∧
          nt.shape.answers ≠ 0 ∧ 0 < nt.shape.mainRows + nt.shape.maskRows :=
  hnew_of_fence hT hSit (hbk_id hent) fun z a hr t he x hx => by
    obtain rfl := hent _ _ he
    obtain ⟨h1, h2⟩ := noticesW_head hS hR O (written3 hS O.pub hy).2.1 (hRch _ _ hr) hq hx
    have hx' : K2.frontAt (IM.k2P Z default "" .head n) a.1 = some x := by
      refine K2.frontOf_iff.1 ?_
      rcases K2.frontOf_iff.2 hx with ⟨e, -⟩ | ⟨-, e⟩ | ⟨e, -⟩
      · rw [hq] at e; cases e
      · exact Or.inr (Or.inl ⟨rfl, e⟩)
      · rw [hq] at e; cases e
    exact ⟨(sw_head hS hR O hF hpl default "" hP hn (hRch _ _ hr)).2 x hx',
      h1.trans (codes_at O hP hn).symm, noticesFit_of_written (by omega) (by omega) h2⟩

theorem hnew_fin_n (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B')
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) (hpl : F.planOk = true)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hRch : ∀ k x, Rch k x → Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k x.1)
    {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp none = some n)
    (hT : sentFitB N 25 ps[353]? n.codes n.sent = true)
    {p : K2.P2} (hq : p.stands = .finish) {enter : S → Except String S}
    {leave : S → S → Except String S} (hSit : Sits B (K2.codeSwitchKind p : Block S Unit) enter leave)
    (hent : ∀ s t, enter s = .ok t → K2.finishFrontQ s = .ok t) :
    ∀ z a τ b, onQ N Mg links ps (fun s => (z, s)) (353) a →
      Rch (353) ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (ownPiece q B (ext z) err).ior.red.out a τ = some b →
      ∀ t, enter a.1 = .ok t → ∃ (x : _root_.Tw.K2.Front) (lay : TreeLay) (n : Nat),
        K2.frontAt p t = some x ∧
        layTrees x.st.codes (switchNotices x.T x.others) = some lay ∧
        sameMembers ((List.range n).map fun i =>
          (t.book.trees.size + lay.tree.getD i 0, lay.part.getD i 0)) (N.sent 25 0) = true ∧
        ∀ i, i < n → ∃ nt, (switchNotices x.T x.others)[i]? = some nt ∧
          nt.shape.answers ≠ 0 ∧ 0 < nt.shape.mainRows + nt.shape.maskRows :=
  hnew_of_fence hT hSit (hbk_fin hent) fun z a hr t he x hx => by
    have hsh := (written3 hS O.pub hy).2.1
    obtain ⟨h1, h2⟩ := noticesW_fin hS hR O hsh (hRch _ _ hr) (hent _ _ he) hq hx
    have hx' : K2.frontAt (IM.k2P Z default "" .finish n) t = some x := by
      refine K2.frontOf_iff.1 ?_
      rcases K2.frontOf_iff.2 hx with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, e⟩
      · rw [hq] at e; cases e
      · rw [hq] at e; cases e
      · exact Or.inr (Or.inr ⟨rfl, e⟩)
    exact ⟨(sw_finish hS hR O hF hpl (by rw [hsh]; exact shW_links) default "" hP hn (hRch _ _ hr)
      (hent _ _ he)).2 x hx', h1.trans (codes_at O hP hn).symm,
      noticesFit_of_written (by omega) (by omega) h2⟩

end

/-! ## (4) hshN -/

/-- **A test with code**: each of the first len seats of the list X sits in a tree whose number is
base + n with n a tree of the stretch ds. -/
def sentInB (X : List (ℕ × ℕ)) (len base : ℕ) (ds : List RDT) : Bool :=
  (List.range len).all fun i =>
    decide (base ≤ (X.getD i (0, 0)).1) && (treeShT ds ((X.getD i (0, 0)).1 - base)).isSome

theorem hsent_of_test {X : List (ℕ × ℕ)} {len base : ℕ} {ds : List RDT}
    (h : sentInB X len base ds = true) {seatN : Fin len → ℕ × ℕ}
    (hN : ∀ i : Fin len, seatN i = X.getD i.val (0, 0)) :
    ∀ i, ∃ n sh, (seatN i).1 = base + n ∧ treeShT ds n = some sh := by
  intro i
  have e := List.all_eq_true.1 h i.val (List.mem_range.2 i.isLt)
  rw [Bool.and_eq_true, decide_eq_true_eq, ← hN i] at e
  obtain ⟨sh, hs⟩ := Option.isSome_iff_exists.1 e.2
  exact ⟨(seatN i).1 - base, sh, by omega, hs⟩

/-- A negative test: a seat in a tree in front of the base. -/
theorem sentIn_can_fail : sentInB [(0, 0)] 1 1 [] = false := by decide

/-- **hshN: every leaf of the new members' trees is shown behind.** -/
theorem hshN_of {k : ℕ} {Xi : Type} {G : FileDescription Xi} {cs : Codes} {l : List (OracleShape × ℕ)}
    {seatN : Fin l.length → ℕ × ℕ} (hAll : q.ShownAll G cs l seatN)
    (hsent : ∀ i, ∃ n sh, (seatN i).1 = q.base + n ∧ treeShT q.ds n = some sh) :
    ∀ z a τ b, onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) →
      ¬ a.1.failed ≠ none → (ownPiece q B (ext z) err).ior.red.out a τ = some b →
      ∀ i, ShownAt G cs l seatN (strsOf Fr b.2) i := by
  intro z a τ b _ _ _ hb i
  obtain ⟨n, sh, h1, h2⟩ := hsent i
  rw [out_behind (ownPiece q B (ext z) err) a b τ hb]
  exact hAll a.2 τ i n sh h1 h2

end

end P1K2

#print axioms P1K2.hbk_id
#print axioms P1K2.hbk_fin
#print axioms P1K2.seedReads
#print axioms P1K2.noticesFit_full
#print axioms P1K2.noticesFit_at
#print axioms P1K2.noticesFit_can_fail
#print axioms P1K2.noticesW_link
#print axioms P1K2.noticesW_head
#print axioms P1K2.noticesW_fin
#print axioms P1K2.book_of_on
#print axioms P1K2.hBF_plain
#print axioms P1K2.hnew_of_fence
#print axioms P1K2.noticesFit_of_written
#print axioms P1K2.hnew_link
#print axioms P1K2.hnew_head
#print axioms P1K2.hnew_fin
#print axioms P1K2.hnew_link_n
#print axioms P1K2.hnew_head_n
#print axioms P1K2.hnew_fin_n
#print axioms P1K2.hsent_of_test
#print axioms P1K2.sentIn_can_fail
#print axioms P1K2.hshN_of
