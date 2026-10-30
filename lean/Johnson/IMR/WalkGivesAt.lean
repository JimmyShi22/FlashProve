-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/WalkGivesAt.lean: WHAT KIND K8's LAW ON A WALK ASKS
(Johnson/Desc/First/K8/LawWalk.lean: K8.Named.WalkGives a b b' s: what a walk from a link's first
sending to the record s in front of the draw hands on): AT ALL 25 LINKS OF THE PROOF FILE's SEAT, IN
THE GOALS' SCOPE, FROM THE FOLDS' RETURNS ALONE.
IT DOES NOT IMPORT THAT FILE.
WalkSeven a b b' s: THAT STRUCTURE's SEVEN FIELDS,
IN ITS ORDER AND ITS LETTERS, AS ONE CONJUNCTION:
its term is
⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩.

  RU, seatKeeps_rootsUp: the count of roots never falls: one more rider of SeatKeeps.lean's walk.
  open_between: of two cuts of c.blocksInOrder in front of the blocks behind the last link, one in front of
    the other: the records of one fold are related.
  open_fits, open_has: Book.BookFits, and as many places as oracle messages, at an opening's
    letters.
  walk_of: the seven fields, from Johnson/IMR/ListsAtDraw.lean's conclusion and these.
  walkGives_at (1 ≤ l < 24), walkGives_at0, walkGives_at24: WalkSeven t₀.roots t₁.roots t₄.roots t₄,
    with t₀.roots ≤ t₁.roots ≤ t₄.roots, which LawWalk.lean's namedAt_of_walk asks beside.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USER: the files on the book's
names.
Not claimed: that the three counts are the plan's numbers (PlanGives). No soundness.
-/
import Johnson.IMR.ListsEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Ground (Core coreOf ByC CoreStill CoreRecv coreStill_same)
open VerifiableInference.Desc.K1.RelCore (coreS)
open VerifiableInference.Desc.Book (BookFits)
open ProofFile (Pub Cl)

/-! ## The count of roots never falls -/

/-- **The relation.** -/
abbrev RU : S → S → Prop := ByC (fun a b => a.roots ≤ b.roots) coreS

theorem ru_same (a b : Core) (_ : b.book = a.book) (h : b.roots = a.roots) : a.roots ≤ b.roots :=
  Nat.le_of_eq h.symm

theorem ru_recv {L : Type} (ft : Nat) (d d' : _root_.Desc.Plain.DState L)
    (sent : Array OracleNotice) (ids : Array Nat) (h : Ground.recvP ft d sent = some (ids, d')) :
    d.roots ≤ d'.roots := by
  obtain ⟨lay, -, e⟩ := Book.recvP_roots ft d d' sent ids h
  rw [e]
  exact Nat.le_add_right _ _

theorem coreRecv_rootsUp : CoreRecv 0 fun a b => a.roots ≤ b.roots where
  refl := fun _ => Nat.le_refl _
  trans := fun h k => Nat.le_trans h k
  newGroup := fun d d' c m n h => Nat.le_of_eq (coreStill_same.newGroup d d' c m n h).2.symm
  admit := fun d d' o r h => Nat.le_of_eq (coreStill_same.admit d d' o r h).2.symm
  join := fun d d' g o k h => Nat.le_of_eq (coreStill_same.join d d' g o k h).2.symm
  addRow := fun d d' g r h => Nat.le_of_eq (coreStill_same.addRow d d' g r h).2.symm
  takeMask := fun d d' o n h => Nat.le_of_eq (coreStill_same.takeMask d d' o n h).2.symm
  closeLedger := fun d d' o h => Nat.le_of_eq (coreStill_same.closeLedger d d' o h).2.symm
  spendAsMask := fun d d' o h => Nat.le_of_eq (coreStill_same.spendAsMask d d' o h).2.symm
  elsewhere := fun d d' m o t h => Nat.le_of_eq (coreStill_same.elsewhere d d' m o t h).2.symm
  recv := fun d d' sent ids h => ru_recv 0 d d' sent ids h

theorem ru_fn {f : S → Except String S}
    (h : ∀ s t, f s = .ok t → t.book = s.book ∧ t.roots = s.roots) : Fn RU f :=
  fun s t k => Nat.le_of_eq (h s t k).2.symm

theorem seatKeeps_rootsUp : SeatKeeps RU where
  refl := fun _ => Nat.le_refl _
  trans := fun _ _ _ h k => Nat.le_trans h k
  frames := fun _ h => framesOf_core ru_same h
  k1First := fun q gp h0 => firstAtS_core coreRecv_rootsUp q gp h0
  k1Later := fun q gp l p m a h0 => laterAt_core coreRecv_rootsUp q gp l p m a h0
  reads := fun h => whole_core ru_same (readsQuietAt_quiet h)
  k3 := fun c r X cs sh a _ h => whole_core ru_same (theStated_quiet c r X cs sh a h)
  k4 := fun p => whole_core ru_same (blockAtC_quiet p)
  k5 := fun W l g bf _ h => whole_core ru_same (k5AtN_quiet W l g bf h)
  k6 := fun h => whole_core ru_same (seatedClaims_quiet h)
  k7 := fun W l => whole_core ru_same (k7Of_quiet W l)
  k8 := fun p => whole_core ru_same (k8Whole_quiet p)
  closeOf := closeOf_core ru_same
  batch := fun p _ hcl => batch_core ru_same (fun h k => Nat.le_trans h k) p hcl
  k11 := fun Q => whole_core ru_same (headMerge11_quiet Q)
  k2 := fun _ _ => ⟨fun s _ _ s' h => by
      obtain ⟨x, lay, -, -, e, -⟩ := K2.yes_seated h
      show s.roots ≤ s'.roots
      rw [e]
      exact Nat.le_add_right _ _,
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  front := fun _ => ru_fn fun _ _ h => K2.headFrontQ_book h
  openQ := fun _ _ => ru_fn fun _ _ h => K2.headOpenQ_book h
  finFront := ru_fn fun _ _ h => K2.finishFrontQ_book h
  finBehind := ru_fn fun _ _ h => K2.finishBehindQ_book h

/-! ## At an opening's letters -/

variable {R : S → S → Prop} {okB : Array Stages.LinkH → Prop} {okP : K2.HeadPar → Prop}
  {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **Of two cuts, one in front of the other.** -/
theorem open_between (H : SeatKeeps R okB okP) (O : IM.Open o pol lay KL F Z Bs base c A B)
    (hB : okB Z.p.built.links) (hP : ∀ l Q, P1K2.pureLetters Bs.G₀ l = some Q → okP Q)
    {k k' : Nat} (hkk : k ≤ k') (hk : k' ≤ (frontOf c).length) {ft : Nat} {s t t' : S}
    {rs r r' : List Fmt.RoundView} {cols q q' : List VerifiableInference.Desc.OpenedColumn}
    (h : foldBlocks ft (c.blocksInOrder.take k) s rs cols = .ok (t, r, q))
    (h' : foldBlocks ft (c.blocksInOrder.take k') s rs cols = .ok (t', r', q')) : R t t' := by
  obtain ⟨h0, K⟩ := open_front H O hB hP
  have e : c.blocksInOrder.take k ++ (c.blocksInOrder.take k').drop k = c.blocksInOrder.take k' := by
    have z := List.take_append_drop k (c.blocksInOrder.take k')
    rwa [List.take_take, Nat.min_eq_left hkk] at z
  rw [← e] at h'
  obtain ⟨u, r₁, q₁, g0, g1⟩ := Keeps.foldBlocks_split ft _ _ _ _ _ _ h'
  rw [h] at g0
  cases g0
  refine Keeps.foldBlocks_keeps R H.refl H.trans ft _ (fun b hb => K b ?_) _ _ _ _ g1
  have hb' := List.mem_of_mem_drop hb
  rw [flat_eq h0, List.take_append_of_le_length hk] at hb'
  exact List.mem_of_mem_take hb'

theorem open_fits (O : IM.Open o pol lay KL F Z Bs base c A B) {k : Nat}
    (hk : k ≤ (frontOf c).length) {ft : Nat} {p : ProofFile.InstPub} {rs : List Fmt.RoundView}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    {r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn}
    (h : foldBlocks ft (c.blocksInOrder.take k) (ProofFile.startS Z p) rs cols = .ok r) : BookFits r.1.book := by
  have K1 : SeatKeeps (PR fun B _ => BookFits B) := seatKeeps_front
    (fun d d' sent ids e k => Book.recvP_fits 0 d d' sent ids e k)
    (fun _ _ _ hs k => K2.fits_same hs k)
  have hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z := O.pub
  refine open_fold K1 O trivial (fun _ _ _ => trivial) hk h ?_
  show BookFits (ProofFile.startS Z p).book
  rw [(start_empty hZ p).1]
  exact Book.bookFits_empty

theorem open_has (O : IM.Open o pol lay KL F Z Bs base c A B) {k : Nat}
    (hk : k ≤ (frontOf c).length) {ft : Nat} {p : ProofFile.InstPub} {rs : List Fmt.RoundView}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    {r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn}
    (h : foldBlocks ft (c.blocksInOrder.take k) (ProofFile.startS Z p) rs cols = .ok r) :
    r.1.book.place.size = r.1.st.oracles.size := by
  have hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z := O.pub
  refine open_fold (seatKeeps_has k2Has) O trivial (fun _ _ _ => trivial) hk h ?_
  show (ProofFile.startS Z p).book.place.size = (ProofFile.startS Z p).st.oracles.size
  rw [(start_empty hZ p).1, start_none hZ p]
  rfl

/-! ## The seven fields -/

/-- K8.Named.WalkGives' seven fields, in its order: fits, has, shape, link, moments, kept, own. -/
def WalkSeven (a b b' : Nat) (s : S) : Prop :=
  BookFits s.book ∧ s.book.place.size = s.st.oracles.size ∧
  (∀ L, s.link? = some L → reqShapeOk L.check.frame.shape = true) ∧
  (∀ L, s.link? = some L → L.check.frame.link = L.link) ∧
  (∀ L, s.link? = some L → L.moments ≤ 2) ∧
  (∀ L, s.link? = some L → ∀ o ∈ L.check.frame.keptBefore.toList,
    ∃ jt : Nat × Nat, s.book.place[o]? = some jt ∧ a ≤ jt.1 ∧ jt.1 < b) ∧
  ∀ L, s.link? = some L → ∀ j o : Nat, L.check.frame.own[j]? = some o →
    ∃ jt : Nat × Nat, s.book.place[o]? = some jt ∧
      ((j < (L.check.frame.atMoment 0).length ∧ a ≤ jt.1 ∧ jt.1 < b) ∨
        ((L.check.frame.atMoment 0).length ≤ j ∧ b ≤ jt.1 ∧ jt.1 < b'))

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy}

/-- **The seven fields**, from ListsAtDraw.lean's conclusion at the record behind the first k
entries. -/
theorem walk_of (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : Nat} (h2 : 2 ≤ k)
    (hk : k ≤ (frontOf c).length) {p : ProofFile.InstPub} {Rr R₄ : List Fmt.RoundView}
    {C C₄ : List VerifiableInference.Desc.OpenedColumn} {t₄ : S} {a b b' : Nat}
    (f₄ : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) Rr C = .ok (t₄, R₄, C₄))
    (hc : ∃ L, t₄.link? = some L ∧
        (∀ o ∈ L.check.frame.keptBefore.toList, ∃ jt : Nat × Nat,
          t₄.book.place[o]? = some jt ∧ a ≤ jt.1 ∧ jt.1 < b) ∧
        (∀ j o : Nat, L.check.frame.own[j]? = some o → ∃ jt : Nat × Nat,
          t₄.book.place[o]? = some jt ∧
          ((j < (L.check.frame.atMoment 0).length ∧ a ≤ jt.1 ∧ jt.1 < b) ∨
            ((L.check.frame.atMoment 0).length ≤ j ∧ b ≤ jt.1 ∧ jt.1 < b'))) ∧
        L.check.frame.link = L.link ∧ L.moments = 2) :
    WalkSeven a b b' t₄ := by
  obtain ⟨L, hL, c1, c2, c3, c4⟩ := hc
  have hsh := shape_ok hS hR O h2 hk f₄
  have un : ∀ L', t₄.link? = some L' → L' = L := fun L' h' =>
    Option.some.inj (h'.symm.trans hL)
  refine ⟨open_fits O hk f₄, open_has O hk f₄, fun L' h' => ?_, fun L' h' => ?_,
    fun L' h' => ?_, fun L' h' => ?_, fun L' h' => ?_⟩
  · rw [un L' h', ← live_open hL]
    exact hsh
  · rw [un L' h']
    exact c3
  · rw [un L' h', c4]
  · rw [un L' h']
    exact c1
  · rw [un L' h']
    exact c2

/-- A link's fifth hearing block stands in front of the blocks behind the last link. -/
theorem draw_in_front (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l i : Nat} (hl : l < 25)
    (hi : i < 7) : 14 * l + i + 2 ≤ (frontOf c).length := by
  obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, f, bL, bB, bC, eL, hlen, -⟩ := hfr l hl
  have hi' : i < Lk.hear.length := by
    rw [hlen]
    split <;> omega
  have k := flatIx_le (chainBy_noFront O.chain) eL (List.getElem?_eq_getElem hi')
  rwa [IM.flatIx_scope hS hR O (by omega) i] at k

/-- **AT THE LINKS 1 TO 23.** -/
theorem walkGives_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ l, 1 ≤ l → l < 24 → ∀ (p : ProofFile.InstPub) (Rr : List Fmt.RoundView)
      (C : List VerifiableInference.Desc.OpenedColumn) (t₀ t₁ t₄ : S) (R₀ R₁ R₄ : List Fmt.RoundView)
      (C₀ C₁ C₄ : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) Rr C = .ok (t₀, R₀, C₀) →
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 3)) (ProofFile.startS Z p) Rr C = .ok (t₁, R₁, C₁) →
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 6)) (ProofFile.startS Z p) Rr C = .ok (t₄, R₄, C₄) →
      WalkSeven t₀.roots t₁.roots t₄.roots t₄ ∧ t₀.roots ≤ t₁.roots ∧
        t₁.roots ≤ t₄.roots := by
  intro l h1 h24 p Rr C t₀ t₁ t₄ R₀ R₁ R₄ C₀ C₁ C₄ f₀ f₁ f₄
  have hk : 14 * l + 6 ≤ (frontOf c).length := draw_in_front hS hR O (l := l) (i := 4) (by omega)
    (by decide)
  obtain ⟨L, hL, c1, c2, -, -, c3, c4⟩ :=
    lists_at_draw hS hR O l h1 h24 p Rr C t₀ t₁ t₄ R₀ R₁ R₄ C₀ C₁ C₄ f₀ f₁ f₄
  exact ⟨walk_of hS hR O (by omega) hk f₄ ⟨L, hL, c1, c2, c3, c4⟩,
    open_between seatKeeps_rootsUp O trivial (fun _ _ _ => trivial) (by omega) (by omega) f₀ f₁,
    open_between seatKeeps_rootsUp O trivial (fun _ _ _ => trivial) (by omega) hk f₁ f₄⟩

/-- **AT LINK 0.** -/
theorem walkGives_at0 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ (p : ProofFile.InstPub) (Rr : List Fmt.RoundView)
      (C : List VerifiableInference.Desc.OpenedColumn) (t₀ t₁ t₄ : S) (R₀ R₁ R₄ : List Fmt.RoundView)
      (C₀ C₁ C₄ : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take 2) (ProofFile.startS Z p) Rr C = .ok (t₀, R₀, C₀) →
      foldBlocks 0 (c.blocksInOrder.take 3) (ProofFile.startS Z p) Rr C = .ok (t₁, R₁, C₁) →
      foldBlocks 0 (c.blocksInOrder.take 6) (ProofFile.startS Z p) Rr C = .ok (t₄, R₄, C₄) →
      WalkSeven t₀.roots t₁.roots t₄.roots t₄ ∧ t₀.roots ≤ t₁.roots ∧
        t₁.roots ≤ t₄.roots := by
  intro p Rr C t₀ t₁ t₄ R₀ R₁ R₄ C₀ C₁ C₄ f₀ f₁ f₄
  have hk : 6 ≤ (frontOf c).length := draw_in_front hS hR O (l := 0) (i := 4) (by decide)
    (by decide)
  obtain ⟨L, hL, c1, c2, -, -, c3, c4⟩ :=
    lists_at_draw0 hS hR O p Rr C t₀ t₁ t₄ R₀ R₁ R₄ C₀ C₁ C₄ f₀ f₁ f₄
  exact ⟨walk_of hS hR O (by decide) hk f₄ ⟨L, hL, c1, c2, c3, c4⟩,
    open_between seatKeeps_rootsUp O trivial (fun _ _ _ => trivial) (by decide) (by omega) f₀ f₁,
    open_between seatKeeps_rootsUp O trivial (fun _ _ _ => trivial) (by decide) hk f₁ f₄⟩

/-- **AT THE HEAD's LINK.** -/
theorem walkGives_at24 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ (p : ProofFile.InstPub) (Rr : List Fmt.RoundView)
      (C : List VerifiableInference.Desc.OpenedColumn) (t₀ t₁ t₄ : S) (R₀ R₁ R₄ : List Fmt.RoundView)
      (C₀ C₁ C₄ : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) Rr C = .ok (t₀, R₀, C₀) →
      foldBlocks 0 (c.blocksInOrder.take 340) (ProofFile.startS Z p) Rr C = .ok (t₁, R₁, C₁) →
      foldBlocks 0 (c.blocksInOrder.take 343) (ProofFile.startS Z p) Rr C = .ok (t₄, R₄, C₄) →
      WalkSeven t₀.roots t₁.roots t₄.roots t₄ ∧ t₀.roots ≤ t₁.roots ∧
        t₁.roots ≤ t₄.roots := by
  intro p Rr C t₀ t₁ t₄ R₀ R₁ R₄ C₀ C₁ C₄ f₀ f₁ f₄
  have hk : 343 ≤ (frontOf c).length := draw_in_front hS hR O (l := 24) (i := 5) (by decide)
    (by decide)
  obtain ⟨L, hL, c1, c2, -, -, c3, c4⟩ :=
    lists_at_draw24 hS hR O p Rr C t₀ t₁ t₄ R₀ R₁ R₄ C₀ C₁ C₄ f₀ f₁ f₄
  exact ⟨walk_of hS hR O (by decide) hk f₄ ⟨L, hL, c1, c2, c3, c4⟩,
    open_between seatKeeps_rootsUp O trivial (fun _ _ _ => trivial) (by decide) (by omega) f₀ f₁,
    open_between seatKeeps_rootsUp O trivial (fun _ _ _ => trivial) (by decide) hk f₁ f₄⟩

end

#print axioms seatKeeps_rootsUp
#print axioms open_between
#print axioms walk_of
#print axioms walkGives_at
#print axioms walkGives_at0
#print axioms walkGives_at24

end Meaning.K2
