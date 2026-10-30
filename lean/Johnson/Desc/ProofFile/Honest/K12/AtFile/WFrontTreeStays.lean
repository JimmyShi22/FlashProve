-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFrontTreeStays.lean: an older tree keeps its parts and its mark
of being opened at one list only, along the first chain.

  TreeStays        the relation on two books
  recv_stays, call_stays, calls_stays   a receiving, a call of a proximity test, a run of calls
  yes_stays        kind K2's block
  seatKeeps_tree, seatBack_tree   all that the library asks of a relation along the first chain

Limits.
- Nothing on completeness, soundness or what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontTrees
import Johnson.IMR.BookFitsSeat
import Johnson.Desc.K12.Coin.BookFitsFields

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K2
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Ground (Core ByC CoreStill CoreRecv coreStill_same)
open VerifiableInference.Desc.K1.RelCore (coreS)
open _root_.Tw.K2 (SwIn SwOut switchBehind switchNotices sendByL8 openOne readOld)
open Meaning.K2

/-- **An older tree keeps its parts and its mark of being opened at one list only.** -/
def TreeStays (A B : TreeBook) : Prop :=
  ∀ (z : ℕ) (T : OnBytes.Tree), A.trees[z]? = some T →
    ∃ T' : OnBytes.Tree, B.trees[z]? = some T' ∧ T'.parts = T.parts ∧ T'.oneList = T.oneList

theorem TreeStays.refl (A : TreeBook) : TreeStays A A := fun _ T h => ⟨T, h, rfl, rfl⟩

theorem TreeStays.trans {A B C : TreeBook} (h : TreeStays A B) (k : TreeStays B C) :
    TreeStays A C := fun z T hT => by
  obtain ⟨T₁, h₁, e₁, f₁⟩ := h z T hT
  obtain ⟨T₂, h₂, e₂, f₂⟩ := k z T₁ h₁
  exact ⟨T₂, h₂, e₂.trans e₁, f₂.trans f₁⟩

theorem counted_stays (A : TreeBook) (t : ℕ) :
    TreeStays A { A with trees := A.trees.modify t fun x => { x with lists := x.lists + 1 } } := by
  intro z T hT
  show ∃ T', (A.trees.modify t fun x => { x with lists := x.lists + 1 })[z]? = some T' ∧ _
  rw [Array.getElem?_modify]
  by_cases c : t = z
  · rw [if_pos c, hT]
    exact ⟨_, rfl, rfl, rfl⟩
  · rw [if_neg c, hT]
    exact ⟨T, rfl, rfl, rfl⟩

theorem openOne_stays {S : Statement} {ft : ℕ} {pos : Positions} {B0 : TreeBook} {t : ℕ}
    {s s' : TreeBook × List _root_.Tw.K2.Col × Array (ℕ × Array ℕ × Array (Array F))}
    (h : openOne S ft pos B0 t s = .ok s') : TreeStays s.1 s'.1 := by
  obtain ⟨tree, tree0, a⟩ := (_root_.Tw.K2.openOne_iff _ _ _ _ _ _ _).1 h
  rw [a.out]
  exact counted_stays _ _

theorem opens_stays {S : Statement} {ft : ℕ} {pos : Positions} {B0 : TreeBook} :
    ∀ (l : List ℕ) (s s' : TreeBook × List _root_.Tw.K2.Col × Array (ℕ × Array ℕ × Array
        (Array F))),
      l.foldlM (fun a t => openOne S ft pos B0 t a) s = .ok s' → TreeStays s.1 s'.1
  | [], s, s', h => by
    cases h
    exact TreeStays.refl _
  | t :: l, s, s', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨m, h1, h2⟩ := VerifiableInference.Desc.bindOk h
    exact (openOne_stays h1).trans (opens_stays l m s' h2)

theorem readOld_stays {i : SwIn} {pos : Positions} {B : TreeBook} {left y}
    (h : readOld i pos = .ok (B, left, y)) : TreeStays i.book B := by
  obtain ⟨places, cols, opened, k⟩ := readOld_inv h
  exact opens_stays _ _ _ k.hOpen

theorem switchBehind_stays {i : SwIn} {o : SwOut} (h : switchBehind i = .ok o) :
    TreeStays i.book o.book := by
  obtain ⟨c, y, S1, S2, S3, rows, b⟩ := switchBehind_inv h
  exact readOld_stays b.hRead

/-- **A yes of kind K2's block: from what the sending returns to the record behind.** -/
theorem yes_stays {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} {s' : S}
    (h : decideWith sendByL8 p s rs gs = .ok s') :
    ∃ (r₁ r₂ : Fmt.RoundView) (x : _root_.Tw.K2.Front), ∃ ids sd an took d', rs = [r₁, r₂] ∧
      _root_.Desc.Plain.sendP (_root_.Desc.Plain.groundG : _root_.Desc.Plain.Ground Unit)
        ⟨p.samples, p.firstTree⟩ false ⟨x.st, s.book, s.roots, [], ()⟩
        (switchNotices x.T x.others) r₁ r₂ = some (ids, sd, an, took, d') ∧
      TreeStays d'.book s'.book := by
  have key : ∀ {f : ReqFrame} {x : _root_.Tw.K2.Front} {r₁ r₂ : Fmt.RoundView} {w : SwOut} {roots : ℕ},
      _root_.Tw.K2.switchE switchBehind (par9 p) sendByL8 ⟨s.st, s.book, s.roots, f, [],
          s.noneWaits⟩
        x r₁ r₂ (flat p gs) = .ok (w, roots) →
      ∃ ids sd an took d', _root_.Desc.Plain.sendP
        (_root_.Desc.Plain.groundG : _root_.Desc.Plain.Ground Unit)
        ⟨p.samples, p.firstTree⟩ false ⟨x.st, s.book, s.roots, [], ()⟩ (switchNotices x.T x.others)
          r₁ r₂ = some (ids, sd, an, took, d') ∧
      TreeStays d'.book w.book := by
    intro f x r₁ r₂ w roots hw
    obtain ⟨y, k⟩ := switchE_inv hw
    obtain ⟨ids, took, d', hs, rfl⟩ := (sendByL8_iff _ _ _ _ _ _ _ _ _).1 k.hSend
    obtain ⟨_, _, sd, an, hx⟩ := (sendOpen_iff _ _ _ _ _ _ _ _ _ _ _).1 hs
    exact ⟨ids, sd, an, took, d', hx, switchBehind_stays k.hBehind⟩
  rcases (stands _ _ _ _ _ _ h) with ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩
  · obtain ⟨r₁, r₂, x, w, roots, S', f, mine, rfl, k⟩ := link_inv hp h
    obtain ⟨ids, sd, an, took, d', h1, h2⟩ := key k.hSwitch
    refine ⟨r₁, r₂, x, ids, sd, an, took, d', rfl, h1, ?_⟩
    rw [k.hOut]
    exact h2
  · obtain ⟨r₁, r₂, a, G, w, roots, rfl, k⟩ := head_inv hp h
    obtain ⟨ids, sd, an, took, d', h1, h2⟩ := key k.hSwitch
    refine ⟨r₁, r₂, _, ids, sd, an, took, d', rfl, h1, ?_⟩
    rw [k.hOut]
    exact h2
  · obtain ⟨r₁, r₂, a, G, w, roots, rfl, k⟩ := finish_inv hp h
    obtain ⟨ids, sd, an, took, d', h1, h2⟩ := key k.hSwitch
    refine ⟨r₁, r₂, _, ids, sd, an, took, d', rfl, h1, ?_⟩
    rw [k.hOut]
    exact h2

theorem laid_other (f : ℕ → OnBytes.Tree → OnBytes.Tree) (idx : ℕ → ℕ) (z : ℕ) :
    ∀ (l : List ℕ) (trees : Array OnBytes.Tree), (∀ i ∈ l, idx i ≠ z) →
      (l.foldl (fun trees i => trees.modify (idx i) (f i)) trees)[z]? = trees[z]?
  | [], _, _ => rfl
  | i :: l, trees, h => by
    rw [List.foldl_cons, laid_other f idx z l _ fun j hj => h j (List.mem_cons_of_mem _ hj),
      Array.getElem?_modify, if_neg (h i List.mem_cons_self)]

/-- **A receiving leaves every older tree as it was.** -/
theorem recv_stays {L : Type} (ft : ℕ) (d d' : _root_.Desc.Plain.DState L)
    (sent : Array OracleNotice) (ids : Array ℕ) (h : Ground.recvP ft d sent = some (ids, d')) :
    TreeStays d.book d'.book := by
  unfold Ground.recvP at h
  split at h
  · obtain ⟨lay, -, e⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨-, rfl⟩ := Prod.mk.inj e
    intro z T hT
    have hz := (Array.getElem?_eq_some_iff.1 hT).1
    refine ⟨T, ?_, rfl, rfl⟩
    show (partsLaid sent lay d.st.oracles.size d.book.trees.size
      (treesSent ft lay.shapes.toList d.roots d.book.trees))[z]? = some T
    unfold partsLaid
    rw [laid_other (fun i x => { x with
        parts := x.parts.push (d.st.oracles.size + i)
        oneList := x.oneList || (sent.getD i default).shape.answers == 0 })
      (fun i => d.book.trees.size + lay.tree.getD i 0) z _ _ fun i _ => by
        show d.book.trees.size + lay.tree.getD i 0 ≠ z
        omega,
      treesSent_old _ _ _ _ z hz]
    exact hT
  · cases h

theorem stays_of_eq {A B : TreeBook} (h : B = A) : TreeStays A B := by
  rw [h]
  exact TreeStays.refl _

theorem call_stays {ft : ℕ} (d d' : _root_.Desc.Plain.DState Unit) (h : H2K.Out.Call ft d d') :
    TreeStays d.book d'.book := by
  cases h with
  | newGroup h => exact stays_of_eq (coreStill_same.newGroup _ _ _ _ _ h).1
  | recv h => exact recv_stays _ _ _ _ _ h
  | admit hs hok hz hr h => exact stays_of_eq (K2.admitP_book h).1
  | join h => exact stays_of_eq (coreStill_same.join _ _ _ _ _ h).1
  | addRow h => exact stays_of_eq (coreStill_same.addRow _ _ _ _ h).1
  | closeLedger h => exact stays_of_eq (coreStill_same.closeLedger _ _ _ h).1
  | spend h => exact stays_of_eq (coreStill_same.spendAsMask _ _ _ h).1
  | begin h =>
    unfold VerifiableInference.Desc.Ground.beginRunP at h
    split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨G, -, -, rfl⟩ := h
      exact TreeStays.refl _
    · cases h
  | count t => exact counted_stays _ _
  | cols l => exact TreeStays.refl _

theorem calls_stays {ft : ℕ} {d d' : _root_.Desc.Plain.DState Unit} (h : H2K.Out.Calls ft d d') :
    TreeStays d.book d'.book := by
  induction h with
  | nil d => exact TreeStays.refl _
  | cons s _ ih => exact (call_stays _ _ s).trans ih

/-- **The proximity test at the first chain's finish.** -/
theorem k12_stays (p : K12.P12) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (h : (K12.atFinish p).decide s rs gs = .ok s') :
    TreeStays s.book s'.book := by
  obtain ⟨o, t', _, _, _, hk, rfl⟩ := K12.Seat.atFinish_ok p s s' rs gs h
  exact calls_stays (H2K.Out.k12_calls p _ t' _ gs hk [] [])

/-- The relation on two records. -/
abbrev TS : S → S → Prop := ByC (fun a b => TreeStays a.book b.book) coreS

theorem ts_same (a b : Core) (h1 : b.book = a.book) (_ : b.roots = a.roots) :
    TreeStays a.book b.book := stays_of_eq h1

theorem coreRecv_tree : CoreRecv 0 fun a b => TreeStays a.book b.book where
  refl := fun _ => TreeStays.refl _
  trans := fun h k => h.trans k
  newGroup := fun d d' c m n h =>
    ts_same _ _ (coreStill_same.newGroup d d' c m n h).1 (coreStill_same.newGroup d d' c m n h).2
  admit := fun d d' o r h =>
    ts_same _ _ (coreStill_same.admit d d' o r h).1 (coreStill_same.admit d d' o r h).2
  join := fun d d' g o k h =>
    ts_same _ _ (coreStill_same.join d d' g o k h).1 (coreStill_same.join d d' g o k h).2
  addRow := fun d d' g r h =>
    ts_same _ _ (coreStill_same.addRow d d' g r h).1 (coreStill_same.addRow d d' g r h).2
  takeMask := fun d d' o n h =>
    ts_same _ _ (coreStill_same.takeMask d d' o n h).1 (coreStill_same.takeMask d d' o n h).2
  closeLedger := fun d d' o h =>
    ts_same _ _ (coreStill_same.closeLedger d d' o h).1 (coreStill_same.closeLedger d d' o h).2
  spendAsMask := fun d d' o h =>
    ts_same _ _ (coreStill_same.spendAsMask d d' o h).1 (coreStill_same.spendAsMask d d' o h).2
  elsewhere := fun d d' m o t h =>
    ts_same _ _ (coreStill_same.elsewhere d d' m o t h).1
      (coreStill_same.elsewhere d d' m o t h).2
  recv := fun d d' sent ids h => recv_stays 0 d d' sent ids h

theorem ts_fn {f : S → Except String S}
    (h : ∀ s t, f s = .ok t → t.book = s.book ∧ t.roots = s.roots) : Fn TS f :=
  fun s t k => ts_same _ _ (h s t k).1 (h s t k).2

theorem k2_tree (p : K2.P2) : Whole TS (K2.codeSwitchKind p : Block S Unit) :=
  ⟨fun s _ _ s' h => by
      obtain ⟨r₁, r₂, x, ids, sd, an, took, d', -, hx, hb⟩ := yes_stays h
      obtain ⟨d₁, h1, e1, -⟩ := K2.sendP_book hx
      have a : TreeStays s.book d₁.book := recv_stays _ _ _ _ _ h1
      rw [e1] at hb
      exact a.trans hb,
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

theorem seatKeeps_tree : SeatKeeps TS where
  refl := fun _ => TreeStays.refl _
  trans := fun _ _ _ h k => h.trans k
  frames := fun _ h => framesOf_core ts_same h
  k1First := fun q gp h0 => firstAtS_core coreRecv_tree q gp h0
  k1Later := fun q gp l p m a h0 => laterAt_core coreRecv_tree q gp l p m a h0
  reads := fun h => whole_core ts_same (readsQuietAt_quiet h)
  k3 := fun c r X cs sh a _ h => whole_core ts_same (theStated_quiet c r X cs sh a h)
  k4 := fun p => whole_core ts_same (blockAtC_quiet p)
  k5 := fun W l g bf _ h => whole_core ts_same (k5AtN_quiet W l g bf h)
  k6 := fun h => whole_core ts_same (seatedClaims_quiet h)
  k7 := fun W l => whole_core ts_same (k7Of_quiet W l)
  k8 := fun p => whole_core ts_same (k8Whole_quiet p)
  closeOf := closeOf_core ts_same
  batch := fun p _ hcl => batch_core ts_same (fun h k => h.trans k) p hcl
  k11 := fun Q => whole_core ts_same (headMerge11_quiet Q)
  k2 := fun p _ => k2_tree p
  front := fun _ => ts_fn fun _ _ h => K2.headFrontQ_book h
  openQ := fun _ _ => ts_fn fun _ _ h => K2.headOpenQ_book h
  finFront := ts_fn fun _ _ h => K2.finishFrontQ_book h
  finBehind := ts_fn fun _ _ h => K2.finishBehindQ_book h

theorem seatBack_tree : SeatBack TS where
  k12 := fun m _ => ⟨fun s rs gs s' h => k12_stays _ s s' rs gs h, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩
  k13M3 := fun p => atM3_core coreRecv_tree.toCoreStill p
  k13M4 := fun _ Q h0 => atM4_core coreRecv_tree _ Q h0

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.yes_stays
#print axioms ProofFile.Honest.K12.AtFile.seatKeeps_tree
#print axioms ProofFile.Honest.K12.AtFile.seatBack_tree
