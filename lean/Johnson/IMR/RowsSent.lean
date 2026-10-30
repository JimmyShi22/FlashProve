-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/RowsSent.lean: THE CARRIED ROWS NAME MESSAGES THAT ARE SENT: at
every state that a fold over a front part of the first chain's flat list returns, at EVERY copy of
the frame that the state holds: at the proof file's seat.
  Low N f: every message that f's carried rows name (singleRowsOracles f.rows) is below N.
  SL: the statement's number of messages does not fall. seatKeeps_sl, seatBack_sl.
  RS s t: SL s t, and for every N that bounds t's number of messages: Low N at every copy in s gives
    Low N at every copy in t. rs_refl, rs_trans, rs_up (from SL and Johnson/IMR/FrAll.lean's FR).
  closing_rs: THE ONE MAKER: the closing lays new rows into the copy in use:
    closeFrame_sent (Johnson/Desc/First/Close/Law/CarriedSent.lean): they name messages of the
    statement behind.
  batch_rs; k13_enter_fr, k13_set_fr, atM3_fr, atM4_fr: the makers behind the last link.
  seatKeeps_rs : SeatKeeps RS; seatBack_rs : SeatBack RS.
  start_low: the first state's carried rows name nothing.
  rows_sent_front: THE TOP, k ≤ the number of entries in front of the sub-protocols behind the last
    link: from the fold's return alone.
  rows_sent: THE TOP, every k: where every entry of the flat list passes its own test on the plan.
  rows_sent_live: so of the copy in use (S.live).
  rows_sent_book_front: of the copy in use, IN THE BOOK's NUMBER OF PLACES, at the cuts of
    rows_sent_front (Johnson/IMR/WalkGivesAt.lean's open_has: there the two numbers are one).
  rowsSent_field: the field of the list of facts along the fold, in that field's letters, general in
    Rch and at_: under two premises on Rch: the fold's form; and "the book has as many places as
    the statement has messages" (hBook).
IN rows_sent AND rows_sent_live THE BOUND IS THE STATEMENT's NUMBER OF MESSAGES, not the book's
number of places: that the two are one behind the last link is not shown here.
OBJECT: ProofFile.onlineDescription's value. USER: the list of facts along the fold (field "rowsSent").
The premises are laws' premises: that a fold returns is shown of no proof here. No soundness.
-/
import Johnson.IMR.FrK2
import Johnson.IMR.CodesSeat
import Johnson.IMR.OpenFlat
import Johnson.IMR.WalkGivesAt
import Johnson.Desc.First.Close.Law.CarriedSent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Ground (groundKeeps_grows)
open VerifiableInference.Desc.K9 (atS batch adds drawAlone)
open ProofFile (Pub Cl)

/-- Every message that the frame's carried rows name is below N. -/
def Low (N : Nat) (f : ReqFrame) : Prop := ∀ o ∈ singleRowsOracles f.rows, o < N

theorem carr_low (N : Nat) : Carr (Low N) := fun f f' h e => by
  unfold Low
  rw [e]
  exact h

/-- The statement's number of messages does not fall. -/
abbrev SL : S → S → Prop := ByS fun T T' => T.oracles.size ≤ T'.oracles.size

theorem size_of_some {α β : Type} {X : Array α} {Y : Array β}
    (h : ∀ (i : Nat) x, X[i]? = some x → ∃ y, Y[i]? = some y) : X.size ≤ Y.size := by
  by_contra hc
  have hlt : Y.size < X.size := by omega
  obtain ⟨y, hy⟩ := h Y.size X[Y.size] (Array.getElem?_eq_getElem hlt)
  rw [Array.getElem?_eq_none (Nat.le_refl _)] at hy
  cases hy

theorem grows_size {T T' : Statement} (g : Grows T T') : T.oracles.size ≤ T'.oracles.size :=
  size_of_some fun i x hx => by
    obtain ⟨x', h', -⟩ := g.2.2 i x hx
    exact ⟨x', h'⟩

theorem batch_sl (p : K9.Where) {claims : S → Except String (List Claim × S)}
    (hcl : FnCl SL claims) : Whole SL (K9.batch K9.atS p claims) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [batch] at h
  obtain ⟨t₁, h1, h⟩ := bindE h
  have a1 : SL s t₁ := drawAlone_by (R := fun T T' => T.oracles.size ≤ T'.oracles.size)
    (fun _ => Nat.le_refl _) p s rs gs t₁ h1
  have a2 : SL t₁ s' := adds_by p p.piece "the segment's" hcl t₁ [] [] s' h
  exact Nat.le_trans a1 a2

theorem seatKeeps_sl : SeatKeeps SL :=
  (seatKeeps_grows k2Grows).mono (fun _ _ g => grows_size g) (fun _ => Nat.le_refl _)
    (fun _ _ _ h k => Nat.le_trans h k) batch_sl

theorem seatBack_sl : SeatBack SL where
  k12 := fun m hp => ⟨fun s rs gs s' h => by
      obtain ⟨o, t', -, -, -, hk, rfl⟩ := K12.Seat.atFinish_ok _ s s' rs gs h
      have hp' := atFinish_planOk hp
      have K := (H2K.Out.k12_out _ (H2K.JointK.early_of_planOk _ hp')
        (H2K.JointK.answers_of_planOk _ hp') _ t' rs gs hk).shapes
      exact size_of_some fun i x hx => by
        obtain ⟨x', h', -⟩ := K i x hx
        exact ⟨x', h'⟩,
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  k13M3 := fun p => ⟨fun s rs gs s' h => grows_size (K13.atM3_grows p s rs gs s' h),
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  k13M4 := fun p P _ => ⟨fun s rs gs s' h => grows_size (K13.atM4_keeps groundKeeps_grows.quiet p _
      (K1.Rel.sendAtS_keeps groundKeeps_grows P) s rs gs s' h),
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

/-- **THE RELATION.** -/
def RS (s t : S) : Prop :=
  SL s t ∧ ∀ N, t.st.oracles.size ≤ N → EachF (Low N) s → EachF (Low N) t

theorem rs_refl (s : S) : RS s s := ⟨Nat.le_refl _, fun _ _ h => h⟩

theorem rs_trans (a b c : S) (h : RS a b) (k : RS b c) : RS a c :=
  ⟨Nat.le_trans h.1 k.1, fun N hN x => k.2 N hN (h.2 N (Nat.le_trans k.1 hN) x)⟩

theorem rs_up {s t : S} (h1 : SL s t) (h2 : FR s t) : RS s t :=
  ⟨h1, fun N _ x => h2 _ (carr_low N) x⟩

theorem whole_rs {C : Type} {b : Block S C} (W₁ : Whole SL b) (W₂ : Whole FR b) : Whole RS b :=
  whole_mono (fun _ _ h => rs_up h.1 h.2) (whole_and W₁ W₂)

theorem fn_rs {f : S → Except String S} (h1 : Fn SL f) (h2 : Fn FR f) : Fn RS f :=
  fun s t k => rs_up (h1 s t k) (h2 s t k)

/-- **THE CLOSING.** -/
theorem closing_low (P : Close.Par) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K9.closing (Cl := Unit) P).decide s rs gs = .ok s') (N : Nat)
    (hN : s'.st.oracles.size ≤ N) (R : EachF (Low N) s) : EachF (Low N) s' := by
  obtain ⟨r, hr, rfl⟩ := Keeps.emap_ok h
  obtain ⟨x, hx, rfl⟩ := Keeps.emap_ok hr
  have hN' : x.2.oracles.size ≤ N := hN
  have hf : Low N x.1 := fun o ho => Nat.lt_of_lt_of_le (Close.closeFrame_sent hx o ho) hN'
  exact ef_putLive (c := { s.live with frame := x.1 }) R hf

theorem closeOf_rs (p : K9.Where) (P : Close.Par) :
    ∀ b ∈ K9.closeOf (Cl := Unit) p P, Whole RS b := by
  intro b hb
  have W₁ := seatKeeps_sl.closeOf p P b hb
  unfold K9.closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact whole_rs W₁ (oneEquation_fr p)
  · exact ⟨fun s rs gs s' h => ⟨W₁.1 s rs gs s' h, fun N hN R => closing_low P h N hN R⟩,
      (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  · exact whole_rs W₁ (shut_fr p _)

/-- **THE BATCHING.** -/
theorem batch_rs (p : K9.Where) {claims : S → Except String (List Claim × S)}
    (hcl : FnCl RS claims) : Whole RS (K9.batch K9.atS p claims) := by
  have W₁ := batch_sl p (claims := claims) fun s y h => (hcl s y h).1
  refine ⟨fun s rs gs s' h => ⟨W₁.1 s rs gs s' h, fun N hN R => ?_⟩, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩
  simp only [batch] at h
  obtain ⟨t₁, h1, h⟩ := bindE h
  have R1 : EachF (Low N) t₁ := drawAlone_fr p s rs gs t₁ h1 _ (carr_low N) R
  simp only [adds] at h
  obtain ⟨s₀, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨x, hx, h⟩ := bindE h
  obtain ⟨q, hq, h⟩ := bindE h
  obtain ⟨F, _, h⟩ := bindE h
  cases h
  obtain ⟨g1, g2⟩ := atS_get (there_some hq)
  have hN' : q.d.st.oracles.size ≤ N := hN
  rw [g2] at hN'
  have R2 : EachF (Low N) x.2 := (hcl t₁ x hx).2 N hN' R1
  exact atS_set_fr R2 (link_fr R2 g1)

theorem seatKeeps_rs : SeatKeeps RS where
  refl := rs_refl
  trans := rs_trans
  frames := fun hB h f hf =>
    ⟨fn_rs (seatKeeps_sl.frames hB h f hf).1 (framesOf_fr h f hf).1,
      fn_rs (seatKeeps_sl.frames hB h f hf).2.1 (framesOf_fr h f hf).2.1,
      fn_rs (seatKeeps_sl.frames hB h f hf).2.2 (framesOf_fr h f hf).2.2⟩
  k1First := fun q gp h0 => whole_rs (seatKeeps_sl.k1First q gp h0) (firstAtS_fr q gp)
  k1Later := fun q gp l p m a h0 =>
    whole_rs (seatKeeps_sl.k1Later q gp l p m a h0) (laterAt_fr q gp l p m a)
  reads := fun h => whole_rs (seatKeeps_sl.reads h) (whole_fr (readsQuietAt_quiet h))
  k3 := fun c r X cs' sh' a _ h =>
    whole_rs (seatKeeps_sl.k3 c r X cs' sh' a h) (whole_fr (theStated_quiet c r X cs' sh' a h))
  k4 := fun p => whole_rs (seatKeeps_sl.k4 p) (whole_fr (blockAtC_quiet p))
  k5 := fun W l g bf _ h =>
    whole_rs (seatKeeps_sl.k5 W l g bf h) (whole_fr (k5AtN_quiet W l g bf h))
  k6 := fun h => whole_rs (seatKeeps_sl.k6 h) (whole_fr (seatedClaims_quiet h))
  k7 := fun W l => whole_rs (seatKeeps_sl.k7 W l) (whole_fr (k7Of_quiet W l))
  k8 := fun p => whole_rs (seatKeeps_sl.k8 p) (whole_fr (k8Whole_quiet p))
  k11 := fun P => whole_rs (seatKeeps_sl.k11 P) (whole_fr (headMerge11_quiet P))
  closeOf := closeOf_rs
  batch := fun p _ hf => batch_rs p hf
  k2 := fun p h0 => whole_rs (seatKeeps_sl.k2 p h0) (K2.k2_rf p)
  front := fun tl => fn_rs (seatKeeps_sl.front tl) (K2.headFrontQ_rf tl)
  openQ := fun P hP => fn_rs (seatKeeps_sl.openQ P hP) (K2.headOpenQ_rf P)
  finFront := fn_rs seatKeeps_sl.finFront K2.finishFrontQ_rf
  finBehind := fn_rs seatKeeps_sl.finBehind K2.finishBehindQ_rf

/-! ## Behind the last link -/

theorem k13_enter_fr {t t' : S} (h : K13.atS.enter t = some t') : FR t t' := fun _ _ R => by
  simp only [K13.atS] at h
  split at h
  · cases h
    exact ef_enterMem R
  · cases h

theorem k13_set_fr {t : S} {p : K13.Part} (q : K13.Part) (h : K13.atS.get? t = some p) :
    FR t (K13.atS.set t q) := fun _ _ R => by
  simp only [K13.atS] at h ⊢
  split at h
  · rename_i o ho
    refine ef_same R fun f hf => ?_
    have hf' : f ∈ [t.check.frame] := hf
    unfold framesIn
    rw [ho]
    exact hf'
  · cases h

theorem frontB_fr {C : Type} (p : K13.Where) : Decides FR (K13.frontB (Cl := C) K13.atS p) := by
  intro t _ _ t' h
  obtain ⟨t₁, h1, h⟩ := ChainEnd.bind_ok h
  obtain ⟨_, _, h⟩ := ChainEnd.bind_ok h
  obtain ⟨_, _, h⟩ := ChainEnd.bind_ok h
  have := K13.pure_ok h
  subst this
  exact k13_enter_fr (K13.there_ok h1)

theorem battB_fr {C : Type} (p : K13.Where) : Decides FR (K13.claimCombinationBlock (Cl := C) K13.atS p) := by
  intro t rs _ t' h
  obtain ⟨s, hs, h⟩ := ChainEnd.bind_ok h
  obtain ⟨_, _, h⟩ := ChainEnd.bind_ok h
  obtain ⟨o, ho, h⟩ := ChainEnd.bind_ok h
  have := K13.pure_ok h
  subst this
  exact k13_set_fr _ (K13.part_ok hs)

theorem quietB_fr {C : Type} (p : K13.Where) : Decides FR (K13.quietB (Cl := C) K13.atS p) := by
  intro t _ _ t' h
  obtain ⟨s, hs, h⟩ := ChainEnd.bind_ok h
  obtain ⟨_, _, h⟩ := ChainEnd.bind_ok h
  obtain ⟨_, _, h⟩ := ChainEnd.bind_ok h
  have := K13.pure_ok h
  subst this
  exact k13_set_fr _ (K13.part_ok hs)

theorem rowsB_fr {C : Type} (p : K13.Where) : Decides FR (K13.rowsB (Cl := C) K13.atS p) := by
  intro t _ _ t' h
  obtain ⟨s, hs, h⟩ := ChainEnd.bind_ok h
  obtain ⟨_, _, h⟩ := ChainEnd.bind_ok h
  obtain ⟨o, ho, h⟩ := ChainEnd.bind_ok h
  have := K13.pure_ok h
  subst this
  exact k13_set_fr _ (K13.part_ok hs)

theorem atM3_fr {C : Type} (p : K13.Where) : Decides FR (K13.atM3 (Cl := C) p) :=
  fun s rs gs s' h =>
    Keeps.andThen_decides _ ef_trans' "K13: the members' batching"
      ((K13.frontB K13.atS p).andThen "the front and the batching" (K13.claimCombinationBlock K13.atS p))
      (K13.quietB K13.atS p)
      (Keeps.andThen_decides _ ef_trans' "the front and the batching" _ _
        (frontB_fr p) (battB_fr p))
      (quietB_fr p) s rs gs s' h

theorem atM4_fr {C : Type} (p : K13.Where) (commitW : Block S C) (hW : Decides FR commitW) :
    Decides FR (K13.atM4 p commitW) :=
  Keeps.andThen_decides _ ef_trans' _ _ _ hW (rowsB_fr p)

theorem seatBack_rs : SeatBack RS where
  k12 := fun m hp => whole_rs (seatBack_sl.k12 m hp) ⟨fun s rs gs s' h _ _ R => by
      obtain ⟨o, t', -, -, -, -, rfl⟩ := K12.Seat.atFinish_ok _ s s' rs gs h
      exact ef_same R fun _ hm => hm,
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  k13M3 := fun p => whole_rs (seatBack_sl.k13M3 p)
    ⟨atM3_fr p, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  k13M4 := fun p P h0 => whole_rs (seatBack_sl.k13M4 p P h0)
    ⟨atM4_fr p _ (sendAtS_fr P).1, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

/-! ## The start, and the tops -/

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **The first state's carried rows name nothing.** -/
theorem start_low (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (p : ProofFile.InstPub) (N : Nat) :
    EachF (Low N) (ProofFile.startS Z p) := by
  have e : EachF (Low N) Z.s₀ := by
    have k := pub_start hZ
    unfold S.startP at k
    split at k
    · rw [← Option.some.inj k]
      intro f hf
      have e : f = (S.firstRecord Z.first.codes Z.first.shape Z.first.layout).check.frame := by
        simpa [framesIn, S.firstRecord] using hf
      rw [e]
      intro o ho
      simp [S.firstRecord, singleRowsOracles] at ho
    · cases k
  unfold ProofFile.startS
  dsimp only
  split
  · exact ef_same e fun _ h => h
  · intro f hf
    have e' : f = S.blank.check.frame := by simpa [framesIn, S.blank, S.start] using hf
    rw [e']
    intro o ho
    simp [S.blank, S.start, singleRowsOracles] at ho

/-- **IN FRONT OF THE SUB-PROTOCOLS BEHIND THE LAST LINK: FROM THE FOLD's RETURN ALONE.** -/
theorem rows_sent_front (O : IM.Open o pol lay KL F Z Bs base c A B) {k : Nat}
    (hk : k ≤ (frontOf c).length) {p : ProofFile.InstPub} {R : List Fmt.RoundView}
    {C : List VerifiableInference.Desc.OpenedColumn}
    {r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn}
    (h : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok r) :
    ∀ f ∈ framesIn r.1, ∀ x ∈ singleRowsOracles f.rows, x < r.1.st.oracles.size :=
  (open_fold seatKeeps_rs O trivial (fun _ _ _ => trivial) hk h).2 _ (Nat.le_refl _)
    (start_low O.pub p _)

/-- **AT EVERY CUT**, where every entry of the flat list passes its own test on the plan. -/
theorem rows_sent (O : IM.Open o pol lay KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (k : Nat) {p : ProofFile.InstPub} {R : List Fmt.RoundView}
    {C : List VerifiableInference.Desc.OpenedColumn}
    {r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn}
    (h : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok r) :
    ∀ f ∈ framesIn r.1, ∀ x ∈ singleRowsOracles f.rows, x < r.1.st.oracles.size :=
  (open_fold_all seatKeeps_rs seatBack_rs O trivial (fun _ _ _ => trivial) hp k h).2 _
    (Nat.le_refl _) (start_low O.pub p _)

/-- **SO OF THE COPY IN USE.** -/
theorem rows_sent_live (O : IM.Open o pol lay KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) (k : Nat) {p : ProofFile.InstPub} {R : List Fmt.RoundView}
    {C : List VerifiableInference.Desc.OpenedColumn}
    {r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn}
    (h : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok r) :
    ∀ x ∈ singleRowsOracles r.1.live.frame.rows, x < r.1.st.oracles.size :=
  EachF.live (Φ := Low r.1.st.oracles.size) (rows_sent O hp k h)

/-- **IN THE BOOK's NUMBER OF PLACES, IN FRONT OF THE SUB-PROTOCOLS BEHIND THE LAST LINK: FROM THE
FOLD's RETURN ALONE.** -/
theorem rows_sent_book_front (O : IM.Open o pol lay KL F Z Bs base c A B) {k : Nat}
    (hk : k ≤ (frontOf c).length) {p : ProofFile.InstPub} {R : List Fmt.RoundView}
    {C : List VerifiableInference.Desc.OpenedColumn}
    {r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn}
    (h : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok r) :
    ∀ x ∈ singleRowsOracles r.1.live.frame.rows, x < r.1.book.place.size := by
  rw [open_has O hk h]
  exact EachF.live (Φ := Low r.1.st.oracles.size) (rows_sent_front O hk h)

/-- **THE FIELD "rowsSent"**, in the letters of Johnson/Desc/First/FoldFacts.lean's field at
P := ProofFile.InstPub (read at that file's text: the same but for one bound letter; this file does not
import it, so Lean has not compared the two). General in Rch and at_, with two premises on Rch:
what is reached is the return of a fold over the flat list's first k entries from ProofFile.startS Z; and
there the book has as many places as the statement has messages. The fence "no mark" is not
spent. -/
theorem rowsSent_field (O : IM.Open o pol lay KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {X : Type}
    (Rch : Nat → X → Prop) (at_ : X → ProofFile.InstPub × S)
    (hRch : ∀ k a, Rch k a → ∃ rs cols r q,
      foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z (at_ a).1) rs cols = .ok ((at_ a).2, r, q))
    (hBook : ∀ k a, Rch k a → (at_ a).2.book.place.size = (at_ a).2.st.oracles.size) :
    ∀ k a, Rch k a → (at_ a).2.failed = none →
      ∀ x ∈ OnBytes.singleRowsOracles (at_ a).2.live.frame.rows, x < (at_ a).2.book.place.size :=
  fun k a hr _ x hx => by
    obtain ⟨rs, cols, r, q, f⟩ := hRch k a hr
    rw [hBook k a hr]
    exact rows_sent_live O hp k f x hx

end

#print axioms seatKeeps_rs
#print axioms seatBack_rs
#print axioms start_low
#print axioms rows_sent_front
#print axioms rows_sent
#print axioms rows_sent_live
#print axioms rows_sent_book_front
#print axioms rowsSent_field

end Meaning.K2
