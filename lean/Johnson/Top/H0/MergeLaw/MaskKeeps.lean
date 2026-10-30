-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/MaskKeeps.lean: which accepting steps leave what the test `maskMsgB`
(MaskFront.lean) reads of the open segment's frame. A relation on two states of the verifier, and
theorems with their proofs.

Why. `maskMsgB O` is meant to be made true where the output head's segment is opened
(MaskMaker.lean), and is asked in front of the merge of the claims on the committed table, some
sub-protocols later. Of each sub-protocol between the two it is wanted that its accepting step
leaves the test's accept. One relation says what is left; it is shown here of every sub-protocol
whose accepting step is quiet (`Quiet`, Johnson/Goal/Meaning/RecQuiet.lean), and of a segment's
later sending.

Main names:
  `SegStays d s s'`: the statement behind has d oracle messages more; and where a segment is open in
    front, one is open behind, with the same number; its frame's fields next, link and shape are as
    they were; and the frame's list of the segment's own messages has grown at its end alone.
  `segStays_refl`, `SegStays.trans`: it holds of a state and itself at 0; two in a row add up.
  `maskOracle_stays`, `SegStays.mask`: WHAT IT IS FOR: `maskMsgB O` in front gives `maskMsgB O`
    behind.
  `SegStays.numbers`: where the frame's number of the segment is the context's in front, it is
    behind. (No file beside this one calls it yet.)
  `not_segStays_closed`: NEGATIVE TEST: a step from an open segment to a state between two segments
    has the relation at no d.
  `ctxOf_link`, `segStays_of_quiet`, `decides_of_quietD`, `decides_of_quiet`: a quiet step has it at
    0. `decides_andThen`: two sub-protocols as one.
  `K1.commitOwn_frameAny`, `K1.commitAtS_frameAny`: a later sending's accepting step, at whatever
    rounds: the frame behind is the frame in front with its moment one higher and some numbers
    behind its list of own messages. They follow `commitOwn_frame` and `commitAtS_frame`
    (Johnson/Desc/K1/Law/FrameAtLater.lean), which speak at two rounds and name the numbers.
  `commitAtS_stays`, `laterAt_stays`: so a later sending has the relation, at the number of its
    messages.
  `theStated_stays`, `seatedClaims_stays`, `k8Whole_stays`: three makers of sub-protocols (the
    lookup; the output head's own rounds; the smallness test), by the quiet steps that
    Johnson/Goal/Meaning/RecSeated.lean shows of them.

Limits. `Decides (SegStays d) b` asks nothing of a sub-protocol b that never accepts: for such a b
it holds at every d, so there "at the number of its messages" fixes no number (a later sending
without a list of arrays, or at a segment or moment at which no frame stands, never accepts; where a
maker gives no sub-protocol, its theorem's premise cannot be met). No accepting step of any of these
makers' sub-protocols is exhibited here. That the IOP as written in Lean holds these makers'
sub-protocols between the opening of the output head's segment and the merge is not said here.
Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.MaskFront
import Johnson.Goal.Meaning.RecSeated
import Johnson.Desc.K1.Law.FrameAtLater
import Johnson.Desc.K1.Law.GoodSendSize

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First.Send (joinOwnP)
open VerifiableInference.Desc.First (S)

variable {Cl : Type}

/-- A later sending's accepting step, at whatever rounds: the context's frame behind. -/
theorem commitOwn_frameAny (P : Par) (link moment : Nat) (arrays : Option (List Nat))
    (s s' : Owing (L3.St (DState Unit))) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitOwn P link moment arrays : Block _ Cl).decide s rs gs = .ok s') :
    ∃ ids : Array Nat, s'.held.L.check.frame =
        { s.held.L.check.frame with
          moment := s.held.L.check.frame.moment + 1
          own := s.held.L.check.frame.own ++ ids } := by
  unfold commitOwn at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · obtain ⟨t, ht, rfl⟩ := (map_ok _ _ _).1 h
      unfold L3.commitStep at ht
      obtain ⟨_, _, ht⟩ := (bind_ok _ _ _).1 ht
      obtain ⟨⟨check, w⟩, h2, ht⟩ := (bind_ok _ _ _).1 ht
      obtain ⟨⟨L, F⟩, h3, ht⟩ := (bind_ok _ _ _).1 ht
      have e : ({ s.held with L := L, F := F, w := w } : L3.St (DState Unit)) = t := by
        simpa [pure, Except.pure] using ht
      obtain ⟨ids, d₁, f', _, a2, a3⟩ := laterOwn_ok P s.owed _ _ _ _ _ h2
      have hf : f' = _ := joinOwnP_frame _ _ _ _ _ _ a2
      unfold L3.commitBehind at h3
      obtain ⟨F₁, _, h3⟩ := (bind_ok _ _ _).1 h3
      split at h3
      · have e3 := (Prod.mk.inj (Except.ok.inj h3)).1
        refine ⟨ids, ?_⟩
        rewrite [← e, ← e3, a3, hf]
        rfl
      · cases h3
  · cases h

/-- The same at the verifier's state. -/
theorem commitAtS_frameAny (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    ∃ (L L' : LinkCtx) (ids : Array Nat), s.link? = some L ∧ s'.link? = some L' ∧
      L'.link = L.link ∧
      L'.check.frame =
        { L.check.frame with
          moment := L.check.frame.moment + 1
          own := L.check.frame.own ++ ids } := by
  unfold commitAtS at h
  dsimp only at h
  split at h
  · rename_i L F tl hL _ _
    obtain ⟨y, hy, rfl⟩ := (map_ok _ _ _).1 h
    obtain ⟨ids, e⟩ := commitOwn_frameAny P link moment arrays _ y rs gs hy
    exact ⟨L, y.held.L, ids, hL, link_put s _ L _ _ hL,
      commitOwn_link P link moment arrays _ y rs gs hy, e⟩
  · cases h

end VerifiableInference.Desc.K1

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes
open OnBytes.Model (LinkCtx)
open VerifiableInference.Desc.K9L (maskOracle)
open VerifiableInference.Desc.Keeps (Decides Whole)

/-! ## The relation -/

/-- **What an accepting step leaves of the open segment's frame.** d: how many oracle messages the
step adds to the statement's. -/
def SegStays (d : ℕ) (s s' : S) : Prop :=
  s'.st.oracles.size = s.st.oracles.size + d ∧
    ∀ L, s.link? = some L → ∃ L', s'.link? = some L' ∧ L'.link = L.link ∧
      L'.check.frame.next = L.check.frame.next ∧ L'.check.frame.link = L.check.frame.link ∧
      L'.check.frame.shape = L.check.frame.shape ∧
      ∃ more, L'.check.frame.own = L.check.frame.own ++ more

/-- It holds of a state and itself, at no new message. -/
theorem segStays_refl (s : S) : SegStays 0 s s :=
  ⟨(Nat.add_zero _).symm, fun L hL => ⟨L, hL, rfl, rfl, rfl, rfl, #[], by simp⟩⟩

/-- Two in a row: what they add adds up. -/
theorem SegStays.trans {d e : ℕ} {a b c : S} (h : SegStays d a b) (k : SegStays e b c) :
    SegStays (d + e) a c := by
  refine ⟨by rw [k.1, h.1, Nat.add_assoc], fun L hL => ?_⟩
  obtain ⟨L₁, h1, l1, n1, k1, s1, m1, o1⟩ := h.2 L hL
  obtain ⟨L₂, h2, l2, n2, k2, s2, m2, o2⟩ := k.2 L₁ h1
  exact ⟨L₂, h2, l2.trans l1, n2.trans n1, k2.trans k1, s2.trans s1, m1 ++ m2, by
    rw [o2, o1, Array.append_assoc]⟩

/-- The answer of `maskOracle` stays where the frame's next, link and shape stay and its list of own
messages grows at its end alone. -/
theorem maskOracle_stays {f f' : ReqFrame} {more : Array ℕ} {o : ℕ} (hn : f'.next = f.next)
    (hl : f'.link = f.link) (hs : f'.shape = f.shape) (ho : f'.own = f.own ++ more)
    (h : maskOracle f = some o) : maskOracle f' = some o := by
  obtain ⟨h1, m, hm, hg⟩ := (maskOracle_iff f o).1 h
  obtain ⟨hlt, _⟩ := Array.getElem?_eq_some_iff.1 hg
  refine (maskOracle_iff f' o).2 ⟨hn.trans h1, m, ?_, ?_⟩
  · rw [hs, hl]
    exact hm
  · rw [ho, Array.getElem?_append_left hlt]
    exact hg

/-- **Where the test accepts in front, at O, it accepts behind, at O.** -/
theorem SegStays.mask {d O : ℕ} {s s' : S} (h : SegStays d s s') (hm : maskMsgB O s = true) :
    maskMsgB O s' = true := by
  obtain ⟨L, hL, ho⟩ := maskMsgB_gives hm
  obtain ⟨L', hL', _, hn, hl, hs, more, hown⟩ := h.2 L hL
  exact maskMsgB_of hL' (maskOracle_stays hn hl hs hown ho)

/-- Where the frame's number of the segment is the context's in front, it is behind. -/
theorem SegStays.numbers {d : ℕ} {s s' : S} (h : SegStays d s s') {L : LinkCtx}
    (hL : s.link? = some L) (e : L.check.frame.link = L.link) :
    ∀ L', s'.link? = some L' → L'.check.frame.link = L'.link := by
  intro L' hL'
  obtain ⟨L₁, h1, l1, _, k1, _⟩ := h.2 L hL
  obtain rfl : L₁ = L' := Option.some.inj (h1.symm.trans hL')
  rw [k1, l1]
  exact e

/-- NEGATIVE TEST: a step from an open segment to a state between two segments has the relation at
no d. -/
theorem not_segStays_closed {d : ℕ} {s s' : S} {L : LinkCtx} (hL : s.link? = some L)
    (h : s'.here = .between) : ¬ SegStays d s s' := by
  intro k
  obtain ⟨L', hL', -⟩ := k.2 L hL
  simp [S.link?, h] at hL'

/-! ## A quiet step -/

/-- What `ctxOf` holds of an open segment's context. -/
theorem ctxOf_link {s : S} {L : LinkCtx} (h : s.link? = some L) :
    ∃ t, (_root_.Meaning.K2.ctxOf s).2 = some (t, L.check.rows, L.link, L.arrayOf) := by
  cases e : s.here with
  | between => simp [S.link?, e] at h
  | lay a =>
    obtain rfl : a.L = L := by simpa [S.link?, e] using h
    exact ⟨0, by simp [_root_.Meaning.K2.ctxOf, e]⟩
  | att a =>
    obtain rfl : a.L = L := by simpa [S.link?, e] using h
    exact ⟨0, by simp [_root_.Meaning.K2.ctxOf, e]⟩
  | head a =>
    cases ho : a.opened with
    | false => simp [S.link?, e, ho] at h
    | true =>
      obtain rfl : a.L = L := by simpa [S.link?, e, ho] using h
      exact ⟨2, by simp [_root_.Meaning.K2.ctxOf, e, ho]⟩
  | fin a => simp [S.link?, e] at h
  | mem a => simp [S.link?, e] at h

/-- **A quiet step has the relation, at no new message.** -/
theorem segStays_of_quiet {s s' : S} (q : _root_.Meaning.K2.Quiet s s') : SegStays 0 s s' := by
  refine ⟨by rw [q.1.1, Nat.add_zero], fun L hL => ?_⟩
  have ho := q.open
  unfold _root_.Meaning.K2.openOf at ho
  rw [hL] at ho
  cases hL' : s'.link? with
  | none =>
    rw [hL'] at ho
    simp at ho
  | some L' =>
    rw [hL'] at ho
    have e : (L'.check, L'.moments) = (L.check, L.moments) := Option.some.inj ho
    have ec : L'.check = L.check := congrArg Prod.fst e
    obtain ⟨t, ht⟩ := ctxOf_link hL
    obtain ⟨t', ht'⟩ := ctxOf_link hL'
    rw [q.ctx, ht] at ht'
    have el : L'.link = L.link := (congrArg (fun x => x.2.2.1) (Option.some.inj ht')).symm
    exact ⟨L', rfl, el, by rw [ec], by rw [ec], by rw [ec], #[], by
      rw [ec, Array.append_empty]⟩

variable {Cl : Type}

/-- A sub-protocol whose accepting steps are quiet has the relation at no new message. -/
theorem decides_of_quietD {b : Block S Cl} (W : Decides _root_.Meaning.K2.Quiet b) :
    Decides (SegStays 0) b := fun s rs gs s' h => segStays_of_quiet (W s rs gs s' h)

/-- The same from the form in which the makers' files have it: of that form the first part alone is
spent. -/
theorem decides_of_quiet {b : Block S Cl} (W : Whole _root_.Meaning.K2.Quiet b) :
    Decides (SegStays 0) b := decides_of_quietD W.1

/-- Two sub-protocols as one: what they add adds up. -/
theorem decides_andThen {d e : ℕ} {p q : Block S Cl} (hp : Decides (SegStays d) p)
    (hq : Decides (SegStays e) q) (n : String) : Decides (SegStays (d + e)) (p.andThen n q) := by
  intro s rs gs s' h
  have h' : (p.decide s (rs.take p.rounds.length) (gs.take p.openings)).bind
      (fun t => q.decide t (rs.drop p.rounds.length) (gs.drop p.openings)) = .ok s' := h
  obtain ⟨t, h1, h2⟩ := Keeps.ebind_ok h'
  exact (hp _ _ _ _ h1).trans (hq _ _ _ _ h2)

/-! ## A segment's later sending -/

/-- **A later sending has the relation, at the number of its messages.** -/
theorem commitAtS_stays (P : K1.Par) (link moment : ℕ) (arrays : Option (List ℕ)) :
    Decides (SegStays (K1.shapesOf P).length) (K1.commitAtS (Cl := Cl) P link moment arrays) := by
  intro s rs gs s' h
  refine ⟨K1.grows_commitAtS P link moment arrays s s' rs gs h, fun L₀ hL₀ => ?_⟩
  obtain ⟨L, L', ids, hL, hL', el, e⟩ := K1.commitAtS_frameAny P link moment arrays s s' rs gs h
  obtain rfl : L = L₀ := Option.some.inj (hL.symm.trans hL₀)
  exact ⟨L', hL', el, by rw [e], by rw [e], by rw [e], ids, by rw [e]⟩

/-- The same at the maker of a segment's later sending. -/
theorem laterAt_stays (q : Params.First) (gp : _root_.Desc.Plain.GPar) (link piece moment : ℕ)
    (arrays : Option (List ℕ)) :
    Decides (SegStays (K1.shapesOf (K1.parLater q gp link piece moment)).length)
      (K1.laterAt (Cl := Cl) q gp link piece moment arrays) :=
  commitAtS_stays _ link moment arrays

/-! ## Three makers of sub-protocols with quiet steps -/

/-- The lookup's maker. -/
theorem theStated_stays (claim : OnBytes.Model.Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : OnBytes.Model.Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place)
    {b : Block S Cl} (h : K3.theStated claim readers X codes shape a = some b) :
    Decides (SegStays 0) b :=
  decides_of_quiet (_root_.Meaning.K2.theStated_quiet claim readers X codes shape a h)

/-- The maker of the output head's own rounds. -/
theorem seatedClaims_stays {W : OnBytes.Model.Verify.Public} {l : ℕ} {before : List (ℕ × ℕ)}
    {b : Block S Claim} (h : Kinds.Head.seatedClaims W l before = some b) :
    Decides (SegStays 0) b :=
  decides_of_quiet (_root_.Meaning.K2.seatedClaims_quiet h)

/-- The smallness test's maker. -/
theorem k8Whole_stays (p : K8.ParW) : Decides (SegStays 0) (K8.whole p) :=
  decides_of_quiet (_root_.Meaning.K2.k8Whole_quiet p)

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.K1.commitOwn_frameAny
#print axioms VerifiableInference.Desc.K1.commitAtS_frameAny
#print axioms VerifiableInference.Desc.First.MergeLaw.segStays_refl
#print axioms VerifiableInference.Desc.First.MergeLaw.SegStays.trans
#print axioms VerifiableInference.Desc.First.MergeLaw.maskOracle_stays
#print axioms VerifiableInference.Desc.First.MergeLaw.SegStays.mask
#print axioms VerifiableInference.Desc.First.MergeLaw.SegStays.numbers
#print axioms VerifiableInference.Desc.First.MergeLaw.ctxOf_link
#print axioms VerifiableInference.Desc.First.MergeLaw.segStays_of_quiet
#print axioms VerifiableInference.Desc.First.MergeLaw.decides_of_quietD
#print axioms VerifiableInference.Desc.First.MergeLaw.decides_of_quiet
#print axioms VerifiableInference.Desc.First.MergeLaw.not_segStays_closed
#print axioms VerifiableInference.Desc.First.MergeLaw.commitAtS_stays
#print axioms VerifiableInference.Desc.First.MergeLaw.laterAt_stays
#print axioms VerifiableInference.Desc.First.MergeLaw.theStated_stays
#print axioms VerifiableInference.Desc.First.MergeLaw.seatedClaims_stays
#print axioms VerifiableInference.Desc.First.MergeLaw.k8Whole_stays
#print axioms VerifiableInference.Desc.First.MergeLaw.decides_andThen
