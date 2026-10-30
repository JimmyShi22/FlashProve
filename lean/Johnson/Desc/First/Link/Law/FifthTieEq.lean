-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FifthTieEq.lean: "WHAT RIDES" AT THE ONE EQUATION's SUB-PROTOCOL, AT THE
COMPOSED MEANING (`mgAll 𝔇 Mg`): THE FIFTH TIE: the field `t5` of `TieRestR`
(LinkTiedR.lean), to the letter. This sub-protocol pushes a row onto the segment's group and may
take entries of one mask ledger: so `SameRead` (Johnson/Top/H0/Walk/FrameFieldsBack.lean), which
asks the groups as they were, does not hold over it, and FifthTie.lean's rule does not serve.

The point. To go BACK, a class's sentence wants only that every row of the class IN FRONT is a row
of the class BEHIND: a push at a list's end gives that at every class, with no fence on the plan's
numbers.

Which items ride there (by Lean's evaluator at the written full list; no theorem): the committed
table's pin; the pile; the index masks' pin; the segment's three moments' pins; the four parts of
later segments' relations and of the output head's; the segment's rows (three samples, carried,
position); at the layers' and the head's segments "wo".

What is said.
  `classRows_push`: every row of a class in front is a row of that class behind a push.
  `ReadW N s t`: what the riders' sentences read of the two states: `SameRead` with "the groups are
    as they were" weakened to that inclusion (and without the mark and the claim of the test on the
    table, which no rider reads).
  `pushRider`: the sorts of item of which the rule speaks.
  `holds_back_push`: **every such rider goes back over a relation that gives `ReadW`.**
  `formsAt_bare`, `ansAt_bare`, `smpNamed_bare`: the named reader of the OOD samples reads nothing
    of a ledger nor of a group.
  `BlockYes b₃ s t`: an accepting step of b₃ from s to t.
  `rows_set`, `readW_eq`: **an accepting step of the one equation's sub-protocol gives `ReadW`.**
  `read3_eq`: the three premises on the readers, at the meant terms.
  `eq_rowAt`, `wo_back_eq`: the reader of the pending claim on the weights answers alike (the proof
    is the one inside `eq_hasRow`, DoorBlind.lean, lifted), so "wo" goes back: where no message of
    the link's own is the index masks' message.
  `t5_eq`: **THE FIELD AT THE ONE EQUATION's PIECE.**

Limits. Left as premises, each by name: `MeantAt`; `HeadOpen`; "no message of the link's own is the
index masks' message", at the state in front, from what is known there; on every rider: it is of a
sort in `pushRider`, it is not the digits' part, its pins' trees lie below the piece's first tree.
No soundness statement.

-/
import Johnson.Desc.First.Link.Law.FifthTie
import Johnson.Desc.First.Link.Law.DoorBlind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open OnBytes.Means (AllSay)
open VerifiableInference.Desc.K9 (atS Where messageNow)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.K1 (formsAt ansAt)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers RowClass classRows start)
open VerifiableInference.Desc.K13.Law (RowsTrue rwBook_same)
open VerifiableInference.OnPublicFiles (headLink)
open Johnson.Desc.First.Walk.Tied
open _root_.Run.PQ (CK)

/-- The message without its ledger. -/
abbrev bare (x : OnBytes.Oracle) : OnBytes.Oracle := { x with ledger := none }

theorem bare_blind : Blind bare := fun _ _ => rfl

/-- **Every row of a class in front is a row of that class behind a push.** -/
theorem classRows_push (N : Numbers) (m : ℕ) (c : RowClass) {s t : S} (g : ℕ) (row : OnBytes.Row)
    (hg : t.st.groups = s.st.groups.modify g fun G => { G with rows := G.rows.push row })
    (hsz : t.st.oracles.size = s.st.oracles.size) (hbk : t.book = s.book)
    (hm : ∀ i : ℕ, (t.st.oracles[i]?).map bare = (s.st.oracles[i]?).map bare) :
    ∀ r ∈ classRows N m c s, r ∈ classRows N m c t := by
  have hsm : ∀ o : ℕ, (t.st.oracles[o]?).map (fun a : OnBytes.Oracle => a.sampleRows.toList) =
      (s.st.oracles[o]?).map (fun a : OnBytes.Oracle => a.sampleRows.toList) := by
    intro o
    have h1 := congrArg (Option.map fun a : OnBytes.Oracle => a.sampleRows.toList) (hm o)
    rw [Option.map_map, Option.map_map] at h1
    exact h1
  have list : ∀ (st n : ℕ) (r : OnBytes.Row),
      r ∈ (match s.st.groups[N.groupAt m]? with
        | none => []
        | some G => (List.range n).filterMap fun j => G.rows[st + j]?) →
      r ∈ (match t.st.groups[N.groupAt m]? with
        | none => []
        | some G => (List.range n).filterMap fun j => G.rows[st + j]?) := by
    intro st n r hr
    rw [hg, Array.getElem?_modify]
    cases hG : s.st.groups[N.groupAt m]? with
    | none =>
      rw [hG] at hr
      cases hr
    | some G =>
      rw [hG] at hr
      obtain ⟨j, hj, e⟩ := List.mem_filterMap.1 hr
      by_cases hi : g = N.groupAt m
      · rw [if_pos hi]
        refine List.mem_filterMap.2 ⟨j, hj, ?_⟩
        show (G.rows.push row)[st + j]? = some r
        have hlt : st + j < G.rows.size := (Array.getElem?_eq_some_iff.1 e).1
        rw [Array.getElem?_push_lt hlt, ← e, Array.getElem?_eq_getElem hlt]
      · rw [if_neg hi]
        exact List.mem_filterMap.2 ⟨j, hj, e⟩
  intro r hr
  cases c with
  | sample k =>
    simp only [classRows, hsz, hbk, hsm] at hr ⊢
    exact hr
  | _ => exact list _ _ r hr

/-- **What the riders' sentences read of the state in front (s) and of the state behind (t).** -/
structure ReadW (N : Numbers) (s t : S) : Prop where
  book : t.book = s.book
  codes : t.st.codes = s.st.codes
  size : t.st.oracles.size = s.st.oracles.size
  msgs : ∀ i : ℕ, (t.st.oracles[i]?).map bare = (s.st.oracles[i]?).map bare
  rows : ∀ r ∈ s.rows, r ∈ t.rows
  classes : ∀ m c, ∀ r ∈ classRows N m c s, r ∈ classRows N m c t

theorem ReadW.shape {N : Numbers} {s t : S} (h : ReadW N s t) (o : ℕ) :
    (t.st.oracles[o]?).map (fun a : OnBytes.Oracle => a.shape) =
      (s.st.oracles[o]?).map (fun a : OnBytes.Oracle => a.shape) := by
  have h1 := congrArg (Option.map fun a : OnBytes.Oracle => a.shape) (h.msgs o)
  rw [Option.map_map, Option.map_map] at h1
  exact h1

/-- The sorts of item of which the rule speaks. -/
def pushRider : Item → Bool
  | .constr _ _ | .pin _ _ | .pinKept _ | .pinI | .pinV | .pinW | .row _ _ | .pile | .wo _ => true
  | _ => false

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

local notation "WT" => Wit (CellsQ rows cols) Tok MsgT

/-- **EVERY SUCH RIDER GOES BACK.** -/
theorem holds_back_push (N : Numbers) (Op : Item → Prop) (low : ℕ → Prop)
    (R : P × S → Strs → P × S → Strs → Prop)
    (hcell : ∀ a y b y', R a y b y' → ∀ x, y'.cell x = y.cell x)
    (hcol : ∀ a y b y', R a y b y' → ∀ j, low j → ∀ x, y'.col j x = y.col j x)
    (hst : ∀ a y b y', R a y b y' → ReadW 𝔇.N a.2 b.2) (h3 : Read3 𝔇 low R)
    (hH : HeadOpen 𝔇 Op R) (hw : WoOpen 𝔇 Op R)
    (hO : ∀ i, Op i → pushRider i = true ∧ notOwn ownDigits i ∧ lowItem N low i) :
    ∀ i, Op i → GoesBack R (i.holds N (mgAll 𝔇 Mg)) := by
  have pinB : ∀ j t, low j → GoesBack R ((mgAll 𝔇 Mg).pin j t) := by
    intro j t hj
    rw [mgAll_pin]
    intro a y b y' w h hp
    have hp' := pinJT_col 𝔇.cs 𝔇.G 𝔇.arr 𝔇.smp 𝔇.ms j t b y' y w
      (fun x => (hcol a y b y' h j hj x).symm) hp
    refine ⟨hp'.1, fun x hx hs => ?_⟩
    obtain ⟨z, hz, h2, h4⟩ := hp'.2 x hx hs
    have hs' : x.1.seat x.2 = (j, t) := hs
    refine ⟨z, ?_, h2, h4⟩
    show 𝔇.smp a x.1 x.2 = some z
    rw [h3.smp a y b y' h x hx (by rw [hs']; exact hj)]
    exact hz
  intro i hi
  obtain ⟨hp, ho, hl⟩ := hO i hi
  cases i with
  | constr m p =>
    have ho' : (p == .lookDigits) = false := ho
    have h1 : p ≠ .lookDigits := by
      intro e
      subst e
      simp at ho'
    have hdec : ∀ a y b y', R a y b y' →
        (oneDec 𝔇.decT 𝔇.H).dec a y = (oneDec 𝔇.decT 𝔇.H).dec b y' := by
      intro a y b y' h
      show 𝔇.decT y.cell a = 𝔇.decT y'.cell b
      rw [show y'.cell = y.cell from funext (hcell a y b y' h)]
      exact h3.dec a y b y' h _
    show GoesBack R ((mgAll 𝔇 Mg).constr m p)
    rw [mgAll_constr]
    by_cases hm : m = headLink X
    · subst hm
      exact constrQAt_back_any (headLink X) 𝔇.put (oneDec 𝔇.decT 𝔇.H) 𝔇.headPart 𝔇.digitsPart _ p
        h1 R (fun a y b y' h => h3.req a y b y' h) hdec (hH p hi)
    · exact constrQAt_back (headLink X) 𝔇.put (oneDec 𝔇.decT 𝔇.H) 𝔇.headPart 𝔇.digitsPart m p h1
        hm R (fun a y b y' h => h3.req a y b y' h) hdec
  | pin m t => exact fun a y b y' w hr h x hx => pinB x.1 x.2 (hl x hx) a y b y' w hr (h x hx)
  | pinKept m => exact fun a y b y' w hr h x hx => pinB x.1 x.2 (hl x hx) a y b y' w hr (h x hx)
  | pinI => exact pinB _ _ hl
  | pinV => exact pinB _ _ hl
  | pinW =>
    show GoesBack R (mgAll 𝔇 Mg).pinW
    rw [mgAll_pinW]
    intro a y b y' w h hq
    show 𝔇.decT y.cell a = some w.cells
    rw [h3.dec a y b y' h, ← show y'.cell = y.cell from funext (hcell a y b y' h)]
    exact hq
  | row m c =>
    show GoesBack R ((mgAll 𝔇 Mg).row m c)
    rw [mgAll_row]
    intro a y b y' w h hq
    have hS := hst a y b y' h
    have hq' : AllSay OnBytes.Slice.rdE b.2.st (classRows 𝔇.N m c b.2)
        (wordsFirst 𝔇.arr b.2.st b.2.book w) := hq
    have ew : wordsFirst 𝔇.arr b.2.st b.2.book w = wordsFirst 𝔇.arr a.2.st a.2.book w := by
      funext o part i
      unfold wordsFirst
      rw [hS.book]
      exact wordsBy_congr 𝔇.arr _ _ a.2.st b.2.st w o o hS.codes rfl (hS.shape o) part i
    rw [ew] at hq'
    show AllSay OnBytes.Slice.rdE a.2.st (classRows 𝔇.N m c a.2)
      (wordsFirst 𝔇.arr a.2.st a.2.book w)
    exact fun r hr =>
      (says_same _ hS.codes hS.size hS.shape r _).1 (hq' r (hS.classes m c r hr))
  | pile =>
    show GoesBack R (mgAll 𝔇 Mg).pile
    rw [mgAll_pile]
    intro a y b y' w h hq
    have hS := hst a y b y' h
    have hq' : RowsTrue (𝔇.rw13 b) b.2 w := hq
    have e : 𝔇.rw13 b w = 𝔇.rw13 a w := rwBook_same 𝔇.arr 𝔇.mat13 a b hS.book hS.codes hS.shape w
    show RowsTrue (𝔇.rw13 a) a.2 w
    intro r hr
    have h1 := hq' r (hS.rows r hr)
    rw [e] at h1
    exact h1
  | wo m =>
    show GoesBack R ((mgAll 𝔇 Mg).wo m)
    rw [mgAll_wo]
    exact hw m hi
  | _ => cases hp

end

/-! ### the named reader of the OOD samples -/

theorem formsAt_bare {A B : Statement}
    (h : ∀ i : ℕ, (B.oracles[i]?).map bare = (A.oracles[i]?).map bare) (cs : Codes)
    (sh : OracleShape) (o : ℕ) : formsAt cs sh B o = formsAt cs sh A o := by
  have e := congrArg (Option.map fun a : OnBytes.Oracle => a.sampleRows) (h o)
  rw [Option.map_map, Option.map_map] at e
  unfold formsAt
  cases hs : A.oracles[o]? with
  | none =>
    rw [hs, Option.map_none, Option.map_eq_none_iff] at e
    rw [e]
  | some a =>
    rw [hs, Option.map_some] at e
    obtain ⟨b, hb, eb⟩ := Option.map_eq_some_iff.1 e
    have eb' : b.sampleRows = a.sampleRows := eb
    rw [hb]
    simp only [Option.bind_some, eb']

theorem ansAt_bare {A B : Statement}
    (h : ∀ i : ℕ, (B.oracles[i]?).map bare = (A.oracles[i]?).map bare) (o : ℕ) :
    ansAt B o = ansAt A o := by
  have e := congrArg (Option.map fun a : OnBytes.Oracle => a.sampleRows) (h o)
  rw [Option.map_map, Option.map_map] at e
  unfold ansAt
  cases hs : A.oracles[o]? with
  | none =>
    rw [hs, Option.map_none, Option.map_eq_none_iff] at e
    rw [e]
  | some a =>
    rw [hs, Option.map_some] at e
    obtain ⟨b, hb, eb⟩ := Option.map_eq_some_iff.1 e
    have eb' : b.sampleRows = a.sampleRows := eb
    rw [hb]
    simp only [Option.bind_some, eb']

theorem smpNamed_bare {P : Type} (cs : Codes) (seats : List (ℕ × ℕ)) (p : P) {s t : S}
    (h : ∀ i : ℕ, (t.st.oracles[i]?).map bare = (s.st.oracles[i]?).map bare) (x : Sending)
    (i : Fin x.l.length) : smpNamed cs seats (p, s) x i = smpNamed cs seats (p, t) x i :=
  (smpNamed_stays cs seats (p, s) (p, t) x i (formsAt_bare h cs _ _) (ansAt_bare h _)).symm

/-! ### the one equation's sub-protocol -/

/-- The rows on the table are not what the lens writes. -/
theorem rows_set (s : S) (q : K9.Part) : (atS.set s q).rows = s.rows := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x =>
    show (({ (S.putLink ⟨st, book, roots, rowsOwed, failed, check, out, .head x, req⟩ q.L).putFork
      q.F with st := q.d.st, rowsOwed := q.owed } : S)).rows = _
    by_cases ho : x.opened = true <;> simp [S.putLink, S.putFork, S.rows, ho]
  | _ => rfl

section
variable {Cl : Type} (pw : Where) (b₃ : Block S Cl)
  (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
    (K9.oneEquation (Cl := Cl) atS pw).step ft s rs cols = .ok x)
include hb₃

/-- **AN ACCEPTING STEP GIVES `ReadW`**, at every plan's numbers. -/
theorem readW_eq (N : Numbers) {s t : S} (h : BlockYes b₃ s t) : ReadW N s t := by
  obtain ⟨ft, rs, cols, k, h⟩ := h
  obtain ⟨a, row, G0, -, -, El⟩ := eq_lays pw b₃ hb₃ ft s rs cols t k h
  obtain ⟨-, -, e, -⟩ := eq_both pw b₃ hb₃ bare_blind ft s rs cols t k h
  obtain ⟨a0, out, -, -, hs'⟩ := oneEquation_inv atS pw _ _ _ _ _ k (hb₃ _ _ _ _ _ h)
  refine ⟨El.book, e.1, El.oracles, e.2, fun r hr => ?_,
    fun m c => classRows_push N m c _ row El.groups El.oracles El.book e.2⟩
  rw [hs', rows_set]
  exact hr

/-- The reader of the pending claim on the weights answers alike. (The proof inside `eq_hasRow`,
lifted.) -/
theorem eq_rowAt {s t : S} (h : BlockYes b₃ s t)
    (hne : ∀ a, atS.get? s = some a → ∀ m o,
      messageNow a.L.check.frame a.L.check.frame.link m = some o → o ≠ s.out.indexMasks)
    (lay : WsLay) (n : ℕ) (lin : Params.LinShape) :
    Johnson.Desc.First.Walk.Law.rowAt lay n lin t =
      Johnson.Desc.First.Walk.Law.rowAt lay n lin s := by
  obtain ⟨ft, rs, cols, k, h⟩ := h
  obtain ⟨a, ha, _, e⟩ := eq_both pw b₃ hb₃ tri_blind ft s rs cols t k h
  obtain ⟨a0, out, ha0, _, hs'⟩ := oneEquation_inv atS pw _ _ _ _ _ k (hb₃ _ _ _ _ _ h)
  have hout : t.out = s.out := by
    rw [hs']
    exact out_set s _
  have hleft : Johnson.Desc.First.Walk.Law.leftOf t = Johnson.Desc.First.Walk.Law.leftOf s := by
    rw [hs']
    exact leftOf_set s _
  have hor : t.st.oracles[s.out.indexMasks]? = s.st.oracles[s.out.indexMasks]? := by
    rcases e with e | ⟨m, o, ho, hj⟩
    · rw [e]
    · exact hj _ (Ne.symm (hne a ha m o ho))
  have key : ∀ (A B : Array OnBytes.Oracle) (i : ℕ) (w : WsForkOut) (r : TensorRow),
      B[i]? = A[i]? → (∃ os, First.Pend.pendingRowO lay i w n lin A = .ok (r, os)) →
      ∃ os, First.Pend.pendingRowO lay i w n lin B = .ok (r, os) := by
    intro A B i w r hAB ⟨os, hos⟩
    obtain ⟨c1, c2, c3, c4, fi, la, c5, c6, c7, c8, c9, Ga, c10, g, c11, l, c12, c, l', c13, c14,
      _⟩ := (First.Pend.pendingRowO_iff lay i w n lin A os r).1 hos
    exact ⟨_, (First.Pend.pendingRowO_iff lay i w n lin B _ r).2 ⟨c1, c2, c3, c4, fi, la, c5, c6,
      c7, c8, c9, Ga, c10, g, c11, l, by rw [hAB]; exact c12, c, l', c13, c14, rfl⟩⟩
  apply Option.ext
  intro r
  unfold Johnson.Desc.First.Walk.Law.rowAt
  rw [Johnson.Desc.First.Walk.Law.rowBy_some, Johnson.Desc.First.Walk.Law.rowBy_some, hleft,
    hout]
  constructor
  · rintro ⟨w, os, hw, hp⟩
    obtain ⟨os', hp'⟩ := key _ _ _ w r hor.symm ⟨os, hp⟩
    exact ⟨w, os', hw, hp'⟩
  · rintro ⟨w, os, hw, hp⟩
    obtain ⟨os', hp'⟩ := key _ _ _ w r hor ⟨os, hp⟩
    exact ⟨w, os', hw, hp'⟩

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- No message of the link's own is the index masks' message. -/
def OwnNotIndex (s : S) : Prop :=
  ∀ a, atS.get? s = some a → ∀ m o,
    messageNow a.L.check.frame a.L.check.frame.link m = some o → o ≠ s.out.indexMasks

/-- **"wo" goes back over the one equation's accepting step.** -/
theorem wo_back_eq (base : ℕ) (In : P × S → Strs → Prop)
    (hne : ∀ p s y, In (p, s) y → OwnNotIndex s) (m : ℕ) :
    GoesBack (StepRel (BlockYes b₃) base In) (First.FillP1.woAt 𝔇.d1 𝔇.rw13 m) := by
  intro a y b y' w hr h
  obtain ⟨p, s⟩ := a
  obtain ⟨p', t⟩ := b
  obtain ⟨e, hq, -, hI⟩ := hr
  obtain rfl : p' = p := e
  have hS := readW_eq pw b₃ hb₃ 𝔇.N hq
  unfold First.FillP1.woAt at h ⊢
  intro r hrow
  have e2 : 𝔇.rw13 (p', t) w = 𝔇.rw13 (p', s) w :=
    rwBook_same 𝔇.arr 𝔇.mat13 (p', s) (p', t) hS.book hS.codes hS.shape w
  have h1 := h r (by
    show Johnson.Desc.First.Walk.Law.rowAt _ _ _ t = some r
    rw [eq_rowAt pw b₃ hb₃ hq (hne p' s y hI)]
    exact hrow)
  rw [e2] at h1
  exact h1

/-- The three premises on the readers, at the meant terms. -/
theorem read3_eq {seats : List (ℕ × ℕ)} {r : P → P5J.TReq} (hM : MeantAt 𝔇 seats r) (base : ℕ)
    (In : P × S → Strs → Prop) :
    Read3 𝔇 (fun j => j < base) (StepRel (BlockYes b₃) base In) where
  req a y b y' h := by rw [hM.req, hM.req, h.1]
  dec a y b y' h c := by
    obtain ⟨p, s⟩ := a
    obtain ⟨p', t⟩ := b
    obtain rfl : p' = p := h.1
    exact hM.dec c p' s t
  smp a y b y' h x _ _ := by
    obtain ⟨p, s⟩ := a
    obtain ⟨p', t⟩ := b
    obtain rfl : p' = p := h.1
    rw [hM.smp]
    exact smpNamed_bare 𝔇.cs seats p' (readW_eq pw b₃ hb₃ 𝔇.N h.2.1).msgs x.1 x.2

end

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
variable {C : CK} {F : Frame}

local notation "WT" => Wit (CellsQ rows cols) Tok MsgT

/-- **THE FIFTH TIE AT THE ONE EQUATION's PIECE.** In: what its payers may spend of the promise in
front. -/
theorem t5_eq (Nm : Numbers) (links : List ModelPart) (pl : List Place) (z : P)
    (Rz : ℕ → S × F.E.Str → Prop) (k : ℕ) (pw : Where) (b₃ : Block S Claim)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Claim) atS pw).step ft s rs cols = .ok x)
    (q : Piece C F S Claim WT) (hqb : q.b = below b₃) (hext : ∀ a τ w, q.ext a τ w = w)
    (In : P × S → Strs → Prop)
    (hIn : ∀ a, onTR Nm (mgAll 𝔇 Mg) links pl (fun s : S => (z, s)) Rz k a →
      In (z, a.1) (strsOf F a.2))
    (hne : ∀ p s y, In (p, s) y → OwnNotIndex s)
    {seats : List (ℕ × ℕ)} {r : P → P5J.TReq} (hM : MeantAt 𝔇 seats r)
    (hH : HeadOpen 𝔇 (fun i => openAfter (insQ links pl) (outsQ links pl) (· ∈ start links) k i ∧
      ¬ insQ links pl k i) (StepRel (BlockYes b₃) q.base In))
    (hO : ∀ i, openAfter (insQ links pl) (outsQ links pl) (· ∈ start links) k i →
      ¬ insQ links pl k i → pushRider i = true ∧ notOwn ownDigits i ∧
        lowItem Nm (fun j => j < q.base) i) :
    ∀ a τ b w i, onTR Nm (mgAll 𝔇 Mg) links pl (fun s : S => (z, s)) Rz k a →
      q.ior.red.out a τ = some b →
      onQ Nm (mgAll 𝔇 Mg) links pl (fun s : S => (z, s)) (k + 1) b →
      relQ Nm (mgAll 𝔇 Mg) links pl (fun s : S => (z, s)) (k + 1) b w →
      openAfter (insQ links pl) (outsQ links pl) (· ∈ start links) k i → ¬ insQ links pl k i →
      meansQ Nm (mgAll 𝔇 Mg) (fun s : S => (z, s)) i a (q.ext a τ w) :=
  t5_of_back Nm (mgAll 𝔇 Mg) links pl z Rz k q hext (BlockYes b₃) In
    (fun a _ _ ha hout => ⟨yes_of_out hqb hout, hIn a ha⟩)
    fun i ho hn => holds_back_push 𝔇 Mg Nm _ _ _ (fun _ _ _ _ h => h.2.2.1.1)
      (fun _ _ _ _ h j hj x => h.2.2.1.2 j x hj)
      (fun _ _ _ _ h => readW_eq pw b₃ hb₃ 𝔇.N h.2.1) (read3_eq pw b₃ hb₃ 𝔇 hM q.base In) hH
      (fun m _ => wo_back_eq pw b₃ hb₃ 𝔇 q.base In hne m) (fun j hj => hO j hj.1 hj.2) i ⟨ho, hn⟩

end

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.classRows_push
#print axioms VerifiableInference.Desc.LinkJoin.holds_back_push
#print axioms VerifiableInference.Desc.LinkJoin.smpNamed_bare
#print axioms VerifiableInference.Desc.LinkJoin.readW_eq
#print axioms VerifiableInference.Desc.LinkJoin.eq_rowAt
#print axioms VerifiableInference.Desc.LinkJoin.wo_back_eq
#print axioms VerifiableInference.Desc.LinkJoin.read3_eq
#print axioms VerifiableInference.Desc.LinkJoin.t5_eq
