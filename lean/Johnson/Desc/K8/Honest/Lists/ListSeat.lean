-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/Lists/ListSeat.lean: THE OPEN LINK's LIST OF ARRAYS, ALONG THE FIRST CHAIN's
FRONT: «WHERE A LINK IS OPEN, ITS CONTEXT's LIST HAS, AT THE LINK's OWN NUMBER, THE ENTRIES tOf» IS
HANDED ON BY EVERY MAKER THAT THE LIBRARY's GENERIC WALK ASKS (`Meaning.K2.SeatKeeps`,
Johnson/IMR/SeatKeeps.lean: twenty fields). IT STANDS OVER THE LIBRARY ALONE. Definitions and
lemmas; none of the library's goals.

  `ListInv tOf s` for every L with s.link? = some L: L.list.nt = tOf L.link. OF THE FIELD nt ALONE:
                   the list's other fields do not stay: the batching's own draw writes `used`
                   (K9.drawn, Johnson/Desc/First/Batch/Kind.lean) and the closing `walked`
                   (K9.closed, Batch/Text.lean)
  `KeepsList tOf s t` ListInv tOf s → ListInv tOf t
  `TpOk tOf built` tOf is the built links' own lists' entries, by number
  the tools `keepsList_refl`, `_trans`, `_of_lk` (from the library's SameLink), `_none`, `_laid`,
                   `_putLink`, `_puts`, `_set`, `_putLive`; `whole_list`
  the frame `zeroAt_tp`, `frameAt_tp`; `layFront_list`, `openAtt_list`, `openLay_list`,
                   `openLayZero_list`, `clearWith_list`, `tailHead_list`; `framesOf_list`
  K1 `commitStep_nt`, `commitAtS_list`, `firstAtS_list`
  the quiet steps behind the reads' sending, and the reply `readsLay_lk`, `readsHead_lk`,
                   `readsAtt_lk`, `readsBlockAt_lk`, `readsQuietAt_lk`, `k7Of_lk`: Whole SameLink
  K9 and K10 `drawn_nt`; `oneEquation_list`, `closing_list`, `shut_list`, `closeOf_list`,
                   `batch_list`
  K2's places `k2_list`, `headFrontQ_list`, `headOpenQ_list`, `finishFrontQ_list`,
                   `finishBehindQ_list`
  **`seatKeeps_list`** SeatKeeps (KeepsList tOf) (TpOk tOf) (fun P => P.X.Tp.nt = tOf P.l)
HOW. SIX FIELDS (k3 · k4 · k5 · k6 · k8 · k11) ARE ONE CALL EACH OF THE LIBRARY's LAWS THAT THESE
KINDS, AS SEATED, LEAVE THE OPEN LINK's CONTEXT WHOLE (`Meaning.Lnk.SameLink`: theStated_lk,
blockAtC_lk, k5AtN_lk, seatedClaims_lk, k8Whole_lk, headMerge11_lk,
Johnson/Goal/Meaning/LinkSeated.lean). WHERE A LINK IS OPENED THE LIBRARY WRITES THE WHOLE CONTEXT
OUT, list := X.Tp: `openAtt_ok`, `openLay_ok`, `openLayZero_ok`, `front_ok`
(Johnson/Top/H0/Walk/FrameLaw.lean); at the head's segment the context is made anew at the opening,
so nothing is asked of what lies hidden before. K2's switch: LinkJoin.k2_link_kept
(Johnson/Desc/First/Link/Law/LooksK2.lean). THE READS' QUIET STEPS: that a yes of each leaves
S.link? is the sixth clause of the library's `K1.QuietL` (Johnson/Desc/K1/Law/ReadsStep.lean):
`quietL_layers`, `quietL_head`, `quietL_att` are called at the three leaves.
WRITTEN A FURTHER TIME, AT ANOTHER FIELD: THE NEAREST KIN IS THE LIBRARY's FAMILY ON arrayOf
(OwnInv, OwnRel, SameCtx: Johnson/Goal/Meaning/OwnInv.lean, OwnMakers.lean, K2Share/OwnKept.lean,
Johnson/IMR/OwnSeat.lean); it cannot be called: its reading ctxOf holds arrayOf, not the list. After
its proofs, with list.nt or Tp in arrayOf's stead: `zeroAt_tp`, `frameAt_tp` (zeroAt_arr,
frameAt_arr) · `framesOf_list` (framesOf_own) · `clearWith_list` (clearWith_own) · `commitStep_nt`,
`commitAtS_list`, `firstAtS_list` (commitStep_ctx, commitAtS_ctx, firstAtS_ctx) · `drawn_nt`,
`oneEquation_list`, `closeOf_list`, `batch_list` (drawn_ctx, oneEquation_ctx, closeOf_own,
batch_own) · `seatKeeps_list` (seatKeeps_own). After the proofs of the library's family on the
arrays' looks (Johnson/Desc/First/Link/Law/LooksSeated.lean, LooksEnds.lean, LooksClose.lean):
`readsBlockAt_lk`, `readsQuietAt_lk`, `k7Of_lk` (readsBlockAt_whole, readsQuietAt_whole,
k7Of_whole): the first two join the three leaves as the library's quietL_blockAt and
quietL_readsQuietAt (ReadsStep.lean) do; these two are not called, since `Whole` asks two halves
more (no runs of claims; none behind), which want the same split into cases · `closing_list`,
`shut_list` (closing_decides, shut_decides) · `headFrontQ_list`, `headOpenQ_list`,
`finishFrontQ_list`, `finishBehindQ_list` (headFront_keeps, headOpen_makes, finFront_keeps,
finBehind_keeps). KIN, NOT CALLED: a second family of the library's has the three leaves' equation
too: `LookSame` (Johnson/Desc/K1/Law/LookSame.lean; lookSame_layers, lookSame_head, lookSame_att,
QuietLook.lean).
NO DEVICE. TACTICS THAT SEARCH: `simp [a list]` on two lines · `simp only [a list]` on nine ·
`simpa` on one · `repeat'` with `first` once; `dsimp only` on three.
Limits. IT SAYS NOTHING OF ANY STATE: a law on steps. Nothing on the list's other four fields.
Nothing on the makers behind the last link (`SeatBack`). No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.IMR.OwnSeat
import Johnson.Goal.Meaning.LinkSeated
import Johnson.LPFK9R.LooksSeat
import Johnson.Desc.K1.Law.ReadsStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Params _root_.Desc.Plain
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.K1
open VerifiableInference.Desc.K9 (drawAlone adds batch oneEquation Where door drawnClean drawn
  Out Drawn St RowsOwed)
open Johnson.Desc.First.Walk
open Meaning.K2 (SeatKeeps whole_mono bindE atS_get there_some door_keeps mem_of_mapM_ok)
open Meaning.Lnk

variable {Cl : Type} {tOf : ℕ → Array N2}

/-! ## The sentence -/

/-- **Where a link is open, its context's list of arrays has, at the link's own number, the entries
tOf.** -/
def ListInv (tOf : ℕ → Array N2) (s : S) : Prop :=
  ∀ L, s.link? = some L → L.list.nt = tOf L.link

/-- The sentence is handed on. -/
def KeepsList (tOf : ℕ → Array N2) : S → S → Prop := fun s t => ListInv tOf s → ListInv tOf t

theorem keepsList_refl (s : S) : KeepsList tOf s s := id

theorem keepsList_trans (a b c : S) (h : KeepsList tOf a b) (k : KeepsList tOf b c) :
    KeepsList tOf a c := fun x => k (h x)

theorem keepsList_of_lk {s t : S} (h : SameLink s t) : KeepsList tOf s t :=
  fun I L hL => I L (Eq.trans (Eq.symm h) hL)

theorem keepsList_none {s t : S} (h : t.link? = none) : KeepsList tOf s t := fun _ L hL => by
  rw [h] at hL
  cases hL

theorem keepsList_laid {s t : S} {L : LinkCtx} (h : t.link? = some L)
    (e : L.list.nt = tOf L.link) : KeepsList tOf s t := fun _ L' hL' => by
  obtain rfl := Option.some.inj (h.symm.trans hL')
  exact e

theorem whole_list {b : Block S Cl} (W : Whole SameLink b) : Whole (KeepsList tOf) b :=
  whole_mono (fun _ _ => keepsList_of_lk) W

/-! ## Writing the open link's context -/

theorem keepsList_putLink {s u : S} {L0 L : LinkCtx} (hL : s.link? = some L0)
    (uL : u.link? = some L0) (el : L.link = L0.link) (en : L.list.nt = L0.list.nt) :
    KeepsList tOf s (u.putLink L) := fun I =>
  keepsList_laid (s := s) (LinkJoin.link_putLink u L0 L uL) (by rw [en, el]; exact I L0 hL) I

theorem keepsList_puts {s u : S} {L0 L : LinkCtx} (hL : s.link? = some L0)
    (uL : u.link? = some L0) (el : L.link = L0.link) (en : L.list.nt = L0.list.nt) (F : Fork) :
    KeepsList tOf s ((u.putLink L).putFork F) :=
  keepsList_trans _ _ _ (keepsList_putLink hL uL el en) (keepsList_of_lk (lk_putFork _ F))

theorem keepsList_set {s : S} {L : LinkCtx} (h : s.link? = some L) (p : K9.Part)
    (e2 : p.L.link = L.link) (e3 : p.L.list.nt = L.list.nt) : KeepsList tOf s (K9.atS.set s p) :=
  fun I L' hL' => keepsList_puts h h e2 e3 p.F I L' hL'

theorem keepsList_putLive (s : S) (c : ChainCheck) : KeepsList tOf s (s.putLive c) := by
  unfold S.putLive
  split
  · rename_i L hL
    exact keepsList_putLink hL hL rfl rfl
  · exact keepsList_of_lk rfl

/-! ## The links' frames -/

open Johnson.Desc.First.Walk.Seat in
theorem zeroAt_tp {built : Array Stages.LinkH} {W : Verify.Public} {P : LayPar}
    (h : zeroAt built W = some P) : ∃ X, built[0]? = some X ∧ P.X.Tp = X.Tp := by
  unfold zeroAt at h
  obtain ⟨X, hX, h⟩ := Option.bind_eq_some_iff.1 h
  refine ⟨X, hX, ?_⟩
  split at h
  · cases h
  · obtain ⟨_, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨hp, -, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    rfl

open Johnson.Desc.First.Walk.Seat in
theorem frameAt_tp {built : Array Stages.LinkH} {W : Verify.Public} {l : Nat} {p : Seat.Par}
    (h : Seat.frameAt built W l = some p) : ∃ X, built[l]? = some X ∧
      match p with
      | .att P _ => P.X.Tp = X.Tp ∧ P.l = l
      | .lay P => P.X.Tp = X.Tp ∧ P.l = l := by
  unfold Seat.frameAt at h
  obtain ⟨X, hX, h⟩ := Option.bind_eq_some_iff.1 h
  refine ⟨X, hX, ?_⟩
  split at h
  · cases h
  · split at h
    · obtain ⟨q, -, h⟩ := Option.bind_eq_some_iff.1 h
      cases h
      exact ⟨rfl, rfl⟩
    · split at h
      · obtain ⟨q, -, h⟩ := Option.bind_eq_some_iff.1 h
        cases h
        exact ⟨rfl, rfl⟩
      · cases h

theorem layFront_list (l : ℕ) : Fn (KeepsList tOf) (layFront l) := fun s t k => by
  rw [(Law.layFront_ok k).1]
  exact keepsList_refl s

theorem openAtt_list (P : AttPar) (hT : P.X.Tp.nt = tOf P.l) : Fn (KeepsList tOf) (openAtt P) :=
  fun _ _ h => keepsList_laid (Law.openAtt_ok h).2.2.2.2.1 hT

theorem openLay_list (P : LayPar) (hT : P.X.Tp.nt = tOf P.l) : Fn (KeepsList tOf) (openLay P) :=
  fun _ _ h => keepsList_laid (Law.openLay_ok h).2.2.2.2.2.1 hT

theorem openLayZero_list (P : LayPar) (fvs : List Bool) (kCol : Nat) (hT : P.X.Tp.nt = tOf 0) :
    Fn (KeepsList tOf) (openLayZero P fvs kCol) :=
  fun _ _ h => keepsList_laid (Law.openLayZero_ok h).2.2.2.2.2.1 hT

theorem clearWith_list (X : LinkPub) (counts : S → Except String Unit)
    (left : S → Option WsForkOut) (row : RowFn) :
    Fn (KeepsList tOf) (clearWith X counts left row) := fun s t h => by
  obtain ⟨-, -, -, -, -, -, -, -, -, hb⟩ := Law.clear_carries h
  have hh : t.here = .between := by
    unfold S.atBetween at hb
    cases k : t.here <;> simp [k] at hb ⊢
  exact keepsList_none (by simp [S.link?, hh])

theorem tailHead_list (X : LinkPub) (ws : WsLay) (lin : LinShape) :
    Fn (KeepsList tOf) (Close.tailHead X ws lin) := clearWith_list _ _ _ _

/-- tOf is the built links' own lists' entries. -/
def TpOk (tOf : ℕ → Array N2) (built : Array Stages.LinkH) : Prop :=
  ∀ l X, built[l]? = some X → X.Tp.nt = tOf l

open Johnson.Desc.First.Walk.Seat in
/-- **Every row of the frame, link by link.** -/
theorem framesOf_list {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} (hA : TpOk tOf built)
    (h : framesOf built first W = .ok fs) : ∀ f ∈ fs,
    Fn (KeepsList tOf) f.lay ∧ Fn (KeepsList tOf) f.opened ∧ Fn (KeepsList tOf) f.clear := by
  intro f hf
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact ⟨layFront_list l, fun s t k I => by cases k; exact I, tailHead_list _ _ _⟩
  · split at e
    · split at e
      · cases e
      · rename_i P hP
        cases e
        obtain ⟨X, hX, e1⟩ := zeroAt_tp hP
        exact ⟨layFront_list 0, openLayZero_list _ _ _ (by rw [e1]; exact hA 0 X hX),
          clearWith_list _ _ _ _⟩
    · split at e
      · cases e
      · rename_i P n hP
        cases e
        obtain ⟨X, hX, e1, e2⟩ := frameAt_tp hP
        exact ⟨layFront_list l, openAtt_list _ (by rw [e1, e2]; exact hA l X hX),
          clearWith_list _ _ _ _⟩
      · rename_i P hP
        cases e
        obtain ⟨X, hX, e1, e2⟩ := frameAt_tp hP
        exact ⟨layFront_list l, openLay_list _ (by rw [e1, e2]; exact hA l X hX),
          clearWith_list _ _ _ _⟩

/-! ## K1 -/

theorem commitStep_nt {P : K1.Par} {owed : Option Nat} {ts : List Nat}
    {x y : L3.St (DState Unit)} {rs : List Fmt.RoundView}
    (h : L3.commitStep (laterOwn P owed) ts x rs = .ok y) :
    y.L.link = x.L.link ∧ y.L.list.nt = x.L.list.nt := by
  unfold L3.commitStep at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨⟨check, w⟩, h1, h⟩ := bindE h
  obtain ⟨⟨L, F⟩, h2, h⟩ := bindE h
  cases h
  unfold L3.commitBehind at h2
  obtain ⟨F', _, h2⟩ := bindE h2
  split at h2
  · cases h2
    exact ⟨rfl, rfl⟩
  · cases h2

theorem commitAtS_list (P : K1.Par) (link moment : Nat) (arrays : Option (List Nat)) :
    Whole (KeepsList tOf) (commitAtS (Cl := Cl) P link moment arrays) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [commitAtS] at h
  split at h
  · rename_i L F tl hL hF htl
    obtain ⟨y, hy, rfl⟩ := Keeps.emap_ok h
    have hfr : y.held.L.link = L.link ∧ y.held.L.list.nt = L.list.nt := by
      simp only [commitOwn] at hy
      split at hy
      · split at hy
        · cases hy
        · obtain ⟨x, hx, rfl⟩ := Keeps.emap_ok hy
          exact commitStep_nt hx
      · cases hy
    exact keepsList_puts (u := laid s y.held.w) hL hL hfr.1 hfr.2 _
  · cases h

theorem firstAtS_list (q : Params.First) (gp : GPar) :
    Whole (KeepsList tOf) (firstSegmentOpening (Cl := Cl) q gp) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [firstSegmentOpening] at h
  obtain ⟨_, hB, h⟩ := bindE h
  obtain ⟨⟨c, d⟩, h1, h⟩ := bindE h
  cases h
  exact keepsList_of_lk rfl

/-! ## The quiet steps behind the reads' sending, and the reply -/

theorem readsLay_lk (P : K8.ReadsQuiet.PG) : Whole SameLink (K8.ReadsQuiet.layers P) :=
  ⟨fun s rs gs s' h => (quietL_layers P s s' rs gs h).2.2.2.2.2, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩

theorem readsHead_lk (P : K8.ReadsQuiet.PH) : Whole SameLink (K8.ReadsQuiet.head P) :=
  ⟨fun s rs gs s' h => (quietL_head P s s' rs gs h).2.2.2.2.2, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩

theorem readsAtt_lk {W : Verify.Public} {l g : ℕ} {b : Block S Unit}
    (h : First.Att.readsAtO W l g = some b) : Whole SameLink b := by
  refine ⟨fun s rs gs s' e => (quietL_att h s s' rs gs e).2.2.2.2.2, ?_, ?_⟩ <;>
    (unfold First.Att.readsAtO at h
     obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
     exact fun _ hc => nomatch hc)

theorem readsBlockAt_lk {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL}
    {Hp : Head.HPlanH2} {kinds : List (ℕ × ℕ)} {l : ℕ} {b : Block S Unit}
    (h : K8.ReadsQuiet.blockAt G hS HLy Hp kinds l = some b) : Whole SameLink b := by
  unfold K8.ReadsQuiet.blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact readsLay_lk _
  · split at h
    · cases h
      exact readsHead_lk _
    · cases h

theorem readsQuietAt_lk {G : ProofFile.Ground} {l : ℕ} {X : Stages.LinkH} {piece : ℕ}
    {b : Block S Unit} (h : ProofFile.readsQuietAt G l X piece = some b) : Whole SameLink b := by
  unfold ProofFile.readsQuietAt at h
  repeat' split at h
  all_goals first
    | exact readsAtt_lk h
    | exact readsBlockAt_lk h
    | cases h

theorem k7Of_lk (W : Verify.Public) (l : ℕ) : Whole SameLink (Kinds.Reply.blockOf W l) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  have h' := h
  unfold Kinds.Reply.blockOf Kinds.Reply.blockAt Kinds.Reply.entered at h'
  dsimp only at h'
  split at h'
  · split at h'
    · exact nomatch h'
    · obtain ⟨_, x, _, _, _, rfl⟩ := Kinds.Head.Law.k7_ok h'
      rfl
  · exact nomatch h'

/-! ## K9 and K10 -/

theorem drawn_nt {rows : Nat} {chi : E} {owed : RowsOwed} {used : Nat} {L : LinkCtx} {F : Fork}
    {o : Drawn} (h : drawnClean rows chi owed used L F = .ok o) :
    o.L.link = L.link ∧ o.L.list.nt = L.list.nt := by
  unfold drawnClean at h
  obtain ⟨o', h1, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  cases h
  unfold drawn at h1
  obtain ⟨_, _, h1⟩ := bindE h1
  obtain ⟨_, _, h1⟩ := bindE h1
  obtain ⟨_, _, h1⟩ := bindE h1
  obtain ⟨_, _, h1⟩ := bindE h1
  obtain ⟨_, _, h1⟩ := bindE h1
  cases h1
  exact ⟨rfl, rfl⟩

theorem oneEquation_list (p : Where) : Whole (KeepsList tOf) (oneEquation (Cl := Cl) K9.atS p) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [oneEquation] at h
  obtain ⟨q, hq, h⟩ := bindE h
  obtain ⟨o, ho, h⟩ := bindE h
  cases h
  obtain ⟨g1, -⟩ := atS_get (there_some hq)
  obtain ⟨d1, -⟩ := door_keeps ho
  exact keepsList_set g1 _ (by show o.L.link = _; rw [d1]) (by show o.L.list.nt = _; rw [d1])

theorem closing_list (P : Close.Par) : Whole (KeepsList tOf) (K9.closing (Cl := Cl) P) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  obtain ⟨r, hr, rfl⟩ := Keeps.emap_ok h
  exact fun I L hL => keepsList_putLive s { s.live with frame := r.frame } I L hL

theorem shut_list (p : Where) (piece : ℕ) : Whole (KeepsList tOf) (K9.shut (Cl := Cl) p piece) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  obtain ⟨L, hL, h⟩ := bindE h
  cases h
  exact keepsList_putLink (there_some hL) (there_some hL) rfl rfl

theorem closeOf_list (p : K9.Where) (P : Close.Par) :
    ∀ b ∈ K9.closeOf (Cl := Cl) p P, Whole (KeepsList tOf) b := by
  intro b hb
  unfold K9.closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact oneEquation_list p
  · exact closing_list P
  · exact shut_list p _

theorem batch_list (p : K9.Where) {claims : S → Except String (List Claim × S)}
    (hcl : FnCl (KeepsList tOf) claims) : Whole (KeepsList tOf) (K9.batch K9.atS p claims) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  simp only [batch] at h
  obtain ⟨t₁, h1, h⟩ := bindE h
  have a1 : KeepsList tOf s t₁ := by
    simp only [drawAlone] at h1
    split at h1
    · obtain ⟨q, hq, h1⟩ := bindE h1
      obtain ⟨chi, _, h1⟩ := bindE h1
      obtain ⟨o, ho, h1⟩ := bindE h1
      cases h1
      obtain ⟨g1, -⟩ := atS_get (there_some hq)
      obtain ⟨d2, d3⟩ := drawn_nt ho
      exact keepsList_set g1 _ d2 d3
    · cases h1
  have a2 : KeepsList tOf t₁ s' := by
    simp only [adds] at h
    obtain ⟨s₀, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨x, hx, h⟩ := bindE h
    obtain ⟨q, hq, h⟩ := bindE h
    obtain ⟨F, _, h⟩ := bindE h
    cases h
    obtain ⟨g1, -⟩ := atS_get (there_some hq)
    exact keepsList_trans _ _ _ (hcl t₁ x hx) (keepsList_set g1 _ rfl rfl)
  exact keepsList_trans _ _ _ a1 a2

/-! ## K2's places -/

section
open VerifiableInference.Desc.First.K2

theorem k2_list (p : P2) : Whole (KeepsList tOf) (codeSwitchKind (Cl := Cl) p) :=
  ⟨fun s rs gs s' h => keepsList_of_lk
    (LinkJoin.k2_link_kept (show decideWith _ p s rs gs = .ok s' from h)),
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

theorem headFrontQ_list (tl : HTailF2) : Fn (KeepsList tOf) (headFrontQ tl) := by
  intro s s' h
  unfold headFrontQ at h
  split at h
  · exact nomatch h
  · rename_i hb
    split at h
    · exact nomatch h
    · obtain ⟨x, _, h⟩ := Keeps.ebind_ok h
      obtain ⟨s₁, h1, h⟩ := Keeps.ebind_ok h
      have hB : s.atBetween = true := by simpa using hb
      have e1 : s.enterHead tl = s₁ := ((S.unmarked_ok _ _).1 h1).1
      unfold S.enterHead at e1
      rw [if_pos hB] at e1
      rw [← e1] at h
      dsimp only at h
      rw [← Except.ok.inj h]
      exact keepsList_none rfl

theorem headOpenQ_list (P : HeadPar) (hT : P.X.Tp.nt = tOf P.l) :
    Fn (KeepsList tOf) (headOpenQ P) := by
  intro s s' h
  obtain ⟨a2, st, f, mine, L, out, y, cov, s₁, b, q⟩ := (headOpenQ_iff P s s').1 h
  obtain ⟨_, ⟨b', hb', ho⟩, _⟩ := headOpenOpens P s s' h
  obtain ⟨_, _, hL, _⟩ := Johnson.Desc.First.Walk.Law.front_ok q.front
  have hb2 : b' = { b with
      L := L
      F := Johnson.Desc.First.Walk.emptySlots
        (Johnson.Desc.First.Walk.weightsAtZero { trees := P.X.Fp.trees }) P.hp.ns } := by
    have e := hb'
    rw [q.out'] at e
    injection e with e
    exact e.symm
  have hlink : s'.link? = some L := by
    unfold S.link?
    rw [hb']
    simp only [ho, if_true]
    rw [hb2]
  exact keepsList_laid hlink (by rw [hL]; exact hT)

theorem finishFrontQ_list : Fn (KeepsList tOf) finishFrontQ := by
  intro s s' h
  unfold finishFrontQ at h
  split at h
  · exact nomatch h
  · split at h
    · exact nomatch h
    · split at h
      · obtain ⟨s₁, _, h⟩ := Keeps.ebind_ok h
        split at h
        · rw [← Except.ok.inj h]
          exact keepsList_none rfl
        · exact nomatch h
      · exact nomatch h
      · exact nomatch h

theorem finishBehindQ_list : Fn (KeepsList tOf) finishBehindQ := by
  intro s s' h
  unfold finishBehindQ at h
  split at h
  · obtain ⟨m, _, rfl⟩ := Keeps.emap_ok h
    exact keepsList_none rfl
  · exact nomatch h

end

/-! ## The seat -/

/-- **THE SENTENCE IS HANDED ON BY EVERY MAKER OF THE FIRST CHAIN's FRONT.** -/
theorem seatKeeps_list :
    SeatKeeps (KeepsList tOf) (TpOk tOf) (fun P => P.X.Tp.nt = tOf P.l) where
  refl := keepsList_refl
  trans := keepsList_trans
  frames := fun hB h => framesOf_list hB h
  k1First := fun q gp _ => firstAtS_list q gp
  k1Later := fun _ _ l _ m a _ => commitAtS_list _ l m a
  reads := fun h => whole_list (readsQuietAt_lk h)
  k3 := fun c r X cs' sh' a _ h => whole_list (theStated_lk c r X cs' sh' a h)
  k4 := fun p => whole_list (blockAtC_lk p)
  k5 := fun W l g bf _ h => whole_list (k5AtN_lk W l g bf h)
  k6 := fun h => whole_list (seatedClaims_lk h)
  k7 := fun W l => whole_list (k7Of_lk W l)
  k8 := fun p => whole_list (k8Whole_lk p)
  k11 := fun P => whole_list (headMerge11_lk P)
  closeOf := closeOf_list
  batch := fun p _ hf => batch_list p hf
  k2 := fun p _ => k2_list p
  front := headFrontQ_list
  openQ := headOpenQ_list
  finFront := finishFrontQ_list
  finBehind := finishBehindQ_list

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.keepsList_refl
#print axioms VerifiableInference.Desc.First.K8.Honest.keepsList_trans
#print axioms VerifiableInference.Desc.First.K8.Honest.keepsList_of_lk
#print axioms VerifiableInference.Desc.First.K8.Honest.keepsList_none
#print axioms VerifiableInference.Desc.First.K8.Honest.keepsList_laid
#print axioms VerifiableInference.Desc.First.K8.Honest.whole_list
#print axioms VerifiableInference.Desc.First.K8.Honest.keepsList_putLink
#print axioms VerifiableInference.Desc.First.K8.Honest.keepsList_puts
#print axioms VerifiableInference.Desc.First.K8.Honest.keepsList_set
#print axioms VerifiableInference.Desc.First.K8.Honest.keepsList_putLive
#print axioms VerifiableInference.Desc.First.K8.Honest.zeroAt_tp
#print axioms VerifiableInference.Desc.First.K8.Honest.frameAt_tp
#print axioms VerifiableInference.Desc.First.K8.Honest.layFront_list
#print axioms VerifiableInference.Desc.First.K8.Honest.openAtt_list
#print axioms VerifiableInference.Desc.First.K8.Honest.openLay_list
#print axioms VerifiableInference.Desc.First.K8.Honest.openLayZero_list
#print axioms VerifiableInference.Desc.First.K8.Honest.clearWith_list
#print axioms VerifiableInference.Desc.First.K8.Honest.tailHead_list
#print axioms VerifiableInference.Desc.First.K8.Honest.framesOf_list
#print axioms VerifiableInference.Desc.First.K8.Honest.commitStep_nt
#print axioms VerifiableInference.Desc.First.K8.Honest.commitAtS_list
#print axioms VerifiableInference.Desc.First.K8.Honest.firstAtS_list
#print axioms VerifiableInference.Desc.First.K8.Honest.readsLay_lk
#print axioms VerifiableInference.Desc.First.K8.Honest.readsHead_lk
#print axioms VerifiableInference.Desc.First.K8.Honest.readsAtt_lk
#print axioms VerifiableInference.Desc.First.K8.Honest.readsBlockAt_lk
#print axioms VerifiableInference.Desc.First.K8.Honest.readsQuietAt_lk
#print axioms VerifiableInference.Desc.First.K8.Honest.k7Of_lk
#print axioms VerifiableInference.Desc.First.K8.Honest.drawn_nt
#print axioms VerifiableInference.Desc.First.K8.Honest.oneEquation_list
#print axioms VerifiableInference.Desc.First.K8.Honest.closing_list
#print axioms VerifiableInference.Desc.First.K8.Honest.shut_list
#print axioms VerifiableInference.Desc.First.K8.Honest.closeOf_list
#print axioms VerifiableInference.Desc.First.K8.Honest.batch_list
#print axioms VerifiableInference.Desc.First.K8.Honest.k2_list
#print axioms VerifiableInference.Desc.First.K8.Honest.headFrontQ_list
#print axioms VerifiableInference.Desc.First.K8.Honest.headOpenQ_list
#print axioms VerifiableInference.Desc.First.K8.Honest.finishFrontQ_list
#print axioms VerifiableInference.Desc.First.K8.Honest.finishBehindQ_list
#print axioms VerifiableInference.Desc.First.K8.Honest.seatKeeps_list
#print axioms VerifiableInference.Desc.First.K8.Honest.ListInv
#print axioms VerifiableInference.Desc.First.K8.Honest.KeepsList
#print axioms VerifiableInference.Desc.First.K8.Honest.TpOk
