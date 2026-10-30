-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/FreshMild.lean: every sub-protocol that the proof file's first chain lays in front of the last
segment's end keeps a relation R on the statement, for every R that meets `StMild`.

Why a new form. The library's two forms of "what a relation on the statement owes" (`GroundKeeps`,
Johnson/Desc/GroundKeeps.lean; `GroundQuiet`, Johnson/Desc/GroundQuiet.lean) both ask that a bare call of the plain
function that marks a message as spent as a mask keeps R; the first asks the same of "sampled in another statement". A
relation that says "nobody was spent" or "nobody was sampled without an answer" cannot meet that. The sub-protocols in
front of the last segment's end never make these calls on their own: only the closing of a segment spends a message, and
it does so right behind the beginning of its proximity test.

  `GroundMild R`      reflexive, transitive, and seven plain functions keep R (not: spend, adopt, sampled elsewhere)
  `StMild R`          `GroundMild R`, and the whole effect of a closing keeps R
  `bat_unmarked`, `closing_stU`, `closeFrame_stU`   a closing's yes: its group bore no mark in front
  `seatKeeps_mild`    `StMild R` gives `Meaning.K2.SeatKeeps (ByS R)` (Johnson/IMR/SeatKeeps.lean)

How. The lemmas whose names end in Md are copies, made by a program, of the library's lemmas of the same names without
these two letters (Johnson/Desc/K1/Keeps.lean, KeepsAtS.lean; the code switch's Keeps.lean, KeepsWhole.lean,
SendsOn.lean (folder Tw/K2C); Johnson/Goal/Meaning/RecGrows.lean; Johnson/Desc/K13/Law/StatementSeated.lean;
Johnson/Desc/AtSeats/Fit/TidyRow.lean; four of Johnson/Desc/GroundKeeps.lean), with the new structure's name in the old
one's place; no proof is changed. They stand in their sources' namespaces. Written by hand: the two structures, the three
lemmas on the closing, `closing_byMd`, `pendingRowO_rowByMd`, `seatKeeps_mild`.

Limits. Nothing on the sub-protocols behind the last segment's end. The sources are imported and not changed.
-/
import Johnson.Desc.K13.Law.StatementSeated
import Johnson.Desc.K1.KeepsAtS
import Johnson.Goal.Meaning.RecGrows
import Johnson.Desc.AtSeats.Fit.TidyRow
import Johnson.Desc.First.Close.Law.StBehind
import Johnson.IMR.SeatKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Ground
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain

/-- What a relation on statements owes: it is reflexive and transitive, and nine of the plain
functions keep it. Three plain functions are left out: the marking of a message as spent as a mask,
the taking over of another chain's messages, and the sampling in another statement. -/
structure GroundMild (R : Statement → Statement → Prop) : Prop where
  refl : ∀ T, R T T
  trans : ∀ {A B C}, R A B → R B C → R A C
  newGroup : ∀ {L : Type} (d d' : DState L) (code maskCode n : Nat),
    newGroupP d code maskCode = some (n, d') → R d.st d'.st
  recv : ∀ {L : Type} (ft : Nat) (d d' : DState L) (sent : Array OracleNotice) (ids : Array Nat),
    recvP ft d sent = some (ids, d') → R d.st d'.st
  admit : ∀ {L : Type} (d d' : DState L) (o : Nat) (rows : Array OnBytes.Row),
    admitP d o rows = some d' → R d.st d'.st
  join : ∀ {L : Type} (d d' : DState L) (g o : Nat) (kept : Bool),
    joinP d g o kept = some d' → R d.st d'.st
  addRow : ∀ {L : Type} (d d' : DState L) (g : Nat) (row : OnBytes.Row),
    addRowP d g row = some d' → R d.st d'.st
  takeMask : ∀ {L : Type} (d d' : DState L) (o n : Nat),
    takeMaskP d o = some (n, d') → R d.st d'.st
  closeLedger : ∀ {L : Type} (d d' : DState L) (o : Nat), closeLedgerP d o = some d' → R d.st d'.st

variable {R : Statement → Statement → Prop} {L : Type}

theorem GroundMild.addRowsFrom (H : GroundMild R) (g : Nat) (rows : List OnBytes.Row) :
    ∀ (d d' : DState L), addRowsFrom g rows d = some d' → R d.st d'.st := by
  induction rows with
  | nil =>
    intro d d' h
    simp only [Ground.addRowsFrom, Option.some.injEq] at h
    subst h
    exact H.refl _
  | cons row l ih =>
    intro d d' h
    simp only [Ground.addRowsFrom] at h
    cases h1 : addRowP d g row with
    | none => simp [h1] at h
    | some e =>
      simp only [h1, Option.bind_some] at h
      exact H.trans (H.addRow d e g row h1) (ih e d' h)

theorem GroundMild.addRows (H : GroundMild R) (d d' : DState L) (g : Nat)
    (rows : List OnBytes.Row) (h : addRowsP d g rows = some d') : R d.st d'.st := by
  unfold addRowsP at h
  split at h
  · exact H.addRowsFrom g rows d d' h
  · cases h

theorem GroundMild.takeMasksInto (H : GroundMild R) (o : Nat) (count : Nat) :
    ∀ (d d' : DState L) (acc : Array Nat) (r : List Nat),
      takeMasksInto o count d acc = some (r, d') → R d.st d'.st := by
  induction count with
  | zero =>
    intro d d' acc r h
    simp only [Ground.takeMasksInto, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact H.refl _
  | succ n ih =>
    intro d d' acc r h
    simp only [Ground.takeMasksInto] at h
    split at h
    · cases h
    · rename_i i e h1
      exact H.trans (H.takeMask d e o i h1) (ih e d' _ r h)

theorem GroundMild.takeMasks (H : GroundMild R) (d d' : DState L) (o count : Nat) (r : List Nat)
    (h : takeMasksP d o count = some (r, d')) : R d.st d'.st :=
  H.takeMasksInto o count d d' #[] r h

end VerifiableInference.Desc.Ground

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Slice
open VerifiableInference.Desc.Ground (GroundMild)

/-- What a relation on statements owes so that every sub-protocol in front of the last segment's end
keeps it: the seven plain functions, and the whole effect of a closing: the proximity test begins at
a group that is there and bears no mark, and one message is marked as spent. -/
structure StMild (R : Statement → Statement → Prop) : Prop where
  ground : GroundMild R
  closed : ∀ (T : Statement) (g : Nat) (G : Group) (id : Nat), T.groups[g]? = some G →
    G.inRun = false → R T (VerifiableInference.Desc.First.Close.spent (begun T g G) id)

end VerifiableInference.Desc.K13.Law

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc.First.Pend (pendingRowO pendingRowO_iff takeEntry nextEntry)
open VerifiableInference.Desc.Ground (GroundMild TidyStay groundQuiet_tidy tidyStay_begun takeMaskP
  takeMaskL)

theorem row_of_quietMd {R : Statement → Statement → Prop} (H : GroundMild R) (lay : WsLay) (im : ℕ)
    (o : WsForkOut) (n : ℕ) (lin : LinShape) (T : Statement) (r : TensorRow)
    (os' : Array OnBytes.Oracle) (h : pendingRowO lay im o n lin T.oracles = .ok (r, os')) :
    R T { T with oracles := os' } := by
  obtain ⟨-, -, -, -, first, last, -, -, -, -, -, Gamma, -, g, -, l, hl, c, l', ht, -, hos⟩ :=
    (pendingRowO_iff lay im o n lin T.oracles os' r).1 h
  let d : _root_.Desc.Plain.DState Unit :=
    { st := T, book := { trees := #[], place := #[] }, roots := 0, opened := [], loc := () }
  unfold takeEntry at ht
  split at ht
  · rename_i hc
    simp only [Option.some.injEq, Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    obtain ⟨x, hx, hxl⟩ := Option.bind_eq_some_iff.1 hl
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
    have hk : takeMaskP d im = some (nextEntry l.rows l.logRows (2 ^ l.logRows) l.next,
        { d with st := { T with oracles := os' } }) := by
      unfold takeMaskP
      have hok : Ground.ok (takeMaskL d.st im) = true := by
        simp [Ground.ok, takeMaskL, Ground.has, d, hx, hxl, hc.1, hc.2]
      rw [if_pos hok]
      show ((T.oracles[im]?).bind (·.ledger)).map _ = _
      rw [hl]
      simp only [Option.map_some, nextEntry_eq, hos, d]
    exact H.takeMask d _ im _ hk
  · cases ht

end VerifiableInference.Desc.K13.Law

namespace VerifiableInference.Desc.First.Close
open OnBytes OnBytes.Slice OnBytes.Means

/-- A yes of the batching at a closing: the group bore no mark. -/
theorem bat_unmarked {S : Statement} {g : Nat} {e : Fmt.Entry} {r : Fmt.RoundView}
    {y : GroupRow × GroupLayout × Statement} (h : bat S g e r = .ok y) {G : Group}
    (hG : S.groups[g]? = some G) : G.inRun = false := by
  unfold bat at h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨p, k1, h⟩ := ok_bind h
  have k1 := got_ok k1
  unfold Ground.beginRunP at k1
  split at k1
  · rename_i hok
    have hG2 : (onSt S).st.groups[g]? = some G := hG
    simp only [Ground.ok, Ground.beginRunL, List.all_cons, List.all_nil, Bool.and_eq_true,
      Bool.and_true] at hok
    obtain ⟨-, h2, -⟩ := hok
    rw [hG2] at h2
    simpa [Ground.has] using h2
  · cases k1

/-- The statement behind a yes of the closing, and that the group bore no mark. -/
theorem closing_stU {P : Plan} {S S' : Statement} {g : Nat} {mask : Option Nat}
    {rs : List Fmt.RoundView} {out : SingleRows} (h : closing P S g mask rs = .ok (out, S')) :
    ∃ G id, mask = some id ∧ S.groups[g]? = some G ∧ G.inRun = false ∧
      S' = spent (begun S g G) id := by
  obtain ⟨G, id, e1, e2, e3⟩ := closing_st h
  refine ⟨G, id, e1, e2, ?_, e3⟩
  unfold closing at h
  split at h
  · obtain ⟨m, -, h⟩ := ok_bind h
    obtain ⟨p, k1, h⟩ := ok_bind h
    exact bat_unmarked k1 e2
  · exact absurd h (by simp)

/-- The same of the frame's closing. -/
theorem closeFrame_stU {owed : Option Nat} {f : ReqFrame} {S : Statement} {es : List Fmt.Entry}
    {rs : List Fmt.RoundView} {x : ReqFrame × Statement} (h : closeFrame owed f S es rs = .ok x) :
    ∃ G id, f.mask = some id ∧ S.groups[f.group]? = some G ∧ G.inRun = false ∧
      x.2 = spent (begun S f.group G) id := by
  unfold closeFrame at h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨L, -, h⟩ := ok_bind h
  obtain ⟨Gf, -, h⟩ := ok_bind h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨y, kc, h⟩ := ok_bind h
  obtain ⟨G, id, e1, e2, e3, e4⟩ := closing_stU (out := y.1) (S' := y.2) kc
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨G, id, e1, e2, e3, e4⟩

end VerifiableInference.Desc.First.Close

namespace VerifiableInference.Desc.K1.Rel
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First.Send (joinOwnP joinAll)
open VerifiableInference.Desc.Ground (GroundMild By)
open VerifiableInference.Desc.Keeps (Decides)

variable {L Cl : Type} {R : Statement → Statement → Prop}

theorem laid_keepsMd (H : GroundMild R) (codes : Codes) (seeds : List (List E × E)) (l : List
    (Nat × OracleShape))
    (ys : List E) (d d' : DState L) (h : Laid codes seeds l ys d d') : R d.st d'.st := by
  induction h with
  | done d => exact H.refl _
  | pass o s l ys d d' h0 h ih => exact ih
  | lay o s l ys d d₁ d' h0 hs hy ha h ih => exact H.trans (H.admit _ _ _ _ ha) ih

theorem decideSend_keepsMd (H : GroundMild R) (P : Par) (owed : Option Nat) (d : DState L)
    (rs : List Fmt.RoundView)
    (y : Array Nat × DState L) (h : decideSend P owed d rs = .ok y) : R d.st y.2.st := by
  unfold decideSend at h
  split at h
  · obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
    obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
    obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
    obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
    obtain ⟨x, h5, h⟩ := (bind_ok _ _ _).1 h
    obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
    obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
    obtain ⟨e, h8, h⟩ := (bind_ok _ _ _).1 h
    have hp : (x.1, e) = y := by simpa [pure, Except.pure] using h
    subst hp
    exact H.trans (H.recv _ d x.2 _ x.1 ((named_ok _ _ _).1 h5))
      (laid_keepsMd H _ _ _ _ _ _ (layRows_ok _ _ _ _ _ _ h8))
  · cases h

theorem joinAll_keepsMd (H : GroundMild R) (p : GPar) (g : Nat) (l : List (ReqMessage × Nat)) : ∀
    (d d' : DState L),
    joinAll groundG p g l d = some d' → R d.st d'.st := by
  induction l with
  | nil =>
    intro d d' h
    cases h
    exact H.refl _
  | cons x l ih =>
    intro d d' h
    cases hj : (groundG (L := L)).join p d g x.2 (decide (0 < x.1.life)) with
    | none => simp [joinAll, hj] at h
    | some e =>
      simp only [joinAll, hj, Option.bind_some] at h
      exact H.trans (H.join d e g x.2 _ hj) (ih e d' h)

theorem joinOwnP_keepsMd (H : GroundMild R) (p : GPar) (d : DState L) (f : ReqFrame)
    (sent : List ReqMessage)
    (ids : Array Nat) (y : ReqFrame × DState L) (h : joinOwnP groundG p d f sent ids = some y) :
    R d.st y.2.st := by
  unfold joinOwnP at h
  split at h
  · cases hj : joinAll groundG p f.group (zipT sent ids.toList) d with
    | none => simp [hj] at h
    | some e =>
      simp only [hj, Option.map_some, Option.some.injEq] at h
      subst h
      exact joinAll_keepsMd H _ _ _ _ _ hj
  · cases h

theorem sendOwn_keepsMd (H : GroundMild R) (P : Par) :
    Decides (By R fun s : Owing (DState (Array Nat)) => s.held.st) (sendOwn (Cl := Cl) P) := by
  intro s rs _ s' h
  obtain ⟨x, h1, h2⟩ := Keeps.emap_ok (x := decideSend P s.owed s.held rs) h
  subst h2
  exact decideSend_keepsMd H _ _ _ _ _ h1

theorem laterOwn_keepsMd (H : GroundMild R) (P : Par) (owed : Option Nat) (c : ChainCheck)
    (w : DState Unit)
    (rs : List Fmt.RoundView) (y : ChainCheck × DState Unit) (h : laterOwn P owed c w rs = .ok y) :
    R w.st y.2.st := by
  unfold laterOwn at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases hd : decideSend P owed w rs with
        | error e => simp [hd] at h
        | ok x =>
          simp only [hd] at h
          split at h
          · cases h
          · rename_i z hz
            cases h
            exact H.trans (decideSend_keepsMd H _ _ _ _ _ hd) (joinOwnP_keepsMd H _ _ _ _ _ _ hz)

theorem commitOwn_keepsMd (H : GroundMild R) (P : Par) (link moment : Nat) (arrays : Option
    (List Nat)) :
    Decides (By R fun s : Owing (L3.St (DState Unit)) => s.held.w.st)
      (commitOwn (Cl := Cl) P link moment arrays) := by
  intro s rs _ s' h
  simp only [commitOwn] at h
  split at h
  · split at h
    · cases h
    · obtain ⟨x, h1, h2⟩ := Keeps.emap_ok h
      subst h2
      exact commitStep_keeps (fun w : DState Unit => w.st) _
        (fun c w rs y hy => laterOwn_keepsMd H P s.owed c w rs y hy) _ _ _ _ h1
  · cases h

end VerifiableInference.Desc.K1.Rel

namespace VerifiableInference.Desc.K1.Rel
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First.Send (joinOwnP joinAll)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (GroundMild By)
open VerifiableInference.Desc.Keeps (Decides)

variable {L Cl : Type} {R : Statement → Statement → Prop}

theorem firstOwn_keepsMd (H : GroundMild R) (P : Par) (owed : Option Nat) (c : ChainCheck)
    (d : DState Unit)
    (rs : List Fmt.RoundView) (y : ChainCheck × DState Unit) (h : firstOwn P owed c d rs = .ok y) :
    R d.st y.2.st := by
  unfold firstOwn at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨g, d₁⟩, h1, h⟩ := (bind_ok _ _ _).1 h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨ids, d₂⟩, h2, h⟩ := (bind_ok _ _ _).1 h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨f₂, d₃⟩, h3, h⟩ := (bind_ok _ _ _).1 h
  cases h
  exact H.trans (H.trans (H.newGroup d d₁ _ _ g ((named_ok _ _ _).1 h1))
    (decideSend_keepsMd H _ _ _ _ _ h2)) (joinOwnP_keepsMd H _ _ _ _ _ _ ((named_ok _ _ _).1 h3))

theorem sendAtS_keepsMd (H : GroundMild R) (P : Par) : Decides (By R fun s : S => s.st) (sendAtS
    (Cl := Cl) P) := by
  intro s rs gs s' h
  simp only [sendAtS] at h
  split at h
  · split at h
    · obtain ⟨y, h1, h2⟩ := Keeps.emap_ok h
      subst h2
      exact sendOwn_keepsMd (Cl := Cl) H P _ _ _ _ h1
    · cases h
  · cases h

theorem commitAtS_keepsMd (H : GroundMild R) (P : Par) (link moment : Nat) (arrays : Option
    (List Nat)) :
    Decides (By R fun s : S => s.st) (commitAtS (Cl := Cl) P link moment arrays) := by
  intro s rs gs s' h
  simp only [commitAtS] at h
  split at h
  · obtain ⟨y, h1, h2⟩ := Keeps.emap_ok h
    subst h2
    show R s.st (((laid s y.held.w).putLink y.held.L).putFork y.held.F).st
    rw [putFork_st, putLink_st]
    exact commitOwn_keepsMd (Cl := Cl) H P link moment arrays _ _ _ _ h1
  · cases h

theorem firstAtS_keepsMd (H : GroundMild R) (q : Params.First) (gp : GPar) :
    Decides (By R fun s : S => s.st) (firstSegmentOpening (Cl := Cl) q gp) := by
  intro s rs _ s' h
  simp only [firstSegmentOpening] at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨c, d⟩, h1, h⟩ := (bind_ok _ _ _).1 h
  cases h
  exact firstOwn_keepsMd H _ _ _ _ _ _ h1
end VerifiableInference.Desc.K1.Rel

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (SwIn SwOut switchBehind switchNotices sendByL8 closeLedgerG joinG addRowsG
    newGroupG dOf firstFront
  finishFront firstBehind)
open VerifiableInference.Desc.Ground (GroundMild)

variable {R : Statement → Statement → Prop}

theorem closeLedgerG_keepsMd (H : GroundMild R) {S S' : Statement} {o : Nat} (h : closeLedgerG S o =
    .ok S') : R S S' := by
  unfold closeLedgerG at h
  split at h
  · rename_i d hd
    cases h
    exact H.closeLedger (dOf S) d o hd
  · cases h

theorem joinG_keepsMd (H : GroundMild R) {S S' : Statement} {g o : Nat} {kept : Bool} (h : joinG S g
    o kept = .ok S') :
    R S S' := by
  unfold joinG at h
  split at h
  · rename_i d hd
    cases h
    exact H.join (dOf S) d g o kept hd
  · cases h

theorem addRowsG_keepsMd (H : GroundMild R) {S S' : Statement} {g : Nat} {rows : List OnBytes.Row}
    (h : addRowsG S g rows = .ok S') : R S S' := by
  unfold addRowsG at h
  split at h
  · rename_i d hd
    cases h
    exact H.addRows (dOf S) d g rows hd
  · cases h

theorem newGroupG_keepsMd (H : GroundMild R) {S S' : Statement} {c m g : Nat} (h : newGroupG S c m =
    .ok (S', g)) :
    R S S' := by
  unfold newGroupG at h
  split at h
  · rename_i g' d hd
    cases h
    exact H.newGroup (dOf S) d c m _ hd
  · cases h

theorem joins_keepMd (H : GroundMild R) {α : Type} (f : Statement → α → Except String Statement)
    (hf : ∀ S a S', f S a = .ok S' → R S S') : ∀ (l : List α) (S S' : Statement),
        l.foldlM f S = .ok S' → R S S'
  | [], S, S', h => by
    cases h
    exact H.refl _
  | a :: l, S, S', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨T, h1, h2⟩ := bindOk h
    exact H.trans (hf _ _ _ h1) (joins_keepMd H f hf l T S' h2)

theorem switchBehind_keepsMd (H : GroundMild R) {i : SwIn} {o : SwOut} (h : switchBehind i = .ok o) :
    R i.st o.st := by
  obtain ⟨c, y, S1, S2, S3, rows, b⟩ := switchBehind_inv h
  have h1 : R i.st S1 := by
    have hl := b.hLedger
    split at hl
    · exact closeLedgerG_keepsMd H hl
    · cases hl
      exact H.refl _
  have h2 : R S1 S2 := joinG_keepsMd H b.hJoinG
  have h3 : R S2 S3 := by
    have hk := b.hJoinKept
    rw [← Array.foldlM_toList] at hk
    exact joins_keepMd H _ (fun _ _ _ e => joinG_keepsMd H e) _ _ _ hk
  have h4 : R S3 o.st := addRowsG_keepsMd H b.hAdded
  exact H.trans h1 (H.trans h2 (H.trans h3 h4))

theorem firstFront_keepsMd (H : GroundMild R) {S : Statement} {f : ReqFrame} {x : _root_.Tw.K2.Front}
    (h : firstFront S f = .ok x) : R S x.st := by
  obtain ⟨L, G, S', g, a⟩ := (_root_.Tw.K2.firstFront_iff S f x).1 h
  rw [a.out]
  exact newGroupG_keepsMd H a.opened

theorem finishFront_keepsMd (H : GroundMild R) {S : Statement} {f : ReqFrame} {x :
    _root_.Tw.K2.Front}
    (h : finishFront S f = .ok x) : R S x.st := by
  obtain ⟨G, S', g, a⟩ := (_root_.Tw.K2.finishFront_iff S f x).1 h
  rw [a.out]
  exact newGroupG_keepsMd H a.opened

theorem firstBehind_keepsMd (H : GroundMild R) {S : Statement} {x : _root_.Tw.K2.Front} {s :
    Switched} {plain : List E}
    {S' : Statement} {f : ReqFrame} {mine : Array Nat} (h : firstBehind S x s plain = .ok (S', f,
        mine)) : R S S' := by
  obtain ⟨mask, a⟩ := (_root_.Tw.K2.firstBehind_iff S x s plain S' f mine).1 h
  exact joins_keepMd H _ (fun _ _ _ e => joinG_keepsMd H e) _ _ _ a.joins

theorem yes_keepsMd (H : GroundMild R) {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat ×
           List UInt64))} {s' : S}
    (h : decideWith sendByL8 p s rs gs = .ok s') :
    ∃ (r₁ r₂ : Fmt.RoundView) (x : _root_.Tw.K2.Front), ∃ ids sd an took d', rs = [r₁, r₂] ∧
      Desc.Plain.sendP (Desc.Plain.groundG : Desc.Plain.Ground Unit) ⟨p.samples, p.firstTree⟩ false
        ⟨x.st, s.book, s.roots, [], ()⟩ (switchNotices x.T x.others) r₁ r₂ = some (ids, sd, an,
            took, d') ∧
      R s.st x.st ∧ R d'.st s'.st := by
  have key : ∀ {f : ReqFrame} {x : _root_.Tw.K2.Front} {r₁ r₂ : Fmt.RoundView} {w : SwOut} {roots : Nat},
      _root_.Tw.K2.switchE switchBehind (par9 p) sendByL8 ⟨s.st, s.book, s.roots, f, [],
          s.noneWaits⟩ x r₁ r₂ (flat p gs) =
        .ok (w, roots) →
      ∃ ids sd an took d',
          Desc.Plain.sendP (Desc.Plain.groundG : Desc.Plain.Ground Unit) ⟨p.samples,
              p.firstTree⟩ false
        ⟨x.st, s.book, s.roots, [], ()⟩ (switchNotices x.T x.others) r₁ r₂ = some (ids, sd, an,
            took, d') ∧
      R d'.st w.st := by
    intro f x r₁ r₂ w roots hw
    obtain ⟨y, k⟩ := switchE_inv hw
    obtain ⟨ids, took, d', hs, rfl⟩ := (sendByL8_iff _ _ _ _ _ _ _ _ _).1 k.hSend
    obtain ⟨_, _, sd, an, hx⟩ := (sendOpen_iff _ _ _ _ _ _ _ _ _ _ _).1 hs
    exact ⟨ids, sd, an, took, d', hx, switchBehind_keepsMd H k.hBehind⟩
  rcases (stands _ _ _ _ _ _ h) with ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩
  · obtain ⟨r₁, r₂, x, w, roots, S', f, mine, rfl, k⟩ := link_inv hp h
    obtain ⟨ids, sd, an, took, d', h1, h2⟩ := key k.hSwitch
    refine ⟨r₁, r₂, x, ids, sd, an, took, d', rfl, h1, firstFront_keepsMd H k.hFront, ?_⟩
    rw [k.hOut]
    exact H.trans h2 (firstBehind_keepsMd H k.hBehind)
  · obtain ⟨r₁, r₂, a, G, w, roots, rfl, k⟩ := head_inv hp h
    obtain ⟨ids, sd, an, took, d', h1, h2⟩ := key k.hSwitch
    refine ⟨r₁, r₂, _, ids, sd, an, took, d', rfl, h1, H.refl _, ?_⟩
    rw [k.hOut]
    exact h2
  · obtain ⟨r₁, r₂, a, G, w, roots, rfl, k⟩ := finish_inv hp h
    obtain ⟨ids, sd, an, took, d', h1, h2⟩ := key k.hSwitch
    refine ⟨r₁, r₂, _, ids, sd, an, took, d', rfl, h1, H.refl _, ?_⟩
    rw [k.hOut]
    exact h2

end VerifiableInference.Desc.First.K2

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (sendByL8)
open VerifiableInference.Desc.Ground (GroundMild groundKeeps_grows)

variable {R : Statement → Statement → Prop}

theorem sampleLoop_keepsMd (H : GroundMild R) {p : Desc.Plain.GPar} {codes : Codes}
    {seeds : List SampleSeed} :
    ∀ (l : List (Nat × OracleShape)) (ys : List E) (d d' : Desc.Plain.DState Unit) (left : List E),
      Desc.Plain.sampleLoop Desc.Plain.groundG p codes seeds l ys d = some (d', left) → R d.st d'.st
  | [], ys, d, d', left, h => by
    simp only [Desc.Plain.sampleLoop, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact H.refl _
  | (o, s) :: l, ys, d, d', left, h => by
    simp only [Desc.Plain.sampleLoop] at h
    split at h
    · cases h
    · rename_i rows ys' _
      split at h
      · cases h
      · rename_i d₁ ha
        exact H.trans (H.admit d d₁ o rows ha) (sampleLoop_keepsMd H l ys' d₁ d' left h)

theorem sendP_keepsAllMd (H : GroundMild R) {p : Desc.Plain.GPar} {own : Bool}
    {d d' : Desc.Plain.DState Unit} {sent : Array OracleNotice} {r₁ r₂ : Fmt.RoundView} {ids sd an need}
    (h : Desc.Plain.sendP Desc.Plain.groundG p own d sent r₁ r₂ = some (ids, sd, an, need, d')) :
    R d.st d'.st := by
  unfold Desc.Plain.sendP at h
  obtain ⟨⟨ids', d₁⟩, h1, h⟩ := optBindB h
  dsimp only at h
  obtain ⟨shapes, _, h⟩ := optBindB h
  obtain ⟨seeds, _, h⟩ := optBindB h
  obtain ⟨an', _, h⟩ := optBindB h
  split at h
  · obtain ⟨⟨d₂, left⟩, h2, h⟩ := optBindB h
    dsimp only at h
    split at h
    · cases h
      exact H.trans (H.recv _ _ _ _ _ h1) (sampleLoop_keepsMd H _ _ _ _ _ h2)
    · cases h
  · cases h

theorem yes_keeps_wholeMd (H : GroundMild R) {p : P2} {s : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {s' : S}
    (h : decideWith sendByL8 p s rs gs = .ok s') : R s.st s'.st := by
  obtain ⟨r₁, r₂, x, ids, sd, an, took, d', _, hs, h1, h2⟩ := yes_keepsMd H h
  exact H.trans h1 (H.trans (sendP_keepsAllMd H hs) h2)

end VerifiableInference.Desc.First.K2

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block roundlessBlock)
open _root_.Tw.K2 (SwIn SwOut switchBehind switchNotices sendByL8 firstFront)
open VerifiableInference.Desc.Ground (GroundMild)

variable {R : Statement → Statement → Prop}

theorem headOpenQ_keepsMd (H : GroundMild R) {P : HeadPar} {s s' : S} (h : headOpenQ P s = .ok s') :
    R s.st s'.st := by
  obtain ⟨a, st, f, mine, L, out, y, cov, s₁, b, k⟩ := (headOpenQ_iff P s s').1 h
  rw [k.out']
  exact firstBehind_keepsMd H k.behind

theorem finishFrontQ_keepsMd (H : GroundMild R) {s s' : S} (h : finishFrontQ s = .ok s') : R s.st
    s'.st := by
  obtain ⟨G, x, s₁, a, k⟩ := (finishFrontQ_iff s s').1 h
  rw [k.out]
  exact finishFront_keepsMd H k.front

end VerifiableInference.Desc.First.K2

namespace Meaning.K2

open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Ground (GroundMild By groundKeeps_grows)
open VerifiableInference.Desc.K9
open Johnson.Desc.First.Walk

variable {Cl : Type} {R : Statement → Statement → Prop}

theorem batch_byMd (H : GroundMild R) (p : Where)
    {claims : S → Except String (List Claim × S)} (hcl : FnCl (ByS R) claims) :
    Decides (ByS R) (batch atS p claims) := by
  intro s rs gs s' h
  simp only [batch] at h
  obtain ⟨t₁, h1, h⟩ := bindE h
  exact H.trans (drawAlone_by H.refl p s rs gs t₁ h1)
    (adds_by p p.piece "the segment's" hcl t₁ [] [] s' h)

theorem takeN_byMd {X : Type} (H : GroundMild R) (o : Nat) : ∀ (n : Nat) (d : St X)
    (acc : List Nat) (y : List Nat × St X), takeN o n d acc = .ok y → R d.st y.2.st
  | 0, d, acc, y, h => by
    cases h
    exact H.refl _
  | n + 1, d, acc, y, h => by
    unfold takeN at h
    obtain ⟨x, hx, h⟩ := bindE h
    exact H.trans (H.takeMask d x.2 o x.1 (there_some hx)) (takeN_byMd H o n x.2 _ y h)

theorem asRow_byMd {X : Type} (H : GroundMild R) {Rw : ReqRows} {f : ReqFrame} {q : Equation}
    {d : St X} {y : Row × St X} (h : asRow Rw f q d = .ok y) : R d.st y.2.st := by
  unfold asRow at h
  obtain ⟨row, _, h⟩ := bindE h
  dsimp only at h
  split at h
  · cases h
    exact H.refl _
  · obtain ⟨m, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨o, _, h⟩ := bindE h
    obtain ⟨x, hx, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    cases h
    exact takeN_byMd H o _ d [] x hx

theorem door_byMd {X : Type} (H : GroundMild R) {owed : RowsOwed} {laid : Option Nat}
    {L : LinkCtx} {F : Fork} {d : St X} {o : Out X} (h : door owed laid L F d = .ok o) :
    R d.st o.d.st := by
  unfold door at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨x, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨y, hy, h⟩ := bindE h
  obtain ⟨d', hd, h⟩ := bindE h
  cases h
  exact H.trans (asRow_byMd H hy) (H.addRow y.2 d' _ y.1 (there_some hd))

theorem oneEquation_byMd (H : GroundMild R) (p : Where) :
    Decides (ByS R) (oneEquation (Cl := Cl) atS p) := by
  intro s rs gs s' h
  simp only [oneEquation] at h
  obtain ⟨q, hq, h⟩ := bindE h
  obtain ⟨o, ho, h⟩ := bindE h
  cases h
  show R s.st o.d.st
  rw [← (atS_get (there_some hq)).2]
  exact door_byMd H ho

end Meaning.K2

namespace Meaning.K2

open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Ground (GroundMild By)
open VerifiableInference.Desc.First.Close (closeFrame ok_bind got_ok bat_inv_layout)
open VerifiableInference.Desc.K13.Law (StMild)

variable {Cl : Type} {R : Statement → Statement → Prop}

theorem by_reflMd (K : StMild R) (s : S) : ByS R s s := K.ground.refl _

theorem by_transMd (K : StMild R) (a b c : S) (h : ByS R a b) (k : ByS R b c) : ByS R a c :=
  K.ground.trans h k

theorem by_of_stMd (K : StMild R) {s t : S} (e : t.st = s.st) : ByS R s t := by
  show R s.st t.st
  rw [e]
  exact K.ground.refl _

theorem by_of_entersMd (K : StMild R) {s s' : S} (q : Enters s s') : ByS R s s' := by_of_stMd K q.1

theorem by_of_quietMd (K : StMild R) {s s' : S} (q : Quiet s s') : ByS R s s' := by_of_entersMd K q.1

theorem whole_byMd (K : StMild R) {b : Block S Cl} (W : Whole Quiet b) : Whole (ByS R) b :=
  whole_mono (fun _ _ => by_of_quietMd K) W

theorem fn_byMd (K : StMild R) {f : S → Except String S} (h : Fn Quiet f) : Fn (ByS R) f :=
  fun s t k => by_of_quietMd K (h s t k)

theorem fn_byEMd (K : StMild R) {f : S → Except String S} (h : Fn Enters f) : Fn (ByS R) f :=
  fun s t k => by_of_entersMd K (h s t k)

theorem closing_byMd (K : StMild R) (P : Close.Par) : Whole (ByS R) (K9.closing (Cl := Cl) P) := by
  refine ⟨fun s rs gs s' h => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  obtain ⟨r, hr, rfl⟩ := Keeps.emap_ok h
  obtain ⟨x, hx, rfl⟩ := Keeps.emap_ok hr
  obtain ⟨G, id, -, hG, hu, e⟩ := Close.closeFrame_stU hx
  have w : R (K9.recOf s).st x.2 := by
    rw [e]
    exact K.closed _ _ _ _ hG hu
  exact w

open Johnson.Desc.First.Walk

theorem pendingRowO_rowByMd (K : StMild R) (lay : WsLay) (lin : LinShape) :
    RowBy R fun im w n os => Pend.pendingRowO lay im w n lin os :=
  fun im w n T r os' h =>
    VerifiableInference.Desc.K13.Law.row_of_quietMd K.ground lay im w n lin T r os' h

theorem clearWith_byMd (K : StMild R) (X : LinkPub) (counts : S → Except String Unit)
    (left : S → Option WsForkOut) {row : RowFn} (hrow : RowBy R row) :
    Fn (ByS R) (clearWith X counts left row) := fun s t h => by
  show R s.st t.st
  unfold clearWith at h
  split at h
  · obtain ⟨-, -, h⟩ := bindE h
    obtain ⟨p, -, h⟩ := bindE h
    split at h
    · rw [leaveLink_st h]
      exact K.ground.refl _
    · split at h
      · cases h
      · rename_i r os hr
        rw [leaveLink_st h]
        exact hrow _ _ _ s.st _ _ hr
  · cases h

theorem tailHead_byMd (K : StMild R) (X : LinkPub) (lay : WsLay) (lin : LinShape) :
    Fn (ByS R) (Close.tailHead X lay lin) := clearWith_byMd K _ _ _ (pendingRowO_rowByMd K lay lin)

open Johnson.Desc.First.Walk.Seat in
theorem framesOf_byMd (K : StMild R) {built : Array Stages.LinkH} {first : Params.First}
    {W : Verify.Public} {fs : List LinkFrame} (h : framesOf built first W = .ok fs) : ∀ f ∈ fs,
    Fn (ByS R) f.lay ∧ Fn (ByS R) f.opened ∧ Fn (ByS R) f.clear := by
  intro f hf
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact ⟨fn_byMd K (layFront_quiet l), fun s t k => by cases k; exact by_reflMd K s,
        tailHead_byMd K _ _ _⟩
  · split at e
    · split at e
      · cases e
      · cases e
        exact ⟨fn_byMd K (layFront_quiet 0), fn_byEMd K (openLayZero_enters _ _ _),
          clearWith_byMd K _ _ _ (pendingRowO_rowByMd K _ _)⟩
    · split at e
      · cases e
      · cases e
        exact ⟨fn_byMd K (layFront_quiet l), fn_byEMd K (openAtt_enters _),
          clearWith_byMd K _ _ _ (pendingRowO_rowByMd K _ _)⟩
      · cases e
        exact ⟨fn_byMd K (layFront_quiet l), fn_byEMd K (openLay_enters _),
          clearWith_byMd K _ _ _ (pendingRowO_rowByMd K _ _)⟩

theorem firstAtS_byMd (K : StMild R) (q : Params.First) (gp : _root_.Desc.Plain.GPar) :
    Whole (ByS R) (K1.firstSegmentOpening (Cl := Cl) q gp) :=
  ⟨K1.Rel.firstAtS_keepsMd K.ground q gp, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

theorem laterAt_byMd (K : StMild R) (q : Params.First) (gp : _root_.Desc.Plain.GPar)
    (link piece moment : Nat) (arrays : Option (List Nat)) :
    Whole (ByS R) (K1.laterAt (Cl := Cl) q gp link piece moment arrays) :=
  ⟨K1.Rel.commitAtS_keepsMd K.ground _ link moment arrays, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩

theorem closeOf_byMd (K : StMild R) (p : K9.Where) (P : Close.Par) :
    ∀ b ∈ K9.closeOf (Cl := Cl) p P, Whole (ByS R) b := by
  intro b hb
  unfold K9.closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact ⟨oneEquation_byMd (Cl := Cl) K.ground p, (fun _ hc => nomatch hc),
      (fun _ hc => nomatch hc)⟩
  · exact closing_byMd K P
  · exact whole_mono (fun _ _ q => by_of_entersMd K q.1) (shut_still p _)

theorem batchW_byMd (K : StMild R) (p : K9.Where)
    {claims : S → Except String (List Claim × S)} (hcl : FnCl (ByS R) claims) :
    Whole (ByS R) (K9.batch K9.atS p claims) :=
  ⟨batch_byMd K.ground p hcl, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

theorem k2_byMd (K : StMild R) (p : K2.P2) : Whole (ByS R) (K2.codeSwitchKind (Cl := Cl) p) :=
  ⟨fun _ _ _ _ h => K2.yes_keeps_wholeMd K.ground h, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩

theorem headFrontQ_byMd (K : StMild R) (tl : HTailF2) : Fn (ByS R) (K2.headFrontQ tl) :=
  fun s t h => by
  obtain ⟨x, s₁, a, k⟩ := (K2.headFrontQ_iff tl s t).1 h
  show R s.st t.st
  rw [k.out]
  exact K2.firstFront_keepsMd K.ground k.front

theorem headOpenQ_byMd (K : StMild R) (P : K2.HeadPar) : Fn (ByS R) (K2.headOpenQ P) :=
  fun _ _ h => K2.headOpenQ_keepsMd K.ground h

theorem finishFrontQ_byMd (K : StMild R) : Fn (ByS R) K2.finishFrontQ :=
  fun _ _ h => K2.finishFrontQ_keepsMd K.ground h

theorem finishBehindQ_byMd (K : StMild R) : Fn (ByS R) K2.finishBehindQ :=
  fun _ _ h => by_of_stMd K (K2.finishBehindQ_st h)

theorem seatKeeps_mild (K : StMild R) : SeatKeeps (ByS R) where
  refl := by_reflMd K
  trans := by_transMd K
  frames := fun _ h => framesOf_byMd K h
  k1First := fun q gp _ => firstAtS_byMd K q gp
  k1Later := fun q gp l p m a _ => laterAt_byMd K q gp l p m a
  reads := fun h => whole_byMd K (readsQuietAt_quiet h)
  k3 := fun c r X cs' sh' a _ h => whole_byMd K (theStated_quiet c r X cs' sh' a h)
  k4 := fun p => whole_byMd K (blockAtC_quiet p)
  k5 := fun W l g bf _ h => whole_byMd K (k5AtN_quiet W l g bf h)
  k6 := fun h => whole_byMd K (seatedClaims_quiet h)
  k7 := fun W l => whole_byMd K (k7Of_quiet W l)
  k8 := fun p => whole_byMd K (k8Whole_quiet p)
  k11 := fun P => whole_byMd K (headMerge11_quiet P)
  closeOf := closeOf_byMd K
  batch := fun p _ hf => batchW_byMd K p hf
  k2 := fun p _ => k2_byMd K p
  front := headFrontQ_byMd K
  openQ := fun P _ => headOpenQ_byMd K P
  finFront := finishFrontQ_byMd K
  finBehind := finishBehindQ_byMd K

end Meaning.K2

#print axioms VerifiableInference.Desc.K1.Rel.laid_keepsMd
#print axioms VerifiableInference.Desc.K1.Rel.decideSend_keepsMd
#print axioms VerifiableInference.Desc.K1.Rel.joinAll_keepsMd
#print axioms VerifiableInference.Desc.K1.Rel.joinOwnP_keepsMd
#print axioms VerifiableInference.Desc.K1.Rel.sendOwn_keepsMd
#print axioms VerifiableInference.Desc.K1.Rel.laterOwn_keepsMd
#print axioms VerifiableInference.Desc.K1.Rel.commitOwn_keepsMd
#print axioms VerifiableInference.Desc.K1.Rel.firstOwn_keepsMd
#print axioms VerifiableInference.Desc.K1.Rel.sendAtS_keepsMd
#print axioms VerifiableInference.Desc.K1.Rel.commitAtS_keepsMd
#print axioms VerifiableInference.Desc.K1.Rel.firstAtS_keepsMd
#print axioms VerifiableInference.Desc.First.K2.closeLedgerG_keepsMd
#print axioms VerifiableInference.Desc.First.K2.joinG_keepsMd
#print axioms VerifiableInference.Desc.First.K2.addRowsG_keepsMd
#print axioms VerifiableInference.Desc.First.K2.newGroupG_keepsMd
#print axioms VerifiableInference.Desc.First.K2.joins_keepMd
#print axioms VerifiableInference.Desc.First.K2.switchBehind_keepsMd
#print axioms VerifiableInference.Desc.First.K2.firstFront_keepsMd
#print axioms VerifiableInference.Desc.First.K2.finishFront_keepsMd
#print axioms VerifiableInference.Desc.First.K2.firstBehind_keepsMd
#print axioms VerifiableInference.Desc.First.K2.yes_keepsMd
#print axioms VerifiableInference.Desc.First.K2.sampleLoop_keepsMd
#print axioms VerifiableInference.Desc.First.K2.sendP_keepsAllMd
#print axioms VerifiableInference.Desc.First.K2.yes_keeps_wholeMd
#print axioms VerifiableInference.Desc.First.K2.headOpenQ_keepsMd
#print axioms VerifiableInference.Desc.First.K2.finishFrontQ_keepsMd
#print axioms Meaning.K2.batch_byMd
#print axioms Meaning.K2.takeN_byMd
#print axioms Meaning.K2.asRow_byMd
#print axioms Meaning.K2.door_byMd
#print axioms Meaning.K2.oneEquation_byMd
#print axioms Meaning.K2.by_reflMd
#print axioms Meaning.K2.by_transMd
#print axioms Meaning.K2.by_of_stMd
#print axioms Meaning.K2.by_of_entersMd
#print axioms Meaning.K2.by_of_quietMd
#print axioms Meaning.K2.whole_byMd
#print axioms Meaning.K2.fn_byMd
#print axioms Meaning.K2.fn_byEMd
#print axioms Meaning.K2.clearWith_byMd
#print axioms Meaning.K2.tailHead_byMd
#print axioms Meaning.K2.framesOf_byMd
#print axioms Meaning.K2.firstAtS_byMd
#print axioms Meaning.K2.laterAt_byMd
#print axioms Meaning.K2.closeOf_byMd
#print axioms Meaning.K2.batchW_byMd
#print axioms Meaning.K2.k2_byMd
#print axioms Meaning.K2.headFrontQ_byMd
#print axioms Meaning.K2.headOpenQ_byMd
#print axioms Meaning.K2.finishFrontQ_byMd
#print axioms Meaning.K2.finishBehindQ_byMd
#print axioms VerifiableInference.Desc.K13.Law.row_of_quietMd
#print axioms VerifiableInference.Desc.Ground.GroundMild.addRowsFrom
#print axioms VerifiableInference.Desc.Ground.GroundMild.addRows
#print axioms VerifiableInference.Desc.Ground.GroundMild.takeMasksInto
#print axioms VerifiableInference.Desc.Ground.GroundMild.takeMasks
#print axioms VerifiableInference.Desc.First.Close.bat_unmarked
#print axioms VerifiableInference.Desc.First.Close.closing_stU
#print axioms VerifiableInference.Desc.First.Close.closeFrame_stU
#print axioms Meaning.K2.closing_byMd
#print axioms Meaning.K2.pendingRowO_rowByMd
#print axioms Meaning.K2.seatKeeps_mild
