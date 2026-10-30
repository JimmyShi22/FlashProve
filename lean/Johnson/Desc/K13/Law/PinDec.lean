-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/PinDec.lean: a member for the pin of Johnson/Desc/K13/Law/PinA.lean: the
witness's matrix and its mask entries of one message are what a total decoder makes of the
STATEMENT, the record and the oracles. Statements with their proofs.

A decoder with samples (such as `Cb.Ood.decMinS`, Cb/Gen/OodDecMin.lean) takes a table of words, a
seed and the answers. The words are read off the oracles; the seed and the answers lie in the
record. So it is a function of the statement, not of the oracles alone.
Main names:
  `pinOfA idx rw decA`, `pinOfA_det`: the pin; it fixes the matrix and the message's mask entries,
    whatever the function decA is.
  `sampleOf`, `SameAll`, `SameSampled n`: what of a statement a decoder with samples may read: the
    codes, and of each message (of each below the number n) its shape, its mark "sampled", its
    sample rows and its pad.
  `ReadsA base n decA`: decA reads the stored table, the trees sent in front of the number base, and
    that part of the record below n, alone. The fence n is there because a sending appends messages:
    behind it the statement has messages that it had not in front.
  `takeMasks_same`, `batt_same`, `atM3_same`, `rows_same`, `rowsB_same`: kind K13's blocks leave
    that part of the record as it is.
  `atM3_goodIn_decA`: **the law of the batching's joined block at that pin**: no premise on the pin
    is left but `ReadsA`.
  `pinOfA_backR`: the pin goes back over the block behind W's commitment.
  `decNext`, `not_readsA_next`: a try: a function that reads the ledger's next free entry, which the
    batching turns, does not meet `ReadsA`.
Used of `verify-on-bytes`: nothing beside what Johnson/Desc/K13/Law/Good2.lean names. Of the ground:
`takeMaskP`, `takeMasksP`, `newGroupP`, `joinP`, `addRowsP`.

What is not claimed. That a decoder of the release's codes, read off a statement, meets `ReadsA`: no
such reading is typed. That a witness which matters has the pin: where two messages of a list have
the answers a total decoder returns one of them, and the law says nothing of the other; that there
is no such clash is to be shown, and priced, where the message is sent and where the pin is closed.
That W's commitment leaves the older messages' part of the record: not shown here. The premise of
`jointA` (Johnson/Desc/K13/Law/PinA.lean) that the pin goes back over W's commitment is not met at
`pinOfA`, and cannot be: the pin is unguarded, and a sending appends messages. The form to carry on
at this pin is `joint_decA` (Johnson/Desc/K13/Law/K1Pin.lean), which asks in its
conditions that n is at most the number of messages.

-/
import Johnson.Desc.K13.Law.PinA
import Johnson.Desc.K13.Law.OneRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice Iop Run
open OnBytes.Flat OnBytes.Maker
open OnBytes.Params (LinShape)
open VerifiableInference.Desc.Ground (takeMaskP takeMasksInto takeMasksP newGroupP joinP addRowsP)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame Piece)

variable {Cl W : Type} {nR : ℕ}

/-- The witness's matrix and its mask entries of the message idx are what a function makes of the
statement. -/
def pinOfA {F : Frame} {k : ℕ} (idx : ℕ) (rw : W → Wit GE nR k)
    (decA : S × F.E.Str → Wit GE nR k) : S × F.E.Str → W → Prop :=
  fun a w => AgreeAt idx (rw w) (decA a)

/-- **It fixes the matrix and the message's mask entries**, whatever the function is. -/
theorem pinOfA_det {F : Frame} {k : ℕ} (idx : ℕ) (rw : W → Wit GE nR k)
    (decA : S × F.E.Str → Wit GE nR k) (a : S × F.E.Str) (w w' : W)
    (ha : a.1.out.indexMasks = idx) (h : pinOfA idx rw decA a w) (h' : pinOfA idx rw decA a w') :
    AgreeAt a.1.out.indexMasks (rw w) (rw w') := by
  rw [ha]
  exact h.trans h'.symm

/-- What of a message a decoder with samples may read. -/
def sampleOf (St : Statement) (j : ℕ) :
    Option (OracleShape × Bool × Array OnBytes.Row × List (OnBytes.Part × ℕ)) :=
  (St.oracles[j]?).map fun x => (x.shape, x.sampled, x.sampleRows, x.pad)

/-- Two statements have the same codes, and each message the same shape, mark, sample rows and pad.
-/
def SameAll (St St' : Statement) : Prop :=
  St'.codes = St.codes ∧ ∀ j, sampleOf St' j = sampleOf St j

/-- A statement and itself. -/
theorem SameAll.refl (St : Statement) : SameAll St St := ⟨rfl, fun _ => rfl⟩

/-- One after the other. -/
theorem SameAll.trans {A B C : Statement} (h : SameAll A B) (h' : SameAll B C) :
    SameAll A C := ⟨h'.1.trans h.1, fun j => (h'.2 j).trans (h.2 j)⟩

/-- The same of the messages below the number n alone. -/
def SameSampled (n : ℕ) (St St' : Statement) : Prop :=
  St'.codes = St.codes ∧ ∀ j, j < n → sampleOf St' j = sampleOf St j

/-- What holds of all messages holds of those below n. -/
theorem SameAll.below {St St' : Statement} (h : SameAll St St') (n : ℕ) : SameSampled n St St' :=
  ⟨h.1, fun j _ => h.2 j⟩

/-- A turn of one message that leaves these four fields. -/
theorem same_modify (St : Statement) (o : ℕ) (f : OnBytes.Oracle → OnBytes.Oracle)
    (hf : ∀ x, ((f x).shape, (f x).sampled, (f x).sampleRows, (f x).pad) =
      (x.shape, x.sampled, x.sampleRows, x.pad)) (j : ℕ) :
    ((St.oracles.modify o f)[j]?).map (fun x => (x.shape, x.sampled, x.sampleRows, x.pad)) =
      sampleOf St j := by
  unfold sampleOf
  rw [Array.getElem?_modify]
  split
  · rw [Option.map_map]
    exact congrArg (fun g => Option.map g St.oracles[j]?) (funext hf)
  · rfl

/-- The taking of one mask entry turns a ledger alone. -/
theorem takeMask_same {d d' : St} {o n : ℕ} (h : takeMaskP d o = some (n, d')) :
    SameAll d.st d'.st := by
  unfold takeMaskP at h
  split at h
  · cases hl : (d.st.oracles[o]?).bind (·.ledger) with
    | none =>
      rw [hl] at h
      cases h
    | some l =>
      rw [hl] at h
      have e : d' = _ := (congrArg Prod.snd (Option.some.inj h)).symm
      subst e
      exact ⟨rfl, same_modify d.st o _ fun _ => rfl⟩
  · cases h

/-- So does the taking of several. -/
theorem takeMasksInto_same (o : ℕ) : ∀ (n : ℕ) (d : St) (acc : Array ℕ) (t : List ℕ × St),
    takeMasksInto o n d acc = some t → SameAll d.st t.2.st
  | 0, d, acc, t, h => by
    have e : some (acc.toList, d) = some t := h
    rw [← Option.some.inj e]
    exact SameAll.refl _
  | n + 1, d, acc, t, h => by
    unfold takeMasksInto at h
    cases hm : takeMaskP d o with
    | none =>
      rw [hm] at h
      cases h
    | some q =>
      obtain ⟨i, d'⟩ := q
      rw [hm] at h
      exact (takeMask_same hm).trans (takeMasksInto_same o n d' _ t h)

/-- The same, as the text calls it. -/
theorem takeMasks_same {d : St} {o n : ℕ} {t : List ℕ × St} (h : takeMasksP d o n = some t) :
    SameAll d.st t.2.st := takeMasksInto_same o n d #[] t h

/-- The batching's text leaves that part of the record. -/
theorem batt_same {owed : Johnson.Desc.First.ForkGround.RowsOwed} {k n : ℕ}
    {pile : List TensorRow} {ledger : ℕ} {d : St} {rs : List Fmt.RoundView} {out : TensorRow × St}
    (h : batt owed k n pile ledger d rs = .ok out) : SameAll d.st out.2.st := by
  obtain ⟨_, _, _, t, _, _, _, _, _, _, _, ht, _, _, _, rfl⟩ := batt_ok h
  exact takeMasks_same ht

/-- **The batching's joined block leaves that part of the record.** -/
theorem atM3_same {P : Where} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s') : SameAll s.st s'.st := by
  have h' : (((frontB (Cl := Cl) atS P).decide s _ _).bind fun s₁ =>
      (claimCombinationBlock (Cl := Cl) atS P).decide s₁ _ _).bind (fun s₂ =>
                      (quietB (Cl := Cl) atS P).decide s₂ _ _) = .ok s' := h
  obtain ⟨s₂, h12, h3⟩ := ebind_ok.1 h'
  obtain ⟨s₁, h1, h2⟩ := ebind_ok.1 h12
  obtain ⟨rfl, _⟩ := enter_eq (frontB_ok atS P h1)
  obtain ⟨p, out, hp, hb, rfl⟩ := battB_ok atS P h2
  obtain ⟨p', msg, hp', rfl⟩ := quietB_ok atS P h3
  obtain rfl := Option.some.inj hp
  obtain rfl := Option.some.inj hp'
  exact batt_same hb

/-- A new group leaves it. -/
theorem newGroup_same {d : St} {c z : ℕ} {b : ℕ × St} (h : newGroupP d c z = some b) :
    SameAll d.st b.2.st := by
  unfold newGroupP at h
  split at h
  · obtain rfl := Option.some.inj h
    exact ⟨rfl, fun _ => rfl⟩
  · cases h

/-- A joining turns a group and a message's list of groups alone. -/
theorem join_same {d d' : St} {g o : ℕ} {kept : Bool} (h : joinP d g o kept = some d') :
    SameAll d.st d'.st := by
  unfold joinP at h
  split at h
  · cases hG : d.st.groups[g]? with
    | none =>
      rw [hG] at h
      cases h
    | some G =>
      rw [hG] at h
      obtain rfl := Option.some.inj h
      exact ⟨rfl, same_modify d.st o _ fun _ => rfl⟩
  · cases h

/-- So do joinings in a row. -/
theorem joinAll_same (g : ℕ) : ∀ (l : List ℕ) (d d' : St), joinAll g l d = .ok d' →
    SameAll d.st d'.st
  | [], d, d', h => by
    rw [pure_ok.1 h]
    exact SameAll.refl _
  | o :: l, d, d', h => by
    simp only [joinAll, bind_ok, there_ok] at h
    obtain ⟨d₁, h1, h2⟩ := h
    exact (join_same h1).trans (joinAll_same g l d₁ d' h2)

/-- The text behind W's commitment leaves that part of the record. -/
theorem rows_same {Sh : LinShape} {claim : LinClaim} {ids : Array ℕ} {d : St} {o : LinFirst × St}
    (h : rows Sh claim ids d = .ok o) : SameAll d.st o.2.st := by
  simp only [rows_is, bind_ok, there_ok, pure_ok] at h
  obtain ⟨w, _, b, hb, d₁, h1, d₂, h2, split, _, d₃, h3, mask, _, row, _, d₄, h4, rfl⟩ := h
  obtain ⟨_, _, _, hst⟩ := addRows_one h4
  have e3 : SameAll d.st d₃.st := by
    have e2 := ((newGroup_same hb).trans (joinAll_same _ _ _ _ h1)).trans (join_same h2)
    split at h3
    · exact e2.trans (join_same h3)
    · rw [← Option.some.inj h3]
      exact e2
  refine e3.trans ?_
  show SameAll d₃.st d₄.st
  rw [hst]
  exact ⟨rfl, fun _ => rfl⟩

/-- **The block behind W's commitment leaves that part of the record.** -/
theorem rowsB_same {P : Where} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (rowsB (Cl := Cl) atS P).decide s rs gs = .ok s') : SameAll s.st s'.st := by
  obtain ⟨m₀, l, o, owed, _, _, hrows, rfl⟩ := rowsB_at h
  exact rows_same hrows

/-- decA reads the stored table, the trees sent in front of the number base, and of the record the
codes and, of each message below the number n, the shape, mark, sample rows and pad, alone. a: in
front; b: behind. -/
def ReadsA {F : Frame} {k : ℕ} (base n : ℕ) (decA : S × F.E.Str → Wit GE nR k) : Prop :=
  ∀ a b : S × F.E.Str, b.2.1 = a.2.1 → (∀ j x, j < base → colAt F b.2 j x = colAt F a.2 j x) →
    SameSampled n a.1.st b.1.st → decA b = decA a

/-- What a piece puts out has the oracles that the piece leaves. General in the piece. -/
theorem out_imp {T : Type} {C : PQ.CK} {F : Frame} (p : Piece C F T Cl W) {a b : T × F.E.Str}
    {τ : Tr (uLT C p.ds)} (h : p.ior.red.out a τ = some b) : b.2 = p.ior.imp a.2 τ := by
  have hb' : (p.ior.out a.1 a.2 τ).map (fun xo => (xo, p.ior.imp a.2 τ)) = some b := h
  cases ho : p.ior.out a.1 a.2 τ with
  | none =>
    rw [ho] at hb'
    cases hb'
  | some xo =>
    rw [ho] at hb'
    rw [← Option.some.inj hb']

/-- **The law of the batching's joined block at that pin.** -/
theorem atM3_goodIn_decA (F : Frame) (P : Where) (base : ℕ) (dZ d0 : RDT) (ds : List RDT)
    (hD : Declared P dZ d0 ds) (idx n : ℕ) (rw : W → Wit GE nR P.lin.kCol)
    (decA : S × F.E.Str → Wit GE nR P.lin.kCol) (hR : ReadsA base n decA) :
    (pieceM3 (Cl := Cl) (W := W) F P base dZ d0 ds).GoodIn (fun a => a.1.out.indexMasks = idx)
      (FrontOk P) (RowsHoldA rw (pinOfA idx rw decA)) (RowsHoldA rw (pinOfA idx rw decA)) :=
  atM3_goodInA F P base dZ d0 ds hD P.lin.kCol hD.len.symm rw _ _
    (fun a w w' ha h h' => pinOfA_det idx rw decA a w w' ha h h')
    fun a τ b w hb hw => by
      obtain ⟨rs, gs, hdec⟩ := piece_ok _ hb
      have hy := out_imp _ hb
      have e : decA b = decA a := hR a b (by rw [hy])
        (fun j x hj => by rw [hy]; exact old_kept _ _ _ j x hj) ((atM3_same hdec).below n)
      show AgreeAt idx (rw w) (decA a)
      rw [← e]
      exact hw

/-- The pin goes back over the block behind W's commitment. -/
theorem pinOfA_backR {F : Frame} (P : Where) (base n idx : ℕ) {k : ℕ} (rw : W → Wit GE nR k)
    (decA : S × F.E.Str → Wit GE nR k) (hR : ReadsA base n decA) (s s' : S) (y : F.E.Str) (w : W)
    (h : (rowsB (Cl := Cl) atS P).decide s [] [] = .ok s') (hw : pinOfA idx rw decA (s', y) w) :
    pinOfA idx rw decA (s, y) w := by
  have e : decA (s', y) = decA (s, y) :=
    hR (s, y) (s', y) rfl (fun _ _ _ => rfl) ((rowsB_same h).below n)
  show AgreeAt idx (rw w) (decA (s, y))
  rw [← e]
  exact hw

/-! ## A try: a function that reads what the batching turns -/

/-- It reads the ledger's next free entry of the message 0. -/
def decNext {F : Frame} {k : ℕ} (a : S × F.E.Str) : Wit GE nR k :=
  ⟨fun _ _ => 0,
    fun _ => ((((a.1.st.oracles[0]?).bind (·.ledger)).map (·.next)).getD 0 : ℕ)⟩

/-- A record whose one message has a ledger with the next free entry n. -/
def recNext (n : ℕ) : S :=
  { S.blank with
    st := { S.blank.st with
      oracles := #[{ (default : OnBytes.Oracle) with
        ledger := some { (default : OnBytes.Ledger) with next := n } }] } }

/-- **It does not meet `ReadsA`.** -/
theorem not_readsA_next {F : Frame} {k : ℕ} (base n : ℕ) (y : F.E.Str) :
    ¬ ReadsA (nR := nR) (k := k) base n (decNext (F := F)) := by
  intro h
  have e := h (recNext 0, y) (recNext 1, y) rfl (fun _ _ _ => rfl)
    ⟨rfl, fun j _ => by cases j <;> rfl⟩
  have e' := congrArg (fun w : Wit GE nR k => w.mask ⟨0, 0⟩) e
  have e'' : ((1 : ℕ) : GE) = ((0 : ℕ) : GE) := e'
  simp at e''

end VerifiableInference.Desc.K13.Law
