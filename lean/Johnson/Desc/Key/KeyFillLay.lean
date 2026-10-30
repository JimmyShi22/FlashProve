-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/KeyFillLay.lean: THE WITNESS's TABLES AT THE LAYING BY THE PAD's PLACES. In the filling famG (Johnson/Desc/Key/KeyFillFam.lean) arr and lay are letters; the theorems on PIN (KeyFillStrs | KeyFillNoColl | KeyFillOracles) take «the witness's table at each
seat is the message's» as a premise, met so far at a silly laying alone. Here lay is filled as Msg.lean words the field: the first table outside the tenant's pad's places, the second at them; with the same test (padB) by which the accessor Wit.tab (Sound/MsgSig.lean, at its type MsgT) chooses.
THAT THIS IS THE LAYING WHICH THE TABLES' USERS WILL HAND IS SHOWN BY NOTHING YET: arr | lay are letters in the tables' one reading. What ties it: toU_famLay (the library's padP) · layIdem_famLay · fam_hW_layAt (layAt, Johnson/Desc/Key/KeyLay.lean, names the tables and meets LaysSeat at it, under ArrOk).
(Where this and lean/THEOREM.md differ, the page holds.)
  padT · padT_inl | padT_inr   padB (Johnson/Desc/SeatAt.lean) in Tab's numbering (row + 2 ^ (row bits) · place); at a shape's entries it is the library's padP
  famLay · famLay_seat         THE LAYING · layIdem_famLay: a table laid over itself is itself (KeyLetters.LayIdem)
  toU_famLay                   read as the library's message, it is the second table's at the library's padP and the first's elsewhere
  AgreeOff                     two seats that bear ONE number hold tables that agree off BOTH pads
  fam_hW_iff                   SHARP, at every arr: some witness names the table T i at every seat JUST IF AgreeOff
  agreeOff_of_apart            free where arr is one-to-one on the seats · agree_ofU | agreeOff_of_copies | two_copies: messages of one shape that are equal off the library's padP (two_pads gives such a pair) are named by one witness under one number
  fam_hW_layAt                 layAt (Johnson/Desc/Key/KeyLay.lean) names them too, under ArrOk, and meets LaysSeat
  fam_promise_padLay           PIN ∧ hasSmp ∧ NoColl at all seats, at the rule's own oracles, AT THIS LAYING, with AgreeOff in place of a witness and a premise on it
  fam_promise_form_padLay      under public premises alone; its sample's tie still reads no record and IS MADE OF THE VERY MESSAGE AND SEED THAT IT IS TO WITNESS («meets» by fiat)
  Toy.apart · Toy.promise_padLay (closed) · Toy.no_witness (A PLANT: both members under one number, two messages that part off the pads: NO witness names both)
OBJECT: msgOf (Johnson/Desc/Msg.lean) | padB (Johnson/Desc/SeatAt.lean); the library's padP · USER: Johnson/Desc/Key/KeyFillSrc.lean (meant: whoever fills arr | lay of the tables' one reading) · LETTERS: cs · l · seat · arr · T.
NOT SAID: the tables' other readers at M := Tab (KRead's val | same | tab); that a real description's numbers and seats are these; where an extractor's tables come from. At l := [] all is true for nothing. Nothing on soundness.
-/
import Johnson.Desc.Key.KeyFillOracles
import Johnson.Desc.Key.KeyLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open Cb Johnson.Pack OnBytes.Slice Prob OnBytes.Maker

section
variable (cs : OnBytes.Codes)

/-- The pad's places, in Tab's numbering. -/
def padT (s : OnBytes.OracleShape) : OnBytes.Part → ℕ → Bool
  | .main, i => padB cs s false (i % 2 ^ k1 s) (i / 2 ^ k1 s)
  | .mask, i => padB cs s true (i % 2 ^ k2 s) (i / 2 ^ k2 s)

theorem padT_inl (s : OnBytes.OracleShape) (q : Fin s.mainRows × Fin (pMain cs s).ell) : padT cs s .main (q.1.val + 2 ^ k1 s * q.2.val) = true ↔ padP cs s (.inl q) := by
  have h1 : (q.1.val + 2 ^ k1 s * q.2.val) % 2 ^ k1 s = q.1.val := idx_mod q.1.isLt
  have h2 : (q.1.val + 2 ^ k1 s * q.2.val) / 2 ^ k1 s = q.2.val := idx_div q.1.isLt
  show padB cs s false ((q.1.val + 2 ^ k1 s * q.2.val) % 2 ^ k1 s) ((q.1.val + 2 ^ k1 s * q.2.val) / 2 ^ k1 s) = true ↔ _
  rw [h1, h2]
  exact padB_inl cs s q

theorem padT_inr (s : OnBytes.OracleShape) (q : Fin s.maskRows × Fin (pMask cs s).ell) : padT cs s .mask (q.1.val + 2 ^ k2 s * q.2.val) = true ↔ padP cs s (.inr q) := by
  have h1 : (q.1.val + 2 ^ k2 s * q.2.val) % 2 ^ k2 s = q.1.val := idx_mod q.1.isLt
  have h2 : (q.1.val + 2 ^ k2 s * q.2.val) / 2 ^ k2 s = q.2.val := idx_div q.1.isLt
  show padB cs s true ((q.1.val + 2 ^ k2 s * q.2.val) % 2 ^ k2 s) ((q.1.val + 2 ^ k2 s * q.2.val) / 2 ^ k2 s) = true ↔ _
  rw [h1, h2]
  exact padB_inr cs s q

/-- Two messages of one shape that are equal off the library's pad have tables that are equal off padT. -/
theorem agree_ofU (s : OnBytes.OracleShape) (e : ℕ) (m m' : (portOmZ cs s e).Msg) (h : ∀ j, ¬ padP cs s j → m j = m' j) (part : OnBytes.Part) (k : ℕ)
    (hk : padT cs s part k = false) : ofU cs s e m part k = ofU cs s e m' part k := by
  match part with
  | .main =>
    show (if h : k % 2 ^ k1 s < s.mainRows ∧ k / 2 ^ k1 s < (pMain cs s).ell then
      m (.inl ((⟨_, h.1⟩, ⟨_, h.2⟩) : Fin s.mainRows × Fin (pMain cs s).ell)) else 0) = (if h : k % 2 ^ k1 s < s.mainRows ∧ k / 2 ^ k1 s < (pMain cs s).ell then
      m' (.inl ((⟨_, h.1⟩, ⟨_, h.2⟩) : Fin s.mainRows × Fin (pMain cs s).ell)) else 0)
    by_cases hr : k % 2 ^ k1 s < s.mainRows ∧ k / 2 ^ k1 s < (pMain cs s).ell
    · rw [dif_pos hr, dif_pos hr]
      refine h _ fun hp => ?_
      have hb : padB cs s false (k % 2 ^ k1 s) (k / 2 ^ k1 s) = true :=
        (padB_inl cs s ((⟨_, hr.1⟩, ⟨_, hr.2⟩) : Fin s.mainRows × Fin (pMain cs s).ell)).2 hp
      have hk' : padB cs s false (k % 2 ^ k1 s) (k / 2 ^ k1 s) = false := hk
      rw [hb] at hk'
      exact nomatch hk'
    · rw [dif_neg hr, dif_neg hr]
  | .mask =>
    show (if h : k % 2 ^ k2 s < s.maskRows ∧ k / 2 ^ k2 s < (pMask cs s).ell then
      m (.inr ((⟨_, h.1⟩, ⟨_, h.2⟩) : Fin s.maskRows × Fin (pMask cs s).ell)) else 0) = (if h : k % 2 ^ k2 s < s.maskRows ∧ k / 2 ^ k2 s < (pMask cs s).ell then
      m' (.inr ((⟨_, h.1⟩, ⟨_, h.2⟩) : Fin s.maskRows × Fin (pMask cs s).ell)) else 0)
    by_cases hr : k % 2 ^ k2 s < s.maskRows ∧ k / 2 ^ k2 s < (pMask cs s).ell
    · rw [dif_pos hr, dif_pos hr]
      refine h _ fun hp => ?_
      have hb : padB cs s true (k % 2 ^ k2 s) (k / 2 ^ k2 s) = true :=
        (padB_inr cs s ((⟨_, hr.1⟩, ⟨_, hr.2⟩) : Fin s.maskRows × Fin (pMask cs s).ell)).2 hp
      have hk' : padB cs s true (k % 2 ^ k2 s) (k / 2 ^ k2 s) = false := hk
      rw [hb] at hk'
      exact nomatch hk'
    · rw [dif_neg hr, dif_neg hr]

variable (l : List (OnBytes.OracleShape × ℕ)) (seat : Fin l.length → ℕ × ℕ)

open Classical in
/-- **THE LAYING BY THE PAD's PLACES**: at a member's seat the second table at the pad's places, the first elsewhere; at no seat the first. -/
def famLay : ℕ → ℕ → Tab → Tab → Tab := fun j t m p part k =>
  if ∃ i : Fin l.length, seat i = (j, t) ∧ padT cs (l.get i).1 part k = true then p part k else m part k

theorem famLay_seat (hinj : Function.Injective seat) (i : Fin l.length) (m p : Tab) (part : OnBytes.Part) (k : ℕ) :
    famLay cs l seat (seat i).1 (seat i).2 m p part k = if padT cs (l.get i).1 part k = true then p part k else m part k := by
  classical
  show (if ∃ i' : Fin l.length, seat i' = ((seat i).1, (seat i).2) ∧ padT cs (l.get i').1 part k = true then p part k else m part k) = _
  by_cases h : padT cs (l.get i).1 part k = true
  · rw [if_pos h, if_pos ⟨i, rfl, h⟩]
  · rw [if_neg h, if_neg]
    rintro ⟨i', hi', h'⟩
    obtain rfl : i' = i := hinj hi'
    exact h h'

open Classical in
/-- **Read as the library's message: the second table's at padP, the first's elsewhere.** -/
theorem toU_famLay (hinj : Function.Injective seat) (i : Fin l.length) (m p : Tab) :
    toU cs (l.get i).1 (l.get i).2 (famLay cs l seat (seat i).1 (seat i).2 m p) =
      fun x => if padP cs (l.get i).1 x then toU cs (l.get i).1 (l.get i).2 p x else toU cs (l.get i).1 (l.get i).2 m x := by
  funext x
  match (x : (Fin (l.get i).1.mainRows × Fin (pMain cs (l.get i).1).ell) ⊕ (Fin (l.get i).1.maskRows × Fin (pMask cs (l.get i).1).ell)) with
  | .inl q =>
    show famLay cs l seat (seat i).1 (seat i).2 m p .main (q.1.val + 2 ^ k1 (l.get i).1 * q.2.val) =
      if padP cs (l.get i).1 (.inl q) then p .main (q.1.val + 2 ^ k1 (l.get i).1 * q.2.val) else m .main (q.1.val + 2 ^ k1 (l.get i).1 * q.2.val)
    rw [famLay_seat cs l seat hinj]
    by_cases h : padP cs (l.get i).1 (.inl q)
    · rw [if_pos h, if_pos ((padT_inl cs _ q).2 h)]
    · rw [if_neg h, if_neg fun h' => h ((padT_inl cs _ q).1 h')]
  | .inr q =>
    show famLay cs l seat (seat i).1 (seat i).2 m p .mask (q.1.val + 2 ^ k2 (l.get i).1 * q.2.val) =
      if padP cs (l.get i).1 (.inr q) then p .mask (q.1.val + 2 ^ k2 (l.get i).1 * q.2.val) else m .mask (q.1.val + 2 ^ k2 (l.get i).1 * q.2.val)
    rw [famLay_seat cs l seat hinj]
    by_cases h : padP cs (l.get i).1 (.inr q)
    · rw [if_pos h, if_pos ((padT_inr cs _ q).2 h)]
    · rw [if_neg h, if_neg fun h' => h ((padT_inr cs _ q).1 h')]

/-- **Two seats that bear one number hold tables that agree off both pads.** -/
def AgreeOff (arr : ℕ → ℕ → ℕ) (T : Fin l.length → Tab) : Prop :=
  ∀ i i' : Fin l.length, arr (seat i).1 (seat i).2 = arr (seat i').1 (seat i').2 → ∀ part k,
    padT cs (l.get i).1 part k = false → padT cs (l.get i').1 part k = false → T i part k = T i' part k

theorem agreeOff_of_apart (arr : ℕ → ℕ → ℕ) (T : Fin l.length → Tab) (h : ∀ i i' : Fin l.length, arr (seat i).1 (seat i).2 = arr (seat i').1 (seat i').2 → i = i') :
    AgreeOff cs l seat arr T := fun i i' e _ _ _ _ => by
  obtain rfl := h i i' e
  rfl

theorem agreeOff_of_copies (arr : ℕ → ℕ → ℕ) (s : OnBytes.OracleShape) (e : ℕ) (hl : ∀ i : Fin l.length, (l.get i).1 = s) (M : Fin l.length → (portOmZ cs s e).Msg)
    (hM : ∀ i i' : Fin l.length, arr (seat i).1 (seat i).2 = arr (seat i').1 (seat i').2 → ∀ j, ¬ padP cs s j → M i j = M i' j) :
    AgreeOff cs l seat arr fun i => ofU cs s e (M i) := fun i i' h part k h1 _ =>
  agree_ofU cs s e _ _ (hM i i' h) part k (by rw [← hl i]; exact h1)

open Classical in
/-- The witness: at a seat's pad the seat's table; as message number n, place by place, the table of some seat that bears n and has no pad there. -/
def padLayW {Cells Tok : Type} (c₀ : Cells) (t₀ : Tok) (arr : ℕ → ℕ → ℕ) (T : Fin l.length → Tab) : Wit Cells Tok Tab where
  cells := c₀
  tok := t₀
  msg := fun n part k => if h : ∃ i : Fin l.length, arr (seat i).1 (seat i).2 = n ∧ padT cs (l.get i).1 part k = false then T h.choose part k else 0
  pad := fun j t => if h : ∃ i : Fin l.length, seat i = (j, t) then T h.choose else fun _ _ => 0

theorem padLayW_pad {Cells Tok : Type} (hinj : Function.Injective seat) (c₀ : Cells) (t₀ : Tok) (arr : ℕ → ℕ → ℕ) (T : Fin l.length → Tab) (i : Fin l.length) :
    (padLayW cs l seat c₀ t₀ arr T).pad (seat i).1 (seat i).2 = T i := by
  classical
  have h : ∃ i' : Fin l.length, seat i' = ((seat i).1, (seat i).2) := ⟨i, rfl⟩
  show (if h : ∃ i' : Fin l.length, seat i' = ((seat i).1, (seat i).2) then T h.choose else fun _ _ => 0) = _
  rw [dif_pos h, choose_seat l seat hinj i h]

variable {A Cells Rec : Type} (seedIs : ∀ i : Fin l.length, A → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop)
  (arr : ℕ → ℕ → ℕ) (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : A → Option Rec)

theorem layIdem_famLay : LayIdem (famG cs l seat seedIs arr (famLay cs l seat) decT recOf) := fun j t m => by
  classical
  funext part k
  show (if ∃ i : Fin l.length, seat i = (j, t) ∧ padT cs (l.get i).1 part k = true then m part k else m part k) = m part k
  exact ite_self _

/-- **R7, SHARP: some witness names T i at every seat JUST IF two seats that bear one number agree off both pads.** -/
theorem fam_hW_iff {Tok : Type} (hinj : Function.Injective seat) (c₀ : Cells) (t₀ : Tok) (T : Fin l.length → Tab) :
    (∃ W : Wit Cells Tok Tab, ∀ i, msgOf (famG cs l seat seedIs arr (famLay cs l seat) decT recOf) W (seat i).1 (seat i).2 = T i) ↔ AgreeOff cs l seat arr T := by
  classical
  constructor
  · rintro ⟨W, hW⟩ i i' harr part k h1 h2
    have e1 : famLay cs l seat (seat i).1 (seat i).2 (W.msg (arr (seat i).1 (seat i).2)) (W.pad (seat i).1 (seat i).2) part k = T i part k := congrFun (congrFun (hW i) part) k
    have e2 : famLay cs l seat (seat i').1 (seat i').2 (W.msg (arr (seat i').1 (seat i').2)) (W.pad (seat i').1 (seat i').2) part k = T i' part k := congrFun (congrFun (hW i') part) k
    rw [famLay_seat cs l seat hinj, if_neg (by rw [h1]; exact Bool.false_ne_true)] at e1
    rw [famLay_seat cs l seat hinj, if_neg (by rw [h2]; exact Bool.false_ne_true)] at e2
    rw [← e1, ← e2, harr]
  · intro hag
    refine ⟨padLayW cs l seat c₀ t₀ arr T, fun i => ?_⟩
    funext part k
    show famLay cs l seat (seat i).1 (seat i).2 ((padLayW cs l seat c₀ t₀ arr T).msg (arr (seat i).1 (seat i).2)) ((padLayW cs l seat c₀ t₀ arr T).pad (seat i).1 (seat i).2) part k = T i part k
    rw [famLay_seat cs l seat hinj, padLayW_pad cs l seat hinj]
    by_cases h : padT cs (l.get i).1 part k = true
    · rw [if_pos h]
    · rw [if_neg h]
      have hf : padT cs (l.get i).1 part k = false := Bool.eq_false_iff.2 h
      have hex : ∃ i' : Fin l.length, arr (seat i').1 (seat i').2 = arr (seat i).1 (seat i).2 ∧ padT cs (l.get i').1 part k = false := ⟨i, rfl, hf⟩
      show (if h : ∃ i' : Fin l.length, arr (seat i').1 (seat i').2 = arr (seat i).1 (seat i).2 ∧ padT cs (l.get i').1 part k = false then T h.choose part k else 0) = T i part k
      rw [dif_pos hex]
      exact hag hex.choose i hex.choose_spec.1 part k hex.choose_spec.2 hf

/-- **A message and its later copy**: messages of one shape that are equal off the library's pad wherever their seats bear one number are named by one witness. -/
theorem two_copies {Tok : Type} (hinj : Function.Injective seat) (c₀ : Cells) (t₀ : Tok) (s : OnBytes.OracleShape) (e : ℕ) (hl : ∀ i : Fin l.length, (l.get i).1 = s)
    (M : Fin l.length → (portOmZ cs s e).Msg)
    (hM : ∀ i i' : Fin l.length, arr (seat i).1 (seat i).2 = arr (seat i').1 (seat i').2 → ∀ j, ¬ padP cs s j → M i j = M i' j) :
    ∃ W : Wit Cells Tok Tab, ∀ i, msgOf (famG cs l seat seedIs arr (famLay cs l seat) decT recOf) W (seat i).1 (seat i).2 = ofU cs s e (M i) :=
  (fam_hW_iff cs l seat seedIs arr decT recOf hinj c₀ t₀ _).2 (agreeOff_of_copies cs l seat arr s e hl M hM)

/-! ## layAt -/

open Classical in
/-- The tables by the messages' numbers. -/
def tblOf (num : Fin l.length → ℕ) (T : Fin l.length → Tab) : ℕ → Tab := fun n => if h : ∃ i : Fin l.length, num i = n then T h.choose else fun _ _ => 0

/-- **layAt names the tables and meets LaysSeat**, under ArrOk: one number, one seat. -/
theorem fam_hW_layAt (hinj : Function.Injective seat) (at_ : Where) (ks : List ℕ) (num : Fin l.length → ℕ) (hseat : ∀ i, seat i = at_ (num i))
    (hks : ∀ k ∈ ks, ∃ i, num i = k) (hnum : ∀ i, num i ∈ ks) (ha : ArrOk (famG cs l seat seedIs arr (famLay cs l seat) decT recOf) at_ ks)
    (T : Fin l.length → Tab) (w₀ : Wit Cells Unit Tab) :
    (∀ i, msgOf (famG cs l seat seedIs arr (famLay cs l seat) decT recOf) (layAt at_ ks (tblOf l num T) w₀) (seat i).1 (seat i).2 = T i) ∧
      LaysSeat at_ ks (layAt at_ ks (tblOf l num T) w₀) := by
  classical
  have hni : Function.Injective num := fun i i' e => hinj (by rw [hseat i, hseat i', e])
  have hap : SeatsApart at_ ks ks := fun k hk k' hk' e => by
    obtain ⟨i, rfl⟩ := hks k hk
    obtain ⟨i', rfl⟩ := hks k' hk'
    rw [← hseat i, ← hseat i'] at e
    rw [hinj e]
  refine ⟨fun i => ?_, laysSeat_layAt at_ ks _ w₀ hap⟩
  have h := msgOf_layAt (famG cs l seat seedIs arr (famLay cs l seat) decT recOf) at_ ks (tblOf l num T) w₀ ha (layIdem_famLay cs l seat seedIs arr decT recOf) hap (num i) (hnum i)
  rw [← hseat i] at h
  rw [h]
  have hex : ∃ i' : Fin l.length, num i' = num i := ⟨i, rfl⟩
  show (if h : ∃ i' : Fin l.length, num i' = num i then T h.choose else fun _ _ => 0) = T i
  rw [dif_pos hex, hni hex.choose_spec]

/-! ## The promise at this laying -/

variable {XI : Type} (F : FileDescription XI)

/-- **PIN AND ITS PROMISE AT ALL SEATS, AT THE RULE's OWN ORACLES, AT THE LAYING BY THE PAD's PLACES.** -/
theorem fam_promise_padLay (Fr : Frame) (hinj : Function.Injective seat) (hS : SeatFits F cs l seat) (hFr : FrameHolds cs l seat Fr)
    (uniq : ∀ i a ρ v ρ' v', seedIs i a ρ v → seedIs i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v')
    (hB : allMeet cs l = true) (y₀ : Fr.E.Str) (a : A) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg)
    (r₀ : ∀ i : Fin l.length, (OmAt cs l i).Rnd) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D)
    (hsend : ∀ i, Sendable cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i)) (hs : ∀ i, seedIs i a (ρ i) ((OmAt cs l i).Z.val (ρ i) (m₀ i)))
    (c₀ : Cells) (hag : AgreeOff cs l seat arr fun i => ofU cs (l.get i).1 (l.get i).2 (m₀ i)) :
    ∃ (W : Wit Cells Unit Tab) (y' : Fr.E.Str), y'.1 = y₀.1 ∧ ∀ i : Fin l.length,
      PIN F (famG cs l seat seedIs arr (famLay cs l seat) decT recOf) (seat i).1 (seat i).2 a (strsOf Fr y') W ∧
      hasSmp (famG cs l seat seedIs arr (famLay cs l seat) decT recOf) (seat i).1 (seat i).2 a = true ∧
      NoColl F (famG cs l seat seedIs arr (famLay cs l seat) decT recOf) (seat i).1 (seat i).2 a (strsOf Fr y') := by
  obtain ⟨W, hW⟩ := (fam_hW_iff cs l seat seedIs arr decT recOf hinj c₀ () _).2 hag
  exact ⟨W, fam_promise_at_oracles cs l seat F seedIs arr (famLay cs l seat) decT recOf Fr hinj hS hFr uniq hB y₀ a m₀ r₀ ρ hsend hs W hW⟩

/-- **UNDER PUBLIC PREMISES ALONE**, at a tie made of the message itself. -/
theorem fam_promise_form_padLay (recOf' : Unit → Option Rec) (c₀ : Cells) (Fr : Frame) (hinj : Function.Injective seat) (hS : SeatFits F cs l seat)
    (hFr : FrameHolds cs l seat Fr) (hB : allMeet cs l = true) (y₀ : Fr.E.Str) (m₀ : ∀ i : Fin l.length, (OmAt cs l i).Msg)
    (r₀ : ∀ i : Fin l.length, (OmAt cs l i).Rnd) (ρ : ∀ i : Fin l.length, (OmAt cs l i).Z.D)
    (hsend : ∀ i, Sendable cs (l.get i).1 (l.get i).2 (m₀ i, r₀ i)) (hag : AgreeOff cs l seat arr fun i => ofU cs (l.get i).1 (l.get i).2 (m₀ i)) :
    ∃ seedIs' : ∀ i : Fin l.length, Unit → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop,
      (∀ i a ρ v ρ' v', seedIs' i a ρ v → seedIs' i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v') ∧
      ∃ (W : Wit Cells Unit Tab) (y' : Fr.E.Str), y'.1 = y₀.1 ∧ ∀ i : Fin l.length,
        PIN F (famG cs l seat seedIs' arr (famLay cs l seat) decT recOf') (seat i).1 (seat i).2 () (strsOf Fr y') W ∧
        hasSmp (famG cs l seat seedIs' arr (famLay cs l seat) decT recOf') (seat i).1 (seat i).2 () = true ∧
        NoColl F (famG cs l seat seedIs' arr (famLay cs l seat) decT recOf') (seat i).1 (seat i).2 () (strsOf Fr y') := by
  have hu : ∀ (i : Fin l.length) (a : Unit) (ρ₁ : (OmAt cs l i).Z.D) (v : (OmAt cs l i).Z.S → GE) (ρ' : (OmAt cs l i).Z.D) (v' : (OmAt cs l i).Z.S → GE),
      (ρ₁ = ρ i ∧ v = (OmAt cs l i).Z.val (ρ i) (m₀ i)) → (ρ' = ρ i ∧ v' = (OmAt cs l i).Z.val (ρ i) (m₀ i)) →
      (OmAt cs l i).Z.val ρ₁ = (OmAt cs l i).Z.val ρ' ∧ v = v' := by
    rintro i _ ρ₁ v ρ' v' ⟨rfl, rfl⟩ ⟨h, rfl⟩
    exact ⟨by rw [h], rfl⟩
  exact ⟨fun i _ ρ₁ v => ρ₁ = ρ i ∧ v = (OmAt cs l i).Z.val (ρ i) (m₀ i), hu,
    fam_promise_padLay cs l seat _ arr decT recOf' F Fr hinj hS hFr hu hB y₀ () m₀ r₀ ρ hsend (fun i => ⟨rfl, rfl⟩) c₀ hag⟩

end

/-! ## The toy -/

namespace Toy

/-- The tenant's number as the message's number: one number, one seat. -/
theorem apart : ∀ i i' : Fin l.length, (fun _ t : ℕ => t) (seat i).1 (seat i).2 = (fun _ t : ℕ => t) (seat i').1 (seat i').2 → i = i' := fun i i' h => Fin.ext (by
  have h2 : 2 * i.val = 2 * i'.val := h
  omega)

/-- **CLOSED: AT THE TOY, PIN · hasSmp · NoColl AT BOTH MEMBERS, AT THE RULE's OWN ORACLES, AT THE LAYING BY THE PAD's PLACES.** -/
theorem promise_padLay {Rec : Type} (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Unit) (recOf : Unit → Option Rec) :
    ∃ seedIs' : ∀ i : Fin l.length, Unit → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop,
      (∀ i a ρ v ρ' v', seedIs' i a ρ v → seedIs' i a ρ' v' → (OmAt cs l i).Z.val ρ = (OmAt cs l i).Z.val ρ' ∧ v = v') ∧
      ∃ (W : Wit Unit Unit Tab) (y' : (FrD 1).E.Str), ∀ i : Fin l.length,
        PIN (FW 15) (famG cs l seat seedIs' (fun _ t => t) (famLay cs l seat) decT recOf) (seat i).1 (seat i).2 () (strsOf (FrD 1) y') W ∧
        hasSmp (famG cs l seat seedIs' (fun _ t => t) (famLay cs l seat) decT recOf) (seat i).1 (seat i).2 () = true ∧
        NoColl (FW 15) (famG cs l seat seedIs' (fun _ t => t) (famLay cs l seat) decT recOf) (seat i).1 (seat i).2 () (strsOf (FrD 1) y') := by
  obtain ⟨sd, hu, W, y', _, h⟩ := fam_promise_form_padLay cs l seat (fun _ t => t) decT (FW 15) recOf () (FrD 1) seat_inj fits holds meets
    ((fun _ => (0, []), fun _ => []) : (FrD 1).E.Str) (fun _ _ => 1) (fun _ _ => 0) (fun _ => Classical.arbitrary _)
    (fun _ _ => ⟨fun _ => ⟨1, map_one _⟩, fun _ => ⟨0, map_zero _⟩⟩) (agreeOff_of_apart cs l seat _ _ apart)
  exact ⟨sd, hu, W, y', h⟩

/-- Two tables that part at a place which is pad for neither member: the first main entry: 1 at the first member, 0 at the second. -/
def partT : Fin l.length → Tab := fun i _ _ => if i.val = 0 then 1 else 0

/-- **A PLANT: both members under ONE number, two tables that part off the pads: NO WITNESS NAMES BOTH.** -/
theorem no_witness {A Rec : Type} (seedIs : ∀ i : Fin l.length, A → (OmAt cs l i).Z.D → ((OmAt cs l i).Z.S → GE) → Prop)
    (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Unit) (recOf : A → Option Rec) :
    ¬ ∃ W : Wit Unit Unit Tab, ∀ i, msgOf (famG cs l seat seedIs (fun _ _ => 0) (famLay cs l seat) decT recOf) W (seat i).1 (seat i).2 = partT i := by
  intro h
  have hag := (fam_hW_iff cs l seat seedIs (fun _ _ => 0) decT recOf seat_inj () () partT).1 h
  have h01 : partT ⟨0, by decide⟩ .main 0 = partT ⟨1, by decide⟩ .main 0 := hag ⟨0, by decide⟩ ⟨1, by decide⟩ rfl .main 0 (by decide +kernel) (by decide +kernel)
  have e : (1 : GE) = 0 := h01
  exact one_ne_zero e

end Toy

end VerifiableInference.Desc.Key.Fill

#print axioms VerifiableInference.Desc.Key.Fill.padT_inl
#print axioms VerifiableInference.Desc.Key.Fill.padT_inr
#print axioms VerifiableInference.Desc.Key.Fill.agree_ofU
#print axioms VerifiableInference.Desc.Key.Fill.famLay_seat
#print axioms VerifiableInference.Desc.Key.Fill.toU_famLay
#print axioms VerifiableInference.Desc.Key.Fill.layIdem_famLay
#print axioms VerifiableInference.Desc.Key.Fill.fam_hW_iff
#print axioms VerifiableInference.Desc.Key.Fill.agreeOff_of_apart
#print axioms VerifiableInference.Desc.Key.Fill.agreeOff_of_copies
#print axioms VerifiableInference.Desc.Key.Fill.two_copies
#print axioms VerifiableInference.Desc.Key.Fill.fam_hW_layAt
#print axioms VerifiableInference.Desc.Key.Fill.fam_promise_padLay
#print axioms VerifiableInference.Desc.Key.Fill.fam_promise_form_padLay
#print axioms VerifiableInference.Desc.Key.Fill.Toy.apart
#print axioms VerifiableInference.Desc.Key.Fill.Toy.promise_padLay
#print axioms VerifiableInference.Desc.Key.Fill.Toy.no_witness
