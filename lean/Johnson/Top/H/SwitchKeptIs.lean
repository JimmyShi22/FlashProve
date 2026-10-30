-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchKeptIs.lean: back across the code switch, on plain tables: what the typed block
hands back as an old kept message stands, to its new copy and to g, as the programs' frame says.

Three files are joined. Johnson/Top/H/SwitchBack.lean: on the promise in front, where the joint in
front holds at what the block's extractor hands back, each held message's word decodes with its
sample to what the cut reads off the new messages. Johnson/Top/H/SwitchHeldSel.lean: which entries
of the new messages these are, along a map of names iJ. Johnson/Top/H/SwitchFront.lean: at the map
iJ that is written out of the programs' frame (Johnson/Top/H/SwitchMaps.lean), a table that holds
what is read along iJ at a member's slots stands in `KeptIs`: it is the new copy outside the old
pad's places, and at the old pad's places it is g's rest. Definitions, statements and proofs; no
new reasoning.
Main names:
  `tabMsg cs sh u`: a typed message of a shape as a table; 0 outside its ranges.
  `slotNum`, `slotRow`, `slotPl`: the three readings of a kept slot (a kept member with one of its
    rows): the member's number in the frame (num, a letter), the row, the member's record (plOf, a
    letter).
  `keptIs_back`: at `heldPort` (Johnson/Top/H/SwitchKept.lean) and the frame's two maps: the table
    of the held message that the closing reads off new messages n stands in `KeptIs` to the tables
    of message 1 + num and of message 0 of n.
  `KeptRecOK`: what is asked of a member's record: its number of rows; its pad's indices differ and
    lie in the member's table: `RecOK` (Johnson/Top/H/SwitchKeptRec.lean) at this caller's numbers.
  `back_keptIs`: with SwitchBack.lean: there is u to which the held word decodes, with that.
  `back_keptIs_sent`: the same of the old message's word as it was sent, where the slot of the open
    word is its reading.
Limits: those of the three files. num, plOf, the frame W and `Fit` are letters or premises: nothing
here says that a frame of the programs meets them. That the slot of the open word is the reading of
the old word is a premise of the last statement; of what the typed fold puts out the library shows
it for `G.P` nonempty and under its hc, if `Hd.Laws` (`LdFoldD.Tw`, Cb/Req1/LdSegKit.lean;
`ldGroup_seg_word`, Cb/Ld/LdGroupSegProofs.lean). Nothing on what fixes a copy's pad, on a witness
of a table of joints, or on soundness.

-/
import Johnson.Top.H.SwitchKeptRec
import Johnson.Top.H.SwitchHeldSel
import Johnson.Top.H.SwitchBack
import Cb.Req1.LdSegProofsFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Slice Cb Iop IOR Johnson.Pack

/-- A typed message of a shape, as a table; 0 outside its ranges. -/
def tabMsg (cs : Codes) (sh : OracleShape) (u : (portCode cs sh).J → GE) : Tab :=
  fun mask row place =>
    if mask then
      if h : row < sh.maskRows ∧ place < (pMask cs sh).ell then
        u (.inr (⟨row, h.1⟩, ⟨place, h.2⟩)) else 0
    else
      if h : row < sh.mainRows ∧ place < (pMain cs sh).ell then
        u (.inl (⟨row, h.1⟩, ⟨place, h.2⟩)) else 0

variable (cs : Codes) (l : List (OracleShape × ℕ)) (mem : Fin l.length → Prop)
  [DecidablePred mem] (s : Sg) (e : ℕ) (oM oZ : Fin l.length → ℕ)
  (hM : ∀ i, mem i → (l.get i).1.mainRows ≠ 0 → cMain cs (l.get i).1 = s.C)
  (hZ : ∀ i, mem i → (l.get i).1.maskRows ≠ 0 → cMask cs (l.get i).1 = s.Z)
  (kp : {i // mem i} → Prop) [DecidablePred kp]
  (h1 : ∀ a, kp a → (l.get a.1).1.mainRows ≠ 0) (h0 : ∀ a, kp a → (l.get a.1).1.maskRows = 0)
  (kq : Fin l.length → Prop) [DecidablePred kq] {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) (rowsPort cs l mem s e oM oZ hM hZ).G.C.J)
  (Z : Evader GE ((rowsPort cs l mem s e oM oZ hM hZ).G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf cs l).sub kq).Msg × Wp))
  (cs' : Codes) (l' : List (OracleShape × ℕ)) (W : SwitchFrame)
  (num : {a // kp a} → ℕ) (plOf : {a // kp a} → KeptPlace)

set_option quotPrecheck false in
local notation "hP" => heldPort cs l mem s e oM oZ hM hZ kp h1 h0 kq
set_option quotPrecheck false in
local notation:max "aK " k:max => (⟨⟨k.1.1, k.2.fst⟩, k.2.snd⟩ : {a // kp a})

/-- The slots' three readings: the member's number in the frame, the row, the member's record. -/
abbrev slotNum (κ : ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).Kp) : ℕ := num κ.1
abbrev slotRow (κ : ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).Kp) : ℕ := κ.2.val
abbrev slotPl (κ : ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).Kp) : KeptPlace := plOf κ.1

variable (Ft : Fit cs' l' s W (slotNum cs l mem s e oM oZ hM hZ kp num)
    (slotRow cs l mem s e oM oZ hM hZ kp) (slotPl cs l mem s e oM oZ hM hZ kp plOf))
  (t : ℕ)
  (w₀ : ((heldPort cs l mem s e oM oZ hM hZ kp h1 h0 kq).foldD Sb sl Z A₀).tgt.W)

/-- **What the switch hands back as an old kept message stands in `KeptIs` to its new copy and to
g.** -/
theorem keptIs_back (n : (sigOf cs' l').Msg) (k : {a // (hP).cl a})
    (inj : ∀ a a' : {a // kp a}, num a = num a' → a = a')
    (hrows : (plOf (aK k)).rows = (l.get k.1.1).1.mainRows)
    (hn : ((plOf (aK k)).pad.map (·.index)).Nodup)
    (hpad : ∀ q, q < (plOf (aK k)).pad.length →
      ((plOf (aK k)).pad.getD q default).index %
          2 ^ (plOf (aK k)).rowBits <
        (plOf (aK k)).rows ∧
      ((plOf (aK k)).pad.getD q default).index /
          2 ^ (plOf (aK k)).rowBits < s.C.l) :
    KeptIs W (plOf (aK k)) s.C.l
      (tabMsg cs (l.get k.1.1).1
        ((closeSel (hP) Sb sl Z A₀ cs' l' (iJ s W _ _ _ cs' l' Ft.nameJ)
          (iQ s W _ _ cs' l' Ft.nameQ) t w₀).loc.hd.msg
            (cutSel cs' l' (iJ s W _ _ _ cs' l' Ft.nameJ) (iQ s W _ _ cs' l' Ft.nameQ) n).1 k))
      (tabOf cs' l' n (1 + num (aK k))) (tabOf cs' l' n 0) := by
  have eC : (cMain cs (l.get k.1.1).1).l = s.C.l :=
    congrArg Fmt.M1.Code.l (hM k.1.1 k.2.fst (h1 ⟨k.1.1, k.2.fst⟩ k.2.snd))
  refine keptIs_of_iJ Ft n (num (aK k)) _
    (fun κ h => congrArg plOf (inj _ _ h)) _ ?_ ?_ hn hpad
  · rintro ⟨a, r⟩ j h
    obtain rfl : a = (aK k) := inj _ _ h
    have hj : j.val < (pMain cs (l.get k.1.1).1).ell := by
      have : (cMain cs (l.get k.1.1).1).l = (pMain cs (l.get k.1.1).1).ell := rfl
      omega
    show tabMsg cs (l.get k.1.1).1 _ false r.val j.val = _
    unfold tabMsg
    rw [if_neg (by decide), dif_pos ⟨r.isLt, hj⟩]
    exact held_port_sel cs l mem s e oM oZ hM hZ kp h1 h0 kq Sb sl Z A₀ cs' l' _ _ t w₀ n k
      (⟨r.val, r.isLt⟩, ⟨j.val, hj⟩)
  · intro b hb
    exact ⟨⟨(aK k), ⟨b, lt_of_lt_of_eq hb hrows⟩⟩, rfl, rfl⟩

variable {Pw : Type} (Cw : LdCode GE Pw)

set_option quotPrecheck false in
local notation "jS" => iJ s W (slotNum cs l mem s e oM oZ hM hZ kp num)
  (slotRow cs l mem s e oM oZ hM hZ kp) (slotPl cs l mem s e oM oZ hM hZ kp plOf) cs' l' Ft.nameJ
set_option quotPrecheck false in
local notation "qS" => iQ s W (slotNum cs l mem s e oM oZ hM hZ kp num)
  (slotRow cs l mem s e oM oZ hM hZ kp) cs' l' Ft.nameQ
set_option quotPrecheck false in
local notation "zK" => switchSel (hP) Sb sl Z A₀ cs' l' (jS) (qS) t w₀ Cw
set_option quotPrecheck false in
local notation "hdK" => (closeSel (hP) Sb sl Z A₀ cs' l' (jS) (qS) t w₀).loc.hd
set_option quotPrecheck false in
local notation:max "nwK " w:max => newOf (hP) Sb sl Z A₀ cs' l' (jS) (qS) t w₀ Cw w

/-- What is asked of the frame's record of a kept member: `RecOK`
(Johnson/Top/H/SwitchKeptRec.lean) at the member's record, its number of main rows in the typed
list, and the number of entries of a message of the stage's main code. -/
abbrev KeptRecOK (k : {a // (hP).cl a}) : Prop :=
  RecOK (plOf (aK k)) (l.get k.1.1).1.mainRows s.C.l

/-- **Back across the switch, on plain tables**: where the joint in front holds at what the
extractor hands back, on the promise: each held message's word decodes with its sample to a message
whose table stands in `KeptIs` to the tables of its new copy and of g among the witness's new
messages. -/
theorem back_keptIs
    (a : (Cb.Pv.SendLoc.stage (zK).sw).X × (Cb.Pv.SendLoc.stage (zK).sw).Ex.Str)
    (τ : Tr (Cb.Pv.SendLocRide.R (zK)).shape) (w : (Cb.Pv.SendLoc.loc (zK).sw).tgt.W)
    (hon : ((Cb.Pv.SendLoc.stage (zK).sw).S.over (Cb.Pv.SendLoc.stage (zK).sw).A).on a)
    (h : (Cb.Pv.SendLocRide.inJ (zK)).relR a (Cb.Pv.SendLocRide.ext (zK) a τ w))
    (inj : ∀ a a' : {a // kp a}, num a = num a' → a = a')
    (k : {a // (hP).cl a})
    (hk : KeptRecOK cs l mem s e oM oZ hM hZ kp h1 h0 kq plOf k) :
    ∃ u : (portCode cs (l.get k.1.1).1).J → GE,
      ((hdK).o k).decW ((hdK).sW k a.2.1.1) (a.1.1.1.2 k) = some u ∧
      KeptIs W (plOf (aK k)) s.C.l (tabMsg cs (l.get k.1.1).1 u)
        (tabOf cs' l' (nwK w) (1 + num (aK k)))
        (tabOf cs' l' (nwK w) 0) :=
  ⟨_, sel_back_dec (hP) Sb sl Z A₀ cs' l' (jS) (qS) t w₀ Cw a τ w hon h k,
    keptIs_back cs l mem s e oM oZ hM hZ kp h1 h0 kq Sb sl Z A₀ cs' l' W num plOf Ft t w₀ _ k inj
      hk.rows hk.nodup hk.pad⟩

/-- **The same of the old message's word as it was sent**: f: a word as sent whose reading is the
slot of the open word (of what a fold puts out the library shows that for `G.P` nonempty and under
its hc, if `Hd.Laws`: `LdFoldD.Tw`, Cb/Req1/LdSegKit.lean; `ldGroup_seg_word`,
Cb/Ld/LdGroupSegProofs.lean). -/
theorem back_keptIs_sent
    (a : (Cb.Pv.SendLoc.stage (zK).sw).X × (Cb.Pv.SendLoc.stage (zK).sw).Ex.Str)
    (τ : Tr (Cb.Pv.SendLocRide.R (zK)).shape) (w : (Cb.Pv.SendLoc.loc (zK).sw).tgt.W)
    (hon : ((Cb.Pv.SendLoc.stage (zK).sw).S.over (Cb.Pv.SendLoc.stage (zK).sw).A).on a)
    (h : (Cb.Pv.SendLocRide.inJ (zK)).relR a (Cb.Pv.SendLocRide.ext (zK) a τ w))
    (inj : ∀ a a' : {a // kp a}, num a = num a' → a = a')
    (k : {a // (hP).cl a})
    (hk : KeptRecOK cs l mem s e oM oZ hM hZ kp h1 h0 kq plOf k)
    (f : ((sigOf cs l).om k.1.1).Str)
    (hf : (hdK).sW k a.2.1.1 = ((sigOf cs l).om k.1.1).upW f) :
    ∃ u : (portCode cs (l.get k.1.1).1).J → GE,
      ((sigOf cs l).om k.1.1).dec f (a.1.1.1.2 k) = some u ∧
      KeptIs W (plOf (aK k)) s.C.l (tabMsg cs (l.get k.1.1).1 u)
        (tabOf cs' l' (nwK w) (1 + num (aK k)))
        (tabOf cs' l' (nwK w) 0) := by
  obtain ⟨u, h1', h2'⟩ := back_keptIs cs l mem s e oM oZ hM hZ kp h1 h0 kq Sb sl Z A₀ cs' l' W num
    plOf Ft t w₀ Cw a τ w hon h inj k hk
  refine ⟨u, ?_, h2'⟩
  rw [OMsg.dec_eq_decW, ← hf]
  exact h1'

end Johnson.Top.H

#print axioms Johnson.Top.H.keptIs_back
#print axioms Johnson.Top.H.back_keptIs_sent
#print axioms Johnson.Top.H.back_keptIs
