-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchHeldSel.lean: at the caller `switchSel` of the code switch the messages that
were held in the open word are read off the new messages, entry by entry, along the map of names iJ.

The library's closing hands back the held messages as slots of what the cut reads off the new
messages (`LdHeld.msg`, Cb/Req1/LdSegKit.lean; `LdCloseD.snd`, `LdCloseD.A₁`,
Cb/Req1/LdSegFit.lean). At `closeSel` (Johnson/Top/H/SwitchSel.lean) the cut is made of two maps of
names. So an old message has no place of its own behind the switch: each of its entries is an entry
of a new message. Statements and proofs; the first two hold by definition.
Main names:
  `held_sel`: entry j of the held message k is the new messages' entry at `iJ (hd.sJ k j)`.
  `held_slot`: `hd.sJ k j` is the kept slot of the entry's row, at the entry's place
    (`GHeld.sJ`, Cb/Ld/LdGroupSeg.lean).
  `undoTab_cJ`, `heldPort_cJ`: at the programs' shapes (`heldPort`, Johnson/Top/H/SwitchKept.lean;
    `undoTab`, Johnson/Top/H/MemberHeld.lean) the row and the place are the entry's own.
  `held_port_sel`: the three together: entry (row, place) of an old kept message's main table is
    the new messages' entry at the name that iJ gives the kept slot of that row, at that place.
`closeSel` is a `LdCloseD`.


Limits: iJ is a letter. Nothing says where the programs lay an old message's entries, or its pad.
Nothing on a decoder, on a word or on soundness.

-/
import Johnson.Top.H.SwitchSel
import Johnson.Top.H.SwitchKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes.Slice Cb Iop IOR Johnson.Pack

section Any
variable {S : Sig GE} {G : Grp S} [Nonempty G.P] {Sh : GShape G} {kp : S.O → Prop}
  [DecidablePred kp] (Hd : GHeld Sh kp) {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) G.C.J) (Z : Evader GE (G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (iJ : Sh.Cf.J → (sigOf cs l).Ent) (iQ : Sh.Cf.Q → (sigOf cs l).Ent)
  (t : ℕ) (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W)

/-- A held message, as the closing reads it off the new messages. -/
theorem held_sel (n : (sigOf cs l).Msg) (k : (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.hd.K)
    (j : ((closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.hd.o k).C.J) :
    (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.hd.msg (cutSel cs l iJ iQ n).1 k j =
      (sigOf cs l).ents n (iJ ((closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.hd.sJ k j)) := rfl

/-- Where an entry of a held message stands in the open word: in the kept slot of its row. -/
theorem held_slot (k : {a // Hd.cl a}) (j : (S.om k.1.1).C.J) :
    (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.hd.sJ k j =
      .inl (some (Hd.slot k (Hd.cJ k j).1), (Hd.cJ k j).2) := rfl

end Any

/-- Where the way back from a table lays an entry of the table: at its own row and place. -/
theorem undoTab_cJ (C C' : Fmt.M1.Code) (a a' n : ℕ) (B : LdCode GE (Fin (2 ^ a')))
    (hS : ∀ p, IsEmpty (B.NS p)) (hJ : IsEmpty B.J) (hQ : IsEmpty B.Q) (e : C' = C)
    (x : Fin n × Fin C'.l) :
    (undoTab C C' a a' n B hS hJ hQ e).cJ (.inl x) =
      (x.1, Fin.cast (congrArg Fmt.M1.Code.l e) x.2) := by
  subst e
  rfl

variable (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ)) (mem : Fin l.length → Prop)
  [DecidablePred mem] (s : Sg) (e : ℕ) (oM oZ : Fin l.length → ℕ)
  (hM : ∀ i, mem i → (l.get i).1.mainRows ≠ 0 → cMain cs (l.get i).1 = s.C)
  (hZ : ∀ i, mem i → (l.get i).1.maskRows ≠ 0 → cMask cs (l.get i).1 = s.Z)
  (kp : {i // mem i} → Prop) [DecidablePred kp]
  (h1 : ∀ a, kp a → (l.get a.1).1.mainRows ≠ 0) (h0 : ∀ a, kp a → (l.get a.1).1.maskRows = 0)
  (kq : Fin l.length → Prop)

/-- At the programs' shapes: entry (row, place) of a kept member's main table stands in the kept
slot of that row, at that place. -/
theorem heldPort_cJ (k : {a // (heldPort cs l mem s e oM oZ hM hZ kp h1 h0 kq).cl a})
    (x : Fin (l.get k.1.1).1.mainRows × Fin (cMain cs (l.get k.1.1).1).l) :
    (heldPort cs l mem s e oM oZ hM hZ kp h1 h0 kq).cJ k (.inl x) =
      (x.1, Fin.cast (congrArg Fmt.M1.Code.l
        (hM k.1.1 k.2.fst (h1 ⟨k.1.1, k.2.fst⟩ k.2.snd))) x.2) :=
  undoTab_cJ _ _ _ _ _ _ _ _ _ _ x

variable [DecidablePred kq] {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) (rowsPort cs l mem s e oM oZ hM hZ).G.C.J)
  (Z : Evader GE ((rowsPort cs l mem s e oM oZ hM hZ).G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf cs l).sub kq).Msg × Wp))
  (cs' : OnBytes.Codes) (l' : List (OnBytes.OracleShape × ℕ))
  (iJ : ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).Sh.Cf.J → (sigOf cs' l').Ent)
  (iQ : ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).Sh.Cf.Q → (sigOf cs' l').Ent)
  (t : ℕ) (w₀ : ((heldPort cs l mem s e oM oZ hM hZ kp h1 h0 kq).foldD Sb sl Z A₀).tgt.W)

/-- **An old kept message, read off the new messages**: entry (row, place) of its main table is the
new messages' entry at the name that iJ gives the kept slot of that row, at that place. -/
theorem held_port_sel (n : (sigOf cs' l').Msg)
    (k : {a // (heldPort cs l mem s e oM oZ hM hZ kp h1 h0 kq).cl a})
    (x : Fin (l.get k.1.1).1.mainRows × Fin (cMain cs (l.get k.1.1).1).l) :
    (closeSel (heldPort cs l mem s e oM oZ hM hZ kp h1 h0 kq) Sb sl Z A₀ cs' l' iJ iQ t
        w₀).loc.hd.msg (cutSel cs' l' iJ iQ n).1 k (.inl x) =
      (sigOf cs' l').ents n (iJ (.inl (some ⟨⟨⟨k.1.1, k.2.fst⟩, k.2.snd⟩, x.1⟩,
        Fin.cast (congrArg Fmt.M1.Code.l
          (hM k.1.1 k.2.fst (h1 ⟨k.1.1, k.2.fst⟩ k.2.snd))) x.2))) := by
  rw [held_sel, held_slot, heldPort_cJ]
  rfl

end Johnson.Top.H

#print axioms Johnson.Top.H.held_sel
#print axioms Johnson.Top.H.held_slot
#print axioms Johnson.Top.H.undoTab_cJ
#print axioms Johnson.Top.H.heldPort_cJ
#print axioms Johnson.Top.H.held_port_sel
