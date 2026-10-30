-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/Covers.lean: FROM A SENDER's LOT TO ANOTHER TEXT OF THE SAME
MESSAGE: `Covers Vd N Ls L`: the lot Ls bears L's number, and wherever L's text answers an element,
Ls's text answers the same. Then what the frame's form `OwnMsgs` says of a Script at Ls it says at L
too: so a text that is in no list of lots can have the form, off a lot that is. For every kind of
sub-protocol: no kind is named. IT PAYS NOTHING. One definition, the form of a premise; six
theorems.

What it is for. The frame's laying of a Script from lots (`Script.ofLots`, `ofLots_ownMsgs`,
Johnson/Desc/ProofFile/Honest/Thread/ScriptLots.lean) meets `OwnMsgs` at a lot THAT IS IN THE LIST.
The list is meant to hold the senders' whole-message lots alone. A kind that reads entries of a
message that another kind sends wants `OwnMsgs` at a text of its own, which answers at these entries
alone. L stands here as the name of a triple (number, challenges, text): it need be in no list.

Main names:
  `Covers Vd N Ls L`: the form. Asked only at the inputs and lists of challenges of which
    `OwnMsgs … Vd N …` speaks.
  `ownMsgs_of_covers`: **`OwnMsgs` at Ls gives `OwnMsgs` at L**, at every Script.
  `ofLots_ownMsgs_of_covers`: **at the laying**: Ls is in the list and the other lots of its message
    agree with it: then `OwnMsgs` at L.
  `covers_of_agree`: how the form is had: one number; `Agree2 L Ls` (AgreeParts.lean in this
    folder): one element wherever both answer; and Ls answers wherever L does.
  `covers_self`, `covers_trans`, `covers_mono`: a lot covers itself; the form goes on along a
    chain; fewer inputs and longer lists of challenges ask less.

How. `OwnMsgs`' end names neither the lot's text nor its number of challenges: the answer is handed
through.

Whose. By the authors of the attention sub-protocol's (K5's) own rounds.

Limits. A FORM AND LOGIC OVER IT. `Covers` is proved here of a lot and itself alone. IT MAY HOLD
EMPTILY: where L's text answers nowhere it asks the numbers' equation alone, and `OwnMsgs` at L then
says nothing. That a list holds a lot Ls, and that the other lots agree with it, are premises. The
names stand in the frame's namespace. It stands over ScriptLots.lean, which lies in no seal.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Small.AgreeParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (MsgT)

variable {Bk : ProverCoinCounts} {S Cl W Cells Tok : Type}

/-- **The lot Ls covers L**: one number; wherever L's text answers an element, Ls's text answers the
same. Vd, N: at which inputs and lists of challenges that is asked. It is a definition: the form of
a premise. -/
def Covers (Vd : W → Prop) (N : Nat) (Ls L : MsgLot Bk W) : Prop :=
  Ls.n = L.n ∧ ∀ k w (hd : List Fmt.Drawn), Vd w → N ≤ hd.length → ∀ mask row place y,
    L.txt k w (hd.take L.fx) mask row place = some y →
    Ls.txt k w (hd.take Ls.fx) mask row place = some y

/-- A lot covers itself. -/
theorem covers_self (Vd : W → Prop) (N : Nat) (L : MsgLot Bk W) : Covers Vd N L L :=
  ⟨rfl, fun _ _ _ _ _ _ _ _ _ q => q⟩

/-- The form goes on along a chain. -/
theorem covers_trans {Vd : W → Prop} {N : Nat} {L₁ L₂ L₃ : MsgLot Bk W}
    (C : Covers Vd N L₁ L₂) (C' : Covers Vd N L₂ L₃) : Covers Vd N L₁ L₃ :=
  ⟨C.1.trans C'.1, fun k w hd hv hN mask row place y q =>
    C.2 k w hd hv hN mask row place y (C'.2 k w hd hv hN mask row place y q)⟩

/-- Fewer inputs and longer lists of challenges ask less. -/
theorem covers_mono {Vd Vd' : W → Prop} {N N' : Nat} {Ls L : MsgLot Bk W}
    (hV : ∀ w, Vd' w → Vd w) (hN : N ≤ N') (C : Covers Vd N Ls L) : Covers Vd' N' Ls L :=
  ⟨C.1, fun k w hd hv hl => C.2 k w hd (hV w hv) (Nat.le_trans hN hl)⟩

/-- **`OwnMsgs` AT THE COVERING LOT GIVES `OwnMsgs` AT THE COVERED ONE.** At every Script. -/
theorem ownMsgs_of_covers {Q : Script Bk W Cells Tok MsgT} {Vd : W → Prop} {N : Nat}
    {Ls L : MsgLot Bk W} (C : Covers Vd N Ls L) (H : OwnMsgs Q Vd N Ls.n Ls.fx Ls.txt) :
    OwnMsgs Q Vd N L.n L.fx L.txt := by
  intro k w hd hv hN mask row place y q
  rw [← C.1]
  exact H k w hd hv hN mask row place y (C.2 k w hd hv hN mask row place y q)

/-- **AT THE LAYING: `OwnMsgs` AT A TEXT THAT IS IN NO LIST, OFF A LOT THAT IS.** CONDITIONAL: hL:
Ls is in the list; hagree: the other lots of its message agree with it; C: it covers L. -/
theorem ofLots_ownMsgs_of_covers (bs : List (Block S Cl)) (front : Nat) (cells : W → Cells)
    (tok : W → Tok) (pl : List (PadLot Bk W)) (tl : Nat → TreeLot Bk W) (ml : List (MsgLot Bk W))
    {Ls L : MsgLot Bk W} (hL : Ls ∈ ml) (hagree : LotsAgree ml Ls) {Vd : W → Prop} {N : Nat}
    (C : Covers Vd N Ls L) :
    OwnMsgs (Script.ofLots bs front cells tok pl tl ml) Vd N L.n L.fx L.txt :=
  ownMsgs_of_covers C (ofLots_ownMsgs bs front cells tok pl tl ml hL hagree Vd N)

/-- **HOW THE FORM IS HAD**: one number; one element wherever both answer; and Ls answers wherever L
does. -/
theorem covers_of_agree {Vd : W → Prop} {N : Nat} {Ls L : MsgLot Bk W} (hn : Ls.n = L.n)
    (hA : Agree2 L Ls)
    (hS : ∀ k w (hd : List Fmt.Drawn), Vd w → N ≤ hd.length → ∀ mask row place,
      (L.txt k w (hd.take L.fx) mask row place).isSome = true →
      (Ls.txt k w (hd.take Ls.fx) mask row place).isSome = true) : Covers Vd N Ls L := by
  refine ⟨hn, fun k w hd hv hN mask row place y q => ?_⟩
  obtain ⟨y', q'⟩ := Option.isSome_iff_exists.1
    (hS k w hd hv hN mask row place (by rw [q]; rfl))
  rw [q', hA hn k w hd mask row place y y' q q']

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.covers_self
#print axioms ProofFile.Honest.FirstThread.covers_trans
#print axioms ProofFile.Honest.FirstThread.covers_mono
#print axioms ProofFile.Honest.FirstThread.ownMsgs_of_covers
#print axioms ProofFile.Honest.FirstThread.ofLots_ownMsgs_of_covers
#print axioms ProofFile.Honest.FirstThread.covers_of_agree
