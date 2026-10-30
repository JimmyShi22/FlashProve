-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegCarryClose.lean: masks that cross a closing: the wide fact through "bridge to fold ;
the one sending ; the locations", and through a whole segment with one group.

Statements (`Cb.Spec.segWide_close`, `Cb.Spec.segWide_segOne`) and proofs: an assembly of the rules
move by move of Cb/Req1/LdSegCarry.lean.

Why: a message with masks that rides in an early prover message of a request serves blocks of
later segments: its masks have to be fresh after closings in between. Cb/Req1/LdSegCarry.lean has
the standard fact that is carried (`a.wideFact Rd Rr own Mk val`: the entries in Rd, the encoding
randomness of the names in Rr, the whole further witness; the entries "own" overwritten) and one
rule for each kind of move. Cb/Req1/LdSegWholeAfter.lean folds such rules through a segment for any
readings. Here both, in the parameters of the wide fact, so that what is left are conditions on
places and on the sender.

Main names (the type Mk of masks is finite and non-empty, as `wideFact` needs):
  `Spec.segWide_close`: D: the first half of a closing (bridge to fold on the group D.G), l its
    link, Q the second half (one sending of the family Q.N; the locations). If the wide fact is
    among the facts X before the fold, and
      (members) every member of the group has its randomness read (Rr), all its entries in Rd, none
        own: the message that holds the masks is no member
      (link) the two facts on `l` (stated of `ldRunGH`: Cb/Ld/LdGroupBlind.lean): transcript,
        explicit part and the test's part of the last witness are functions of the members' pairs;
        the carried part is handed on
      (sender) its laws; its messages and the further witness that it hands on are the same for two
        witnesses that agree on what the fact shows off the own entries
      (cut) what the locations read of the new messages lies in RdN; and whatever the arguments hold
        as proofs
    then the wide fact is among the facts after the locations: on the messages that are left its
    sets are the old ones (restricted to what is kept and not held), on the new family any RdN, RrN
    with (cut); no new entry is own.
  `Spec.segWide_segOne`: the same through a whole segment with one group (Cb/Req1/LdSegWhole.lean:
    `segOne`; `hT`: the body's moves are of the kinds that the body of a segment may hold:
    `LdSeg.bodyT`, Cb/Req1/LdSeg.lean; and whatever the arguments hold as proofs): body ; batching ;
    step ; fold ; sending ; locations, from "the fact is fresh after the body".

Limits: this file says nothing on two groups. It does not say that the fact is fresh after the body
(rules: Cb/Req1/LdSegCarry.lean; at the sender: Cb/Req1/LdSegSendFresh.lean). A mask message that is
held in the folded complex is not covered (its entries leave the signature).
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegCarry
import Cb.Req1.LdSegWholeAfter

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR IOR.Chain

namespace Spec
section
variable (E Kc : Type) [Field E] [Fintype E]

/-- The wide fact through the closing of one group. -/
def segWide_close : Prop :=
  ∀ (D : LdFoldD E Kc) (l : Link Kc D.src.J D.mid) (Q : LdCloseD D) (X : MaskFact D.src.J.W → Prop)
      (Rd : D.S.Ent → Prop) (Rr : D.S.O → Prop) (own : D.S.Ent → Prop) (Mk : Type) [Fintype Mk]
      [Nonempty Mk] (val : Mk → D.S.Ent → E) (RdN : Q.N.Ent → Prop) (RrN : Q.N.O → Prop),
    (∀ (w w' : D.src.J.W) x c ρ, D.G.wit w'.1 = D.G.wit w.1 →
      ((l.H.strat w' x c).run ρ).1 = ((l.H.strat w x c).run ρ).1 ∧
      ((l.H.strat w' x c).run ρ).2.1 = ((l.H.strat w x c).run ρ).2.1 ∧
      ((l.H.strat w' x c).run ρ).2.2.1 = ((l.H.strat w x c).run ρ).2.2.1) →
    (∀ (w : D.src.J.W) x c ρ,
      ((l.H.strat w x c).run ρ).2.2.2 = (D.S.res (T := OMsg.Wit) D.kp w.1, w.2)) →
    (∀ o, D.G.mem o → Rr o ∧ ∀ j, Rd ⟨o, j⟩ ∧ ¬ own ⟨o, j⟩) →
    Q.Sn.Laws (D.tgt.S.backN Q.N Q.snd.bk) →
    (∀ w w' : D.tgt.W,
      D.tgt.S.Alike (D.S₁.subQ _ (D.S.subQ D.kp Rd)) (D.S₁.subQ _ (D.S.subQ D.kp own))
        (D.tgt.S.msgs w.1) (D.tgt.S.msgs w'.1) →
      (∀ o : D.tgt.S.O, Rr o.1.1 → (w'.1 o).2 = (w.1 o).2) → w'.2 = w.2 →
      (∀ k, Q.Sn.put w' k = Q.Sn.put w k) ∧ (Q.Sn.rest w').2 = (Q.Sn.rest w).2) →
    (∀ m m' : Q.N.Msg, (∀ n : Q.N.Ent, RdN n → m' n.1 n.2 = m n.1 n.2) → Q.cutN m' = Q.cutN m) →
    X (D.src.wideFact Rd Rr own Mk val) →
    Q.locP.After ((LdMv.send D.tgt Q.snd).After ((Q.foldP l).After X))
      (Q.loc.tgt.wideFact (D.tgt.S.sumP Q.N (D.S₁.subQ _ (D.S.subQ D.kp Rd)) RdN)
        (D.tgt.S.sumO Q.N (fun a => Rr a.1.1) RrN)
        (D.tgt.S.sumP Q.N (D.S₁.subQ _ (D.S.subQ D.kp own)) fun _ => False) Mk
        fun M => D.tgt.S.sumV Q.N (D.S₁.subF _ (D.S.subF D.kp (val M))) fun _ => 0)

/-- The wide fact through a segment with one group. -/
def segWide_segOne : Prop :=
  ∀ (a : LdStage E Kc) (D : LdCl1 E Kc) (body : LdProg a D.bat.src)
      (hT : body.All fun t => t = .send ∨ t = .sub ∨ t = .step)
      (l : Link Kc D.fold.src.J D.fold.mid) (Q : LdCloseD D.fold) (base : MaskFact a.J.W → Prop)
      (Rd : D.S.Ent → Prop) (Rr : D.S.O → Prop) (own : D.S.Ent → Prop) (Mk : Type) [Fintype Mk]
      [Nonempty Mk] (val : Mk → D.S.Ent → E) (RdN : Q.N.Ent → Prop) (RrN : Q.N.O → Prop),
    (∀ (w w' : D.fold.src.J.W) x c ρ, D.fold.G.wit w'.1 = D.fold.G.wit w.1 →
      ((l.H.strat w' x c).run ρ).1 = ((l.H.strat w x c).run ρ).1 ∧
      ((l.H.strat w' x c).run ρ).2.1 = ((l.H.strat w x c).run ρ).2.1 ∧
      ((l.H.strat w' x c).run ρ).2.2.1 = ((l.H.strat w x c).run ρ).2.2.1) →
    (∀ (w : D.fold.src.J.W) x c ρ,
      ((l.H.strat w x c).run ρ).2.2.2 = (D.fold.S.res (T := OMsg.Wit) D.fold.kp w.1, w.2)) →
    (∀ o, D.fold.G.mem o → Rr o ∧ ∀ j, Rd ⟨o, j⟩ ∧ ¬ own ⟨o, j⟩) →
    Q.Sn.Laws (D.fold.tgt.S.backN Q.N Q.snd.bk) →
    (∀ w w' : D.fold.tgt.W,
      D.fold.tgt.S.Alike (D.fold.S₁.subQ _ (D.fold.S.subQ D.fold.kp Rd))
        (D.fold.S₁.subQ _ (D.fold.S.subQ D.fold.kp own))
        (D.fold.tgt.S.msgs w.1) (D.fold.tgt.S.msgs w'.1) →
      (∀ o : D.fold.tgt.S.O, Rr o.1.1 → (w'.1 o).2 = (w.1 o).2) → w'.2 = w.2 →
      (∀ k, Q.Sn.put w' k = Q.Sn.put w k) ∧ (Q.Sn.rest w').2 = (Q.Sn.rest w).2) →
    (∀ m m' : Q.N.Msg, (∀ n : Q.N.Ent, RdN n → m' n.1 n.2 = m n.1 n.2) → Q.cutN m' = Q.cutN m) →
    body.After base (D.bat.src.wideFact Rd Rr own Mk val) →
    (segOne D body hT l Q).After base
      (Q.loc.tgt.wideFact
        (D.fold.tgt.S.sumP Q.N (D.fold.S₁.subQ _ (D.fold.S.subQ D.fold.kp Rd)) RdN)
        (D.fold.tgt.S.sumO Q.N (fun a => Rr a.1.1) RrN)
        (D.fold.tgt.S.sumP Q.N (D.fold.S₁.subQ _ (D.fold.S.subQ D.fold.kp own)) fun _ => False) Mk
        fun M =>
          D.fold.tgt.S.sumV Q.N (D.fold.S₁.subF _ (D.fold.S.subF D.fold.kp (val M))) fun _ => 0)

end
end Spec

section
variable {E Kc : Type} [Field E] [Fintype E]

theorem segWide_close : Spec.segWide_close E Kc := by
  intro D l Q X Rd Rr own Mk _ _ val RdN RrN F1 F2 hm hL hp hc hX
  have h3 : (Q.foldP l).After X
      (D.tgt.wideFact (D.S₁.subQ _ (D.S.subQ D.kp Rd)) (fun a => Rr a.1.1)
        (D.S₁.subQ _ (D.S.subQ D.kp own)) Mk fun M => D.S₁.subF _ (D.S.subF D.kp (val M))) := by
    rw [LdCloseD.foldP, LdProg.after_snoc, LdProg.after_nil]
    exact segWide_fold D l X Rd Rr own Mk val F1 F2 hm hX
  have h4 := segWide_send_old D.tgt Q.snd ((Q.foldP l).After X) _ _ _ Mk _ RdN RrN hL hp h3
  rw [LdCloseD.locP, LdProg.after_snoc, LdProg.after_nil]
  refine segWide_loc Q.loc _ _ _ _ Mk _ (fun m m' hA => hc _ _ fun n hn => ?_) h4
  exact hA ⟨Sum.inr n.1, n.2⟩ hn fun h => h

theorem segWide_segOne : Spec.segWide_segOne E Kc := by
  intro a D body hT l Q base Rd Rr own Mk _ _ val RdN RrN F1 F2 hm hL hp hc hb
  have h1 : (LdMv.bat D.bat).After (body.After base) (D.bat.tgt.wideFact Rd Rr own Mk val) :=
    segWide_bat D.bat _ Rd Rr own Mk val hb
  have h2 : D.step.After ((LdMv.bat D.bat).After (body.After base))
      (D.fold.src.wideFact Rd Rr own Mk val) := by
    unfold LdCl1.step ldStepF
    exact segCarry_step D.bat.tgt D.fold.src _ _ _ _ _ (D.bat.tgt.wideFact Rd Rr own Mk val)
      _ (D.fold.src.wideFact Rd Rr own Mk val).kc (D.fold.src.wideFact Rd Rr own Mk val).put
      h1 (fun _ _ _ _ h => ⟨rfl, h⟩)
  have h2' : D.batP.After (body.After base) (D.fold.src.wideFact Rd Rr own Mk val) := by
    rw [LdCl1.batP, LdProg.after_snoc, LdProg.after_snoc, LdProg.after_nil]
    exact h2
  exact segWide_close D.fold l Q _ Rd Rr own Mk val RdN RrN F1 F2 hm hL hp hc h2'

end
end Cb
