-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqStdFresh.lean: a sending of a request with the standard sender: what zero knowledge
asks of the sender, beside its hypotheses (`LdSendD.Hyp`) ("fresh" for masks that it lays down;
"does not look" at masks in older messages) from the layout and from one condition on the data map.
(not all hypotheses are named here: see `Spec.stdSend_many`, `Spec.stdSend_one`)

Definitions, statements (each a `Prop` in `Cb.Spec`) and proofs.
A sending (`d : LdSendD a`, Cb/Req1/LdSegKit.lean) is a step in which the prover sends new oracle
messages, the verifier draws their seeds, and the prover sends the answers; its honest prover is the
sender `d.D`. `LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0` (Cb/Obj/LdObjectSenders.lean) is the
sending whose sender is `Y.snd` of a layout `Y : N.StdL F` (Cb/Ld/LdSendStdL.lean) at the data map
`dat`. Wide facts: `LdStage.wideFact` (Cb/Req1/LdSegCarry.lean). `H.Fresh Ri bud kc Mk put`: for
every (x, y, w) in Ri, every ρ outside `H.withheld w x` and every T with `bud ρ T`: the distribution
of `H.seen …` over uniform coins does not change if its third part is overwritten by `put M` at an
independent uniform M. (`Honest.Fresh`, `Honest.seen`: Ior/KnowCollRulesMask.lean; in
`Spec.stdSend_many` it stands as the conclusion.)

The calculus of masks of a reference request (Cb/Req1/LdReqRefLay.lean) asks of the honest senders,
which are parameters there:
  (1) the one sending of a closing (or a first sending) is `Fresh` for the wide fact of the masks
      that it lays down (first clause of "laid down by the one sending");
  (2) the senders inside a body do not look at the own entries of a fact that passes
      (`LdSendD.NoLook`, Cb/Req1/LdSegRefCarry.lean);
  (3) the one sender of a closing that a fact crosses has its laws and does not look.
Here all three at the term `LdSendD.std`, on Cb/Ld/LdSendStdL.lean, Cb/Ld/LdSendStdOwn.lean.

Main names:
  (1) has two forms, which differ in the fact's reading.
  The masks in any members; the reading forgets all pads and all encoding randomness of the new
  family (fresh for a body that follows; it cannot cross a closing whose group holds new members):
    `Y.ownP pl`, `Y.valP pl M`: the own entries: the free entries at an injective family of places
      `pl : I → Σ a, Y.Fr a`; their values.
    `Spec.stdSend_many`: pl injective, `Y.OK t` ⇒ the link is `Fresh` for `d.tgt.wideFact` (old
      part: any RdOld, RrOld; new part: all entries that are no pads, no randomness) with these own
      entries. `Spec.stdSend_manyAfter`: so the fact is fresh after the move, whatever was fresh
      before.
  The masks in one member o; the reading shows all entries but o's pads and the randomness of all
  members but o (the form that can cross): Cb/Ld/LdSendStdVis.lean: `stdL_vis`, `stdL_visAfter`:
  from their pl (`I → Y.Fr o`) injective and `Y.OK t` (not all hypotheses are named here: see
  `stdL_vis`, `stdL_visAfter`); not repeated here.
  (2), (3): the one condition on the data map (`DatBlind a dat Rd Rr own`): two witnesses whose old
  messages agree at all entries in Rd that are not own, whose old randomness agrees at the names in
  Rr, and whose further witnesses are equal, have the same data. (So: dat reads, of the old pairs,
  entries in Rd that are not own and randomness at Rr, and the further witness.)
    `Spec.stdSend_noLook`: `DatBlind` ⇒ `(LdSendD.std ..).NoLook Rd Rr own`. Nothing else is asked
      beside whatever the arguments hold as proofs: what is handed on of the further witness is rst
      of it.
    `Spec.stdSend_one`: `Y.OK t`, `bk₀ (dat w) (rst w.2) = w.2`, `DatBlind` ⇒ the sender's laws for
      the extractor of the move, and the clause "alike ⇒ the same messages for all coins, the same
      further witness handed on".
    `Spec.stdSend_datBlind`: a data map that reads the further witness alone is `DatBlind` for all
      Rd, Rr, own.

Limits: this file says nothing on the second clause of "laid down" (the cut of the locations does
not look): a condition on the cut. It says nothing on narrow facts: by the entry step, from wide
ones.
Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectSenders
import Cb.Ld.LdSendStdOwn
import Cb.Req1.LdSegRefCarry
import Cb.Req1.LdSegSendFreshProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The own entries; their values. -/
def Sig.StdL.ownP {N : Sig E} (Y : N.StdL F) {I : Type} (pl : I → Σ a, Y.Fr a) (n : N.Ent) : Prop :=
  ∃ i, n = Y.entF (pl i)
def Sig.StdL.valP
    {N : Sig E} (Y : N.StdL F) {I : Type} (pl : I → Σ a, Y.Fr a) (M : I → E) : N.Ent → E :=
  Function.extend (fun i => Y.entF (pl i)) M fun _ => 0

/-- The data map does not look. -/
def DatBlind {Kc D : Type} (a : LdStage E Kc) (dat : a.S.Wit × a.Wp → D) (Rd : a.S.Ent → Prop)
    (Rr : a.S.O → Prop) (own : a.S.Ent → Prop) : Prop :=
  ∀ w w' : a.S.Wit × a.Wp, a.S.Alike Rd own (a.S.msgs w.1) (a.S.msgs w'.1) →
    (∀ o, Rr o → (w'.1 o).2 = (w.1 o).2) → w'.2 = w.2 → dat w' = dat w

end

namespace Spec
section
variable (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- Fresh for masks in any members. (not all hypotheses are named here: see the statement below) -/
def stdSend_many : Prop :=
  ∀ (a : LdStage E Kc) (N : Sig E) (Sd : N.Seeds) (Wp' : Type) (L t : N.O → ℕ)
      (Y : N.StdL F) (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E) (rst : a.Wp → Wp')
      (bk₀ : (∀ i, Y.Dt i → E) → Wp' → a.Wp) (w0 : a.S.Wit × a.Wp) (I : Type) [Fintype I]
      [Fintype (I → E)] [Nonempty (I → E)] (pl : I → Σ a, Y.Fr a)
      (RdOld : a.S.Ent → Prop) (RrOld : a.S.O → Prop),
    Function.Injective pl → Y.OK t →
    (LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0).link.H.Fresh a.J.rels.rel
      (LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0).link.P.bud
      ((LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0).tgt.wideFact (a.S.sumP N RdOld Y.NoPad)
        (a.S.sumO N RrOld fun _ => False) (a.S.sumP N (fun _ => False) (Y.ownP pl)) (I → E)
        fun M => a.S.sumV N (fun _ => 0) (Y.valP pl M)).kc
      (I → E) ((LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0).tgt.wideFact (a.S.sumP N RdOld Y.NoPad)
        (a.S.sumO N RrOld fun _ => False) (a.S.sumP N (fun _ => False) (Y.ownP pl)) (I → E)
        fun M => a.S.sumV N (fun _ => 0) (Y.valP pl M)).put

def stdSend_manyAfter : Prop :=
  ∀ (a : LdStage E Kc) (N : Sig E) (Sd : N.Seeds) (Wp' : Type) (L t : N.O → ℕ) (Y : N.StdL F)
      (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E) (rst : a.Wp → Wp')
      (bk₀ : (∀ i, Y.Dt i → E) → Wp' → a.Wp) (w0 : a.S.Wit × a.Wp) (I : Type) [Fintype I]
      [Fintype (I → E)] [Nonempty (I → E)] (pl : I → Σ a, Y.Fr a) (RdOld : a.S.Ent → Prop)
      (RrOld : a.S.O → Prop) (base : MaskFact a.J.W → Prop),
    Function.Injective pl → Y.OK t →
    (LdMv.send a (LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0)).After base
      ((LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0).tgt.wideFact (a.S.sumP N RdOld Y.NoPad)
        (a.S.sumO N RrOld fun _ => False) (a.S.sumP N (fun _ => False) (Y.ownP pl)) (I → E)
        fun M => a.S.sumV N (fun _ => 0) (Y.valP pl M))

/-- Under the hypotheses below, the sender does not look. -/
def stdSend_noLook : Prop :=
  ∀ (a : LdStage E Kc) (N : Sig E) (Sd : N.Seeds) (Wp' : Type) (L t : N.O → ℕ) (Y : N.StdL F)
      (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E) (rst : a.Wp → Wp')
      (bk₀ : (∀ i, Y.Dt i → E) → Wp' → a.Wp) (w0 : a.S.Wit × a.Wp) (Rd : a.S.Ent → Prop)
      (Rr : a.S.O → Prop) (own : a.S.Ent → Prop),
    DatBlind a dat Rd Rr own → (LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0).NoLook Rd Rr own

/-- The one sender of a closing that a fact crosses. -/
def stdSend_one : Prop :=
  ∀ (a : LdStage E Kc) (N : Sig E) (Sd : N.Seeds) (Wp' : Type) (L t : N.O → ℕ) (Y : N.StdL F)
      (dat : a.S.Wit × a.Wp → ∀ i, Y.Dt i → E) (rst : a.Wp → Wp')
      (bk₀ : (∀ i, Y.Dt i → E) → Wp' → a.Wp) (w0 : a.S.Wit × a.Wp) (Rd : a.S.Ent → Prop)
      (Rr : a.S.O → Prop) (own : a.S.Ent → Prop),
    Y.OK t → (∀ w, bk₀ (dat w) (rst w.2) = w.2) → DatBlind a dat Rd Rr own →
    (LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0).D.Laws
      (a.S.backN N (LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0).bk) ∧
    ∀ w w' : a.W, a.S.Alike Rd own (a.S.msgs w.1) (a.S.msgs w'.1) →
      (∀ o, Rr o → (w'.1 o).2 = (w.1 o).2) → w'.2 = w.2 →
      (∀ k, (LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0).D.put w' k =
        (LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0).D.put w k) ∧
      ((LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0).D.rest w').2 =
        ((LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0).D.rest w).2

def stdSend_datBlind : Prop :=
  ∀ (D : Type) (a : LdStage E Kc) (δ : a.Wp → D) (Rd : a.S.Ent → Prop)
      (Rr : a.S.O → Prop) (own : a.S.Ent → Prop),
    DatBlind a (fun w => δ w.2) Rd Rr own

end
end Spec

section
variable (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem stdSend_many : Spec.stdSend_many F E Kc := by
  classical
  intro a N Sd Wp' L t Y dat rst bk₀ w0 I _ _ _ pl RdOld RrOld hpl hY
  have hinj : Function.Injective fun i => Y.entF (pl i) := Y.entF_injective.comp hpl
  have h1 := stdL_own F E N Y t _ _ dat (fun w : a.S.Wit × a.Wp => (w.1, rst w.2)) w0 I pl hpl Sd hY
  have hH :=
    (stdL_all F E N Y t _ _ dat (fun w : a.S.Wit × a.Wp => (w.1, rst w.2)) w0 hY).2.2.2.2.2.1
  have h2 := ldSendSig_fresh_wide E a.S N Sd a.St a.Wp Wp' a.E₀
    (Y.snd dat (fun w : a.S.Wit × a.Wp => (w.1, rst w.2)) w0) t a.J.rels.rel (I → E)
    (Y.ownAt pl hpl dat (fun w : a.S.Wit × a.Wp => (w.1, rst w.2)) w0) _ _ _ h1 hH
  have h3 := fresh_conseq _ _ _ _ _ _ _
    (ldSendSigHon Sd a.St a.E₀ (Y.snd dat (fun w : a.S.Wit × a.Wp => (w.1, rst w.2)) w0))
    a.J.rels.rel a.J.rels.rel _ _ _ _ _
    (fun k : (N.Ent → E) × (a.S.Wit × Wp') =>
      ((a.S.join N (T := OMsg.Msg) (a.S.cut RdOld (a.S.msgs k.2.1))
        (fun i j => k.1 ⟨i, j⟩) : (a.S.sum N).Msg),
        ((a.S.join N (T := fun o => Option o.Rnd)
            (fun o => if RrOld o then some (k.2.1 o).2 else none)
            (fun _ => none) : ∀ o, Option ((a.S.sum N).om o).Rnd),
          k.2.2)))
    (I → E) _
    (fun M k =>
      ((a.S.sum N).ow (a.S.sumP N (fun _ => False) (Y.ownP pl))
          (a.S.sumV N (fun _ => 0) (Y.valP pl M)) k.1,
        k.2))
    (fun _ _ _ h => h) (fun _ _ h => h) (fun M k => by
      refine Prod.ext (funext fun o => ?_) rfl
      rcases o with o | i
      · funext j
        exact (if_neg fun h : False => h).symm
      · funext j
        show Function.extend (fun x => Y.entF (pl x)) M k.1 ⟨i, j⟩ =
          if Y.ownP pl ⟨i, j⟩ then Y.valP pl M ⟨i, j⟩ else k.1 ⟨i, j⟩
        by_cases hw : Y.ownP pl ⟨i, j⟩
        · obtain ⟨x, e⟩ := hw
          rw [if_pos ⟨x, e⟩, e, hinj.extend_apply]
          exact (hinj.extend_apply M _ x).symm
        · rw [if_neg hw, Function.extend_apply' _ _ _ fun ⟨x, e⟩ => hw ⟨x, e.symm⟩]) h2
  refine Eq.mp
    (congrArg (fun kc =>
        (ldSendSigHon Sd a.St a.E₀ (Y.snd dat (fun w : a.S.Wit × a.Wp => (w.1, rst w.2)) w0)).Fresh
          a.J.rels.rel _ kc (I → E) _)
      (funext fun v => ?_)) h3
  refine Prod.ext (funext fun o => ?_) (Prod.ext (funext fun o => ?_) rfl)
  · rcases o with o | i <;> rfl
  · rcases o with o | i
    · rfl
    · exact (if_neg fun h : False => h).symm

theorem stdSend_manyAfter : Spec.stdSend_manyAfter F E Kc := by
  intro a N Sd Wp' L t Y dat rst bk₀ w0 I _ _ _ pl RdOld RrOld base hpl hY
  have h2 := stdSend_many F E Kc a N Sd Wp' L t Y dat rst bk₀ w0 I pl RdOld RrOld hpl hY
  refine segCarry_send_new a (LdSendD.std a N Sd Wp' L t Y dat rst bk₀ w0) base _ ?_
  exact h2

theorem stdSend_noLook : Spec.stdSend_noLook F E Kc := by
  intro a N Sd Wp' L t Y dat rst bk₀ w0 Rd Rr own hd w w' h1 h2 h3
  refine ⟨fun k => ?_, congrArg rst h3⟩
  funext i
  show Y.msgOf i (Sum.elim (dat w' i) (k i).1) (k i).2 =
    Y.msgOf i (Sum.elim (dat w i) (k i).1) (k i).2
  rw [hd w w' h1 h2 h3]

theorem stdSend_one : Spec.stdSend_one F E Kc := by
  intro a N Sd Wp' L t Y dat rst bk₀ w0 Rd Rr own hY hb hd
  refine ⟨?_, stdSend_noLook F E Kc a N Sd Wp' L t Y dat rst bk₀ w0 Rd Rr own hd⟩
  refine (stdL_all F E N Y t _ _ dat (fun w : a.S.Wit × a.Wp => (w.1, rst w.2)) w0 hY).2.2.2.1 _
    fun w k => ?_
  show (w.1, bk₀ (Y.dataOf _) (rst w.2)) = w
  rw [stdL_data F E N Y t _ _ dat (fun w : a.S.Wit × a.Wp => (w.1, rst w.2)) w0 hY w k, hb w]

omit [Field E] [Fintype E] [Algebra F E] in
theorem stdSend_datBlind : Spec.stdSend_datBlind E Kc := fun _ _ δ _ _ _ _ _ _ _ h => congrArg δ h

end
end Cb
