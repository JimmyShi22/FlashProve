-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupNewStd.lean: for toys: the second half of a closing with standard new messages, for any
shape of a group and any choice of kept messages, an abstract field and variable codes: the sender
is built, and what the one sending asks is proved from conditions on codes and on the samples' data
(`V.OK L t`).

In the words of lean/GLOSSARY.md: toy: a small example instance.

In standard terms: in the code switch that follows the fold of several oracle codewords the prover
sends new codewords whose messages contain the message and the encoding randomness of the old,
folded word. This file builds that step with the sender `V.snd` and derives, for `G.P` nonempty and
from `V.OK L t`, the hypotheses that the composition theorems ask of its one sending.

Definitions, statements and proofs. A tool for guards against empty theorems; no parameter of a
protocol.
It builds on Cb/Ld/LdGroupPlace.lean (`GNew`: where the entries of the folded complex go),
Cb/Obj/LdObjectToyKit.lean (`StdM`: a standard oracle message: data and one pad entry, the row with
a pad as sample, its sender), Cb/Req1/LdSegFit.lean and Cb/Req1/LdSegWhole.lean (the moves of a
closing from one record; a segment).

The data (`StdNew Hd Pn`). `ag`: which held messages are encoded anew; `pj k`: the one pad place of
such a message; `Mn k`: the standard message that is its new encoding: its data are the cells
(`cl k`), its pad stands at the pad place; `Mc`: the carried message, a standard message whose data
are all that goes nowhere else (`cc`): among them the ordinary slot, the two masks, all encoding
randomness, the old pads, the messages that ride; its one fresh entry is its pad; `inj`: different
entries of held messages are in different entries of the folded complex.

Main names:
  `V.val`, `V.datC`, `V.datN`, `V.mem`, `V.snd w0`: the sender: the data of each new message are
    read off the witness of the open test; independent coins: the pads.
  `StdNew.cut_put`: what the new messages hold is the witness of the open test: `V.N.cut` of the
    messages that the sender makes is (message, randomness) of the folded complex, whatever the
    coins.
  `V.close ..`: the second half of the closing (Cb/Req1/LdSegFit.lean: `LdCloseD`): N := V.N.N₀,
    cutN := V.N.cut, independent seeds, tl locations.
  `stdNew_snd`: `V.OK L t` (`M.OK` of all new messages) ⇒ the seven hypotheses of the one sending.
    (`StdM.OK`, Cb/Obj/LdObjectToyKit.lean: L and t enter its fields `list : M.Cm.ListAt M.e L` and
    `zk : M.Cm.Zk t` (`LdCode.ListAt`, `LdCode.Zk`, Cb/Ld/LdRel.lean); L: every native word has at
    most L codewords within `M.e` long positions.)
  `V.seg ..`, `stdNew_seg`: a segment without a body and without a batching: bridge-to-fold; the one
    sending; the locations; its hypotheses from those of bridge-to-fold and `V.OK`.
  `V.SegAll ..`, `stdNew_all`: what then, under hl (bridge-to-fold's hypotheses) and `V.OK L t`,
    holds of it (Cb/Req1/LdSeg.lean): its hypotheses; all of the bundle but zero knowledge
    (`GoodB`); knowledge soundness on collision-free statements into collision-free statements, at
    both ends those that also meet the base joint's own condition (`on` of `Sig.over`,
    Cb/Ld/LdSig.lean) (`KnowInto`, Ior/KnowColl.lean); its rounds are those of bridge-to-fold and 3
    more.
From `V.close` on, the group's set of common long positions, `G.P`, is nonempty.

`GoodB` is `IOR.GoodT` without its clause on zero knowledge. `IOR.GoodT` (likewise `IOR.Good`,
Ior/Chain.lean) bundles what is asked of one reduction, with its honest side, between two joints, at
given numbers; among its clauses: completeness between the honest relations, outside sets of
verifier randomness whose probabilities further clauses bound by the numbers; round-by-round
knowledge soundness (`Know`) between the relaxed relations, on the input joint's set of statements,
with a given extractor, at the numbers' list of errors; and one on honest-verifier zero knowledge.

Limits: this file does not say that the conditions can be met (Cb/Req1/LdSegToy.lean). It says
nothing on more than one pad place in a message, and nothing on riders of a next segment. The
standard parts are no proposal for a protocol.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupPlaceProofs
import Cb.Ld.LdGroupStdMsg
import Cb.Req1.LdSegWhole
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.Ood

section
variable {E : Type} [Field E] {S : Sig E} {G : Grp S} {Sh : GShape G}
  {kp : S.O → Prop} (Hd : GHeld Sh kp)

/-- one pad place in each message that is encoded anew -/
abbrev GHeld.padAt (ag : {a // Hd.cl a} → Prop) (pj : ∀ k : {k // ag k}, (S.om k.1.1.1).C.J) :
    ∀ k : {k // ag k}, (S.om k.1.1.1).C.J → Prop :=
  fun k j => j = pj k

instance (ag : {a // Hd.cl a} → Prop)
    (pj : ∀ k : {k // ag k}, (S.om k.1.1.1).C.J) (k : {k // ag k}) :
    DecidablePred (Hd.padAt ag pj k) :=
  fun j => inferInstanceAs (Decidable (j = pj k))

variable (ag : {a // Hd.cl a} → Prop)
  (pad : ∀ k : {k // ag k}, (S.om k.1.1.1).C.J → Prop) [∀ k, DecidablePred (pad k)]

/-- the entries that go into the carried message, when it has one fresh entry of its own -/
abbrev GHeld.Car : Type := {u : Hd.All ag pad Unit // ¬ Hd.InNew ag pad Unit u}

theorem GHeld.not_inNew_own : ¬ Hd.InNew ag pad Unit (.inr (.inr ())) := fun ⟨n, hn⟩ => by
  unfold GHeld.toNew at hn
  split_ifs at hn
  cases hn

/-- its own fresh entry -/
def GHeld.own : Hd.Car ag pad := ⟨.inr (.inr ()), Hd.not_inNew_own ag pad⟩

end

/-- Standard new messages of a closing: the data. -/
structure StdNew {E : Type} [Field E] {S : Sig E} {G : Grp S} {Sh : GShape G} {kp : S.O → Prop}
    (Hd : GHeld Sh kp) (Pn : Type) [Fintype Pn] where
  ag  : {a // Hd.cl a} → Prop
  [decAg : DecidablePred ag]
  pj  : ∀ k : {k // ag k}, (S.om k.1.1.1).C.J
  Mn  : ∀ _ : {k // ag k}, StdM E Pn
  cl  : ∀ k : {k // ag k}, {j : (S.om k.1.1.1).C.J // j ≠ pj k} ≃ (Mn k).Dt
  Mc  : StdM E Pn
  cc  : {v : Hd.Car ag (Hd.padAt ag pj) // v ≠ Hd.own ag (Hd.padAt ag pj)} ≃ Mc.Dt
  inj : ∀ n n' : Hd.Ent, Hd.sJ n.1 n.2 = Hd.sJ n'.1 n'.2 → n = n'

attribute [instance] StdNew.decAg

namespace StdNew
variable {E : Type} [Field E] {S : Sig E} {G : Grp S} {Sh : GShape G} {kp : S.O → Prop}
  {Hd : GHeld Sh kp} {Pn : Type} [Fintype Pn] (V : StdNew Hd Pn)

abbrev pad := Hd.padAt V.ag V.pj

/-- the entries of a message and of the same message encoded anew: a cell is a datum, the pad place
is the pad -/
def same (k : {k // V.ag k}) : (S.om k.1.1.1).C.J ≃ (V.Mn k).Cm.J :=
  (splitAt (V.pj k)).trans ((Equiv.sumCongr (V.cl k) (Equiv.refl Unit)).trans (V.Mn k).place)

open Classical in
/-- the carried message holds exactly what goes nowhere else: the data, and its own pad -/
def eC : Hd.Car V.ag V.pad ≃ V.Mc.Cm.J :=
  (splitAt (Hd.own V.ag V.pad)).trans ((Equiv.sumCongr V.cc (Equiv.refl Unit)).trans V.Mc.place)

variable [Fintype E]

/-- The new messages. -/
@[reducible] def N : GNew Hd where
  oc := V.Mc.om
  ag := V.ag
  on := fun k => (V.Mn k).om
  same := V.same
  pad := V.pad
  Qc := Unit
  eC := V.eC
  inj := V.inj

omit [Fintype E] in
theorem same_cell (k : {k // V.ag k}) (j : (S.om k.1.1.1).C.J) (h : j ≠ V.pj k) :
    V.same k j = (V.Mn k).place (.inl (V.cl k ⟨j, h⟩)) := by
  show (V.Mn k).place (Equiv.sumCongr (V.cl k) (Equiv.refl Unit) (splitAt (V.pj k) j)) = _
  rw [splitAt_ne h]
  rfl

omit [Fintype E] in
open Classical in
theorem eC_data (v : Hd.Car V.ag V.pad) (h : v ≠ Hd.own V.ag V.pad) :
    V.eC v = V.Mc.place (.inl (V.cc ⟨v, h⟩)) := by
  show V.Mc.place (Equiv.sumCongr V.cc (Equiv.refl Unit) (splitAt (Hd.own V.ag V.pad) v)) = _
  rw [splitAt_ne h]
  rfl

variable [DecidablePred kp] {Wl Wr : Type}

/-- the value of an entry that is placed: of the message, of the randomness of the folded complex;
at fresh entries 0 (their values are the sender's coins) -/
def val (w : (Sh.Cf.J → E) × (Sh.Cf.Q → E)) : V.N.U → E
  | .inl (.inl j) => w.1 j
  | .inl (.inr q) => w.2 q
  | .inr _ => 0

/-- the data of the carried message, of a message encoded anew -/
def datC (w : Wl × (((Sh.Cf.J → E) × (Sh.Cf.Q → E)) × Wr)) : V.Mc.Dt → E := fun d =>
  V.val w.2.1 (V.cc.symm d).1.1
def datN (k : {k // V.ag k}) (w : Wl × (((Sh.Cf.J → E) × (Sh.Cf.Q → E)) × Wr)) : (V.Mn k).Dt → E :=
  fun d => w.2.1.1 (Hd.sJ k.1 ((V.cl k).symm d).1)

/-- the members' senders -/
@[reducible] def mem (w0 : Wl × (((Sh.Cf.J → E) × (Sh.Cf.Q → E)) × Wr)) :
    ∀ a, (V.N.N₀.om a).Sender (Wl × (((Sh.Cf.J → E) × (Sh.Cf.Q → E)) × Wr)) Unit
  | none => V.Mc.snd V.datC w0
  | some k => (V.Mn k).snd (V.datN k) w0

/-- The sender: independent coins; the witness of the open test moves into the new messages. -/
@[reducible] def snd (w0 : Wl × (((Sh.Cf.J → E) × (Sh.Cf.Q → E)) × Wr)) :
    V.N.N₀.Sender (Wl × (((Sh.Cf.J → E) × (Sh.Cf.Q → E)) × Wr)) (Wl × Wr) :=
  Sig.Sender.ofMem (V.mem w0) (fun w => (w.1, w.2.2)) w0

/-- What the new messages hold is the witness of the open test. -/
theorem cut_put (w0 w : Wl × (((Sh.Cf.J → E) × (Sh.Cf.Q → E)) × Wr)) (k : ∀ a, (V.mem w0 a).Mk) :
    V.N.cut (fun a => (V.mem w0 a).upM ((V.mem w0 a).put w (k a))) = w.2.1 := by
  have hc : ∀ (u : V.N.U) (h : ¬ Hd.InNew V.ag V.pad Unit u), (⟨u, h⟩ : Hd.Car V.ag V.pad) ≠
        Hd.own V.ag V.pad →
      V.N.N₀.ents (fun a => (V.mem w0 a).upM ((V.mem w0 a).put w (k a))) (V.N.place u) =
        V.val w.2.1 u := by
    intro u h hne
    rw [V.N.place_not u h]
    show (V.Mc.snd V.datC w0).upM ((V.Mc.snd V.datC w0).put w (k none)) (V.eC ⟨u, h⟩) = _
    rw [V.eC_data _ hne, stdM_put]
    show V.val w.2.1 (V.cc.symm (V.cc ⟨⟨u, h⟩, hne⟩)).1.1 = _
    rw [Equiv.symm_apply_apply]
  refine Prod.ext (funext fun j => ?_) (funext fun q => ?_)
  · show V.N.N₀.ents (fun a => (V.mem w0 a).upM ((V.mem w0 a).put w (k a)))
        (V.N.place (.inl (.inl j))) = w.2.1.1 j
    by_cases h : Hd.InNew V.ag V.pad Unit (.inl (.inl j))
    · obtain ⟨n, hn, rfl⟩ := V.N.inNew_msg h
      rw [ldGroup_place_cell E S G Sh kp Hd V.N n.1 n.2 hn]
      show ((V.Mn n.1).snd (V.datN n.1) w0).upM
          (((V.Mn n.1).snd (V.datN n.1) w0).put w (k (some n.1))) (V.same n.1 n.2) = _
      rw [V.same_cell _ _ hn, stdM_put]
      show w.2.1.1 (Hd.sJ n.1.1 ((V.cl n.1).symm (V.cl n.1 ⟨n.2, hn⟩)).1) = _
      rw [Equiv.symm_apply_apply]
    · exact hc _ h fun he => by cases congrArg Subtype.val he
  · show V.N.N₀.ents (fun a => (V.mem w0 a).upM ((V.mem w0 a).put w (k a)))
        (V.N.place (.inl (.inr q))) = w.2.1.2 q
    refine hc _ (fun ⟨n, hn⟩ => ?_) fun he => by cases congrArg Subtype.val he
    unfold GHeld.toNew at hn
    split_ifs at hn
    cases hn

/-- what is asked of the standard messages -/
def OK (L t : ℕ) : Prop := V.Mc.OK L t ∧ ∀ k, (V.Mn k).OK L t

end StdNew

section
variable {E B Kc : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  {Sh : GShape G} {kp : S.O → Prop} [DecidablePred kp] {Hd : GHeld Sh kp} {Pn : Type} [Fintype Pn]
  (V : StdNew Hd Pn) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))
  {St₀ Wp : Type} {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))

/-- The second half of the closing: one sending of the new messages, independent seeds; tl
locations. -/
@[reducible] def StdNew.close
    (w0 : (Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp) (L t tl : ℕ) :
    LdCloseD (Hd.foldD Sb sl Z A₀) where
  N := V.N.N₀
  Sd := Sig.Seeds.indep _
  Wp' := Wp
  cutN := V.N.cut
  bk₀ := fun _ w' => w'
  Sn := V.snd w0
  L := fun _ => L
  tN := fun _ => t
  t := tl
  neP := inferInstanceAs (Nonempty G.P)

/-- What the sending asks. -/
theorem stdNew_snd (w0 : (Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp) {L t : ℕ}
    (tl : ℕ) (h : V.OK L t) :
    (V.close Sb sl Z A₀ w0 L t tl).snd.Hyp where
  laws := fun i => match i with
    | none => h.1.laws
    | some k => (h.2 k).laws
  fair := (ldSendFam_fair_indep E _).1
  list := fun i => match i with
    | none => stdM_list V.Mc h.1
    | some k => stdM_list (V.Mn k) (h.2 k)
  evades := fun i => match i with
    | none => stdM_evades V.Mc h.1
    | some k => stdM_evades (V.Mn k) (h.2 k)
  sender := ldSendMem_laws E _ _ _ (V.mem w0) (fun w => (w.1, w.2.2)) w0 _
    (fun a m r => match a with
      | none => stdM_enc V.Mc _ _ m r
      | some k => stdM_enc (V.Mn k) _ _ m r)
    (fun w k => Prod.ext rfl (Prod.ext (V.cut_put w0 w k) rfl))
  blind := ldSendMem_blind E _ _ _ (V.mem w0) (fun w => (w.1, w.2.2)) w0 _ fun a => match a with
    | none => stdM_blind V.Mc h.1 _ _
    | some k => stdM_blind (V.Mn k) (h.2 k) _ _
  hides := ldSendMem_hides E _ _ _ (V.mem w0) (fun w => (w.1, w.2.2)) w0 (fun _ => t) fun a => match a with
    | none => stdM_hides V.Mc h.1 _ _
    | some k => stdM_hides (V.Mn k) (h.2 k) _ _

/-- A segment without a body: bridge-to-fold; the one sending; the locations. -/
def StdNew.seg (l : Link Kc (Hd.foldD Sb sl Z A₀).src.J (Hd.foldD Sb sl Z A₀).mid)
    (w0 : (Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp) (L t tl : ℕ) :
    LdSeg (Hd.foldD Sb sl Z A₀).src (V.close Sb sl Z A₀ w0 L t tl).loc.tgt where
  b := (Hd.foldD Sb sl Z A₀).src
  b₁ := (Hd.foldD Sb sl Z A₀).src
  c := (Hd.foldD Sb sl Z A₀).tgt
  body := .nil _
  bat := .nil _
  fold := (V.close Sb sl Z A₀ w0 L t tl).foldP l
  snd := (V.close Sb sl Z A₀ w0 L t tl).snd
  loc := (V.close Sb sl Z A₀ w0 L t tl).locP
  bodyT := LdProg.all_nil _ _
  batT := LdProg.all_nil _ _
  foldT := (LdProg.all_snoc' _ _ _).2 ⟨LdProg.all_nil _ _, Or.inl rfl⟩
  locT := (LdProg.all_snoc' _ _ _).2 ⟨LdProg.all_nil _ _, Or.inl rfl⟩

theorem stdNew_seg (l : Link Kc (Hd.foldD Sb sl Z A₀).src.J (Hd.foldD Sb sl Z A₀).mid)
    (w0 : (Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp) {L t : ℕ} (tl : ℕ)
    (hl : (Hd.foldD Sb sl Z A₀).Hyp l) (h : V.OK L t) :
    (V.seg Sb sl Z A₀ l w0 L t tl).Hyp := by
  obtain ⟨f1, f2, f3⟩ :=
    ldSegFit_hyp E Kc _ (V.close Sb sl Z A₀ w0 L t tl) l hl (stdNew_snd V Sb sl Z A₀ w0 tl h)
  exact ⟨LdProg.hyp_nil _, LdProg.hyp_nil _, f1, f2, f3⟩

/-- What holds of the segment: `Hyp`, `GoodB`, `KnowInto`, `nAll` (in words: the head's row of
`V.SegAll`). -/
def StdNew.SegAll (l : Link Kc (Hd.foldD Sb sl Z A₀).src.J (Hd.foldD Sb sl Z A₀).mid)
    (w0 : (Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp)
    (L t tl : ℕ) (dw : (Hd.foldD Sb sl Z A₀).src.W) : Prop :=
  (V.seg Sb sl Z A₀ l w0 L t tl).Hyp ∧ ((V.seg Sb sl Z A₀ l w0 L t tl).chain.link dw).GoodB ∧
  ((V.seg Sb sl Z A₀ l w0 L t tl).chain.link dw).R.red.KnowInto
    ((Hd.foldD Sb sl Z A₀).src.S.over (Hd.foldD Sb sl Z A₀).src.A).on
    ((V.close Sb sl Z A₀ w0 L t tl).loc.tgt.S.over (V.close Sb sl Z A₀ w0 L t tl).loc.tgt.A).on
    ((Hd.foldD Sb sl Z A₀).src.S.over (Hd.foldD Sb sl Z A₀).src.A).relR
    ((V.close Sb sl Z A₀ w0 L t tl).loc.tgt.S.over (V.close Sb sl Z A₀ w0 L t tl).loc.tgt.A).relR
    ((V.seg Sb sl Z A₀ l w0 L t tl).chain.link dw).ext
    ((V.seg Sb sl Z A₀ l w0 L t tl).chain.link dw).P.err ∧
  (V.seg Sb sl Z A₀ l w0 L t tl).nAll = l.R.shape.nAll + 3

theorem stdNew_all (l : Link Kc (Hd.foldD Sb sl Z A₀).src.J (Hd.foldD Sb sl Z A₀).mid)
    (w0 : (Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp) {L t : ℕ} (tl : ℕ)
    (dw : (Hd.foldD Sb sl Z A₀).src.W) (hl : (Hd.foldD Sb sl Z A₀).Hyp l) (h : V.OK L t) :
    V.SegAll Sb sl Z A₀ l w0 L t tl dw := by
  have hs := stdNew_seg V Sb sl Z A₀ l w0 tl hl h
  refine ⟨hs, ldSeg_goodB E Kc _ _ _ dw hs, ldSeg_into E Kc _ _ _ dw hs, ?_⟩
  obtain ⟨r1, -, -, r4, r5, -⟩ := ldSeg_rounds E Kc
  have a1 := (r1 _ (V.close Sb sl Z A₀ w0 L t tl).snd).1
  have a2 := (r4 (V.close Sb sl Z A₀ w0 L t tl).loc).1
  have a3 := (r5 (Hd.foldD Sb sl Z A₀) l).1
  simp only [LdSeg.nAll, StdNew.seg, LdCloseD.foldP, LdCloseD.locP,
    LdProg.nAll, LdMv.chain, Chain.nAll]
  rw [a1, a2, a3]
  omega

end
end Cb
