-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupNewFmt.lean: under the hypotheses of `stdNew_seg_fmt`, the segment "bridge-to-fold; the
one sending; the locations" (`V.seg` of Cb/Ld/LdGroupNewStd.lean at the link of
Cb/Ld/LdGroupSeg.lean, with its standard new messages) has the format of a preamble, whatever is
carried beside it: any signature, any group of it, any carried joint, and oracle messages that are
kept, no members and not held.

Definitions, statements as theorems, proofs.
In standard terms: a demand is a predicate on finite sets of oracle positions; a link has the format
(`Link.Fmt`, Cb/Req1/LdReqFormat.lean) between a format at its input joint and one at its output
joint, each with its demand; `Link.Fmt` has four clauses: idx (`IdxLink`), pass (`Passes`: rc is
handed on), hands (`Hands`, Cb/Ld/LdWfPre.lean), bears (`Bears`, Ior/Bears.lean). The format of a
joint (`JFmt`): ix (where the index sits), rc (what is read off the explicit part: the record), px
(what is read off a witness: the prover encoded index), q (its demand).

Why: Cb/Obj/LdObjectReqStd.lean has the formats of one request, in which nothing but the request's
own claim is carried and, of the carried oracles, the demand allows nothing of the kept oracle
messages (`rqQF`). A request with a pending tensor row carries more: that row, a ghost, and the
message with the masks for it, which crosses the closing: it is kept at the bridge, is no member of
the group and is not held in the folded word. Here the segment's format is shown in that generality;
who sends what before, and what follows, is left to the caller.

The demands on positions, backwards. q₂: what may still be asked, after the segment, of the further
oracles and of the messages that are kept and not held (a parameter).
  at the end: `D.S₂.qSum N q₂ tN`: q₂, and at most `tN a` long positions of each new message.
  `D.qOpen q₂ tl`: with the test open: at most tl positions of the open word, and q₂.
    `LdCloseD.loc_need`: the locations need no more (for any second half `Q : LdCloseD D`).
  `D.qCar q₂`: of the carried oracles after the bridge: q₂; nothing of the held messages.
    `LdFoldD.open_need`: tl ≤ t (see its docstring).
  `Hd.qSrc .. q₂ t`: before the bridge: the sources of at most t common long positions of the group,
    and of q₂.
  `ldGroup_qSrc_le`: in numbers: if q₂ allows q₀ of the further oracles and at most `b₂ a` long
    positions of a message that is kept and not held, then before the bridge: q₀, and of each oracle
    message at most `Hd.bSrc`: t if it is a member, plus b₂ if it is kept and not held.

Main names:
  `ldGroup_link_fmt`: bridge, arrangement, fold: under hc (every oracle message is a member of the
    group or kept), hS, hY, hZ, hLi, hF (the shape's laws, the fold's own hypotheses, the evader
    evades, a bound on the list of the complex, `G.Fits`), the link of Cb/Ld/LdGroupSeg.lean has the
    format up to the joint "the folded word beside what is carried".
  `stdNew_seg_fmt`: under hc, hS, hY, hZ, hLi, hF, `V.OK L₂ t₂` and tl ≤ t, `V.seg` of
    Cb/Ld/LdGroupNewStd.lean, at that link, has the format, for any place i of the encoded index
    among the further oracles, any rc, px.
  `stdNew_seg_zk`: zero knowledge asks nothing of the segment's own moves, beside their hypotheses,
    in this sense: `(V.seg ..).Zk base` for every base (`LdSeg.Zk`, Cb/Req1/LdReq.lean: a condition,
    a premise of `Spec.ldReq_seg_ok`).
In these three and in `ldGroup_qSrc_le` the group's set of common long positions, `G.P`, is
nonempty.

Limits: this file does not say that masks in a message that crosses the closing stay fresh
(Cb/Req1/LdSegCarryClose.lean). It does not say that the segment is zero knowledge: `stdNew_seg_zk`
gives the condition `Zk` alone, which `Spec.ldReq_seg_ok` (Cb/Req1/LdReq.lean) takes as a premise.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupNewStd
import Cb.Req1.LdSegFormatMoves
import Cb.Req1.LdSegFormatGroup
import Cb.Ld.LdLinCloseDemandProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood

section
variable {E Kc : Type} [Field E] [Fintype E] (D : LdFoldD E Kc)

/-- a position of (further oracles, messages kept and not held), among the carried oracles after the
bridge -/
def LdFoldD.emb : (D.E₀.prod D.S₂.ext).Pos → (D.E₀.prod D.S₁.ext).Pos
  | .inl p => .inl p
  | .inr s => .inr ⟨s.1.1, s.2⟩

/-- the same position, among the oracles with the test open -/
def LdFoldD.embO : (D.E₀.prod D.S₂.ext).Pos → D.tgt.Ex.Pos
  | .inl p => .inl (.inr p)
  | .inr s => .inr s

variable (q₂ : Finset (D.E₀.prod D.S₂.ext).Pos → Prop) (tl : ℕ)

open Classical in
/-- of the carried oracles: what q₂ allows of the further oracles and of the messages that are kept
and not held; nothing of the held ones -/
def LdFoldD.qCar : Finset (D.E₀.prod D.S₁.ext).Pos → Prop := fun W =>
  ∃ U₂, q₂ U₂ ∧ W = U₂.image D.emb

open Classical in
/-- with the test open: at most tl positions of the open word, and what q₂ allows -/
def LdFoldD.qOpen : Finset D.tgt.Ex.Pos → Prop := fun U =>
  ∃ (X : Finset D.Cf.ext.Pos) (U₂ : Finset (D.E₀.prod D.S₂.ext).Pos),
    X.card ≤ tl ∧ q₂ U₂ ∧ U = X.image (fun x => Sum.inl (Sum.inl x)) ∪ U₂.image D.embO

open Classical in
/-- if tl ≤ t: what is needed with the test open is, before the step that lets the kept messages be
read in the folded word, within (at most t positions of the folded word, qCar) -/
theorem LdFoldD.open_need (t : ℕ) (ht : tl ≤ t) (U : Finset D.tgt.Ex.Pos) (W : Finset D.mid.E.Pos)
    (hW : ∀ x, x ∈ W ↔ ∃ u ∈ U, x ∈ D.pE.src u) (hU : D.qOpen q₂ tl U) :
    besideQ (fun S : Finset D.Cf.ext.Pos => S.card ≤ t) (D.qCar q₂) W := by
  obtain ⟨X, U₂, hX, h2, rfl⟩ := hU
  refine ⟨le_trans (Finset.card_le_card fun x hx => ?_) (le_trans hX ht), U₂,
    h2, Finset.ext fun x => ?_⟩
  · obtain ⟨u, hu, hs⟩ := (hW _).1 (Finset.mem_toLeft.1 hx)
    rcases Finset.mem_union.1 hu with hu | hu
    · obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hu
      obtain rfl : x = x' := Sum.inl.inj (Finset.mem_singleton.1 hs)
      exact hx'
    · obtain ⟨u', -, rfl⟩ := Finset.mem_image.1 hu
      rcases u' with p | s
      · obtain ⟨q, -, hq⟩ := (mem_biUnion_at _).1 hs
        cases Finset.mem_singleton.1 hq
      · obtain ⟨q, -, hq⟩ := (mem_biUnion_at _).1 hs
        obtain ⟨q', -, hq'⟩ := (mem_biUnion_at _).1 hq
        cases Finset.mem_singleton.1 hq'
  · rw [Finset.mem_toRight, hW, Finset.mem_image]
    constructor
    · rintro ⟨u, hu, hs⟩
      rcases Finset.mem_union.1 hu with hu | hu
      · obtain ⟨x', -, rfl⟩ := Finset.mem_image.1 hu
        cases Finset.mem_singleton.1 hs
      · obtain ⟨u', hu', rfl⟩ := Finset.mem_image.1 hu
        refine ⟨u', hu', ?_⟩
        rcases u' with p | s
        · obtain ⟨q, hq0, hq⟩ := (mem_biUnion_at _).1 hs
          obtain rfl := Finset.mem_singleton.1 hq0
          exact (Sum.inr.inj (Finset.mem_singleton.1 hq)).symm
        · obtain ⟨q, hq0, hq⟩ := (mem_biUnion_at _).1 hs
          obtain rfl := Finset.mem_singleton.1 hq0
          obtain ⟨q', hq0', hq'⟩ := (mem_biUnion_at _).1 hq
          obtain rfl := Finset.mem_singleton.1 hq0'
          exact (Sum.inr.inj (Finset.mem_singleton.1 hq')).symm
    · rintro ⟨u', hu', rfl⟩
      refine ⟨D.embO u', Finset.mem_union.2 (Or.inr (Finset.mem_image.2 ⟨u', hu', rfl⟩)), ?_⟩
      rcases u' with p | s
      · exact (mem_biUnion_at _).2 ⟨_, Finset.mem_singleton_self _, Finset.mem_singleton_self _⟩
      · exact (mem_biUnion_at _).2
          ⟨_, Finset.mem_singleton_self _,
            (mem_biUnion_at _).2 ⟨_, Finset.mem_singleton_self _, Finset.mem_singleton_self _⟩⟩

open Classical in
/-- if what follows asks within `qSum Q.N q₂ Q.tN` (`hU`): what the locations need is within what
the one sending bears, and qOpen -/
theorem LdCloseD.loc_need (Q : LdCloseD D) (ρ : Rho Q.loc.link.R.shape)
    (U : Finset Q.loc.tgt.Ex.Pos) (hU : D.S₂.qSum Q.N (E₀ := D.E₀) q₂ Q.tN U) :
    D.S₂.qSum Q.N (E₀ := D.tgt.E₀) (D.qOpen q₂ Q.t) Q.tN (Q.loc.link.R.need ρ U) := by
  have hn := ldFmt_loc_need E Kc Q.loc ρ U
  refine ⟨fun W hW =>
      ⟨Finset.univ.image ρ.1,
        (U.biUnion (D.S₂.mergeE Q.N D.E₀).src).toLeft,
        le_trans Finset.card_image_le (le_of_eq (by rw [Finset.card_univ, Fintype.card_fin])),
        hU.1 _ fun p => by rw [Finset.mem_toLeft, Finset.mem_biUnion],
        Finset.ext fun p => ?_⟩,
    fun a => ?_⟩
  · rw [hW, Finset.mem_union, Finset.mem_image, Finset.mem_image]
    constructor
    · rintro ⟨u, hu, hs⟩
      rcases (hn _).1 hu with ⟨k, rfl⟩ | ⟨u', hu1, rfl⟩
      · exact Or.inl
          ⟨ρ.1 k, Finset.mem_image.2 ⟨k, Finset.mem_univ _, rfl⟩,
            (Sum.inl.inj (Finset.mem_singleton.1 hs)).symm⟩
      · right
        rcases u' with p0 | ⟨a | a, z⟩
        · exact ⟨.inl p0,
            Finset.mem_toLeft.2 (Finset.mem_biUnion.2 ⟨_, hu1, Finset.mem_singleton_self _⟩),
            (Sum.inl.inj (Finset.mem_singleton.1 hs)).symm⟩
        · exact ⟨.inr ⟨a, z⟩,
            Finset.mem_toLeft.2 (Finset.mem_biUnion.2 ⟨_, hu1, Finset.mem_singleton_self _⟩),
            (Sum.inl.inj (Finset.mem_singleton.1 hs)).symm⟩
        · cases Finset.mem_singleton.1 hs
    · rintro (⟨x, hx, rfl⟩ | ⟨p2, hp2, rfl⟩)
      · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx
        exact ⟨.inl (.inl (ρ.1 k)), (hn _).2 (Or.inl ⟨k, rfl⟩), Finset.mem_singleton_self _⟩
      · obtain ⟨u', hu1, hs⟩ := Finset.mem_biUnion.1 (Finset.mem_toLeft.1 hp2)
        refine ⟨Q.loc.oldPos u', (hn _).2 (Or.inr ⟨u', hu1, rfl⟩), ?_⟩
        rcases u' with p0 | ⟨a | a, z⟩
        · obtain rfl := Sum.inl.inj (Finset.mem_singleton.1 hs)
          exact Finset.mem_singleton_self _
        · obtain rfl := Sum.inl.inj (Finset.mem_singleton.1 hs)
          exact Finset.mem_singleton_self _
        · cases Finset.mem_singleton.1 hs
  · refine le_trans (cnt_mono fun x hx => ?_) (hU.2 a)
    rcases (hn _).1 hx with ⟨k, hk⟩ | ⟨u', hu1, hu'⟩
    · cases hk
    · rcases u' with p | s'
      · cases hu'
      · obtain rfl := Sum.inr.inj hu'
        exact hu1

end

section
variable {E B Kc : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  {Sh : GShape G} {kp : S.O → Prop} [DecidablePred kp] {Hd : GHeld Sh kp} {Pn : Type} [Fintype Pn]
  (V : StdNew Hd Pn) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))
  {St₀ Wp : Type} {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp)) {E0 : ExtSpec}
  {Rc Pw : Type} (i : IxAt E0 E₀) (rc : St₀ → Rc) (px : Wp → Pw)
  (q₂ : Finset (E₀.prod (Hd.foldD Sb sl Z A₀).S₂.ext).Pos → Prop) (hc : ∀ o, G.mem o ∨ kp o)
  (dw : S.Wit × Wp) (d t : ℕ) (Lst mC mS mW : ℕ → ℕ) (L : ℕ)

open Classical in
/-- before the bridge: the sources of at most t common long positions of the group and of what q₂
allows -/
def GHeld.qSrc : Finset (Hd.foldD Sb sl Z A₀).src.Ex.Pos → Prop := fun W =>
  ∃ U,
    besideQ (fun X : Finset G.C.ext.Pos => X.card ≤ t) ((Hd.foldD Sb sl Z A₀).qCar q₂) U ∧
    W = U.biUnion (ldBrG G kp E₀).src

open Classical in
/-- For `G.P` nonempty and under `hc`, `hS`, `hY`, `hZ`, `hLi`, `hF`: bridge, arrangement, fold has
the format, whatever is carried. -/
theorem ldGroup_link_fmt (hS : Sh.OK) (hY : Sh.par.Hyp d G.e t Lst mC mS mW) (hZ : Z.OK)
    (hLi : G.C.ListAt G.e L) (hF : G.Fits) :
    (Hd.link Sb sl Z A₀ hc dw d t Lst mC mS mW L).Fmt
      ((Hd.foldD Sb sl Z A₀).src.fmt i (fun st => rc st.2) px (Hd.qSrc Sb sl Z A₀ q₂ t))
      ((Hd.foldD Sb sl Z A₀).fmtMid
        i rc px (besideQ (fun X => X.card ≤ t) ((Hd.foldD Sb sl Z A₀).qCar q₂))) where
  idx := ldFmt_run_idx E B _ S G kp Sb sl Z _ _ _ _ i
  pass := ldFmt_run_pass E B _ _ S G kp Sb sl Z _ _ _ rc
  hands := ldFmt_run_hands E B _ _ _ S G kp Sb sl Z _ _ _ px _
  bears := (ldGroup_fold E B Kc _ _ S G Sh kp Sb sl Z L _ A₀ hc dw d t Lst mC mS mW
    (Hd.qSrc Sb sl Z A₀ q₂ t) ((Hd.foldD Sb sl Z A₀).qCar q₂) hS hY hZ hLi hF fun U hU =>
      ⟨U, hU, Finset.ext fun _ => (mem_biUnion_at _).trans (mem_biUnion_at _).symm⟩).1.bears

/-- the bound before the bridge: t for a member, and b₂ for a message that is kept and not held -/
def GHeld.bSrc (b₂ : (Hd.foldD Sb sl Z A₀).S₂.O → ℕ) : S.O → ℕ := fun o =>
  (if G.mem o then t else 0) +
    (if h : kp o then (if h' : Hd.cl ⟨o, h⟩ then 0 else b₂ ⟨⟨o, h⟩, h'⟩) else 0)

open Classical in
/-- In numbers, for `G.P` nonempty: if q₂ allows q₀ of the further oracles and at most `b₂ a` long
positions of each message that is kept and not held, then before the bridge: q₀, and of each oracle
message at most bSrc. -/
theorem ldGroup_qSrc_le (q₀ : Finset E₀.Pos → Prop) (b₂ : (Hd.foldD Sb sl Z A₀).S₂.O → ℕ)
    (h2 : ∀ U₂, q₂ U₂ → (Hd.foldD Sb sl Z A₀).S₂.qFam q₀ b₂ U₂)
    (W : Finset (Hd.foldD Sb sl Z A₀).src.Ex.Pos) (hW : Hd.qSrc Sb sl Z A₀ q₂ t W) :
    S.qFam q₀ (Hd.bSrc Sb sl Z A₀ t b₂) W := by
  obtain ⟨U, ⟨hU1, U₂, hq, hU2⟩, rfl⟩ := hW
  obtain ⟨hq0, hb⟩ := h2 U₂ hq
  refine ⟨?_, fun o => ?_⟩
  · rw [ldBrG_toLeft, hU2]
    have e : (U₂.image (Hd.foldD Sb sl Z A₀).emb).toLeft = U₂.toLeft := Finset.ext fun p => by
      rw [Finset.mem_toLeft, Finset.mem_toLeft, Finset.mem_image]
      constructor
      · rintro ⟨s, hs, he⟩
        rcases s with p' | s
        · obtain rfl : p' = p := Sum.inl.inj he
          exact hs
        · cases he
      · exact fun hp => ⟨_, hp, rfl⟩
    rw [e]
    exact hq0
  · refine (cnt_le_add (ldBrG_mem_inr G kp E₀ _ U o)).trans (Nat.add_le_add ?_ ?_)
    · by_cases h : G.mem o
      · rw [if_pos h, cnt_eq_card_filter]
        refine le_trans
          (le_trans (Finset.card_le_card (t := U.toLeft.image (G.pos ⟨o, h⟩)) fun x hx => ?_)
            Finset.card_image_le) hU1
        obtain ⟨_, z, hz, hzx⟩ := (Finset.mem_filter.1 hx).2
        exact Finset.mem_image.2 ⟨z, hz, hzx⟩
      · rw [if_neg h, cnt_false fun x hx => h hx.1]
    · by_cases h : kp o
      · rw [dif_pos h]
        have key : ∀ x : (S.om o).P,
            (∃ h : kp o, (Sum.inr ⟨⟨o, h⟩, x⟩ : (E₀.prod (S.sub kp).ext).Pos) ∈ U.toRight) →
            ∃ h' : ¬ Hd.cl ⟨o, h⟩,
              (Sum.inr ⟨⟨⟨o, h⟩, h'⟩, x⟩ : (E₀.prod (Hd.foldD Sb sl Z A₀).S₂.ext).Pos) ∈ U₂ := by
          rintro x ⟨_, hx⟩
          rw [hU2] at hx
          obtain ⟨s, hs, he⟩ := Finset.mem_image.1 hx
          rcases s with p' | ⟨⟨⟨o', ho'⟩, hn⟩, x'⟩
          · cases he
          · have he' : (⟨⟨o', ho'⟩, x'⟩ : (S.sub kp).ext.Pos) = ⟨⟨o, h⟩, x⟩ := Sum.inr.inj he
            obtain rfl : o' = o := congrArg (fun s => s.1.1) he'
            obtain rfl : x' = x := eq_of_heq (Sigma.mk.inj he').2
            exact ⟨hn, hs⟩
        by_cases h' : Hd.cl ⟨o, h⟩
        · rw [dif_pos h', cnt_false fun x hx => (key x hx).1 h']
        · rw [dif_neg h']
          exact (cnt_mono fun x hx => (key x hx).2).trans (hb ⟨⟨o, h⟩, h'⟩)
      · rw [dif_neg h, cnt_false fun x hx => h hx.1]

variable (w0 : (Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp) (L₂ t₂ tl : ℕ)

open Classical in
/-- Under the hypotheses of its statement: the segment has the format, whatever is carried: from
(the sources of at most t common positions of the group, and of what q₂ allows) to (at most t₂
long positions of each new message, and what q₂ allows of the further oracles and of the
messages that are kept and not held). -/
theorem stdNew_seg_fmt (hS : Sh.OK) (hY : Sh.par.Hyp d G.e t Lst mC mS mW) (hZ : Z.OK)
    (hLi : G.C.ListAt G.e L) (hF : G.Fits) (h₂ : V.OK L₂ t₂) (ht : tl ≤ t) :
    (V.seg Sb sl Z A₀ (Hd.link Sb sl Z A₀ hc dw d t Lst mC mS mW L) w0 L₂ t₂ tl).Fmt
      ((Hd.foldD Sb sl Z A₀).src.fmt i (fun st => rc st.2) px (Hd.qSrc Sb sl Z A₀ q₂ t))
      ((V.close Sb sl Z A₀ w0 L₂ t₂ tl).loc.tgt.fmt
        i (fun st => rc st.2) px ((Hd.foldD Sb sl Z A₀).S₂.qSum V.N.N₀ q₂ fun _ => t₂)) := by
  refine ⟨_, _,
    (Hd.foldD Sb sl Z A₀).tgt.fmt
      (i.inr _) (fun st => rc st.2) (fun w => px w.2) ((Hd.foldD Sb sl Z A₀).qOpen q₂ tl),
    (V.close Sb sl Z A₀ w0 L₂ t₂ tl).snd.tgt.fmt (i.inr _) (fun st => rc st.2) px
      ((Hd.foldD Sb sl Z A₀).S₂.qSum V.N.N₀ ((Hd.foldD Sb sl Z A₀).qOpen q₂ tl) fun _ => t₂),
    (LdProg.fmt_nil _ _ _).2 rfl,
    (LdProg.fmt_nil _ _ _).2 rfl,
    ?_, ?_, ?_⟩
  · refine (LdProg.fmt_snoc _ _ _ _).2 ⟨_, (LdProg.fmt_nil _ _ _).2 rfl, (Chain.fmt_one _ _ _).2 ?_⟩
    exact ldFmt_fold E Kc E0 Rc Pw (Hd.foldD Sb sl Z A₀) _ i rc px _ _ _
      (ldGroup_link_fmt Sb sl Z A₀ i rc px q₂ hc dw d t Lst mC mS mW L hS hY hZ hLi hF)
      (fun U W hW hU => (Hd.foldD Sb sl Z A₀).open_need q₂ tl t ht U W hW hU)
  · exact ldFmt_send E Kc E0 Rc Pw (Hd.foldD Sb sl Z A₀).tgt
      (V.close Sb sl Z A₀ w0 L₂ t₂ tl).snd (i.inr _) (fun st => rc st.2) (fun w => px w.2) px _
      (stdNew_snd V _ _ _ _ w0 tl h₂) fun _ => rfl
  · refine (LdProg.fmt_snoc _ _ _ _).2 ⟨_, (LdProg.fmt_nil _ _ _).2 rfl, (Chain.fmt_one _ _ _).2 ?_⟩
    exact ldFmt_loc E Kc E0 Rc Pw (V.close Sb sl Z A₀ w0 L₂ t₂ tl).loc i rc px _ _
      (fun ρ U hU => LdCloseD.loc_need _ q₂ (V.close Sb sl Z A₀ w0 L₂ t₂ tl) ρ U hU)

/-- For `G.P` nonempty: zero knowledge asks nothing of the segment, beside its hypotheses, in this
sense: `(V.seg ..).Zk base` for every base (`LdSeg.Zk`, Cb/Req1/LdReq.lean: a condition, a premise
of `Spec.ldReq_seg_ok`): no move of it is a sub-protocol or a split -/
theorem stdNew_seg_zk (l : Link Kc (Hd.foldD Sb sl Z A₀).src.J (Hd.foldD Sb sl Z A₀).mid)
    (base : MaskFact (Hd.foldD Sb sl Z A₀).src.J.W → Prop) :
    (V.seg Sb sl Z A₀ l w0 L₂ t₂ tl).Zk base :=
  ⟨ldReq_zk_free E Kc _ _ _ _ (LdProg.all_nil _ _),
    ldReq_zk_free E Kc _ _ _ _ (LdProg.all_nil _ _),
    ldReq_zk_free E Kc _ _ _ _
      ((LdProg.all_snoc' _ _ _).2
        ⟨LdProg.all_nil _ _, ⟨fun h => LdTag.noConfusion h, fun h => LdTag.noConfusion h⟩⟩),
    ldReq_zk_free E Kc _ _ _ _
      ((LdProg.all_snoc' _ _ _).2
        ⟨LdProg.all_nil _ _, ⟨fun h => LdTag.noConfusion h, fun h => LdTag.noConfusion h⟩⟩)⟩

end
end Cb
