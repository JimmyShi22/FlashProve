-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupNewRide.lean: this file is for toys (a toy: a small example instance). In the code
switch that follows the fold of several oracle codewords, the prover message that carries the new
codewords also carries the first oracle codewords of the next part of the protocol ("riders"). This
file defines that step and derives, under the hypotheses of its statements, the hypotheses that the
composition theorems ask of it.

Definitions, statements as theorems, proofs. Generic: an abstract field, variable codes.

Why: a segment has, between its fold and its locations, one sending (Cb/Req1/LdSeg.lean, part
"snd"): the new messages of the closing and the first oracle messages of what follows. The second
half of a closing in Cb/Ld/LdGroupNewStd.lean (`V.close`) sends the new messages alone. Here the
same with riders.

Main names:
  `RideD E W`, `Rd.OK`: the riders: any family, a sender for each member on the witness W of the
    sending (so its data may be read off the further witness, its masks may be coins), bounds for
    lists, positions borne; asked, member by member: the code's laws, the list, the sample evades,
    the sender's first law, "the law of the answers does not depend on the witness" (`blind`:
    `OMsg.Sender.Blind`, Cb/Ld/LdSend.lean), the encoder hides (`hides`: `Enc.Hides`,
    Cb/Gen/Code.lean).
  `V.closeR .. Rd`: the second half of a closing, with riders.
  `stdNewR_snd`: `V.OK L t`, `Rd.OK` ⇒ the seven hypotheses of the sending (`LdSendD.Hyp`,
    Cb/Req1/LdSegKit.lean).
  `V.pJR`, `V.pQR`, `stdNewR_lin`, `stdNewR_rows_new`: what is claimed after the locations.
  `pk.seg1R .. Rd`: the whole segment from a bundle (Cb/Ld/LdGroupPack.lean), with riders;
    `gPack_seg1R` (its hypotheses), `gPack_seg1R_zk` (zero knowledge asks of it what it asks of the
    body, beside its hypotheses), `gPack_seg1R_fmt`; each under the hypotheses of its statement.
In the statements on `V.closeR` the group's set of common long positions, `G.P`, is nonempty; a
bundle has that as a field.

Limits: this file does not say that masks in a rider are fresh after the segment (the sending's own
matter: Cb/Ld/LdSendFresh*.lean; the locations do not read a rider; at this closing:
`stdNewR_fresh`, `stdNewR_cutQuiet`, Cb/Ld/LdGroupNewRideFresh.lean, each under its hypotheses). No
instance of its own. This file gives no instance that meets its hypotheses, so as far as this file
shows its theorems may hold of nothing. `V.closeR` is the case "all of the further witness is handed
on" of `V.closeRW` (Cb/Ld/LdGroupNewRideW.lean; `stdNewW_old` there: by definition).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupPackFmt
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood

/-- Oracle messages that ride with a sending: the data: a family, a sender for each member (on the
witness W of the sending), bounds for lists, numbers of long positions that the encodings bear. -/
structure RideD (E W : Type) [Field E] where
  N  : Sig E
  m  : ∀ b, (N.om b).Sender W Unit
  L  : N.O → ℕ
  t  : N.O → ℕ

/-- What is asked of them, member by member. -/
structure RideD.OK {E W : Type} [Field E] [Fintype E] (Rd : RideD E W) : Prop where
  laws   : ∀ b, (Rd.N.om b).C.Laws
  list   : ∀ b, (Rd.N.om b).ListLE (Rd.L b)
  evades : ∀ b, (Rd.N.om b).Evades
  enc    : ∀ b m r,
    (Rd.N.om b).upW ((Rd.m b).N.enc m r) = (Rd.N.om b).C.enc ((Rd.m b).upM m) ((Rd.m b).upR r)
  blind  : ∀ b, (Rd.m b).Blind
  hides  : ∀ b, (Rd.m b).N.Hides ((Rd.N.om b).C.budT (Rd.t b))

section
variable {E B Kc : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  {Sh : GShape G} {kp : S.O → Prop} [DecidablePred kp] {Hd : GHeld Sh kp} {Pn : Type} [Fintype Pn]
  (V : StdNew Hd Pn) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))
  {St₀ Wp : Type} {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (w0 : (Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp) (L t tl : ℕ)
  (Rd : RideD E ((Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp))

/-- the members' senders: the new messages', the riders' -/
@[reducible] def StdNew.memR :
    ∀ a, ((V.N.N₀.sum Rd.N).om a).Sender
      ((Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp) Unit
  | .inl a => V.mem w0 a
  | .inr b => Rd.m b

/-- The second half of the closing, with riders: one sending of the new messages and of the riders,
independent coins and seeds; the open word's witness is cut out of the new messages alone; tl
locations. -/
@[reducible] def StdNew.closeR : LdCloseD (Hd.foldD Sb sl Z A₀) where
  N := V.N.N₀.sum Rd.N
  Sd := Sig.Seeds.indep _
  Wp' := Wp
  cutN := fun m => V.N.cut fun a => m (.inl a)
  bk₀ := fun _ w' => w'
  Sn := Sig.Sender.ofMem (V.memR Sb sl Z A₀ w0 Rd) (fun w => (w.1, w.2.2)) w0
  L := Sum.elim (fun _ => L) Rd.L
  tN := Sum.elim (fun _ => t) Rd.t
  t := tl
  neP := inferInstanceAs (Nonempty G.P)

/-- What the sending asks: for `G.P` nonempty, `V.OK L t` (`h`) and `Rd.OK` (`hR`) give its seven
hypotheses. -/
theorem stdNewR_snd (h : V.OK L t) (hR : Rd.OK) : (V.closeR Sb sl Z A₀ w0 L t tl Rd).snd.Hyp where
  laws := fun i => match i with
    | .inl none => h.1.laws
    | .inl (some k) => (h.2 k).laws
    | .inr b => hR.laws b
  fair := (ldSendFam_fair_indep E _).1
  list := fun i => match i with
    | .inl none => stdM_list V.Mc h.1
    | .inl (some k) => stdM_list (V.Mn k) (h.2 k)
    | .inr b => hR.list b
  evades := fun i => match i with
    | .inl none => stdM_evades V.Mc h.1
    | .inl (some k) => stdM_evades (V.Mn k) (h.2 k)
    | .inr b => hR.evades b
  sender := ldSendMem_laws E _ _ _ (V.memR Sb sl Z A₀ w0 Rd) (fun w => (w.1, w.2.2)) w0 _
    (fun a m r => match a with
      | .inl none => stdM_enc V.Mc _ _ m r
      | .inl (some k) => stdM_enc (V.Mn k) _ _ m r
      | .inr b => hR.enc b m r)
    (fun w k => Prod.ext rfl (Prod.ext (V.cut_put w0 w fun a => k (.inl a)) rfl))
  blind := ldSendMem_blind E _ _ _ (V.memR Sb sl Z A₀ w0 Rd) (fun w => (w.1, w.2.2)) w0 _ fun a => match a with
    | .inl none => stdM_blind V.Mc h.1 _ _
    | .inl (some k) => stdM_blind (V.Mn k) (h.2 k) _ _
    | .inr b => hR.blind b
  hides := ldSendMem_hides E _ _ _ (V.memR Sb sl Z A₀ w0 Rd) (fun w => (w.1, w.2.2)) w0 (Sum.elim (fun _ => t) Rd.t) fun a => match a with
    | .inl none => stdM_hides V.Mc h.1 _ _
    | .inl (some k) => stdM_hides (V.Mn k) (h.2 k) _ _
    | .inr b => hR.hides b

/-- where the entries of the folded complex are among the entries of the oracle messages after the
segment -/
def StdNew.pJR (j : Sh.Cf.J) : (V.closeR Sb sl Z A₀ w0 L t tl Rd).loc.S.Ent :=
  ⟨.inr (.inl (V.N.place (.inl (.inl j))).1), (V.N.place (.inl (.inl j))).2⟩
def StdNew.pQR (q : Sh.Cf.Q) : (V.closeR Sb sl Z A₀ w0 L t tl Rd).loc.S.Ent :=
  ⟨.inr (.inl (V.N.place (.inl (.inr q))).1), (V.N.place (.inl (.inr q))).2⟩

/-- For `G.P` nonempty, if the folded complex has its laws (`hC`): what is claimed after the
locations is a family of rows on entries of the new messages.
(`LdLocD.Lin`: the premise of `ldLoc_after_rows`, Cb/Req1/LdSegAfterRows.lean) -/
theorem stdNewR_lin (hC : Sh.Cf.Laws) :
    (V.closeR Sb sl Z A₀ w0 L t tl Rd).loc.Lin (V.pJR Sb sl Z A₀ w0 L t tl Rd)
      (V.pQR Sb sl Z A₀ w0 L t tl Rd) (Hd.foldD Sb sl Z A₀).slf id where
  cutJ := fun _ _ => rfl
  cutQ := fun _ _ => rfl
  form := fun _ _ => Iff.rfl
  laws := hC

/-- For `G.P` nonempty: these rows read the new messages alone: neither what crossed the closing nor
a rider. -/
theorem stdNewR_rows_new
    (x : ((V.closeR Sb sl Z A₀ w0 L t tl Rd).loc.Xc ×
        (V.closeR Sb sl Z A₀ w0 L t tl Rd).loc.hd.Smp) ×
      (V.closeR Sb sl Z A₀ w0 L t tl Rd).loc.Lc)
    (b : (V.closeR Sb sl Z A₀ w0 L t tl Rd).loc.RowN)
    (n : (V.closeR Sb sl Z A₀ w0 L t tl Rd).loc.S.Ent) (hn : ∀ a, n.1 ≠ .inr (.inl a)) :
    ((V.closeR Sb sl Z A₀ w0 L t tl Rd).loc.rowsOf (V.pJR Sb sl Z A₀ w0 L t tl Rd)
          (V.pQR Sb sl Z A₀ w0 L t tl Rd) (Hd.foldD Sb sl Z A₀).slf id x).2
        b n = 0 := by
  have hJ : ∀ i, V.pJR Sb sl Z A₀ w0 L t tl Rd i ≠ n := fun i h => hn _ (congrArg Sigma.fst h).symm
  have hQ : ∀ i, V.pQR Sb sl Z A₀ w0 L t tl Rd i ≠ n := fun i h => hn _ (congrArg Sigma.fst h).symm
  rcases b with _ | ks | iα
  · exact pushTo_off _ _ _ hJ
  · exact pushTo_off _ _ _ fun i => hJ _
  · show pushTo _ _ _ + pushTo _ _ _ = 0
    rw [pushTo_off _ _ _ hJ, pushTo_off _ _ _ hQ, add_zero]

end

/-! ## A whole segment from a bundle, with riders -/

section
variable {E B Kc : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {mem kp : S.O → Prop}
  [DecidablePred kp] {clP : {o // kp o} → Prop} {Pn : Type} [Fintype Pn] {d e t : ℕ}
  {Lst mC mS mW : ℕ → ℕ} {L L₂ t₂ : ℕ} (pk : GPack S mem kp clP Pn d e t Lst mC mS mW L L₂ t₂)
  (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) S.Ent) (Z : Evader E B) (Zb : Evader E (pk.G.Row Unit))
  {St₀ Wp : Type} {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp)) {a : LdStage E Kc}
  (body : LdProg a (pk.cl1 Sb sl Z Zb A₀).bat.src)
  (hT : body.All fun t => t = .send ∨ t = .sub ∨ t = .step) (dw : S.Wit × Wp)
  (w0 : (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).tgt.S.Wit ×
    (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).tgt.Wp)
  (tl : ℕ)
  (Rd : RideD E
    ((pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).tgt.S.Wit ×
      (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).tgt.Wp))

/-- the second half of the closing, with riders -/
@[reducible] def GPack.closeR :
    LdCloseD (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀) :=
  pk.V.closeR (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀ w0 L₂ t₂ tl Rd

/-- The segment, with riders: any body; many rows into one; the step; bridge-to-fold; the one
sending of the new messages and the riders; the locations. -/
def GPack.seg1R : LdSeg a (pk.closeR Sb sl Z Zb A₀ w0 tl Rd).loc.tgt :=
  segOne (pk.cl1 Sb sl Z Zb A₀) body hT
    (pk.link (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀ dw)
    (pk.closeR Sb sl Z Zb A₀ w0 tl Rd)

theorem gPack_seg1R (hb : body.Hyp) (hZ : Z.OK) (hZb : Zb.OK)
    (hs : ∀ b st (n : S.Ent), ¬ mem n.1 → sl b st n = 0) (hR : Rd.OK) :
    (pk.seg1R Sb sl Z Zb A₀ body hT dw w0 tl Rd).Hyp :=
  ldSegWhole_one E Kc a (pk.cl1 Sb sl Z Zb A₀) body hT _ _ hb hZ
    (fun b st n hn => hs b st n fun h => hn ((pk.memI n.1).2 h)) (gPack_fold pk _ _ Zb A₀ dw hZb)
    (stdNewR_snd pk.V _ _ Zb A₀ w0 L₂ t₂ tl Rd pk.new hR)

theorem gPack_seg1R_zk (base : MaskFact a.J.W → Prop) (hb : body.Zk base) :
    (pk.seg1R Sb sl Z Zb A₀ body hT dw w0 tl Rd).Zk base :=
  ldSegWholeZk_one E Kc a (pk.cl1 Sb sl Z Zb A₀) body hT _ _ base hb

variable {E0 : ExtSpec} {Rc Pw : Type} (i : IxAt E0 E₀) (rc : St₀ → Rc) (px : Wp → Pw)
  (q₂ : Finset
      (E₀.prod (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).S₂.ext).Pos → Prop)

open Classical in
/-- The format: after the locations: q₂; at most t₂ long positions of each new message; at most
Rd.t b of the rider b. (`Sig.qSum`, Cb/Ld/LdSendPiece.lean)
(not all hypotheses are named here: see the statement below) -/
theorem gPack_seg1R_fmt (φ : JFmt Kc E0 Rc Pw a.J)
    (hb : body.Fmt φ
      ((pk.cl1 Sb sl Z Zb A₀).bat.src.fmt i (fun st => rc st.2) px (pk.qIn Sb sl Z Zb A₀ q₂)))
    (hZb : Zb.OK) (ht : tl ≤ t) (hR : Rd.OK) :
    (pk.seg1R Sb sl Z Zb A₀ body hT dw w0 tl Rd).Fmt φ
      ((pk.closeR Sb sl Z Zb A₀ w0 tl Rd).loc.tgt.fmt i (fun st => rc st.2) px
        ((pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).S₂.qSum
          (pk.V.N.N₀.sum Rd.N) q₂ (Sum.elim (fun _ => t₂) Rd.t))) := by
  refine ⟨_,
    (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).src.fmt
      i (fun st => rc st.2) px (pk.qIn Sb sl Z Zb A₀ q₂),
    (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).tgt.fmt (i.inr _)
      (fun st => rc st.2) (fun w => px w.2)
      ((pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).qOpen q₂ tl),
    (pk.closeR Sb sl Z Zb A₀ w0 tl Rd).snd.tgt.fmt (i.inr _) (fun st => rc st.2) px
      ((pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).S₂.qSum
        (pk.V.N.N₀.sum Rd.N)
        ((pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).qOpen q₂ tl)
        (Sum.elim (fun _ => t₂) Rd.t)),
    hb, ?_, ?_, ?_, ?_⟩
  · refine (LdProg.fmt_snoc _ _ _ _).2
      ⟨(pk.cl1 Sb sl Z Zb A₀).bat.tgt.fmt i (fun st => rc st.2) px (pk.qIn Sb sl Z Zb A₀ q₂),
        (LdProg.fmt_snoc _ _ _ _).2 ⟨_, (LdProg.fmt_nil _ _ _).2 rfl, (Chain.fmt_one _ _ _).2 ?_⟩,
        ?_⟩
    · exact ldFmt_bat E Kc E0 Rc Pw (pk.cl1 Sb sl Z Zb A₀).bat i rc px _
    · exact ldStepF_fmt S _ _ _ i _ _ px _ fun _ => rfl
  · refine (LdProg.fmt_snoc _ _ _ _).2 ⟨_, (LdProg.fmt_nil _ _ _).2 rfl, (Chain.fmt_one _ _ _).2 ?_⟩
    exact ldFmt_fold E Kc E0 Rc Pw
      (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀) _ i rc px _ _ _
      (ldGroup_link_fmt _ _ Zb A₀ i rc px q₂ pk.hc dw d t Lst mC mS mW L pk.ok
        pk.hyp hZb pk.list pk.fits)
      (fun U W hW hU =>
        (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).open_need
          q₂ tl t ht U W hW hU)
  · exact ldFmt_send E Kc E0 Rc Pw
      (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).tgt
      (pk.closeR Sb sl Z Zb A₀ w0 tl Rd).snd (i.inr _) (fun st => rc st.2) (fun w => px w.2) px _
      (stdNewR_snd pk.V _ _ Zb A₀ w0 L₂ t₂ tl Rd pk.new hR) fun _ => rfl
  · refine (LdProg.fmt_snoc _ _ _ _).2 ⟨_, (LdProg.fmt_nil _ _ _).2 rfl, (Chain.fmt_one _ _ _).2 ?_⟩
    exact ldFmt_loc E Kc E0 Rc Pw (pk.closeR Sb sl Z Zb A₀ w0 tl Rd).loc i rc px _ _
      (fun ρ U hU => LdCloseD.loc_need _ q₂ (pk.closeR Sb sl Z Zb A₀ w0 tl Rd) ρ U hU)

end
end Cb
