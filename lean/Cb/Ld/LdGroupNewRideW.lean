-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupNewRideW.lean: this file is for toys (a toy: a small example instance). The prover
message that carries the new codewords of a code switch also carries further oracle codewords
("riders"), which encode a part of the prover's further witness (`LdStage.Wp`). From then on the
relation reads that part off their messages (bkR) and no longer off the further witness.

Definitions, statements as theorems, proofs: mainly those of Cb/Ld/LdGroupNewRide.lean with three
more parameters (Wp', rst, bkR). Generic.
Further witness (lean/GLOSSARY.md): the part of a stage's witness beside the messages of the open
oracle messages (`LdStage`, Cb/Req1/LdSegKit.lean).

Why: behind a sending the exact relation knows of the new oracle messages only what the old witness,
read back off them, says. (`Sig.grow`, Cb/Ld/LdSigSum.lean.) The first oracle messages of the next
segment hold data of which the next segment's first claim speaks. So these data are in the further
witness up to the closing, with their claim carried, and the closing's one sending moves them into
the riders.

Main names:
  `V.closeRW .. Rd Wp' rst bkR`: as `V.closeR` (Cb/Ld/LdGroupNewRide.lean: the same members'
    senders), but: the further witness after the sending is Wp'.
  `stdNewW_snd`: the seven hypotheses of the sending (`LdSendD.Hyp`, Cb/Req1/LdSegKit.lean), from
    `V.OK L t`, `Rd.OK` (`RideD.OK`, Cb/Ld/LdGroupNewRide.lean) and one law: bkR (the riders'
    messages as sent) (rst of the further witness) gives the further witness back.
  `pk.closeRW`, `pk.seg1W`, `gPack_seg1W` (hypotheses), `gPack_seg1W_zk`, `gPack_seg1W_fmt` (px' on
    Wp' with px' (rst wp) = px wp): the whole segment from a bundle; each under the hypotheses of
    its statement.
In the statements on `V.closeRW` the group's set of common long positions, `G.P`, is nonempty; a
bundle has that as a field.

Over `StdNew` the second half of a closing with riders has four forms: `V.closeR`
(Cb/Ld/LdGroupNewRide.lean); `V.closeRW` (this file); `V.closeS` (Cb/Ld/LdGroupNewStdS.lean: the one
sending is the standard sending by definition; another term of a stage after it); `V.closeRT`
(Cb/Ld/LdGroupNewStdT.lean: this file's closing at standard riders but for the sender, which is the
standard one; its sending is the standard sending: proved under the hypothesis of `stdNewT_eq`; the
same stage after it).

Limits: what the head of Cb/Ld/LdGroupNewRide.lean lists as not said is not said here either: this
file does not say that masks in a rider are fresh after the segment (at this closing:
`stdNewW_fresh`, `stdNewW_cutQuiet`, Cb/Ld/LdGroupNewRideWFresh.lean, each under its hypotheses),
and it has no instance of its own.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupNewCut
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood

section
variable {E B Kc : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  {Sh : GShape G} {kp : S.O → Prop} [DecidablePred kp] {Hd : GHeld Sh kp} {Pn : Type} [Fintype Pn]
  (V : StdNew Hd Pn) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))
  {St₀ Wp : Type} {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (w0 : (Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp) (L t tl : ℕ)
  (Rd : RideD E ((Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp)) (Wp' : Type)
  (rst : Wp → Wp') (bkR : Rd.N.Msg → Wp' → Wp)

/-- The second half of the closing, with riders that give a part of the further witness back: one
sending of the new messages and of the riders, independent coins and seeds; the open word's witness
is cut out of the new messages alone; of the further witness rst is handed on, and bkR reads the
whole back off the riders and what was handed on; tl locations. -/
@[reducible] def StdNew.closeRW : LdCloseD (Hd.foldD Sb sl Z A₀) where
  N := V.N.N₀.sum Rd.N
  Sd := Sig.Seeds.indep _
  Wp' := Wp'
  cutN := fun m => V.N.cut fun a => m (.inl a)
  bk₀ := fun m w' => bkR (fun b => m (.inr b)) w'
  Sn := Sig.Sender.ofMem (V.memR Sb sl Z A₀ w0 Rd) (fun w => (w.1, rst w.2.2)) w0
  L := Sum.elim (fun _ => L) Rd.L
  tN := Sum.elim (fun _ => t) Rd.t
  t := tl
  neP := inferInstanceAs (Nonempty G.P)

/-- For `G.P` nonempty: the closing with riders of Cb/Ld/LdGroupNewRide.lean is the case in which
all of the further witness is handed on, by definition. -/
theorem stdNewW_old :
    V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp id (fun _ w => w) = V.closeR Sb sl Z A₀ w0 L t tl Rd := rfl

/-- What the sending asks: for `G.P` nonempty, `V.OK L t` (`h`), `Rd.OK` (`hR`) and the law `hbk`
give its seven hypotheses. -/
theorem stdNewW_snd (h : V.OK L t) (hR : Rd.OK)
    (hbk : ∀ w (k : ∀ b, (Rd.m b).Mk),
      bkR (fun b => (Rd.m b).upM ((Rd.m b).put w (k b))) (rst w.2.2) = w.2.2) :
    (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).snd.Hyp where
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
  sender := ldSendMem_laws E _ _ _ (V.memR Sb sl Z A₀ w0 Rd) (fun w => (w.1, rst w.2.2)) w0 _
    (fun a m r => match a with
      | .inl none => stdM_enc V.Mc _ _ m r
      | .inl (some k) => stdM_enc (V.Mn k) _ _ m r
      | .inr b => hR.enc b m r)
    (fun w k =>
      Prod.ext rfl (Prod.ext (V.cut_put w0 w fun a => k (.inl a)) (hbk w fun b => k (.inr b))))
  blind := ldSendMem_blind E _ _ _ (V.memR Sb sl Z A₀ w0 Rd) (fun w => (w.1, rst w.2.2)) w0 _ fun a => match a with
    | .inl none => stdM_blind V.Mc h.1 _ _
    | .inl (some k) => stdM_blind (V.Mn k) (h.2 k) _ _
    | .inr b => hR.blind b
  hides := ldSendMem_hides E _ _ _ (V.memR Sb sl Z A₀ w0 Rd) (fun w => (w.1, rst w.2.2)) w0 (Sum.elim (fun _ => t) Rd.t) fun a => match a with
    | .inl none => stdM_hides V.Mc h.1 _ _
    | .inl (some k) => stdM_hides (V.Mn k) (h.2 k) _ _
    | .inr b => hR.hides b

/-- where the entries of the folded complex are among the entries of the oracle messages after the
segment -/
def StdNew.pJW (j : Sh.Cf.J) :
    (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.S.Ent :=
  ⟨.inr (.inl (V.N.place (.inl (.inl j))).1), (V.N.place (.inl (.inl j))).2⟩
def StdNew.pQW (q : Sh.Cf.Q) :
    (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.S.Ent :=
  ⟨.inr (.inl (V.N.place (.inl (.inr q))).1), (V.N.place (.inl (.inr q))).2⟩

/-- For `G.P` nonempty, if the folded complex has its laws (`hC`): what is claimed after the
locations is a family of rows on entries of the new messages.
(`LdLocD.Lin`, Cb/Req1/LdSegAfterRows.lean; the equivalence: `stdNewW_after_all`,
Cb/Ld/LdGroupNewRowsW.lean) -/
theorem stdNewW_lin (hC : Sh.Cf.Laws) :
    (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.Lin
      (V.pJW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR) (V.pQW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR)
      (Hd.foldD Sb sl Z A₀).slf id where
  cutJ := fun _ _ => rfl
  cutQ := fun _ _ => rfl
  form := fun _ _ => Iff.rfl
  laws := hC

/-- For `G.P` nonempty: these rows read the new messages alone: neither what crossed the closing nor
a rider. -/
theorem stdNewW_rows_new
    (x : ((V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.Xc ×
        (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.hd.Smp) ×
      (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.Lc)
    (b : (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.RowN)
    (n : (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.S.Ent)
    (hn : ∀ a, n.1 ≠ .inr (.inl a)) :
    ((V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.rowsOf
          (V.pJW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR) (V.pQW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR)
          (Hd.foldD Sb sl Z A₀).slf id x).2
        b n = 0 := by
  have hJ : ∀ i, V.pJW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR i ≠ n := fun i h =>
    hn _ (congrArg Sigma.fst h).symm
  have hQ : ∀ i, V.pQW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR i ≠ n := fun i h =>
    hn _ (congrArg Sigma.fst h).symm
  rcases b with _ | ks | iα
  · exact pushTo_off _ _ _ hJ
  · exact pushTo_off _ _ _ fun i => hJ _
  · show pushTo _ _ _ + pushTo _ _ _ = 0
    rw [pushTo_off _ _ _ hJ, pushTo_off _ _ _ hQ, add_zero]

/-- For `G.P` nonempty: messages that agree at all entries of the new messages that are no pads have
the same cut: no entry of a rider is read. -/
theorem stdNewW_cut_congr (m m' : (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).N.Msg)
    (h : ∀ n : V.N.N₀.Ent, ¬ V.IsPad n → m' (.inl n.1) n.2 = m (.inl n.1) n.2) :
    (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).cutN m' =
      (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).cutN m :=
  stdNew_cut_congr V (fun a => m (.inl a)) (fun a => m' (.inl a)) h

/-- an entry of a rider, after the locations -/
def StdNew.rideAtW (n : Rd.N.Ent) : (V.closeRW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR).loc.S.Ent :=
  ⟨.inr (.inr n.1), n.2⟩

theorem stdNewW_rideAt_inj :
    Function.Injective (V.rideAtW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR) := by
  rintro ⟨a, j⟩ ⟨a', j'⟩ h
  obtain ⟨h1, h2⟩ := Sigma.mk.inj h
  obtain rfl : a = a' := Sum.inr.inj (Sum.inr.inj h1)
  exact congrArg (Sigma.mk a) (eq_of_heq h2)

theorem stdNewW_rideAt_new (n : Rd.N.Ent) (a : V.N.N₀.O) :
    (V.rideAtW Sb sl Z A₀ w0 L t tl Rd Wp' rst bkR n).1 ≠ .inr (.inl a) :=
  fun h => by cases Sum.inr.inj h

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
  (Wp' : Type) (rst : Wp → Wp') (bkR : Rd.N.Msg → Wp' → Wp)

/-- the second half of the closing, with riders -/
@[reducible] def GPack.closeRW :
    LdCloseD (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀) :=
  pk.V.closeRW (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀ w0 L₂ t₂ tl Rd Wp' rst bkR

/-- The segment, with riders: any body; many rows into one; the step; bridge-to-fold; the one
sending of the new messages and the riders; the locations. -/
def GPack.seg1W : LdSeg a (pk.closeRW Sb sl Z Zb A₀ w0 tl Rd Wp' rst bkR).loc.tgt :=
  segOne (pk.cl1 Sb sl Z Zb A₀) body hT
    (pk.link (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀ dw)
    (pk.closeRW Sb sl Z Zb A₀ w0 tl Rd Wp' rst bkR)

theorem gPack_seg1W (hb : body.Hyp) (hZ : Z.OK) (hZb : Zb.OK)
    (hs : ∀ b st (n : S.Ent), ¬ mem n.1 → sl b st n = 0) (hR : Rd.OK)
    (hbk : ∀ w (k : ∀ b, (Rd.m b).Mk),
      bkR (fun b => (Rd.m b).upM ((Rd.m b).put w (k b))) (rst w.2.2) = w.2.2) :
    (pk.seg1W Sb sl Z Zb A₀ body hT dw w0 tl Rd Wp' rst bkR).Hyp :=
  ldSegWhole_one E Kc a (pk.cl1 Sb sl Z Zb A₀) body hT _ _ hb hZ
    (fun b st n hn => hs b st n fun h => hn ((pk.memI n.1).2 h)) (gPack_fold pk _ _ Zb A₀ dw hZb)
    (stdNewW_snd pk.V _ _ Zb A₀ w0 L₂ t₂ tl Rd Wp' rst bkR pk.new hR hbk)

theorem gPack_seg1W_zk (base : MaskFact a.J.W → Prop) (hb : body.Zk base) :
    (pk.seg1W Sb sl Z Zb A₀ body hT dw w0 tl Rd Wp' rst bkR).Zk base :=
  ldSegWholeZk_one E Kc a (pk.cl1 Sb sl Z Zb A₀) body hT _ _ base hb

variable {E0 : ExtSpec} {Rc Pw : Type} (i : IxAt E0 E₀) (rc : St₀ → Rc)
  (px : Wp → Pw) (px' : Wp' → Pw)
  (q₂ : Finset
      (E₀.prod (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).S₂.ext).Pos → Prop)

open Classical in
/-- The format: after the locations: q₂; at most t₂ long positions of each new message; at most
Rd.t b of the rider b. (`Sig.qSum`, Cb/Ld/LdSendPiece.lean)
(not all hypotheses are named here: see the statement below) -/
theorem gPack_seg1W_fmt (φ : JFmt Kc E0 Rc Pw a.J)
    (hb : body.Fmt φ
      ((pk.cl1 Sb sl Z Zb A₀).bat.src.fmt i (fun st => rc st.2) px (pk.qIn Sb sl Z Zb A₀ q₂)))
    (hZb : Zb.OK) (ht : tl ≤ t) (hR : Rd.OK)
    (hbk : ∀ w (k : ∀ b, (Rd.m b).Mk),
      bkR (fun b => (Rd.m b).upM ((Rd.m b).put w (k b))) (rst w.2.2) = w.2.2)
    (hpx : ∀ wp, px' (rst wp) = px wp) :
    (pk.seg1W Sb sl Z Zb A₀ body hT dw w0 tl Rd Wp' rst bkR).Fmt φ
      ((pk.closeRW Sb sl Z Zb A₀ w0 tl Rd Wp' rst bkR).loc.tgt.fmt i (fun st => rc st.2) px'
        ((pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).S₂.qSum
          (pk.V.N.N₀.sum Rd.N) q₂ (Sum.elim (fun _ => t₂) Rd.t))) := by
  refine ⟨_,
    (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).src.fmt
      i (fun st => rc st.2) px (pk.qIn Sb sl Z Zb A₀ q₂),
    (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).tgt.fmt (i.inr _)
      (fun st => rc st.2) (fun w => px w.2)
      ((pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).qOpen q₂ tl),
    (pk.closeRW Sb sl Z Zb A₀ w0 tl Rd Wp' rst bkR).snd.tgt.fmt (i.inr _) (fun st => rc st.2) px'
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
      (pk.closeRW Sb sl Z Zb A₀ w0 tl Rd Wp' rst bkR).snd (i.inr _) (fun st => rc st.2)
      (fun w => px w.2) px' _
      (stdNewW_snd pk.V _ _ Zb A₀ w0 L₂ t₂ tl Rd Wp' rst bkR pk.new hR hbk) fun w => hpx w.2.2
  · refine (LdProg.fmt_snoc _ _ _ _).2 ⟨_, (LdProg.fmt_nil _ _ _).2 rfl, (Chain.fmt_one _ _ _).2 ?_⟩
    exact ldFmt_loc E Kc E0 Rc Pw (pk.closeRW Sb sl Z Zb A₀ w0 tl Rd Wp' rst bkR).loc i rc px' _ _
      (fun ρ U hU => LdCloseD.loc_need _ q₂ (pk.closeRW Sb sl Z Zb A₀ w0 tl Rd Wp' rst bkR) ρ U hU)

end
end Cb
