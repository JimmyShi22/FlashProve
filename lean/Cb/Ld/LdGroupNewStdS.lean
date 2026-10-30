-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupNewStdS.lean: for toys: this file builds the second half of a closing whose one sending
is, by definition, the standard sending of a request.

In the words of lean/GLOSSARY.md: toy: a small example instance. rider: a further oracle message
that a closing's one sending sends with the closing's own new messages (`RideD`,
Cb/Ld/LdGroupNewRide.lean). locations: the one-round step in
which the prover sends nothing and the verifier draws long positions of an open word and reads it
there.

In standard terms: in the code switch that follows the fold of several oracle codewords the prover
sends new codewords whose messages contain the message and the encoding randomness of the old,
folded word.

Definitions, statements as theorems, proofs. No parameter of a protocol. The closing of the title is
the analogue of `V.closeRW` (Cb/Ld/LdGroupNewRideW.lean) and, with riders, of `V.close`
(Cb/Ld/LdGroupNewStd.lean); it has another sender, and its cut (`LdCloseD.cutN`,
Cb/Req1/LdSegFit.lean) and its read-back (`bk₀`) read the data.

Why: Cb/Req1/LdReqProtoStd.lean asks of every sending of the reference request but those of the list
`more` the equation d = `LdSendD.std ..` (Cb/Obj/LdObjectSenders.lean: one sending of a request,
with the standard sender of a layout: data read off the witness, free entries and pads coins; what
is read back is read off the data of the messages). The senders of the new messages in `V.close` and
`V.closeRW` have coins of another type (one element of the field, not a pair of families), and their
cut reads messages: the equation does not hold there by definition, and we see no way to show it.
(`V.closeRT`, Cb/Ld/LdGroupNewStdT.lean, is `V.closeRW` at standard riders but for the sender:
`stdNewT_loc`, and, under hD, `stdNewT_eq`.)

Main names:
  `V.layN : V.N.N₀.StdL E`, `stdNew_layN_ok`: the layout of the new messages: data; no free entry;
    one pad each; plain format; in order if `V.OK L t`.
  `V.datV`: the data of the new messages; `V.ofData`: new messages with given data, all pads 0;
    `V.cutD`: the cut, read off the data. `stdNew_cutD_dat`: the data of the new messages hold the
    witness of the open test. `stdNew_ofData_at` (off the pads: `hn`), `stdNew_cutD_of`: the cut
    read off the data of messages is their cut (Cb/Ld/LdGroupNewCut.lean: the cut reads no pad).
  `V.layS N₁ Y₁` := `V.layN.sum Y₁` (Cb/Ld/LdSendStdSum.lean), `V.datS`, `V.bkS`: the one prover
    message: the new messages and standard riders (N₁, Y₁, dat₁); what is read back: the witness of
    the open test off the new messages' data; the further witness by bkD off the riders' data and
    what was handed on.
  `V.closeS .. N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD : LdCloseD ..`: the closing of the title.
  `stdNewS_eq`: `(V.closeS ..).snd` = `LdSendD.std ..`, by definition. `stdNewS_isStd`: `IsStd E`,
    from `V.OK L t`, `Y₁.OK t₁`, the riders' codes' laws, lists, evading samples, and the law bkD
    (dat₁ w) (rst w.2.2) = w.2.2.
  `stdNewS_after_all`: from the laws of the folded complex (hC): what is claimed after the locations
    holds if and only if all rows of `rowsOf` hold of the entries. `stdNewS_after_new`: see its doc
    comment.
  `pk.closeS`, `pk.seg1S`, `gPack_seg1S`, `gPack_seg1S_zk`, `gPack_seg1S_fmt`: the whole segment
    from a bundle; see their statements. `gPack_seg1S`: the hypotheses of `pk.seg1S` (`LdSeg.Hyp`),
    from `hT` (every move of the body is a sending, a sub-protocol or a step without rounds), the
    body's hypotheses (`hb : body.Hyp`), both evaders evade (`hZ`, `hZb`), sl vanishes at the
    entries of oracle messages that are no members (`hs`), and `h₁`, `hl`, `hs₁`, `he`, `hbk` as in
    the row of `stdNewS_isStd`. `gPack_seg1S_zk`: see its statement, and the second limit below.
    `gPack_seg1S_fmt`: its format (hypotheses: see its doc comment and statement).
In the statements on `V.closeS` the group's set of common long positions, `G.P`, is nonempty; a
bundle has that as a field.

Limits: this file says nothing on masks (Cb/Req1/LdReqStdLay*.lean under `IsStd`).
It does not say that the segment is zero knowledge: `gPack_seg1S_zk` gives the condition `Zk base`
of the segment from that of its body (under `hT`), and `Spec.ldReq_seg_ok` (Cb/Req1/LdReq.lean)
takes it as a premise.
This file gives no instance that meets its hypotheses, so as far as this file shows its theorems may
hold of nothing.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupNewRowsW
import Cb.Obj.LdObjectSendersStdM
import Cb.Ld.LdSendStdSum
import Cb.Req1.LdReqProtoStd
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks IOR Cb.Ood

section
variable {E : Type} [Field E] [Fintype E] {S : Sig E} {G : Grp S} {Sh : GShape G} {kp : S.O → Prop}
  [DecidablePred kp] {Hd : GHeld Sh kp} {Pn : Type} [Fintype Pn] (V : StdNew Hd Pn)

/-- The layout of the new messages: data; no free entry; one pad each; plain format. -/
@[reducible] def StdNew.layN : V.N.N₀.StdL E where
  Dt := fun a => match a with
    | none => V.Mc.Dt
    | some k => (V.Mn k).Dt
  finDt := fun a => match a with
    | none => V.Mc.finDt
    | some k => (V.Mn k).finDt
  Fr := fun _ => Empty
  Pd := fun _ => Unit
  ν := fun a => match a with
    | none => stdMNu (fun _ : Unit => V.Mc) ()
    | some k => stdMNu (fun _ : Unit => V.Mn k) ()
  En := fun a => match a with
    | none => V.Mc.Cm.Nn
    | some k => (V.Mn k).Cm.Nn
  upM := fun a => match a with
    | none => fun m => m
    | some _ => fun m => m
  upR := fun a => match a with
    | none => fun r => r
    | some _ => fun r => r
  msgOf := fun a => match a with
    | none => fun x η j => withPad (F := E) x η (stdMNu (fun _ : Unit => V.Mc) () j)
    | some k => fun x η j => withPad (F := E) x η (stdMNu (fun _ : Unit => V.Mn k) () j)

theorem stdNew_layN_ok {L t : ℕ} (h : V.OK L t) : V.layN.OK fun _ => t := by
  have hc := (stdMFam_ok E Pn Unit (fun _ => V.Mc) (fun _ => L) (fun _ => t) fun _ => h.1).1
  have hn := fun k =>
    (stdMFam_ok E Pn Unit (fun _ => V.Mn k) (fun _ => L) (fun _ => t) fun _ => h.2 k).1
  refine ⟨fun a => ?_, fun a => ?_, fun a => ?_, fun a => ?_⟩
  · rcases a with _ | k
    · exact hc.enc ()
    · exact (hn k).enc ()
  · rcases a with _ | k
    · exact hc.lay ()
    · exact (hn k).lay ()
  · rcases a with _ | k
    · exact hc.priv ()
    · exact (hn k).priv ()
  · rcases a with _ | k
    · exact hc.hides ()
    · exact (hn k).hides ()

variable {Wl Wr : Type}

/-- the data of the new messages -/
def StdNew.datV (w : Wl × (((Sh.Cf.J → E) × (Sh.Cf.Q → E)) × Wr)) : ∀ a, V.layN.Dt a → E
  | none => V.datC w
  | some k => V.datN k w

/-- new messages with given data, all pads 0 -/
def StdNew.ofData (d : ∀ a, V.layN.Dt a → E) : V.N.N₀.Msg
  | none => fun j => Sum.elim (d none) (fun _ => 0) (V.Mc.place.symm j)
  | some k => fun j => Sum.elim (d (some k)) (fun _ => 0) ((V.Mn k).place.symm j)

/-- the cut, read off the data -/
def StdNew.cutD (d : ∀ a, V.layN.Dt a → E) : (Sh.Cf.J → E) × (Sh.Cf.Q → E) :=
  V.N.cut (V.ofData d)

/-- The data of the new messages hold the witness of the open test. -/
theorem stdNew_cutD_dat (w0 w : Wl × (((Sh.Cf.J → E) × (Sh.Cf.Q → E)) × Wr)) :
    V.cutD (V.datV w) = w.2.1 := by
  have e : V.ofData (V.datV w) = fun a => (V.mem w0 a).upM ((V.mem w0 a).put w (match a with
      | none => (0 : E)
      | some _ => (0 : E))) := by
    funext a
    rcases a with _ | k <;> rfl
  show V.N.cut (V.ofData (V.datV w)) = _
  rw [e]
  exact V.cut_put w0 w _

omit [Fintype E] in
theorem offPad_aux {J Dt : Type} (pl : Dt ⊕ Unit ≃ J) (m : J → E) (j : J) (hj : j ≠ pl (.inr ())) :
    Sum.elim (fun i => m (pl (.inl i))) (fun _ => 0) (pl.symm j) = m j := by
  obtain ⟨x, rfl⟩ := pl.surjective j
  rw [Equiv.symm_apply_apply]
  rcases x with i | u
  · rfl
  · exact absurd rfl hj

/-- messages and "their data, pads 0" agree off the pads -/
theorem stdNew_ofData_at (m : V.N.N₀.Msg) (n : V.N.N₀.Ent) (hn : ¬ V.IsPad n) :
    V.ofData (V.layN.dataOf m) n.1 n.2 = m n.1 n.2 := by
  obtain ⟨_ | k, j⟩ := n
  · exact offPad_aux V.Mc.place (m none) j hn
  · exact offPad_aux (V.Mn k).place (m (some k)) j hn

/-- so the cut, read off the data of messages, is their cut -/
theorem stdNew_cutD_of (m : V.N.N₀.Msg) : V.cutD (V.layN.dataOf m) = V.N.cut m :=
  stdNew_cut_congr V m _ fun n hn => stdNew_ofData_at V m n hn

end

section
variable {E B Kc : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  {Sh : GShape G} {kp : S.O → Prop} [DecidablePred kp] {Hd : GHeld Sh kp} {Pn : Type} [Fintype Pn]
  (V : StdNew Hd Pn) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))
  {St₀ Wp : Type} {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (w0 : (Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp) (L t tl : ℕ) (N₁ : Sig E)
  (Y₁ : N₁.StdL E)
  (dat₁ : (Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp → ∀ b, Y₁.Dt b → E)
  (L₁ t₁ : N₁.O → ℕ) (Wp' : Type) (rst : Wp → Wp') (bkD : (∀ b, Y₁.Dt b → E) → Wp' → Wp)

/-- the layout of the one prover message: the new messages, the riders -/
@[reducible] def StdNew.layS : (V.N.N₀.sum N₁).StdL E := V.layN.sum Y₁

/-- its data -/
def StdNew.datS :
    (Hd.foldD Sb sl Z A₀).tgt.S.Wit × (Hd.foldD Sb sl Z A₀).tgt.Wp → ∀ a, (V.layS N₁ Y₁).Dt a → E :=
  sumDat V.layN Y₁ V.datV dat₁

/-- what is read back off the data: the witness of the open test off the new messages'; the further
witness off the riders' and what was handed on -/
def StdNew.bkS (d : ∀ a, (V.layS N₁ Y₁).Dt a → E) (w' : Wp') :
    (Hd.foldD Sb sl Z A₀).tgt.Wp :=
  (V.cutD fun a => d (.inl a), bkD (fun b => d (.inr b)) w')

/-- The second half of the closing, the one sending the standard sending. -/
@[reducible] def StdNew.closeS : LdCloseD (Hd.foldD Sb sl Z A₀) where
  N := V.N.N₀.sum N₁
  Sd := Sig.Seeds.indep _
  Wp' := Wp'
  cutN := fun m => V.cutD fun a => (V.layS N₁ Y₁).dataOf m (.inl a)
  bk₀ := fun m w' => bkD (fun b => (V.layS N₁ Y₁).dataOf m (.inr b)) w'
  Sn := (V.layS N₁ Y₁).snd (V.datS Sb sl Z A₀ N₁ Y₁ dat₁) (fun w => (w.1, rst w.2.2)) w0
  L := Sum.elim (fun _ => L) L₁
  tN := Sum.elim (fun _ => t) t₁
  t := tl
  neP := inferInstanceAs (Nonempty G.P)

/-- Its sending is the standard one, by definition. -/
theorem stdNewS_eq :
    (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).snd =
      LdSendD.std (Hd.foldD Sb sl Z A₀).tgt (V.N.N₀.sum N₁) (Sig.Seeds.indep _) Wp'
        (Sum.elim (fun _ => L) L₁) (Sum.elim (fun _ => t) t₁) (V.layS N₁ Y₁)
        (V.datS Sb sl Z A₀ N₁ Y₁ dat₁) (fun x => rst x.2) (V.bkS Sb sl Z A₀ N₁ Y₁ Wp' bkD) w0 := rfl

theorem stdNewS_isStd (h : V.OK L t) (h₁ : Y₁.OK t₁) (hl : ∀ b, (N₁.om b).C.Laws)
    (hs : ∀ b, (N₁.om b).ListLE (L₁ b)) (he : ∀ b, (N₁.om b).Evades)
    (hbk : ∀ w, bkD (dat₁ w) (rst w.2.2) = w.2.2) :
    (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).snd.IsStd E :=
  ⟨V.layS N₁ Y₁, V.datS Sb sl Z A₀ N₁ Y₁ dat₁, fun x => rst x.2, V.bkS Sb sl Z A₀ N₁ Y₁ Wp' bkD, w0,
    rfl, (stdL_sum E E _ _ V.layN Y₁ _ t₁ (stdNew_layN_ok V h) h₁).1,
    fun w => Prod.ext (stdNew_cutD_dat V w0 w) (hbk w),
    fun i => match i with
      | .inl none => h.1.laws
      | .inl (some k) => (h.2 k).laws
      | .inr b => hl b,
    (ldSendFam_fair_indep E _).1,
    fun i => match i with
      | .inl none => stdM_list V.Mc h.1
      | .inl (some k) => stdM_list (V.Mn k) (h.2 k)
      | .inr b => hs b,
    fun i => match i with
      | .inl none => stdM_evades V.Mc h.1
      | .inl (some k) => stdM_evades (V.Mn k) (h.2 k)
      | .inr b => he b⟩

/-- its cut is the cut of the new messages -/
theorem stdNewS_cut (m : (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).N.Msg) :
    (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).cutN m =
      V.N.cut fun a => m (.inl a) :=
  stdNew_cutD_of V fun a => m (.inl a)

/-- What the sending asks. -/
theorem stdNewS_snd (h : V.OK L t) (h₁ : Y₁.OK t₁) (hl : ∀ b, (N₁.om b).C.Laws)
    (hs₁ : ∀ b, (N₁.om b).ListLE (L₁ b)) (he : ∀ b, (N₁.om b).Evades)
    (hbk : ∀ w, bkD (dat₁ w) (rst w.2.2) = w.2.2) :
    (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).snd.Hyp :=
  ldReqProtoStd_send E E Kc _ _
    (stdNewS_isStd V Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD h h₁ hl hs₁ he hbk)

/-- where the entries of the folded complex are among the entries of the oracle messages after the
segment -/
def StdNew.pJS (j : Sh.Cf.J) :
    (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.S.Ent :=
  ⟨.inr (.inl (V.N.place (.inl (.inl j))).1), (V.N.place (.inl (.inl j))).2⟩
def StdNew.pQS (q : Sh.Cf.Q) :
    (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.S.Ent :=
  ⟨.inr (.inl (V.N.place (.inl (.inr q))).1), (V.N.place (.inl (.inr q))).2⟩

/-- For `G.P` nonempty, if the folded complex has its laws (`hC`): what is claimed after the
locations is a family of rows on entries of the new messages. -/
theorem stdNewS_lin (hC : Sh.Cf.Laws) :
    (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.Lin
      (V.pJS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD)
      (V.pQS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD) (Hd.foldD Sb sl Z A₀).slf id where
  cutJ := fun _ j =>
    congrFun
      (congrArg Prod.fst (stdNewS_cut V Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD _)) j
  cutQ := fun _ q =>
    congrFun
      (congrArg Prod.snd (stdNewS_cut V Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD _)) q
  form := fun _ _ => Iff.rfl
  laws := hC

/-- For `G.P` nonempty: these rows read the new messages alone: neither what crossed the closing nor
a rider. -/
theorem stdNewS_rows_new
    (x : ((V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.Xc ×
        (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.hd.Smp) ×
      (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.Lc)
    (b : (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.RowN)
    (n : (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.S.Ent)
    (hn : ∀ a, n.1 ≠ .inr (.inl a)) :
    ((V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.rowsOf
          (V.pJS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD)
          (V.pQS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD)
          (Hd.foldD Sb sl Z A₀).slf id x).2
        b n = 0 := by
  have hJ : ∀ i, V.pJS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD i ≠ n := fun i h =>
    hn _ (congrArg Sigma.fst h).symm
  have hQ : ∀ i, V.pQS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD i ≠ n := fun i h =>
    hn _ (congrArg Sigma.fst h).symm
  rcases b with _ | ks | iα
  · exact pushTo_off _ _ _ hJ
  · exact pushTo_off _ _ _ fun i => hJ _
  · show pushTo _ _ _ + pushTo _ _ _ = 0
    rw [pushTo_off _ _ _ hJ, pushTo_off _ _ _ hQ, add_zero]

/-- For `G.P` nonempty: messages that agree at all entries of the new messages that are no pads have
the same cut: no entry of a rider is read. -/
theorem stdNewS_cut_congr
    (m m' : (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).N.Msg)
    (h : ∀ n : V.N.N₀.Ent, ¬ V.IsPad n → m' (.inl n.1) n.2 = m (.inl n.1) n.2) :
    (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).cutN m' =
      (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).cutN m :=
  (stdNewS_cut V Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD m').trans
    ((stdNew_cut_congr V (fun a => m (.inl a)) (fun a => m' (.inl a)) h).trans
      (stdNewS_cut V Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD m).symm)

/-- an entry of a rider, after the locations -/
def StdNew.rideAtS (n : N₁.Ent) :
    (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.S.Ent :=
  ⟨.inr (.inr n.1), n.2⟩

theorem stdNewS_rideAt_inj :
    Function.Injective (V.rideAtS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD) := by
  rintro ⟨a, j⟩ ⟨a', j'⟩ h
  obtain ⟨h1, h2⟩ := Sigma.mk.inj h
  obtain rfl : a = a' := Sum.inr.inj (Sum.inr.inj h1)
  exact congrArg (Sigma.mk a) (eq_of_heq h2)

theorem stdNewS_rideAt_new (n : N₁.Ent) (a : V.N.N₀.O) :
    (V.rideAtS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD n).1 ≠ .inr (.inl a) :=
  fun h => by cases Sum.inr.inj h

/-- an entry of a new message, after the locations -/
def StdNew.newAtS (n : V.N.N₀.Ent) :
    (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.S.Ent :=
  ⟨.inr (.inl n.1), n.2⟩

theorem stdNewS_newAt_inj :
    Function.Injective (V.newAtS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD) := by
  rintro ⟨a, j⟩ ⟨a', j'⟩ h
  obtain ⟨h1, h2⟩ := Sigma.mk.inj h
  obtain rfl : a = a' := Sum.inl.inj (Sum.inr.inj h1)
  exact congrArg (Sigma.mk a) (eq_of_heq h2)

/-- The forms and the targets. -/
def StdNew.aftFS
    (x : ((V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.Xc ×
        (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.hd.Smp) ×
      (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.Lc)
    (j : (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.RowN) (n : V.N.N₀.Ent) :
    E :=
  ((V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.rowsOf
      (V.pJS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD)
      (V.pQS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD) (Hd.foldD Sb sl Z A₀).slf id x).2
    j (V.newAtS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD n)
def StdNew.aftTS
    (x : ((V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.Xc ×
        (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.hd.Smp) ×
      (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.Lc)
    (j : (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.RowN) : E :=
  ((V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.rowsOf
    (V.pJS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD)
    (V.pQS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD) (Hd.foldD Sb sl Z A₀).slf id x).1 j

theorem stdNewS_after_all (hC : Sh.Cf.Laws)
    (x : ((V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.Xc ×
        (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.hd.Smp) ×
      (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.Lc)
    (m : (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.S.Msg) :
    (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.After x m ↔
    Slf.All (fun _ : (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.RowN =>
        (Slf.idf : Slf E
          ((V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.S.Ent → E)
          (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.S.Ent))
      ((V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.rowsOf
        (V.pJS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD)
        (V.pQS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD) (Hd.foldD Sb sl Z A₀).slf id x)
      ((V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.S.ents m) :=
  ldLoc_after_rows E Kc _ _ _ _ _ _
    (stdNewS_lin V Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD hC) x m

/-- For `G.P` nonempty, if the folded complex has its laws (`hC`): what is claimed after the
locations, as claims on the entries of the new messages. -/
theorem stdNewS_after_new (hC : Sh.Cf.Laws)
    (x : ((V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.Xc ×
        (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.hd.Smp) ×
      (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.Lc)
    (m : (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.S.Msg) :
    (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.After x m ↔
    ∀ j, ∑ n : V.N.N₀.Ent, V.aftFS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD x j n *
        (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.S.ents
          m (V.newAtS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD n) =
      V.aftTS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD x j := by
  rw [stdNewS_after_all V Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD hC x m]
  refine forall_congr' fun j => ?_
  show (∑ n, _ * _ = _) ↔ _
  rw [← Fintype.sum_of_injective (V.newAtS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD)
      (stdNewS_newAt_inj V Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD)
      (fun n =>
        V.aftFS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD x j n *
          (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.S.ents
            m (V.newAtS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD n))
      _ (fun n hn => ?_) fun _ => rfl]
  · rfl
  · obtain ⟨o, e⟩ := n
    have h0 := stdNewS_rows_new V Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD x j ⟨o, e⟩ fun a ha => by
      obtain rfl : o = .inr (.inl a) := ha
      exact hn ⟨⟨a, e⟩, rfl⟩
    exact (congrArg
        (· * (V.closeS Sb sl Z A₀ w0 L t tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.S.ents m ⟨o, e⟩)
        h0).trans (zero_mul _)

end

/-! ## A whole segment from a bundle, the one sending the standard sending -/

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
  (tl : ℕ) (N₁ : Sig E) (Y₁ : N₁.StdL E)
  (dat₁ : (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).tgt.S.Wit ×
      (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).tgt.Wp →
    ∀ b, Y₁.Dt b → E)
  (L₁ t₁ : N₁.O → ℕ) (Wp' : Type) (rst : Wp → Wp') (bkD : (∀ b, Y₁.Dt b → E) → Wp' → Wp)

/-- the second half of the closing, the one sending the standard sending -/
@[reducible] def GPack.closeS :
    LdCloseD (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀) :=
  pk.V.closeS (fun _ : Unit => GPack.Sx Sb Z)
    (pk.row1 Sb sl Z) Zb A₀ w0 L₂ t₂ tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD

/-- The segment: any body under `hT` (every move of it is a sending, a sub-protocol or a step
without rounds); many rows into one; the step; bridge-to-fold; the one sending of the new messages
and the riders by the standard sender; the locations. -/
def GPack.seg1S :
    LdSeg a (pk.closeS Sb sl Z Zb A₀ w0 tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.tgt :=
  segOne (pk.cl1 Sb sl Z Zb A₀) body hT
    (pk.link (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀ dw)
    (pk.closeS Sb sl Z Zb A₀ w0 tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD)

theorem gPack_seg1S (hb : body.Hyp) (hZ : Z.OK) (hZb : Zb.OK)
    (hs : ∀ b st (n : S.Ent), ¬ mem n.1 → sl b st n = 0) (h₁ : Y₁.OK t₁)
    (hl : ∀ b, (N₁.om b).C.Laws) (hs₁ : ∀ b, (N₁.om b).ListLE (L₁ b)) (he : ∀ b, (N₁.om b).Evades)
    (hbk : ∀ w, bkD (dat₁ w) (rst w.2.2) = w.2.2) :
    (pk.seg1S Sb sl Z Zb A₀ body hT dw w0 tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).Hyp :=
  ldSegWhole_one E Kc a (pk.cl1 Sb sl Z Zb A₀) body hT _ _ hb hZ
    (fun b st n hn => hs b st n fun h => hn ((pk.memI n.1).2 h)) (gPack_fold pk _ _ Zb A₀ dw hZb)
    (stdNewS_snd pk.V _ _ Zb A₀ w0 L₂ t₂ tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD pk.new h₁ hl hs₁ he hbk)

theorem gPack_seg1S_zk (base : MaskFact a.J.W → Prop) (hb : body.Zk base) :
    (pk.seg1S Sb sl Z Zb A₀ body hT dw w0 tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).Zk base :=
  ldSegWholeZk_one E Kc a (pk.cl1 Sb sl Z Zb A₀) body hT _ _ base hb

variable {E0 : ExtSpec} {Rc Pw : Type} (i : IxAt E0 E₀) (rc : St₀ → Rc)
  (px : Wp → Pw) (px' : Wp' → Pw)
  (q₂ : Finset
      (E₀.prod (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).S₂.ext).Pos → Prop)

open Classical in
/-- The format: after the locations: q₂; at most t₂ long positions of each new message; at most t₁ b
of the rider b.
(not all hypotheses are named here: see the statement below) -/
theorem gPack_seg1S_fmt (φ : JFmt Kc E0 Rc Pw a.J)
    (hb : body.Fmt φ
      ((pk.cl1 Sb sl Z Zb A₀).bat.src.fmt i (fun st => rc st.2) px (pk.qIn Sb sl Z Zb A₀ q₂)))
    (hZb : Zb.OK) (ht : tl ≤ t) (h₁ : Y₁.OK t₁) (hl : ∀ b, (N₁.om b).C.Laws)
    (hs₁ : ∀ b, (N₁.om b).ListLE (L₁ b)) (he : ∀ b, (N₁.om b).Evades)
    (hbk : ∀ w, bkD (dat₁ w) (rst w.2.2) = w.2.2) (hpx : ∀ wp, px' (rst wp) = px wp) :
    (pk.seg1S Sb sl Z Zb A₀ body hT dw w0 tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).Fmt φ
      ((pk.closeS Sb sl Z Zb A₀ w0 tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc.tgt.fmt
        i (fun st => rc st.2) px'
        ((pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).S₂.qSum
          (pk.V.N.N₀.sum N₁) q₂ (Sum.elim (fun _ => t₂) t₁))) := by
  refine ⟨_,
    (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).src.fmt
      i (fun st => rc st.2) px (pk.qIn Sb sl Z Zb A₀ q₂),
    (pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).tgt.fmt (i.inr _)
      (fun st => rc st.2) (fun w => px w.2)
      ((pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).qOpen q₂ tl),
    (pk.closeS Sb sl Z Zb A₀ w0 tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).snd.tgt.fmt
      (i.inr _) (fun st => rc st.2) px'
      ((pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).S₂.qSum (pk.V.N.N₀.sum N₁)
        ((pk.fold (fun _ : Unit => GPack.Sx Sb Z) (pk.row1 Sb sl Z) Zb A₀).qOpen q₂ tl)
        (Sum.elim (fun _ => t₂) t₁)),
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
      (pk.closeS Sb sl Z Zb A₀ w0 tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).snd (i.inr _) (fun st => rc st.2)
      (fun w => px w.2) px' _
      (stdNewS_snd pk.V _ _ Zb A₀ w0 L₂ t₂ tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD pk.new h₁ hl hs₁ he hbk)
      fun w => hpx w.2.2
  · refine (LdProg.fmt_snoc _ _ _ _).2 ⟨_, (LdProg.fmt_nil _ _ _).2 rfl, (Chain.fmt_one _ _ _).2 ?_⟩
    exact ldFmt_loc E Kc E0 Rc Pw
      (pk.closeS Sb sl Z Zb A₀ w0 tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD).loc i rc px' _ _
      (fun ρ U hU =>
        LdCloseD.loc_need _ q₂ (pk.closeS Sb sl Z Zb A₀ w0 tl N₁ Y₁ dat₁ L₁ t₁ Wp' rst bkD) ρ U hU)

end
end Cb
