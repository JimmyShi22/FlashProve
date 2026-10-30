-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/TieThreeR.lean: THE THIRD TIE OF THE CODE SWITCH AT A PLACE, WITH «REACHED»:
where the seated piece accepts, under the table of joints' promise in front and Rch, at a state
without a mark: what the table's row opens behind (the pin of every tenant of the new sending; the
two items on classes of rows) gives the relation behind of the law at a place (k02_place,
Johnson/Top/H0/K2Caller/PlaceLaw.lean): at every statement that meets the law's one condition in
front (OnTop) at a frame of the family: each new member's word decodes, with its OOD sample, to
the witness's message; each row that the switch's group has gained holds of these messages; the
carried base joint asks nothing. A JOINING. NO BLOCK IMPORTS THIS FILE.
hAt IS BOUND AT THE PIECE's OWN TWO VIEWS AND COLUMNS (the two written rounds' real
views vN d₁ … | vN d₂ …, and the columns that the step shows, shownP …), AS seated_both HANDS THEM
OVER, NOT OVER EVERY r₁ r₂ gs THAT WITNESS AtYes:
by reading, the payer of T3At.typed has what it needs at the piece's own columns alone.

ONE HYPOTHESIS MORE IN THE PAYER's HAND: in hAt the kind's own decision's
accept (decideWith sendByL8 p t [r₁, r₂] gs = .ok t') stands beside AtYes:
by reading, the road to OnlyAt (hands_of_plan) asks it, AtYes has no such field, and
«every drawn position is in range» follows from none of AtYes' fields. By seated_both
(K2Caller/SeatText.lean).
Asking that each typed member BE a member of the table's list,
and that the table's reader of OOD samples give newSmp TO THE SEED would ask
more than the proof needs and may be unpayable at the closed list of
members, where both seeds are chosen. HERE: K2.MembersLike (Alike, Sound/PinMove.lean) · SmpBySeat ·
K2.SmpLike (up to the seed's values): K2C/StringsNew.lean.
  decs_behind   the first clause: from the pins (pinJT at each new member's seat), carried to the
                typed member along Alike (pin_move_mp), the seed turned by its values
                (dec_congr)
  T3At          WHAT IS ASKED AT AN ACCEPT, as one structure of named fields
  k02_t3R       the tie
THE PREMISES, AND WHO PAYS EACH. hoP · hoC · hoR: the row opens «pin m 0», «row m carried», «row m
position»: closed facts on the written list. hpin · hrowM: the composed meaning's two fields, by
unfolding at its filling (mgAll_pin · mgAll_row). M: K2.MembersLike ms ⟨r.l, seatN⟩ (N.sent m 0):
four closed clauses on lists (owed). hBy: SmpBySeat (smpNamed_bySeat). hσ:
K2.SmpLike: the table's reader gives, at the new members behind, newSmp's answers and a seed with
newSmp's seed's values (owed likewise). hAt: AT EVERY ACCEPT, with the promise in front, Rch, «the
second round draws as many positions as the typed structure counts» and the decision's own accept
in hand: the way out leaves the tables and the switch's group's rows (for AtYes.behind): at a
link: «opened» leaves the statement (opened_keeps, Johnson/Top/H0/Walk/FrameOpened.lean); at the
finish: every field but «here» is left (K2.finishBehindQ_iff); at the head "H.1.quiet" turns the
statement (it joins the link's own messages to the group) ; that it leaves the tables and every
group's rows: K2Caller.headOpenQ_kept (Johnson/Top/H0/K2Caller/DoorKeeps.lean: Kept t m: the same
tables, and group by group the same open rows), and headOpenQ_same
(Tw/K2C/HeadQuietSame.lean; by report: not read and not built) · and T3At: keptPos
(keptPos_atLink | _atFront | _atFinish, KeptPosAt.lean) · fresh (the new group has no row yet) ·
groupIs · carried · position (the debts of K2.SwitchDebts: rows_debts,
Johnson/Top/H0/Tw/K2C/RowsDebts.lean) · seats (seat_by_new with
«the piece's base is the first tree's number plus the own trees sent so far») · count · groupNo
(the first tie's content) · typed: OnlyAt at each laid row (only_at_yes (not in this library) |
only_at_yes_light, over K2Hands.only_at_rows: by report: statements only) ·
ZeroAsks · SlotsAll (words_at_accept, K2Caller/WordsNamesAt.lean).
THREE NOTES FOR WHOEVER ASSEMBLES THE TIES. m IS THE NEW SEGMENT's NUMBER (pin m 0 · N.sent m 0);
in the first and fourth ties m is the carried item's: m here = m there + 1. T3At.fresh with
OnTop's «G.rows.size = rows» forces rows = 0 at every place. T3At.seats speaks of the book BEHIND
(b.1): a payer that takes it from «reached» wants Rch (k + 1) b: it leans on the hand-on
(HandsOn).
LIMITS. A SENTENCE WITH MANY PREMISES; NONE IS SHOWN MET HERE; no member. It is no soundness of
the protocol. On hiding nothing.
-/
import Johnson.Top.H0.Tw.K2C.TieThreeRows
import Johnson.Top.H0.K2Caller.SeatText
import Johnson.Top.H0.K2Caller.TopAt
import Johnson.Top.H0.Tw.K2C.StringsNew
import Johnson.Desc.Sound.BordersQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc (Block Claim FileDescription Strs Wit Place)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers)
open VerifiableInference.Desc.First.K2Hands
open _root_.Run (ckP)

variable {F : Frame}

theorem decs_behind {A Xi Cells Tok : Type} {r : SwRow} (G : FileDescription Xi)
    (seatN : Fin r.l.length → ℕ × ℕ) (n0 : ℕ) (arr : ℕ → ℕ → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf r.cs s.l).om i).Smp)
    {ms : List Mem} {X : List (ℕ × ℕ)} (M : K2.MembersLike ms ⟨r.l, seatN⟩ X)
    (hBy : SmpBySeat r.cs smp) (a : A) (b : Rec × F.E.Str)
    (hσ : K2.SmpLike r.cs smp a ⟨r.l, seatN⟩ (fun o => newSmp n0 b.1 o))
    (w : Wit Cells Tok MsgT)
    (hp : ∀ i, pinJT r.cs G arr smp ms (seatN i).1 (seatN i).2 a (strsOf F b.2) w) :
    ∀ o, (sigOf r.cs r.l).decs (fun o => newSmp n0 b.1 o)
      (wordsOf G r.cs r.l seatN (strsOf F b.2)) o = some (msgsOf r.cs r.l seatN arr w o) := by
  intro o
  obtain ⟨⟨e, he, hse⟩, hall⟩ := hp o
  have hl : VerifiableInference.Desc.Sound.Alike e ⟨⟨r.l, seatN⟩, o⟩ := M.like o e he hse
  obtain ⟨zσ, hz, -, hd⟩ := pin_move_mp r.cs G arr smp e ⟨⟨r.l, seatN⟩, o⟩ hl a
    (hBy a e ⟨⟨r.l, seatN⟩, o⟩ hl) (strsOf F b.2) w (hall e he hse)
  obtain ⟨zz, hzz, hv, ha⟩ := hσ o
  have hz' : smp a ⟨r.l, seatN⟩ o = some zσ := hz
  obtain rfl : zz = zσ := Option.some.inj (hzz.symm.trans hz')
  have hd' : ((sigOf r.cs r.l).om o).dec (wordsOf G r.cs r.l seatN (strsOf F b.2) o) (zz.1, zz.2) =
      some (msgsOf r.cs r.l seatN arr w o) := hd
  rw [VerifiableInference.Desc.Sound.dec_congr _ _ zz.1 (newSmp n0 b.1 o).1 zz.2 hv, ha] at hd'
  exact hd'

/-- What the third tie asks at an accept: x the front, rows the rows that the switch lays, s' the
state behind the seated sub-protocol. -/
structure T3At {r : SwRow} (H : r.OK)
    (iJ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
      r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r H (Letters.plain r H).t₀ (Letters.plain r H).oM (Letters.plain r H).oZ).keep
      r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    (seatN : Fin r.l.length → ℕ × ℕ) (N : Numbers) (m n0 grp : ℕ) (s' : Rec)
    (x : _root_.Tw.K2.Front) (rows : List OnBytes.Row) (r₂ : Fmt.RoundView) (Gg : Group) : Prop where
  keptPos : K2.KeptPos x.T
  fresh : Gg.rows = #[]
  groupIs : N.groupAt m = x.f.group
  carried : ∀ W₀, K2.frameAt x = some W₀ → N.rowsAt m .carried = (0, 1 + K2.keptSamples x W₀)
  position : ∀ W₀, K2.frameAt x = some W₀ → N.rowsAt m .position =
    (1 + K2.keptSamples x W₀, r₂.drawn.poss.length * (1 + K2.targetRows x.T + 2))
  seats : ∀ i : Fin r.l.length,
    seatBy noFirst s'.book (x.st.oracles.size + i.val) = some (seatN i)
  count : x.st.oracles.size = n0
  groupNo : x.f.group = grp
  typed : ∃ (W₀ : SwitchFrame) (mem row : (selR (Letters.plain r H)).Kp → ℕ)
    (pl : (selR (Letters.plain r H)).Kp → KeptPlace),
    (∀ ρ ∈ rows, OnlyAt r.cs r.l (fun i => x.st.oracles.size + i)
      (Inside (selR (Letters.plain r H)).s W₀ pl) ρ) ∧
    ZeroAsks (selR (Letters.plain r H)) r.cs r.l iJ iQ W₀ mem row pl x.st.oracles.size s'.st ∧
    SlotsAll (selR (Letters.plain r H)).Kp W₀ mem row pl

set_option maxHeartbeats 4000000 in
theorem k02_t3R {P Cells Tok Cl Cl₀ Xi : Type} {r : SwRow} (h : r.ok = true)
    (iJ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says
        h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.J →
      (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r (r.ok_says h) (Letters.plain r (r.ok_says h)).t₀ (Letters.plain r (r.ok_says
        h)).oM (Letters.plain r (r.ok_says h)).oZ).keep r.kp).Sh.Cf.Q →
      (sigOf r.cs r.l).Ent)
    (G : FileDescription Xi) (seatN : Fin r.l.length → ℕ × ℕ) (base : ℕ) (d₁ d₂ : RDT)
    (w2 : K2Wr r d₁ d₂) (arr : ℕ → ℕ → ℕ) (p : K2.P2)
    (orc : F.E.Str → ℕ → ℕ → List UInt64)
    (smpT : _root_.Tw.K2.Front → SwitchFrame → (vecD (plainD r (r.ok_says h))).held.Smp)
    (d₀ : (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).X ×
      (Cb.Pv.SendLoc.stage (selZ (Letters.plain r (r.ok_says h)) iJ iQ).sw).Ex.Str) (y₀ : F.E.Str)
    (aOf : (selLoc (Letters.plain r (r.ok_says h)) iJ iQ).hd.K → ℕ)
    (iOf : ∀ k, ((selLoc (Letters.plain r (r.ok_says h)) iJ iQ).hd.o k).Z.S → ℕ)
    (B : Block Rec Cl) (enter : Rec → Except String Rec) (leave : Rec → Rec → Except String Rec)
    (hr : B.rounds = (K2.codeSwitchKind (Cl := Cl₀) p).rounds)
    (hs : SeatStep B (K2.codeSwitchKind (Cl := Cl₀) p) enter leave)
    (ext' : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → Wit Cells Tok MsgT →
      Wit Cells Tok MsgT)
    (N : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place)
    (z : P) (Rch : ℕ → Rec × F.E.Str → Prop) (k m : ℕ)
    (hoP : Item.pin m 0 ∈ (rowQ links ps k).outs)
    (hoC : Item.row m .carried ∈ (rowQ links ps k).outs)
    (hoR : Item.row m .position ∈ (rowQ links ps k).outs)
    (smp : P × First.S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf r.cs s.l).om i).Smp) (ms : List Mem)
    (hpin : ∀ (q : ℕ × ℕ) s y w, Mg.pin q.1 q.2 (z, s) y w →
      pinJT r.cs G arr smp ms q.1 q.2 (z, s) y w)
    (hrowM : ∀ c s y w, Mg.row m c (z, s) y w →
      rowSays N (wordsAtFirst (P := P) arr) m c (z, s) y w)
    (M : K2.MembersLike ms ⟨r.l, seatN⟩ (N.sent m 0)) (hBy : SmpBySeat r.cs smp)
    (n0 grp rows : ℕ) (b₀ : TB (Letters.plain r (r.ok_says h)) iJ iQ) (Fam : SwitchFrame → Prop)
    (hσ : ∀ a τ b, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      (seatedAt (k2Piece (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G
          seatN base d₁ F) p base
        idExt) B ext').ior.red.out a τ = some b →
      K2.SmpLike r.cs smp (z, b.1) ⟨r.l, seatN⟩ (fun o => newSmp n0 b.1 o))
    (hAt : ∀ a τ b, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      (seatedAt (k2Piece (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G
          seatN base d₁ F) p base
        idExt) B ext').ior.red.out a τ = some b →
      ∀ t t' x y S3 Y rws Gg c, enter a.1 = .ok t → leave a.1 t' = .ok b.1 →
        (vN d₂ τ.2.2.1 τ.2.2.2.1).drawn.poss.length = baseCount r.set .request r.g →
        K2.decideWith _root_.Tw.K2.sendByL8 p t [vN d₁ τ.1 τ.2.1, vN d₂ τ.2.2.1 τ.2.2.2.1]
          (shownP (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G seatN base d₁ F) p
              base idExt (t, a.2) τ) = .ok t' →
        K2.AtYes p t t' (vN d₁ τ.1 τ.2.1) (vN d₂ τ.2.2.1 τ.2.2.2.1)
          (shownP (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G seatN base d₁ F) p
              base idExt (t, a.2) τ) x y S3 Y rws Gg c →
        K2.SameTables t'.st b.1.st ∧
        (b.1.st.groups[x.f.group]?).map (·.rows) = (t'.st.groups[x.f.group]?).map (·.rows) ∧
        T3At (r.ok_says h) iJ iQ seatN N m n0 grp b.1 x rws (vN d₂ τ.2.2.1 τ.2.2.2.1) Gg) :
    ∀ a τ b w, onQ N Mg links ps (fun s => (z, s)) k a → Rch k a → ¬ a.1.failed ≠ none →
      (seatedAt (k2Piece (W := Unit) (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂ (wordsMade iJ iQ G
          seatN base d₁ F) p base
        idExt) B ext').ior.red.out a τ = some b →
      relAt (meansQ N Mg (fun s => (z, s))) (outsQ links ps k) b w →
      ∀ W₀ : {V // Fam V}, ∀ a', OnTop iJ iQ p orc smpT d₀ y₀ W₀.1 n0 grp rows aOf iOf a' →
        lawRb (Letters.plain r (r.ok_says h)) iJ iQ p F.E.Str a' (b.1, fbMade iJ iQ G seatN n0 b₀ b)
          (wtMade iJ iQ seatN arr w) := by
  intro a τ b w ha hrc hm hout hrel W₀ a' hO
  have mem : ∀ i, i ∈ (rowQ links ps k).outs → meansQ N Mg (fun s => (z, s)) i b w := fun i hi =>
    hrel i (List.mem_append_left _ (List.mem_append_left _ hi))
  obtain ⟨t, t', et, el, hlen, ht, x, y', S3, Y, rws, Gg, c, A⟩ :=
      seated_both (Letters.plain r (r.ok_says h)) iJ iQ d₁ d₂
    (wordsMade iJ iQ G seatN base d₁ F) p base idExt w2 B enter leave hr hs ext'
    (strsTop iJ iQ p orc smpT d₀) (inXTop iJ iQ p orc smpT d₀ y₀) a b τ hout
  obtain ⟨hT, hR, T⟩ := hAt a τ b ha hrc hm hout t t' x y' S3 Y rws Gg c et el hlen ht A
  obtain ⟨Wz, mem', row', pl', hOnly, Q, Aall⟩ := T.typed
  have hP : ∀ q ∈ N.sent m 0, Mg.pin q.1 q.2 (z, b.1) (strsOf F b.2) w := mem _ hoP
  refine ⟨(rb_decs_iff iJ iQ G seatN n0 b₀ arr w b).2 (decs_behind G seatN n0 arr smp M
    hBy (z, b.1) b (hσ a τ b ha hrc hm hout) w fun i =>
        hpin _ _ _ _ (hP _ (M.into i))), ?_, rb_carried iJ iQ G seatN n0 b₀ arr w b⟩
  exact rows_behind iJ iQ seatN arr w (A.behind hT hR) T.keptPos T.fresh N m z (strsOf F b.2)
      T.groupIs
    T.carried T.position (hrowM _ _ _ _ (mem _ hoC)) (hrowM _ _ _ _ (mem _ hoR)) T.seats hOnly Q
    Aall a'.1 fun fx hfx => by
      obtain ⟨-, -, e1, -, e2, -⟩ := hO.1 fx hfx
      exact ⟨e1.trans T.count.symm, e2.trans T.groupNo.symm⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.decs_behind
#print axioms VerifiableInference.Desc.First.K2Caller.k02_t3R
