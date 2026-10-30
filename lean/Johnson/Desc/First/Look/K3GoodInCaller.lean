-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3GoodInCaller.lean: THE CLOSING STEP OF A LOOKUP's CHAIN, ONCE FOR ALL
CALLERS: from the law on the kind's decide and ANY caller of the proved lookup block with riders
(LookupCRCaller) to the form that the rule of composition asks of a block (Piece.GoodIn), by the
rule's own carriage (pieceGoodIn). It is the proof of k3_att_goodIn_of
(Johnson/Desc/First/Look/K3AttGoodIn.lean) with the caller, the two readers of the statement and the
witness, and the two sentences on the oracle messages made letters, with laws. Definitions and one
theorem. NO SOUNDNESS OF THE PROTOCOL IS CLAIMED: the premises that are not theorems are premises.

THE LETTERS. r: the caller. lm, first, mk, pl: the planes' row bits, the first mask slot, where a
mask entry and a cell of the planes' matrix lie among the caller's entries. st: the caller's state,
read off the rule's statement (at the head's link: the token that was heard). y₀: the oracles beside
the block: a constant. sm, wd: the samples and the words of the caller's signature, read off the
rule's statement. wt: the proved block's witness, read off the rule's.
Cond: what is asked of a statement beside the ledger. Pin: what ties a statement to a witness.
Says: what the joint in front says of a witness, at a statement.

THE END THEOREM k3_goodIn_caller: the piece p has GoodIn between
  on   COn: Cond; the record's ledger is open and has its sizes;
  RA   CFront: Pin, and Says;
  on'  COn': Cond of the statement behind; a ledger F' with its sizes and what was heard, g, stand
       in the record behind, and stand for some rounds (K3Stands);
  RB   CBehind: Pin still; THE ROW OUT (K3Out) at the record's g and F', at the entries that the
       caller's msg₀ reads off the witness's messages; AND ITS FOURTH ITEM (K3OutRider).
  err  the least written errors that bear the proved block's (bearT).

THE LAWS ASKED OF THE LETTERS. hSt: the caller's state stays under decide's yes. hOn: Cond gives the
proved block's condition in front. hStay: Cond stays under decide's yes, behind the stretch. hBack:
Pin goes back over the stretch. hDecs: Pin gives that every oracle message decodes to the witness's.
hOutB: the lookup's out-claim and the riders' clause are the proved joint behind (a line where the
caller's own joint R0 is quiet). hSays: the proved base joint in front gives Says. The oracles
behind the stretch are written out: (y.1, sLeft C (stg Fr p.base p.ds) y τ): what the stage leaves.

Limits. Those of K3AttGoodIn.lean. ALL IS AT LETTERS: nothing here says that any caller meets the
laws; a Cond that holds nowhere, or a Pin that no witness meets, makes the theorem empty. The
extractor is the identity.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Top.H.K3RowOutRider
import Johnson.Desc.Sound.KnowInProofs
import Johnson.Desc.First.Look.K3PieceSays
import Johnson.Desc.First.Look.K3Caller
import Johnson.Desc.First.Look.K3CallerErr
import OnBytes.Tie.Pv.Lookup.Peel.FoPeelMapsT

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open Cb.Fo.Pin
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

section
variable {S Cl W : Type} {Fr : Frame} (r : LookupCRCaller) (lm first : ℕ)
  (mk : ℕ → r.c.J₀) (pl : ℕ → ℕ → r.c.J₀) (st : S × Fr.E.Str → r.c.St₀) (y₀ : r.c.Ex.Str)
  (sm : S × Fr.E.Str → r.c.Sg.Smp) (wd : S × Fr.E.Str → r.c.Sg.ext.Str)
  (wt : W → r.c.Sg.Wit × r.c.Wp)
  (fork : S → Option Fork) (heard : S → Option Forest.Heard)
  (Cond : S × Fr.E.Str → Prop) (Pin : S × Fr.E.Str → W → Prop)
  (Says : S × Fr.E.Str → W → Prop)

/-- The witness's messages, as the signature's tuple. -/
def cMs (w : W) : r.c.Sg.Msg := r.c.Sg.msgs (wt w).1

/-- The entries, read off the witness's messages by the caller's msg₀. -/
def cMu (w : W) : r.c.J₀ → Cb.Gl.E := r.c.msg₀ (cMs r wt w)

/-- The reading of the places: a mask, a cell of the planes' matrix. -/
def cNu (w : W) (q : _root_.Fo.Pl) : Cb.Gl.E := zext (cMu r wt w) (placeOf mk pl q)

/-- **The condition in front.** -/
def COn (a : S × Fr.E.Str) : Prop :=
  Cond a ∧ ∃ Fk, fork a.1 = some Fk ∧ OnBytes.PscRun.Sized Fk

/-- **The promise behind.** -/
def COn' (a : S × Fr.E.Str) : Prop :=
  Cond a ∧ ∃ (g : Forest.Heard) (F' : Fork), fork a.1 = some F' ∧ heard a.1 = some g ∧
    OnBytes.PscRun.Sized F' ∧ K3Stands r.c.h lm first Reading.gl g F'

/-- **The relation in front.** -/
def CFront (a : S × Fr.E.Str) (w : W) : Prop := Pin a w ∧ Says a w

/-- **The relation behind: what the later blocks owe.** -/
def CBehind (a : S × Fr.E.Str) (w : W) : Prop :=
  Pin a w ∧ ∃ (g : Forest.Heard) (F' : Fork), fork a.1 = some F' ∧ heard a.1 = some g ∧
    K3Out r.c.h lm first (cNu r mk pl wt w) (forK Cb.Gl.E r.c.L (st a) (zext (cMu r wt w)))
      Reading.gl g F' ∧
    K3OutRider r lm first (st a) (cMs r wt w) g F'

/-- The statement of the proved block that is read off the statement in front. -/
def cRd (a : S × Fr.E.Str) : (r.c.St₀ × r.c.Sg.Smp) × (r.c.Ex.prod r.c.Sg.ext).Str :=
  ((st a, sm a), (y₀, wd a))

variable {r lm first mk pl st y₀ sm wd wt fork heard Cond Pin Says}

/-- The library's test on a written list of callers, at the list of one. -/
theorem okL_of_ok (hok : FoNums.ok r.c.h = true) : OkLookupC (callersCR [r]) := by
  intro c' hc'
  obtain rfl : c' = r.c := List.mem_singleton.1 hc'
  exact hok

/-- **THE END THEOREM, at any caller.** -/
theorem k3_goodIn_caller (p : Piece (ckP .two) Fr S Cl W)
    (hselL : SelLookupCR [r]) (hok : FoNums.ok r.c.h = true) (h5 : 5 ≤ lm) (hlm : lm ≤ r.c.h.kT + 5)
    (hmk : ∀ t, r.c.L.mkS t = mk (first + t))
    (hbc : ∀ t k j, k < r.c.h.NC →
      r.c.L.bc t k j =
        pl (FoNums.cellRC r.c.h lm (t, k, j)).1 (FoNums.cellRC r.c.h lm (t, k, j)).2)
    (decide : S → List Fmt.RoundView → List (List (ℕ × List UInt64)) → Except String S)
    (hext : ∀ a τ w, p.ext a τ w = w)
    (hM : List.Forall₂ MeetsT p.ds (specF r.c.h)) (hA : ∀ d ∈ p.ds, NoAns d.items)
    (hε : bearT p.ds _ ((kLookupCRN [r]).ε r) = some p.err)
    (hCut : PieceHears p decide)
    (P0 : Desc.First.Look.P) (hsh : P0.shape = some r.c.h)
    (hD : K3DecideHears fork heard P0.calls P0.pub P0.lid decide)
    (hnext : ∀ s rs cols s' Fk, decide s rs cols = .ok s' → fork s = some Fk → Fk.next = first)
    (hSt : ∀ s y (τ : Tr (uLT (ckP .two) p.ds)) rs cols s', decide s rs cols = .ok s' →
      st (s', (y.1, sLeft (ckP .two) (stg Fr p.base p.ds) y τ)) = st (s, y))
    (hOn : ∀ a, Cond a → ((kLookupCRN [r]).toKind.src r).on (cRd r st y₀ sm wd a))
    (hStay : ∀ s y (τ : Tr (uLT (ckP .two) p.ds)) rs cols s', decide s rs cols = .ok s' →
      Cond (s, y) → Cond (s', (y.1, sLeft (ckP .two) (stg Fr p.base p.ds) y τ)))
    (hBack : ∀ s y (τ : Tr (uLT (ckP .two) p.ds)) rs cols s' w, decide s rs cols = .ok s' →
      Pin (s', (y.1, sLeft (ckP .two) (stg Fr p.base p.ds) y τ)) w → Pin (s, y) w)
    (hDecs : ∀ a w, Pin a w → ∀ i, r.c.Sg.decs (sm a) (wd a) i = some ((wt w).1 i).1)
    (hOutB : ∀ X w, (forA Cb.Gl.E r.c.h r.c.L).lk.out id id X (zext (cMu r wt w)) →
      r.tgt (cMs r wt w) (X, y₀) →
        ((kLookupCRN [r]).B r).relR (X, y₀) (cMs r wt w, (wt w).2))
    (hSays : ∀ a w, ((kLookupCRN [r]).A r).relR (st a, y₀) (cMs r wt w, (wt w).2) → Says a w) :
    p.GoodIn (COn fork Cond) (COn' r lm first fork heard Cond) (CFront Pin Says)
      (CBehind r lm first mk pl st wt fork heard Pin) := by
  have hrm : r ∈ (kLookupCRN [r]).sizes := List.mem_singleton.2 rfl
  have hKA := lookupCRN_knowAt [r] (okL_of_ok hok) hselL
  refine pieceGoodIn S Cl _ _ Fr p _ _ _ _ ((kLookupCRN [r]).toKind.block r).R.red
    (fun _ => lookCarryT r.c.h r.c.L r.c.Ex p.ds hM.length_eq) ((kLookupCRN [r]).ε r)
    (cRd r st y₀ sm wd) _ _ ((kLookupCRN [r]).toKind.src r).on
    ((kLookupCRN [r]).toKind.dst r).on _ _ ((kLookupCRN [r]).toKind.src r).relR
    ((kLookupCRN [r]).toKind.dst r).relR ((kLookupCRN [r]).toKind.block r).ext
    (fun _ => lookCarryT_fits r.c.h r.c.L r.c.Ex p.ds hM _ _ (bearT_bears _ _ _ _ hε)) ?_ ?_
    (knowInOfCarry _ _ _ _ _ _ _ _ _ _ _
      (fun a τ b ha hb =>
        BaseKind.onOut_toKind (BaseKind.onOut_of_knowAt hKA) r hrm a τ b hb ha)
      (BaseKind.know_toKind (BaseKind.know_of_knowAt hKA) r hrm))
  · -- the condition in front gives the proved block's
    rintro a ⟨hC, -⟩
    exact hOn a hC
  · -- the block's yes
    rintro ⟨s, y⟩ τ ⟨s', y'⟩ ⟨hC, Fk, hFk, hSz⟩ ho
    obtain ⟨hp, e2, hw, cols, hdec⟩ := hCut _ τ _ ho
    have e2' : y' = (y.1, sLeft (ckP .two) (stg Fr p.base p.ds) y τ) := e2
    subst e2'
    have hC1 : Cond (s, y) := hC
    have hdec1 : decide s ((rvT (ckP .two) p.ds τ).map Desc.noDigest) cols = .ok s' := hdec
    have hnx : Fk.next = first := hnext _ _ _ _ _ hdec1 hFk
    -- (L1) at the caller
    obtain ⟨X, hx, hiff⟩ := out_iff_items [r] r hok lm first h5 hlm mk pl hmk hbc p.ds hM hA
      (cRd r st y₀ sm wd (s, y)) τ
    -- the out-statement by name: for the riders' clause
    have eX := out_is_lookOutE [r] r hok lm first mk pl hmk hbc p.ds hM hA
      (cRd r st y₀ sm wd (s, y)) τ X hx
    rw [mapsT_view] at hx
    -- (L2a): what was heard stands for the transcript's rounds
    obtain ⟨F1, F2, g, d1, d2, d3, -, hlaw⟩ := hD Cb.Gl.E Reading.gl lm s s' _ cols hw hdec1
    obtain rfl : Fk = F1 := Option.some.inj (Eq.trans (Eq.symm hFk) d1)
    obtain ⟨hSh, hPad, hI⟩ := hlaw hSz
    have hg : g.shape = r.c.h := by
      obtain ⟨h0, a0, -, a2⟩ := hSh
      obtain ⟨h1, b0, -, b2⟩ := shape_made hsh
      have e : h0 = h1 := Except.ok.inj (a0.symm.trans b0)
      rw [a2, b2, e]
    rw [hg, hnx, viewRounds_noDigest] at hI
    refine ⟨lookImgT r.c.h r.c.L r.c.Ex p.ds τ, _,
      lookCarryT_pass r.c.h r.c.L r.c.Ex p.ds hM.length_eq τ hp, hx,
      fun _ => ⟨hStay s y τ _ cols s' hdec1 hC1, g, F2, d2, d3, hPad.fit, _, hI⟩, ?_⟩
    rintro w ⟨hPin, g', F'', f1', f2', ⟨k1, k2, k3⟩, k4⟩
    obtain rfl : g = g' := Option.some.inj (Eq.trans (Eq.symm d3) f2')
    obtain rfl : F2 = F'' := Option.some.inj (Eq.trans (Eq.symm d2) f1')
    have hpin0 : Pin (s, y) w := hBack s y τ _ cols s' w hdec1 hPin
    -- the caller's state behind is the one in front
    have hst := hSt s y τ _ cols s' hdec1
    have k3' : K3OutKeys r.c.h lm first (cNu r mk pl wt w)
        (forK Cb.Gl.E r.c.L (st (s, y)) (zext (cMu r wt w))) Reading.gl g F2 := by
      rw [← hst]
      exact k3
    have k4' : K3OutRider r lm first (st (s, y)) (cMs r wt w) g F2 := by
      rw [← hst]
      exact k4
    have hout := (hiff (cMu r wt w)).2 ⟨k1 _ hI, k2 _ hI, k3' _ hI⟩
    have htgt : r.tgt (cMs r wt w) (X, y₀) := by
      rw [eX]
      exact tgt_of_rider r lm first _ (st (s, y)) (cMs r wt w) g F2 _ y₀ hI k4'
    refine ⟨wt w, ⟨fun i => hDecs (s, y) w hpin0 i, hOutB X w hout htgt⟩, fun hRA => ?_⟩
    rw [hext]
    exact ⟨hpin0, hSays (s, y) w
      (show (∀ i, r.c.Sg.decs (sm (s, y)) (wd (s, y)) i = some ((wt w).1 i).1) ∧
        ((kLookupCRN [r]).A r).relR (st (s, y), y₀) (cMs r wt w, (wt w).2) from hRA).2⟩

end

#print axioms k3_goodIn_caller

end VerifiableInference.OnPublicFiles
