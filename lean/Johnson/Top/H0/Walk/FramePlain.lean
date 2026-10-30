-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FramePlain.lean: the link's frame's law in the plain form
(Johnson/Desc/Plain/Leads.lean: Reduction.Leads), at a piece of the rule of composition (Piece).

The frame's blocks take no round and draw nothing: what they guarantee holds for certain. So each
law is by Leads.of_sure, at the piece's own list of errors, whatever it is. That a piece's
reduction puts out b only where its block's decision went on to b's record is piece_decides
(Johnson/Desc/Plain/K7Law.lean).

How a block of the frame stands in a description, and what is asked of it here:
  YesOf b f         b says yes only where f does, with f's record: met by roundlessBlock .. f
                    (yesOf_quiet), by that block with another test on the plan (Link.blocksInOrder's
                    "laid": yesOf_plan), and by any wrapper that can only turn a yes into a no
                    (yesOf_narrow)
  YesBehind b p f   b is another block p with the frame's step joined behind it: a yes of b is a
                    yes of p up to some record m, and then f's yes from m: met by Block.andThen
                    (yesBehind_andThen): so stands "opened", behind the link's first call
  leads_of_yes, leads_behind   the two general steps
  laid_law, openedAtt_law, openedLay_law, openedZero_law, cleared_law, clearedRow_law
                    the frame's law

Limits. Post-conditions of a yes; a block that refuses all meets them emptily; nothing on
completeness; no soundness statement. The letters (l, P, X, counts, left, row) are free: that they
are the plan's is for whoever fills them in to show. In the laws on "opened" the record m between
the first call's block and the frame's step is bound by "there is": what that block guarantees of
m is its own law's to say.

-/
import Johnson.Desc.Plain.K7Law
import Johnson.Top.H0.Walk.FrameProps
import Johnson.Top.H0.Walk.FrameSized

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Plain
open OnBytes OnBytes.Model
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err)
open VerifiableInference.Desc (Block roundlessBlock)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain (piece_decides)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Pend (pendingRowO takeEntry)

variable {Cl W : Type} {C : CK} {F : Frame}

/-! ### how a block of the frame stands -/

/-- b says yes only where f does, with f's record. -/
def YesOf (b : Block S Cl) (f : S → Except String S) : Prop :=
  ∀ s rs gs t, b.decide s rs gs = .ok t → f s = .ok t

theorem yesOf_quiet (name : String) (chain : Nat) (link : Option Nat) (piece : Nat) (f : S → Except
    String S) :
    YesOf (roundlessBlock name chain link piece f : Block S Cl) f := fun _ _ _ _ h => h

theorem yesOf_plan (name : String) (chain : Nat) (link : Option Nat) (piece : Nat) (f : S → Except
    String S) (plan : Bool) :
    YesOf ({ (roundlessBlock name chain link piece f : Block S Cl) with planOk := plan }) f := fun _ _ _
        _ h => h

/-- A wrapper that can only turn a yes into a no. -/
theorem yesOf_narrow {b c : Block S Cl} {f : S → Except String S} (hb : YesOf b f)
    (hc : ∀ s rs gs t, c.decide s rs gs = .ok t → b.decide s rs gs = .ok t) : YesOf c f :=
  fun s rs gs t h => hb s rs gs t (hc s rs gs t h)

/-- b is p with the frame's step joined behind it. -/
def YesBehind (b p : Block S Cl) (f : S → Except String S) : Prop :=
  ∀ s rs gs t, b.decide s rs gs = .ok t → ∃ m rs' gs', p.decide s rs' gs' = .ok m ∧ f m = .ok t

theorem yesBehind_andThen (name : String) (p q : Block S Cl) {f : S → Except String S} (hq : YesOf q
    f) :
    YesBehind (p.andThen name q) p f := by
  intro s rs gs t h
  have h' : (p.decide s (rs.take p.rounds.length) (gs.take p.openings)).bind (fun s' =>
      q.decide s' (rs.drop p.rounds.length) (gs.drop p.openings)) = .ok t := h
  cases hm : p.decide s (rs.take p.rounds.length) (gs.take p.openings) with
  | error e => rw [hm] at h'; exact nomatch h'
  | ok m => rw [hm] at h'; exact ⟨m, _, _, hm, hq _ _ _ _ h'⟩

/-! ### the two general steps -/

theorem leads_of_yes (p : Piece C F S Cl W) {f : S → Except String S} (hp : YesOf p.b f)
    {Q : S → S → Prop} (hQ : ∀ s t, f s = .ok t → Q s t) :
    p.ior.red.Leads (fun _ => True) (fun a b => Q a.1 b.1) p.err :=
  Reduction.Leads.of_sure _ fun a τ b _ hb => by
    obtain ⟨rs, gs, hd⟩ := piece_decides p a τ b hb
    exact hQ _ _ (hp _ _ _ _ hd)

theorem leads_behind (p : Piece C F S Cl W) {first : Block S Cl} {f : S → Except String S}
    (hp : YesBehind p.b first f) {Q : S → S → Prop} (hQ : ∀ s t, f s = .ok t → Q s t) :
    p.ior.red.Leads (fun _ => True)
      (fun a b => ∃ m rs gs, first.decide a.1 rs gs = .ok m ∧ Q m b.1) p.err :=
  Reduction.Leads.of_sure _ fun a τ b _ hb => by
    obtain ⟨rs, gs, hd⟩ := piece_decides p a τ b hb
    obtain ⟨m, rs', gs', hm, hf⟩ := hp _ _ _ _ hd
    exact ⟨m, rs', gs', hm, hQ _ _ hf⟩

/-! ### the frame's law -/

/-- «laid»: the record is handed on as it is; no link is open in it; a first call is due; the chain
stands at link l. -/
theorem laid_law (p : Piece C F S Cl W) (l : Nat) (hp : YesOf p.b (layFront l)) :
    p.ior.red.Leads (fun _ => True) (fun a b => b.1 = a.1 ∧ Props.LayFront l a.1) p.err :=
  leads_of_yes p hp (Q := fun s t => t = s ∧ Props.LayFront l s) fun _ _ h => Props.layFront_iff.1 h

/-- What «opened» guarantees at every sort of link. ns: the plan's number of slots. -/
def Opened (X : LinkPub) (l ns : Nat) (s t : S) : Prop :=
  s.atBetween = true ∧ Props.FirstRun s.check ∧ s.check.frame.link = l ∧
    t.link? = some { check := s.check, link := l, arrayOf := X.arrayOf, list := X.Tp } ∧
    t.fork? = some (startFork X ns) ∧ Law.SizedAt ns t ∧
    t.check = s.check ∧ t.live = s.check ∧ t.st = s.st ∧ t.failed = s.failed

theorem openedAtt_law (p : Piece C F S Cl W) (first : Block S Cl) (P : AttPar) (hp : YesBehind p.b
    first (openAtt P)) :
    p.ior.red.Leads (fun _ => True)
      (fun a b => ∃ m rs gs, first.decide a.1 rs gs = .ok m ∧ Opened P.X P.l P.ns m b.1 ∧
        b.1.tl? = some { P.tl₀ with funClosed := false, foldDrawn := 0 }) p.err :=
  leads_behind p hp (Q := fun s t => Opened P.X P.l P.ns s t ∧
      t.tl? = some { P.tl₀ with funClosed := false, foldDrawn := 0 }) fun s t h => by
    obtain ⟨h1, h2, _, h4, h5, h6, h7, h8, h9, _⟩ := Law.openAtt_ok h
    exact ⟨⟨h1, (Props.firstRun_iff _).1 h2, h4, h5, h6, Law.ledger_sized_at_lay_att h, h7,
      Law.openAtt_carries h, h8, h9⟩, Law.openAtt_tl h⟩

theorem openedLay_law (p : Piece C F S Cl W) (first : Block S Cl) (P : LayPar) (hp : YesBehind p.b
    first (openLay P)) :
    p.ior.red.Leads (fun _ => True)
      (fun a b => ∃ m rs gs, first.decide a.1 rs gs = .ok m ∧ Opened P.X P.l P.ns m b.1 ∧
        b.1.tl? = some P.tl₀) p.err :=
  leads_behind p hp (Q := fun s t => Opened P.X P.l P.ns s t ∧ t.tl? = some P.tl₀) fun s t h => by
    obtain ⟨h1, h2, _, h4, _, h5, h6, h7, h8, h9, _⟩ := Law.openLay_ok h
    exact ⟨⟨h1, (Props.firstRun_iff _).1 h2, h4, h5, h6, Law.ledger_sized_at_lay_lay h, h7,
      Law.openLay_carries h, h8, h9⟩, Law.openLay_tl h⟩

/-- Link 0: as at a layers' link, and the index masks' message is found, has a ledger with room, and
its number is laid into the walk's result. -/
theorem openedZero_law (p : Piece C F S Cl W) (first : Block S Cl) (P : LayPar) (fvs : List Bool)
    (kCol : Nat)
    (hp : YesBehind p.b first (openLayZero P fvs kCol)) :
    p.ior.red.Leads (fun _ => True)
      (fun a b => ∃ m rs gs, first.decide a.1 rs gs = .ok m ∧ Opened P.X 0 P.ns m b.1 ∧
        b.1.tl? = some P.tl₀ ∧
        ∃ im, Props.IndexMasksAt (roomOf fvs kCol) m.check m.st.oracles im ∧
          b.1.out.indexMasks = im) p.err :=
  leads_behind p hp (Q := fun s t => Opened P.X 0 P.ns s t ∧ t.tl? = some P.tl₀ ∧
      ∃ im, Props.IndexMasksAt (roomOf fvs kCol) s.check s.st.oracles im ∧
        t.out.indexMasks = im) fun s t h => by
    obtain ⟨h1, h2, h3, _, ⟨im, hi, ho⟩, h5, h6, h7, h8, h9⟩ := Law.openLayZero_ok h
    refine ⟨⟨h1, (Props.firstRun_iff _).1 h2, h3, h5, h6, Law.ledger_sized_at_lay_zero h, h7,
      by simp [S.live, h5], h8, h9⟩, Law.openLayZero_tl h, im, Props.indexMasksAt_iff.1 hi, ?_⟩
    rw [ho]

/-- «cleared»: what is carried across a link's end. -/
def Cleared (s t : S) : Prop :=
  t.live = s.live ∧ t.book = s.book ∧ t.roots = s.roots ∧ t.rowsOwed = s.rowsOwed ∧
    t.failed = s.failed ∧ t.req = s.req ∧ t.check = s.live ∧ t.st.codes = s.st.codes ∧
    t.st.groups = s.st.groups ∧ t.atBetween = true

theorem cleared_law (p : Piece C F S Cl W) (X : LinkPub) (counts : S → Except String Unit)
    (left : S → Option WsForkOut) (row : RowFn) (hp : YesOf p.b (clearWith X counts left row)) :
    p.ior.red.Leads (fun _ => True) (fun a b => counts a.1 = .ok () ∧ Cleared a.1 b.1) p.err :=
  leads_of_yes p hp (Q := fun s t => counts s = .ok () ∧ Cleared s t) fun s t h => by
    obtain ⟨_, _, _, _, hc, _⟩ := Props.clearWith_iff.1 h
    exact ⟨hc, Law.clear_carries h⟩

/-- «cleared» where the link leaves a row, at the pending row's own function: just one entry of the
index masks' ledger is taken, and the row that bears it is laid at the pile's end. -/
def ClearedRow (left : S → Option WsForkOut) (s t : S) : Prop :=
  ∃ l c l' w r, Law.ledgerAt s = some l ∧ takeEntry l = some (c, l') ∧ left s = some w ∧
    t.out.pending = s.out.pending ++ [r] ∧ r.masks = [(⟨s.out.indexMasks, c⟩, w.beta)] ∧
    t.out.indexMasks = s.out.indexMasks ∧ Law.ledgerAt t = some l'

theorem clearedRow_law (p : Piece C F S Cl W) (X : LinkPub) (counts : S → Except String Unit)
    (left : S → Option WsForkOut) (lay : WsLay) (lin : Params.LinShape) (hv : X.fv = true)
    (hp : YesOf p.b (clearWith X counts left fun im w n os => pendingRowO lay im w n lin os)) :
    p.ior.red.Leads (fun _ => True) (fun a b => ClearedRow left a.1 b.1) p.err :=
  leads_of_yes p hp (Q := ClearedRow left) fun _ _ h => Law.clear_row h hv

#print axioms yesBehind_andThen
#print axioms leads_of_yes
#print axioms leads_behind
#print axioms laid_law
#print axioms openedAtt_law
#print axioms openedLay_law
#print axioms openedZero_law
#print axioms cleared_law
#print axioms clearedRow_law

end Johnson.Desc.First.Walk.Plain
