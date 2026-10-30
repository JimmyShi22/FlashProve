-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SendLaw.lean: WHERE THE PROMISE BESIDE A PIN COMES FROM, AND HOW IT RIDES. The
law of a block that sends sampled members, as a statement in the rule of composition's frame; the
one row from which it follows; the frame fact by which pin and promise ride past a later block.
Statements and proofs.

The promise `CfAt` (MsgSig.lean) has three clauses: the record holds the member's sample; every leaf
is shown; no collision at the sample's seed. WordsLaw.lean spends it. WITHOUT A STATEMENT THAT
SOMEBODY GIVES IT, a reading of the samples that gives nothing (smp := nothing) would make every
closer's law free.
  `SendGivesCf p new on on'`: **THE LAW OF A SENDING**: at every statement a inside `on`, outside
    the rounds' lost sets (p.err): where p says yes, with b behind: on' b, and EACH NEW MEMBER HAS
    `CfAt` AT b. At smp := nothing it is false of every block with a new member that says yes, at
    some statement inside `on`, outside the price.
  `SendGivesSmp`: **THE ONE ROW THAT IS OWED**, in the library's own terms: …: on' b, and for each
    new member the record behind holds a sample at whose seed the library's `OMsg.Clash` does not
    hold of the member's word behind. (The priced seeds: the library's `sig_cnt_clash`; its lemma on
    a sending: `sigOf_send`, `send_closed`.)
  `SentBy p new` (WordsLaw.lean): each new member's tree is one that p's own stretch sends.
  `sendCf_of_smp` (PROVED): where the piece shows what it sends (`Piece.ShownAll`: `shownOfData`,
    ShownOfData.lean: at no price), `SendGivesSmp` gives `SendGivesCf`.
  `out_behind` (proved): the strings of the statement behind a piece are what its stage leaves.
  `SmpStays p ms`: A FRAME FACT, OWED BY EVERY BLOCK BETWEEN A SENDING AND ITS CLOSING: where p says
    yes, the record behind holds, for each member of ms, the sample that the record in front holds.
  `rides` (PROVED): past a piece in front of which the members' trees were sent (`Fenced`) and which
    keeps their samples (`SmpStays`): `PinAt` and `CfAt` say the same of the statement behind and of
    the statement in front.
  `fenced_later` (PROVED): what a piece's own stretch sends lies in front of (is `Fenced` at) every
    piece whose base is at or behind the end of that stretch's trees. `goodIn_carries` (PROVED):
    **THE PROMISE IS CARRIED PAST A BLOCK**: whatever a block owes (`Piece.GoodIn on on' R R'`),
    under `Fenced` and `SmpStays` it owes as well at (on ∧ Promised ms) and (on' ∧ Promised ms). So
    from its sender to its closer the promise goes: `SendGivesCf` · `fenced_later` ·
    `goodIn_carries` at every piece between. (That a PIN rides, in the table's own form:
    `pinFrames`, OwnOfWords.lean.)
A PIECE THAT CLOSES AND ALSO SENDS. `WordsAreCommitted` and `SendGivesCf` are two `Doomed` at one
p.err: two such join only at the SUM of the errors (GoodIn.lean's Limits). At such a piece the
sender's law has to stand INSIDE the closer's on' (on' b := … ∧ the new members' `CfAt` at b), under
the one `Doomed`: `sendCf_of_smp`, whose conclusion is a whole `Doomed`, does not serve there; what
serves is its inner step: `out_behind` with `Piece.ShownAll`.
Limits. At smp := `smpOf forms ans` (Seed.lean) `SmpStays` follows where the record's sample rows,
as linear forms, and their targets stay; a copy's rows bear another oracle's number (the program's
`Row.renamed`): the letter forms reads a row as a form ON THE MEMBER's OWN MESSAGE, so that number
is read away inside it: whoever fills forms shows it. NOTHING IS PROVED OF ANY BLOCK.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.WordsLaw
import Johnson.Desc.Sound.ShownOfData

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Doomed)

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {A Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
  (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  {C : CK} {Fr : Frame} {Cl W : Type}

/-- The strings of the statement behind a piece are what its stage leaves. -/
theorem out_behind (p : Piece C Fr A Cl W) (a b : A × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (h : p.ior.red.out a τ = some b) : b.2 = behind C Fr p.base p.ds a.2 τ := by
  have h' : (p.ior.out a.1 a.2 τ).map (fun x => (x, p.ior.imp a.2 τ)) = some b := h
  obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.1 h'
  rfl

/-- **THE LAW OF A SENDING**: behind it each new member has the promise. -/
def SendGivesCf (p : Piece C Fr A Cl W) (new : List Mem) (on on' : A × Fr.E.Str → Prop) : Prop :=
  ∀ a, on a → Doomed (uLT C p.ds) p.err fun τ => ∀ b, p.ior.red.out a τ = some b → on' b ∧
    ∀ x ∈ new, CfAt G cs x.1.l x.1.seat (fun z => smp z x.1) x.2 b.1 (strsOf Fr b.2)

/-- **The one row that is owed**: the record behind holds each new member's sample, and at its seed
the member's word behind has no collision. -/
def SendGivesSmp (p : Piece C Fr A Cl W) (new : List Mem) (on on' : A × Fr.E.Str → Prop) : Prop :=
  ∀ a, on a → Doomed (uLT C p.ds) p.err fun τ => ∀ b, p.ior.red.out a τ = some b → on' b ∧
    ∀ x ∈ new, ∃ z, smp b.1 x.1 x.2 = some z ∧
      ¬ ((sigOf cs x.1.l).om x.2).Clash (wordsOf G cs x.1.l x.1.seat (strsOf Fr b.2) x.2) z.1

/-- **From the row to the law**: "every leaf is shown" is gained at no price. -/
theorem sendCf_of_smp (p : Piece C Fr A Cl W) (new : List Mem) (on on' : A × Fr.E.Str → Prop)
    (hB : SentBy p new) (hSh : ∀ x ∈ new, p.ShownAll G cs x.1.l x.1.seat)
    (h : SendGivesSmp cs G smp p new on on') : SendGivesCf cs G smp p new on on' := by
  intro a ha
  refine Doomed.mono _ _ (fun τ hτ b hb => ⟨(hτ b hb).1, fun x hx => ?_⟩) (h a ha)
  obtain ⟨z, hz, hn⟩ := (hτ b hb).2 x hx
  obtain ⟨n, sh, hj, hs⟩ := hB x hx
  refine ⟨z, hz, ?_, hn⟩
  rw [out_behind p a b τ hb]
  exact hSh x hx a.2 τ x.2 n sh hj hs

/-- **A frame fact**: where the piece says yes, the record behind holds the members' samples as the
record in front does. -/
def SmpStays (p : Piece C Fr A Cl W) (ms : List Mem) : Prop :=
  ∀ a τ b, p.ior.red.out a τ = some b → ∀ x ∈ ms, smp b.1 x.1 x.2 = smp a.1 x.1 x.2

/-- **Pin and promise ride** past a piece in front of which the members' trees were sent and which
keeps their samples. -/
theorem rides (p : Piece C Fr A Cl W) (ms : List Mem) (hF : Fenced p.base ms)
    (hS : SmpStays cs smp p ms) (a b : A × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (hb : p.ior.red.out a τ = some b) (x : Mem) (hx : x ∈ ms) :
    (∀ w : Wit Cells Tok MsgT,
      PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 b.1 (strsOf Fr b.2) w ↔
        PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 a.1 (strsOf Fr a.2) w) ∧
      (CfAt G cs x.1.l x.1.seat (fun z => smp z x.1) x.2 b.1 (strsOf Fr b.2) ↔
        CfAt G cs x.1.l x.1.seat (fun z => smp z x.1) x.2 a.1 (strsOf Fr a.2)) := by
  have e := out_behind p a b τ hb
  have es := hS a τ b hb x hx
  have hw := wordsStay G cs x.1.l x.1.seat C Fr p.base p.ds a.2 τ x.2 (hF x hx)
  have hsh : ShownAt G cs x.1.l x.1.seat (strsOf Fr (behind C Fr p.base p.ds a.2 τ)) x.2 ↔
      ShownAt G cs x.1.l x.1.seat (strsOf Fr a.2) x.2 := by
    unfold ShownAt
    rw [wordStays Xi G C Fr p.base p.ds a.2 τ (x.1.seat x.2).1 (x.1.seat x.2).2 (hF x hx)]
  rw [e]
  unfold PinAt CfAt
  simp only [es, hw, hsh]
  exact ⟨fun _ => trivial, trivial⟩

/-- **From the sender to every later piece**: what a piece's own stretch sends lies in front of
every piece whose base is at or behind the end of that stretch's trees. -/
theorem fenced_later (p : Piece C Fr A Cl W) (new : List Mem) (h : SentBy p new) (base : ℕ)
    (hb : p.base + nTrees p.ds ≤ base) : Fenced base new := by
  intro x hx
  obtain ⟨n, sh, hj, hs⟩ := h x hx
  have := treeShT_lt _ _ _ hs
  omega

/-- **THE PROMISE IS CARRIED PAST A BLOCK**: whatever a block owes (`Piece.GoodIn`), it owes as well
with the promise of members that were sent in front of it, and whose samples it keeps, on both
sides. -/
theorem goodIn_carries (p : Piece C Fr A Cl W) (ms : List Mem) (on on' : A × Fr.E.Str → Prop)
    (R R' : A × Fr.E.Str → W → Prop) (hF : Fenced p.base ms) (hS : SmpStays cs smp p ms)
    (h : p.GoodIn on on' R R') :
    p.GoodIn (fun a => on a ∧ Promised cs G smp ms a.1 (strsOf Fr a.2))
      (fun b => on' b ∧ Promised cs G smp ms b.1 (strsOf Fr b.2)) R R' := by
  intro a ha
  refine Doomed.mono _ _ (fun τ hτ b hb => ⟨⟨(hτ b hb).1, fun x hx => ?_⟩, (hτ b hb).2⟩) (h a ha.1)
  exact ((rides (Cells := Unit) (Tok := Unit) cs G (fun _ _ => 0) smp p ms hF hS a b τ hb x hx).2).2
    (ha.2 x hx)

end

end VerifiableInference.Desc.Sound
