-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/K6AtSig.lean: THE OUTPUT HEAD'S BLOCK'S TIES AT THE FILLING OF THE TABLE'S SIX
LETTERS ON THE ORACLES THAT LIES (`meaningSig`, Johnson/Desc/Sound/BordersFill.lean): WHAT RIDES
PAST THE BLOCK IS PAID THERE. Five lemmas, one theorem. A rule: NO RESULT ON THE PROTOCOL.

THE TIES STAND NOT AT THE TERM `meaningSig …` BUT AT ANY MEANING WHOSE SIX LETTERS ON THE ORACLES
ARE SO FILLED (`SigFields`): so that they hold at a meaning that lays other letters over it (the map
to the model's `meaningQ`).

What is said, at a meaning Mg with `SigFields cs G arr smp msT decT Mg`, at a piece that holds the
seated constant (`Seated`, Johnson/Desc/Sound/K6Tied.lean), where the samples' reader and the
decoder do not read where the chain stands (`Blind`):
  `k6_dec_rides`: "the stored table decodes with the record" rides.
  `blindOrder_sig`: "the sample is held" does not read where the chain stands (by the filling's
    text); "in order": a premise.
  `shownAt_rides`: every leaf of a tree that was sent in front of a piece shows its symbol behind it
    just where it does in front. `k6_shown_rides`, `k6_noColl_rides`: so "shown" and "no collision"
    ride, each alone, at every tenant of a tree that was sent in front of the piece (hFen).
  `K6Bill`: what is left of K6's side at this filling, one field a premise.
  **`tied61_at_sig`**: `Tied61` (Johnson/Desc/Sound/Border62.lean) at the object, at this filling:
    AGAINST `tied61_of_object`: hT, hDec, hSh ARE GONE; of hOr "in order" alone is left (hIn); NEW:
    hFen: a test on the plan.

Limits. smp, decT, msT, Mg are letters. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.Border62
import Johnson.Desc.Sound.BordersFill
import Johnson.Desc.Sound.SendLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound

open OnBytes.Maker OnBytes.Flat KObj Johnson.Pack
open _root_.Run.PQ (CK SgX)

/-- Every leaf of a tree that was sent in front of a piece shows its symbol behind the piece just
where it does in front. -/
theorem shownAt_rides (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {A Cl W : Type} {C : CK}
    {Fr : Frame} (p : Piece C Fr A Cl W) (a b : A × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (hb : p.ior.red.out a τ = some b) (x : Mem) (hx : (x.1.seat x.2).1 < p.base) :
    ShownAt G cs x.1.l x.1.seat (strsOf Fr b.2) x.2 ↔
      ShownAt G cs x.1.l x.1.seat (strsOf Fr a.2) x.2 := by
  rw [out_behind p a b τ hb]
  unfold ShownAt
  rw [wordStays Xi G C Fr p.base p.ds a.2 τ (x.1.seat x.2).1 (x.1.seat x.2).2 hx]

/-- **The table's six letters on the oracles are filled as `meaningSig` fills them.** -/
structure SigFields (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi)
    (arr : ℕ → ℕ → ℕ)
    (smp : P × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (msT : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → P × First.S → Option Cells)
    (Mg : First.Meaning P (Wit Cells Tok MsgT)) : Prop where
  pin : Mg.pin = pinJT cs G arr smp msT
  noColl : Mg.noColl = noCollJT cs G smp msT
  shown : Mg.shown = shownJT cs G msT
  held : Mg.held = fun j t a => smpHeld a.2.st a.2.book j t
  pinW : Mg.pinW = pinWOf decT
  decodes : Mg.decodes = decodesOf decT

/-- At `meaningSig` itself: by its text. -/
theorem sigFields_sig (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi)
    (arr : ℕ → ℕ → ℕ)
    (smp : P × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (msT : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → P × First.S → Option Cells)
    (Mg₀ : First.Meaning P (Wit Cells Tok MsgT)) :
    SigFields cs G arr smp msT decT (meaningSig cs G arr smp msT decT Mg₀) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A meaning whose six letters are so filled IS `meaningSig` of itself: so whatever is shown at the
term `meaningSig …` holds at it. -/
theorem SigFields.eq {cs : OnBytes.Codes} {Xi P Cells Tok : Type} {G : FileDescription Xi}
    {arr : ℕ → ℕ → ℕ}
    {smp : P × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp}
    {msT : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → P × First.S → Option Cells}
    {Mg : First.Meaning P (Wit Cells Tok MsgT)} (h : SigFields cs G arr smp msT decT Mg) :
    meaningSig cs G arr smp msT decT Mg = Mg := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  cases Mg
  simp only at h1 h2 h3 h4 h5 h6
  subst h1 h2 h3 h4 h5 h6
  rfl

end VerifiableInference.Desc.Sound

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning Pub pubFit sampledIn pubOfItems)
open VerifiableInference.Desc.Sound (Piece Frame relAt Sending Mem MsgT onQ meansQ relQ insQ outsQ
  openAfter strsOf openQ pubQ Fenced ErrBears kitK kitFs BlindOrder meaningSig out_behind
  shownAt_rides SitsAt SigFields)

section
variable (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option Cells) (msT : List Mem)
  {Mg : Meaning P (Wit Cells Tok MsgT)} (hSig : SigFields cs G arr smp msT decT Mg)
  {Wp : OnBytes.Model.Verify.Public} {fld : Fmt.Fld} {Fr : Frame}
  {q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT)} {l : ℕ}
  {bef : List (ℕ × ℕ)} {B bS : Block S Claim}

include hSig

/-- "The stored table decodes with the record" rides past K6's block. -/
theorem k6_dec_rides (H : Seated Wp fld Fr q l bef B bS) (hBl : Blind cs smp decT)
    (a : (P × S) × Fr.E.Str) (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds))
    (b : (P × S) × Fr.E.Str) (hb : q.ior.red.out a τ = some b)
    (h : Mg.decodes a.1 (strsOf Fr a.2)) :
    Mg.decodes b.1 (strsOf Fr b.2) := by
  obtain ⟨o, F1, X, Q, _, _, _, e⟩ := k6_behind H a b τ hb
  have e2 := out_behind q a b τ hb
  rw [hSig.decodes] at h ⊢
  show (decT (strsOf Fr b.2).cell b.1).isSome = true
  rw [e, hBl.dec, e2]
  exact h

/-- At this filling "the sample is held" does not read where the chain stands. -/
theorem blindOrder_sig
    (hIn : ∀ (z : P) (s : S) h, Mg.inOrder (z, { s with here := h }) = Mg.inOrder (z, s)) :
    BlindOrder Mg :=
  ⟨hIn, fun _ _ _ _ _ => by rw [hSig.held]⟩

/-- "Shown" rides, at a tenant of a tree that was sent in front of the piece. -/
theorem k6_shown_rides (a : (P × S) × Fr.E.Str) (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds))
    (b : (P × S) × Fr.E.Str) (hb : q.ior.red.out a τ = some b) (x : ℕ × ℕ) (hx : x.1 < q.base)
    (h : Mg.shown x.1 x.2 (strsOf Fr a.2)) :
    Mg.shown x.1 x.2 (strsOf Fr b.2) := by
  rw [hSig.shown] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, fun y hy hs => (shownAt_rides cs G q a b τ hb y ?_).2 (h2 y hy hs)⟩
  have e : y.1.seat y.2 = (x.1, x.2) := hs
  rw [e]
  exact hx

/-- "No collision" rides there. -/
theorem k6_noColl_rides (H : Seated Wp fld Fr q l bef B bS) (hBl : Blind cs smp decT)
    (a : (P × S) × Fr.E.Str) (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds))
    (b : (P × S) × Fr.E.Str) (hb : q.ior.red.out a τ = some b) (x : ℕ × ℕ) (hx : x.1 < q.base)
    (h : Mg.noColl x.1 x.2 a.1 (strsOf Fr a.2)) :
    Mg.noColl x.1 x.2 b.1 (strsOf Fr b.2) := by
  rw [hSig.noColl] at h ⊢
  intro y hy hs
  have e : y.1.seat y.2 = (x.1, x.2) := hs
  refine ((Sound.rides (Cells := Cells) (Tok := Tok) cs G arr smp q [y] ?_ ?_ a b τ hb y
    (List.mem_singleton.2 rfl)).2).2 (h y hy hs)
  · intro y' hy'
    rw [List.mem_singleton.1 hy', e]
    exact hx
  · intro a' τ' b' hb' y' _
    obtain ⟨o, F1, X, Q, _, _, _, e'⟩ := k6_behind H a' b' τ' hb'
    rw [e', hBl.smp]

end

section
variable (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option Cells) (c₀ : Cells) (ms msT : List Mem)
  (rd6 : (Mem → MsgT) → Cells → Pinned) (Wp : OnBytes.Model.Verify.Public) (fld : Fmt.Fld)
  (Fr : Frame) (tokOf : P × S → Tok) (N : Numbers) (Mg : Meaning P (Wit Cells Tok MsgT))
  (H : First.Blocks S Claim) (links : List ModelPart) (k m : ℕ)

/-- The driver's list of places. -/
local notation "PS" => First.flatPlacesOf links true

/-- **WHAT IS LEFT OF K6's SIDE AT THIS FILLING, BESIDE THE OBJECT AND THE TABLE's OWN TESTS: ONE
FIELD A PREMISE.** ON THE PLAN: plan fenced fence logs · ON THE FILLINGS: blind reads pubSays order
· THE BITS: bits · THE PUBLIC ITEMS BEHIND: pubBehind (eight fields) · THE TIES: t3 t4 t5. A
STRUCTURE THAT COMPILES SAYS NOTHING ON WHETHER ITS FIELDS CAN BE MET TOGETHER. -/
structure K6Bill (q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT)) : Prop where
  /-- two tests on the plan -/
  plan : planB Wp = true
  /-- the trees of what the head reads were sent in front of the piece -/
  fenced : Fenced q.base ms
  /-- so were the trees of every pin that is open in front of it -/
  fence : ∀ x ∈ sampledIn N (openQ links PS k), x.1 < q.base
  logs : ∀ d, d ∈ toRDs q.ds → d.entry.logN ≤ 64
  /-- the samples' reader and the decoder do not read where the chain stands -/
  blind : Blind cs smp decT
  /-- the reader of K6's files (rd6) reads pinned places alone -/
  reads : ReadsPinned cs ms rd6
  /-- three public items give three of K6's files' tests -/
  pubSays : PubSays Wp Mg m
  /-- "in order" does not read where the chain stands -/
  order : ∀ (z : P) (s : S) h, Mg.inOrder (z, { s with here := h }) = Mg.inOrder (z, s)
  /-- every public item that is open behind holds there, as a Bool -/
  pubBehind : ∀ a τ b, onQ (Fr := Fr) N Mg links PS (fun a => a) k a → a.1.2.failed = none →
    q.ior.red.out a τ = some b → K6After Wp b.1.2 →
    ∀ x ∈ pubQ Mg.more links PS (k + 1) ++ pubOfItems (openQ links PS (k + 1)), Mg.pub x b.1 = true
  /-- and as a sentence -/
  pubSentences : ∀ a τ b, onQ (Fr := Fr) N Mg links PS (fun a => a) k a → a.1.2.failed = none →
    q.ior.red.out a τ = some b → K6After Wp b.1.2 →
    ∀ x ∈ pubQ Mg.more links PS (k + 1), Mg.pubP x b.1
  /-- the plan's numbers: the block sends no tree and no message -/
  numbers : N.treesAt PS[k + 1]? = N.treesAt PS[k]? ∧ N.msgsAt PS[k + 1]? = N.msgsAt PS[k]?
  /-- the piece's errors bear the law's prices -/
  bits : ErrBears (_root_.Run.ckP fld)
    (fun j => kitK (toRDs q.ds) j *
      (priceAt (parOf Wp.hS (workOf Wp)) j * kitFs fld (toRDs q.ds) j)) (toRDs q.ds) 0 q.err
  t3 : ∀ a τ b w, onQ (Fr := Fr) N Mg links PS (fun a => a) k a → a.1.2.failed = none →
    q.ior.red.out a τ = some b → K6After Wp b.1.2 →
    relAt (meansQ (Fr := Fr) N Mg fun a => a) (outsQ links PS k) b w →
    relAt (meansK6 cs G arr (fun s => smp (b.1.1, s)) (fun c s => decT c (b.1.1, s)) ms rd6 Wp
      Fr) OutK6 (b.1.2, b.2) w
  t4 : ∀ a τ b w, onQ (Fr := Fr) N Mg links PS (fun a => a) k a → a.1.2.failed = none →
    q.ior.red.out a τ = some b → K6After Wp b.1.2 →
    relAt (meansQ (Fr := Fr) N Mg fun a => a) (outsQ links PS k) b w →
    relAt (meansK6 cs G arr (fun s => smp (a.1.1, s)) (fun c s => decT c (a.1.1, s)) ms rd6 Wp
      Fr) InK6 (a.1.2, a.2) w → relAt (meansQ (Fr := Fr) N Mg fun a => a) (insQ links PS k) a w
  t5 : ∀ a τ b w i, onQ (Fr := Fr) N Mg links PS (fun a => a) k a → a.1.2.failed = none →
    q.ior.red.out a τ = some b → onQ (Fr := Fr) N Mg links PS (fun a => a) (k + 1) b →
    relQ (Fr := Fr) N Mg links PS (fun a => a) (k + 1) b w →
    openAfter (insQ links PS) (outsQ links PS) (· ∈ First.start links) k i → ¬ insQ links PS k i →
    meansQ (Fr := Fr) N Mg (fun a => a) i a w

/-- **`Tied61` AT THE OBJECT, AT THE FILLING OF THE SIX LETTERS ON THE ORACLES.** hfit hs hp':
ON THE TABLE: tests at the list of segments and the door's filling. L: all else that is left. -/
theorem tied61_at_sig (bef : List (ℕ × ℕ)) (n : String) (bS B : Block S Claim)
    (q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT))
    (hO : Object61 Wp fld Fr H links k m bef n bS B q)
    (hfit : pubFit Mg.more links PS = true)
    (hs : links[m]? = some .head)
    (hp' : PS[k + 1]? = some { chain := 1, link := some m, piece := 5, kind := .K1 })
    (hSig : SigFields cs G arr smp msT decT Mg)
    (L : K6Bill cs G arr smp decT ms rd6 Wp fld Fr N Mg links k m q) :
    Tied61 cs G arr smp decT c₀ ms msT rd6 Wp fld Fr tokOf N Mg links k q := by
  have Hs := seated_of_object Wp fld Fr H links k m bef n bS B q hO
  exact tied61_of_object cs G arr smp decT c₀ ms msT rd6 Wp fld Fr tokOf N Mg H links k m bef n bS B
    q hO hfit hs hp' L.numbers L.plan
    L.fenced L.logs L.blind L.reads L.pubSays (blindOrder_sig cs G arr smp decT msT hSig L.order)
    L.pubBehind L.pubSentences L.bits (k6_dec_rides cs G arr smp decT msT hSig Hs L.blind)
    (fun a τ b hb x hx h => k6_shown_rides cs G arr smp decT msT hSig a τ b hb x (L.fence x hx) h)
    (fun a τ b hb x hx h =>
      k6_noColl_rides cs G arr smp decT msT hSig Hs L.blind a τ b hb x (L.fence x hx) h)
    L.t3 L.t4 L.t5

end

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Sound.shownAt_rides
#print axioms VerifiableInference.Desc.Sound.SigFields.eq
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_dec_rides
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_shown_rides
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_noColl_rides
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.tied61_at_sig
