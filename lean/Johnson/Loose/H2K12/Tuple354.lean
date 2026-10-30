-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.Frame354
import Johnson.Loose.H2K12.Promise354
import Johnson.Desc.K12.Coin.TupleOfMembers
import Johnson.Desc.K12.Coin.HeldYes
/-
Johnson/Loose/H2K12/Tuple354.lean: THE LAW OF THE PROXIMITY TEST (the kind K12) ON THE
PROOF FILE's FIRST CHAIN, sub-protocol number 354 of the table of joints: THE FOURTH TIE's FIRST HALF
(`T4aAt`, H2K12/Frame354.lean): inside the table's promise, at a reached state without a mark, at an
accept of the file's own piece, the game's conclusion gives ONE TUPLE OF TYPED MESSAGES of which every
row that the test takes in says its claim, a candidate at each member of the group under test.
Statements and proofs: calls. STATED GENERAL IN THE BORDER's NUMBER k AND IN THE GROUP's MEMBERS. At the
full size the tenants whose pin is open at 354 are ONE seat, (76, 0): the statement's message number 185
(the witness's number 149), by evaluations at the stored files: so "each member" is there one member;
nothing here reads that.
  `qw_of_accept`: an accept of a piece that holds a sub-protocol sitting on the kind's, with the
    game's conclusion at the state in front ⊢ the relation QW (Johnson/Desc/K12/Coin/GameOut.lean); and
    the first fold's mask has come (`mask_of_yes`, MaskOfYes.lean).
  `tuple_354`: `T4aAt` at R₀ := `R354` at the numbering by labels from 0 and Mid := `Tuple354`.
  `tuple_354_memOf`: the same at mem := `memOf ms d.L.places`: a term.
WHO SAYS WHAT. The stand "at the finish": R₀'s own door · the mask: the accept · which messages are
members, where they sit, that their leaves are shown: the table's promise (H2K12/Promise354.lean) ·
the book in order, the seats carried, "tidy", the codes, THE FRAME's GROUP AT THE FINISH, THE SENDINGS'
INVARIANT AT THE MEMBERS: `FactsK12`, from "reached" · all else: `PublicK12` and three equations on the
letters Mg.shown, smp, mem.
What it is not. EVERY PREMISE IS A PREMISE. `FactsK12`'s last two fields have no payer; `PublicK12`
is shown at no list of rounds. No example. The tie's second half (from the tuple to the items that the
row closes, at the extractor's witness) is another file's. No soundness is claimed. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12
open OnBytes OnBytes.Slice OnBytes.Maker Johnson.Pack
open _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Coin (QW QN nuOf nlAt MemberAt tuple_of_members yes_step
  step_of_held step_decide mask_of_yes)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers openSets start)
open H2K.JointK (Sits)
open H2K.Pin (NTuple)

/-- **An accept of the file's own piece, with the game's conclusion in front, is QW; and the mask has
come.** -/
theorem qw_of_accept {P S Cl W : Type} {Fr : Frame} (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ)
    (rdN : ℕ → ℕ) (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (B : Block S Cl) (hS : Sits B (proximityTestKind guardedProximityTestParts π : Block T12 Unit) enter leave)
    (q : Piece (ckP .two) Fr (P × S) Cl W) (hb : q.b = held (P := P) B) (h0 : q.back = [])
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (ho : π.nums.ownMask = false)
    (a b : (P × S) × Fr.E.Str) (τ : Iop.Tr (uLT (ckP .two) q.ds))
    (hout : q.ior.red.out a τ = some b)
    (hR : ∃ t, enter a.1.2 = .ok t ∧
      QN π (NTuple Fr π (nuOf π nl t) (fun s => r s.st) rdN) (t, a.2)) :
    QW Fr π nl r rdN enter leave a b ∧ ∀ t, enter a.1.2 = .ok t → t.mask.isSome = true := by
  obtain ⟨_, k, hst, _⟩ := yes_step q h0 a τ b hout
  rw [hb] at hst
  obtain ⟨h1, _⟩ := step_of_held B Fr.ft a.1 b.1 _ _ k hst
  obtain ⟨t, t', e1, e2, e3⟩ := hS.step Fr.ft _ _ _ _ k h1
  obtain ⟨gs, hd⟩ := step_decide _ Fr.ft t t' _ _ k e2
  obtain ⟨t₀, ht₀, hq⟩ := hR
  obtain rfl : t₀ = t := Except.ok.inj (ht₀.symm.trans e1)
  refine ⟨⟨t₀, t', e1, e3, hq, _, gs, hd⟩, fun t₁ ht₁ => ?_⟩
  obtain rfl : t₁ = t₀ := Except.ok.inj (ht₁.symm.trans e1)
  exact mask_of_yes π hp ho t₁ t' Fr.ft k _ _ e2

/-- **THE FOURTH TIE's FIRST HALF.** -/
theorem tuple_354 {P Cl W Xi : Type} {Fr : Frame} (cs : Codes) (G : FileDescription Xi) (π : P12)
    (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ) (d : First.FoldData)
    (smp : P × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (mem : ℕ → Option Mem) (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (ps : List Place) (Rch : ℕ → (P × First.S) × Fr.E.Str → Prop) (k : ℕ)
    (q : Piece (ckP .two) Fr (P × First.S) Cl W) (B : Block First.S Cl)
    (leave : First.S → T12 → Except String First.S) (hb : q.b = held (P := P) B)
    (h0 : q.back = []) (hS : Sits B (proximityTestKind guardedProximityTestParts π : Block T12 Unit) enterFinish leave)
    (hP : PublicK12 cs G Fr π r d N links.length ((openSets links ps (start links))[k]?.getD [])
      ms)
    (hsh : Mg.shown = shownJT cs G ms)
    (hsmp : ∀ a o x, ListedAt ms d.L.places o x →
      smp a x.1 x.2 = K1.smpAt cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 a.2.st o)
    (hmem : ∀ o x, ListedAt ms d.L.places o x → mem o = some x)
    (hF : ∀ a, Rch k a → a.1.2.failed = none → FactsK12 d N links.length cs ms a.1.2) :
    T4aAt N Mg links ps Rch k q
      (R354 Fr π (fun t => nuOf π (nlAt π 0) t) (fun s => r s.st) rdN)
      (fun a => Tuple354 cs G smp mem a.1 (strsOf Fr a.2)) := by
  intro a τ b hon hR hm hout hq
  have hm0 : a.1.2.failed = none := Classical.not_not.1 hm
  have F := hF a hR hm0
  obtain ⟨hQW, hmask⟩ := qw_of_accept π (nlAt π 0) r rdN enterFinish leave B hS q hb h0 hP.plan
    hP.own a b τ hout hq
  have key : ∀ t, enterFinish a.1.2 = .ok t →
      t.st = a.1.2.st ∧ t.book = a.1.2.book ∧ t.g = N.groupAt links.length := by
    intro t ht
    obtain ⟨o, ho, _, _, rfl⟩ := VerifiableInference.Desc.K12.Seat.enterFinish_ok a.1.2 t ht
    exact ⟨rfl, rfl, F.groupAtFinish o ho⟩
  obtain ⟨t, G0, ht, hG, m, hall, hc⟩ := tuple_of_members cs G Fr π 0 d.ft r rdN smp mem (rdTab cs)
    (fun _ _ _ _ => rfl) enterFinish leave a b a.1 hQW hP.joh hP.plan hP.first
    (ListedAt ms d.L.places) (fun _ _ _ h h' => ListedAt.inj hP.placesOnce h h')
    (fun t ht => by rw [(key t ht).1]; exact F.codes.trans hP.codes)
    (fun t ht => by rw [(key t ht).1]; exact (OnBytes.Means.tidy4B_iff.1 F.tidy).inOrder)
    (fun t ht => by rw [(key t ht).2.1]; exact bookOrd_of d.ft a.1.2 F.bookInOrder)
    hmask
    (fun t G0 ht hG o ho => by
      obtain ⟨e1, e2, e3⟩ := key t ht
      rw [e1, e3] at hG
      obtain ⟨x, hL, hpl, hpin, hshown⟩ := member_listed cs G N Mg links ps ms d.L links.length k a
        hon hm0 hsh hP.rowOpen F.seatsCarried G0 hG o ho
      obtain ⟨hpub, htold⟩ := hP.member x hL.1 hpin
      refine ⟨x, hL, hpub, by rw [e1]; exact F.seedIs G0 hG o ho x hL,
        by rw [e1]; exact hsmp a.1 o x hL, hmem o x hL,
        ⟨seatOf x, by rw [e2]; exact hpl, ?_, fun u hu T hT => ?_⟩, hshown⟩
      · show x.1.seat x.2 = (0 + (x.1.seat x.2).1, (x.1.seat x.2).2)
        rw [Nat.zero_add]
      · rw [e2] at hT
        exact htold u T.shape hu (tree_listed d.L a.1.2 F.seatsCarried _ T hT))
  exact ⟨t, G0, m, ht, hG, hall, hc⟩

/-- **The same with the laying of numbers onto members a term** (`memOf`, H2K12/Promise354.lean): the
premise on the letter mem is gone. -/
theorem tuple_354_memOf {P Cl W Xi : Type} {Fr : Frame} (cs : Codes) (G : FileDescription Xi) (π : P12)
    (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ) (d : First.FoldData)
    (smp : P × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (ps : List Place) (Rch : ℕ → (P × First.S) × Fr.E.Str → Prop) (k : ℕ)
    (q : Piece (ckP .two) Fr (P × First.S) Cl W) (B : Block First.S Cl)
    (leave : First.S → T12 → Except String First.S) (hb : q.b = held (P := P) B)
    (h0 : q.back = []) (hS : Sits B (proximityTestKind guardedProximityTestParts π : Block T12 Unit) enterFinish leave)
    (hP : PublicK12 cs G Fr π r d N links.length ((openSets links ps (start links))[k]?.getD [])
      ms)
    (hsh : Mg.shown = shownJT cs G ms)
    (hsmp : ∀ a o x, ListedAt ms d.L.places o x →
      smp a x.1 x.2 = K1.smpAt cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 a.2.st o)
    (hF : ∀ a, Rch k a → a.1.2.failed = none → FactsK12 d N links.length cs ms a.1.2) :
    T4aAt N Mg links ps Rch k q
      (R354 Fr π (fun t => nuOf π (nlAt π 0) t) (fun s => r s.st) rdN)
      (fun a => Tuple354 cs G smp (memOf ms d.L.places) a.1 (strsOf Fr a.2)) :=
  tuple_354 cs G π r rdN d smp ms (memOf ms d.L.places) N Mg links ps Rch k q B leave hb h0 hS hP hsh
    hsmp (fun _ _ h => memOf_listed hP.seatsOnce h) hF

end H2K12

#print axioms H2K12.tuple_354_memOf
#print axioms H2K12.qw_of_accept
#print axioms H2K12.tuple_354
