-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.Sound.TiedR
import Johnson.Desc.Sound.ReExt
import Johnson.Desc.Plain.Leads
import Johnson.Desc.Sound.WordsLaw
import Johnson.Desc.K14.Law.LedgerSay
import Johnson.Desc.K12.AtFinish
import Johnson.Desc.K12.Law.BatValsPay
import Johnson.Desc.K12.Law.TupleWords
import Johnson.Desc.K12.Coin.LawN
/-
Johnson/Loose/H2K12/Frame354.lean: THE LAW OF THE PROXIMITY TEST (the kind K12) ON THE
PROOF FILE's FIRST CHAIN, sub-protocol number 354 of the table's written list: THE FRAME's LETTERS.
Definitions and one rule over letters. What is owed there is TiedAtR
(Johnson/Desc/Sound/ChainOfPromisesR.lean): four letters o o' R R', the law GoodIn at them, five ties,
"a mark stays" and "decodes rides". This file fixes the four letters and names what is then left.
THE CHOICE. o := o' := "nothing asked"; R' := "nothing asked"; R a _ := R₀ a, a condition on the
statement in front alone. So the first and the third tie are free, and all the content lies in the
second tie (an accept keeps the table's promise), the fourth (R₀ gives the items that the row closes,
at the extractor's witness) and the fifth (every other open item rides back).
  Tup cs          a tuple of typed messages: one for each member of a sending
  rdTab cs        the one reader of a member's message (tabP, Johnson/Desc/K12/Law/TupleWords.lean)
  Tuple354At, Tuple354   THE MIDDLE OF THE FOURTH TIE: at a state a and strings Y: the door
                  enterFinish lets a in as t; the group under test is G0; there is ONE tuple m of
                  which every row that the test takes in says its claim, and m is a candidate
                  (CandAt, Johnson/Desc/Sound/WordsLaw.lean) at each member of the sendings that mem
                  lays at a member of G0. To the letter the end of core_at
                  (Johnson/Desc/Sound/SeamFacts.lean) at sits := "mem lays it at a member of G0"
  R354            R₀ as it is meant: the door lets the state in, and the game's conclusion QN at
                  NTuple holds there
  T2At, T4aAt, T4bAt, T5At   the second tie; the fourth tie's two halves, which meet at a letter Mid;
                  the fifth tie: the clauses of TiedByR (Johnson/Desc/Sound/TiedR.lean) at the choice,
                  with the extractor's value at an accept written e a b w
  goodIn_of_leads   GoodIn at the choice from Leads (Johnson/Desc/Plain/Leads.lean) at any Q that
                  gives R₀: at any map e laid in as the extractor, since R₀ reads no witness
  tiedByR_of_frame  THE RULE: GoodIn, the four named premises, "a mark stays" and "decodes rides"
                  give TiedByR at the choice
WHAT IT IS NOT. A RULE OVER LETTERS: it pays nothing. It is idle wherever one of its premises cannot be
met: whether T2At, T4aAt, T4bAt and T5At can be met together at the table's meaning and at the picked
condition "reached" is shown nowhere. At Rch := "never" every tie is free and the end says nothing.
No soundness statement. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (KindName Place FileDescription Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start)

/-- A tuple of typed messages: one for each member of a sending. -/
abbrev Tup (cs : OnBytes.Codes) : Type :=
  (x : Mem) → ((Johnson.Pack.sigOf cs x.1.l).om x.2).Msg

/-- The one reader of a member's message. -/
noncomputable def rdTab (cs : OnBytes.Codes) (x : Mem)
    (m : ((Johnson.Pack.sigOf cs x.1.l).om x.2).Msg) (part : OnBytes.Part) (i : ℕ) : OnBytes.Slice.GE :=
  H2K.Pin.tabP cs (x.1.l.get x.2).1 m part i

section
variable (cs : OnBytes.Codes) {Xi P : Type} (G : FileDescription Xi)
  (smp : P × VerifiableInference.Desc.First.S → (s : Sending) → (i : Fin s.l.length) →
    Option ((Johnson.Pack.sigOf cs s.l).om i).Smp)
  (mem : ℕ → Option Mem) (a : P × VerifiableInference.Desc.First.S) (Y : Strs)

/-- **The middle of the fourth tie, with its three witnesses named.** -/
structure Tuple354At (t : VerifiableInference.Desc.K12.T12) (G0 : OnBytes.Group) (m : Tup cs) :
    Prop where
  /-- the door lets the state in -/
  enter : VerifiableInference.Desc.K12.enterFinish a.2 = .ok t
  /-- the group under test -/
  group : t.st.groups[t.g]? = some G0
  /-- every row that the test takes in says its claim of the tuple's words -/
  allSay : OnBytes.Means.AllSay OnBytes.Model.Reading.gl (OnBytes.Slice.begun t.st t.g G0)
    (OnBytes.Slice.runRows t.st G0).toList (_root_.Desc.K14.Law.wordsT cs mem (rdTab cs) m)
  /-- the tuple is a candidate at whatever mem lays at a member of the group -/
  cand : ∀ o ∈ G0.members.toList, ∀ x, mem o = some x → CandAt cs G smp x a Y (m x)

/-- **The middle of the fourth tie.** -/
def Tuple354 : Prop := ∃ t G0 m, Tuple354At cs G smp mem a Y t G0 m

end

/-- **R₀ as it is meant**: the door lets the state in, and the game's conclusion holds there. no: the
numbering of the book's places, which may read what the door returns. -/
def R354 {P : Type} (Fr : Frame) (π : VerifiableInference.Desc.K12.P12)
    (no : VerifiableInference.Desc.K12.T12 → ℕ → ℕ) (rad : OnBytes.Slice.Sg → ℕ) (rdN : ℕ → ℕ)
    (a : (P × VerifiableInference.Desc.First.S) × Fr.E.Str) : Prop :=
  ∃ t, VerifiableInference.Desc.K12.enterFinish a.1.2 = .ok t ∧
    VerifiableInference.Desc.K12.Coin.QN π (H2K.Pin.NTuple Fr π (no t) rad rdN) (t, a.2)

section
variable {Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
  (links : List ModelPart) (ps : List Place)
  (Rch : ℕ → (P × VerifiableInference.Desc.First.S) × Fr.E.Str → Prop) (k : ℕ)
  (q : Piece C Fr (P × VerifiableInference.Desc.First.S) Cl W)
  (e : (P × VerifiableInference.Desc.First.S) × Fr.E.Str →
    (P × VerifiableInference.Desc.First.S) × Fr.E.Str → W → W)
  (R₀ Mid : (P × VerifiableInference.Desc.First.S) × Fr.E.Str → Prop)

/-- **The second tie at the choice**: an accept keeps the table's promise. -/
def T2At : Prop :=
  ∀ a τ b, onQ N Mg links ps (fun a => a) k a → Rch k a → ¬ a.1.2.failed ≠ none →
    q.ior.red.out a τ = some b → onQ N Mg links ps (fun a => a) (k + 1) b

/-- **The fourth tie's first half**: R₀ gives the middle. -/
def T4aAt : Prop :=
  ∀ a τ b, onQ N Mg links ps (fun a => a) k a → Rch k a → ¬ a.1.2.failed ≠ none →
    q.ior.red.out a τ = some b → R₀ a → Mid a

/-- **The fourth tie's second half**: the middle gives the items that the row closes, at the
extractor's witness. -/
def T4bAt : Prop :=
  ∀ a τ b w, onQ N Mg links ps (fun a => a) k a → Rch k a → ¬ a.1.2.failed ≠ none →
    q.ior.red.out a τ = some b → relAt (meansQ N Mg (fun a => a)) (outsQ links ps k) b w →
    Mid a → relAt (meansQ N Mg (fun a => a)) (insQ links ps k) a (e a b w)

/-- **The fifth tie at the choice**: every open item that the row does not close rides back. -/
def T5At : Prop :=
  ∀ a τ b w i, onQ N Mg links ps (fun a => a) k a → Rch k a → ¬ a.1.2.failed ≠ none →
    q.ior.red.out a τ = some b → onQ N Mg links ps (fun a => a) (k + 1) b →
    relQ N Mg links ps (fun a => a) (k + 1) b w →
    openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
    meansQ N Mg (fun a => a) i a (e a b w)

/-- GoodIn at the choice, from Leads at any Q that gives R₀. -/
theorem goodIn_of_leads
    (Q : (P × VerifiableInference.Desc.First.S) × Fr.E.Str →
      (P × VerifiableInference.Desc.First.S) × Fr.E.Str → Prop)
    (hQ : ∀ a b, Q a b → R₀ a) (hL : q.ior.red.Leads (fun _ => True) Q q.err) :
    (q.withMap e).GoodIn (fun _ => True) (fun _ => True) (fun a _ => R₀ a) (fun _ _ => True) :=
  fun a _ => Iop.Doomed.mono _ _ (fun _ hτ b hb => ⟨trivial, fun _ _ => hQ a b (hτ b hb)⟩)
    (hL a trivial)

/-- **The rule.** -/
theorem tiedByR_of_frame
    (hG : (q.withMap e).GoodIn (fun _ => True) (fun _ => True) (fun a _ => R₀ a) (fun _ _ => True))
    (t2 : T2At N Mg links ps Rch k q) (t4a : T4aAt N Mg links ps Rch k q R₀ Mid)
    (t4b : T4bAt N Mg links ps Rch k q e Mid) (t5 : T5At N Mg links ps Rch k q e)
    (hMark : ∀ a τ b, q.ior.red.out a τ = some b → a.1.2.failed ≠ none → b.1.2.failed ≠ none)
    (hDec : ∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes a.1 (strsOf Fr a.2) →
      Mg.decodes b.1 (strsOf Fr b.2)) :
    TiedByR N Mg links ps (fun a => a) Rch k (q.withMap e) (fun _ => True) (fun _ => True)
      (fun a _ => R₀ a) (fun _ _ => True) := by
  refine ⟨hG, fun _ _ _ _ => trivial, fun a τ b ha hr hm hb _ => t2 a τ b ha hr hm hb,
    fun _ _ _ _ _ _ _ _ _ _ => trivial, ?_, ?_, hMark, hDec⟩
  · intro a τ b w ha hr hm hb _ hO hR
    rw [withMap_ext q e a τ b w hb]
    exact t4b a τ b w ha hr hm hb hO (t4a a τ b ha hr hm hb hR)
  · intro a τ b w i ha hr hm hb hon hall hi hin
    rw [withMap_ext q e a τ b w hb]
    exact t5 a τ b w i ha hr hm hb hon hall hi hin

end

end H2K12

#print axioms H2K12.goodIn_of_leads
#print axioms H2K12.tiedByR_of_frame
