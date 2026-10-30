-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/WordsLaw.lean: **WORDS ARE COMMITTED**: THE LAW OF A BLOCK THAT CLOSES PINS, as a
statement in the rule of composition's frame; its plain shadow; the one row from which it follows;
that it follows; and that it is what the rule asks of a block.

The setting. A piece p of a chain (ChainRule.lean) whose block is a test of proximity. mine: the
sampled members (`Mem`, World.lean) whose pins the block closes: sent IN FRONT of the block.
  `Promised mine a y`: THE PROMISE in front of the block: for each of mine `CfAt` (MsgSig.lean): the
    record holds its sample, every leaf is shown, and the library's `OMsg.Clash` does not hold at
    the sample's seed. Where it comes from and how it rides: SendLaw.lean.
  `SeatsFit mine`: the members' seats fit (`SeatFits`): a test on the plan alone. `Fenced p.base
    mine`: THE FENCE: they lie in trees that were sent in front of the block. BOTH ARE PREMISES OF
    ALL THREE STATEMENTS.
  `Pinned mine a y w`: for each of mine `PinAt`: the library's `OMsg.dec` gives the witness's
    message.
  ins: WHAT THE BLOCK's ROW ASKS IN FRONT BESIDE THE PINS: the rows on the group, of the witness's
  messages. on': the promise behind the block. Letters.
  `WordsAreCommitted p mine on on' ins outs`: **THE LAW**: at every statement a inside `on` and the
    promise, outside the rounds' lost sets (p.err, round by round: `Doomed`): where p says yes, with
    the statement b behind: on' b; and where `outs` holds at (b, w): AT THE ROW's EXTRACTOR's VALUE
    (`extAt mine []`, World.lean: w with the members' components, message and pad, set to what they
    decode to) all of mine are pinned AND ins HOLDS.
  `WordsPlain`: ITS PLAIN SHADOW: … where `outs` can be met behind: SOME WITNESS is pinned at all of
    mine and meets ins.
  `CandAt x a y m`, `LaidBy`; `TestGivesCand`: **THE ONE ROW THAT IS OWED**, in the library's own
    terms: …: on' b; and where `outs` holds at (b, w): THERE IS ONE TUPLE OF CANDIDATES (the
    library's `OMsg.Cand`: (α) in the word's list, (β) with the sample's answers), one for each of
    mine, SUCH THAT ins HOLDS OF w WITH THESE LAID.
  `dec_of_cand` (PROVED): inside the promise a member decodes TO ITS CANDIDATE: by the library's
    `sig_dec_good`.
  `words_of_cand` (PROVED): if no two of mine have one number, `TestGivesCand` gives
    `WordsAreCommitted`.
  `plain_of_words` (PROVED): the law gives its shadow.
  `goodIn_of_words` (PROVED): THE LAW IS `Piece.GoodIn` (GoodIn.lean: what the rule of composition
    asks of a block), where the piece's extractor is the row's WHEREVER ITS BLOCK SAYS YES.
WHO IS NO MEMBER. (1) A MESSAGE WITHOUT A SAMPLE (a fold's fresh mask; a masking word): nobody
spends "its word is near the code": the library's law of a batching with a fold takes the mask as
any word that is fixed before the fold's first draw (Johnson/Top/H/BatFold.lean; `Rels.keepE`,
Ior/Frame.lean: the further oracle is read in neither relation nor condition). So no boundary's
relation speaks of it. (2) A MESSAGE THAT IS SENT, SAMPLED AND CLOSED INSIDE ONE PIECE: its pin is
open at no boundary: it is the matter of that block's own lemma. THE THREE PRICED EVENTS. (γ) a
collision at a sample's seed: priced at the sending (SendLaw.lean); here it is shut out by the
promise. (α), (β): priced in p.err, at the test's own rounds. That a block's reads are the strings'
values is exact (`readsAreStrings`, ReadsAre.lean). SILLY MEMBERS (BY ARGUMENT: none is typed). A
block that says yes to all fails the law wherever a statement inside `on` and the promise has a word
without a candidate (a word far from the code has an empty list, so no collision: it is inside the
promise), outs can be met behind, and every entry of p.err is below its round's number of
challenges. mine := []: the law is `on' b` and `outs b w → ins a w`. outs := False: the law is `on'
b`.
Limits. The law is stated at a row that lays neither the cells nor the token. `smp`, `decT` are
letters (`smp`: meant as `smpOf forms ans`, Seed.lean). NOTHING IS PROVED OF ANY BLOCK.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.World
import Johnson.Desc.Sound.GoodIn
import Cb.Ld.LdSigProofs

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

/-- **The promise in front of the block**: for each member: its sample is held, every leaf is shown,
no collision at the seed. -/
def Promised (mine : List Mem) (a : A) (y : Strs) : Prop :=
  ∀ x ∈ mine, CfAt G cs x.1.l x.1.seat (fun z => smp z x.1) x.2 a y

/-- The seats of these members fit: a test on the plan alone. -/
def SeatsFit (ms : List Mem) : Prop := ∀ x ∈ ms, SeatFits G cs x.1.l x.1.seat

/-- Each member is pinned. -/
def Pinned (mine : List Mem) (a : A) (y : Strs) (w : Wit Cells Tok MsgT) : Prop :=
  ∀ x ∈ mine, PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 a y w

/-- The message m is a candidate of the member x: it is in its word's list and has the answers of
the sample which the record holds. -/
def CandAt (x : Mem) (a : A) (y : Strs) (m : ((sigOf cs x.1.l).om x.2).Msg) : Prop :=
  ∃ z, smp a x.1 x.2 = some z ∧
    ((sigOf cs x.1.l).om x.2).Cand (wordsOf G cs x.1.l x.1.seat y x.2) z m

/-- w' is w with the members' components (the message by its number, and the seat's pad) laid from
the tuple of messages c, and nothing else turned. -/
def LaidBy (mine : List Mem) (c : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg)
    (w w' : Wit Cells Tok MsgT) : Prop :=
  w'.cells = w.cells ∧ w'.tok = w.tok ∧
    (∀ x ∈ mine, w'.msg (numOf arr x) = toMsgT cs x.1.l x.2 (c x)) ∧
    (∀ n, n ∉ mine.map (numOf arr) → w'.msg n = w.msg n) ∧
    (∀ x ∈ mine, w'.pad (x.1.seat x.2).1 (x.1.seat x.2).2 = toMsgT cs x.1.l x.2 (c x)) ∧
    ∀ j t, (j, t) ∉ mine.map seatOf → w'.pad j t = w.pad j t

variable (decT : (ℕ → Option (ℕ × List UInt64)) → A → Option Cells) (c₀ : Cells)
  {C : CK} {Fr : Frame} {Cl : Type}

/-- **The fence**: every member lies in a tree that was sent in front of the block. (A stage never
reads the strings in front of it at a tree from its own base on: of a tree that the block's own
stretch sends the strings in front say nothing; behind any earlier piece such a tree is empty.) -/
def Fenced (base : ℕ) (ms : List Mem) : Prop := ∀ x ∈ ms, (x.1.seat x.2).1 < base

/-- Each of these members' trees is one that the piece's own stretch sends. -/
def SentBy {W : Type} (p : Piece C Fr A Cl W) (ms : List Mem) : Prop :=
  ∀ x ∈ ms, ∃ n sh, (x.1.seat x.2).1 = p.base + n ∧ treeShT p.ds n = some sh

/-- **WORDS ARE COMMITTED: the law of a block that closes pins.** ins: what the block's row asks in
front beside the pins (the rows on the group). on': the promise behind the block. -/
def WordsAreCommitted (p : Piece C Fr A Cl (Wit Cells Tok MsgT)) (mine : List Mem)
    (on on' : A × Fr.E.Str → Prop) (ins outs : A × Fr.E.Str → Wit Cells Tok MsgT → Prop) : Prop :=
  SeatsFit cs G mine → Fenced p.base mine →
    ∀ a, on a → Promised cs G smp mine a.1 (strsOf Fr a.2) →
    Doomed (uLT C p.ds) p.err fun τ => ∀ b, p.ior.red.out a τ = some b → on' b ∧ ∀ w, outs b w →
      Pinned cs G arr smp mine a.1 (strsOf Fr a.2)
          (extAt cs G arr smp decT c₀ mine [] false none a.1 (strsOf Fr a.2) w) ∧
        ins a (extAt cs G arr smp decT c₀ mine [] false none a.1 (strsOf Fr a.2) w)

/-- Its plain shadow: of some witness. -/
def WordsPlain (p : Piece C Fr A Cl (Wit Cells Tok MsgT)) (mine : List Mem)
    (on on' : A × Fr.E.Str → Prop) (ins outs : A × Fr.E.Str → Wit Cells Tok MsgT → Prop) : Prop :=
  SeatsFit cs G mine → Fenced p.base mine →
    ∀ a, on a → Promised cs G smp mine a.1 (strsOf Fr a.2) →
    Doomed (uLT C p.ds) p.err fun τ => ∀ b, p.ior.red.out a τ = some b → on' b ∧
      ((∃ w, outs b w) →
        ∃ w : Wit Cells Tok MsgT, Pinned cs G arr smp mine a.1 (strsOf Fr a.2) w ∧ ins a w)

/-- **The one row that is owed**, in the library's own terms: the promise behind is kept, and THERE
IS ONE TUPLE OF CANDIDATES OF WHICH THE ROW's ins HOLD. -/
def TestGivesCand (p : Piece C Fr A Cl (Wit Cells Tok MsgT)) (mine : List Mem)
    (on on' : A × Fr.E.Str → Prop) (ins outs : A × Fr.E.Str → Wit Cells Tok MsgT → Prop) : Prop :=
  SeatsFit cs G mine → Fenced p.base mine →
    ∀ a, on a → Promised cs G smp mine a.1 (strsOf Fr a.2) →
    Doomed (uLT C p.ds) p.err fun τ => ∀ b, p.ior.red.out a τ = some b → on' b ∧ ∀ w, outs b w →
      ∃ c : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg,
        (∀ x ∈ mine, CandAt cs G smp x a.1 (strsOf Fr a.2) (c x)) ∧
          ∀ w', LaidBy cs arr mine c w w' → ins a w'

theorem agree_of_nodup (mine : List Mem) (h : (mine.map (numOf arr)).Nodup) (a : A) (y : Strs)
    (n : ℕ) : Agree cs G arr smp mine a y n := by
  intro x hx x' hx' e e' m m' hm hm'
  have ex : x = x' := List.inj_on_of_nodup_map h hx hx' (e.trans e'.symm)
  subst ex
  exact Option.some.inj (hm.symm.trans hm')

/-- No two with one number: so no two at one seat. -/
theorem agreeSeat_of_nodup (mine : List Mem) (h : (mine.map (numOf arr)).Nodup) (a : A) (y : Strs)
    (k : ℕ × ℕ) : AgreeBy cs G smp seatOf mine a y k := by
  intro x hx x' hx' e e' m m' hm hm'
  have es : seatOf x = seatOf x' := e.trans e'.symm
  have en : numOf arr x = numOf arr x' := congrArg (fun s : ℕ × ℕ => arr s.1 s.2) es
  have ex : x = x' := List.inj_on_of_nodup_map h hx hx' en
  subst ex
  exact Option.some.inj (hm.symm.trans hm')

/-- **Inside the promise a member decodes to its candidate**: by the library's `sig_dec_good`: at a
seed without a collision the decoder returns m just where m is a candidate. -/
theorem dec_of_cand (x : Mem) (a : A) (y : Strs) (m : ((sigOf cs x.1.l).om x.2).Msg)
    (hp : CfAt G cs x.1.l x.1.seat (fun z => smp z x.1) x.2 a y) (hc : CandAt cs G smp x a y m) :
    decAt cs G smp x.1 x.2 a y = some (toMsgT cs x.1.l x.2 m) := by
  obtain ⟨z, hz, hs, hn⟩ := hp
  obtain ⟨z', hz', hm⟩ := hc
  have ez : z' = z := Option.some.inj (hz'.symm.trans hz)
  subst ez
  have hd : ((sigOf cs x.1.l).om x.2).dec (wordsOf G cs x.1.l x.1.seat y x.2) z' = some m :=
    (sig_dec_good GE _ _ z'.1 hn z'.2 m).2 hm
  unfold decAt
  rw [hz', Option.bind_some, if_pos hs, hd]
  rfl

/-- **From the candidates to the law.** -/
theorem words_of_cand (p : Piece C Fr A Cl (Wit Cells Tok MsgT)) (mine : List Mem)
    (on on' : A × Fr.E.Str → Prop) (ins outs : A × Fr.E.Str → Wit Cells Tok MsgT → Prop)
    (hN : (mine.map (numOf arr)).Nodup) (h : TestGivesCand cs G arr smp p mine on on' ins outs) :
    WordsAreCommitted cs G arr smp decT c₀ p mine on on' ins outs := by
  intro hS hF a ha hp
  refine Doomed.mono _ _ (fun τ hτ b hb => ⟨(hτ b hb).1, fun w hw => ?_⟩) (h hS hF a ha hp)
  obtain ⟨c, h1, h2⟩ := (hτ b hb).2 w hw
  have hd : ∀ x ∈ mine, decAt cs G smp x.1 x.2 a.1 (strsOf Fr a.2) =
      some (toMsgT cs x.1.l x.2 (c x)) := fun x hx =>
    dec_of_cand cs G smp x a.1 (strsOf Fr a.2) (c x) (hp x hx) (h1 x hx)
  have hA := fun n => agree_of_nodup cs G arr smp mine hN a.1 (strsOf Fr a.2) n
  have hB : ∀ k, AgreeBy cs G smp seatOf (mine ++ []) a.1 (strsOf Fr a.2) k := fun k => by
    rw [List.append_nil]
    exact agreeSeat_of_nodup cs G arr smp mine hN a.1 (strsOf Fr a.2) k
  refine ⟨fun x hx => pin_ext cs G arr smp decT c₀ mine [] false none a.1 (strsOf Fr a.2) w x hx _
    (hd x hx) (hA _) (hB _), h2 _ ⟨rfl, rfl, fun x hx => ?_, fun n hn => ?_, fun x hx => ?_,
      fun j t hn => ?_⟩⟩
  · show (if numOf arr x ∈ mine.map (numOf arr) then
      msgAt cs G arr smp mine a.1 (strsOf Fr a.2) (numOf arr x) else w.msg (numOf arr x)) = _
    rw [if_pos (List.mem_map.2 ⟨x, hx, rfl⟩),
      msgAt_of cs G arr smp mine a.1 (strsOf Fr a.2) x hx _ (hd x hx) (hA _)]
  · exact extAt_other cs G arr smp decT c₀ mine [] false none a.1 (strsOf Fr a.2) w n hn
  · show (if ((x.1.seat x.2).1, (x.1.seat x.2).2) ∈ (mine ++ []).map seatOf then
      padAt cs G smp (mine ++ []) a.1 (strsOf Fr a.2) (x.1.seat x.2).1 (x.1.seat x.2).2
      else w.pad (x.1.seat x.2).1 (x.1.seat x.2).2) = _
    have h1 : ((x.1.seat x.2).1, (x.1.seat x.2).2) ∈ (mine ++ []).map seatOf :=
      List.mem_map.2 ⟨x, List.mem_append_left _ hx, rfl⟩
    rw [if_pos h1]
    exact tabBy_of cs G smp seatOf (mine ++ []) a.1 (strsOf Fr a.2) x (List.mem_append_left _ hx) _
      (hd x hx) (hB _)
  · exact extAt_other_pad cs G arr smp decT c₀ mine [] false none a.1 (strsOf Fr a.2) w j t
      (by rw [List.append_nil]; exact hn)

/-- **The law gives its shadow.** -/
theorem plain_of_words (p : Piece C Fr A Cl (Wit Cells Tok MsgT)) (mine : List Mem)
    (on on' : A × Fr.E.Str → Prop) (ins outs : A × Fr.E.Str → Wit Cells Tok MsgT → Prop)
    (h : WordsAreCommitted cs G arr smp decT c₀ p mine on on' ins outs) :
    WordsPlain cs G arr smp p mine on on' ins outs := by
  intro hS hF a ha hp
  refine Doomed.mono _ _ (fun τ hτ b hb => ⟨(hτ b hb).1, fun hw => ?_⟩) (h hS hF a ha hp)
  obtain ⟨w, hw⟩ := hw
  exact ⟨_, (hτ b hb).2 w hw⟩

/-- **THE LAW IS WHAT THE RULE OF COMPOSITION ASKS OF A BLOCK** (`Piece.GoodIn`, GoodIn.lean): where
the seats fit, the members are fenced and the piece's extractor is the row's: between (`on` with the
promise) and on', and between (the pins with ins) and outs. -/
theorem goodIn_of_words (p : Piece C Fr A Cl (Wit Cells Tok MsgT)) (mine : List Mem)
    (on on' : A × Fr.E.Str → Prop) (ins outs : A × Fr.E.Str → Wit Cells Tok MsgT → Prop)
    (hS : SeatsFit cs G mine) (hF : Fenced p.base mine)
    (hx : ∀ a τ b w, p.ior.red.out a τ = some b → p.ext a τ w =
      extAt cs G arr smp decT c₀ mine [] false none a.1 (strsOf Fr a.2) w)
    (h : WordsAreCommitted cs G arr smp decT c₀ p mine on on' ins outs) :
    p.GoodIn (fun a => on a ∧ Promised cs G smp mine a.1 (strsOf Fr a.2)) on'
      (fun a w => Pinned cs G arr smp mine a.1 (strsOf Fr a.2) w ∧ ins a w) outs := by
  intro a ha
  refine Doomed.mono _ _ (fun τ hτ b hb => ⟨(hτ b hb).1, fun w hw => ?_⟩) (h hS hF a ha.1 ha.2)
  rw [hx a τ b w hb]
  exact (hτ b hb).2 w hw

end

end VerifiableInference.Desc.Sound
