-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/StartAtFiles.lean: THE PROOF FILE'S FIRST TEST ON AN INSTANCE (`FileDescription.okStart` of the IOP as
written in Lean; `ProofFile.okBy`, Johnson/Desc/ProofFile/Pub.lean) ACCEPTS WHAT THE LIBRARY'S MAP WRITES
FOR EVERY INSTANCE OF THE TYPE, AT EVERY OOD SAMPLE, under one condition on the public files. No
relation, no witness and no coin is read. Statements and proofs; nothing is evaluated.

Why. Whoever shows that the verifier accepts an honest run has to pass that test first. It reads no
prover. Here it is cut into what holds by the instance's type, what holds by the OOD sample's type,
and what is a matter of the three public files alone.

THE EIGHT TESTS, AND BY WHAT EACH HOLDS (`okStart_eq` writes the first test out).
- The two files' lengths; the reader of the request and the reply (`Head.stFromCall`); the covered
  positions (`Head.coveredOf`): BY THE TYPE of the instance: `Flat.Req` is the type of «the requests
  that the reader takes» (Johnson/Flat/LedgerClaim.lean), its tokens and positions are bounded by
  type; by the library's `stFromCall_wordsOf`, `coveredOf_wordsOf`; given that the public part's two
  numbers are the type's.
- The words of the OOD seeds, and the shared chain's own test on the table's key (seeds, answers,
  item 0): BY THE TYPE of the OOD sample: what is written of a field's element has its words below
  the prime (the library's `written_okE`, `okKey_instK`).
- The request's item is made; its comparison with the public part (`Verify.statementHeld`); the
  segments' data: THE PUBLIC FILES' MATTER: `StartHeld`.

What is defined.
  **`StartHeld o mk Zp`**: the public part's numbers of tokens and of the vocabulary's entries are
    the type's · at EVERY string of the request file's length the request's item is made and the
    comparison accepts · the segments' data are made.
What is shown.
  `size_bytesOfWords`, `okSeeds_keyOf`, `inst_request`, `inst_reply`, `inst_key`, `okBy_of_tests`:
    pieces.
  **`okBy_of_public`**, **`okStart_of_public`**: under `StartHeld` the test accepts `instanceAsPlainRecord z` at
    every z; the second at the seated IOP's own term (`P5J.F0T`).
  `links_of_pub`: where the public part is made, the segments' data are made: `StartHeld`'s last
    clause.
  `item_of_okBy`: the converse at one instance: an accept gives the two clauses on the item back, at
    that instance's request.
  **`item_free`**: AT THE FORMAT'S EARLIER HASH THE CLAUSE ON THE ITEM HANGS ON THE REQUEST'S LENGTH
    ALONE: by the library's `itemStep_free` (OnBytes/K/ServedFreeItem.lean).
  **`okStart_all_of_one`**: ALL OR NONE: there, where the public part is made and the two numbers
    are the type's: an accept at ONE instance of the type gives an accept at EVERY instance, at
    every OOD sample.

Limits.
- `StartHeld` IS A PREMISE. Its clause on the item is shown here at no public files. In the library
  an accept of `Verify.statementHeld` is concluded from an accept of `verify-on-bytes`'s stage of
  the request alone (OnBytes/K/ExitRequest.lean, ExitFull.lean). That test holds two readers of the
  parameter file against each other, and three digests that must have been made with the same o.
- `item_free` and `okStart_all_of_one` are at the format's second hash function, not at a variable o: the
  library's law spends that this hash's values have 32 bytes.
- The two numbers: the library shows the head's shape's numbers in scope
  (Johnson/Desc/Kinds/Law/TablesPlanInScope.lean); their tie to these two fields is not typed here.
- Nothing on completeness as such, on soundness, or on what a view shows.


-/
import Johnson.Desc.Laid.ProofFull
import Johnson.Flat.CoveredAt
import Johnson.Flat.LayBytes
import OnBytes.K.IdTableSpell
import OnBytes.Maker.OkViewLaws
import Johnson.RunOne.Sound.OkStartAtInstK
import Johnson.P5J.AtTerm
import Johnson.IMR.PureJoin
import Johnson.Desc.ProofFile.Law.PlainMade
import Johnson.Desc.RunLaws
import OnBytes.K.ServedFreeItem
import OnBytes.Tie.Decl.RequestItemLaw

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.Start
open OnBytes OnBytes.Flat OnBytes.Model OnBytes.Slice Inst.Model
open LPFD.Full (instanceAsPlainRecord instPartsOf XF)

/-- **What the first test on an instance asks of the public files alone.** o: the format's second
hash function, as a variable. mk: what computes the segments' data. (tokens, vocab) the public part's
numbers of tokens and of the vocabulary's entries are the instance's type's; (item) at every string
of the request file's length the request's item is made, and the comparison of that item with the
public part accepts; (links) the segments' data are made, at whatever positions a request covers.
-/
structure StartHeld (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Zp : ProofFile.Pub) : Prop where
  tokens : Zp.p.X.T = ppref.T
  vocab : Zp.p.X.P.h.V = ppref.V
  item : ∀ req : ByteArray, req.size = 4 * (Zp.p.X.T + 2) →
    ∃ it, Fmt.requestItem o Zp.pol Zp.KL req = some it ∧ Verify.statementHeld Zp.p.X it = .ok ()
  links : ∀ cov, ∃ ls, mk Zp.p.X cov = .ok ls

theorem size_bytesOfWords (w : Array UInt32) : (bytesOfWords w).size = 4 * w.size := by
  unfold bytesOfWords
  rw [size_catWords, Array.length_toList]

/-- Every word of every OOD seed that is written of a field's elements is below the prime. -/
theorem okSeeds_keyOf {B : Type} (val : B → GE) {v lg s : ℕ} (rec : RecP B v lg s) :
    Maker.okSeeds (keyOf val rec) = true := by
  rw [Maker.okSeeds_iff]
  intro x hx
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  refine ⟨OnBytes.K.IdTable.written_okE _, fun a ha => ?_⟩
  obtain ⟨t, rfl⟩ := (List.mem_ofFn' _ _).1 ha
  exact OnBytes.K.IdTable.written_okE _

/-- The first test, from its seven tests one by one. -/
theorem okBy_of_tests {o : ProofFile.SecondHashFunctionArgument} {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {x : ProofFile.Inst}
    {so : Head.StOwn} {cov : Head.Covered} {it : ByteArray} {ls : Array Stages.LinkH}
    (e1 : (x.pub.request.size % 4 != 0 || x.y.size % 4 != 0) = false)
    (e2 : Head.stFromCall (Verify.words32 x.pub.request) (Verify.words32 x.y) Z.p.X.T = .ok so)
    (e3 : Head.coveredOf so Z.p.X.T Z.p.X.P.h.V = .ok cov)
    (e4 : Fmt.requestItem o Z.pol Z.KL x.pub.request = some it)
    (e5 : Verify.statementHeld Z.p.X it = .ok ()) (e6 : mk Z.p.X cov = .ok ls)
    (e7 : Maker.okSeeds x.pub.key = true) : ProofFile.okBy o mk Z x = true := by
  unfold ProofFile.okBy ProofFile.holdBy
  simp only [e1, e2, e3, e4, e5, e6, e7, ProofFile.held, refuseIf, Except.mapError, bind, Except.bind,
    Option.elim, Bool.false_eq_true, Bool.not_true, if_false, pure, Except.pure]
  rfl

theorem inst_request (z : XF × RecFull) : (instanceAsPlainRecord z).pub.request = requestBytesOf z.1.val := by
  simp only [instanceAsPlainRecord, instPartsOf]

theorem inst_reply (z : XF × RecFull) : (instanceAsPlainRecord z).y = replyBytesOf z.1.val := by
  simp only [instanceAsPlainRecord, instPartsOf]

theorem inst_key (z : XF × RecFull) :
    (instanceAsPlainRecord z).pub.key = keyOf (fun β : NZ => β.val) z.2 := by
  simp only [instanceAsPlainRecord, instPartsOf]

/-- **The first test accepts what is written for every instance of the type**, at every OOD sample:
under `StartHeld`. No relation is read. -/
theorem okBy_of_public {o : ProofFile.SecondHashFunctionArgument} {mk : ProofFile.LinksBy} {Zp : ProofFile.Pub}
    (hS : StartHeld o mk Zp) (z : XF × RecFull) : ProofFile.okBy o mk Zp (instanceAsPlainRecord z) = true := by
  have hT := hS.tokens
  have hV := hS.vocab
  have h32T : ppref.T < 2 ^ 32 := by decide
  have h32V : ppref.V ≤ 2 ^ 32 := by decide
  have hre := z.1.property.1
  have hy := z.1.property.2
  have s1 : (requestBytesOf z.1.val).size = 4 * (ppref.T + 2) := by
    unfold requestBytesOf
    rw [size_bytesOfWords, size_requestWordsOf]
  have s2 : (replyBytesOf z.1.val).size = 4 * 1 := by
    unfold replyBytesOf
    rw [size_bytesOfWords]
    rfl
  have w1 : Verify.words32 (requestBytesOf z.1.val) = requestWordsOf z.1.val :=
    words32_bytesOfWords _
  have w2 : Verify.words32 (replyBytesOf z.1.val) = replyWordsOf z.1.val := words32_bytesOfWords _
  obtain ⟨cov, e3⟩ := coveredOf_wordsOf z.1.val h32T h32V hre
  obtain ⟨it, e4, e5⟩ := hS.item (requestBytesOf z.1.val) (by rw [s1, hT])
  obtain ⟨ls, e6⟩ := hS.links cov
  refine okBy_of_tests
    (so := { req := requestWordsOf z.1.val, r := z.1.val.r, e := z.1.val.e, y := z.1.val.y.val })
    (cov := cov) (it := it) (ls := ls) ?_ ?_ ?_ ?_ e5 e6 ?_
  · rw [inst_request, inst_reply, s1, s2, Nat.mul_mod_right, Nat.mul_mod_right]
    rfl
  · rw [inst_request, inst_reply, w1, w2, hT]
    exact stFromCall_wordsOf z.1.val h32T h32V hre hy
  · rw [hT, hV]
    exact e3
  · rw [inst_request]
    exact e4
  · rw [inst_key]
    exact okSeeds_keyOf _ z.2

/-- The first test of the seated description, written out: the seven tests, and the shared chain's
own test on the table's key. -/
theorem okStart_eq (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain VerifiableInference.Desc.First.S ProofFile.Cl) (x : ProofFile.Inst) :
    (P5J.F0T o Zp Np cF).okStart x = (ProofFile.okBy o ProofFile.pureRoad.links Zp x &&
      _root_.Desc.K14.okKey (_root_.Desc.K14.p14Of Zp.p.chains (_root_.Desc.K14.beforePointOf Np))
        x.pub.key) := rfl

/-- **The proof file's first test accepts what is written for every instance of the type, at every
OOD sample**: at the seated description's own term. -/
theorem okStart_of_public {o : ProofFile.SecondHashFunctionArgument} {Zp : ProofFile.Pub} (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain VerifiableInference.Desc.First.S ProofFile.Cl)
    (hS : StartHeld o ProofFile.pureRoad.links Zp) (z : XF × RecFull) :
    (P5J.F0T o Zp Np cF).okStart (instanceAsPlainRecord z) = true := by
  rw [okStart_eq, okBy_of_public hS z, inst_key, Bool.true_and]
  exact Johnson.RunOne.Sound.okKey_instK _ rfl z.2

/-- **Where the public part is made, the segments' data are made**: they hang on the public part
alone. -/
theorem links_of_pub {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Zp : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Zp) (cov : Head.Covered) :
    ∃ ls, ProofFile.pureRoad.links Zp.p.X cov = .ok ls := by
  obtain ⟨l₀, hl, -⟩ := IM.plain_built (IM.planned_built (ProofFile.Law.pub_planned h))
  exact ⟨l₀, hl⟩

/-- **What an accept of the first test at one instance gives back**: the two clauses on the
request's item, at that instance's request. -/
theorem item_of_okBy {o : ProofFile.SecondHashFunctionArgument} {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {x : ProofFile.Inst}
    (h : ProofFile.okBy o mk Z x = true) :
    ∃ it, Fmt.requestItem o Z.pol Z.KL x.pub.request = some it ∧
      Verify.statementHeld Z.p.X it = .ok () := by
  unfold ProofFile.okBy at h
  cases hG : ProofFile.holdBy o mk Z x with
  | error e => rw [hG] at h; cases h
  | ok G =>
    unfold ProofFile.holdBy at hG
    dsimp only at hG
    obtain ⟨_, -, hG⟩ := VerifiableInference.Desc.bind_eq_ok hG
    obtain ⟨_, -, hG⟩ := VerifiableInference.Desc.bind_eq_ok hG
    obtain ⟨_, -, hG⟩ := VerifiableInference.Desc.bind_eq_ok hG
    obtain ⟨it, h4, hG⟩ := VerifiableInference.Desc.bind_eq_ok hG
    obtain ⟨u, h5, -⟩ := VerifiableInference.Desc.bind_eq_ok hG
    refine ⟨it, ?_, ?_⟩
    · cases hr : Fmt.requestItem o Z.pol Z.KL x.pub.request with
      | none => rw [hr] at h4; cases h4
      | some it' =>
        rw [hr] at h4
        cases h4
        rfl
    · cases hs : Verify.statementHeld Z.p.X it with
      | error e => rw [hs] at h5; cases h5
      | ok v => rfl

/-! ## At the format's second hash function: the clause on the item hangs on the request's length alone -/

/-- **At the format's second hash function the two clauses on the item hold at one request just if at every
request of the same length**: by the library's `itemStep_free`. -/
theorem item_free {X : Verify.Public} {pol KL req req' : ByteArray} (h : req.size = req'.size)
    (h1 : ∃ it, Fmt.requestItem secondHashFunction pol KL req = some it ∧
      Verify.statementHeld X it = .ok ()) :
    ∃ it, Fmt.requestItem secondHashFunction pol KL req' = some it ∧ Verify.statementHeld X it = .ok () := by
  obtain ⟨it, e4, e5⟩ := h1
  have e := OnBytes.K.itemStep_free X pol KL req req' h
  rw [OnBytes.Tie.Decl.RequestItemLaw.requestItem_eq,
    OnBytes.Tie.Decl.RequestItemLaw.requestItem_eq, e4] at e
  cases hr : Fmt.requestItem secondHashFunction pol KL req' with
  | none =>
    rw [hr] at e
    simp only [Verify.named, e5, Except.mapError, bind, Except.bind, pure, Except.pure] at e
    cases e
  | some it' =>
    rw [hr] at e
    refine ⟨it', rfl, ?_⟩
    cases hs : Verify.statementHeld X it' with
    | ok u => rfl
    | error w =>
      simp only [Verify.named, e5, hs, Except.mapError, bind, Except.bind, pure, Except.pure] at e
      cases e

/-- **All or none**: at the format's second hash function, where the public part is made and its number of
tokens and its vocabulary are the type's: if the first test accepts what is written for ONE instance
of the type, it accepts what is written for EVERY instance of the type, at every OOD sample. -/
theorem okStart_all_of_one {pol lay KL : ByteArray} {Zp : ProofFile.Pub} (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain VerifiableInference.Desc.First.S ProofFile.Cl)
    (hp : ProofFile.pureRoad.pub secondHashFunction pol lay KL = .ok Zp) (hT : Zp.p.X.T = ppref.T)
    (hV : Zp.p.X.P.h.V = ppref.V) {z₀ : XF × RecFull}
    (h₀ : (P5J.F0T secondHashFunction Zp Np cF).okStart (instanceAsPlainRecord z₀) = true) (z : XF × RecFull) :
    (P5J.F0T secondHashFunction Zp Np cF).okStart (instanceAsPlainRecord z) = true := by
  rw [okStart_eq, Bool.and_eq_true] at h₀
  have hi := item_of_okBy h₀.1
  rw [inst_request] at hi
  have s0 : (requestBytesOf z₀.1.val).size = 4 * (ppref.T + 2) := by
    unfold requestBytesOf
    rw [size_bytesOfWords, size_requestWordsOf]
  exact okStart_of_public Np cF ⟨hT, hV, fun req hq => item_free (by rw [s0, hq, hT]) hi,
    links_of_pub hp⟩ z

end AtPublicFiles.Start

#print axioms AtPublicFiles.Start.size_bytesOfWords
#print axioms AtPublicFiles.Start.okSeeds_keyOf
#print axioms AtPublicFiles.Start.inst_request
#print axioms AtPublicFiles.Start.inst_reply
#print axioms AtPublicFiles.Start.inst_key
#print axioms AtPublicFiles.Start.okBy_of_tests
#print axioms AtPublicFiles.Start.okBy_of_public
#print axioms AtPublicFiles.Start.okStart_eq
#print axioms AtPublicFiles.Start.okStart_of_public
#print axioms AtPublicFiles.Start.links_of_pub
#print axioms AtPublicFiles.Start.item_of_okBy
#print axioms AtPublicFiles.Start.item_free
#print axioms AtPublicFiles.Start.okStart_all_of_one
