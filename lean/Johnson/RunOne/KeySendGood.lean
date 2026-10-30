-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeySendGood.lean: THEOREMS. **The law of a sending (send_goodIn) at the three sendings of a key file's first
chain, with the conditions and relations at the two borders left as letters**, so that any frame can lay its own.
  dsOf_one_seed     the draws of a round that draws c + 1 elements, one of them other than 0, no position and no matrix entry, and is no sealing: c elements,
                    then one element other than 0, then an empty draw of matrix entries: whatever the round's kind otherwise is
  SeedRound         a written round is a sending's round of seeds: its entry is the kind's own (seedEntry), and its kind is no sealing
  five_of_seedRound at one seed, such a round has the five things that send_goodIn asks of the first written round
  planOwn_idxAt | planOwn_msgAt | planOwn_wAt   the joined block's test on the plan holds the kind's own test on the plan
  cond_of           the law's one Boolean from its three clauses
  Pays              what a block brings to the law: the kind's own test on the plan, and IsSend
  idx_pays | msg_pays | w_pays   the three joined blocks bring it, where their own test on the plan says yes
  sendGood          send_goodIn with the five paid by SeedRound, and its Boolean and IsSend by Pays and two clauses on the codes
What is not claimed. LEFT AS PREMISES at each place: the joined block's own test on the plan says yes (idx_pays | msg_pays | w_pays) · the first written round is the round of seeds (SeedRound P d₁) · one seed (proved elsewhere from the fold's yes) ·
the codes' lengths are powers of two · every sampled
message meets the library's test at its radius (meetsB) · the written count bears the number of bad seeds (errPort ≤ e) · the words' family and that it reads
the first round's message alone (A CONSTANT FAMILY MEETS THAT PREMISE: then «Sealed» seals a word that nobody sent, and the law holds and says nothing: THE DEBT OF WHOEVER SPENDS Sealed: fOf y k IS the frame's reading, in the strings y, of the oracle
message number «size − length + k») · the condition in front gives that behind · a witness behind is one in front · that the frame's piece at the seat is sendPiece.
Whether meetsB holds at the real codes and a frame's radii is a matter of evaluation, not settled here. Nothing on soundness.

-/
import Johnson.RunOne.KeySendIs

set_option autoImplicit false

namespace Johnson.RunOne.KeySendGood

open OnBytes OnBytes.Params VerifiableInference.Desc.Key Johnson.RunOne.KeyKeeps
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice
open Johnson.Pack Cb Cb.Ood
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.K1 (Par IsSend seedEntry planOkOwn condPort errPort sendPiece send_goodIn Sealed shapeAt shapesOf sampledAt)

/-! ## The draws of a round of one seed -/

theorem dsOf_one_seed (e : Fmt.Entry) (k : Fmt.Kind) (c : Nat) (hp : e.poss = 0) (ht : e.trits = 0) (hE : e.drawE = c + 1) (hN : e.drawNZ = 1)
    (hk : k ≠ .sealed) : Fmt.dsOf e k = List.replicate c Fmt.Draw.elem ++ [Fmt.Draw.elemNZ, Fmt.Draw.trits 0] := by
  unfold Fmt.dsOf Fmt.dsElems Fmt.dsSeeds
  rw [hp, ht, hE, hN, if_neg hk]
  by_cases h : k = .seeds
  · rw [if_pos h]
    simp [Nat.mod_one]
  · rw [if_neg h]
    simp

theorem plain_rep : ∀ c : Nat, PlainDraws (List.replicate c Fmt.Draw.elem ++ [Fmt.Draw.elemNZ, Fmt.Draw.trits 0])
  | 0 => ⟨rfl, trivial⟩
  | c + 1 => plain_rep c

theorem nE_rep : ∀ c : Nat, nE (List.replicate c Fmt.Draw.elem ++ [Fmt.Draw.elemNZ, Fmt.Draw.trits 0]) = c + 1
  | 0 => rfl
  | c + 1 => congrArg (· + 1) (nE_rep c)

theorem nP_rep : ∀ c : Nat, nP (List.replicate c Fmt.Draw.elem ++ [Fmt.Draw.elemNZ, Fmt.Draw.trits 0]) = 0
  | 0 => rfl
  | c + 1 => nP_rep c

theorem isNZ_rep : ∀ c : Nat, IsNZ (List.replicate c Fmt.Draw.elem ++ [Fmt.Draw.elemNZ, Fmt.Draw.trits 0]) c
  | 0 => trivial
  | c + 1 => isNZ_rep c

/-- A written round is a sending's round of seeds. -/
structure SeedRound (P : Par) (d : RDT) : Prop where
  entry : d.entry = seedEntry P
  kind : d.kind ≠ .sealed

/-- **At one seed the round of seeds has what the law asks of the first written round.** -/
theorem five_of_seedRound (P : Par) (h1 : P.seeds = 1) (d : RDT) (h : SeedRound P d) :
    PlainDraws (Fmt.dsOf d.entry d.kind) ∧ nE (Fmt.dsOf d.entry d.kind) = P.coordinates + 1 ∧ nP (Fmt.dsOf d.entry d.kind) = 0 ∧
      IsNZ (Fmt.dsOf d.entry d.kind) P.coordinates ∧ d.entry.logN ≤ 64 := by
  have hd : Fmt.dsOf d.entry d.kind = List.replicate P.coordinates Fmt.Draw.elem ++ [Fmt.Draw.elemNZ, Fmt.Draw.trits 0] := by
    refine dsOf_one_seed d.entry d.kind P.coordinates ?_ ?_ ?_ ?_ h.kind
    · rw [h.entry]; rfl
    · rw [h.entry]; rfl
    · rw [h.entry]; show P.seeds * (P.coordinates + 1) = _; rw [h1, Nat.one_mul]
    · rw [h.entry]; exact h1
  rw [hd]
  refine ⟨plain_rep _, nE_rep _, nP_rep _, isNZ_rep _, ?_⟩
  rw [h.entry]
  exact Nat.zero_le _

/-! ## The test on the plan -/

variable {β Cl : Type}

theorem planOwn_idxAt (one : OneTime) (N : Pieces) (groups : List (List Nat)) (h : (sendIndexMasks (β := β) (Cl := Cl) one N groups).planOk = true) :
    planOkOwn (sendingPar one N.idx "the index masks" #[one.indexMasks] groups) = true := by
  have h' : (planOkOwn (sendingPar one N.idx "the index masks" #[one.indexMasks] groups) && true) = true := h
  simpa using h'

theorem planOwn_msgAt (one : OneTime) (N : Pieces) (groups : List (List Nat)) (h : (sendOwnMessage (β := β) (Cl := Cl) one N groups).planOk = true) :
    planOkOwn (sendingPar one N.msg "the lookups' own message and what rides with it" (Wf.messageOf one.ranges) groups) = true := by
  have h' : (planOkOwn (sendingPar one N.msg "the lookups' own message and what rides with it" (Wf.messageOf one.ranges) groups) && true) = true := h
  simpa using h'

theorem planOwn_wAt {one : OneTime} {N : Pieces} {sent : Nat} {groups : List (List Nat)} {bw : Block (ChainState β) Cl} {msg : Array OracleNotice}
    (hm : linMessageW one.lin = some msg) (hb : sendW one N sent groups = some bw) (h : bw.planOk = true) :
    planOkOwn (sendingPar one N.w "W and what rides with it" msg groups) = true := by
  unfold sendW at hb
  rw [hm] at hb
  have hb' := Option.some.inj hb
  rw [← hb'] at h
  have h' : ((((true && planOkOwn (sendingPar one N.w "W and what rides with it" msg groups)) && true) &&
      (VerifiableInference.Desc.K13.rowsB (Cl := Cl) (batchLens (β := β)) (batchWhere one N sent)).planOk)) = true := h
  simp only [Bool.and_eq_true, Bool.true_and, Bool.and_true] at h'
  exact h'.1

/-- The law's one Boolean from its three clauses. -/
theorem cond_of (P : Par) (rad : Nat → Nat) (hB : planOkOwn P = true) (hl : P.codes.lengthsOk = true)
    (hm : ∀ k, sampledAt P k → meetsB P.codes (shapeAt P k) (rad k.val) = true) : condPort P rad = true := by
  simp only [condPort, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hB, hl⟩, hm⟩

/-! ## The law -/

variable {T W : Type} {F : Frame}

/-- What a block brings to the law of a sending. -/
structure Pays (P : Par) (stOf : T → Statement) (b : Block T Cl) : Prop where
  plan : planOkOwn P = true
  send : IsSend P stOf b

theorem idx_pays (one : OneTime) (N : Pieces) (groups : List (List Nat)) (h : (sendIndexMasks (β := β) (Cl := Cl) one N groups).planOk = true) :
    Pays (sendingPar one N.idx "the index masks" #[one.indexMasks] groups) (st₁ (β := β)) (sendIndexMasks (Cl := Cl) one N groups) :=
  ⟨planOwn_idxAt one N groups h, isSend_idxAt one N groups⟩

theorem msg_pays (one : OneTime) (N : Pieces) (groups : List (List Nat)) (h : (sendOwnMessage (β := β) (Cl := Cl) one N groups).planOk = true) :
    Pays (sendingPar one N.msg "the lookups' own message and what rides with it" (Wf.messageOf one.ranges) groups) (st₁ (β := β)) (sendOwnMessage (Cl := Cl) one N groups) :=
  ⟨planOwn_msgAt one N groups h, isSend_msgAt one N groups⟩

theorem w_pays {one : OneTime} {N : Pieces} {sent : Nat} {groups : List (List Nat)} {bw : Block (ChainState β) Cl} (hb : sendW one N sent groups = some bw)
    (h : bw.planOk = true) : ∃ msg, linMessageW one.lin = some msg ∧ Pays (sendingPar one N.w "W and what rides with it" msg groups) st₁ bw := by
  obtain ⟨msg, hm, hS⟩ := isSend_wAt hb
  exact ⟨msg, hm, planOwn_wAt hm hb h, hS⟩

/-- **send_goodIn, the first written round's five premises paid, its Boolean cut into what the block brings and two clauses on the codes.** -/
theorem sendGood (P : Par) (rad : Nat → Nat) (h1 : P.seeds = 1) (b : Block T Cl) (stOf : T → Statement) (hb : Pays P stOf b)
    (hl : P.codes.lengthsOk = true) (hm : ∀ k, sampledAt P k → meetsB P.codes (shapeAt P k) (rad k.val) = true)
    (base : Nat) (d₁ d₂ : RDT) (hd : SeedRound P d₁) (e : Nat)
    (he : errPort P rad ≤ e)
    (fOf : F.E.Str → ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str)
    (fIn : F.E.Str → (wT d₁).Msg → ∀ k, (portOmZ P.codes (shapeAt P k) (rad k.val)).Str)
    (hf : ∀ y τ, fOf ((sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.imp y τ) = fIn y τ.1)
    (On On' : T × F.E.Str → Prop) (R R' : T × F.E.Str → W → Prop)
    (hkeep : ∀ a τ x, On a → (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some x → On' x)
    (hback : ∀ a τ x w, On a → (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some x → R' x w → R a w) :
    (sendPiece (W := W) (F := F) b base d₁ d₂ P.coordinates e).GoodIn On
      (fun x => On' x ∧ ∀ k, sampledAt P k →
        Sealed P.codes (shapeAt P k) (rad k.val) (fOf x.2 k) (stOf x.1) ((stOf x.1).oracles.size - (shapesOf P).length + k.val)) R R' := by
  obtain ⟨hp, hE, hP, hz, hl'⟩ := five_of_seedRound P h1 d₁ hd
  exact send_goodIn P rad (cond_of P rad hb.plan hl hm) h1 b stOf hb.send base d₁ d₂ hp hE hP hz hl' e he fOf fIn hf On On' R R' hkeep hback

end Johnson.RunOne.KeySendGood

#print axioms Johnson.RunOne.KeySendGood.five_of_seedRound
#print axioms Johnson.RunOne.KeySendGood.idx_pays
#print axioms Johnson.RunOne.KeySendGood.msg_pays
#print axioms Johnson.RunOne.KeySendGood.w_pays
#print axioms Johnson.RunOne.KeySendGood.sendGood
